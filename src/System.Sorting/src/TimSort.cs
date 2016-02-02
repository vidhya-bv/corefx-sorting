using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Sorting;
using System.Text;

// This implementation was referenced from Java opensource, which has been found here:
// http://grepcode.com/file/repository.grepcode.com/java/root/jdk/openjdk/8-b132/java/util/TimSort.java
// Other Open Source references used C++:
//https://github.com/gfx/cpp-TimSort/blob/master/timsort.hpp
//Reference: https://en.wikipedia.org/wiki/Timsort
//ref:http://svn.python.org/projects/python/trunk/Objects/listsort.txt - Original explanation from Tim
//Timsort is a hybrid stable sorting algorithm, derived from merge sort and insertion sort, designed to perform well on many kinds of partially sorted real-world data
//Timsort is not a standalone algorithm but a hybrid, an efficient combination of a number of other algorithms
//The algorithm finds subsets of the data that are already ordered, and uses that knowledge to sort the remainder more efficiently. This is done by merging an identified subset, called a run, with existing runs until certain criteria are fulfilled
namespace System.Sorting
{
    //utility class for Timsort
 internal static class TimSortUtilities
    {
        //?Jave uses 32, Timsort Python originally uses 64. this may need to be revisited by testing new numbers for C# 
        //several magic numbers used for efficiency
        //A natural run is a sub-array that is already ordered. Timsort chooses a sorting technique depending on the length of the run. For example, if the run length is smaller than a certain value, insertion sort is used. Thus Timsort is an adaptive sort
        //If the entire array is less than this length, no merges will be performed, instead Binary Insertion sort is used directly.
        internal const int MinMerge = 32;

        //Most of the merge occurs in what is called "one pair at a time" mode, 
        //where respective elements of both runs are compared. When the algorithm merges left-to-right, 
        //the smaller of the two is brought to a merge area. A count of the number of times the final element appears in a given run is recorded. When this value reaches a certain threshold, MIN_GALLOP, the merge switches to "galloping mode".
        internal const int MinGallop = 7;

        //C uses 85, Java uses a mixed mode of arriving at most efficient number for stackLength. This varies depending on 
        //MinMerge number above. we may need to readjust these nos, in c# based on code performance.
        internal const int StackLength = 40;

        //internal T[] mergeBufferArray=new T[256];

        //The minimum run size (minrun) depends on the size of the array.
        //The final algorithm takes the six most significant bits of the size of the array, adds one if any of the remaining bits are set, and uses that result as the minrun.This algorithm works for all arrays, including those smaller than 32
        internal static int FindMinimumRun(int arrayLength)
        {
            int remainder = 0;  /* becomes 1 if the least significant bits contain at least one off bit */
            while (arrayLength >= MinMerge)
            {
                remainder |= arrayLength & 1;
                arrayLength >>= 1;
            }
            return arrayLength + remainder;
        }

    }
    //public class TimSort<T> where T : IComparable<T>
    public class TimSort<T> where T : IComparable,new()
    {
        //counter to increase the arrayRunBase & arrayRunLength
        private int stackSize;

        /// <summary>
		/// A stack of pending runs yet to be merged. 
        /// Run i starts at
		/// address base[i] and extends for len[i] elements.  It's always
		/// true (so long as the indices are in bounds) that:
		/// <c>runBase[i] + runLen[i] == runBase[i + 1]</c>
        private int[] arrayRunBase;
        private int[] arrayRunLength;

        /// <summary>
        /// Temp storage for merges.
        /// </summary>
        private T[] mergeBufferArray;// = new T[256];
        
        /// <summary>The array being sorted.</summary>
		private readonly T[] array;
        private int m_minGallop;

        /*** The comparer for this sort.*/
        private IComparer<T> vComparable;

        //private TimSort(T[] keys, IComparer<T> comparer)
        public TimSort(T[] keys, IComparer<T> comparer)
        {
            array = keys;
            arrayRunBase = new int[TimSortUtilities.StackLength];
            arrayRunLength = new int[TimSortUtilities.StackLength];
            vComparable = comparer;
            m_minGallop = TimSortUtilities.MinGallop;
            mergeBufferArray = new T[array.Length];
        }

        //static volatile TimSort<T> defaultArraySortHelper;
        //public static TimSort<T> Default(T[] keys, IComparer<T> comparer)
        //{
        //    //get{
        //        //TimSort<T> sorter = defaultArraySortHelper;
        //        if (defaultArraySortHelper == null)
        //        defaultArraySortHelper = new TimSort<T>(keys, comparer);

        //        return defaultArraySortHelper;
        //    //}
        //}

        public void Sort(T[] keys, int index, int arrayLength, IComparer<T> comparer)
        {
            Contract.Assert(keys != null, "Check the arguments in the caller!");
            Contract.Assert(index >= 0 && arrayLength >= 0 && (keys.Length - index >= arrayLength), "Check the arguments in the caller!");
            
            if (arrayLength < 2) return; // Arrays of size 0 and 1 are always sorted
                                         //array = keys;

            try
            {
                if (comparer == null)
                {
                    comparer = Comparer<T>.Default;
                }

                //if array lenghth is < 32, do a BinaryInsertionSort & exit
                if (arrayLength < TimSortUtilities.MinMerge)
                {
                    int firstRunLength = CountFirstRunAndReverseDescending(keys, index, arrayLength, comparer);
                    BinaryInsertionSort(keys, index, arrayLength, index+firstRunLength, comparer);
                    return;
                }

                int remainingArrayWidth = arrayLength;
                // if arrayLength > MinMerge, March over the array once, left to right, finding natural runs,
                // extending short natural runs to minRun elements using BinaryInsertionSort, and merging runs
                // to maintain stack invariant.
                int minRun=TimSortUtilities.FindMinimumRun(keys.Length);
                do
                {
                    //var timSort = new TimSort<T>();
                    //identify next run
                    int runLen = CountEachRunAndReverseDescending(keys,index, arrayLength, comparer);

                    // If run is short, extend to min(minRun, nRemaining), and then use BinaryInsertionSort to sort that specific run
                    if (runLen< minRun)
                    {
                        int force = Math.Min(remainingArrayWidth, minRun);//remainingArrayWidth <= TimSortUtilities.MinMerge ? remainingArrayWidth : TimSortUtilities.MinMerge;
                        BinaryInsertionSort(keys, index, index + force, index + runLen, comparer);
                        runLen = force;
                    }

                    // Push run onto pending-run stack, and merge
                    PushRun(index, runLen);
                    
                    //merge runs from stack                     
                    MergeCollapse();

                    //advance to next run
                    index += runLen;
                    remainingArrayWidth -= runLen;

                } while (remainingArrayWidth>0);

                // Merge all remaining runs to complete sort
                MergeForceCollapse();
            }
            catch(IndexOutOfRangeException)
            {
                throw new ArgumentException("BadIComparer");
            }
            catch (Exception e)
            {
                throw new InvalidOperationException(e.Message);
            }                      
        }

        private static int CountFirstRunAndReverseDescending(T[] array, int lo, int hi, IComparer<T> comparer)
        {
            return CountEachRunAndReverseDescending(array, lo, hi, comparer);                    
        }

        /// <summary>
        /// Returns the length of the run beginning at the specified position in
        /// the specified array and reverses the run if it is descending (ensuring
        /// that the run will always be ascending when the method returns).
        /// A run is the longest ascending sequence with: <c><![CDATA[a[lo] <= a[lo + 1] <= a[lo + 2] <= ...]]></c>
        /// or the longest descending sequence with: <c><![CDATA[a[lo] >  a[lo + 1] >  a[lo + 2] >  ...]]></c>
        /// </summary>
        /// <param name="array">the array in which a run is to be counted and possibly reversed.</param>
        /// <param name="lo">index of the first element in the run.</param>
        /// <param name="hi">index after the last element that may be contained in the run. It is required 
        /// that <c><![CDATA[lo < hi]]></c>.</param>
        /// <param name="c">the compararer to used for the sort.</param>
        /// <returns>the length of the run beginning at the specified position in the specified array</returns>
        private static int CountEachRunAndReverseDescending(T[] array, int lo, int hi, IComparer<T> comparer)
        {
            int next = lo + 1;
                //if (next == hi) return 1;
            int order = comparer.Compare(array[next], array[lo]);

            ////if descending, make ascending and count the run
            // Find end of run, and reverse range if descending
            if (order < 0)
            {
                while (next < hi && comparer.Compare(array[next], array[next - 1]) < 0) next++;
                Array.Reverse(array, lo, next);
            }
            else
            {
               // Ascending
               while (next < hi && comparer.Compare(array[next], array[next - 1]) >= 0) next++;
            }
                return next - lo;
         }

        /// <summary>
        /// Sorts the specified portion of the specified array using a binary insertion sort. This is the best method for 
        /// sorting small numbers of elements. It requires O(n log n) compares, but O(n^2) data movement (worst case).
        /// If the initial part of the specified range is already sorted, this method can take advantage of it: the method 
        /// assumes that the elements from index inclusive, to <c>value</c>, exclusive are already sorted.
        /// </summary>
        /// <param name="array">the array in which a range is to be sorted.</param>
        /// <param name="index">the index of the first element in the range to be sorted.</param>
        /// <param name="length">the index after the last element in the range to be sorted.</param>
        /// <param name="value">start the index of the first element in the range that is not already known to be sorted 
        /// (<c><![CDATA[lo <= start <= hi]]></c>)</param>
        /// <param name="c">The comparator to used for the sort.</param>
        private static void BinaryInsertionSort(T[] array, int index, int length, int value, IComparer<T> comparer)
        {
           Contract.Assert(array != null, "Check the arguments in the caller!");
           Contract.Assert(index >= 0 && length >= 0 && index <= value && value<=length, "Check the arguments in the caller!");

            ////?if (index == value) value++;

            for (/* nothing */; value < length; value++)
            {
                T pivot = array[value];
                int lo = index;
                int hi = value;//index + length - 1;

                while (lo < hi)
                {
                    int mid = lo + ((hi - lo) >> 1);
                    int order = comparer.Compare(array[mid], pivot);

                    //if (order == 0) return mid;
                    if (order > 0)
                    {
                        hi = mid;
                        //lo = mid + 1;
                    }
                    else
                    {
                        lo = mid + 1;
                    }
                }
                               
                int moveBy = value - lo;
                Array.Copy(array, lo, array, lo+1, moveBy);
                array[lo] = pivot;
            }
        }

        /// <summary>
		/// Pushes the specified run onto the pending-run stack.
		/// </summary>
		/// <param name="runBase">index of the first element in the run.</param>
		/// <param name="runLength">the number of elements in the run.</param>
        private void PushRun(int runBase, int runLength)
        {
            arrayRunBase[stackSize] = runBase;
            arrayRunLength[stackSize] = runLength;
            stackSize++;
        }

        /// <summary>
		/// Examines the stack of runs waiting to be merged and merges adjacent runs until the stack invariants are
		/// reestablished: 
		/// <c><![CDATA[1. runLen[i - 3] > runLen[i - 2] + runLen[i - 1] ]]></c> and 
		/// <c><![CDATA[2. runLen[i - 2] > runLen[i - 1] ]]></c>
		/// This method is called each time a new run is pushed onto the stack		
		/// </summary>
        private void MergeCollapse()
        {
            while (stackSize > 1)
            {
                int n = stackSize - 2;

                //runLen[i-1]<run[i-2]+runLen[i-3] as an outcome of condition mentioned above.
                if (n > 0 && arrayRunLength[n - 1] <= arrayRunLength[n] + arrayRunLength[n + 1])
                {          
                    //Merge runLen[i-2] with runLen[i-3] or runLen[i-1] depending on which is smaller
                    if (arrayRunLength[n - 1] < arrayRunLength[n + 1]) n--;
                    MergeAt(n);
                }
                else if (arrayRunLength[n] <= arrayRunLength[n + 1])
                {
                    MergeAt(n);
                }
                else
                {
                    break; 
                }
            }
        }

        /// <summary>
        /// Merges all runs on the stack until only one remains.  This method is called once, to complete the sort.
        /// </summary>
        private void MergeForceCollapse()
        {
            while (stackSize > 1)
            {
                int n = stackSize - 2;
                if (n > 0 && arrayRunLength[n - 1] < arrayRunLength[n + 1]) n--;
                MergeAt(n);
            }
        }

        /// <summary>
        /// Merges the two runs at stack indices i and i+1.  Run i must be the penultimate or antepenultimate run on the stack. 
        /// In other words, i must be equal to stackSize-2 or stackSize-3.
        /// </summary>
        /// <param name="runIndex">stack index of the first of the two runs to merge.</param>
        private void MergeAt(int runIndex)
        {
            int base1 = arrayRunBase[runIndex];
            int len1 = arrayRunLength[runIndex];
            int base2 = arrayRunBase[runIndex + 1];
            int len2 = arrayRunLength[runIndex + 1];
            
            arrayRunLength[runIndex] = len1 + len2;
            if (runIndex == stackSize - 3)
            {
                arrayRunBase[runIndex + 1] = arrayRunBase[runIndex + 2];
                arrayRunLength[runIndex + 1] = arrayRunLength[runIndex + 2];
            }
            stackSize--;

            // Find where the first element of run2 goes in run1. Prior elements
            // in run1 can be ignored (because they're already in place).
            int k = Gallop(array[base2], array, base1, len1, 0,vComparable);
            
            base1 += k;
            len1 -= k;
            if (len1 == 0) return;

            // Find where the last element of run1 goes in run2. Subsequent elements
            // in run2 can be ignored (because they're already in place).
            len2 = Gallop(array[base1 + len1 - 1], array, base2, len2, len2 - 1, vComparable);

            if (len2 == 0) return;

            // Merge remaining runs, using tmp array with min(len1, len2) elements
            if (len1 <= len2)
                MergeLo(base1, len1, base2, len2);
            else
                MergeHi(base1, len1, base2, len2);
        }

        /// <summary>
        /// Locates the position at which to insert the specified key into the
        /// specified sorted range; 
        /// </summary>
        /// <param name="key">the key whose insertion point to search for.</param>
        /// <param name="array">the array in which to search.</param>
        /// <param name="lo">the index of the first element in the range.</param>
        /// <param name="length">the length of the range; must be &gt; 0.</param>
        /// <param name="hint">the index at which to begin the search, 0 <= hint < n. 
        /// <param name="comparer">the comparator used to order the range, and to search.</param>
        /// <returns>the int k,  0 <= k <= n such that 
        /// return k such that B[2**(k-1) - 1] < A[0] <= B[2**k - 1].
        /// After finding such a k, the region of uncertainty is reduced to 2**(k-1) - 1
        ///       consecutive elements, and a straight binary search requires exactly k-1
        ///additional comparisons to nail it.Then we copy all the B's up to that
        ///point in one chunk, and then copy A[0].  Note that no matter where A[0]
        ///belongs in B, the combination of galloping + binary search finds it in no
        ///more than about 2*lg(B) comparisons.
        /// </returns>
        private static int Gallop(T key, T[] array, int lo, int length, int hint,IComparer<T> comparer)
        {
            int lastOfs = 0;
            int ofs = 1;

            if (comparer.Compare(key, array[lo + hint]) < 0)
            {
                // Gallop left until a[b+hint - ofs] <= key < a[b+hint - lastOfs]
                int maxOfs = hint + 1;
                while (ofs < maxOfs && comparer.Compare(key, array[lo + hint - ofs]) < 0)
                {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0)   // int overflow
                        ofs = maxOfs;
                }
                if (ofs > maxOfs)
                    ofs = maxOfs;

                // Make offsets relative to b
                int tmp = lastOfs;
                lastOfs = hint - ofs;
                ofs = hint - tmp;
            }
            else
            {
                // a[b + hint] <= key
                // Gallop right until a[b+hint + lastOfs] <= key < a[b+hint + ofs]
                int maxOfs = length - hint;
                while (ofs < maxOfs && comparer.Compare(key, array[lo + hint + ofs]) >= 0)
                {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0)   // int overflow
                        ofs = maxOfs;
                }
                if (ofs > maxOfs)
                    ofs = maxOfs;

                // Make offsets relative to b
                lastOfs += hint;
                ofs += hint;
            }

            lastOfs++;
            while (lastOfs < ofs)
            {
                int m = lastOfs + ((ofs - lastOfs) >> 1);

                if (comparer.Compare(key, array[lo + m]) > 0)
                    lastOfs = m + 1; // a[base + m] < key
                else
                    ofs = m; // key <= a[base + m]
            }

            return ofs;
        }

        /// <summary>
        /// Merges two adjacent runs in place, in a stable fashion. The first element of the first run must be greater than 
        /// the first element of the second run (a[base1] &gt; a[base2]), and the last element of the first run 
        /// (a[base1 + len1-1]) must be greater than all elements of the second run.
        /// For performance, this method should be called only when len1 &lt;= len2; its twin, mergeHi should be called if 
        /// len1 &gt;= len2. (Either method may be called if len1 == len2.)
        /// </summary>
        /// <param name="base1">index of first element in first run to be merged.</param>
        /// <param name="len1">length of first run to be merged (must be &gt; 0).</param>
        /// <param name="base2">index of first element in second run to be merged (must be aBase + aLen).</param>
        /// <param name="len2">length of second run to be merged (must be &gt; 0).</param>
        private void MergeLo(int base1, int len1, int base2, int len2)
        {
            //Debug.Assert(len1 > 0 && len2 > 0 && base1 + len1 == base2);

            // Copy first run into temp array
            //var array = m_Array; // For performance
            //var mergeBuffer = EnsureCapacity(len1);
            Array.Copy(array, base1, mergeBufferArray, 0, len1);

            int cursor1 = 0;       // Indexes into tmp array
            int cursor2 = base2;   // Indexes int a
            int dest = base1;      // Indexes int a

            // Move first element of second run and deal with degenerate cases
            array[dest++] = array[cursor2++];
            if (--len2 == 0)
            {
                Array.Copy(mergeBufferArray, cursor1, array, dest, len1);
                return;
            }
            if (len1 == 1)
            {
                Array.Copy(array, cursor2, array, dest, len2);
                array[dest + len2] = mergeBufferArray[cursor1]; // Last elt of run 1 to end of merge
                return;
            }

            int minGallop = m_minGallop;

            while (true)
            {
                int count1 = 0; // Number of times in a row that first run won
                int count2 = 0; // Number of times in a row that second run won

                /*
				 * Do the straightforward thing until (if ever) one run starts
				 * winning consistently.
				 */
                do
                {
                    if (vComparable.Compare(array[cursor2], mergeBufferArray[cursor1]) < 0)
                    {
                        array[dest++] = array[cursor2++];
                        count2++;
                        count1 = 0;
                        if (--len2 == 0)
                            goto break_outer;
                    }
                    else
                    {
                        array[dest++] = mergeBufferArray[cursor1++];
                        count1++;
                        count2 = 0;
                        if (--len1 == 1)
                            goto break_outer;
                    }
                } while ((count1 | count2) < minGallop);

                // One run is winning so consistently that galloping may be a
                // huge win. So try that, and continue galloping until (if ever)
                // neither run appears to be winning consistently anymore.
                do
                {
                    count1 = Gallop(array[cursor2], mergeBufferArray, cursor1, len1, 0, vComparable);
                    if (count1 != 0)
                    {
                        Array.Copy(mergeBufferArray, cursor1, array, dest, count1);
                        dest += count1;
                        cursor1 += count1;
                        len1 -= count1;
                        if (len1 <= 1) // len1 == 1 || len1 == 0
                            goto break_outer;
                    }
                    array[dest++] = array[cursor2++];
                    if (--len2 == 0)
                        goto break_outer;

                    count2 = Gallop(mergeBufferArray[cursor1], array, cursor2, len2, 0,vComparable);
                    if (count2 != 0)
                    {
                        Array.Copy(array, cursor2, array, dest, count2);
                        dest += count2;
                        cursor2 += count2;
                        len2 -= count2;
                        if (len2 == 0)
                            goto break_outer;
                    }
                    array[dest++] = mergeBufferArray[cursor1++];
                    if (--len1 == 1)
                        goto break_outer;
                    minGallop--;
                } while (count1 >= TimSortUtilities.MinGallop | count2 >= TimSortUtilities.MinGallop);

                if (minGallop < 0)
                    minGallop = 0;
                minGallop += 2;  // Penalize for leaving gallop mode
            }  // End of "outer" loop

            break_outer: 
            
            if (len1 == 1)
            {
                Array.Copy(array, cursor2, array, dest, len2);
                array[dest + len2] = mergeBufferArray[cursor1]; //  Last elt of run 1 to end of merge
            }
            else if (len1 == 0)
            {
                throw new ArgumentException("Comparison method violates its general contract!");
            }
            else
            {
                Array.Copy(mergeBufferArray, cursor1, array, dest, len1);
            }
        }

        /// <summary>
        /// Like mergeLo, except that this method should be called only if
        /// len1 &gt;= len2; mergeLo should be called if len1 &lt;= len2. (Either method may be called if len1 == len2.)
        /// </summary>
        /// <param name="base1">index of first element in first run to be merged.</param>
        /// <param name="len1">length of first run to be merged (must be &gt; 0).</param>
        /// <param name="base2">index of first element in second run to be merged (must be aBase + aLen).</param>
        /// <param name="len2">length of second run to be merged (must be &gt; 0).</param>
        private void MergeHi(int base1, int len1, int base2, int len2)
        {
            Array.Copy(array, base2, mergeBufferArray, 0, len2);

            int cursor1 = base1 + len1 - 1;  // Indexes into a
            int cursor2 = len2 - 1;          // Indexes into tmp array
            int dest = base2 + len2 - 1;     // Indexes into a

            // Move last element of first run and deal with degenerate cases
            array[dest--] = array[cursor1--];
            if (--len1 == 0)
            {
                Array.Copy(mergeBufferArray, 0, array, dest - (len2 - 1), len2);
                return;
            }
            if (len2 == 1)
            {
                dest -= len1;
                cursor1 -= len1;
                Array.Copy(array, cursor1 + 1, array, dest + 1, len1);
                array[dest] = mergeBufferArray[cursor2];
                return;
            }

            //var c = m_Comparer;  // Use local variables for performance
            int minGallop = TimSortUtilities.MinGallop;

            while (true)
            {
                int count1 = 0; // Number of times in a row that first run won
                int count2 = 0; // Number of times in a row that second run won

                // Do the straightforward thing until (if ever) one run appears to win consistently.
                do
                {
                    //Debug.Assert(len1 > 0 && len2 > 1);
                    if (vComparable.Compare(mergeBufferArray[cursor2], array[cursor1]) < 0)
                    {
                        array[dest--] = array[cursor1--];
                        count1++;
                        count2 = 0;
                        if (--len1 == 0)
                            goto break_outer;
                    }
                    else
                    {
                        array[dest--] = mergeBufferArray[cursor2--];
                        count2++;
                        count1 = 0;
                        if (--len2 == 1)
                            goto break_outer;
                    }
                } while ((count1 | count2) < minGallop);

                // One run is winning so consistently that galloping may be a
                // huge win. So try that, and continue galloping until (if ever)
                // neither run appears to be winning consistently anymore.
                do
                {
                    count1 = len1 - Gallop(mergeBufferArray[cursor2], array, base1, len1, len1 - 1, vComparable);
                    if (count1 != 0)
                    {
                        dest -= count1;
                        cursor1 -= count1;
                        len1 -= count1;
                        Array.Copy(array, cursor1 + 1, array, dest + 1, count1);
                        if (len1 == 0)
                            goto break_outer;
                    }
                    array[dest--] = mergeBufferArray[cursor2--];
                    if (--len2 == 1)
                        goto break_outer;

                    count2 = len2 - Gallop(array[cursor1], mergeBufferArray, 0, len2, len2 - 1, vComparable);
                    if (count2 != 0)
                    {
                        dest -= count2;
                        cursor2 -= count2;
                        len2 -= count2;
                        Array.Copy(mergeBufferArray, cursor2 + 1, array, dest + 1, count2);
                        if (len2 <= 1)  // len2 == 1 || len2 == 0
                            goto break_outer;
                    }
                    array[dest--] = array[cursor1--];
                    if (--len1 == 0)
                        goto break_outer;
                    minGallop--;
                } while (count1 >= TimSortUtilities.MinGallop | count2 >= TimSortUtilities.MinGallop);

                if (minGallop < 0)
                    minGallop = 0;
                minGallop += 2;  // Penalize for leaving gallop mode
            } // End of "outer" loop

            break_outer: // goto me! ;)

            //m_MinGallop = minGallop < 1 ? 1 : minGallop;  // Write back to field

            if (len2 == 1)
            {
                //Debug.Assert(len1 > 0);
                dest -= len1;
                cursor1 -= len1;
                Array.Copy(array, cursor1 + 1, array, dest + 1, len1);
                array[dest] = mergeBufferArray[cursor2];  // Move first elt of run2 to front of merge
            }
            else if (len2 == 0)
            {
                throw new ArgumentException("Comparison method violates its general contract!");
            }
            else
            {
                Array.Copy(mergeBufferArray, 0, array, dest - (len2 - 1), len2);
            }
        }
    }
}
