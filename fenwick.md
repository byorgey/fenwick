XXX motivating example.

The general situation is as follows:

* We have a sequence of elements taken from some monoid $M$, indexed
  from $1 \dots n$.
* There are two operations we want to be able to perform:
    * Update the value at a particular index $i$, by combining it with
      an arbitrary element $m \in M$.
    * Query the current value of combining all the elements in the
      range $[i \dots j]$ according to the monoid.

What data structure should we use?

One obvious solution is to use a (mutable) array.  This allows us to
update in $O(1)$ time, but to do a range query there is nothing to do
but iterate through all values in the range, taking $O(n)$ in the
worst case.
