///////////////////////////////////////////////////////////////////////////////////////////////////////
// 1.1 (Optional) Swap lemma proof obligation for WP

//  SwapLemmaWP

///////////////////////////////////////////////////////////////////////////////////////////////////////
// 1.2 (Optional) Swap lemma proof obligation for SP

 // SwapLemmaSP

///////////////////////////////////////////////////////////////////////////////////////////////////////
// 3.1 Integer square root methods

// An axiomatic definition of integer square root.
function Sqrt(n: int): int
  requires n >= 0;
  ensures forall m:nat :: m*m<=n && (m+1)*(m+1)>n ==> m==Sqrt(n);

// Computes the integer square root of n via a linear search from 0 to n.
method SlowSqrt(n: nat) returns (r: nat)
  ensures r == Sqrt(n)
{
  r := 0;
  while(r*r<=n && (r+1)*(r+1) <= n)
  invariant 0 <= r*r <= n 
  decreases n - r
  {
	assert 0<= r*r <=n;
	r:=r+1;
	}
	assert 0<= r*r <=n;
	assert !(r*r<=n && (r+1)*(r+1) < n);
	assert r == Sqrt(n);
}

// Computes the integer square root of n via a binary search.
method FastSqrt(n: nat) returns (r: nat)
	ensures r == Sqrt(n)
{
	r := 0;
	var low:nat := 0;
	var high:nat := n;
	while (high >= low + 2)
	invariant low*low <= n &&  n <= high* high
	{
		assert low*low <= n &&  n <= high*high;
		r := (low + high)/2; 
		if(r*r > n){
			high := r;
		}
		else
		{
			low := r;
		}
	
	}
	assert low*low <= n &&   n <= high*high;
	assert !(high >= low + 2);
	if(high*high == n){
		r := high;
	}
	else {
		r := low;
	}
	assert r == Sqrt(n);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////
// 3.2 Array search methods

// Finds the first array index containing the value 'val' by searching left-to-right.
method find(arr: array<int>, val: int) returns (res: nat)
requires arr != null;
ensures (exists z:: 0 <= z < arr.Length && arr[z]==val) ==> (0 <= res < arr.Length && arr[res]==val);
{
	var i := 0;
	while (i < arr.Length)
	invariant i <=arr.Length
	invariant forall j :: 0 <= j < i ==> arr[j] != val;
    decreases arr.Length - i;

	{
		if (arr[i] == val) {
			res := i;
			break;
		}
		i := i + 1;
	}
	assert (exists z:: 0 <= z < arr.Length && arr[z]==val) ==> (0 <= res < arr.Length && arr[res]==val);
}

// Evaluates to true if the given value is in the array index range [from to).
predicate inRange(arr: array<int>, val: int, from: nat, to: nat)
requires arr != null;
requires from < arr.Length;
requires to <= arr.Length;
reads arr;
{
	exists z:: from <= z < to && arr[z] == val
}

// Finds the array index containing the value 'val' by first searching the range [pos,arr.Length} and then
// (if the value is not found) the range [0,pos).
method circularFind(arr: array<int>, val: int, pos: nat) returns (res: nat)
requires arr != null;
requires 0 <= pos < arr.Length;
ensures inRange(arr, val, 0, arr.Length) ==> (0 <= res < arr.Length && arr[res]==val);
{
	var i := pos;	
	while (i < arr.Length)
	invariant i <=arr.Length
	invariant forall j :: pos <= j < i ==> arr[j] != val;
    decreases arr.Length - i;
	
	{
		if (arr[i] == val) {
			res := i;
			break;
		}
		i := i + 1;
	}
	if (i == arr.Length) {
		i := 0;		
		while (i < pos)
		invariant i <=pos
		invariant forall k :: 0 <= k  <i ==> arr[k] != val;
		 {
			if (arr[i] == val) {
				res := i;
				break;
			}
			i := i + 1;
		}
	}
	assert inRange(arr, val, 0, arr.Length) ==> (0 <= res < arr.Length && arr[res]==val);
}