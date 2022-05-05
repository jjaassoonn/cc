Taking cohomology at the wrong place:
compute cohomology first then take limit.


I should use `simplex` as
```lean
def simplex (n : \Nat) :=
  fin n.succ \to \iota
```