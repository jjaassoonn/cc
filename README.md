# Čech cohomology

Progress so far:

```lean
lemma dd_pos.eq :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ∑ j in (range n.succ).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩)))
```
