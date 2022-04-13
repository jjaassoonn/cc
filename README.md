# Čech cohomology

First baby step

```lean
lemma dd {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) : d_pos (nat.zero_lt_succ _) (d_pos hn f) = 0 :=
begin
  ext σ,
  convert dd_pos.eq26 hn f σ,
end
```

So we have a differential now, which means we can build cohomology theory.
