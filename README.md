# Čech cohomology

## Open coverings

Let $X$ be a topological space, an open covering for $X$ is a collection of open sets whose union is the whole $X$. In the case of Čech cohomology, we require the underlying set to be well ordered.

Let $X$ be a topological space, an open covering for $X$ is a collection of open sets whose union is the whole $X$. In the case of Čech cohomology, we require the underlying set to be linearly ordered.
In Lean we express this as

```lean
structure oc : Type (u+1) :=
(ι : Type.{u})
[lo : linear_order ι . tactic.apply_instance] 
[wo : is_well_order ι ((<) : ι → ι → Prop) . tactic.apply_instance]
(cover : ι → opens X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover
```

Then for two open covers $\mathfrak A$ and $\mathfrak B$ indexed by $I$ and $J$, respectively, we say $\mathfrak A$ refines $\mathfrak B$, if there is a strictly monotonic function $f : I \to J$ such that $\mathfrak A_i \subseteq \mathfrak B_{f(j)}$ for all $i ∈ I$. In Lean, this is

``` lean
@[ext] structure refines (𝔄 𝔅 : X.oc) : Type (u+1) :=
(func : 𝔄.ι → 𝔅.ι)
(strict_mono : strict_mono func)
(is_refinement : ∀ i : 𝔄.ι, 𝔄.cover i ≤ 𝔅.cover (func i))
```

We temporarily fix the indexing set $ι$, then an $n$-simplex is simply a finite set of $ι$ with $n+1$ elements. In Lean, this is

```lean
@[ext] structure simplex (n : ℕ) extends finset ι :=
(card_eq : to_finset.card = n.succ)
```

TBC
First baby step

```lean
lemma dd {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) : d_pos (nat.zero_lt_succ _) (d_pos hn f) = 0 :=
begin
  ext σ,
  convert dd_pos.eq26 hn f σ,
end
```

So we have a differential now, which means we can build cohomology theory.

To use the mathlib version of Abelian group has colimits, we need to lift up one universe.

## FIXME

~~Currently, I accidentally implemented the ordered chain as~~

```math
\begin{CD}
\mathcal F(X) @>>> \prod_i \mathcal F(U_i) @>>> \prod_{i_0<i_1} \mathcal F(U_i\cap U_j) @>>> \cdots
\end{CD}
```


~~But we should not have included the first term. Similarly for unordered.~~
