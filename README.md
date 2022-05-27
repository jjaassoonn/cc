# Čech cohomology

## Open coverings

Let $X$ be a topological space, an open covering for $X$ is a collection of open sets whose union is the whole $X$. In the case of Čech cohomology, we require the underlying set to be well ordered.

Let $X$ be a topological space, an open covering for $X$ is a collection of open sets whose union is the whole $X$. In the case of Čech cohomology, we require the underlying set to be linearly ordered.
In Lean we express this as

```lean
structure oc : Type (u+1) :=
(ι : Type.{u})
[lo : linear_order ι . tactic.apply_instance] 
(cover : ι → opens X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover
```

Then for two open covers $\mathfrak A$ and $\mathfrak B$ indexed by $I$ and $J$, respectively, we say $\mathfrak A$ refines $\mathfrak B$, if there is a strictly monotonic function $f : I \to J$ such that $\mathfrak A_i \subseteq \mathfrak B_{f(j)}$ for all $i ∈ I$. In Lean, this is

``` lean
@[ext] structure refines (𝔄 𝔅 : X.oc) : Type (u+1) :=
(func : 𝔄.ι → 𝔅.ι)
(is_refinement : ∀ i : 𝔄.ι, 𝔄.cover i ≤ 𝔅.cover (func i))
```

~~We temporarily fix the indexing set $ι$, then an $n$-simplex is simply a finite set of $ι$ with $n+1$ elements. In Lean, this is~~

```lean
-- @[ext] structure simplex (n : ℕ) extends finset ι :=
-- (card_eq : to_finset.card = n.succ)
```

## Unordered

```lean
def C.pre (n : ℕ) : Type* :=
Π (α : fin n → U.ι), 𝓕.1.obj (op $ face α)

abbreviation C (n : ℕ) := AddCommGroup.of (C.pre 𝓕 U n)

lemma d_def (f : C 𝓕 U n) (α : fin (n + 1) → U.ι) :
  d 𝓕 U n f α =
  ∑ (i : fin (n+1)), 
    (ite (even i.1) id has_neg.neg)
      𝓕.1.map (hom_of_le $ face.le_ignore α i).op (f (ignore α i) := 
...

def Cech_complex_wrt_cover_unordered : cochain_complex Ab.{u} ℕ :=
{ X := λ n, C 𝓕 U (n + 1),
  d := λ i j, d_from_to 𝓕 U (i + 1) (j + 1),
  shape' := λ i j h, ...,
  d_comp_d' := λ i j k h1 h2, ... }
```

## Ordered

```lean
structure vec_o (n : ℕ) : Type u :=
(to_fun : fin n → U.ι)
(is_strict_mono : strict_mono to_fun)

def C_o.pre (n : ℕ) : Type u :=
Π (α : vec_o U n), 𝓕.1.obj (op $ face α)

def C_o (n : ℕ) : Ab := AddCommGroup.of (C_o.pre 𝓕 U n)

def Cech_complex_wrt_cover_ordered : cochain_complex Ab.{u} ℕ :=
{ X := λ n, C_o 𝓕 U (n + 1),
  d := λ i j, d_o_from_to 𝓕 U _ _,
  shape' := λ i j h, ...,
  d_comp_d' := λ i j k h1 h2, ... }

def Cech_Cohomology_Group_wrt_cover_ordered_nth (n : ℕ) : Ab :=
@homological_complex.homology ℕ Ab _ _ (complex_shape.up ℕ) (abelian.has_zero_object) _ _ _ (Cech_complex_wrt_cover_ordered 𝓕 U) n


def zeroth_Cech_Cohomology :
  (Cech_Cohomology_Group_wrt_cover_ordered_nth 𝓕 U 0) ≅
  𝓕.1.obj (op ⊤) :=
ex1 𝓕 U ≪≫ ex2 𝓕 U ≪≫ ex3 𝓕 U ≪≫ 
{ hom := (ex41 _ _).to_add_monoid_hom,
  inv := (ex41 _ _).symm.to_add_monoid_hom,
  hom_inv_id' := begin
    ext f σ,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.symm_apply_apply, id_apply],
  end,
  inv_hom_id' := begin
    ext f σ,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.apply_symm_apply, id_apply],
  end }
```

## Morphism between Ordered and unordered chain

I believe this is how it should be done

```lean
def unordered_to_ordered.to_fun (n : ℕ) :
  C 𝓕 U n → C_o 𝓕 U n :=
λ f σ, f σ.to_fun

def ordered_to_unordered.to_fun (n : ℕ) :
  C_o 𝓕 U n → C 𝓕 U n := λ f α, 
dite (function.injective α)
(λ h, match signature α with
  | sign.zero := 0 -- this will never occur
  | sign.pos := 𝓕.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  | sign.neg := - 𝓕.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  end)
(λ _, 0)

```

## FIXME

~~Currently, I accidentally implemented the ordered chain as~~

```math
\begin{CD}
\mathcal F(X) @>>> \prod_i \mathcal F(U_i) @>>> \prod_{i_0<i_1} \mathcal F(U_i\cap U_j) @>>> \cdots
\end{CD}
```


~~But we should not have included the first term. Similarly for unordered.~~
