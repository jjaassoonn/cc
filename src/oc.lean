import topology.category.Top

namespace Top

open category_theory
open topological_space

universes u
variables (X : Top.{u})

structure oc : Type (u+1) :=
(ι : Type.{u})
[lo : linear_order ι . tactic.apply_instance] 
[wo : is_well_order ι ((<) : ι → ι → Prop) . tactic.apply_instance]
(cover : ι → opens X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover

instance (A : X.oc) [nonempty X] : nonempty A.ι :=
⟨nonempty.some $ classical.by_contradiction $ λ r, @@is_empty.false (not_nonempty_iff.mp r) $ 
  (opens.mem_supr.mp (by rw A.is_cover; trivial : nonempty.some infer_instance ∈ supr A.cover)).some⟩

noncomputable instance (A : X.oc) [inhabited X] : inhabited A.ι :=
⟨nonempty.some infer_instance⟩

variables {X} 
/--
A cover `𝔄` refines a cover `𝔅` if there is a function `f` between their indexing sets such that
for all `i` in indexing set of `𝔄`, `𝔄ᵢ ⊆ 𝔅_{f i}`
-/
@[ext] structure refines (𝔄 𝔅 : X.oc) : Type (u+1) :=
(func : 𝔄.ι → 𝔅.ι)
-- (strict_mono : strict_mono func)
(is_refinement : ∀ i : 𝔄.ι, 𝔄.cover i ≤ 𝔅.cover (func i))

def refines.refl (𝔄 : X.oc) : refines 𝔄 𝔄 :=
{ func := id,
  -- strict_mono := strict_mono_id,
  -- is_inj := function.injective_id,
  is_refinement := λ i, le_refl _ }

def refines.trans {𝔄 𝔅 ℭ : X.oc} (r1 : refines 𝔄 𝔅) (r2 : refines 𝔅 ℭ) : refines 𝔄 ℭ :=
{ func := r2.func ∘ r1.func,
  -- is_inj := function.injective.comp (r2.is_inj) (r1.is_inj),
  -- strict_mono := strict_mono.comp (r2.strict_mono) (r1.strict_mono),
  is_refinement := λ i, le_trans (r1.is_refinement i) (r2.is_refinement $ r1.func i) }

-- instance : has_le X.oc :=
-- { le := λ 𝔄 𝔅, nonempty (refines 𝔄 𝔅) }

-- instance : has_lt X.oc :=
-- { lt := λ 𝔄 𝔅, 𝔄 ≤ 𝔅 ∧ ¬ 𝔅 ≤ 𝔄 }

instance : inhabited X.oc :=
{ default := 
  { ι := punit,
    wo := ⟨{ apply := λ x, by { cases x, fconstructor, rintros ⟨-⟩ r, exfalso, simpa using r } }⟩,
    cover := λ _, ⊤,
    is_cover := by simp } }

-- this is probably wrong
-- example (A : X.oc) (f : refines A A) (i) : f.func i = i :=
-- begin
--   have := @trichotomous _ ((<) : A.ι → A.ι → Prop) _ (f.func i) i,
--   rcases this,
--   { -- this is contradiction
--     -- suppose `a` is the least function such that `f a < a` then `f f a < f a < a` contradiction
--     sorry },
--   { rcases this,
--     { exact this },
--     { -- 
--       sorry } },
-- end


-- instance : preorder X.oc :=
-- { le := (≤),
--   lt := (<),
--   le_refl := λ x, nonempty.intro $ refines.refl _,
--   le_trans := λ _ _ _ ⟨r1⟩ ⟨r2⟩, ⟨r1.trans r2⟩,
--   lt_iff_le_not_le := λ _ _, ⟨id, id⟩ }

-- def common_refinement (A B : X.oc) : X.oc :=
-- { ι := A.ι ⊗ B.ι,
--   lo := 
--   { le := sum.lex ((≤) : A.ι → A.ι → Prop) ((≤) : B.ι → B.ι → Prop),
--     lt := _,
--     le_refl := _,
--     le_trans := _,
--     lt_iff_le_not_le := _,
--     le_antisymm := _,
--     le_total := _,
--     decidable_le := _,
--     decidable_eq := _,
--     decidable_lt := _,
--     max := _,
--     max_def := _,
--     min := _,
--     min_def := _ },
--   wo := _,
--   cover := λ i, sum.rec_on i A.cover B.cover,
--   is_cover := sorry }

instance : category_theory.small_category X.oc := 
{ hom := λ A B, refines A B,
  id := λ A, refines.refl A,
  comp := λ A B C f g, refines.trans f g,
  id_comp' := λ A B f, by ext; refl,
  comp_id' := λ A B f, by ext; refl,
  assoc' := λ A B C D f g h, by ext; refl }

-- instance : category_theory.is_cofiltered X.oc :=
-- { cocone_objs := λ A B, sorry, -- common refinement
--   cocone_maps := λ A B, sorry,
--   /-
--   A indexed by a
--   B indexed by b
--                   f             
--   W -------> A ========> B 
--                   g

--   such that f ≫ h = g ≫ h

--   -/
--   nonempty := ⟨default⟩ }

end Top