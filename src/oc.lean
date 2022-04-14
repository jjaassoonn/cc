import topology.category.Top

namespace Top

open topological_space category_theory

variables (X : Top)

structure oc :=
(ι : Type*)
[lo : linear_order ι . tactic.apply_instance] 
[wo : is_well_order ι ((<) : ι → ι → Prop) . tactic.apply_instance]
(cover : ι → opens X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover

namespace oc
open category_theory

variables {X} 

/--
A cover `𝔄` refines a cover `𝔅` if there is a function `f` between their indexing sets such that
for all `i` in indexing set of `𝔄`, `𝔄ᵢ ⊆ 𝔅_{f i}`
-/
structure refines (𝔄 𝔅 : X.oc) :=
(func : 𝔄.ι → 𝔅.ι)
(is_inj : function.injective func)
(is_refinement : ∀ i : 𝔄.ι, 𝔄.cover i ≤ 𝔅.cover (func i))

def refines.refl (𝔄 : X.oc) : refines 𝔄 𝔄 :=
{ func := id,
  is_inj := function.injective_id,
  is_refinement := λ i, le_refl _ }

def refines.trans {𝔄 𝔅 ℭ : X.oc} (r1 : refines 𝔄 𝔅) (r2 : refines 𝔅 ℭ) : refines 𝔄 ℭ :=
{ func := r2.func ∘ r1.func,
  is_inj := function.injective.comp (r2.is_inj) (r1.is_inj),
  is_refinement := λ i, le_trans (r1.is_refinement i) (r2.is_refinement $ r1.func i) }

instance : has_le X.oc :=
{ le := λ 𝔄 𝔅, nonempty (refines 𝔄 𝔅) }

instance : has_lt X.oc :=
{ lt := λ 𝔄 𝔅, 𝔄 ≤ 𝔅 ∧ ¬ 𝔅 ≤ 𝔄 }

instance : has_bot X.oc :=
{ bot := 
  { ι := punit,
    wo := ⟨{ apply := λ x, by { cases x, fconstructor, rintros ⟨-⟩ r, exfalso, simpa using r } }⟩,
    cover := λ _, ⊤,
    is_cover := by simp } }

instance : preorder X.oc :=
{ le := (≤),
  lt := (<),
  le_refl := λ x, nonempty.intro $ refines.refl _,
  le_trans := λ _ _ _ ⟨r1⟩ ⟨r2⟩, ⟨r1.trans r2⟩,
  lt_iff_le_not_le := λ _ _, ⟨id, id⟩ }

end oc

end Top