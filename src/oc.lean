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
(cover : ι → opens.{u} X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover

variables {X} 
/--
A cover `𝔄` refines a cover `𝔅` if there is a function `f` between their indexing sets such that
for all `i` in indexing set of `𝔄`, `𝔄ᵢ ⊆ 𝔅_{f i}`
-/
@[ext] structure refines (𝔄 𝔅 : X.oc) :=
(func : 𝔄.ι → 𝔅.ι)
(strict_mono : strict_mono func)
(is_inj : function.injective func)
(is_refinement : ∀ i : 𝔄.ι, 𝔄.cover i ≤ 𝔅.cover (func i))

def refines.refl (𝔄 : X.oc) : refines 𝔄 𝔄 :=
{ func := id,
  strict_mono := strict_mono_id,
  is_inj := function.injective_id,
  is_refinement := λ i, le_refl _ }

def refines.trans {𝔄 𝔅 ℭ : X.oc} (r1 : refines 𝔄 𝔅) (r2 : refines 𝔅 ℭ) : refines 𝔄 ℭ :=
{ func := r2.func ∘ r1.func,
  is_inj := function.injective.comp (r2.is_inj) (r1.is_inj),
  strict_mono := strict_mono.comp (r2.strict_mono) (r1.strict_mono),
  is_refinement := λ i, le_trans (r1.is_refinement i) (r2.is_refinement $ r1.func i) }

-- instance : has_le X.oc :=
-- { le := λ 𝔄 𝔅, nonempty (refines 𝔄 𝔅) }

-- instance : has_lt X.oc :=
-- { lt := λ 𝔄 𝔅, 𝔄 ≤ 𝔅 ∧ ¬ 𝔅 ≤ 𝔄 }

instance : has_bot X.oc :=
{ bot := 
  { ι := punit,
    wo := ⟨{ apply := λ x, by { cases x, fconstructor, rintros ⟨-⟩ r, exfalso, simpa using r } }⟩,
    cover := λ _, ⊤,
    is_cover := by simp } }

-- instance : preorder X.oc :=
-- { le := (≤),
--   lt := (<),
--   le_refl := λ x, nonempty.intro $ refines.refl _,
--   le_trans := λ _ _ _ ⟨r1⟩ ⟨r2⟩, ⟨r1.trans r2⟩,
--   lt_iff_le_not_le := λ _ _, ⟨id, id⟩ }

instance : category_theory.category X.oc := 
{ hom := λ A B, refines A B,
  id := λ A, refines.refl A,
  comp := λ A B C f g, refines.trans f g,
  id_comp' := λ A B f, by ext; refl,
  comp_id' := λ A B f, by ext; refl,
  assoc' := λ A B C D f g h, by ext; refl }

end Top