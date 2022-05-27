import algebraic_geometry.presheafed_space

open topological_space category_theory opposite
open category_theory.limits

namespace algebraic_geometry

universes v u

variables {C : Type u} [category.{v} C]

class PresheafedSpace.is_closed_immersion {X Y : PresheafedSpace C}
  (f : X ⟶ Y) :=
(closed_image : ∃ (s : set Y) (f : X ≃ₜ s), is_closed s)
-- (surj : function.surjective )

end algebraic_geometry