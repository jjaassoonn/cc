import new.unordered.chain
import new.ordered.chain_o
-- import algebra.category.Group.abelian
import algebra.homology.homotopy

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open opposite
open AddCommGroup (hiding has_zero_object)

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)

namespace computing_homotopy

variables {𝓕 U}

def unordered_to_ordered.to_fun (n : ℕ) :
  C 𝓕 U n → C_o 𝓕 U n :=
λ f σ, f σ.to_fun

def unordered_to_ordered (n : ℕ) :
  C 𝓕 U n ⟶ C_o 𝓕 U n :=
{ to_fun := unordered_to_ordered.to_fun n,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

def chain_unordered_to_ordered :
  Cech_complex_wrt_cover_unordered 𝓕 U ⟶
  Cech_complex_wrt_cover_ordered   𝓕 U :=
{ f := λ n, unordered_to_ordered (n+1),
  comm' := sorry }

def vec2vec_o_of_inj.to_fun {n} {α : fin n → U.ι} (h : function.injective α) : fin n → U.ι :=
let β := finset.order_iso_of_fin (finset.image α finset.univ) 
  (show (finset.image α finset.univ).card = n, begin
    rw finset.card_image_eq_iff_inj_on.mpr,
    rw finset.card_univ,
    rw fintype.card_fin,
    apply set.inj_on_of_injective,
    assumption
  end) in
(λ x, x.1 : finset.image α finset.univ → U.ι) ∘ β.to_fun

lemma vec2vec_o_of_inj.is_strict_mono {n} {α : fin n → U.ι} (h : function.injective α) :
  strict_mono (vec2vec_o_of_inj.to_fun h) := λ i j ineq,
begin
  rw vec2vec_o_of_inj.to_fun,
  simp only,
  rw function.comp_apply,
  rw function.comp_apply,
  simpa only [order_iso.to_fun_eq_coe, subtype.val_eq_coe, finset.coe_order_iso_of_fin_apply, order_embedding.lt_iff_lt],
end

def vec2vec_o_of_inj {n} {α : fin n → U.ι} (h : function.injective α) : vec_o U n :=
{ to_fun := vec2vec_o_of_inj.to_fun h,
  is_strict_mono := vec2vec_o_of_inj.is_strict_mono h }

lemma face.vec2vec_o_eq {n} {α : fin n → U.ι} (h : function.injective α) :
  face α = 
  face_o (vec2vec_o_of_inj h) :=
sorry

def ordered_to_unordered.to_fun (n : ℕ) :
  C_o 𝓕 U n → C 𝓕 U n := λ f α, 
dite (function.injective α)
(λ h, match signature α with
  | sign.zero := 0 -- this will never occur
  | sign.pos := 𝓕.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  | sign.neg := - 𝓕.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  end)
(λ _, 0)

def ordered_to_unordered (n : ℕ) :
  C_o 𝓕 U n ⟶ C 𝓕 U n :=
{ to_fun := ordered_to_unordered.to_fun n,
  map_zero' := sorry,
  map_add' := sorry }

def chain_ordered_to_unordered :
  Cech_complex_wrt_cover_ordered   𝓕 U ⟶
  Cech_complex_wrt_cover_unordered 𝓕 U :=
{ f := λ n, ordered_to_unordered (n + 1),
  comm' := sorry }

end computing_homotopy

def chain_unordered_homotopically_equivalent_ordered :
  homotopy_equiv
    (Cech_complex_wrt_cover_unordered 𝓕 U)
    (Cech_complex_wrt_cover_ordered 𝓕 U) 
    := 
{ hom := computing_homotopy.chain_unordered_to_ordered,
  inv := computing_homotopy.chain_ordered_to_unordered,
  homotopy_hom_inv_id := sorry,
  homotopy_inv_hom_id := sorry }

def cohomology_unordered_eq_ordered (n : ℕ) :
  Cech_Cohomology_Group_wrt_cover_unordered_nth 𝓕 U n ≅
  Cech_Cohomology_Group_wrt_cover_ordered_nth 𝓕 U n :=
@homology_obj_iso_of_homotopy_equiv 
  ℕ Ab _ _ (complex_shape.up ℕ)
  (Cech_complex_wrt_cover_unordered 𝓕 U)
  (Cech_complex_wrt_cover_ordered 𝓕 U)
  _ _ _ _ (abelian.has_zero_object)
  (chain_unordered_homotopically_equivalent_ordered 𝓕 U)
  n


def example1 : 
  Cech_Cohomology_Group_wrt_cover_unordered_nth 𝓕 U 0 ≅ 
  𝓕.1.obj (op ⊤) :=
cohomology_unordered_eq_ordered 𝓕 U 0 ≪≫ zeroth_Cech_Cohomology 𝓕 U


end