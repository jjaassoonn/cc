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

open_locale big_operators

universe u
variables {X : Top.{u}} (ð : sheaf Ab X) (U : X.oc)

namespace computing_homotopy

variables {ð U}

def unordered_to_ordered.to_fun (n : â) :
  C ð U n â C_o ð U n :=
Î» f Ï, f Ï.to_fun

def unordered_to_ordered (n : â) :
  C ð U n â¶ C_o ð U n :=
{ to_fun := unordered_to_ordered.to_fun n,
  map_zero' := rfl,
  map_add' := Î» _ _, rfl }

def chain_unordered_to_ordered :
  Cech_complex_wrt_cover_unordered ð U â¶
  Cech_complex_wrt_cover_ordered   ð U :=
{ f := Î» n, unordered_to_ordered (n+1),
  comm' := Î» i j (h : _ + 1 = _), begin
    subst h,
    ext f Î±,
    -- change unordered_to_ordered.to_fun (i + 1) â« _ = _,
    rw [comp_apply, comp_apply, unordered_to_ordered, add_monoid_hom.coe_mk, 
      unordered_to_ordered, add_monoid_hom.coe_mk, unordered_to_ordered.to_fun,
      unordered_to_ordered.to_fun],
    simp only,
    erw d_o_to_succ,
    erw d_to_succ,
    rw dd_o_aux.d_o_def,
    rw dd_aux.d_def,
    rw finset.sum_congr rfl,
    rintros â¨k, hkâ© -,
    split_ifs,
    { rw [id], refl, },
    { refl, },
  end }

def vec2vec_o_of_inj.to_fun {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) : fin n â U.Î¹ :=
let Î² := finset.order_iso_of_fin (finset.image Î± finset.univ) 
  (show (finset.image Î± finset.univ).card = n, begin
    rw finset.card_image_eq_iff_inj_on.mpr,
    rw finset.card_univ,
    rw fintype.card_fin,
    apply set.inj_on_of_injective,
    assumption
  end) in
(Î» x, x.1 : finset.image Î± finset.univ â U.Î¹) â Î².to_fun

lemma vec2vec_o_of_inj.to_fun_mem {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) (i : fin n) :
  vec2vec_o_of_inj.to_fun h i â finset.image Î± finset.univ := finset.mem_image.mpr $
begin
  dunfold vec2vec_o_of_inj.to_fun,
  simp only [finset.mem_univ, subtype.val_eq_coe, order_iso.to_fun_eq_coe, 
    function.comp_app, finset.coe_order_iso_of_fin_apply, exists_true_left],
  generalize_proofs card_eq,
  sorry
end

lemma vec2vec_o_of_inj.is_strict_mono {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) :
  strict_mono (vec2vec_o_of_inj.to_fun h) := Î» i j ineq,
begin
  rw vec2vec_o_of_inj.to_fun,
  simp only,
  rw function.comp_apply,
  rw function.comp_apply,
  simpa only [order_iso.to_fun_eq_coe, subtype.val_eq_coe, finset.coe_order_iso_of_fin_apply, order_embedding.lt_iff_lt],
end

def vec2vec_o_of_inj {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) : vec_o U n :=
{ to_fun := vec2vec_o_of_inj.to_fun h,
  is_strict_mono := vec2vec_o_of_inj.is_strict_mono h }

lemma vec2vec_o_of_inj.mem_image {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) (i : fin n) :
  vec2vec_o_of_inj h i â finset.image Î± finset.univ :=
vec2vec_o_of_inj.to_fun_mem h i


lemma face.vec2vec_o_eq {n} {Î± : fin n â U.Î¹} (h : function.injective Î±) :
  face Î± = 
  face_o (vec2vec_o_of_inj h) := 
opens.ext $ set.ext $ Î» p,
begin
  erw [opens.mem_coe, opens.mem_coe, opens.fintype_infi, opens.mem_coe, opens.fintype_infi],
  split;
  intros hp i,
  { rcases finset.mem_image.mp (vec2vec_o_of_inj.mem_image h i) with â¨j, _, hjâ©,
    specialize hp j,
    rw hj at hp,
    exact hp, },
  { sorry },
end

def ordered_to_unordered.to_fun (n : â) :
  C_o ð U n â C ð U n := Î» f Î±, 
dite (function.injective Î±)
(Î» h, match signature Î± with
  | sign.zero := 0 -- this will never occur
  | sign.pos := ð.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  | sign.neg := - ð.1.map (eq_to_hom (face.vec2vec_o_eq h)).op (f (vec2vec_o_of_inj h))
  end)
(Î» _, 0)

def ordered_to_unordered (n : â) :
  C_o ð U n â¶ C ð U n :=
{ to_fun := ordered_to_unordered.to_fun n,
  map_zero' := sorry,
  map_add' := sorry }

def chain_ordered_to_unordered :
  Cech_complex_wrt_cover_ordered   ð U â¶
  Cech_complex_wrt_cover_unordered ð U :=
{ f := Î» n, ordered_to_unordered (n + 1),
  comm' := sorry }

end computing_homotopy

def chain_unordered_homotopically_equivalent_ordered :
  homotopy_equiv
    (Cech_complex_wrt_cover_unordered ð U)
    (Cech_complex_wrt_cover_ordered ð U) 
    := 
{ hom := computing_homotopy.chain_unordered_to_ordered,
  inv := computing_homotopy.chain_ordered_to_unordered,
  homotopy_hom_inv_id := sorry,
  homotopy_inv_hom_id := sorry }

def cohomology_unordered_eq_ordered (n : â) :
  Cech_Cohomology_Group_wrt_cover_unordered_nth ð U n â
  Cech_Cohomology_Group_wrt_cover_ordered_nth ð U n :=
@homology_obj_iso_of_homotopy_equiv 
  â Ab _ _ (complex_shape.up â)
  (Cech_complex_wrt_cover_unordered ð U)
  (Cech_complex_wrt_cover_ordered ð U)
  _ _ _ _ (abelian.has_zero_object)
  (chain_unordered_homotopically_equivalent_ordered ð U)
  n


def example1 : 
  Cech_Cohomology_Group_wrt_cover_unordered_nth ð U 0 â 
  ð.1.obj (op â¤) :=
cohomology_unordered_eq_ordered ð U 0 âªâ« zeroth_Cech_Cohomology ð U


end