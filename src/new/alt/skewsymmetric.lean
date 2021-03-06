import new.unordered.d
import new.unordered.C

open topological_space Top Top.sheaf
open category_theory
open opposite

universe u
variables {X : Top.{u}} (ð : sheaf Ab X) (U : X.oc)

section C_alt

variables {ð U}
def C.pre.is_skewsymmetric {n : â} (f : C.pre ð U n) : Prop :=
â (i j : fin n) (Î± : fin n â U.Î¹),
  f Î± =
  ð.1.map (eq_to_hom (face.swap_eq Î± i j)).op (- f (swap i j Î±))

def C.pre.is_skewsymmetric' {n : â} (f : C.pre ð U n) : Prop :=
â (i j : fin n) (Î± : fin n â U.Î¹),
  f (swap i j Î±) =
  - ð.1.map (eq_to_hom (face.swap_eq Î± i j).symm).op (f Î±)

lemma is_skewsymmetric_iff_is_skewsymmetric' {n} (f : C.pre ð U n) :
  C.pre.is_skewsymmetric f â C.pre.is_skewsymmetric' f :=
{ mp := Î» h i j Î±, begin
    specialize h i j Î±,
    rw [h, map_neg, map_neg, neg_neg, â comp_apply, â ð.1.map_comp, â op_comp, eq_to_hom_trans, eq_to_hom_refl],
    simp,
  end,
  mpr := Î» h i j Î±, begin
    specialize h i j Î±,
    rw [h, neg_neg, â comp_apply, â ð.1.map_comp, â op_comp, eq_to_hom_trans, eq_to_hom_refl],
    simp
  end }

end C_alt

def C_alt.pre (n : â) : add_subgroup (C ð U n) :=
{ carrier := { f : C.pre ð U n | f.is_skewsymmetric â§ â (Î± : fin n â U.Î¹), Â¬ function.injective Î± â f Î± = 0},
  add_mem' := Î» f g hf hg, begin
    rcases hf with â¨hf1, hf2â©,
    rcases hg with â¨hg1, hg2â©,
    split,
    intros i j Î±,
    change f Î± + g Î± = ð.1.map _ (- (f _ + g _)),
    rw [map_neg, map_add, hf1 i j, hg1 i j, map_neg, map_neg, neg_add],
    

    intros Î± ha,
    change f Î± + g Î± = 0,
    rw [hf2, hg2, add_zero];
    assumption,
  end,
  zero_mem' := begin
    split,
    intros i j Î±,
    simp only [C_pre.zero_apply, neg_zero, map_zero],

    intros Î± ha,
    simp,
  end,
  neg_mem' := Î» f â¨hf1, hf2â©, begin
    split,
    intros i j Î±,
    simp only [C_pre.neg_apply],
    rw neg_neg,
    rw hf1 i j,
    simp only [map_neg, neg_neg],

    intros Î± ha,
    change - (f Î±) = 0,
    rw hf2 _ ha,
    rw neg_zero,
  end }

def C_alt (n : â) : Ab := AddCommGroup.of $ C_alt.pre ð U n

def d_alt (n : â) : C_alt ð U n â¶ C_alt ð U (n + 1) :=
{ to_fun := Î» f, â¨d ð U n f.1, sorryâ©,
  map_zero' := begin
    rw subtype.ext_iff_val,
    simp,
  end,
  map_add' := begin
    rintros â¨f, hfâ© â¨g, hgâ©,
    rw subtype.ext_iff_val,
    simp,
  end }

lemma d_alt_d_alt_eq_zero (n : â) :
  d_alt ð U n â« d_alt ð U (n + 1) = 0 :=
begin
  ext f Î±,
  rw [comp_apply],
  simp only [AddCommGroup.zero_apply, add_subgroup.coe_zero, C_pre.zero_apply],
  convert dd_eq_zero ð U n f.1 Î±,
end