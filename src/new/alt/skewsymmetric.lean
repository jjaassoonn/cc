import new.unordered.d
import new.unordered.C

open topological_space Top Top.sheaf
open category_theory
open opposite

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)

section C_alt

variables {𝓕 U}
def C.pre.is_skewsymmetric {n : ℕ} (f : C.pre 𝓕 U n) : Prop :=
∀ (i j : fin n) (α : fin n → U.ι),
  f α =
  𝓕.1.map (eq_to_hom (face.swap_eq α i j)).op (- f (swap i j α))

def C.pre.is_skewsymmetric' {n : ℕ} (f : C.pre 𝓕 U n) : Prop :=
∀ (i j : fin n) (α : fin n → U.ι),
  f (swap i j α) =
  - 𝓕.1.map (eq_to_hom (face.swap_eq α i j).symm).op (f α)

lemma is_skewsymmetric_iff_is_skewsymmetric' {n} (f : C.pre 𝓕 U n) :
  C.pre.is_skewsymmetric f ↔ C.pre.is_skewsymmetric' f :=
{ mp := λ h i j α, begin
    specialize h i j α,
    rw [h, map_neg, map_neg, neg_neg, ← comp_apply, ← 𝓕.1.map_comp, ← op_comp, eq_to_hom_trans, eq_to_hom_refl],
    simp,
  end,
  mpr := λ h i j α, begin
    specialize h i j α,
    rw [h, neg_neg, ← comp_apply, ← 𝓕.1.map_comp, ← op_comp, eq_to_hom_trans, eq_to_hom_refl],
    simp
  end }

end C_alt

def C_alt.pre (n : ℕ) : add_subgroup (C 𝓕 U n) :=
{ carrier := { f : C.pre 𝓕 U n | f.is_skewsymmetric ∧ ∀ (α : fin n → U.ι), ¬ function.injective α → f α = 0},
  add_mem' := λ f g hf hg, begin
    rcases hf with ⟨hf1, hf2⟩,
    rcases hg with ⟨hg1, hg2⟩,
    split,
    intros i j α,
    change f α + g α = 𝓕.1.map _ (- (f _ + g _)),
    rw [map_neg, map_add, hf1 i j, hg1 i j, map_neg, map_neg, neg_add],
    

    intros α ha,
    change f α + g α = 0,
    rw [hf2, hg2, add_zero];
    assumption,
  end,
  zero_mem' := begin
    split,
    intros i j α,
    simp only [C_pre.zero_apply, neg_zero, map_zero],

    intros α ha,
    simp,
  end,
  neg_mem' := λ f ⟨hf1, hf2⟩, begin
    split,
    intros i j α,
    simp only [C_pre.neg_apply],
    rw neg_neg,
    rw hf1 i j,
    simp only [map_neg, neg_neg],

    intros α ha,
    change - (f α) = 0,
    rw hf2 _ ha,
    rw neg_zero,
  end }

def C_alt (n : ℕ) : Ab := AddCommGroup.of $ C_alt.pre 𝓕 U n

def d_alt (n : ℕ) : C_alt 𝓕 U n ⟶ C_alt 𝓕 U (n + 1) :=
{ to_fun := λ f, ⟨d 𝓕 U n f.1, sorry⟩,
  map_zero' := begin
    rw subtype.ext_iff_val,
    simp,
  end,
  map_add' := begin
    rintros ⟨f, hf⟩ ⟨g, hg⟩,
    rw subtype.ext_iff_val,
    simp,
  end }

lemma d_alt_d_alt_eq_zero (n : ℕ) :
  d_alt 𝓕 U n ≫ d_alt 𝓕 U (n + 1) = 0 :=
begin
  ext f α,
  rw [comp_apply],
  simp only [AddCommGroup.zero_apply, add_subgroup.coe_zero, C_pre.zero_apply],
  convert dd_eq_zero 𝓕 U n f.1 α,
end