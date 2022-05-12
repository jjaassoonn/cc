import new.C

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

def C_alt (n : ℕ) : Type* :=
{ f : C.pre 𝓕 U n // f.is_skewsymmetric ∧ ∀ (α : fin n → U.ι), ¬ function.injective α → f α = 0}

namespace C_alt

variables (n : ℕ)

@[ext]
lemma ext_val {f g : C_alt 𝓕 U n} (eq1 : f.1 = g.1) :
  f = g := subtype.ext_val eq1

instance : has_add (C_alt 𝓕 U n) :=
{ add := λ f g,
  ⟨f.1 + g.1, begin
    split,
    intros i j α,
    change f.1 α + g.1 α = 𝓕.1.map _ (- (f.1 _ + g.1 _)),
    rw [map_neg, map_add, f.2.1 i j, g.2.1 i j, map_neg, map_neg, neg_add],

    intros α ha,
    change f.1 α + g.1 α = 0,
    rw [f.2.2, g.2.2, add_zero];
    assumption,
  end⟩ }

instance : has_zero (C_alt 𝓕 U n) :=
{ zero := 
  ⟨0, begin
    split,
    intros i j α,
    simp only [C_pre.zero_apply, neg_zero, map_zero],

    intros α ha,
    simp,
  end⟩ }

instance : has_scalar ℕ (C_alt 𝓕 U n) :=
{ smul := λ m f, ⟨m • f.1, begin
    split,
    intros i j α,
    simp only [C_pre.nsmul_apply, eq_to_hom_op, eq_to_hom_map, map_neg, map_nsmul],
    rw f.2.1 i j,
    simp only [eq_to_hom_op, eq_to_hom_map, map_neg, neg_nsmul],

    intros α ha,
    change m • f.1 α = 0,
    rw f.2.2 _ ha,
    simp,
  end⟩ }

instance : add_comm_monoid (C_alt 𝓕 U n) :=
{ add := (+),
  add_assoc := λ a b c, begin
    ext,
    change (a.1 + b.1 + c.1) _ = (a.1 + (b.1 + c.1)) _,
    simp only [C_pre.add_apply],
    rw add_assoc,
  end,
  zero := 0,
  zero_add := λ f, begin
    ext,
    change (0 + f.1) _ = _,
    simp only [C_pre.add_apply, C_pre.zero_apply, zero_add],
  end,
  add_zero := λ f, begin
    ext,
    change (f.1 + 0) _ = _,
    simp only [C_pre.add_apply, C_pre.zero_apply, add_zero],
  end,
  nsmul := (•),
  nsmul_zero' := λ f, begin
    ext,
    change 0 • f.1 _ = 0,
    rw zero_smul,
  end,
  nsmul_succ' := λ m f, begin
    ext,
    change (m + 1) • f.1 x = (f.1 + m • f.1) x,
    rw [add_smul, one_smul, C_pre.add_apply, add_comm],
    refl,
  end,
  add_comm := λ f g, begin
    ext,
    change (f.1 + g.1) x = (g.1 + f.1) x,
    simp only [add_comm, C_pre.add_apply],
  end }

instance : add_comm_group (C_alt 𝓕 U n) :=
{ neg := λ f, ⟨-f.1, begin
    split,
    intros i j α,
    simp only [C_pre.neg_apply],
    rw neg_neg,
    rw f.2.1 i j,
    simp only [map_neg, neg_neg],

    intros α ha,
    change - (f.1 α) = 0,
    rw f.2.2 _ ha,
    rw neg_zero,
  end⟩,
  add_left_neg := λ f, begin
    ext,
    change (-f.1 + f.1) x = 0,
    simp,
  end,
  ..C_alt.add_comm_monoid 𝓕 U n }

end C_alt