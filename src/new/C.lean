import topology.sheaves.sheaf
import algebra.category.Group.limits
import oc
import lemmas.about_opens

section

open topological_space Top Top.sheaf
open category_theory
open opposite

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)

section

variables {U}

def swap {n : ℕ} (i j : fin n) (α : fin n → U.ι) : fin n → U.ι :=
λ k, if (k = i) 
  then α j
  else if (k = j)
    then α i
    else α k


namespace swap

variables {U} {n : ℕ} (α : fin n → U.ι)

@[simp]
lemma same (i : fin n) :
  swap i i α = α :=
begin
  ext,
  change ite _ _ _ = _,
  split_ifs,
  { subst h, },
  { refl, }
end

@[simp]
lemma symmetric (i j : fin n) :
  swap i j α = swap j i α :=
begin
  ext,
  change ite _ _ _ = ite _ _ _,
  split_ifs with h1 h2,
  { subst h1,
    subst h2, },
  { subst h1, },
  { subst h, },
  { refl, },
end

@[simp]
lemma twice (i j : fin n) :
  swap i j (swap i j α) = α :=
begin
  ext,
  change ite _ _ _ = _,
  split_ifs with h1,
  { change ite _ _ _ = _,
    split_ifs with h2,
    { subst h2, subst h1, },
    { subst h1, }, },
  { change ite _ _ _ = _,
    rw if_pos rfl,
    subst h, },
  { change ite _ _ _ = _,
    split_ifs,
    refl, },
end

lemma apply1 (i j : fin n) :
  swap i j α i = α j :=
begin
  change ite _ _ _ = _,
  rw if_pos rfl,
end

lemma apply2 (i j : fin n) :
  swap i j α j = α i :=
begin
  change ite _ _ _ = _,
  rw if_pos rfl,
  split_ifs,
  { subst h, },
  { refl, }
end

lemma apply_ne (i j k : fin n)
  (ineq1 : k ≠ i)
  (ineq2 : k ≠ j) :
  swap i j α k = α k :=
begin
  change ite _ _ _ = _,
  rw [if_neg, if_neg];
  assumption,
end

end swap

def face {n : ℕ} (α : fin n → U.ι) : opens X :=
  infi (λ (k : fin n), U.cover $ α k)

section face

lemma face.congr {n : ℕ} {α β : fin n → U.ι} (h : α = β) :
  face α = face β :=
by subst h

lemma face.swap_eq {n : ℕ} (α : fin n → U.ι) (i j : fin n) :
  face α = face (swap i j α) :=
begin
  change infi _ = infi _,
  refine le_antisymm _ _,
  { rw le_infi_iff,
    intros k,
    by_cases k = i,
    { subst h,
      by_cases k = j,
      { subst h,
        rw _root_.swap.same α k,
        intros p hp,
        erw opens.fintype_infi at hp,
        apply hp, },
      { rw _root_.swap.apply1,
        intros p hp,
        erw opens.fintype_infi at hp,
        apply hp, }, },
      { by_cases k = j,
        { subst h,
          rw _root_.swap.apply2,
          intros p hp,
          erw opens.fintype_infi at hp,
          apply hp, },
        { rw _root_.swap.apply_ne,
          intros p hp,
          erw opens.fintype_infi at hp,
          apply hp,
          assumption,
          assumption, }, }, },
  { intros p hp,
    erw opens.fintype_infi at hp ⊢,
    intros k,
    by_cases h1 : k = i,
    { subst h1,
      by_cases h2 : k = j,
      { subst j,
        rw _root_.swap.same at hp,
        apply hp, },
      { specialize hp j,
        rwa _root_.swap.apply2 at hp, }, },
    { by_cases h2 : k = j,
      { subst h2,
        specialize hp i,
        rwa _root_.swap.apply1 at hp, },
      { specialize hp k,
        rwa _root_.swap.apply_ne at hp,
        assumption,
        assumption }, }, }
end

end face


end

def C.pre (n : ℕ) : Type* :=
Π (α : fin n → U.ι), 𝓕.1.obj (op $ face α)

namespace C_pre

variable {n : ℕ}
variables {𝓕 U}

instance : has_add (C.pre 𝓕 U n) :=
{ add := λ f g α, f α + g α }

@[simp] lemma add_apply (f g : C.pre 𝓕 U n) (α : fin n → U.ι) :
  (f + g) α = f α + g α := rfl

instance : has_zero (C.pre 𝓕 U n) :=
{ zero := λ α, 0 }

@[simp]
lemma zero_apply (α : fin n → U.ι) :
  (0 : C.pre 𝓕 U n) α = 0 := rfl

instance : has_scalar ℕ (C.pre 𝓕 U n) :=
{ smul := λ n f α, n • f α }

@[simp]
lemma nsmul_apply (f : C.pre 𝓕 U n) (α : fin n → U.ι) (m : ℕ) :
  (m • f) α = m • f α := rfl

instance : add_comm_monoid (C.pre 𝓕 U n) :=
{ add := (+),
  add_assoc := λ a b c, by ext; simp [add_assoc],
  zero := 0,
  zero_add := λ f, by ext; simp,
  add_zero := λ f, by ext; simp,
  nsmul := (•),
  nsmul_zero' := λ f, by ext; simp,
  nsmul_succ' := λ m f, begin
    ext,
    simp [nat.succ_eq_add_one, add_smul, add_comm],
  end,
  add_comm := λ f g, by ext; simp [add_comm] }

instance : add_comm_group (C.pre 𝓕 U n) :=
{ neg := λ f α, - f α,
  add_left_neg := λ f, by ext; simp,
  ..(_ : add_comm_monoid (C.pre 𝓕 U n))}

@[simp]
lemma neg_apply (f : C.pre 𝓕 U n) (α : fin n → U.ι) :
  (-f) α = - (f α) := rfl

end C_pre

section

variables {𝓕 U}
def C.pre.is_skewsymmetric {n : ℕ} (f : C.pre 𝓕 U n) : Prop :=
∀ (i j : fin n) (α : fin n → U.ι),
  f α =
  𝓕.1.map (eq_to_hom (face.swap_eq α i j)).op (- f (swap i j α))

end

def C (n : ℕ) : Type* :=
{ f : C.pre 𝓕 U n // f.is_skewsymmetric }

namespace C

variables (n : ℕ)

@[ext]
lemma ext_val {f g : C 𝓕 U n} (eq1 : f.1 = g.1) :
  f = g := subtype.ext_val eq1

instance : has_add (C 𝓕 U n) :=
{ add := λ f g,
  ⟨f.1 + g.1, λ i j α, begin
    change f.1 α + g.1 α = 𝓕.1.map _ (- (f.1 _ + g.1 _)),
    rw [map_neg, map_add, f.2 i j, g.2 i j, map_neg, map_neg, neg_add],
  end⟩ }

instance : has_zero (C 𝓕 U n) :=
{ zero := 
  ⟨0, λ i j α, begin
    simp only [C_pre.zero_apply, neg_zero, map_zero],
  end⟩ }

instance : has_scalar ℕ (C 𝓕 U n) :=
{ smul := λ m f, ⟨m • f.1, λ i j α, begin
    simp only [C_pre.nsmul_apply, eq_to_hom_op, eq_to_hom_map, map_neg, map_nsmul],
    rw f.2 i j,
    simp only [eq_to_hom_op, eq_to_hom_map, map_neg, neg_nsmul],
  end⟩ }

instance : add_comm_monoid (C 𝓕 U n) :=
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

instance : add_comm_group (C 𝓕 U n) :=
{ neg := λ f, ⟨-f.1, λ i j α, begin
    simp only [C_pre.neg_apply],
    rw neg_neg,
    rw f.2 i j,
    simp only [map_neg, neg_neg],
  end⟩,
  add_left_neg := λ f, begin
    ext,
    change (-f.1 + f.1) x = 0,
    simp,
  end,
  ..add_comm_monoid 𝓕 U n }

end C

end