import topology.sheaves.sheaf
import algebra.category.Group.limits
import oc
import lemmas.about_opens
import group_theory.perm.sign
import tactic

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open opposite

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)

section

variables {U}

def ignore {n : ℕ} (α : fin (n + 1) → U.ι) (i : fin (n + 1)) :
  fin n → U.ι :=
λ k, dite (k.1 < i.1)
  (λ ineq1, α ⟨k.1, lt_trans ineq1 i.2⟩)
  (λ ineq1, α ⟨k.1.pred, begin
    rw nat.lt_succ_iff,
    refine le_of_lt _,
    exact lt_of_le_of_lt (nat.pred_le _) k.2,
  end⟩)

def ignore₂ {n : ℕ} (α : fin (n + 2) → U.ι) (i : fin (n + 2)) (j : fin (n + 1)) :
  fin n → U.ι :=
ignore (ignore α i) j

lemma ignore.apply_lt {n : ℕ} (α : fin (n + 1) → U.ι) (i : fin (n + 1))
  {k : fin n} (ineq1 : k.1 < i.1) :
  ignore α i k = α ⟨k.1, lt_trans ineq1 i.2⟩ :=
dif_pos ineq1

lemma ignore.apply_not_lt {n : ℕ} (α : fin (n + 1) → U.ι) (i : fin (n + 1))
  {k : fin n} (ineq1 : ¬ k.1 < i.1) :
  ignore α i k = α ⟨k.1.pred, begin
    rw nat.lt_succ_iff,
    refine le_of_lt _,
    exact lt_of_le_of_lt (nat.pred_le _) k.2,
  end⟩ :=
dif_neg ineq1

lemma ignore.apply_ite {n : ℕ} (α : fin (n + 1) → U.ι) (i : fin (n + 1))
  (k : fin n) :
  ignore α i k =
  dite (k.1 < i.1)
    (λ ineq1, α ⟨k.1, lt_trans ineq1 i.2⟩)
    (λ ineq1, α ⟨k.1.pred, begin
      rw nat.lt_succ_iff,
      refine le_of_lt _,
      exact lt_of_le_of_lt (nat.pred_le _) k.2,
    end⟩) := rfl

/--

a0, a1, ..., ai, ..., aj, ...., a(n+2)

                                                j-1th  jth
ignore α i = a0, a1, ...., a(i-1), a(i+1), .... aj,   a(j+1) ...., a(n+2)
ignore α (ignore α i) j = a0, a1, ..., a(i-1), a(i+1), ..., aj, a(j+2), ... a(n+2)

so ignore₂ α i j = ignore₂ α (j + 1) i

-/
lemma ignore₂_symm {n : ℕ} (α : fin (n + 2) → U.ι) 
  (i : fin (n + 2))
  (j : fin (n + 1))
  (h : i.1 ≤ j.1) :
  ignore₂ α ⟨j.1 + 1, nat.succ_lt_succ_iff.mpr j.2⟩ ⟨i.1, lt_of_le_of_lt h j.2⟩ = ignore₂ α i j :=
begin
  sorry
end

lemma ignore₂_symm' {n : ℕ} (α : fin (n + 2) → U.ι)
  {i : ℕ} (hi : i ∈ finset.range n.succ)
  {j : ℕ} (hj : j ∈ finset.Ico i n.succ) :
  ignore₂ α ⟨j + 1, begin
    rw finset.mem_Ico at hj,
    rw nat.succ_lt_succ_iff,
    exact hj.2
  end⟩ ⟨i, finset.mem_range.mp hi⟩ = ignore₂ α ⟨i, lt_trans (finset.mem_range.mp hi) (lt_add_one _)⟩ ⟨j, (finset.mem_Ico.mp hj).2⟩ :=
begin
  convert ignore₂_symm α i j _;
  sorry
end

@[derive [decidable_eq]]
inductive sign
| neg
| zero
| pos

def unit_to_sign (n : ℤˣ) : sign :=
if n = 1 then sign.pos else sign.neg

def signature.order_aux {n : ℕ} {α : fin n → U.ι} (inj : function.injective α) :
  fin n ≃o finset.image α finset.univ :=
finset.order_iso_of_fin _ begin
  rw finset.card_image_of_injective _ inj,
  exact finset.card_fin n,
end

def signature.restrict_aux {n : ℕ} {α : fin n → U.ι} (inj : function.injective α) :
  fin n ≃ finset.image α finset.univ :=
equiv.of_bijective (λ k, ⟨α k, finset.mem_image.mpr ⟨k, finset.mem_univ _, rfl⟩⟩) begin
  split,
  { intros a b h,
    simp only [subtype.mk_eq_mk] at h,
    apply_fun α,
    exact h, },
  { rintros ⟨i, hi⟩,
    rw finset.mem_image at hi,
    rcases hi with ⟨j, _, rfl⟩,
    use j, }
end

def signature.equiv {n : ℕ} {α : fin n → U.ι} (inj : function.injective α) :
  fin n ≃ fin n :=
{ to_fun := function.comp (signature.order_aux inj).symm (signature.restrict_aux inj),
  inv_fun := function.comp (signature.restrict_aux inj).symm (signature.order_aux inj),
  left_inv := λ k, by simp,
  right_inv := λ k, by simp }

def signature {n : ℕ} (α : fin n → U.ι) : sign :=
dite (function.injective α)
(λ inj, unit_to_sign $ equiv.perm.sign (signature.equiv inj))
(λ _, sign.zero)

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

lemma apply1' (i j : fin n) {i' : fin n} (eq1 : i'.1 = i.1) :
  swap i j α i' = α j :=
begin
  convert apply1 α i j,
  rw subtype.ext_iff_val,
  exact eq1,
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

lemma apply2' (i j : fin n) {j' : fin n} (eq1 : j'.1 = j.1) :
  swap i j α j' = α i :=
begin
  convert apply2 α i j,
  rw subtype.ext_iff_val,
  exact eq1,
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

lemma nat.pred_eq_self {n : ℕ} (h : n.pred = n) : n = 0 :=
begin
  induction n with n h1 generalizing h,
  { refl, },
  { rw nat.pred_succ at h,
    exfalso,
    have ineq1 := lt_add_one n,
    rw nat.succ_eq_add_one at h,
    rw ← h at ineq1,
    apply lt_irrefl _ ineq1, },
end

-- If `max i j < k`, then `ignore (swap i j α) k = swap i j (ignore α k)`
-- If `k < min i j`, then `ignore (swap i j α) k = swap (i + 1) (j + 1) (ignore α k)`
-- If `min i j ≤ k ≤ max i j`, then `ignore (swap i j α) k = swap (min i j) ((max i j) - 1) (ignore α k)` or `ignore (swap i j α) k = swap (min i j) (max i j) (ignore α k)`

-- lemma ignore_swap_eq_swap_ignore
--   (α : fin (n + 1) → U.ι)
--   (i j k : fin (n + 1)) :
--   ∃ (i' j' : fin n),
--   ignore (swap i j α) k = swap i' j' (ignore α k) := sorry


-- lemma swap_ignore_gt (α : fin (n+1) → U.ι) (i j k : fin (n+1)) 
--   (ineq1 : max i.1 j.1 < k.1):
--   ignore (swap i j α) k = swap ⟨i.1, begin
--     by_contra r,
--     rw not_lt at r,
--     have ineq2 := i.2,
--     have eq1 : i.1 = n,
--     { linarith, },
--     have ineq3 : n < k.1,
--     { refine lt_of_le_of_lt _ ineq1,
--       simp [← eq1], },
--     have ineq4 := k.2,
--     linarith,
--   end⟩ ⟨j.1, begin
--     by_contra r,
--     rw not_lt at r,
--     have ineq2 := j.2,
--     have eq1 : j.1 = n,
--     { linarith, },
--     have ineq3 : n < k.1,
--     { refine lt_of_le_of_lt _ ineq1,
--       simp [← eq1], },
--     have ineq4 := k.2,
--     linarith,
--   end⟩ (ignore α k) :=
-- begin
--   ext m,
--   by_cases ineq2 : m.1 = i.1;
--   by_cases ineq3 : m.1 = j.1,
--   { -- m = i = j,
--     rw [← ineq2, ← ineq3, max_self] at ineq1,
--     rw ignore.apply_lt,
--     swap, exact ineq1,
--     rw [apply1', apply1', ignore.apply_lt],
--     congr' 1,
--     rw subtype.ext_iff_val,
--     { convert ineq1,
--       rw subtype.ext_iff_val,
--       exact ineq3.symm, },
--     exact ineq2,
--     exact ineq2, },
--   { -- m = i but m ≠ j,
--     rw apply1',
--     swap, exact ineq2,
--     rw ← ineq2 at ineq1,
--     have ineq4 := lt_of_le_of_lt (le_max_left _ _) ineq1,
--     rw ignore.apply_lt,
--     swap, exact ineq4,
--     rw apply1',
--     swap, exact ineq2,
--     rw ignore.apply_lt,
--     swap, exact lt_of_le_of_lt (le_max_right _ _) ineq1,
--     congr' 1,
--     rw subtype.ext_iff_val, },
--   { -- m ≠ i but m = j,
--     rw apply2',
--     swap, exact ineq3,
--     rw ← ineq3 at ineq1,
--     have ineq4 := lt_of_le_of_lt (le_max_right _ _) ineq1,
--     rw ignore.apply_lt,
--     swap, exact ineq4,
--     rw ignore.apply_lt,
--     swap, exact lt_of_le_of_lt (le_max_left _ _) ineq1,
--     rw apply2',
--     swap, exact ineq3,
--     congr' 1,
--     rw subtype.ext_iff_val, },
--   { -- m ≠ i and m ≠ j,
--     rw apply_ne,
--     swap, contrapose! ineq2, rw ineq2,
--     swap, contrapose! ineq3, rw ineq3,
--     rw ignore.apply_ite,
--     rw ignore.apply_ite,
--     split_ifs with ineq4,
--     { rw apply_ne,

--       contrapose! ineq2,
--       rw ← ineq2,

--       contrapose! ineq3,
--       rw ← ineq3, },
--     { by_cases ineq5 : m.1.pred = i.1,
--       { rw apply1',
--         swap, exact ineq5,

--         have EQ : i.1 = j.1,
--         { have ineq0 : m.1 ≠ 0,
--           { intro r,
--             rw r at *,
--             linarith, },
--           have eq0 : m.1 = i.1 + 1,
--           { rw [← ineq5, ← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
--             linarith },
--           rw [eq0, not_lt] at ineq4,
--           have ineq6 : k.1 = i.1 + 1,
--           { have INEQ : i.1 < k.1 := lt_of_le_of_lt (le_max_left _ _) ineq1,
--             linarith },
--           have ineq7 : i.1 ≤ j.1,
--           { have INEQ := lt_of_lt_of_le ineq1 ineq4,
--             have EQ : max i.1 j.1 = j.1,
--             { suffices : i ≤ j,  }, },
--           sorry },
--         congr' 1,
--         rw [subtype.ext_iff_val, ← EQ, ← ineq5], },
--       { sorry } }, }
-- end

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

lemma face.le_ignore {n : ℕ} (α : fin (n + 1) → U.ι) (k : fin (n + 1)) :
  face α ≤ face (ignore α k) :=
begin
  intros p hp,
  rw opens.mem_coe at hp ⊢,
  change _ ∈ infi _ at hp,
  change _ ∈ infi _,
  rw opens.fintype_infi at hp ⊢,
  rintros ⟨i, hi⟩,
  by_cases ineq : i < k.1,
  { specialize hp ⟨i, _⟩,
    { refine lt_trans hi _,
      exact lt_add_one n, },
    rw ignore.apply_lt,
    swap, exact ineq,
    exact hp, },
  { specialize hp ⟨i.pred, _⟩,
    { rw nat.lt_succ_iff,
      by_cases i = 0,
      { subst h,
        exact nat.zero_le _, },
      refine le_of_lt _,
      refine lt_trans _ hi,
      exact nat.pred_lt h, },
    rw ignore.apply_not_lt,
    convert hp,
    exact ineq, }
end

lemma face.le_ignore₂ {n : ℕ} (α : fin (n + 2) → U.ι) (i : fin (n + 2)) (j : fin (n + 1)) :
  face α ≤ face (ignore₂ α i j) :=
le_trans (face.le_ignore α i) (face.le_ignore _ j)

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

abbreviation C (n : ℕ) := AddCommGroup.of (C.pre 𝓕 U n)

-- section

-- variables {𝓕 U}
-- def C.pre.is_skewsymmetric {n : ℕ} (f : C.pre 𝓕 U n) : Prop :=
-- ∀ (i j : fin n) (α : fin n → U.ι),
--   f α =
--   𝓕.1.map (eq_to_hom (face.swap_eq α i j)).op (- f (swap i j α))

-- def C.pre.is_skewsymmetric' {n : ℕ} (f : C.pre 𝓕 U n) : Prop :=
-- ∀ (i j : fin n) (α : fin n → U.ι),
--   f (swap i j α) =
--   - 𝓕.1.map (eq_to_hom (face.swap_eq α i j).symm).op (f α)

-- lemma is_skewsymmetric_iff_is_skewsymmetric' {n} (f : C.pre 𝓕 U n) :
--   C.pre.is_skewsymmetric f ↔ C.pre.is_skewsymmetric' f :=
-- { mp := λ h i j α, begin
--     specialize h i j α,
--     rw [h, map_neg, map_neg, neg_neg, ← comp_apply, ← 𝓕.1.map_comp, ← op_comp, eq_to_hom_trans, eq_to_hom_refl],
--     simp,
--   end,
--   mpr := λ h i j α, begin
--     specialize h i j α,
--     rw [h, neg_neg, ← comp_apply, ← 𝓕.1.map_comp, ← op_comp, eq_to_hom_trans, eq_to_hom_refl],
--     simp
--   end }

-- end

-- def C (n : ℕ) : Type* :=
-- { f : C.pre 𝓕 U n // f.is_skewsymmetric ∧ ∀ (α : fin n → U.ι), ¬ function.injective α → f α = 0}

-- namespace C

-- variables (n : ℕ)

-- @[ext]
-- lemma ext_val {f g : C 𝓕 U n} (eq1 : f.1 = g.1) :
--   f = g := subtype.ext_val eq1

-- instance : has_add (C 𝓕 U n) :=
-- { add := λ f g,
--   ⟨f.1 + g.1, begin
--     split,
--     intros i j α,
--     change f.1 α + g.1 α = 𝓕.1.map _ (- (f.1 _ + g.1 _)),
--     rw [map_neg, map_add, f.2.1 i j, g.2.1 i j, map_neg, map_neg, neg_add],

--     intros α ha,
--     change f.1 α + g.1 α = 0,
--     rw [f.2.2, g.2.2, add_zero];
--     assumption,
--   end⟩ }

-- instance : has_zero (C 𝓕 U n) :=
-- { zero := 
--   ⟨0, begin
--     split,
--     intros i j α,
--     simp only [C_pre.zero_apply, neg_zero, map_zero],

--     intros α ha,
--     simp,
--   end⟩ }

-- instance : has_scalar ℕ (C 𝓕 U n) :=
-- { smul := λ m f, ⟨m • f.1, begin
--     split,
--     intros i j α,
--     simp only [C_pre.nsmul_apply, eq_to_hom_op, eq_to_hom_map, map_neg, map_nsmul],
--     rw f.2.1 i j,
--     simp only [eq_to_hom_op, eq_to_hom_map, map_neg, neg_nsmul],

--     intros α ha,
--     change m • f.1 α = 0,
--     rw f.2.2 _ ha,
--     simp,
--   end⟩ }

-- instance : add_comm_monoid (C 𝓕 U n) :=
-- { add := (+),
--   add_assoc := λ a b c, begin
--     ext,
--     change (a.1 + b.1 + c.1) _ = (a.1 + (b.1 + c.1)) _,
--     simp only [C_pre.add_apply],
--     rw add_assoc,
--   end,
--   zero := 0,
--   zero_add := λ f, begin
--     ext,
--     change (0 + f.1) _ = _,
--     simp only [C_pre.add_apply, C_pre.zero_apply, zero_add],
--   end,
--   add_zero := λ f, begin
--     ext,
--     change (f.1 + 0) _ = _,
--     simp only [C_pre.add_apply, C_pre.zero_apply, add_zero],
--   end,
--   nsmul := (•),
--   nsmul_zero' := λ f, begin
--     ext,
--     change 0 • f.1 _ = 0,
--     rw zero_smul,
--   end,
--   nsmul_succ' := λ m f, begin
--     ext,
--     change (m + 1) • f.1 x = (f.1 + m • f.1) x,
--     rw [add_smul, one_smul, C_pre.add_apply, add_comm],
--     refl,
--   end,
--   add_comm := λ f g, begin
--     ext,
--     change (f.1 + g.1) x = (g.1 + f.1) x,
--     simp only [add_comm, C_pre.add_apply],
--   end }

-- instance : add_comm_group (C 𝓕 U n) :=
-- { neg := λ f, ⟨-f.1, begin
--     split,
--     intros i j α,
--     simp only [C_pre.neg_apply],
--     rw neg_neg,
--     rw f.2.1 i j,
--     simp only [map_neg, neg_neg],

--     intros α ha,
--     change - (f.1 α) = 0,
--     rw f.2.2 _ ha,
--     rw neg_zero,
--   end⟩,
--   add_left_neg := λ f, begin
--     ext,
--     change (-f.1 + f.1) x = 0,
--     simp,
--   end,
--   ..add_comm_monoid 𝓕 U n }

-- end C

end