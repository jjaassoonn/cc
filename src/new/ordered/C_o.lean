import topology.sheaves.sheaf
import algebra.category.Group.limits
import oc
import data.nat.parity
import new.unordered.C
import lemmas.about_opens
import lemmas.lemmas

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open opposite

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)

structure vec_o (n : ℕ) : Type u :=
(to_fun : fin n → U.ι)
(is_strict_mono : strict_mono to_fun)

instance (n : ℕ) : has_coe_to_fun (vec_o U n) (λ _, fin n → U.ι) :=
{ coe := λ α, α.to_fun }

instance (n : ℕ) : has_coe (vec_o U n) (fin n → U.ι) :=
{ coe := λ α, α.to_fun }

def C_o.pre (n : ℕ) : Type u :=
Π (α : vec_o U n), 𝓕.1.obj (op $ face α)

section

variables {𝓕 U}
lemma map_congr.vec_o_eq {n} (f : C_o.pre 𝓕 U n) {α β : vec_o U n} (EQ : α = β) :
  f α = 𝓕.1.map (eq_to_hom $ by rw EQ).op (f β) :=
begin
  subst EQ,
  rw [eq_to_hom_op, eq_to_hom_map, eq_to_hom_refl, id_apply],
end

end

namespace C_o_pre

variable (n : ℕ)
variables {𝓕 U}

instance : has_add (C_o.pre 𝓕 U n) :=
{ add := λ f g α, f α + g α }

lemma add_assoc (f g h : C_o.pre 𝓕 U n) :
  f + g + h = f + (g + h) :=
begin
  ext α,
  simp [pi.add_apply, add_assoc],
end

lemma add_comm (f g : C_o.pre 𝓕 U n) :
  f + g = g + f :=
funext $ λ _, by simp [add_comm]

instance : has_zero (C_o.pre 𝓕 U n) :=
{ zero := λ α, 0 }

lemma zero_add (f : C_o.pre 𝓕 U n) :
  0 + f = f :=
funext $ λ α, by simp

lemma add_zero (f : C_o.pre 𝓕 U n) :
  f + 0 = f :=
funext $ λ _, by simp

instance (α : Type*) [Π (O : opens X), has_scalar α (𝓕.1.obj (op O))] : 
  has_scalar α (C_o.pre 𝓕 U n) :=
{ smul := λ m f β, m • (f β) }

lemma nsmul_zero (f : C_o.pre 𝓕 U n):
  0 • f = 0 :=
funext $ λ _, by simp

lemma zsmul_zero (f : C_o.pre 𝓕 U n) :
  (0 : ℤ) • f = 0 :=
funext $ λ _, by simp

lemma nsmul_succ (m : ℕ) (f : C_o.pre 𝓕 U n)  :
  m.succ • f = f + m • f :=
funext $ λ α, by simp [add_nsmul, nat.succ_eq_add_one, _root_.add_comm]

lemma zsmul_succ (m : ℕ) (f : C_o.pre 𝓕 U n)  :
  int.of_nat (m.succ) • f = f + int.of_nat m • f :=
funext $ λ α, by simp [add_smul, _root_.add_comm]

instance : has_neg (C_o.pre 𝓕 U n) :=
{ neg := λ f α, - f α }

lemma add_left_neg (f : C_o.pre 𝓕 U n) :
  (-f) + f = 0 :=
funext $ λ _, by simp

instance : has_sub (C_o.pre 𝓕 U n) :=
{ sub := λ f g α, f α - g α }

lemma sub_eq_add_neg (f g : C_o.pre 𝓕 U n) :
  f - g = f + (- g) :=
funext $ λ α, 
calc  (f - g) α 
    = f α - g α : rfl
... = f α + (- g α) : by abel

end C_o_pre

instance (n : ℕ) : add_comm_group (C_o.pre 𝓕 U n) :=
{ add := (+),
  add_assoc := C_o_pre.add_assoc n,
  zero := 0,
  zero_add := C_o_pre.zero_add n,
  add_zero := C_o_pre.add_zero n,
  nsmul := (•),
  nsmul_zero' := C_o_pre.nsmul_zero n,
  nsmul_succ' := C_o_pre.nsmul_succ n,
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := C_o_pre.sub_eq_add_neg n,
  zsmul := (•),
  zsmul_zero' := C_o_pre.zsmul_zero n,
  zsmul_succ' := C_o_pre.zsmul_succ n,
  zsmul_neg' := λ m f, funext $ λ α, by simp [add_smul],
  add_left_neg := C_o_pre.add_left_neg n,
  add_comm := C_o_pre.add_comm n }

def C_o (n : ℕ) : Ab := AddCommGroup.of (C_o.pre 𝓕 U n)

section ignore_o

variable (n : ℕ)
variables {U 𝓕 n}

def ignore_o (α : vec_o U (n + 1)) (k : fin (n + 1)) : vec_o U n :=
{ to_fun := ignore α.to_fun k,
  is_strict_mono := λ i j h, begin
    by_cases ineq1 : j.1 < k.1,
    { rw ignore.apply_lt,
      work_on_goal 2
      { transitivity j.1,
        exact h,
        exact ineq1, },
      rw ignore.apply_lt,
      work_on_goal 2
      { assumption, },
      apply α.2,
      exact h },
    -- rw not_lt at ineq1,
    
    { rw ignore.apply_not_lt α.1 _ ineq1,
      rw not_lt at ineq1,
      rw ignore.apply_ite,
      split_ifs with ineq2,
      { apply α.2,
        change i.1 < j.1.pred,
        sorry },
      { apply α.2,
        change i.1.pred < j.1.pred,
        sorry }, },
  end }

def ignore_o₂ (α : vec_o U (n + 2)) (i : fin (n + 2)) (j : fin (n + 1)) :
  vec_o U n :=
ignore_o (ignore_o α i) j

lemma ignore_o₂_symm' {n : ℕ} (α : vec_o U (n+2))
  {i : ℕ} (hi : i ∈ finset.range n.succ)
  {j : ℕ} (hj : j ∈ finset.Ico i n.succ) : -- i ≤ j
  ignore_o₂ α ⟨j + 1, begin
    rw finset.mem_Ico at hj,
    rw nat.succ_lt_succ_iff,
    exact hj.2
  end⟩ ⟨i, finset.mem_range.mp hi⟩ = ignore_o₂ α ⟨i, lt_trans (finset.mem_range.mp hi) (lt_add_one _)⟩ ⟨j, (finset.mem_Ico.mp hj).2⟩ :=
begin
  sorry
end

lemma ignore_o.apply_lt (α : vec_o U (n + 1)) (k : fin (n + 1)) (i : fin n)
  (ineq : i.1 < k.1) :
  ignore_o α k i = α ⟨i.1, lt_trans i.2 (lt_add_one _)⟩ :=
begin
  change ignore α.to_fun k i = α.1 _,
  rw ignore.apply_lt,
  exact ineq
end

lemma ignore_o.apply_not_lt (α : vec_o U (n + 1)) (k : fin (n + 1)) (i : fin n)
  (ineq : ¬ i.1 < k.1) :
  ignore_o α k i = α ⟨i.1.pred, begin
    rw nat.lt_succ_iff,
    refine le_of_lt _,
    exact lt_of_le_of_lt (nat.pred_le _) i.2,
  end⟩ :=
begin
  change ignore α.to_fun k i = α.1 _,
  rw ignore.apply_not_lt,
  exact ineq,
end
  

def face_o (α : vec_o U n) : opens X :=
infi (λ (k : fin n), U.cover $ α k)


lemma face.le_ignore_o (α : vec_o U (n + 1)) (k : fin (n + 1)) :
  face_o α ≤ face_o (ignore_o α k) := λ p hp,
begin
  rw opens.mem_coe at hp ⊢,
  erw opens.fintype_infi at hp ⊢,
  rintros ⟨i, hi⟩,
  by_cases ineq : i < k.1,
  { specialize hp ⟨i, _⟩,
    { refine lt_trans hi _,
      exact lt_add_one n, },
    rw ignore_o.apply_lt,
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
    rw ignore_o.apply_not_lt,
    convert hp,
    exact ineq, }
end

lemma face.le_ignore_o₂ (α : vec_o U (n + 2)) (i : fin (n + 2)) (j : fin (n + 1)) :
  face_o α ≤ face_o (ignore_o₂ α i j) :=
le_trans (face.le_ignore_o _ i) (face.le_ignore_o _ _)

end ignore_o

section d_o

open nat
open_locale big_operators

variable (n : ℕ)
variables {𝓕 U n}

def d_o.to_fun.component' (α : vec_o U (n + 1)) (k : fin (n + 1)) (f : C_o.pre 𝓕 U n)  :
  𝓕.1.obj (op (face α)) :=
(ite (even k.1) id (has_neg.neg)) $
  𝓕.1.map (hom_of_le $ face.le_ignore α k).op $ f (ignore_o α k)


def d_o.to_fun.component (k : fin (n + 1)) :
  C_o.pre 𝓕 U n → C_o.pre 𝓕 U (n + 1) :=
λ f α, d_o.to_fun.component' α k f

def d_o.to_fun (f : C_o.pre 𝓕 U n) (α : vec_o U (n + 1)) : 𝓕.1.obj (op (face α)) :=
∑ (k : fin (n + 1)), d_o.to_fun.component k f α

variables (n 𝓕 U)
def d_o : C_o 𝓕 U n ⟶ C_o 𝓕 U (n + 1) :=
{ to_fun := d_o.to_fun,
  map_zero' := funext $ λ α, begin
    simp only [pi.zero_apply],
    change ∑ _, _ = _,
    rw finset.sum_eq_zero,
    intros i hi,
    change (ite _ id has_neg.neg) _ = _,
    split_ifs with e,
    { rw [id, pi.zero_apply, map_zero], },
    { rw [pi.zero_apply, map_zero, neg_zero], },
  end,
  map_add' := λ f g, funext $ λ α, begin
    rw pi.add_apply,
    change ∑ _, _ = ∑ _, _ + ∑ _, _,
    rw ← finset.sum_add_distrib,
    rw finset.sum_congr rfl,
    intros i _,
    change (ite _ id _) _ = (ite _ id _) _ + (ite _ id _) _,
    split_ifs with e,
    { rw [id, id, id, pi.add_apply, map_add], },
    { rw [pi.add_apply, map_add, neg_add], },
  end }

abbreviation dd_o : C_o 𝓕 U n ⟶ C_o 𝓕 U (n + 2) :=
d_o _ _ _ ≫ d_o _ _ _

namespace dd_o_aux

lemma d_o_def (f : C_o 𝓕 U n) (α : vec_o U (n + 1)) :
  d_o 𝓕 U n f α =
  ∑ (i : fin (n+1)), 
    (ite (even i.1) id has_neg.neg)
      𝓕.1.map (hom_of_le $ face.le_ignore_o α i).op (f (ignore_o α i)) :=
begin
  rw [d_o],
  simp only [add_monoid_hom.coe_mk, fin.val_eq_coe],
  change ∑ _, _ = _,
  rw finset.sum_congr rfl,
  intros i _,
  change (ite _ id _) _ = _,
  split_ifs,
  { rw [id, id],
    refl, },
  { simpa, },
end

lemma eq1 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  d_o 𝓕 U (n + 1) (d_o 𝓕 U n f) α := rfl

lemma eq2 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (𝓕.1.map (hom_of_le (face.le_ignore_o α i)).op (d_o 𝓕 U n f (ignore_o α i))) :=
begin
  rw [eq1, d_o_def, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { simp },
  { simp },
end

lemma eq3 (f : C_o 𝓕 U n) (α : vec_o U (n+2))  :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (𝓕.1.map (hom_of_le (face.le_ignore α i)).op
        (∑ (j : fin (n + 1)), 
          (ite (even j.1) id has_neg.neg)
            (𝓕.1.map (hom_of_le (face.le_ignore (ignore_o α i) j)).op (f (ignore_o (ignore_o α i) j))))) :=
begin
  rw [eq2, finset.sum_congr rfl],
  intros i _,
  rw [d_o_def],
  split_ifs,
  { simp only [id.def],
    rw [add_monoid_hom.map_sum, add_monoid_hom.map_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id],
      refl, },
    { simp only [pi.neg_apply, add_monoid_hom.neg_apply],
      refl, }, },
  { congr' 2,
    rw [finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id],
      refl, },
    { simp only [pi.neg_apply, add_monoid_hom.neg_apply, neg_inj],
      refl, } },
end

lemma eq4 (f : C_o 𝓕 U n) (α : vec_o U (n+2))  :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        𝓕.1.map (hom_of_le (face.le_ignore_o α i)).op
          ((ite (even j.1) id has_neg.neg)
            𝓕.1.map (hom_of_le (face.le_ignore_o (ignore_o α i) j)).op 
              (f (ignore_o (ignore_o α i) j)))) :=
begin
  rw [eq3, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [add_monoid_hom.map_sum, id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id],
      refl, },
    { simpa }, },
  { rw [add_monoid_hom.map_sum, finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id],
      refl, },
    { simpa }, },
end

lemma eq5 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore_o α i)).op
          (𝓕.1.map (hom_of_le (face.le_ignore_o (ignore_o α i) j)).op
            (f (ignore_o (ignore_o α i) j))))) :=
begin
  rw [eq4, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp, }, },
end  

lemma eq6₀ (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map ((hom_of_le (face.le_ignore (ignore α i) j)).op ≫ (hom_of_le (face.le_ignore α i)).op)
            (f (ignore_o (ignore_o α i) j)))) :=
begin
  rw [eq5, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, 𝓕.1.map_comp, comp_apply],
      refl, },
    { rw [𝓕.1.map_comp, comp_apply],
      refl, }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, 𝓕.1.map_comp, comp_apply],
      refl, },
    { rw [neg_neg, neg_neg, 𝓕.1.map_comp, comp_apply],
      refl, }, }
end

lemma eq6₁ (f : C_o 𝓕 U n) (α : vec_o U (n+2))  :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore α i) ≫ hom_of_le (face.le_ignore (ignore α i) j)).op)
            (f (ignore_o (ignore_o α i) j))) :=
begin
  rw [eq6₀, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, op_comp], },
    { rw [op_comp],
      simp }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, op_comp] },
    { rw [op_comp],
      simp }, }
end

lemma eq6₂ (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore_o₂ α i j)).op)
            (f (ignore_o₂ α i j))) :=
begin
  rw [eq6₁, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], congr, },
    { congr, }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], congr, },
    { congr }, },
end

lemma eq7 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)),
    (ite (even i.1) id has_neg.neg)
      (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore_o₂ α i j)).op)
            (f (ignore_o₂ α i j)) :=
begin
  rw [eq6₂, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, id], },
    { rw [id], }, },
  { rw [finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, pi.neg_apply, id], congr, },
    { rw [pi.neg_apply, neg_neg, add_monoid_hom.neg_apply, neg_neg], }, },
end

lemma eq8 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)),
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j)) :=
begin
  rw [eq7, finset.sum_congr rfl],
  intros i _,
  rw [finset.sum_congr rfl],
  intros j _,
  split_ifs with h1 h2 h12,
  { refl, },
  { exfalso,
    apply h12,
    exact even.add_even h1 h2 },
  { exfalso,
    rw ← nat.odd_iff_not_even at h2,
    have := even.add_odd h1 h2,
    rw nat.odd_iff_not_even at this,
    apply this,
    exact h, },
  { rw [id],
    refl, },
  { rw ← nat.odd_iff_not_even at h1,
    have := odd.add_even h1 h,
    rw nat.odd_iff_not_even at this,
    exfalso,
    apply this,
    assumption, },
  { rw [pi.neg_apply, id],
    refl, },
  { rw [pi.neg_apply, neg_neg, id],
    refl, },
  { rw ← nat.odd_iff_not_even at *,
    have := odd.add_odd h1 h,
    rw nat.even_iff_not_odd at this, 
    exfalso,
    apply this,
    assumption },
end

lemma eq9 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  ∑ (i : fin (n + 2)), 
    ((∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), i.1 ≤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j))) +
    (∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j)))) :=
begin
  rw [eq8, finset.sum_congr rfl],
  intros i _,
  have : 
    (finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.val)) =
    (finset.univ.filter (λ (j : fin (n + 1)), i.val ≤ j.val))ᶜ,
  { ext1 k,
    split; 
    intros hk;
    simp only [finset.compl_filter, not_le, finset.mem_filter, finset.mem_univ, true_and] at hk ⊢;
    assumption, },
  rw [this, finset.sum_add_sum_compl],
end

lemma eq11 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), i.1 ≤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j))) +
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j))) :=
begin
  rw [eq9, finset.sum_add_distrib],
end

lemma eq13 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore_o₂ α i j))) :=
begin
  rw [eq11],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i _,
  apply finset.sum_bij,

  work_on_goal 5
  { intros j hj,
    refine ⟨j.1, _⟩,
    rw finset.mem_Ico,
    rw finset.mem_filter at hj,
    refine ⟨hj.2, _⟩,
    exact j.2 },
  { intros j hj,
    dsimp only,
    rw finset.mem_filter at hj,
    apply finset.mem_attach, },
  { intros j hj,
    dsimp only,
    split_ifs,
    { rw [id, id],
      rw map_congr.vec_o_eq f (_ : ignore_o₂ α i j = ignore_o₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_o_eq f (_ : ignore_o₂ α i j = ignore_o₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, }, },
  { intros j1 j2 h1 h2 H,
    dsimp only at H,
    rw subtype.ext_iff_val at *,
    assumption },
  { intros j _,
    have hj := j.2,
    rw finset.mem_Ico at hj,
    refine ⟨⟨j.1, hj.2⟩, _, _⟩,
    rw finset.mem_filter,
    refine ⟨finset.mem_univ ⟨j.val, _⟩, hj.1⟩,
    dsimp only,
    rw subtype.ext_iff_val, },
end

lemma eq14 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ (i : fin (n + 2)), ∑ j in (finset.range i.1).attach,
    (ite (even (i.1 + j)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_range at hj,
            have hi : i.1 ≤ n+1,
            { linarith [i.2], },
            linarith,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) :=
begin
  rw [eq13],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i hi,
  apply finset.sum_bij',

  work_on_goal 4
  { intros j hj,
    rw finset.mem_filter at hj,
    refine ⟨j.1, _⟩,
    rw finset.mem_range,
    exact hj.2 },
  work_on_goal 5
  { intros j _,
    have hj := j.2,
    rw finset.mem_range at hj,
    refine ⟨j.1, _⟩,
    linarith [i.2], },
  { intros j hj,
    dsimp only,
    split_ifs,
    { rw [id, id],
      rw map_congr.vec_o_eq f (_ : ignore_o₂ α i j = ignore_o₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_o_eq f (_ : ignore_o₂ α i j = ignore_o₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, }, },
  { intros j hj,
    dsimp only,
    rw subtype.ext_iff_val, },
  { intros j hj,
    rw subtype.ext_iff_val, },
  { intros j hj,
    apply finset.mem_attach, },
  { intros j _,
    have hj := j.2,
    rw finset.mem_range at hj,
    rw finset.mem_filter,
    dsimp only,
    refine ⟨_, hj⟩,
    apply finset.mem_univ, },
end

lemma eq15 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ j in (finset.range n.succ).attach, ∑ i in (finset.Ico j.1.succ n.succ.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rwa finset.mem_Ico at hi,
            exact hi.2,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rwa finset.mem_range at hj,
          end⟩)).op)
            (f (ignore_o₂ α _ _))) :=
begin
  rw [eq14],
  congr' 1,
  rw [finset.sum_sigma', finset.sum_sigma'],
  apply finset.sum_bij',
  work_on_goal 4
  { refine λ x h, ⟨⟨x.2.1, begin
    have hx2 := x.2.2,
    have hx1 := x.1.2,
    rw finset.mem_range at hx2 ⊢,
    have : x.1.1 ≤ n + 1,
    { linarith },
    refine lt_of_lt_of_le hx2 this,
  end⟩, ⟨x.1.1, _⟩⟩, },
  work_on_goal 6
  { refine λ x h, ⟨⟨x.2.1, begin
    have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx1,
    rw finset.mem_Ico at hx2,
    exact hx2.2,
  end⟩, ⟨x.1.1, begin
    have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx1 ⊢,
    rw finset.mem_Ico at hx2,
    refine lt_of_le_of_lt _ hx2.1,
    refl, 
  end⟩⟩, },
  { rintros ⟨⟨i, hi⟩, j⟩ h,
    dsimp only,
    congr, },
  { rintros ⟨⟨i, hi⟩, j⟩ h,
    simp only,
    split,
    refl,
    rw heq_iff_eq,
    rw subtype.ext_iff_val, },
  { rintros ⟨i, j⟩ h,
    simp only,
    split,
    rw subtype.ext_iff_val,
    rw heq_iff_eq,
    rw subtype.ext_iff_val, },
  { have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx2,
    rw finset.mem_Ico,
    refine ⟨_, hx1⟩,
    exact hx2, },
  { rintros ⟨i, j⟩ h,
    rw finset.mem_sigma,
    split,
    apply finset.mem_attach,
    apply finset.mem_attach },
  { intros x h,
    rw finset.mem_sigma,
    split,
    apply finset.mem_univ,
    apply finset.mem_attach, },
end


lemma eq16 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, ∑ j in (finset.Ico i.1.succ n.succ.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨j.1, begin
            have hi := j.2,
            rwa finset.mem_Ico at hi,
            exact hi.2,
          end⟩ ⟨i.1, begin
            have hj := i.2,
            rwa finset.mem_range at hj,
          end⟩)).op)
            (f (ignore_o₂ α _ _))) :=
begin
  rw [eq15],
end

lemma eq17 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even ((j.1 + 1) + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨j.1 + 1, begin
            have hi := j.2,
            rw finset.mem_Ico at hi,
            rw succ_lt_succ_iff,
            exact hi.2,
          end⟩ ⟨i.1, begin
            have hj := i.2,
            rwa finset.mem_range at hj,
          end⟩)).op)
            (f (ignore_o₂ α ⟨j.1 + 1, _⟩ ⟨i.1, _⟩))) :=
begin
  rw [eq16],
  congr' 1,
  rw finset.sum_congr rfl,
  intros i hi,
  apply finset.sum_bij',
  work_on_goal 4
  { intros j _, refine ⟨j.1.pred, _⟩,
    have hj := j.2,
    rw finset.mem_Ico at hj ⊢,
    rcases hj with ⟨hj1, hj2⟩,
    have ineq0 : 0 < j.1,
    { refine lt_of_lt_of_le _ hj1,
      exact nat.zero_lt_succ _, }, 
    have eq1 : j.1 = j.1.pred.succ,
    { rwa nat.succ_pred_eq_of_pos, },
    split,
    rw eq1 at hj1,
    rwa succ_le_succ_iff at hj1,

    rw eq1 at hj2,
    rwa succ_lt_succ_iff at hj2 },
  work_on_goal 5
  { intros j _, refine ⟨j.1 + 1, _⟩,
    have hj := j.2, 
    rw finset.mem_Ico at hj ⊢,
    rcases hj with ⟨hj1, hj2⟩,
    split,

    rwa succ_le_succ_iff,
    rwa succ_lt_succ_iff,
    },
  { intros j hj,
    dsimp only,
    rw map_congr.vec_o_eq f (_ : ignore_o₂ α ⟨j.1, _⟩ ⟨i.1, _⟩ = ignore_o₂ α ⟨j.1.pred + 1, _⟩ ⟨i.1, _⟩),
    by_cases e1 : even (j.1 + i.1),
    { rw [if_pos e1, if_pos, id, id, ← comp_apply, ← 𝓕.1.map_comp], congr,
      rwa [← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      have hj := j.2,
      rw finset.mem_Ico at hj,
      refine lt_of_lt_of_le _ hj.1,
      exact nat.zero_lt_succ _, },
    { rw [if_neg e1, if_neg, add_monoid_hom.neg_apply, add_monoid_hom.neg_apply, ← comp_apply, ← 𝓕.1.map_comp],
      congr,
      rwa [← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      have hj := j.2,
      rw finset.mem_Ico at hj,
      refine lt_of_lt_of_le _ hj.1,
      exact nat.zero_lt_succ _, },
    congr,
    rwa [← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
    have hj := j.2,
    rw finset.mem_Ico at hj,
    refine lt_of_lt_of_le _ hj.1,
    exact nat.zero_lt_succ _, },
  { intros j hj,
    simp only,
    rw subtype.ext_iff_val,
    dsimp only,
    rw [← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
    have hj := j.2,
    rw finset.mem_Ico at hj,
    refine lt_of_lt_of_le _ hj.1,
    exact nat.zero_lt_succ _, },
  { intros j hj,
    simp only,
    rw subtype.ext_iff_val,
    dsimp only,
    rw nat.pred_succ, },
  { intros j hj,
    apply finset.mem_attach, },
  { intros j hj,
    apply finset.mem_attach, },
end

lemma eq18 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even ((j.1 + 1) + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
begin
  rw eq17 𝓕 U n f α,
  apply congr_arg2 (+) rfl _,
  rw [finset.sum_congr rfl],
  intros i hi,
  rw [finset.sum_congr rfl],
  intros j hj,
  generalize_proofs _ h1 h2 h3 h4 h5,
  rw map_congr.vec_o_eq f (_ : ignore_o₂ α ⟨j.1 + 1, h1⟩ ⟨i.1, h2⟩ = ignore_o₂ α ⟨i.1, h4⟩ ⟨j.1, _⟩),
  split_ifs,
  { rw [id, id, ← comp_apply, ← 𝓕.1.map_comp],
    congr },
  { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply, ← comp_apply, ← 𝓕.1.map_comp],
    congr },
  have := ignore_o₂_symm' α i.2 j.2,
  convert ← this,
end

lemma eq19 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α i ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, - ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq18],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i _,
  rw [finset.neg_sum, finset.sum_congr rfl],
  intros j _,
  split_ifs with h1 h2,
  { exfalso,
    have o1 : odd (1 : ℕ) := odd_one,
    have := even.add_odd h2 o1,
    rw nat.odd_iff_not_even at this,
    apply this,
    convert h1 using 1,
    abel, },
  { rw [id, add_monoid_hom.neg_apply, neg_neg], },
  { rw [id, add_monoid_hom.neg_apply], },
  { rw ← nat.odd_iff_not_even at h h1,
    have o1 : odd (1 : ℕ) := odd_one,
    have := odd.add_odd h o1,
    rw nat.even_iff_not_odd at this,
    exfalso,
    apply this,
    convert h1 using 1,
    abel, },
end

lemma eq20₀ (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ i in (finset.range (n+2)).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            exact finset.mem_range.mp hi,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, - ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq19],
  congr' 1,
  rw finset.sum_fin_eq_sum_range,
  rw ← finset.sum_attach,
  rw finset.sum_congr rfl,
  intros i hi,
  rw dif_pos,
  refl,
end

lemma eq20₁ (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ i in (finset.range (n+1)).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, - ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
have eq0 : 
  ∑ i in (finset.range (n+2)).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
          have hi := i.2,
          exact finset.mem_range.mp hi,
        end⟩ ⟨j.1, begin
          have hj := j.2,
          rw finset.mem_Ico at hj,
          exact hj.2,
        end⟩)).op)
          (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩)) =
  ∑ i in (insert n.succ (finset.range (n+1))).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
          have hi := i.2,
          rw finset.mem_insert at hi,
          cases hi,
          rw hi, exact lt_add_one _,

          rw finset.mem_range at hi,
          refine lt_trans hi _,
          exact lt_add_one _,
        end⟩ ⟨j.1, begin
          have hj := j.2,
          rw finset.mem_Ico at hj,
          exact hj.2,
        end⟩)).op)
          (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩)),
begin
  rw finset.sum_bij',
  work_on_goal 4
  { intros a _,
    refine ⟨a.1, _⟩,
    rw finset.mem_insert,
    have ha := a.2,
    by_cases a.1 = n.succ, 
    left, assumption,
    right,
    rw finset.mem_range at ha ⊢,
    contrapose! h,
    have ha' : a.1 ≤ n+1,
    linarith,
    refine le_antisymm ha' h, },
  work_on_goal 5
  { intros a _,
    refine ⟨a.1, _⟩,
    have ha := a.2,
    rw finset.mem_insert at ha,
    rw finset.mem_range at ha ⊢,
    cases ha,
    rw ha, exact lt_add_one _,
    linarith, },
  { intros, simp only, },
  { intros, simp only, rw subtype.ext_iff_val, },
  { intros, simp only, rw subtype.ext_iff_val, },
  { intros, simp only,
    apply finset.mem_attach },
  { intros, apply finset.mem_attach },
end,
begin
  rw [eq20₀],
  apply congr_arg2 (+) _ rfl,
  rw eq0,
  rw finset.attach_insert,
  rw finset.sum_insert,
  conv_lhs { simp only [add_comm] },
  congr' 1,
  { simp only [finset.sum_image, subtype.forall, subtype.coe_mk, imp_self, implies_true_iff], },
  { rw finset.mem_image,
    push_neg,
    intros a _,
    have ha := a.2,
    rw finset.mem_range at ha,
    intro r,
    rw r at ha,
    apply lt_irrefl _ ha, },
end

lemma eq21 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ i in (finset.range (n+1)).attach, ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ i in (finset.range n.succ).attach, - ∑ j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq20₁],
  abel,
end

lemma eq22 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ i in (finset.range (n+1)).attach, 
    ((∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
    (- ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (j.1 + i.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨i.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq21, finset.sum_add_distrib],
end

lemma eq23 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α =
  (∑ i in (finset.range (n+1)).attach, 0) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq22],
  congr' 1,
  rw finset.sum_congr rfl,
  intros i _,
  simp_rw [add_comm],
  rw add_neg_eq_zero,
end

lemma eq24 (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α = 0 +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore_o₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq23],
  congr',
  rw finset.sum_eq_zero,
  intros, refl,
end

lemma eq_zero (f : C_o 𝓕 U n) (α : vec_o U (n+2)) :
  dd_o 𝓕 U n f α = 0 :=
begin
  rw [eq24, zero_add],
  convert finset.sum_empty,
  rw finset.Ico_self,
  rw finset.attach_empty
end


end dd_o_aux

end d_o

end