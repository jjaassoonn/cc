import new.C
import data.nat.parity
import algebra.category.Group.colimits
import lemmas.lemmas
import algebra.big_operators

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open opposite
open nat

open_locale big_operators

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U : X.oc)
variable (n : ℕ)

section

variables {n 𝓕 U}

/--
`α = (i₀,⋯,i_{n+1})` then if `k` is even, 
we write `f (i_0, ..., i_{k-1}, i_{k+1}, ..., i_{n+1}) ∈ 𝓕(U_0 ∩ ... ∩ U_{k-1} ∩ U_{k+1} ∩ ... ∩ U_{n+1})` restricted to `U_0 ∩ ... ∩ U_{n+1}` 
-/
def d.to_fun.component' (α : fin (n + 1) → U.ι) (k : fin (n + 1)) (f : C.pre 𝓕 U n)  :
  𝓕.1.obj (op (face α)) :=
(ite (even k.1) id (has_neg.neg)) $
  𝓕.1.map (hom_of_le $ face.le_ignore α k).op $ f (ignore α k)

lemma map_congr.vec_eq (f : C.pre 𝓕 U n) {α β : fin n → U.ι} (EQ : α = β) :
  f α = 𝓕.1.map (eq_to_hom $ by rw EQ).op (f β) :=
begin
  subst EQ,
  rw [eq_to_hom_op, eq_to_hom_map],
  refl,
end

def d.to_fun.component (k : fin (n + 1)) :
  C.pre 𝓕 U n → C.pre 𝓕 U (n + 1) :=
λ f α, d.to_fun.component' α k f

def d.to_fun (f : C.pre 𝓕 U n) (α : fin (n + 1) → U.ι) : 𝓕.1.obj (op (face α)) :=
∑ (k : fin (n + 1)), d.to_fun.component k f α

end

-- instance {n : ℕ} : add_comm_group (C.pre 𝓕 U n) := by apply_instance
def d : (C 𝓕 U n) ⟶ (C 𝓕 U (n+1)) := 
{ to_fun := λ f α, d.to_fun f α,
  map_zero' := begin
    ext1 α,
    simp only [C_pre.zero_apply],
    change ∑ _, _ = _,
    rw finset.sum_eq_zero,
    intros i _,
    change (ite _ id _) _ = _,
    split_ifs,
    { rw [id, C_pre.zero_apply, map_zero], },
    { rw [C_pre.zero_apply, map_zero, neg_zero], },
  end,
  map_add' := λ f g, begin
    ext1 α,
    dsimp only,
    change ∑ _, _ = ∑ _, _ + ∑ _, _,
    rw ← finset.sum_add_distrib,
    rw finset.sum_congr rfl,
    intros i _,
    change (ite _ id _) _ = (ite _ id _) _ + (ite _ id _) _,
    split_ifs,
    { rw [id, id, id, C_pre.add_apply, map_add], },
    { rw [C_pre.add_apply, map_add, neg_add], },
  end }

abbreviation dd : C 𝓕 U n ⟶ C 𝓕 U (n + 2) := d 𝓕 U n ≫ d 𝓕 U (n + 1)

namespace dd_aux

lemma d_def (f : C 𝓕 U n) (α : fin (n + 1) → U.ι) :
  d 𝓕 U n f α =
  ∑ (i : fin (n+1)), 
    (ite (even i.1) id has_neg.neg)
      𝓕.1.map (hom_of_le $ face.le_ignore α i).op (f (ignore α i)) :=
begin
  rw [d],
  simp only [add_monoid_hom.coe_mk, fin.val_eq_coe],
  change ∑ _, _ = _,
  rw finset.sum_congr rfl,
  intros i _,
  change (ite _ id _) _ = _,
  split_ifs,
  { rw [id, id], },
  { simp, },
end

lemma eq1 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  d 𝓕 U (n + 1) (d 𝓕 U n f) α := rfl

lemma eq2 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (𝓕.1.map (hom_of_le (face.le_ignore α i)).op (d 𝓕 U n f (ignore α i))) :=
begin
  rw [eq1, d_def, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { simp },
  { simp },
end

lemma eq3 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (𝓕.1.map (hom_of_le (face.le_ignore α i)).op
        (∑ (j : fin (n + 1)), 
          (ite (even j.1) id has_neg.neg)
            (𝓕.1.map (hom_of_le (face.le_ignore (ignore α i) j)).op (f (ignore (ignore α i) j))))) :=
begin
  rw [eq2, finset.sum_congr rfl],
  intros i _,
  rw [d_def],
  split_ifs,
  { simp only [id.def],
    rw [add_monoid_hom.map_sum, add_monoid_hom.map_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp only [pi.neg_apply, add_monoid_hom.neg_apply], }, },
  { congr' 2,
    rw [finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp } },
end

lemma eq4 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        𝓕.1.map (hom_of_le (face.le_ignore α i)).op
          ((ite (even j.1) id has_neg.neg)
            𝓕.1.map (hom_of_le (face.le_ignore (ignore α i) j)).op 
              (f (ignore (ignore α i) j)))) :=
begin
  rw [eq3, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [add_monoid_hom.map_sum, id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp }, },
  { rw [add_monoid_hom.map_sum, finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id], },
    { simp }, },
end

lemma eq5 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore α i)).op
          (𝓕.1.map (hom_of_le (face.le_ignore (ignore α i) j)).op
            (f (ignore (ignore α i) j))))) :=
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

lemma eq6₀ (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map ((hom_of_le (face.le_ignore (ignore α i) j)).op ≫ (hom_of_le (face.le_ignore α i)).op)
            (f (ignore (ignore α i) j)))) :=
begin
  rw [eq5, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, 𝓕.1.map_comp, comp_apply], },
    { rw [𝓕.1.map_comp, comp_apply] }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, 𝓕.1.map_comp, comp_apply] },
    { rw [neg_neg, neg_neg, 𝓕.1.map_comp, comp_apply] }, }
end

lemma eq6₁ (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore α i) ≫ hom_of_le (face.le_ignore (ignore α i) j)).op)
            (f (ignore (ignore α i) j))) :=
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

lemma eq6₂ (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (∑ (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j))) :=
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

lemma eq7 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)),
    (ite (even i.1) id has_neg.neg)
      (ite (even j.1) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j)) :=
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

lemma eq8 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)),
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j)) :=
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
  { rw [id], },
  { rw ← nat.odd_iff_not_even at h1,
    have := odd.add_even h1 h,
    rw nat.odd_iff_not_even at this,
    exfalso,
    apply this,
    assumption, },
  { rw [pi.neg_apply, id], },
  { rw [pi.neg_apply, neg_neg, id], },
  { rw ← nat.odd_iff_not_even at *,
    have := odd.add_odd h1 h,
    rw nat.even_iff_not_odd at this, 
    exfalso,
    apply this,
    assumption },
end

lemma eq9 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  ∑ (i : fin (n + 2)), 
    ((∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), i.1 ≤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j))) +
    (∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j)))) :=
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

lemma eq11 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), i.1 ≤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j))) +
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j))) :=
begin
  rw [eq9, finset.sum_add_distrib],
end

lemma eq13 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
  (∑ (i : fin (n + 2)), ∑ (j : fin (n + 1)) in finset.univ.filter (λ (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i j)).op)
            (f (ignore₂ α i j))) :=
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
      rw map_congr.vec_eq f (_ : ignore₂ α i j = ignore₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_eq f (_ : ignore₂ α i j = ignore₂ α i ⟨j.1, _⟩),
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

lemma eq14 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
  (∑ (i : fin (n + 2)), ∑ j in (finset.range i.1).attach,
    (ite (even (i.1 + j)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_range at hj,
            have hi : i.1 ≤ n+1,
            { linarith [i.2], },
            linarith,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) :=
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
      rw map_congr.vec_eq f (_ : ignore₂ α i j = ignore₂ α i ⟨j.1, _⟩),
      rw [← comp_apply, ← 𝓕.1.map_comp, ← op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_eq f (_ : ignore₂ α i j = ignore₂ α i ⟨j.1, _⟩),
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

lemma eq15 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
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
            (f (ignore₂ α _ _))) :=
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


lemma eq16 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
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
            (f (ignore₂ α _ _))) :=
begin
  rw [eq15],
end

lemma eq17 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨j.1 + 1, _⟩ ⟨i.1, _⟩))) :=
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
    rw map_congr.vec_eq f (_ : ignore₂ α ⟨j.1, _⟩ ⟨i.1, _⟩ = ignore₂ α ⟨j.1.pred + 1, _⟩ ⟨i.1, _⟩),
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

lemma eq18 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
begin
  rw eq17 𝓕 U n f α,
  apply congr_arg2 (+) rfl _,
  rw [finset.sum_congr rfl],
  intros i hi,
  rw [finset.sum_congr rfl],
  intros j hj,
  generalize_proofs _ h1 h2 h3 h4 h5,
  rw map_congr.vec_eq f (_ : ignore₂ α ⟨j.1 + 1, h1⟩ ⟨i.1, h2⟩ = ignore₂ α ⟨i.1, h4⟩ ⟨j.1, _⟩),
  split_ifs,
  { rw [id, id, ← comp_apply, ← 𝓕.1.map_comp],
    congr },
  { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply, ← comp_apply, ← 𝓕.1.map_comp],
    congr },
  have := ignore₂_symm' α i.2 j.2,
  convert ← this,
end

lemma eq19 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
  (∑ (i : fin (n + 2)), ∑ j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α i ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α i ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
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

lemma eq20₀ (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
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

lemma eq20₁ (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) :=
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
          (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩)) =
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
          (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩)),
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

lemma eq21 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq20₁],
  abel,
end

lemma eq22 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))) +
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
            (f (ignore₂ α ⟨i.1, _⟩ ⟨j.1, _⟩))))) +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq21, finset.sum_add_distrib],
end

lemma eq23 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α =
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
            (f (ignore₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq22],
  congr' 1,
  rw finset.sum_congr rfl,
  intros i _,
  simp_rw [add_comm],
  rw add_neg_eq_zero,
end

lemma eq24 (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α = 0 +
  (∑ j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (𝓕.1.map (hom_of_le (face.le_ignore₂ α ⟨n.succ, begin
            exact lt_add_one _,
          end⟩ ⟨j.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          end⟩)).op)
            (f (ignore₂ α ⟨n.succ, _⟩ ⟨j.1, _⟩))) :=
begin
  rw [eq23],
  congr',
  rw finset.sum_eq_zero,
  intros, refl,
end

lemma eq_zero (f : C 𝓕 U n) (α : fin (n + 2) → U.ι) :
  dd 𝓕 U n f α = 0 :=
begin
  rw [eq24, zero_add],
  convert finset.sum_empty,
  rw finset.Ico_self,
  rw finset.attach_empty
end

end dd_aux

lemma dd_eq_zero (n : ℕ) : dd 𝓕 U n = 0 :=
begin
  ext f α,
  convert dd_aux.eq_zero 𝓕 U n f α,
end

end