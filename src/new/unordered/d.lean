import new.unordered.C
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
variables {X : Top.{u}} (š : sheaf Ab X) (U : X.oc)
variable (n : ā)

section

variables {n š U}

/--
`Ī± = (iā,āÆ,i_{n+1})` then if `k` is even, 
we write `f (i_0, ..., i_{k-1}, i_{k+1}, ..., i_{n+1}) ā š(U_0 ā© ... ā© U_{k-1} ā© U_{k+1} ā© ... ā© U_{n+1})` restricted to `U_0 ā© ... ā© U_{n+1}` 
-/
def d.to_fun.component' (Ī± : fin (n + 1) ā U.Ī¹) (k : fin (n + 1)) (f : C.pre š U n)  :
  š.1.obj (op (face Ī±)) :=
(ite (even k.1) id (has_neg.neg)) $
  š.1.map (hom_of_le $ face.le_ignore Ī± k).op $ f (ignore Ī± k)

lemma map_congr.vec_eq (f : C.pre š U n) {Ī± Ī² : fin n ā U.Ī¹} (EQ : Ī± = Ī²) :
  f Ī± = š.1.map (eq_to_hom $ by rw EQ).op (f Ī²) :=
begin
  subst EQ,
  rw [eq_to_hom_op, eq_to_hom_map],
  refl,
end

def d.to_fun.component (k : fin (n + 1)) :
  C.pre š U n ā C.pre š U (n + 1) :=
Ī» f Ī±, d.to_fun.component' Ī± k f

def d.to_fun (f : C.pre š U n) (Ī± : fin (n + 1) ā U.Ī¹) : š.1.obj (op (face Ī±)) :=
ā (k : fin (n + 1)), d.to_fun.component k f Ī±

end

-- instance {n : ā} : add_comm_group (C.pre š U n) := by apply_instance
def d : (C š U n) ā¶ (C š U (n+1)) := 
{ to_fun := Ī» f Ī±, d.to_fun f Ī±,
  map_zero' := begin
    ext1 Ī±,
    simp only [C_pre.zero_apply],
    change ā _, _ = _,
    rw finset.sum_eq_zero,
    intros i _,
    change (ite _ id _) _ = _,
    split_ifs,
    { rw [id, C_pre.zero_apply, map_zero], },
    { rw [C_pre.zero_apply, map_zero, neg_zero], },
  end,
  map_add' := Ī» f g, begin
    ext1 Ī±,
    dsimp only,
    change ā _, _ = ā _, _ + ā _, _,
    rw ā finset.sum_add_distrib,
    rw finset.sum_congr rfl,
    intros i _,
    change (ite _ id _) _ = (ite _ id _) _ + (ite _ id _) _,
    split_ifs,
    { rw [id, id, id, C_pre.add_apply, map_add], },
    { rw [C_pre.add_apply, map_add, neg_add], },
  end }

abbreviation dd : C š U n ā¶ C š U (n + 2) := d š U n ā« d š U (n + 1)

namespace dd_aux

lemma d_def (f : C š U n) (Ī± : fin (n + 1) ā U.Ī¹) :
  d š U n f Ī± =
  ā (i : fin (n+1)), 
    (ite (even i.1) id has_neg.neg)
      š.1.map (hom_of_le $ face.le_ignore Ī± i).op (f (ignore Ī± i)) :=
begin
  rw [d],
  simp only [add_monoid_hom.coe_mk, fin.val_eq_coe],
  change ā _, _ = _,
  rw finset.sum_congr rfl,
  intros i _,
  change (ite _ id _) _ = _,
  split_ifs,
  { rw [id, id], },
  { simp, },
end

lemma eq1 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  d š U (n + 1) (d š U n f) Ī± := rfl

lemma eq2 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (š.1.map (hom_of_le (face.le_ignore Ī± i)).op (d š U n f (ignore Ī± i))) :=
begin
  rw [eq1, d_def, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { simp },
  { simp },
end

lemma eq3 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (š.1.map (hom_of_le (face.le_ignore Ī± i)).op
        (ā (j : fin (n + 1)), 
          (ite (even j.1) id has_neg.neg)
            (š.1.map (hom_of_le (face.le_ignore (ignore Ī± i) j)).op (f (ignore (ignore Ī± i) j))))) :=
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

lemma eq4 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (ā (j : fin (n + 1)),
        š.1.map (hom_of_le (face.le_ignore Ī± i)).op
          ((ite (even j.1) id has_neg.neg)
            š.1.map (hom_of_le (face.le_ignore (ignore Ī± i) j)).op 
              (f (ignore (ignore Ī± i) j)))) :=
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

lemma eq5 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (ā (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignore Ī± i)).op
          (š.1.map (hom_of_le (face.le_ignore (ignore Ī± i) j)).op
            (f (ignore (ignore Ī± i) j))))) :=
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

lemma eq6ā (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (ā (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (š.1.map ((hom_of_le (face.le_ignore (ignore Ī± i) j)).op ā« (hom_of_le (face.le_ignore Ī± i)).op)
            (f (ignore (ignore Ī± i) j)))) :=
begin
  rw [eq5, finset.sum_congr rfl],
  intros i _,
  split_ifs,
  { rw [id, id, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, š.1.map_comp, comp_apply], },
    { rw [š.1.map_comp, comp_apply] }, },
  { rw [finset.neg_sum, finset.neg_sum, finset.sum_congr rfl],
    intros j _,
    split_ifs,
    { rw [id, id, š.1.map_comp, comp_apply] },
    { rw [neg_neg, neg_neg, š.1.map_comp, comp_apply] }, }
end

lemma eq6ā (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (ā (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignore Ī± i) ā« hom_of_le (face.le_ignore (ignore Ī± i) j)).op)
            (f (ignore (ignore Ī± i) j))) :=
begin
  rw [eq6ā, finset.sum_congr rfl],
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

lemma eq6ā (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)),
    (ite (even i.1) id has_neg.neg)
      (ā (j : fin (n + 1)),
        (ite (even j.1) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j))) :=
begin
  rw [eq6ā, finset.sum_congr rfl],
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

lemma eq7 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)), ā (j : fin (n + 1)),
    (ite (even i.1) id has_neg.neg)
      (ite (even j.1) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j)) :=
begin
  rw [eq6ā, finset.sum_congr rfl],
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

lemma eq8 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)), ā (j : fin (n + 1)),
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j)) :=
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
    rw ā nat.odd_iff_not_even at h2,
    have := even.add_odd h1 h2,
    rw nat.odd_iff_not_even at this,
    apply this,
    exact h, },
  { rw [id], },
  { rw ā nat.odd_iff_not_even at h1,
    have := odd.add_even h1 h,
    rw nat.odd_iff_not_even at this,
    exfalso,
    apply this,
    assumption, },
  { rw [pi.neg_apply, id], },
  { rw [pi.neg_apply, neg_neg, id], },
  { rw ā nat.odd_iff_not_even at *,
    have := odd.add_odd h1 h,
    rw nat.even_iff_not_odd at this, 
    exfalso,
    apply this,
    assumption },
end

lemma eq9 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  ā (i : fin (n + 2)), 
    ((ā (j : fin (n + 1)) in finset.univ.filter (Ī» (j : fin (n + 1)), i.1 ā¤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j))) +
    (ā (j : fin (n + 1)) in finset.univ.filter (Ī» (j : fin (n + 1)), j.1 < i.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j)))) :=
begin
  rw [eq8, finset.sum_congr rfl],
  intros i _,
  have : 
    (finset.univ.filter (Ī» (j : fin (n + 1)), j.1 < i.val)) =
    (finset.univ.filter (Ī» (j : fin (n + 1)), i.val ā¤ j.val))į¶,
  { ext1 k,
    split; 
    intros hk;
    simp only [finset.compl_filter, not_le, finset.mem_filter, finset.mem_univ, true_and] at hk ā¢;
    assumption, },
  rw [this, finset.sum_add_sum_compl],
end

lemma eq11 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā (j : fin (n + 1)) in finset.univ.filter (Ī» (j : fin (n + 1)), i.1 ā¤ j.1),
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j))) +
  (ā (i : fin (n + 2)), ā (j : fin (n + 1)) in finset.univ.filter (Ī» (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j))) :=
begin
  rw [eq9, finset.sum_add_distrib],
end

lemma eq13 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā (i : fin (n + 2)), ā (j : fin (n + 1)) in finset.univ.filter (Ī» (j : fin (n + 1)), j.1 < i.1),
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i j)).op)
            (f (ignoreā Ī± i j))) :=
begin
  rw [eq11],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i _,
  apply finset.sum_bij,

  work_on_goal 5
  { intros j hj,
    refine āØj.1, _ā©,
    rw finset.mem_Ico,
    rw finset.mem_filter at hj,
    refine āØhj.2, _ā©,
    exact j.2 },
  { intros j hj,
    dsimp only,
    rw finset.mem_filter at hj,
    apply finset.mem_attach, },
  { intros j hj,
    dsimp only,
    split_ifs,
    { rw [id, id],
      rw map_congr.vec_eq f (_ : ignoreā Ī± i j = ignoreā Ī± i āØj.1, _ā©),
      rw [ā comp_apply, ā š.1.map_comp, ā op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_eq f (_ : ignoreā Ī± i j = ignoreā Ī± i āØj.1, _ā©),
      rw [ā comp_apply, ā š.1.map_comp, ā op_comp],
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
    refine āØāØj.1, hj.2ā©, _, _ā©,
    rw finset.mem_filter,
    refine āØfinset.mem_univ āØj.val, _ā©, hj.1ā©,
    dsimp only,
    rw subtype.ext_iff_val, },
end

lemma eq14 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā (i : fin (n + 2)), ā j in (finset.range i.1).attach,
    (ite (even (i.1 + j)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_range at hj,
            have hi : i.1 ā¤ n+1,
            { linarith [i.2], },
            linarith,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) :=
begin
  rw [eq13],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i hi,
  apply finset.sum_bij',

  work_on_goal 4
  { intros j hj,
    rw finset.mem_filter at hj,
    refine āØj.1, _ā©,
    rw finset.mem_range,
    exact hj.2 },
  work_on_goal 5
  { intros j _,
    have hj := j.2,
    rw finset.mem_range at hj,
    refine āØj.1, _ā©,
    linarith [i.2], },
  { intros j hj,
    dsimp only,
    split_ifs,
    { rw [id, id],
      rw map_congr.vec_eq f (_ : ignoreā Ī± i j = ignoreā Ī± i āØj.1, _ā©),
      rw [ā comp_apply, ā š.1.map_comp, ā op_comp],
      congr,
      congr' 1,
      rw subtype.ext_iff_val, },
    { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply],
      rw map_congr.vec_eq f (_ : ignoreā Ī± i j = ignoreā Ī± i āØj.1, _ā©),
      rw [ā comp_apply, ā š.1.map_comp, ā op_comp],
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
    refine āØ_, hjā©,
    apply finset.mem_univ, },
end

lemma eq15 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā j in (finset.range n.succ).attach, ā i in (finset.Ico j.1.succ n.succ.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rwa finset.mem_Ico at hi,
            exact hi.2,
          endā© āØj.1, begin
            have hj := j.2,
            rwa finset.mem_range at hj,
          endā©)).op)
            (f (ignoreā Ī± _ _))) :=
begin
  rw [eq14],
  congr' 1,
  rw [finset.sum_sigma', finset.sum_sigma'],
  apply finset.sum_bij',
  work_on_goal 4
  { refine Ī» x h, āØāØx.2.1, begin
    have hx2 := x.2.2,
    have hx1 := x.1.2,
    rw finset.mem_range at hx2 ā¢,
    have : x.1.1 ā¤ n + 1,
    { linarith },
    refine lt_of_lt_of_le hx2 this,
  endā©, āØx.1.1, _ā©ā©, },
  work_on_goal 6
  { refine Ī» x h, āØāØx.2.1, begin
    have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx1,
    rw finset.mem_Ico at hx2,
    exact hx2.2,
  endā©, āØx.1.1, begin
    have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx1 ā¢,
    rw finset.mem_Ico at hx2,
    refine lt_of_le_of_lt _ hx2.1,
    refl, 
  endā©ā©, },
  { rintros āØāØi, hiā©, jā© h,
    dsimp only,
    congr, },
  { rintros āØāØi, hiā©, jā© h,
    simp only,
    split,
    refl,
    rw heq_iff_eq,
    rw subtype.ext_iff_val, },
  { rintros āØi, jā© h,
    simp only,
    split,
    rw subtype.ext_iff_val,
    rw heq_iff_eq,
    rw subtype.ext_iff_val, },
  { have hx1 := x.1.2,
    have hx2 := x.2.2,
    rw finset.mem_range at hx2,
    rw finset.mem_Ico,
    refine āØ_, hx1ā©,
    exact hx2, },
  { rintros āØi, jā© h,
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


lemma eq16 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, ā j in (finset.Ico i.1.succ n.succ.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØj.1, begin
            have hi := j.2,
            rwa finset.mem_Ico at hi,
            exact hi.2,
          endā© āØi.1, begin
            have hj := i.2,
            rwa finset.mem_range at hj,
          endā©)).op)
            (f (ignoreā Ī± _ _))) :=
begin
  rw [eq15],
end

lemma eq17 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even ((j.1 + 1) + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØj.1 + 1, begin
            have hi := j.2,
            rw finset.mem_Ico at hi,
            rw succ_lt_succ_iff,
            exact hi.2,
          endā© āØi.1, begin
            have hj := i.2,
            rwa finset.mem_range at hj,
          endā©)).op)
            (f (ignoreā Ī± āØj.1 + 1, _ā© āØi.1, _ā©))) :=
begin
  rw [eq16],
  congr' 1,
  rw finset.sum_congr rfl,
  intros i hi,
  apply finset.sum_bij',
  work_on_goal 4
  { intros j _, refine āØj.1.pred, _ā©,
    have hj := j.2,
    rw finset.mem_Ico at hj ā¢,
    rcases hj with āØhj1, hj2ā©,
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
  { intros j _, refine āØj.1 + 1, _ā©,
    have hj := j.2, 
    rw finset.mem_Ico at hj ā¢,
    rcases hj with āØhj1, hj2ā©,
    split,

    rwa succ_le_succ_iff,
    rwa succ_lt_succ_iff,
    },
  { intros j hj,
    dsimp only,
    rw map_congr.vec_eq f (_ : ignoreā Ī± āØj.1, _ā© āØi.1, _ā© = ignoreā Ī± āØj.1.pred + 1, _ā© āØi.1, _ā©),
    by_cases e1 : even (j.1 + i.1),
    { rw [if_pos e1, if_pos, id, id, ā comp_apply, ā š.1.map_comp], congr,
      rwa [ā nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      have hj := j.2,
      rw finset.mem_Ico at hj,
      refine lt_of_lt_of_le _ hj.1,
      exact nat.zero_lt_succ _, },
    { rw [if_neg e1, if_neg, add_monoid_hom.neg_apply, add_monoid_hom.neg_apply, ā comp_apply, ā š.1.map_comp],
      congr,
      rwa [ā nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      have hj := j.2,
      rw finset.mem_Ico at hj,
      refine lt_of_lt_of_le _ hj.1,
      exact nat.zero_lt_succ _, },
    congr,
    rwa [ā nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
    have hj := j.2,
    rw finset.mem_Ico at hj,
    refine lt_of_lt_of_le _ hj.1,
    exact nat.zero_lt_succ _, },
  { intros j hj,
    simp only,
    rw subtype.ext_iff_val,
    dsimp only,
    rw [ā nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
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

lemma eq18 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even ((j.1 + 1) + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) :=
begin
  rw eq17 š U n f Ī±,
  apply congr_arg2 (+) rfl _,
  rw [finset.sum_congr rfl],
  intros i hi,
  rw [finset.sum_congr rfl],
  intros j hj,
  generalize_proofs _ h1 h2 h3 h4 h5,
  rw map_congr.vec_eq f (_ : ignoreā Ī± āØj.1 + 1, h1ā© āØi.1, h2ā© = ignoreā Ī± āØi.1, h4ā© āØj.1, _ā©),
  split_ifs,
  { rw [id, id, ā comp_apply, ā š.1.map_comp],
    congr },
  { rw [add_monoid_hom.neg_apply, add_monoid_hom.neg_apply, ā comp_apply, ā š.1.map_comp],
    congr },
  have := ignoreā_symm' Ī± i.2 j.2,
  convert ā this,
end

lemma eq19 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā (i : fin (n + 2)), ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± i āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± i āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, - ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) :=
begin
  rw [eq18],
  congr' 1,
  rw [finset.sum_congr rfl],
  intros i _,
  rw [finset.neg_sum, finset.sum_congr rfl],
  intros j _,
  split_ifs with h1 h2,
  { exfalso,
    have o1 : odd (1 : ā) := odd_one,
    have := even.add_odd h2 o1,
    rw nat.odd_iff_not_even at this,
    apply this,
    convert h1 using 1,
    abel, },
  { rw [id, add_monoid_hom.neg_apply, neg_neg], },
  { rw [id, add_monoid_hom.neg_apply], },
  { rw ā nat.odd_iff_not_even at h h1,
    have o1 : odd (1 : ā) := odd_one,
    have := odd.add_odd h o1,
    rw nat.even_iff_not_odd at this,
    exfalso,
    apply this,
    convert h1 using 1,
    abel, },
end

lemma eq20ā (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā i in (finset.range (n+2)).attach, ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            exact finset.mem_range.mp hi,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, - ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) :=
begin
  rw [eq19],
  congr' 1,
  rw finset.sum_fin_eq_sum_range,
  rw ā finset.sum_attach,
  rw finset.sum_congr rfl,
  intros i hi,
  rw dif_pos,
  refl,
end

lemma eq20ā (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā i in (finset.range (n+1)).attach, ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) +
  (ā j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØn.succ, begin
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØn.succ, _ā© āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, - ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) :=
have eq0 : 
  ā i in (finset.range (n+2)).attach, ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
          have hi := i.2,
          exact finset.mem_range.mp hi,
        endā© āØj.1, begin
          have hj := j.2,
          rw finset.mem_Ico at hj,
          exact hj.2,
        endā©)).op)
          (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©)) =
  ā i in (insert n.succ (finset.range (n+1))).attach, ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (i.1 + j.1)) id has_neg.neg)
        (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
          have hi := i.2,
          rw finset.mem_insert at hi,
          cases hi,
          rw hi, exact lt_add_one _,

          rw finset.mem_range at hi,
          refine lt_trans hi _,
          exact lt_add_one _,
        endā© āØj.1, begin
          have hj := j.2,
          rw finset.mem_Ico at hj,
          exact hj.2,
        endā©)).op)
          (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©)),
begin
  rw finset.sum_bij',
  work_on_goal 4
  { intros a _,
    refine āØa.1, _ā©,
    rw finset.mem_insert,
    have ha := a.2,
    by_cases a.1 = n.succ, 
    left, assumption,
    right,
    rw finset.mem_range at ha ā¢,
    contrapose! h,
    have ha' : a.1 ā¤ n+1,
    linarith,
    refine le_antisymm ha' h, },
  work_on_goal 5
  { intros a _,
    refine āØa.1, _ā©,
    have ha := a.2,
    rw finset.mem_insert at ha,
    rw finset.mem_range at ha ā¢,
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
  rw [eq20ā],
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

lemma eq21 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā i in (finset.range (n+1)).attach, ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) +
  (ā i in (finset.range n.succ).attach, - ā j in (finset.Ico i.1 n.succ).attach,
    (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) +
  (ā j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØn.succ, begin
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØn.succ, _ā© āØj.1, _ā©))) :=
begin
  rw [eq20ā],
  abel,
end

lemma eq22 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā i in (finset.range (n+1)).attach, 
    ((ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (i.1 + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            refine lt_trans (finset.mem_range.mp hi) _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))) +
    (- ā j in (finset.Ico i.1 n.succ).attach,
      (ite (even (j.1 + i.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØi.1, begin
            have hi := i.2,
            rw finset.mem_range at hi,
            refine lt_trans hi _,
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØi.1, _ā© āØj.1, _ā©))))) +
  (ā j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØn.succ, begin
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØn.succ, _ā© āØj.1, _ā©))) :=
begin
  rw [eq21, finset.sum_add_distrib],
end

lemma eq23 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± =
  (ā i in (finset.range (n+1)).attach, 0) +
  (ā j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØn.succ, begin
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØn.succ, _ā© āØj.1, _ā©))) :=
begin
  rw [eq22],
  congr' 1,
  rw finset.sum_congr rfl,
  intros i _,
  simp_rw [add_comm],
  rw add_neg_eq_zero,
end

lemma eq24 (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± = 0 +
  (ā j in (finset.Ico n.succ n.succ).attach,
    (ite (even (n.succ + j.1)) id has_neg.neg)
          (š.1.map (hom_of_le (face.le_ignoreā Ī± āØn.succ, begin
            exact lt_add_one _,
          endā© āØj.1, begin
            have hj := j.2,
            rw finset.mem_Ico at hj,
            exact hj.2,
          endā©)).op)
            (f (ignoreā Ī± āØn.succ, _ā© āØj.1, _ā©))) :=
begin
  rw [eq23],
  congr',
  rw finset.sum_eq_zero,
  intros, refl,
end

lemma eq_zero (f : C š U n) (Ī± : fin (n + 2) ā U.Ī¹) :
  dd š U n f Ī± = 0 :=
begin
  rw [eq24, zero_add],
  convert finset.sum_empty,
  rw finset.Ico_self,
  rw finset.attach_empty
end

end dd_aux

lemma dd_eq_zero' (n : ā) : dd š U n = 0 :=
begin
  ext f Ī±,
  convert dd_aux.eq_zero š U n f Ī±,
end

lemma dd_eq_zero (n : ā) (f Ī±) :
  d š U (n+1) (d š U n f) Ī± = 0 :=
begin
  have : dd š U n f Ī± = 0,
  { rw dd_eq_zero', 
    simp },
  convert this,
end

end