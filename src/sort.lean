import data.finset
import tactic.linarith

section examples

variables {ι : Type*} [linear_order ι] -- [is_well_order ι ((≤) : ι → ι → Prop)]

namespace finset

def erase_nth (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) : finset ι :=
s.erase (s.order_emb_of_fin h m)

lemma mem_erase_nth (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) (i : ι) :
  i ∈ s.erase_nth h m ↔ i ≠ s.order_emb_of_fin h m ∧ i ∈ s :=
begin
  unfold erase_nth,
  rw mem_erase,
end


lemma erase_nth_card (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) :
  (s.erase_nth h m).card = k.pred :=
begin
  unfold erase_nth,
  rw finset.card_erase_eq_ite,
  split_ifs with h2,
  { rw h,
    exact nat.pred_eq_sub_one _, },
  { exfalso,
    apply h2,
    apply finset.order_emb_of_fin_mem },
end

def erase_order_emb_of_fin' (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) :
  fin k.pred ↪o ι :=
{ to_fun := λ n, 
    if (n.1 < m.1) 
    then s.order_emb_of_fin h ⟨n.1, lt_trans n.2 $ nat.pred_lt $ λ r, by rw r at m; exact fin_zero_elim m⟩ 
    else s.order_emb_of_fin h ⟨n.1.succ, by { convert nat.succ_lt_succ n.2, rw nat.succ_pred_eq_of_pos, apply nat.pos_of_ne_zero (λ r, _), rw r at m, exact fin_zero_elim m } ⟩,
  inj' := λ x y H, begin
    dsimp only at H,
    split_ifs at H with hx hy;
    have := (s.order_emb_of_fin h).inj' H;
    rw subtype.ext_iff_val at this ⊢,
    { exact this, },
    { rw this at *,
      exfalso,
      apply hy,
      exact lt_trans (lt_add_one _) hx, },
    { rw ← this at *,
      exfalso,
      apply hx,
      exact lt_trans (lt_add_one _) (by assumption) },
    { apply_fun nat.succ using nat.succ_injective,
      exact this },
  end,
  map_rel_iff' := λ a b, begin
    split,
    { intro H,
      simp only [function.embedding.coe_fn_mk] at H,
      split_ifs at H with h1 h2 h3,
      { rw order_embedding.le_iff_le (s.order_emb_of_fin h) at H,
        convert H },
      { rw order_embedding.le_iff_le (s.order_emb_of_fin h) at H,
        change a.1 ≤ b.1.succ at H,
        change a.1 ≤ b.1,
        linarith },
      { rw order_embedding.le_iff_le (s.order_emb_of_fin h) at H,
        change a.1.succ ≤ b.1 at H,
        change a.1 ≤ b.1,
        exfalso,
        apply h1,
        transitivity a.1.succ,
        { exact lt_add_one _ },
        { exact lt_of_le_of_lt H h3 } },
      { rw order_embedding.le_iff_le (s.order_emb_of_fin h) at H,
        change a.1.succ ≤ b.1.succ at H,
        rw nat.succ_le_succ_iff at H,
        convert H, } },
    { intro H,
      change a.1 ≤ b.1 at H,
      simp only [function.embedding.coe_fn_mk],
      split_ifs with h1 h2 h3;
      rw order_embedding.le_iff_le (s.order_emb_of_fin h),
      { change a.1 ≤ b.1,
        exact H },
      { change a.1 ≤ b.1.succ,
        transitivity b.1,
        { exact H },
        { exact le_of_lt (lt_add_one _) } },
      { change a.1.succ ≤ b.1,
        contrapose! h1,
        rw nat.lt_succ_iff_lt_or_eq at h1,
        cases h1,
        { linarith },
        { rwa h1 at h3 }, },
      { change a.1.succ ≤ b.1.succ,
        rwa nat.succ_le_succ_iff } }
  end }

lemma erase_order_emb_of_fin'_mem (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) (x : fin k.pred) :
  s.erase_order_emb_of_fin' h m x ∈ s.erase_nth h m := 
begin
  unfold erase_order_emb_of_fin',
  simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk],
  unfold erase_nth,
  split_ifs with h2,
  { rw mem_erase,
    refine ⟨λ r, _, order_emb_of_fin_mem s h _⟩,
    replace r := (s.order_emb_of_fin h).inj' r,
    rw subtype.ext_iff_val at r,
    linarith, },
  { rw mem_erase,
    refine ⟨λ r, _, order_emb_of_fin_mem s h _⟩,
    replace r := (s.order_emb_of_fin h).inj' r,
    rw subtype.ext_iff_val at r,
    rw ← r at h2,
    change ¬ x.1 < x.1.succ at h2,
    apply h2,
    exact lt_add_one _, },
end

theorem erase_order_emb_of_fin'_eq (s : finset ι) {k : ℕ} (h : s.card = k) (m : fin k) :
  (s.erase_nth h m).order_emb_of_fin (s.erase_nth_card h m) = 
  s.erase_order_emb_of_fin' h m := 
begin
  symmetry,
  have := finset.order_emb_of_fin_unique (s.erase_nth_card h m) begin
    intros x,
    apply erase_order_emb_of_fin'_mem,
  end (order_embedding.strict_mono (s.erase_order_emb_of_fin' h m)),
  ext x,
  rw this,
end

end finset

end examples