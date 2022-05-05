import topology.category.Top.opens

section

open category_theory Top topological_space

lemma opens.finset_infi {ι : Type*} {X : Top} (f : ι -> opens X) (s : finset ι) (x : X) :
  (x ∈ ⨅ (i : ι) (hi : i ∈ s), f i) ↔ ∀ (i : ι), i ∈ s → x ∈ f i :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  induction s using finset.induction_on with i s hi ih,
  { split,
    { intros hx,
      intros i hi,
      exfalso,
      exact finset.not_mem_empty _ hi, },
    { intros hx,
      simp only [infi_false, infi_top]}, },
  { split,
    { intros hx,
      intros j hj,
      rw finset.mem_insert at hj,
      rcases hj with rfl|hj,
      { simp only [finset.infi_insert] at hx,
        rw ← opens.inter_eq at hx,
        rcases hx with ⟨h1, h2⟩,
        exact h1 },
      { refine ih.mp _ j hj,
        rw finset.infi_insert at hx,
        rw ← opens.inter_eq at hx,
        rcases hx with ⟨h1, h2⟩,
        exact h2, }, },
    { intros hx,
      rw finset.infi_insert,
      rw ← opens.inter_eq,
      refine ⟨_, _⟩,
      { apply hx,
        exact finset.mem_insert_self i s, },
      { refine ih.mpr _,
        intros j hj,
        apply hx,
        exact finset.mem_insert_of_mem hj, }, }, },
end

lemma opens.fintype_infi_aux {ι : Type*} [h : fintype ι] {X : Top} (f : ι -> opens X) :
  infi f = ⨅ (i ∈ h.elems), f i :=
begin
  have h2 := h.2,
  refine le_antisymm _ _,
  { rw infi_le_iff,
    intros u h3,
    simp only [le_infi₂_iff],
    intros i hi,
    apply h3, },
  { rw infi_le_iff,
    intros i hi,
    simp only [le_infi_iff],
    intros j,
    specialize hi j,
    rw le_infi_iff at hi,
    apply hi,
    apply h.2 },
end

lemma opens.fintype_infi {ι : Type*} [fintype ι] {X : Top} (f : ι -> opens X) (x : X) :
  x ∈ infi f ↔ ∀ i : ι, x ∈ f i :=
begin
  rw opens.fintype_infi_aux,
  rw opens.finset_infi,
  split,
  { intros hi i,
    apply hi,
    exact fintype.complete i, },
  { intros hi i _,
    apply hi, },
end

end