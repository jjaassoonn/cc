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

end