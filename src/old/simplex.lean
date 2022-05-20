-- import topology.sheaves.sheaf
-- import sort
-- import algebra.category.Group.limits
-- import oc

-- section 

-- open category_theory Top Top.sheaf topological_space finset
-- open opposite

-- variable (X : Top) 

-- variable {X}
-- variable (𝓕 : sheaf Ab X)
-- variable (𝔘 : oc X)

-- local notation `ι ` := 𝔘.ι
-- local notation `𝓕.obj` := 𝓕.1.obj
-- local notation `𝓕.map` := 𝓕.1.map

-- @[ext] structure simplex (n : ℕ) extends finset ι :=
-- (card_eq : to_finset.card = n.succ)

-- attribute [simp] simplex.card_eq

-- namespace simplex

-- variables {𝔘}

-- def nth {n : ℕ} (σ : simplex 𝔘 n) (m : fin n.succ) : ι :=
-- σ.to_finset.order_emb_of_fin σ.2 m

-- instance {n : ℕ} : has_mem ι (simplex 𝔘 n) :=
-- { mem := λ i σ, i ∈ σ.to_finset }

-- lemma nth_mem {n : ℕ} (σ : simplex 𝔘 n) (m : fin n.succ) :
--   σ.nth m ∈ σ :=
-- σ.to_finset.order_emb_of_fin_mem σ.card_eq m

-- def zero_from (i : ι) : simplex 𝔘 0 :=
-- { to_finset := {i},
--   card_eq := rfl }

-- variables {n : ℕ} (hn : 0 < n)

-- def ignore (σ : simplex 𝔘 n) (m : fin n.succ) : simplex 𝔘 n.pred :=
-- { to_finset := σ.1.erase_nth σ.2 m,
--   card_eq := (nat.succ_pred_eq_of_pos hn).symm ▸ σ.1.erase_nth_card _ m }

-- lemma mem_ignore (σ : simplex 𝔘 n) (m : fin n.succ) (i : ι) :
--   i ∈ σ.ignore hn m ↔ i ∈ σ ∧ i ≠ σ.nth m :=
-- begin
--   split,
--   { intros hi,
--     change i ∈ simplex.to_finset _ at hi,
--     unfold ignore at hi,
--     dsimp only at hi,
--     rw mem_erase_nth at hi,
--     refine ⟨hi.2, hi.1⟩, },
--   { intros hi,
--     change i ∈ simplex.to_finset _,
--     unfold ignore,
--     dsimp only,
--     rw mem_erase_nth,
--     refine ⟨hi.2, hi.1⟩, },
-- end 

-- def ignore₂ (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) : simplex 𝔘 n.pred :=
-- (σ.ignore (nat.zero_lt_succ _) m).ignore hn m'

-- lemma ignore_subset (σ : simplex 𝔘 n) (m : fin n.succ) :
--   (σ.ignore hn m).to_finset ⊆ σ.to_finset := λ x hx,
-- begin
--   change x ∈ finset.erase _ _ at hx,
--   rw finset.mem_erase at hx,
--   exact hx.2,
-- end

-- lemma ignore₂_subset (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
--   (σ.ignore₂ hn m m').to_finset ⊆ σ.to_finset :=
-- subset.trans ((σ.ignore (nat.zero_lt_succ _) m).ignore_subset hn m') $ σ.ignore_subset _ _

-- lemma ignore₂_to_finset_case1 (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m'.1 < m.1) :
--   (σ.ignore₂ hn m m').to_finset =
--   σ.to_finset \ 
--   { σ.1.order_emb_of_fin σ.2 m, 
--     σ.1.order_emb_of_fin σ.2 ⟨m'.1, lt_trans m'.2 (lt_add_one n.succ)⟩ } :=
-- begin
--   unfold ignore₂ ignore,
--   dsimp,
--   ext i,
--   split,
--   { intros hi,
--     erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m] at hi,
--     unfold erase_order_emb_of_fin' at hi,
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth] at hi,
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
--     tauto },
--   { intros hi,
--     erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m, mem_erase_nth],
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
--     refine ⟨_, hi.2.1, hi.1⟩,
--     convert hi.2.2,
--     unfold erase_order_emb_of_fin',
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth],
--     refl, }
-- end

-- lemma ignore₂_to_finset_case2 (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 ≤ m'.1) :
--   (σ.ignore₂ hn m m').to_finset =
--   σ.to_finset \ 
--   { σ.to_finset.order_emb_of_fin σ.2 m, 
--     σ.to_finset.order_emb_of_fin σ.2 ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ } :=
-- begin
--   have ineq : ¬ m'.1 < m.1,
--   { rwa not_lt },
--   unfold ignore₂ ignore,
--   dsimp,
--   ext i,
--   split,
--   { intros hi,
--     erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m] at hi,
--     unfold erase_order_emb_of_fin' at hi,
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth] at hi,
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
--     tauto },
--   { intros hi,
--     erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m, mem_erase_nth],
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
--     refine ⟨_, hi.2.1, hi.1⟩,
--     convert hi.2.2,
--     unfold erase_order_emb_of_fin',
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth],
--     refl, }
-- end

-- lemma ignore₂_eq_ignore₂.aux (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 ≤ m'.1) :
--   (σ.ignore₂ hn m m').to_finset = 
--   (σ.ignore₂ hn ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ ⟨m.1, by linarith [m'.2]⟩).to_finset :=
-- begin
--   rw [ignore₂_to_finset_case2 _ _ _ _ hmm', ignore₂_to_finset_case1],
--   { ext i,
--     split;
--     { intros hi,
--       rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi ⊢,
--       tauto, } },
--   { dsimp only,
--     exact lt_of_le_of_lt hmm' (lt_add_one _), },
-- end

-- lemma ignore₂_eq_ignore₂ (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 ≤ m'.1) :
--   (σ.ignore₂ hn m m') = 
--   (σ.ignore₂ hn ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ ⟨m.1, by linarith [m'.2]⟩) :=
-- by rw [simplex.ext_iff, ignore₂_eq_ignore₂.aux]

-- def face {n : ℕ} (σ : simplex 𝔘 n) : opens X :=
-- ⨅ (i : ι) (H : i ∈ σ.to_finset), 𝔘.cover i

-- lemma face0 (σ : simplex 𝔘 0) :
--   σ.face = 𝔘.cover (σ.nth 0) := 
-- begin
--   unfold face,
--   have eq1 : σ.to_finset = {σ.nth 0},
--   { rcases card_eq_one.mp σ.2 with ⟨a, eq1⟩,
--     have := σ.nth_mem 0,
--     change _ ∈ σ.to_finset at this,
--     rw eq1 at *,
--     rw mem_singleton at this,
--     rw this },
--   rw [eq1, finset.infi_singleton],
-- end

-- lemma face1 (σ : simplex 𝔘 1) :
--   σ.face = 𝔘.cover (σ.nth 0) ⊓ 𝔘.cover (σ.nth ⟨1, one_lt_two⟩) :=
-- begin
--   rcases card_eq_two.mp σ.2 with ⟨a, b, ineq, eq1⟩,
--   have mem1 : (_ ∈ σ.to_finset) := σ.nth_mem 0,
--   have mem2 : (_ ∈ σ.to_finset) := σ.nth_mem ⟨1, one_lt_two⟩,
--   have ineq2 : σ.nth 0 ≠ σ.nth ⟨1, one_lt_two⟩,
--   { intro rid,
--     unfold simplex.nth at rid,
--     replace rid := (σ.to_finset.order_emb_of_fin σ.2).inj' rid,
--     rw subtype.ext_iff_val at rid,
--     change 0 = 1 at rid,
--     linarith, },
--   rw [eq1, mem_insert, mem_singleton] at mem1 mem2,
--   unfold face,
--   rw [eq1, finset.infi_insert, finset.infi_singleton],
--   cases mem1;
--   cases mem2;
--   rw [mem1, mem2] at *;
--   tauto <|> exact inf_comm,
-- end

-- def subset₀ {n : ℕ} (σ : simplex 𝔘 n) (m : fin n.succ) :
--   σ.face ⟶ (simplex.zero_from 𝔘 (σ.nth m)).face := hom_of_le $ λ p hp, 
-- begin
--   rw [opens.mem_coe] at hp ⊢,
--   rw face0,
--   change _ ∈ (infi _) at hp,
--   have := (infi_le _ : ∀ _,  σ.face ≤ _),
--   specialize this ((simplex.zero_from 𝔘 (σ.nth m)).nth 0),
--   simp only [le_infi_iff] at this,
--   refine this _ hp,
--   have : _ ∈ {_} := (simplex.zero_from 𝔘 (σ.nth m)).nth_mem 0,
--   rw mem_singleton at this,
--   rw this,
--   apply simplex.nth_mem,
-- end

-- def der {n : ℕ} (hn : 0 < n) (σ : simplex 𝔘 n) (m : fin n.succ) :
--   σ.face ⟶ (σ.ignore hn m).face := hom_of_le $ λ p hp, 
-- begin
--   rw [opens.mem_coe] at hp ⊢,
--   rcases hp with ⟨S, ⟨oS, hS⟩, p_mem⟩,
--   refine ⟨S, ⟨oS, λ x x_mem, _⟩, p_mem⟩,
--   specialize hS x_mem,
--   simp only [subtype.val_eq_coe, set.Inf_eq_sInter, set.sInter_image, set.mem_range, 
--     set.Inter_exists, set.Inter_Inter_eq', set.mem_Inter, opens.mem_coe] at hS ⊢,
--   intros i,
--   specialize hS i,
--   rcases hS with ⟨w, ⟨hw1, hw2⟩, hx⟩,
--   refine ⟨w, ⟨hw1, _⟩, hx⟩,
--   intros y hy,
--   specialize hw2 hy,
--   simp only [subtype.val_eq_coe, set.Inf_eq_sInter, set.sInter_image, set.mem_range, exists_prop, 
--     set.mem_Inter, opens.mem_coe, and_imp, forall_apply_eq_imp_iff'] at hw2 ⊢,
--   intros hi2,
--   apply hw2,
--   apply simplex.ignore_subset,
--   exact hi2,
-- end

-- def dder {n : ℕ} (hn : 0 < n) (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
--   σ.face ⟶ (σ.ignore₂ hn m m').face :=
-- der (nat.zero_lt_succ _) σ m ≫ der _ (σ.ignore _ m) m'

-- section refinement

-- variables {A B : X.oc} (h : A ⟶ B) (inj : function.injective h.func)

-- include inj
-- def refine (σ : simplex A n) : simplex B n :=
-- { to_finset := finset.image h.func σ.to_finset,
--   card_eq := begin
--     rw [← σ.2, finset.card_image_of_inj_on],
--     apply function.injective.inj_on,
--     assumption,
--   end }

-- -- lemma refine_self (σ : simplex A n) :
-- --   σ.refine (𝟙 A) = σ :=
-- -- begin
-- --   ext i,
-- --   split,
-- --   { intros hi,
-- --     unfold simplex.refine at hi,
-- --     dsimp only at hi,
-- --     change i ∈ finset.image id _ at hi,
-- --     rw finset.mem_image at hi,
-- --     rcases hi with ⟨a, ha, rfl⟩,
-- --     exact ha },
-- --   { intros hi,
-- --     unfold simplex.refine,
-- --     dsimp only,
-- --     change i ∈ finset.image id _,
-- --     rw finset.mem_image,
-- --     refine ⟨i, hi, rfl⟩, },
-- -- end

-- -- lemma refine_comp {n : ℕ} {A B D : X.oc} (r1 : A ⟶ B) (r2 : B ⟶ D) (σ : simplex A n) :
-- --   σ.refine (r1 ≫ r2) = (σ.refine r1).refine r2 :=
-- -- begin
-- --   ext d,
-- --   split;
-- --   intros hd;
-- --   unfold simplex.refine at hd ⊢;
-- --   dsimp only at hd ⊢;
-- --   rw finset.mem_image at hd ⊢,
-- --   { rcases hd with ⟨a, ha, rfl⟩,
-- --     refine ⟨r1.func a, _, rfl⟩,
-- --     rw finset.mem_image,
-- --     exact ⟨a, ha, rfl⟩, },
-- --   { rcases hd with ⟨b, hb, rfl⟩, 
-- --     rw finset.mem_image at hb,
-- --     rcases hb with ⟨a, ha, rfl⟩,
-- --     exact ⟨a, ha, rfl⟩, },
-- -- end

-- -- lemma refine_ignore {n : ℕ} (hn : 0 < n) {A B : oc X} (h : A ⟶ B) (inj : function.injective h.func) (σ : simplex A n) (m : fin n.succ) : 
-- --   (σ.refine h inj).ignore hn m = (σ.ignore hn m).refine h inj := 
-- -- begin
-- --   ext i,
-- --   split,
-- --   { rintros (hi : i ∈ simplex.ignore hn (simplex.refine h inj σ) m),
-- --     rw simplex.mem_ignore at hi, 
-- --     rcases hi with ⟨h1, h2⟩,
-- --     change _ ∈ simplex.to_finset _ at h1,
-- --     unfold simplex.refine at h1 ⊢,
-- --     dsimp only at h1 ⊢,
-- --     rw finset.mem_image at h1 ⊢,
-- --     rcases h1 with ⟨a, ha, rfl⟩,
-- --     refine ⟨a, _, rfl⟩,
-- --     change a ∈ simplex.ignore hn σ m,
-- --     rw simplex.mem_ignore,
-- --     refine ⟨ha, _⟩,
-- --     contrapose! h2,
-- --     rw [simplex.refine_nth, h2] },
-- --   { rintros hi,
-- --     erw simplex.mem_ignore,
-- --     change i ∈ simplex.to_finset _ ∧ _,
-- --     unfold simplex.refine at hi,
-- --     dsimp only at hi,
-- --     rw finset.mem_image at hi,
-- --     rcases hi with ⟨a, ha, rfl⟩,
-- --     erw simplex.mem_ignore at ha,
-- --     rcases ha with ⟨h1, h2⟩,
-- --     refine ⟨_, _⟩,
-- --     { change _ ∈ simplex.to_finset _,
-- --       unfold simplex.refine,
-- --       dsimp only,
-- --       rw finset.mem_image,
-- --       exact ⟨a, h1, rfl⟩, },
-- --     { contrapose! h2,
-- --       rw simplex.refine_nth at h2,
-- --       exact h.strict_mono.injective h2, } },
-- -- end

-- end refinement

-- end simplex

-- end