-- import topology.sheaves.sheaf
-- import sort
-- import algebra.category.Group.limits
-- import oc

-- section 

-- open category_theory Top Top.sheaf topological_space finset
-- open opposite

-- variable (X : Top) 

-- variable {X}
-- variable (π : sheaf Ab X)
-- variable (π : oc X)

-- local notation `ΞΉ ` := π.ΞΉ
-- local notation `π.obj` := π.1.obj
-- local notation `π.map` := π.1.map

-- @[ext] structure simplex (n : β) extends finset ΞΉ :=
-- (card_eq : to_finset.card = n.succ)

-- attribute [simp] simplex.card_eq

-- namespace simplex

-- variables {π}

-- def nth {n : β} (Ο : simplex π n) (m : fin n.succ) : ΞΉ :=
-- Ο.to_finset.order_emb_of_fin Ο.2 m

-- instance {n : β} : has_mem ΞΉ (simplex π n) :=
-- { mem := Ξ» i Ο, i β Ο.to_finset }

-- lemma nth_mem {n : β} (Ο : simplex π n) (m : fin n.succ) :
--   Ο.nth m β Ο :=
-- Ο.to_finset.order_emb_of_fin_mem Ο.card_eq m

-- def zero_from (i : ΞΉ) : simplex π 0 :=
-- { to_finset := {i},
--   card_eq := rfl }

-- variables {n : β} (hn : 0 < n)

-- def ignore (Ο : simplex π n) (m : fin n.succ) : simplex π n.pred :=
-- { to_finset := Ο.1.erase_nth Ο.2 m,
--   card_eq := (nat.succ_pred_eq_of_pos hn).symm βΈ Ο.1.erase_nth_card _ m }

-- lemma mem_ignore (Ο : simplex π n) (m : fin n.succ) (i : ΞΉ) :
--   i β Ο.ignore hn m β i β Ο β§ i β  Ο.nth m :=
-- begin
--   split,
--   { intros hi,
--     change i β simplex.to_finset _ at hi,
--     unfold ignore at hi,
--     dsimp only at hi,
--     rw mem_erase_nth at hi,
--     refine β¨hi.2, hi.1β©, },
--   { intros hi,
--     change i β simplex.to_finset _,
--     unfold ignore,
--     dsimp only,
--     rw mem_erase_nth,
--     refine β¨hi.2, hi.1β©, },
-- end 

-- def ignoreβ (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ) : simplex π n.pred :=
-- (Ο.ignore (nat.zero_lt_succ _) m).ignore hn m'

-- lemma ignore_subset (Ο : simplex π n) (m : fin n.succ) :
--   (Ο.ignore hn m).to_finset β Ο.to_finset := Ξ» x hx,
-- begin
--   change x β finset.erase _ _ at hx,
--   rw finset.mem_erase at hx,
--   exact hx.2,
-- end

-- lemma ignoreβ_subset (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
--   (Ο.ignoreβ hn m m').to_finset β Ο.to_finset :=
-- subset.trans ((Ο.ignore (nat.zero_lt_succ _) m).ignore_subset hn m') $ Ο.ignore_subset _ _

-- lemma ignoreβ_to_finset_case1 (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m'.1 < m.1) :
--   (Ο.ignoreβ hn m m').to_finset =
--   Ο.to_finset \ 
--   { Ο.1.order_emb_of_fin Ο.2 m, 
--     Ο.1.order_emb_of_fin Ο.2 β¨m'.1, lt_trans m'.2 (lt_add_one n.succ)β© } :=
-- begin
--   unfold ignoreβ ignore,
--   dsimp,
--   ext i,
--   split,
--   { intros hi,
--     erw [mem_erase_nth, Ο.to_finset.erase_order_emb_of_fin'_eq Ο.2 m] at hi,
--     unfold erase_order_emb_of_fin' at hi,
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth] at hi,
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
--     tauto },
--   { intros hi,
--     erw [mem_erase_nth, Ο.to_finset.erase_order_emb_of_fin'_eq Ο.2 m, mem_erase_nth],
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
--     refine β¨_, hi.2.1, hi.1β©,
--     convert hi.2.2,
--     unfold erase_order_emb_of_fin',
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth],
--     refl, }
-- end

-- lemma ignoreβ_to_finset_case2 (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 β€ m'.1) :
--   (Ο.ignoreβ hn m m').to_finset =
--   Ο.to_finset \ 
--   { Ο.to_finset.order_emb_of_fin Ο.2 m, 
--     Ο.to_finset.order_emb_of_fin Ο.2 β¨m'.1.succ, nat.succ_lt_succ m'.2β© } :=
-- begin
--   have ineq : Β¬ m'.1 < m.1,
--   { rwa not_lt },
--   unfold ignoreβ ignore,
--   dsimp,
--   ext i,
--   split,
--   { intros hi,
--     erw [mem_erase_nth, Ο.to_finset.erase_order_emb_of_fin'_eq Ο.2 m] at hi,
--     unfold erase_order_emb_of_fin' at hi,
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth] at hi,
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
--     tauto },
--   { intros hi,
--     erw [mem_erase_nth, Ο.to_finset.erase_order_emb_of_fin'_eq Ο.2 m, mem_erase_nth],
--     rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
--     refine β¨_, hi.2.1, hi.1β©,
--     convert hi.2.2,
--     unfold erase_order_emb_of_fin',
--     simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth],
--     refl, }
-- end

-- lemma ignoreβ_eq_ignoreβ.aux (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 β€ m'.1) :
--   (Ο.ignoreβ hn m m').to_finset = 
--   (Ο.ignoreβ hn β¨m'.1.succ, nat.succ_lt_succ m'.2β© β¨m.1, by linarith [m'.2]β©).to_finset :=
-- begin
--   rw [ignoreβ_to_finset_case2 _ _ _ _ hmm', ignoreβ_to_finset_case1],
--   { ext i,
--     split;
--     { intros hi,
--       rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi β’,
--       tauto, } },
--   { dsimp only,
--     exact lt_of_le_of_lt hmm' (lt_add_one _), },
-- end

-- lemma ignoreβ_eq_ignoreβ (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
--   (hmm' : m.1 β€ m'.1) :
--   (Ο.ignoreβ hn m m') = 
--   (Ο.ignoreβ hn β¨m'.1.succ, nat.succ_lt_succ m'.2β© β¨m.1, by linarith [m'.2]β©) :=
-- by rw [simplex.ext_iff, ignoreβ_eq_ignoreβ.aux]

-- def face {n : β} (Ο : simplex π n) : opens X :=
-- β¨ (i : ΞΉ) (H : i β Ο.to_finset), π.cover i

-- lemma face0 (Ο : simplex π 0) :
--   Ο.face = π.cover (Ο.nth 0) := 
-- begin
--   unfold face,
--   have eq1 : Ο.to_finset = {Ο.nth 0},
--   { rcases card_eq_one.mp Ο.2 with β¨a, eq1β©,
--     have := Ο.nth_mem 0,
--     change _ β Ο.to_finset at this,
--     rw eq1 at *,
--     rw mem_singleton at this,
--     rw this },
--   rw [eq1, finset.infi_singleton],
-- end

-- lemma face1 (Ο : simplex π 1) :
--   Ο.face = π.cover (Ο.nth 0) β π.cover (Ο.nth β¨1, one_lt_twoβ©) :=
-- begin
--   rcases card_eq_two.mp Ο.2 with β¨a, b, ineq, eq1β©,
--   have mem1 : (_ β Ο.to_finset) := Ο.nth_mem 0,
--   have mem2 : (_ β Ο.to_finset) := Ο.nth_mem β¨1, one_lt_twoβ©,
--   have ineq2 : Ο.nth 0 β  Ο.nth β¨1, one_lt_twoβ©,
--   { intro rid,
--     unfold simplex.nth at rid,
--     replace rid := (Ο.to_finset.order_emb_of_fin Ο.2).inj' rid,
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

-- def subsetβ {n : β} (Ο : simplex π n) (m : fin n.succ) :
--   Ο.face βΆ (simplex.zero_from π (Ο.nth m)).face := hom_of_le $ Ξ» p hp, 
-- begin
--   rw [opens.mem_coe] at hp β’,
--   rw face0,
--   change _ β (infi _) at hp,
--   have := (infi_le _ : β _,  Ο.face β€ _),
--   specialize this ((simplex.zero_from π (Ο.nth m)).nth 0),
--   simp only [le_infi_iff] at this,
--   refine this _ hp,
--   have : _ β {_} := (simplex.zero_from π (Ο.nth m)).nth_mem 0,
--   rw mem_singleton at this,
--   rw this,
--   apply simplex.nth_mem,
-- end

-- def der {n : β} (hn : 0 < n) (Ο : simplex π n) (m : fin n.succ) :
--   Ο.face βΆ (Ο.ignore hn m).face := hom_of_le $ Ξ» p hp, 
-- begin
--   rw [opens.mem_coe] at hp β’,
--   rcases hp with β¨S, β¨oS, hSβ©, p_memβ©,
--   refine β¨S, β¨oS, Ξ» x x_mem, _β©, p_memβ©,
--   specialize hS x_mem,
--   simp only [subtype.val_eq_coe, set.Inf_eq_sInter, set.sInter_image, set.mem_range, 
--     set.Inter_exists, set.Inter_Inter_eq', set.mem_Inter, opens.mem_coe] at hS β’,
--   intros i,
--   specialize hS i,
--   rcases hS with β¨w, β¨hw1, hw2β©, hxβ©,
--   refine β¨w, β¨hw1, _β©, hxβ©,
--   intros y hy,
--   specialize hw2 hy,
--   simp only [subtype.val_eq_coe, set.Inf_eq_sInter, set.sInter_image, set.mem_range, exists_prop, 
--     set.mem_Inter, opens.mem_coe, and_imp, forall_apply_eq_imp_iff'] at hw2 β’,
--   intros hi2,
--   apply hw2,
--   apply simplex.ignore_subset,
--   exact hi2,
-- end

-- def dder {n : β} (hn : 0 < n) (Ο : simplex π n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
--   Ο.face βΆ (Ο.ignoreβ hn m m').face :=
-- der (nat.zero_lt_succ _) Ο m β« der _ (Ο.ignore _ m) m'

-- section refinement

-- variables {A B : X.oc} (h : A βΆ B) (inj : function.injective h.func)

-- include inj
-- def refine (Ο : simplex A n) : simplex B n :=
-- { to_finset := finset.image h.func Ο.to_finset,
--   card_eq := begin
--     rw [β Ο.2, finset.card_image_of_inj_on],
--     apply function.injective.inj_on,
--     assumption,
--   end }

-- -- lemma refine_self (Ο : simplex A n) :
-- --   Ο.refine (π A) = Ο :=
-- -- begin
-- --   ext i,
-- --   split,
-- --   { intros hi,
-- --     unfold simplex.refine at hi,
-- --     dsimp only at hi,
-- --     change i β finset.image id _ at hi,
-- --     rw finset.mem_image at hi,
-- --     rcases hi with β¨a, ha, rflβ©,
-- --     exact ha },
-- --   { intros hi,
-- --     unfold simplex.refine,
-- --     dsimp only,
-- --     change i β finset.image id _,
-- --     rw finset.mem_image,
-- --     refine β¨i, hi, rflβ©, },
-- -- end

-- -- lemma refine_comp {n : β} {A B D : X.oc} (r1 : A βΆ B) (r2 : B βΆ D) (Ο : simplex A n) :
-- --   Ο.refine (r1 β« r2) = (Ο.refine r1).refine r2 :=
-- -- begin
-- --   ext d,
-- --   split;
-- --   intros hd;
-- --   unfold simplex.refine at hd β’;
-- --   dsimp only at hd β’;
-- --   rw finset.mem_image at hd β’,
-- --   { rcases hd with β¨a, ha, rflβ©,
-- --     refine β¨r1.func a, _, rflβ©,
-- --     rw finset.mem_image,
-- --     exact β¨a, ha, rflβ©, },
-- --   { rcases hd with β¨b, hb, rflβ©, 
-- --     rw finset.mem_image at hb,
-- --     rcases hb with β¨a, ha, rflβ©,
-- --     exact β¨a, ha, rflβ©, },
-- -- end

-- -- lemma refine_ignore {n : β} (hn : 0 < n) {A B : oc X} (h : A βΆ B) (inj : function.injective h.func) (Ο : simplex A n) (m : fin n.succ) : 
-- --   (Ο.refine h inj).ignore hn m = (Ο.ignore hn m).refine h inj := 
-- -- begin
-- --   ext i,
-- --   split,
-- --   { rintros (hi : i β simplex.ignore hn (simplex.refine h inj Ο) m),
-- --     rw simplex.mem_ignore at hi, 
-- --     rcases hi with β¨h1, h2β©,
-- --     change _ β simplex.to_finset _ at h1,
-- --     unfold simplex.refine at h1 β’,
-- --     dsimp only at h1 β’,
-- --     rw finset.mem_image at h1 β’,
-- --     rcases h1 with β¨a, ha, rflβ©,
-- --     refine β¨a, _, rflβ©,
-- --     change a β simplex.ignore hn Ο m,
-- --     rw simplex.mem_ignore,
-- --     refine β¨ha, _β©,
-- --     contrapose! h2,
-- --     rw [simplex.refine_nth, h2] },
-- --   { rintros hi,
-- --     erw simplex.mem_ignore,
-- --     change i β simplex.to_finset _ β§ _,
-- --     unfold simplex.refine at hi,
-- --     dsimp only at hi,
-- --     rw finset.mem_image at hi,
-- --     rcases hi with β¨a, ha, rflβ©,
-- --     erw simplex.mem_ignore at ha,
-- --     rcases ha with β¨h1, h2β©,
-- --     refine β¨_, _β©,
-- --     { change _ β simplex.to_finset _,
-- --       unfold simplex.refine,
-- --       dsimp only,
-- --       rw finset.mem_image,
-- --       exact β¨a, h1, rflβ©, },
-- --     { contrapose! h2,
-- --       rw simplex.refine_nth at h2,
-- --       exact h.strict_mono.injective h2, } },
-- -- end

-- end refinement

-- end simplex

-- end