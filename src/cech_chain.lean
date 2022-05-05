import cech_d
import algebra.homology.homological_complex
import algebra.homology.homology
import algebraic_geometry.sheafed_space
import category_theory.opposites
import oc
import simplex
import algebra.category.Group.colimits
import algebra.category.Group.limits
import lemmas.ulift
import topology.sheaves.sheaf_condition.unique_gluing
import lemmas.about_opens

section

-- open_locale classical
open category_theory Top Top.presheaf category_theory.limits

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (𝔘 : X.ocᵒᵖ)

section

open topological_space opposite category_theory.opposite Top
open_locale big_operators

lemma face.refine {n : ℕ} {A B : oc X} (h : A ⟶ B) (inj : function.injective h.func) (σ : simplex A n) :
  σ.face ≤ (σ.refine h inj).face := 
begin
  change infi _ ≤ infi _,
  change infi _ ≤ ⨅ (i : B.ι) (H : i ∈ finset.image h.func σ.to_finset), B.cover i,
  induction σ.to_finset using finset.induction with a s ha ih,
  { rw finset.image_empty,
    simp only [infi_false, infi_top, top_le_iff], },
  { rw [finset.infi_insert, finset.image_insert, finset.infi_insert],
    refine le_trans (inf_le_inf_left (A.cover a) ih) _,
    exact inf_le_inf_right _ (h.is_refinement a), },
end

@[simps]
noncomputable
def C.refine (n : ℕ) {A B : oc X} (h : A ⟶ B) :
  C 𝓕 B n ⟶ C 𝓕 A n :=
begin
  haveI : decidable (function.injective h.func) := classical.dec _,
  refine { to_fun := λ f σ, dite (function.injective h.func) _ _,
    map_zero' := _,
    map_add' := λ f g, _ },
  { intros inj,
    exact 𝓕.1.map (hom_of_le $ face.refine h inj σ).op (f (σ.refine h inj)), },
  { intros ninj,
    exact 0 },
  { ext1 σ,
    dsimp only,
    split_ifs,
    { simp only [Cech.zero_apply, map_zero] },
    { simp only [Cech.zero_apply], }, },
  { ext1 σ,
    split_ifs,
    { simp, },
    { simp, }, }
end

lemma C.refine_apply_if_pos (n : ℕ) {A B : oc X} (h : A ⟶ B)
  (inj : function.injective h.func) (f : C 𝓕 B n) (σ : simplex _ n) :
  C.refine 𝓕 n h f σ = 𝓕.1.map (hom_of_le $ face.refine h inj σ).op (f (σ.refine h inj)) :=
begin
  rw C.refine_apply,
  rw dif_pos,
end

lemma 𝓕_map_congr' {U V : opens X} (i1 i2 : U ⟶ V) (x y : 𝓕.1.obj (op V)) (h2 : x = y) :
  𝓕.1.map i1.op x = 𝓕.1.map i2.op y :=
have h : i1 = i2 := by ext,
by subst h; subst h2


lemma 𝓕_map_congr'' {n : ℕ} (A B : X.oc) (r : B ⟶ A) (σ : simplex B n) (σ1 σ2 : simplex A n.pred) (h : σ1 = σ2) (f : C 𝓕 A n.pred)
  (i1 : σ.face ⟶ σ1.face) (i2 : σ.face ⟶ σ2.face) :
  𝓕.1.map i1.op (f σ1) = 𝓕.1.map i2.op (f σ2) :=
begin
  subst h,
  congr,
end

lemma 𝓕_map_congr''' {n : ℕ} {A : X.oc} (f : C 𝓕 A n) 
  (σ1 σ2 : simplex A n) (h0 : σ1 = σ2)
  {U : opens X} (i1 : U ⟶ σ1.face) (i2 : U ⟶ σ2.face)  :
  𝓕.1.map i1.op (f σ1) = 𝓕.1.map i2.op (f σ2) := 
by { subst h0, apply 𝓕_map_congr', refl, }

example {A B : oc X} (h : A ⟶ B) :
  C.refine 𝓕 0 h ≫ @d_pos X 𝓕 A _ (nat.zero_lt_succ 0) = 
  @d_pos X 𝓕 B _ (nat.zero_lt_succ 0) ≫ C.refine 𝓕 1 h :=
begin
  haveI : decidable (function.injective h.func) := classical.dec _,
  ext f σ,
  simp only [comp_apply],
  simp only [C.refine_apply],
  split_ifs with inj,
  { rw d_pos_01,
    rw d_pos_01,
    change _ - _ = _,
    change _ = 𝓕.1.map _ (_ - _),
    rw map_sub,
    rw C.refine_apply_if_pos,
    swap, assumption,
    rw C.refine_apply_if_pos,
    swap, assumption,
    rw ← comp_apply,
    rw ← comp_apply,
    rw ← comp_apply,
    rw ← comp_apply,
    rw ← 𝓕.1.map_comp,
    rw ← 𝓕.1.map_comp,
    rw ← 𝓕.1.map_comp,
    rw ← 𝓕.1.map_comp,
    rw ← op_comp,
    rw ← op_comp,
    rw ← op_comp,
    rw ← op_comp,

    sorry,
     },
  { have : (C.refine 𝓕 0 h) f = 0,
    { ext1 σ,
      simp only [C.refine_apply],
      rw dif_neg,
      refl,
      assumption },
    rw this,
    simp only [map_zero, Cech.zero_apply], },
end

lemma C_refine_d_pos_commute (n : ℕ) {A B : oc X} (h : A ⟶ B) :
  C.refine 𝓕 n h ≫ @d_pos X 𝓕 A _ (nat.zero_lt_succ n) = 
  @d_pos X 𝓕 B _ (nat.zero_lt_succ n) ≫ C.refine 𝓕 n.succ h :=
begin
  haveI : decidable (function.injective h.func) := classical.dec _,
  ext f σ,
  simp only [comp_apply],
  simp only [C.refine_apply],
  split_ifs with inj,
  { rw d_pos.def,
    rw d_pos.def,
    rw add_monoid_hom.map_sum,
    apply finset.sum_congr rfl,
    rintros ⟨j, hj⟩ _,
    dsimp only,
    by_cases is_even : even j,
    { rw if_pos is_even,
      rw id,
      rw if_pos is_even,
      rw id,
      rw C.refine_apply_if_pos,
      swap,
      exact inj,
      change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
      rw ← 𝓕.1.map_comp,
      rw ← op_comp,
      rw ← 𝓕.1.map_comp,
      rw ← op_comp,
      apply 𝓕_map_congr'',
      exact h,
      sorry
     },
    { rw if_neg is_even,
      rw if_neg is_even,
      rw map_neg,
      congr' 1,
      rw C.refine_apply_if_pos,
      swap,
      exact inj,
      change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
      rw ← 𝓕.1.map_comp,
      rw ← op_comp,
      rw ← 𝓕.1.map_comp,
      rw ← op_comp,
      apply 𝓕_map_congr'',
      exact h,
      sorry } },
  { have : (C.refine 𝓕 n h) f = 0,
    { ext1 σ,
      simp only [C.refine_apply],
      rw dif_neg,
      refl,
      assumption },
    rw this,
    simp only [map_zero, Cech.zero_apply], },
end


-- lemma C.refine_self (n : ℕ) (A : X.oc) :
--   C.refine 𝓕 n (𝟙 A) = 𝟙 (C 𝓕 A n) := 
-- begin
--   ext f σ,
--   change 𝓕.1.map _ _ = f σ,
--   have eq1 : f σ = 𝓕.1.map (𝟙 _).op (f σ),
--   { rw [category_theory.op_id, 𝓕.1.map_id], refl, },
--   rw [eq1],
--   apply 𝓕_map_congr''' 𝓕 f,
--   rw σ.refine_self,
-- end

-- lemma C.refine_comp (n : ℕ) {A B D : oc X} (r1 : A ⟶ B) (r2 : B ⟶ D) :
--   C.refine 𝓕 n r2 ≫ C.refine 𝓕 n r1 = C.refine 𝓕 n (r1 ≫ r2) := 
-- begin
--   ext1 f,
--   change C.refine 𝓕 n r1 (C.refine 𝓕 n r2 f) = _,
--   ext1 σ,
--   change 𝓕.1.map _ (𝓕.1.map _ _) = 𝓕.1.map _ (f _),
--   change (𝓕.1.map _ ≫ 𝓕.1.map _) _ = _,
--   rw [← category_theory.functor.map_comp, ← category_theory.op_comp],
--   apply 𝓕_map_congr''',
--   symmetry,
--   apply simplex.refine_comp,
-- end

-- def C.refine_functor (n : ℕ) : X.ocᵒᵖ ⥤ Ab :=
-- { obj := λ A, C 𝓕 A.unop n,
--   map := λ A B f, C.refine 𝓕 n f.unop,
--   map_id' := λ A, C.refine_self 𝓕 n A.unop,
--   map_comp' := λ A B D f g, by rw [unop_comp, C.refine_comp] }

namespace d

def from_to (i j : ℕ) : C 𝓕 𝔘.unop i ⟶ C 𝓕 𝔘.unop j :=
dite (i + 1 = j) (λ h, begin subst h, exact d_pos (nat.zero_lt_succ _) end) (λ h, 0)

lemma to_succ (i : ℕ) :
  from_to 𝓕 𝔘 i i.succ = d_pos (nat.zero_lt_succ _) :=
dif_pos rfl

lemma not_succ (i j : ℕ) (h : i + 1 ≠ j) :
  from_to 𝓕 𝔘 i j = 0 :=
dif_neg h

end d

@[simps]
def cech_chain : cochain_complex Ab ℕ :=
{ X := λ n, (AddCommGroup.ulift_functor.{u u+1}).obj $ C 𝓕 𝔘.unop n,
  d := λ i j, (AddCommGroup.ulift_functor.{u u+1}).map $ d.from_to 𝓕 𝔘 i j,
  shape' := λ i j r, begin
    simp only [complex_shape.up_rel] at r,
    unfold d.from_to,
    split_ifs,
    { tauto, },
    refl,
  end,
  d_comp_d' := λ i j k h1 h2, begin
    simp only [complex_shape.up_rel] at h1 h2,
    subst' h1,
    subst' h2,
    rw [d.to_succ, d.to_succ],
    ext1 f,
    rw [← category_theory.functor.map_comp, add_monoid_hom.zero_apply],
    ext1,
    simp only [functor.map_comp, comp_apply, AddCommGroup.ulift.zero_down],
    rw AddCommGroup.ulift_functor_map_down,
    rw AddCommGroup.ulift_functor_map_down,
    rw ← comp_apply,
    erw dd_pos.eq0 (nat.zero_lt_succ _),
    refl,
  end }

lemma cech_chain_d_down (i : ℕ) (f) :
  ((cech_chain 𝓕 𝔘).d i (i + 1) f).down =
  (@d_pos X 𝓕 𝔘.unop (i + 1) (nat.zero_lt_succ _)) f.down := 
begin
  rw cech_chain_d,
  simp only [AddCommGroup.ulift_functor_map_down],
  unfold d.from_to,
  rw dif_pos,
  refl,
end

-- def cech_chain.functor : X.ocᵒᵖ ⥤ cochain_complex Ab ℕ :=
-- { obj := λ 𝔘, cech_chain 𝓕 𝔘,
--   map := λ A B r, 
--   { f := λ i, (C.refine_functor 𝓕 i).map r,
--     comm' := λ i j h, begin
--       simp only [complex_shape.up_rel] at h,
--       subst h,
--       ext f σ,
--       change (d.from_to _ _ i (i + 1)) (C.refine 𝓕 _ r.unop f) σ = (C.refine 𝓕 _ r.unop) (d.from_to _ _ _ _ _) _,
--       rw [d.to_succ, d_pos.def, d.to_succ],
--       change _ = 𝓕.1.map _ _,
--       rw [d_pos.def, add_monoid_hom.map_sum],
--       apply finset.sum_congr rfl (λ j hj, _),
--       by_cases e : even j.1,
--       { rw [if_pos e, id, if_pos e, id],
--         change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map ((σ.refine r.unop).der _ ⟨j.val, _⟩).op ≫ _) _,
--         rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
--         apply 𝓕_map_congr'',
--         exact r.unop,
--         symmetry,
--         apply simplex.refine_ignore, },
--       { rw [if_neg e, if_neg e, map_neg],
--         congr' 1,
--         change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map ((σ.refine r.unop).der _ ⟨j.val, _⟩).op ≫ _) _,
--         rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
--         apply 𝓕_map_congr'',
--         exact r.unop,
--         symmetry,
--         apply simplex.refine_ignore, },
--     end },
--   map_id' := λ A, begin
--     ext i f σ,
--     simp only [unop_id, homological_complex.id_f, id_apply],
--     change 𝓕.1.map _ _ = _,
--     have eq1 : f σ = 𝓕.1.map (𝟙 _) (f σ),
--     { rw category_theory.functor.map_id,
--       refl, },
--     conv_rhs { rw eq1 },
--     symmetry,
--     have := 𝓕_map_congr''' 𝓕 f σ (σ.refine (𝟙 _)) (σ.refine_self).symm,
--     convert this _ _,
--     exact 𝟙 _,
--   end,
--   map_comp' := λ A B D r1 r2, begin
--     ext i f σ,
--     simp only [unop_comp, homological_complex.comp_f, comp_apply],
--     rw category_theory.functor.map_comp,
--     refl,
--   end }

-- include 𝓕

-- def Cech_Ab (n : ℕ) : X.ocᵒᵖ ⥤ Ab.{u+1} := 
-- C.refine_functor 𝓕 n ⋙ AddCommGroup.ulift_functor.{u u+1}

-- why do we need to lift up
/-
```
include 𝓕

example (n : ℕ) : true := 
begin
  have := @AddCommGroup.colimits.colimit X.ocᵒᵖ _ (C.refine_functor 𝓕 n),
  -- this doesn't work, because we need a functor ` (X.oc)ᵒᵖ ⥤ AddCommGroup : Type (u+2)`,
  -- but we only have `C.refine_functor 𝓕 n : (X.oc)ᵒᵖ ⥤ Ab : Type u+1`
end
```
-/

-- lemma Cech_Ab_obj (n : ℕ) (A : X.ocᵒᵖ) :
--   (Cech_Ab 𝓕 n).obj A = AddCommGroup.ulift.{u u+1} (C 𝓕 A.unop n) := rfl

-- lemma Cech_Ab_map (n : ℕ) {A B : X.ocᵒᵖ} (r : A ⟶ B) :
--   (Cech_Ab 𝓕 n).map r = (AddCommGroup.ulift_functor.{u u+1}).map (C.refine 𝓕 n r.unop) := rfl

-- def Cech_d (A : X.ocᵒᵖ) (i j : ℕ) : (Cech_Ab 𝓕 i).obj A ⟶ (Cech_Ab 𝓕 j).obj A :=
-- dite (i + 1 = j) (λ h, (AddCommGroup.ulift_functor.{u u+1}).map (d_pos (nat.zero_lt_succ _)) ≫ eq_to_hom begin subst h, refl end) (λ h, 0)

-- lemma Cech_d_down_apply (A : X.ocᵒᵖ) (i j : ℕ) (f : (Cech_Ab 𝓕 i).obj A) :
--   (Cech_d 𝓕 A i j f).down = 
--   dite (i + 1 = j) (λ h, begin subst h, exact (d_pos (nat.zero_lt_succ _) f.down) end) (λ h, 0) := 
-- begin
--   induction f,
--   dsimp only [Cech_d],
--   split_ifs,
--   { induction h, refl, },
--   { refl, },
-- end

-- lemma Cech_d_succ_down_apply (A : X.ocᵒᵖ) (i : ℕ) (f : (Cech_Ab 𝓕 i).obj A) :
--   (Cech_d 𝓕 A i (i+1) f).down = 
--   (d_pos (nat.zero_lt_succ _) f.down) := 
-- begin
--   induction f,
--   dsimp only [Cech_d],
--   split_ifs;
--   refl,
-- end

-- lemma Cech_d_not_succ_down_apply (A : X.ocᵒᵖ) {i j : ℕ} (h : i + 1 ≠ j) (f : (Cech_Ab 𝓕 i).obj A) :
--   (Cech_d 𝓕 A i j f).down = 0 := 
-- begin
--   induction f,
--   dsimp only [Cech_d],
--   rw dif_neg h,
--   refl,
-- end

-- -- def from_to (i j : ℕ) : C 𝓕 𝔘.unop i ⟶ C 𝓕 𝔘.unop j :=
-- -- dite (i + 1 = j) (λ h, begin subst h, exact d_pos (nat.zero_lt_succ _) end) (λ h, 0)

-- lemma Cech_d_to_succ (A : X.ocᵒᵖ) (i : ℕ) :
--   Cech_d 𝓕 A i i.succ = (AddCommGroup.ulift_functor.{u u+1}).map (d_pos (nat.zero_lt_succ _)) :=
-- dif_pos rfl

-- lemma Cech_d_not_succ (A : X.ocᵒᵖ) {i j : ℕ} (h : i + 1 ≠ j) :
--   Cech_d 𝓕 A i j = 0 :=
-- dif_neg h

-- -- lemma to_succ (i : ℕ) :
-- --   from_to 𝓕 𝔘 i i.succ = d_pos (nat.zero_lt_succ _) :=
-- -- dif_pos rfl

-- -- lemma not_succ (i j : ℕ) (h : i + 1 ≠ j) :
-- --   from_to 𝓕 𝔘 i j = 0 :=
-- -- dif_neg h

-- def Cech_complex_obj (A : X.ocᵒᵖ) : cochain_complex Ab.{u+1} ℕ :=
-- { X := λ n, (Cech_Ab 𝓕 n).obj A,
--   d := λ i j, Cech_d 𝓕 A i j,
--   shape' := λ i j r, dif_neg r,
--   d_comp_d' := λ i j k h1 h2, begin
--     simp only [complex_shape.up_rel] at h1 h2,
--     subst' h1,
--     subst' h2,
--     rw [Cech_d_to_succ, Cech_d_to_succ],
--     ext1 f,
--     rw [← category_theory.functor.map_comp, dd_pos.eq0 (nat.zero_lt_succ _)],
--     refl,
--   end }

-- lemma Cech_complex_obj_d (A : X.ocᵒᵖ) :
--   (Cech_complex_obj 𝓕 A).d = Cech_d 𝓕 A := rfl

-- def Cech_complex : X.ocᵒᵖ ⥤ cochain_complex Ab.{u+1} ℕ :=
-- { obj := λ A, Cech_complex_obj 𝓕 A,
--   map := λ A B r, 
--   { f := λ i, (Cech_Ab 𝓕 i).map r,
--     comm' := λ i j h, begin
--       simp only [complex_shape.up_rel] at h,
--       subst h,
--       ext f σ,
--       rw [category_theory.comp_apply, category_theory.comp_apply, Cech_Ab_map, Cech_complex_obj_d, Cech_d_succ_down_apply],
--       change _ = 𝓕.1.map _ _,
--       rw [d_pos.def, Cech_complex_obj_d, Cech_d_succ_down_apply, d_pos.def, add_monoid_hom.map_sum],
--       apply finset.sum_congr rfl (λ j hj, _),
--       by_cases e : even j.1,
--       { rw [if_pos e, id, if_pos e, id],
--         change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map ((σ.refine r.unop).der _ ⟨j.val, _⟩).op ≫ _) _,
--         rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
--         apply 𝓕_map_congr'',
--         exact r.unop,
--         symmetry,
--         apply simplex.refine_ignore, },
--       { rw [if_neg e, if_neg e, map_neg],
--         congr' 1,
--         change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map ((σ.refine r.unop).der _ ⟨j.val, _⟩).op ≫ _) _,
--         rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
--         apply 𝓕_map_congr'',
--         exact r.unop,
--         symmetry,
--         apply simplex.refine_ignore, },
--     end },
--   map_id' := λ A, begin
--     ext i f σ,
--     simp only [unop_id, homological_complex.id_f, id_apply, Cech_Ab_map, AddCommGroup.ulift_functor_map_down],
--     rw C.refine_self,
--     refl,
--   end,
--   map_comp' := λ A B D r1 r2, begin
--     ext i f σ,
--     simp only [unop_comp, homological_complex.comp_f, comp_apply, Cech_Ab_map, AddCommGroup.ulift_functor_map_down],
--     change _ = (C.refine 𝓕 i r1.unop ≫ C.refine 𝓕 i r2.unop) f.down σ,
--     rw C.refine_comp,
--   end }

noncomputable def ex1 :
  homological_complex.homology (cech_chain 𝓕 𝔘) 0 ≅
  kernel ((cech_chain 𝓕 𝔘).d 0 1) :=
begin
  refine homology_iso_cokernel_image_to_kernel' _ _ _ ≪≫ _,
  change cokernel (kernel.lift _ _ _) ≅ _,

  simp only [image.ι_zero', homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero, eq_self_iff_true, kernel.lift_zero, cech_chain_d], -- , Cech_complex_obj_d, Cech_d_to_succ
  refine cokernel_zero_iso_target ≪≫ _,
  refine AddCommGroup.kernel_iso_ker _ ≪≫ _,
  refine _ ≪≫ (AddCommGroup.kernel_iso_ker (AddCommGroup.ulift_functor.map (d_pos _))).symm,
  refine { hom := _, inv := _, hom_inv_id' := _, inv_hom_id' := _ },
  { refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros x,
      refine ⟨x.1, _⟩,
      rw add_monoid_hom.mem_ker,
      have := x.2,
      rw add_monoid_hom.mem_ker at this,
      change homological_complex.d_from (cech_chain 𝓕 𝔘) 0 x.1 = _ at this,
      have eq1 := homological_complex.d_from_eq (cech_chain 𝓕 𝔘) (show 1 = 0 + 1, from rfl),
      rw cech_chain_d at eq1,
      rw d.to_succ at eq1,
      generalize_proofs h1 h2 at eq1,
      have eq2 : homological_complex.d_from (cech_chain 𝓕 𝔘) 0 x.1 = (AddCommGroup.ulift_functor.map (d_pos h1) ≫ (homological_complex.X_next_iso (cech_chain 𝓕 𝔘) h2).inv) x.1,
      { congr, rw eq1, },
      rw comp_apply at eq2,
      rw this at eq2,
      apply_fun (homological_complex.X_next_iso (cech_chain 𝓕 𝔘) h2).hom at eq2,
      simp only [map_zero, coe_inv_hom_id] at eq2,
      rw <- eq2 },
    { rw subtype.ext_iff_val,
      refl, },
    { intros x1 x2, 
      rw subtype.ext_iff_val,
      refl, } },
  { refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros x,
      refine ⟨x.1, _⟩,
      have := x.2,
      rw add_monoid_hom.mem_ker at this ⊢,
      have eq1 := homological_complex.d_from_eq (cech_chain 𝓕 𝔘) (show 1 = 0 + 1, from rfl),
      erw eq1,
      rw comp_apply,
      generalize_proofs h1 h2,
      apply_fun (homological_complex.X_next_iso (cech_chain 𝓕 𝔘) h1).hom,
      simp only [coe_inv_hom_id, map_zero],
      convert this,
      apply function.bijective.injective,
      rw function.bijective_iff_has_inverse,
      use (homological_complex.X_next_iso (cech_chain 𝓕 𝔘) h1).inv,
      refine ⟨_, _⟩,
      intros x,
      rw coe_hom_inv_id,
      intros x,
      rw coe_inv_hom_id, },
    { rw subtype.ext_iff_val,
      refl },
    { intros x y,
      rw subtype.ext_iff_val,
      refl, } },
  { ext1 σ,
    simp only [comp_apply, subtype.val_eq_coe, add_subgroup.coe_mk, add_monoid_hom.coe_mk, set_like.eta, id_apply] },
  { ext1 σ,
    simp only [comp_apply, subtype.val_eq_coe, add_subgroup.coe_mk, add_monoid_hom.coe_mk, set_like.eta, id_apply] },
end

noncomputable def ex2 : 
  kernel ((cech_chain 𝓕 𝔘).d 0 1) ≅ 
  kernel ((AddCommGroup.ulift_functor.{u u+1}).map (@d_pos X 𝓕 (unop 𝔘) _ (nat.zero_lt_succ 0))) :=
begin
  change kernel ((cech_chain 𝓕 𝔘).d 0 1) ≅ _,
  refine AddCommGroup.kernel_iso_ker _ ≪≫ _,
  refine _ ≪≫ (AddCommGroup.kernel_iso_ker (AddCommGroup.ulift_functor.map (d_pos _))).symm,
  refine { hom := 𝟙 _, inv := 𝟙 _ },
end

noncomputable def ex3 :
  kernel ((AddCommGroup.ulift_functor.{u u+1}).map (@d_pos X 𝓕 (unop 𝔘) _ (nat.zero_lt_succ 0))) ≅
  (AddCommGroup.ulift_functor.{u u+1}).obj (kernel (@d_pos X 𝓕 (unop 𝔘) _ (nat.zero_lt_succ 0))) :=
begin
  apply AddCommGroup.ulift_kernel_iso_kernel_ulift,
end

lemma ex41.forward.aux1 {i j : 𝔘.unop.ι} {f : C 𝓕 𝔘.unop 0} (h : d_pos (nat.zero_lt_succ 0) f = 0) :
  𝓕.1.map (((unop 𝔘).cover i).inf_le_left ((unop 𝔘).cover j) ≫ eq_to_hom begin
    unfold simplex.face,
    simp
  end).op (f {to_finset := {i}, card_eq := rfl}) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_left,
    unfold simplex.face,
    simp
  end).op (f {to_finset := {i}, card_eq := rfl}) :=
begin
  congr,
end

lemma ex41.forward.aux1' {i j : 𝔘.unop.ι} {f : C 𝓕 𝔘.unop 0} (h : d_pos (nat.zero_lt_succ 0) f = 0) :
  𝓕.1.map (((unop 𝔘).cover i).inf_le_right ((unop 𝔘).cover j) ≫ eq_to_hom begin
    unfold simplex.face,
    simp
  end).op (f {to_finset := {j}, card_eq := rfl}) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_right,
    unfold simplex.face,
    simp
  end).op (f {to_finset := {j}, card_eq := rfl}) :=
begin
  congr,
end

lemma ex41.forward.aux2 {i j : 𝔘.unop.ι} {f : C 𝓕 𝔘.unop 0} (h : d_pos (nat.zero_lt_succ 0) f = 0) :
  𝓕.1.map (((unop 𝔘).cover i).inf_le_right ((unop 𝔘).cover j) ≫ eq_to_hom begin
    unfold simplex.face,
    simp
  end).op (f {to_finset := {j}, card_eq := rfl}) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_right,
    unfold simplex.face,
    simp
  end).op (f {to_finset := {j}, card_eq := rfl}) :=
begin
  congr,
end

lemma ex41.forward.aux2' {i j : 𝔘.unop.ι} {f : C 𝓕 𝔘.unop 0} (h : d_pos (nat.zero_lt_succ 0) f = 0) :
  𝓕.1.map (((unop 𝔘).cover i).inf_le_left ((unop 𝔘).cover j) ≫ eq_to_hom begin
    unfold simplex.face,
    simp
  end).op (f {to_finset := {i}, card_eq := rfl}) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_left,
    unfold simplex.face,
    simp
  end).op (f {to_finset := {i}, card_eq := rfl}) :=
begin
  congr,
end

lemma ex41.forward.aux3 {i j : 𝔘.unop.ι} (ineq : i < j) (f : C 𝓕 𝔘.unop 0) :
  𝓕.1.map (simplex.der (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ ⟨0, nat.zero_lt_succ 1⟩).op 
  (f (simplex.ignore (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ 0)) =
  𝓕.1.map 
  ((hom_of_le (λ p hp, begin
    rw [opens.mem_coe] at hp ⊢,
    change _ ∈ (infi _) at hp,
    have := (infi_le (λ (i_1 : (unop 𝔘).ι), ⨅ (H : i_1 ∈ ({to_finset := {i, j}, card_eq := begin
      rw finset.card_insert_of_not_mem,
      refl,
      rw [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end} : simplex _ 1).to_finset), (unop 𝔘).cover i_1)),
    specialize this j,
    dsimp only at this,
    simp only [le_infi_iff] at this,
    specialize this _,
    { rw finset.mem_insert,
      right,
      exact finset.mem_singleton_self _ },
    specialize this hp,
    convert this,
    unfold simplex.face,
    { simp },
  end) : 
  ({to_finset := {i, j}, card_eq := begin
     rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end} : simplex _ 1).face ⟶
  ({to_finset := {j}, card_eq := begin
    rw finset.card_singleton,
  end} : simplex _ 0).face)).op 
  (f ⟨{j}, rfl⟩) 
  :=
begin
  generalize_proofs _ h1 h2 h3 h4 h5,
  apply 𝓕_map_congr''',
  unfold simplex.ignore,
  dsimp only,
  rw simplex.ext_iff,
  dsimp only,
  ext1 k,
  split,
  { intro hk,
    rw finset.mem_erase_nth at hk,
    rcases hk with ⟨hk1, hk2⟩,
    rw [finset.mem_insert, finset.mem_singleton] at hk2,
    rcases hk2 with rfl|rfl,
    { rw finset.mem_singleton,
      contrapose! hk1,
      rw finset.order_emb_of_fin_zero,
      rw finset.min'_insert,
      rw finset.min'_singleton,
      symmetry,
      rw min_eq_right_iff,
      refine le_of_lt ineq, },
    { exact finset.mem_singleton_self _ }, },
  { intro hk,
    rw finset.mem_singleton at hk,
    rw hk,
    rw finset.mem_erase_nth,
    split,
    { intro rid,
      rw finset.order_emb_of_fin_zero at rid,
      rw finset.min'_insert at rid,
      rw finset.min'_singleton at rid,
      have ineq2 := min_le_right j i,
      have ineq3 := min_le_left j i,
      rw ← rid at ineq2,
      rw lt_iff_not_ge at ineq,
      apply ineq,
      exact ineq2, },
    { rw finset.mem_insert,
      right,
      exact finset.mem_singleton_self _, } },
end

lemma ex41.forward.aux3' {i j : 𝔘.unop.ι} (ineq : j < i) (f : C 𝓕 𝔘.unop 0) :
  𝓕.1.map (simplex.der (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ ⟨0, nat.zero_lt_succ 1⟩).op 
  (f (simplex.ignore (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ 0)) =
  𝓕.1.map 
  ((hom_of_le (λ p hp, begin
    rw [opens.mem_coe] at hp ⊢,
    change _ ∈ (infi _) at hp,
    have := (infi_le (λ (i_1 : (unop 𝔘).ι), ⨅ (H : i_1 ∈ ({to_finset := {i, j}, card_eq := begin
      rw finset.card_insert_of_not_mem,
      refl,
      rw [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end} : simplex _ 1).to_finset), (unop 𝔘).cover i_1)),
    specialize this i,
    dsimp only at this,
    simp only [le_infi_iff] at this,
    specialize this _,
    { rw finset.mem_insert,
      left,
      refl, },
    specialize this hp,
    convert this,
    unfold simplex.face,
    { simp },
  end) : 
  ({to_finset := {i, j}, card_eq := begin
     rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end} : simplex _ 1).face ⟶
  ({to_finset := {i}, card_eq := begin
    rw finset.card_singleton,
  end} : simplex _ 0).face)).op 
  (f ⟨{i}, rfl⟩) 
  :=
begin
  generalize_proofs _ h1 h2 h3 h4 h5,
  apply 𝓕_map_congr''',
  unfold simplex.ignore,
  dsimp only,
  rw simplex.ext_iff,
  dsimp only,
  ext1 k,
  split,
  { intro hk,
    rw finset.mem_erase_nth at hk,
    rcases hk with ⟨hk1, hk2⟩,
    rw [finset.mem_insert, finset.mem_singleton] at hk2,
    rcases hk2 with rfl|rfl,
    { rw finset.mem_singleton, },
    { contrapose! hk1,
      rw finset.order_emb_of_fin_zero,
      rw finset.min'_insert,
      rw finset.min'_singleton,
      symmetry,
      rw min_eq_left_iff,
      refine le_of_lt ineq }, },
  { intro hk,
    rw finset.mem_singleton at hk,
    rw hk,
    rw finset.mem_erase_nth,
    split,
    { intro rid,
      rw finset.order_emb_of_fin_zero at rid,
      rw finset.min'_insert at rid,
      rw finset.min'_singleton at rid,
      have ineq2 := min_le_right j i,
      have ineq3 := min_le_left j i,
      rw ← rid at ineq3,
      rw lt_iff_not_ge at ineq,
      apply ineq,
      exact ineq3, },
    { rw finset.mem_insert,
      left,
      refl } },
end

lemma ex41.forward.aux4 {i j : 𝔘.unop.ι} (ineq : i < j) (f : C 𝓕 𝔘.unop 0) :
  𝓕.1.map (simplex.der (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ ⟨1, lt_add_one 1⟩).op 
  (f (simplex.ignore (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ 1)) =
  𝓕.1.map 
  ((hom_of_le (λ p hp, begin
    rw [opens.mem_coe] at hp ⊢,
    change _ ∈ (infi _) at hp,
    have := (infi_le (λ (i_1 : (unop 𝔘).ι), ⨅ (H : i_1 ∈ ({to_finset := {i, j}, card_eq := begin
      rw finset.card_insert_of_not_mem,
      refl,
      rw [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end} : simplex _ 1).to_finset), (unop 𝔘).cover i_1)),
    specialize this i,
    dsimp only at this,
    simp only [le_infi_iff] at this,
    specialize this _,
    { rw finset.mem_insert,
      left,
      refl },
    specialize this hp,
    convert this,
    unfold simplex.face,
    { simp },
  end) : 
  ({to_finset := {i, j}, card_eq := begin
     rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end} : simplex _ 1).face ⟶
  ({to_finset := {i}, card_eq := begin
    rw finset.card_singleton,
  end} : simplex _ 0).face)).op 
  (f ⟨{i}, rfl⟩) 
  :=
begin
  generalize_proofs _ h1 h2 h3 h4 h5,
  apply 𝓕_map_congr''',
  unfold simplex.ignore,
  dsimp only,
  rw simplex.ext_iff,
  dsimp only,
  ext1 k,
  split,
  { intro hk,
    rw finset.mem_erase_nth at hk,
    rcases hk with ⟨hk1, hk2⟩,
    rw [finset.mem_insert, finset.mem_singleton] at hk2,
    rcases hk2 with rfl|rfl,
    { rw finset.mem_singleton },
    { rw finset.mem_singleton,
      contrapose! hk1,
      -- have := finset.order_emb_of_fin_last,
      rw finset.order_emb_of_fin_last ({to_finset := {i, k}, card_eq := begin
        rw [finset.card_insert_of_not_mem],
        refl,
        rw [finset.mem_singleton],
        intro r,
        rw r at ineq,
        exact lt_irrefl _ ineq,
      end} : simplex _ 1).card_eq,
      rw finset.max'_insert,
      rw finset.max'_singleton,
      symmetry,
      rw max_eq_left_iff,
      refine le_of_lt ineq,
      exact nat.zero_lt_succ _, }, },
  { intro hk,
    rw finset.mem_singleton at hk,
    rw hk,
    rw finset.mem_erase_nth,
    split,
    { intro rid,
      subst hk,
      rw finset.order_emb_of_fin_last ({to_finset := {k, j}, card_eq := begin
        rw [finset.card_insert_of_not_mem],
        refl,
        rw [finset.mem_singleton],
        intro r,
        rw r at ineq,
        exact lt_irrefl _ ineq,
      end} : simplex _ 1).card_eq at rid,
      dsimp only at rid,
      generalize_proofs ne at rid,
      have := finset.le_max' {k, j} j _,
      erw ← rid at this,
      rw lt_iff_not_ge at ineq,
      apply ineq,
      exact this,
      rw finset.mem_insert,
      right,
      rw finset.mem_singleton,
      exact nat.zero_lt_succ _, },
    { rw finset.mem_insert,
      left,
      refl } },
end

lemma ex41.forward.aux4' {i j : 𝔘.unop.ι} (ineq : j < i) (f : C 𝓕 𝔘.unop 0) :
  𝓕.1.map (simplex.der (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ ⟨1, lt_add_one 1⟩).op 
  (f (simplex.ignore (nat.zero_lt_succ 0) ⟨{i, j}, begin
    rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end⟩ 1)) =
  𝓕.1.map 
  ((hom_of_le (λ p hp, begin
    rw [opens.mem_coe] at hp ⊢,
    change _ ∈ (infi _) at hp,
    have := (infi_le (λ (i_1 : (unop 𝔘).ι), ⨅ (H : i_1 ∈ ({to_finset := {i, j}, card_eq := begin
      rw finset.card_insert_of_not_mem,
      refl,
      rw [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end} : simplex _ 1).to_finset), (unop 𝔘).cover i_1)),
    specialize this j,
    dsimp only at this,
    simp only [le_infi_iff] at this,
    specialize this _,
    { rw finset.mem_insert,
      right,
      rw finset.mem_singleton, },
    specialize this hp,
    convert this,
    unfold simplex.face,
    { simp },
  end) : 
  ({to_finset := {i, j}, card_eq := begin
     rw [finset.card_insert_of_not_mem],
    refl,
    rw [finset.mem_singleton],
    intro r,
    rw r at ineq,
    exact lt_irrefl _ ineq,
  end} : simplex _ 1).face ⟶
  ({to_finset := {j}, card_eq := begin
    rw finset.card_singleton,
  end} : simplex _ 0).face)).op 
  (f ⟨{j}, rfl⟩) 
  :=
begin
  generalize_proofs _ h1 h2 h3 h4 h5,
  apply 𝓕_map_congr''',
  unfold simplex.ignore,
  dsimp only,
  rw simplex.ext_iff,
  dsimp only,
  ext1 k,
  split,
  { intro hk,
    rw finset.mem_erase_nth at hk,
    rcases hk with ⟨hk1, hk2⟩,
    rw [finset.mem_insert, finset.mem_singleton] at hk2,
    rcases hk2 with rfl|rfl,
    { rw finset.mem_singleton,
      contrapose! hk1,
      -- have := finset.order_emb_of_fin_last,
      rw finset.order_emb_of_fin_last ({to_finset := {k, j}, card_eq := begin
        rw [finset.card_insert_of_not_mem],
        refl,
        rw [finset.mem_singleton],
        intro r,
        rw r at ineq,
        exact lt_irrefl _ ineq,
      end} : simplex _ 1).card_eq,
      rw finset.max'_insert,
      rw finset.max'_singleton,
      symmetry,
      rw max_eq_right_iff,
      refine le_of_lt ineq,
      exact nat.zero_lt_succ _, },
    { rw finset.mem_singleton }, },
  { intro hk,
    rw finset.mem_singleton at hk,
    rw hk,
    rw finset.mem_erase_nth,
    split,
    { intro rid,
      subst hk,
      rw finset.order_emb_of_fin_last ({to_finset := {i, k}, card_eq := begin
        rw [finset.card_insert_of_not_mem],
        refl,
        rw [finset.mem_singleton],
        intro r,
        rw r at ineq,
        exact lt_irrefl _ ineq,
      end} : simplex _ 1).card_eq at rid,
      dsimp only at rid,
      generalize_proofs ne at rid,
      have := finset.le_max' {i, k} i _,
      erw ← rid at this,
      rw lt_iff_not_ge at ineq,
      apply ineq,
      exact this,
      rw finset.mem_insert,
      left,
      refl,
      exact nat.zero_lt_succ _, },
    { rw finset.mem_insert,
      right,
      rw finset.mem_singleton, } },
end

lemma ex41.forward.aux5 (f : C 𝓕 𝔘.unop 0) 
  (o1 o2 o3 o4 : opens X)
  (oop2 : 𝓕.val.obj (op o2))
  (oop3 : 𝓕.val.obj (op o3))
-- o1 : face ij
-- o2 : face i
-- o3 : face j
-- o4 : cover i ⊓ cover j
  (h12 : o1 ≤ o2)
  (h13 : o1 ≤ o3)
  (h42 : o4 ≤ o2)
  (h43 : o4 ≤ o3)
  (h14 : o4 ≤ o1)
  (eq1 : 𝓕.1.map (hom_of_le h12).op oop2 = 𝓕.1.map (hom_of_le h13).op oop3) : 
  𝓕.1.map (hom_of_le h42).op oop2 = 𝓕.1.map (hom_of_le h43).op oop3 :=
begin
  have : hom_of_le h42 = hom_of_le h14 ≫ hom_of_le h12,
  { ext, },
  rw this,
  have : hom_of_le h43 = hom_of_le h14 ≫ hom_of_le h13,
  { ext },
  rw this,
  rw [op_comp, category_theory.functor.map_comp, op_comp, category_theory.functor.map_comp],
  rw [comp_apply, comp_apply, eq1],
end

lemma ker_compatible (f : add_monoid_hom.ker (@d_pos X 𝓕 𝔘.unop 1 (nat.zero_lt_succ 0))) : presheaf.is_compatible 𝓕.1 𝔘.unop.cover 
  (λ i, begin
    refine 𝓕.1.map (eq_to_hom _).op (f.1 ⟨{i}, rfl⟩),
    unfold simplex.face,
    simp,
  end) :=
begin
  intros i j,
  have := f.2,
  rw add_monoid_hom.mem_ker at this,
      
  rcases @trichotomous 𝔘.unop.ι (<) _ i j with ineq|ineq|ineq,
  { dsimp only,
    change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
    rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← op_comp, ← op_comp],
    rw ex41.forward.aux1 _ _ this,
    rw ex41.forward.aux2 _ _ this,

    have eq1 : d_pos (nat.zero_lt_succ 0) f.1 ⟨{i, j}, begin
      rw finset.card_insert_of_not_mem,
      simp only [finset.card_singleton],
      simp only [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end⟩ = 0,
    { rw this, simp, },
    simp only [d_pos_01] at eq1,
    change _ - _ = _ at eq1,
    rw sub_eq_zero at eq1,
    dsimp only at eq1,
    rw ex41.forward.aux3 at eq1,
    have eq2 := eq.trans eq1 (ex41.forward.aux4 𝓕 𝔘 ineq f.1),
          
    refine ex41.forward.aux5 𝓕 𝔘 f.1 ({to_finset := {i, j}, card_eq := _} : simplex 𝔘.unop 1).face 
      ({to_finset := {i}, card_eq := _} : simplex _ 0).face
      ({to_finset := {j}, card_eq := _} : simplex _ 0).face
      ((unop 𝔘).cover i ⊓ (unop 𝔘).cover j)
      (f.val {to_finset := {i}, card_eq := _})
      (f.val {to_finset := {j}, card_eq := _})
      _ _ _ _ _ _,
    { rw finset.card_insert_of_not_mem,
      refl,
      rw finset.mem_singleton,
      intro r,
      subst r,
      apply lt_irrefl i ineq, },
    { unfold simplex.face,
      intros p hp,
      erw opens.finset_infi at hp ⊢,
      intros k hk,
      apply hp,
      dsimp only at hk ⊢,
      rw [finset.mem_insert, finset.mem_singleton],
      left,
      simpa using hk, },
    { unfold simplex.face,
      intros p hp,
      erw opens.finset_infi at hp ⊢,
      intros k hk,
      apply hp,
      dsimp only at hk ⊢,
      rw [finset.mem_insert, finset.mem_singleton],
      right,
      simpa using hk, },
    { intros p hp,
      unfold simplex.face,
      rw [opens.mem_coe] at hp ⊢,
      rw opens.finset_infi,
      intros h hk,
      dsimp only at hk,
      rw [finset.mem_insert, finset.mem_singleton] at hk,
      rw ← opens.inter_eq at hp,
      rcases hp with ⟨hp1, hp2⟩,
      rcases hk with rfl|rfl,
      { exact hp1, },
      { exact hp2, }, },
    { symmetry,
      exact eq2, }, },
  { subst ineq, refl, },
  { dsimp only,
    change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
    rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← op_comp, ← op_comp],
    rw ex41.forward.aux1' _ _ this,
    rw ex41.forward.aux2' _ _ this,

    have eq1 : d_pos (nat.zero_lt_succ 0) f.1 ⟨{i, j}, begin
      rw finset.card_insert_of_not_mem,
      simp only [finset.card_singleton],
      simp only [finset.mem_singleton],
      intro r,
      rw r at ineq,
      exact lt_irrefl _ ineq,
    end⟩ = 0,
    { rw this, simp, },
    simp only [d_pos_01] at eq1,
    change _ - _ = _ at eq1,
    rw sub_eq_zero at eq1,
    dsimp only at eq1,
    rw ex41.forward.aux3' at eq1,
    have eq2 := eq.trans eq1 (ex41.forward.aux4' 𝓕 𝔘 ineq f.1),

    refine ex41.forward.aux5 𝓕 𝔘 f.1 ({to_finset := {i, j}, card_eq := _} : simplex 𝔘.unop 1).face 
      ({to_finset := {i}, card_eq := _} : simplex _ 0).face
      ({to_finset := {j}, card_eq := _} : simplex _ 0).face
      ((unop 𝔘).cover i ⊓ (unop 𝔘).cover j)
      (f.val {to_finset := {i}, card_eq := _})
      (f.val {to_finset := {j}, card_eq := _})
      _ _ _ _ _ _,
    { rw finset.card_insert_of_not_mem,
      refl,
      rw finset.mem_singleton,
      intro r,
      subst r,
      apply lt_irrefl i ineq, },
    { unfold simplex.face,
      intros p hp,
      erw opens.finset_infi at hp ⊢,
      intros k hk,
      apply hp,
      dsimp only at hk ⊢,
      rw [finset.mem_insert, finset.mem_singleton],
      left,
      simpa using hk, },
    { unfold simplex.face,
      intros p hp,
      erw opens.finset_infi at hp ⊢,
      intros k hk,
      apply hp,
      dsimp only at hk ⊢,
      rw [finset.mem_insert, finset.mem_singleton],
      right,
      simpa using hk, },
    { intros p hp,
      unfold simplex.face,
      rw [opens.mem_coe] at hp ⊢,
      rw opens.finset_infi,
      intros h hk,
      dsimp only at hk,
      rw [finset.mem_insert, finset.mem_singleton] at hk,
      rw ← opens.inter_eq at hp,
      rcases hp with ⟨hp1, hp2⟩,
      rcases hk with rfl|rfl,
      { exact hp1, },
      { exact hp2, }, },
    { exact eq2, } },
end

lemma unique_gluing_prop (f : add_monoid_hom.ker (@d_pos X 𝓕 𝔘.unop 1 (nat.zero_lt_succ 0))) :
  ∃! (s : 𝓕.val.obj (op ⊤)),
  ∀ (i : (unop 𝔘).ι),
    (𝓕.val.map (hom_of_le le_top).op) s =
    (𝓕.val.map (eq_to_hom (begin
        unfold simplex.face,
        simp,
      end : (unop 𝔘).cover i = ({to_finset := {i}, card_eq := begin
        rw finset.card_singleton,
      end} : simplex _ 0).face)).op) (f.val {to_finset := {i}, card_eq := rfl}) :=
begin
  exact sheaf.exists_unique_gluing' 𝓕 𝔘.unop.cover ⊤ (λ i, hom_of_le le_top) begin
      rw 𝔘.unop.is_cover,
      exact le_refl _,
    end (λ i, begin
      refine 𝓕.1.map (eq_to_hom _).op (f.1 ⟨{i}, rfl⟩),
      unfold simplex.face,
      simp,
    end) (ker_compatible 𝓕 𝔘 f),
end

noncomputable def unique_gluing (f : add_monoid_hom.ker (@d_pos X 𝓕 𝔘.unop 1 (nat.zero_lt_succ 0))) :
  𝓕.1.obj (op ⊤) :=
classical.some (unique_gluing_prop _ _ f)

lemma unique_gluing_is_glueing (f : add_monoid_hom.ker (@d_pos X 𝓕 𝔘.unop 1 (nat.zero_lt_succ 0))) (i : 𝔘.unop.ι) :
  𝓕.1.map (hom_of_le le_top).op (unique_gluing _ _ f) = 
  𝓕.1.map (eq_to_hom (begin
        unfold simplex.face,
        simp,
      end : (unop 𝔘).cover i = ({to_finset := {i}, card_eq := begin
        rw finset.card_singleton,
      end} : simplex _ 0).face)).op (f.1 ⟨{i}, rfl⟩) := 
begin
  have := classical.some_spec (unique_gluing_prop _ _ f),
  dsimp only at this,
  rcases this with ⟨h1, h2⟩,
  exact h1 i,
end

lemma unique_gluing_is_unique (f : add_monoid_hom.ker (@d_pos X 𝓕 𝔘.unop 1 (nat.zero_lt_succ 0))) (s : 𝓕.1.obj (op ⊤))
  (is_glue : ∀ (i : 𝔘.unop.ι), 
    𝓕.1.map (hom_of_le le_top).op s = 
    𝓕.1.map (eq_to_hom (begin
        unfold simplex.face,
        simp,
      end : (unop 𝔘).cover i = ({to_finset := {i}, card_eq := begin
        rw finset.card_singleton,
      end} : simplex _ 0).face)).op (f.1 ⟨{i}, rfl⟩)) :
  (unique_gluing _ _ f) = s :=
begin
  have := classical.some_spec (unique_gluing_prop _ _ f),
  dsimp only at this,
  rcases this with ⟨h1, h2⟩,
  symmetry,
  apply h2,
  assumption,
end

noncomputable def ex41.forward :
  (AddCommGroup.of $ add_monoid_hom.ker (@d_pos X 𝓕 (unop 𝔘) _ (nat.zero_lt_succ 0))) ⟶
  𝓕.1.obj (op ⊤) :=
{ to_fun := λ f, unique_gluing _ _ f,
  map_zero' := begin
    apply unique_gluing_is_unique,
    intros i,
    simp,
  end,
  map_add' := λ f g, begin
    apply unique_gluing_is_unique,
    intros i,
    rw map_add,
    erw map_add,
    congr;
    apply unique_gluing_is_glueing,
  end }

lemma inj :
  function.injective (ex41.forward 𝓕 𝔘) :=
begin
  intros f g h,
  change unique_gluing _ _ f = unique_gluing _ _ g at h,
  have h1 := unique_gluing_is_glueing _ _ f,
  rw subtype.ext_iff_val,
  ext σ,
  have eq1 : ∃ i, σ.to_finset = {i},
  { have := σ.card_eq,
    simp only [nat.pred_succ] at this,
    rwa finset.card_eq_one at this, },
  rcases eq1 with ⟨i, hi⟩,
  specialize h1 i,
  
  have h2 := unique_gluing_is_glueing _ _ g,
  specialize h2 i,

  rw [eq_to_hom_op, eq_to_hom_map] at h1 h2,
  rw h at h1,
  rw h1 at h2,

  have eq2 : σ = ⟨{i}, rfl⟩,
  { rw simplex.ext_iff, exact hi, },
  rw eq2,
  generalize_proofs _ _ h3 at h2,
  suffices : function.injective (eq_to_hom h3),
  apply this,
  exact h2,

  intros x y h,
  apply_fun (eq_to_hom h3.symm) at h,
  change (eq_to_hom h3 ≫ eq_to_hom h3.symm) x = (eq_to_hom h3 ≫ eq_to_hom h3.symm) y at h,
  rw [eq_to_hom_trans, eq_to_hom_refl] at h_1,
  simpa only using h_1,
end

lemma surj :
  function.surjective (ex41.forward 𝓕 𝔘) :=
begin
  rw function.surjective_iff_has_right_inverse,
  fconstructor,
  { intros s,
    refine ⟨λ σ, _, _⟩,
    exact 𝓕.1.map (hom_of_le le_top).op s,
    rw add_monoid_hom.mem_ker,
    ext σ,
    simp only [Cech.zero_apply],
    rw d_pos_01,
    change _ - _ = _,
    rw sub_eq_zero,
    dsimp only,
    change (𝓕.1.map _ ≫ 𝓕.1.map _) _ = (𝓕.1.map _ ≫ 𝓕.1.map _) _,
    suffices :
      (𝓕.val.map ((simplex.der d0._proof_6 σ ⟨0, d0._proof_5⟩) ≫ (hom_of_le le_top)).op) s =
      (𝓕.val.map ((simplex.der d0._proof_10 σ ⟨1, d0._proof_9⟩) ≫ (hom_of_le le_top)).op) s,
    convert this,
    rw op_comp,
    rw 𝓕.1.map_comp,

    rw op_comp,
    rw 𝓕.1.map_comp,

    apply 𝓕_map_congr',
    refl, },
  { intros s,
    apply unique_gluing_is_unique,
    intros i,
    dsimp only,
    change _ = (𝓕.1.map _ ≫ 𝓕.1.map _) _,
    congr' 1,
    rw ← 𝓕.1.map_comp,
    rw ← op_comp,
    congr' 1,
  },
end

-- #check equiv.of_bijective (ex41.forward 𝓕 𝔘) ⟨inj _ _, surj _ _⟩
noncomputable def ex41 :
  (AddCommGroup.of $ add_monoid_hom.ker (@d_pos X 𝓕 (unop 𝔘) _ (nat.zero_lt_succ 0))) ≃+
  𝓕.1.obj (op ⊤) :=
add_equiv.of_bijective (ex41.forward _ _) ⟨inj _ _, surj _ _⟩

noncomputable def ex4 :
  homological_complex.homology (cech_chain 𝓕 𝔘) 0 ≅
  (AddCommGroup.ulift_functor.{u u+1}).obj (𝓕.1.obj (op ⊤)) :=
begin
  refine ex1 _ _ ≪≫ _,
  refine ex2 _ _ ≪≫ _,
  refine AddCommGroup.ulift_kernel_iso_kernel_ulift _ ≪≫ _,
  apply AddCommGroup.ulift_iso,
  refine AddCommGroup.kernel_iso_ker _ ≪≫ _,
  refine { hom := _, inv := _, hom_inv_id' := _, inv_hom_id' := _ },
  { exact (ex41 _ _).to_add_monoid_hom, },
  { exact (ex41 _ _).symm.to_add_monoid_hom },
  { ext1,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.symm_apply_apply, id_apply], },
  { ext1,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.apply_symm_apply, id_apply]},
end

noncomputable def cech_cohomology_wrt_cover_nth (n : ℕ) : Ab :=
  homological_complex.homology (cech_chain 𝓕 𝔘) n

noncomputable def cech_cohomology_wrt_cover_nth_map (n : ℕ) {A B : (X.oc)ᵒᵖ}
  (f : A ⟶ B) :
  (cech_cohomology_wrt_cover_nth 𝓕 A n) ⟶ (cech_cohomology_wrt_cover_nth 𝓕 B n) :=
homology.map _ _ 
{ left := match n with
  | nat.zero := 0
  | nat.succ n := begin
    refine (homological_complex.X_prev_iso (cech_chain 𝓕 A) (show n + 1 = n + 1, from rfl)).hom ≫ _,
    refine (_ : (cech_chain 𝓕 A).X n ⟶ (cech_chain 𝓕 B).X n) ≫ 
      (homological_complex.X_prev_iso (cech_chain 𝓕 B) (show n + 1 = n + 1, from rfl)).inv,
    refine AddCommGroup.ulift_functor.map _,
    apply C.refine,
    exact f.unop,
  end
  end,
  right := begin
    refine AddCommGroup.ulift_functor.map _,
    apply C.refine,
    exact f.unop,
  end,
  w' := begin
    simp only [functor.id_map, arrow.mk_hom],
    cases n,
    { change 0 ≫ _ = _,
      simp only [homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero, zero_comp], },
    { change (_ ≫ _ ≫ _) ≫ _ = _ ≫ _,
      simp only [category.assoc, homological_complex.X_prev_iso_comp_d_to, cech_chain_d],
      ext g σ,
      simp only [AddCommGroup.ulift_functor_map_down, comp_apply],
      rw d.to_succ,
      rw homological_complex.d_to_eq (cech_chain 𝓕 A) (show n + 1 = n + 1, from rfl),
      simp only [cech_chain_d, comp_apply],
      },
  end } 
{ left := _,
  right := _,
  w' := _ } _

include 𝓕
example (n : ℕ) {A B : (X.oc)ᵒᵖ}
  (f : A ⟶ B) : true :=
begin
  have := (cech_chain 𝓕)
end

noncomputable
def ex : ℕ ⥤ Ab :=
{ obj := λ i, cech_cohomology_wrt_cover_nth 𝓕 𝔘 i,
  map := λ i j h, begin
    have := le_of_hom h,
    sorry
  end,
  map_id' := sorry,
  map_comp' := sorry }

-- lemma aux1 (i k : ℕ) (A : X.ocᵒᵖ) (σ : simplex (unop A) k) (f : (cech_chain 𝓕 A).X i) : 
--   ((0 : Cech_Ab 𝓕 i ⟶ Cech_Ab 𝓕 k).app A f).down σ = 0 :=
-- begin
--   rw show (0 : Cech_Ab 𝓕 i ⟶ Cech_Ab 𝓕 k).app A f = 0, from rfl,
--   rw [AddCommGroup.ulift.zero_down],
--   refl,
-- end

-- lemma aux2 (i j : ℕ) : colim.map (0 : Cech_Ab 𝓕 i ⟶ Cech_Ab 𝓕 j) = 0 := 
-- begin
--   apply colimit.hom_ext,
--   intros U,
--   ext x,
--   simp only [colimit.ι_map, nat_trans.app_zero, zero_comp, comp_zero],
-- end

-- noncomputable def Cech_complex_colimit : cochain_complex Ab.{u+1} ℕ :=
-- { X := λ n, colim.obj (Cech_Ab 𝓕 n),
--   d := λ i j, colim.map $ 
--   { app := λ A, Cech_d 𝓕 A i j,
--     naturality' := λ A B r, begin
--       -- sorry
--       ext f σ,
--       by_cases ineq1 : i + 1 = j,
--       { subst ineq1, 
--         simp only [Cech_Ab_map, Cech_d_succ_down_apply, comp_apply, AddCommGroup.ulift_functor_map_down],
--         rw [d_pos.def],
--         change _ = 𝓕.1.map _ _,
--         rw [d_pos.def, add_monoid_hom.map_sum],
--         apply finset.sum_congr rfl (λ j hj, _),
--         by_cases e : even j.1,
--         { rw [if_pos e, id, if_pos e, id],
--           change ((𝓕.1.map _) ≫ (𝓕.1.map _)) _ = ((𝓕.1.map _) ≫ (𝓕.1.map _)) _,
--           rw [← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp],
--           induction f,
--           dsimp only,
--           apply 𝓕_map_congr'',
--           exact r.unop,
--           symmetry,
--           apply simplex.refine_ignore },
--         { rw [if_neg e, if_neg e, map_neg],
--           congr' 1,
--           change ((𝓕.1.map _) ≫ (𝓕.1.map _)) _ = ((𝓕.1.map _) ≫ (𝓕.1.map _)) _,
--           rw [← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp],
--           induction f,
--           dsimp only,
--           apply 𝓕_map_congr'',
--           exact r.unop,
--           symmetry,
--           apply simplex.refine_ignore, }, },
--       { simp only [Cech_Ab_map, comp_apply, AddCommGroup.ulift_functor_map_down],
--         change _ = 𝓕.1.map _ _,
--         rw [Cech_d_not_succ_down_apply, Cech_d_not_succ_down_apply, Cech.zero_apply, Cech.zero_apply, map_zero];
--         exact ineq1, },
--     end },
--   shape' := λ i j h, begin
--     suffices : colim.map 0 = 0,
--     { convert this,
--       ext A f σ,
--       rw [Cech_d_not_succ_down_apply, Cech.zero_apply],
--       refl, 
--       exact h,},
--     { apply aux2, },
--   end,
--   d_comp_d' := λ i j k h1 h2, begin
--     rw ← category_theory.functor.map_comp,
--     suffices : colim.map 0 = 0,
--     { convert this,
--       ext A f σ,
--       rw [nat_trans.comp_app],
--       dsimp only,
--       rw aux1 𝓕,
--       change i + 1 = j at h1,
--       subst h1,
--       change (i + 1) + 1 = k at h2,
--       subst h2,
--       rw [category_theory.comp_apply, Cech_d_succ_down_apply, Cech_d_succ_down_apply],
--       convert dd_pos_eq_zero _ _ _, },
--     { apply aux2, },
--   end }

end

end
