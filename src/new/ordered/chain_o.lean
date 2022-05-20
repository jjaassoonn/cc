import new.ordered.C_o
import algebra.homology.homological_complex
import algebra.category.Group.abelian
import algebra.homology.homology
import topology.sheaves.sheaf_condition.unique_gluing
-- import new.refinement

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open category_theory.limits
open opposite
open nat

open_locale big_operators

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U V : X.oc)

section

variables {U}

def vec_o.single (i : U.ι) : vec_o U 1 :=
{ to_fun := λ _, i,
  is_strict_mono := λ ⟨i, hi⟩ ⟨j, hj⟩ (h : i < j), by linarith }

def vec_o.double {i j : U.ι} (h : i < j) :
  vec_o U 2 :=
{ to_fun := ![i, j],
  is_strict_mono := begin
    intros m n ineq,
    fin_cases m;
    fin_cases n,
    { exfalso, exact lt_irrefl _ ineq, },
    { exact h },
    { have triv : ¬ 1 < 0,
      { rw not_lt,
        linarith, },
      exfalso, exact triv ineq, },
    { exfalso, exact lt_irrefl _ ineq, },
  end }

lemma vec_o.double_apply0 {i j : U.ι} (h : i < j) :
  vec_o.double h 0 = i :=
begin
  change ![i, j] 0 = i,
  simp only [matrix.cons_val_zero],
end

lemma vec_o.double_apply1 {i j : U.ι} (h : i < j) :
  vec_o.double h 1 = j :=
begin
  change ![i, j] 1 = j,
  simp only [matrix.cons_val_one, matrix.head_cons],
end

lemma vec_o.double_ignore0 {i j : U.ι} (h : i < j) :
  ignore_o (vec_o.double h) 0 = vec_o.single j :=
sorry

lemma vec_o.double_ignore1 {i j : U.ι} (h : i < j) :
  ignore_o (vec_o.double h) 1 = vec_o.single i :=
sorry

lemma face.vec_o_single (i : U.ι) :
  face_o (vec_o.single i) = U.cover i :=
begin
  change face (vec_o.single i) = _,
  ext,
  split;
  intros hx;
  rw opens.mem_coe at hx ⊢,
  { erw opens.fintype_infi at hx,
    specialize hx 0,
    convert hx,  },
  { erw opens.fintype_infi,
    rintros ⟨i, hi⟩,
    interval_cases i,
    convert hx, },
end

lemma face.double_le_single1 {i j : U.ι} (h : i < j) :
  face_o (vec_o.double h) ≤ face_o (vec_o.single i) := sorry

lemma face.double_le_single2 {i j : U.ι} (h : i < j) :
  face_o (vec_o.double h) ≤ face_o (vec_o.single j) := sorry


end

def d_o_from_to (i j : ℕ) : C_o 𝓕 U i ⟶ C_o 𝓕 U j :=
dite (j = i + 1)
(λ h, d_o 𝓕 U i ≫ eq_to_hom (by rw h))
(λ h, 0)

lemma d_o_to_succ {i : ℕ} (f α) :
  d_o_from_to 𝓕 U i (i + 1) f α = d_o 𝓕 U i f α :=
begin
  rw [d_o_from_to],
  rw dif_pos rfl,
  rw comp_apply,
  refl,
end

lemma d_o_to_succ' (i : ℕ) :
  d_o_from_to 𝓕 U i (i + 1) = d_o 𝓕 U i :=
begin
  ext f α,
  rw d_o_from_to,
  rw dif_pos rfl,
  refl,
end

lemma d_o_not_to_succ {i j : ℕ} (h : j ≠ i + 1) (f α) :
  d_o_from_to 𝓕 U i j f α = 0 :=
begin
  rw [d_o_from_to, dif_neg h],
  refl,
end

def Cech_complex_wrt_cover_ordered : cochain_complex Ab.{u} ℕ :=
{ X := λ n, C_o 𝓕 U (n + 1),
  d := λ i j, d_o_from_to 𝓕 U _ _,
  shape' := λ i j h, begin
    ext f α,
    rw d_o_not_to_succ,
    rw [add_monoid_hom.zero_apply, pi.zero_apply],
    simp only [complex_shape.up_rel] at h,
    contrapose! h,
    symmetry,
    simpa [add_left_inj] using h,
  end,
  d_comp_d' := λ i j k h1 h2, begin
    simp only [complex_shape.up_rel] at h1 h2,
    subst' h2,
    subst' h1,
    ext f α,
    rw comp_apply,
    rw d_o_to_succ,
    rw d_o_to_succ',
    simp only [AddCommGroup.zero_apply, pi.zero_apply],
    rw dd_o_eq_zero,
  end }

lemma Cech_complex_wrt_cover_ordered.d_to_rel
  (n : ℕ) (m) (h : (complex_shape.up ℕ).prev n = some m) :
  (Cech_complex_wrt_cover_ordered 𝓕 U).d m.1 n =
  d_o 𝓕 U (m.1 + 1) ≫ eq_to_hom begin
    have := m.2,
    simp only [complex_shape.up_rel] at this,
    rw this,
    refl,
  end :=
begin
  change d_o_from_to 𝓕 U _ _ = _,
  rw [d_o_from_to, dif_pos],
  refl,
  rw add_left_inj,
  exact m.2.symm,
end

def Cech_Cohomology_Group_wrt_cover_ordered_nth (n : ℕ) : Ab :=
@homological_complex.homology ℕ Ab _ _ (complex_shape.up ℕ) (abelian.has_zero_object) _ _ _
  (Cech_complex_wrt_cover_ordered 𝓕 U) n

section zeroth

def ex1 :
  Cech_Cohomology_Group_wrt_cover_ordered_nth 𝓕 U 0 ≅
  kernel ((Cech_complex_wrt_cover_ordered 𝓕 U).d 0 1) :=
begin
  refine homology_iso_cokernel_image_to_kernel' _ _ _ ≪≫ _,
  change cokernel (kernel.lift _ _ _) ≅ _,

  simp only [image.ι_zero', homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero, eq_self_iff_true, kernel.lift_zero],
  refine cokernel_zero_iso_target ≪≫ _,
  refine AddCommGroup.kernel_iso_ker _ ≪≫ _,
  refine _ ≪≫ (AddCommGroup.kernel_iso_ker (d_o 𝓕 U _)).symm,
  refine { hom := _, inv := _, hom_inv_id' := _, inv_hom_id' := _ },
  { refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros x,
      refine ⟨x.1, _⟩,
      rw add_monoid_hom.mem_ker,
      have := x.2,
      rw add_monoid_hom.mem_ker at this,
      have eq1 := homological_complex.d_from_eq (Cech_complex_wrt_cover_ordered 𝓕 U) (show 1 = 0 + 1, from rfl),
      generalize_proofs h1 h2 at eq1,
      change _ = d_o _ _ _ ≫ _ at eq1,
      have eq2 : homological_complex.d_from (Cech_complex_wrt_cover_ordered 𝓕 U) 0 x.1 = (d_o 𝓕 _ _ ≫ (homological_complex.X_next_iso (Cech_complex_wrt_cover_ordered 𝓕 U) h1).inv) x.1,
      { apply congr_fun,
        simpa only [fun_like.coe_fn_eq] using eq1, },
      apply_fun (homological_complex.X_next_iso (Cech_complex_wrt_cover_ordered 𝓕 U) h1).hom at eq2,
      rw comp_apply at eq2,
      rw this at eq2,
      simp only [map_zero, coe_inv_hom_id] at eq2,
      rw ←eq2, 
      },
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
      have eq1 := homological_complex.d_from_eq (Cech_complex_wrt_cover_ordered 𝓕 U) (show 1 = 0 + 1, from rfl),
      erw eq1,
      rw comp_apply,
      generalize_proofs h1 h2,
      apply_fun (homological_complex.X_next_iso (Cech_complex_wrt_cover_ordered 𝓕 U) h1).hom,
      simp only [coe_inv_hom_id, map_zero],
      convert this,
      apply function.bijective.injective,
      rw function.bijective_iff_has_inverse,
      use (homological_complex.X_next_iso (Cech_complex_wrt_cover_ordered 𝓕 U) h1).inv,
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

def ex2 :
  kernel ((Cech_complex_wrt_cover_ordered 𝓕 U).d 0 1) ≅
  kernel (d_o 𝓕 U 1) :=
eq_to_iso rfl

def ex3 :
  kernel (d_o 𝓕 U 1) ≅
  AddCommGroup.of (add_monoid_hom.ker (d_o 𝓕 U 1)) :=
AddCommGroup.kernel_iso_ker _

lemma ex41.forward.aux1 {i j : U.ι} {f : C_o 𝓕 U 1} 
  (h : d_o _ _ _ f = 0) :
  𝓕.1.map ((U.cover i).inf_le_left (U.cover j) ≫ eq_to_hom begin
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single i)) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_left,
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single i)) :=
begin
  congr,
end

lemma ex41.forward.aux1' {i j : U.ι} {f : C_o 𝓕 U 1} 
  (h : d_o _ _ _ f = 0) :
  𝓕.1.map ((U.cover i).inf_le_right (U.cover j) ≫ eq_to_hom begin
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single j)) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_right,
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single j)) :=
begin
  congr,
end

lemma ex41.forward.aux2 {i j : U.ι} {f : C_o 𝓕 U 1} 
  (h : d_o _ _ _ f = 0) :
  𝓕.1.map ((U.cover i).inf_le_right (U.cover j) ≫ eq_to_hom begin
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single j)) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_right,
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single j)) :=
begin
  congr,
end

lemma ex41.forward.aux2' {i j : U.ι} {f : C_o 𝓕 U 1} 
  (h : d_o _ _ _ f = 0) :
  𝓕.1.map ((U.cover i).inf_le_left (U.cover j) ≫ eq_to_hom begin
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single i)) = 
  𝓕.1.map (hom_of_le begin
    convert inf_le_left,
    rw ← face.vec_o_single,
    refl,
  end).op (f (vec_o.single i)) :=
begin
  congr,
end

lemma ex41.forward.aux3 {i j : U.ι} (ineq : i < j) (f : C_o 𝓕 U 1) :
  𝓕.1.map (hom_of_le (face.le_ignore_o _ _)).op (f (ignore_o (vec_o.double ineq) 0)) =
  𝓕.1.map ((hom_of_le (face.double_le_single2 ineq))).op (f (vec_o.single j)) :=
begin
  generalize_proofs _ h1 h2,
  rw map_congr.vec_o_eq f (vec_o.double_ignore0 ineq),
  rw [← comp_apply, ← 𝓕.1.map_comp],
  congr,
end

lemma ex41.forward.aux3' {i j : U.ι} (ineq : j < i) (f : C_o 𝓕 U 1) :
  𝓕.1.map (hom_of_le (face.le_ignore_o _ _)).op 
  (f (ignore_o (vec_o.double ineq) 0)) =
  𝓕.1.map 
  (hom_of_le (face.double_le_single2 ineq)).op 
  (f (vec_o.single i)) 
  :=
begin
  generalize_proofs _ h1 h2 h3 h4 h5,
  rw map_congr.vec_o_eq f (vec_o.double_ignore0 ineq),
  rw [← comp_apply, ← 𝓕.1.map_comp],
  congr,
end

lemma ex41.forward.aux4 {i j : U.ι} (ineq : i < j) (f : C_o 𝓕 U 1) :
  𝓕.1.map (hom_of_le (face.le_ignore_o _ _)).op (f (ignore_o (vec_o.double ineq) 1)) =
  𝓕.1.map (hom_of_le (face.double_le_single1 ineq)).op (f (vec_o.single i)) 
  :=
begin
  generalize_proofs _ h1 h2,
  rw map_congr.vec_o_eq f (vec_o.double_ignore1 ineq),
  rw [← comp_apply, ← 𝓕.1.map_comp],
  congr,
end

lemma ex41.forward.aux4' {i j : U.ι} (ineq : j < i) (f : C_o 𝓕 U 1) :
  𝓕.1.map (hom_of_le (face.le_ignore_o _ _)).op 
  (f (ignore_o (vec_o.double ineq) 1)) =
  𝓕.1.map 
  (hom_of_le (face.double_le_single1 ineq)).op 
  (f (vec_o.single j)) 
  :=
begin
  generalize_proofs _ h1 h2,
  rw map_congr.vec_o_eq f (vec_o.double_ignore1 ineq),
  rw [← comp_apply, ← 𝓕.1.map_comp],
  congr,
end

lemma ex41.forward.aux5 (f : C_o 𝓕 U 1) 
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

lemma ker_compatible (f : add_monoid_hom.ker (d_o 𝓕 U 1)) : 
  presheaf.is_compatible 𝓕.1 U.cover 
  (λ i, begin
    refine 𝓕.1.map (eq_to_hom _).op (f.1 (vec_o.single i)),
    rw ← face.vec_o_single,
    refl,
  end) :=
begin
  intros i j,
  have := f.2,
  rw add_monoid_hom.mem_ker at this,
      
  rcases @trichotomous U.ι (<) _ i j with ineq|ineq|ineq,
  { dsimp only,
    change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
    rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← op_comp, ← op_comp],
    rw ex41.forward.aux1 _ _ this,
    rw ex41.forward.aux2 _ _ this,

    have eq1 : d_o _ _ _ f.1 (vec_o.double ineq) = 0,
    { rw this, simp, },
    simp only [d_o_small.d_o.one_apply] at eq1,
    rw sub_eq_zero at eq1,
    rw ex41.forward.aux3 at eq1,
    have eq2 := eq.trans eq1 (ex41.forward.aux4 𝓕 U ineq f.1),
          
    refine ex41.forward.aux5 𝓕 U f.1 (face_o (vec_o.double ineq)) 
      (face_o (vec_o.single i))
      (face_o (vec_o.single j))
      (U.cover i ⊓ U.cover j)
      (f.val (vec_o.single i))
      (f.val (vec_o.single j))
      _ _ _ _ _ _,
    { apply face.double_le_single1, },
    { apply face.double_le_single2, },
    { intros p hp,
      rcases hp with ⟨hp1, hp2⟩,
      rw opens.mem_coe at hp1 hp2 ⊢,
      erw opens.fintype_infi,
      intros k,
      fin_cases k,
      { rwa vec_o.double_apply0, },
      { rwa vec_o.double_apply1, }, },
    { exact eq2.symm, }, },
  { subst ineq, refl, },
  { dsimp only,
    change (𝓕.1.map _ ≫ _) _ = (𝓕.1.map _ ≫ _) _,
    rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← op_comp, ← op_comp],
    rw ex41.forward.aux1' _ _ this,
    rw ex41.forward.aux2' _ _ this,

    have eq1 : d_o _ _ _ f.1 (vec_o.double ineq) = 0,
    { rw this, simp, },
    simp only [d_o_small.d_o.one_apply] at eq1,
    change _ - _ = _ at eq1,
    rw sub_eq_zero at eq1,
    dsimp only at eq1,
    rw ex41.forward.aux3' at eq1,
    have eq2 := eq.trans eq1 (ex41.forward.aux4' 𝓕 U ineq f.1),

    refine ex41.forward.aux5 𝓕 U f.1 
      (face_o (vec_o.double ineq)) 
      (face_o (vec_o.single i))
      (face_o (vec_o.single j))
      (U.cover i ⊓ U.cover j)
      (f.val (vec_o.single i))
      (f.val (vec_o.single j))
      _ _ _ _ _ _,
    { apply face.double_le_single2, },
    { apply face.double_le_single1, },
    { intros p hp,
      rcases hp with ⟨hp1, hp2⟩,
      rw opens.mem_coe at hp1 hp2 ⊢,
      erw opens.fintype_infi,
      intros k,
      fin_cases k,
      { rwa vec_o.double_apply0, },
      { rwa vec_o.double_apply1, }, },
    { convert eq2, }, },
end

lemma unique_gluing_prop 
  (f : add_monoid_hom.ker (d_o 𝓕 U 1)) :
  ∃! (s : 𝓕.val.obj (op ⊤)),
  ∀ (i : U.ι),
    (𝓕.val.map (hom_of_le le_top).op) s =
    (𝓕.val.map (eq_to_hom (by rw ← face.vec_o_single : U.cover i = (face_o (vec_o.single i)))).op)
      (f.val (vec_o.single i)) :=
sheaf.exists_unique_gluing' 
  𝓕 U.cover ⊤ 
  (λ i, hom_of_le le_top) 
  begin
    rw U.is_cover,
    exact le_refl _,
  end 
  (λ i, begin
    refine 𝓕.1.map (eq_to_hom _).op (f.1 (vec_o.single i)),
    rw ← face.vec_o_single,
    refl,
  end) 
  (ker_compatible 𝓕 U f)

def unique_gluing (f : add_monoid_hom.ker (d_o 𝓕 U 1)) :
  𝓕.1.obj (op ⊤) :=
classical.some (unique_gluing_prop _ _ f)

lemma unique_gluing_is_glueing 
  (f : add_monoid_hom.ker (d_o 𝓕 U 1))  
  (i : U.ι) :
  𝓕.1.map (hom_of_le le_top).op (unique_gluing _ _ f) = 
  𝓕.1.map (eq_to_hom (begin
    rw ← face.vec_o_single,
    refl,
  end : U.cover i = _)).op (f.1 (vec_o.single i)) := 
begin
  have := classical.some_spec (unique_gluing_prop _ _ f),
  dsimp only at this,
  rcases this with ⟨h1, h2⟩,
  exact h1 i,
end

lemma unique_gluing_is_unique 
  (f : add_monoid_hom.ker (d_o 𝓕 U 1))  
  (s : 𝓕.1.obj (op ⊤))
  (is_glue : ∀ (i : U.ι), 
    𝓕.1.map (hom_of_le le_top).op s = 
    𝓕.1.map (eq_to_hom (begin
      rw ← face.vec_o_single,
      refl,
    end : U.cover i = _)).op (f.1 (vec_o.single i))) :
  (unique_gluing _ _ f) = s :=
begin
  have := classical.some_spec (unique_gluing_prop _ _ f),
  dsimp only at this,
  rcases this with ⟨h1, h2⟩,
  symmetry,
  apply h2,
  assumption,
end

def ex41.forward :
  (AddCommGroup.of $ add_monoid_hom.ker (d_o 𝓕 U 1)) ⟶ 𝓕.1.obj (op ⊤) :=
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
  function.injective (ex41.forward 𝓕 U) :=
begin
  intros f g h,
  change unique_gluing _ _ f = unique_gluing _ _ g at h,
  have h1 := unique_gluing_is_glueing _ _ f,
  rw subtype.ext_iff_val,
  ext σ,
  -- have eq1 : ∃ i, σ.to_finset = {i},
  -- { have := σ.card_eq,
  --   simp only [nat.pred_succ] at this,
  --   rwa finset.card_eq_one at this, },
  -- rcases eq1 with ⟨i, hi⟩,
  specialize h1 (σ 0),
  
  have h2 := unique_gluing_is_glueing _ _ g,
  specialize h2 (σ 0),

  rw [eq_to_hom_op, eq_to_hom_map] at h1 h2,
  rw h at h1,
  rw h1 at h2,

  have eq2 : σ = vec_o.single (σ 0),
  { ext, rcases x with ⟨x, hx⟩, interval_cases x, refl, },
  rw eq2,
  generalize_proofs _ h3 at h2,
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
  function.surjective (ex41.forward 𝓕 U) :=
begin
  rw function.surjective_iff_has_right_inverse,
  fconstructor,
  { intros s,
    refine ⟨λ σ, _, _⟩,
    exact 𝓕.1.map (hom_of_le le_top).op s,
    rw add_monoid_hom.mem_ker,
    ext σ,
    rw pi.zero_apply,
    rw d_o_small.d_o.one_apply,
    rw sub_eq_zero,
    dsimp only,
    change (𝓕.1.map _ ≫ 𝓕.1.map _) _ = (𝓕.1.map _ ≫ 𝓕.1.map _) _,
    rw [← 𝓕.1.map_comp,  ← 𝓕.1.map_comp, ← op_comp],
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

def ex41 :
  (AddCommGroup.of $ add_monoid_hom.ker (d_o 𝓕 U 1)) ≃+
  𝓕.1.obj (op ⊤) :=
add_equiv.of_bijective (ex41.forward _ _) ⟨inj _ _, surj _ _⟩


def zeroth_Cech_Cohomology :
  (Cech_Cohomology_Group_wrt_cover_ordered_nth 𝓕 U 0) ≅
  𝓕.1.obj (op ⊤) :=
ex1 𝓕 U ≪≫ ex2 𝓕 U ≪≫ ex3 𝓕 U ≪≫ 
{ hom := (ex41 _ _).to_add_monoid_hom,
  inv := (ex41 _ _).symm.to_add_monoid_hom,
  hom_inv_id' := begin
    ext f σ,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.symm_apply_apply, id_apply],
  end,
  inv_hom_id' := begin
    ext f σ,
    simp only [comp_apply, add_equiv.coe_to_add_monoid_hom, add_equiv.apply_symm_apply, id_apply],
  end }


end zeroth

end