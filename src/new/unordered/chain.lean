import new.unordered.d
import algebra.homology.homological_complex
import algebra.category.Group.abelian
import algebra.homology.homology
import new.unordered.refinement

noncomputable theory

section

open topological_space Top Top.sheaf
open category_theory
open opposite
open nat

open_locale big_operators

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U V : X.oc)

def d_from_to (i j : ℕ) : C 𝓕 U i ⟶ C 𝓕 U j :=
dite (j = i + 1)
(λ h, d 𝓕 U i ≫ eq_to_hom (by rw h))
(λ h, 0)

lemma d_to_succ {i : ℕ} (f α) :
  d_from_to 𝓕 U i (i + 1) f α = d 𝓕 U i f α :=
begin
  rw [d_from_to],
  rw dif_pos rfl,
  rw comp_apply,
  refl,
end

lemma d_to_succ' (i : ℕ) :
  d_from_to 𝓕 U i (i + 1) = d 𝓕 U i :=
begin
  ext f α,
  rw d_to_succ,
end

lemma d_not_to_succ {i j : ℕ} (h : j ≠ i + 1) (f α) :
  d_from_to 𝓕 U i j f α = 0 :=
begin
  rw [d_from_to, dif_neg h],
  refl,
end

def Cech_complex_wrt_cover_unordered : cochain_complex Ab.{u} ℕ :=
{ X := λ n, C 𝓕 U (n + 1),
  d := λ i j, d_from_to 𝓕 U (i + 1) (j + 1),
  shape' := λ i j h, begin
    ext f α,
    rw d_not_to_succ,
    rw [add_monoid_hom.zero_apply, pi.zero_apply],
    simp only [complex_shape.up_rel] at h,
    contrapose! h,
    simp only [add_left_inj] at h,
    exact h.symm,
  end,
  d_comp_d' := λ i j k h1 h2, begin
    simp only [complex_shape.up_rel] at h1 h2,
    subst' h2,
    subst' h1,
    ext f α,
    rw comp_apply,
    rw d_to_succ,
    rw d_to_succ',
    simp only [AddCommGroup.zero_apply, C_pre.zero_apply],
    rw dd_eq_zero,
  end }

lemma Cech_complex_wrt_cover_unordered.d_to_rel
  (n : ℕ) (m) (h : (complex_shape.up ℕ).prev n = some m) :
  (Cech_complex_wrt_cover_unordered 𝓕 U).d m.1 n =
  d 𝓕 U (m.1 + 1) ≫ eq_to_hom begin
    have := m.2,
    simp only [complex_shape.up_rel] at this,
    rw this,
    refl,
  end :=
begin
  change d_from_to 𝓕 U _ _ = _,
  rw [d_from_to, dif_pos],
  refl,
  have h2 := m.2.symm,
  rw ← h2,
end

def Cech_Cohomology_Group_wrt_cover_unordered_nth (n : ℕ) : Ab.{u} :=
@homological_complex.homology ℕ Ab _ _ (complex_shape.up ℕ) (abelian.has_zero_object) _ _ _
  (Cech_complex_wrt_cover_unordered 𝓕 U) n

section

variables {U V} (r : U ⟶ V)

include r
def Cech_complex_wrt_cover_unordered.prev (n : ℕ) :
  @homological_complex.X_prev _ _ _ _ (complex_shape.up ℕ) 
    (Cech_complex_wrt_cover_unordered 𝓕 V)
    (abelian.has_zero_object) n ⟶
  @homological_complex.X_prev _ _ _ _ (complex_shape.up ℕ)
    (Cech_complex_wrt_cover_unordered 𝓕 U)
    (abelian.has_zero_object) n :=
match (complex_shape.up ℕ).prev n with
| none := 0
| some m := begin
  refine _ ≫ @C.refine X 𝓕 _ _ (m.1 + 1) r ≫ _,
  refine (@@homological_complex.X_prev_iso _ _ _ (abelian.has_zero_object) m.2).hom,
  exact (@@homological_complex.X_prev_iso _ _ (Cech_complex_wrt_cover_unordered 𝓕 U) (abelian.has_zero_object) m.2).inv,
end
end

lemma Cech_complex_wrt_cover_unordered.prev_none (n : ℕ)
  (h : (complex_shape.up ℕ).prev n = none) :
  Cech_complex_wrt_cover_unordered.prev 𝓕 r n = 0 :=
begin
  rw Cech_complex_wrt_cover_unordered.prev,
  rw h,
  refl,
end 

lemma Cech_Group_wrt_cover_unordered_nth.prev_some (n : ℕ) (m)
  (h : (complex_shape.up ℕ).prev n = some m) :
  Cech_complex_wrt_cover_unordered.prev 𝓕 r n = 
  (@@homological_complex.X_prev_iso _ _ _ (abelian.has_zero_object) m.2).hom ≫ 
    @C.refine X 𝓕 _ _ (m.1 + 1) r ≫ 
    (@@homological_complex.X_prev_iso _ _ (Cech_complex_wrt_cover_unordered 𝓕 U) (abelian.has_zero_object) m.2).inv :=
begin
  rw Cech_complex_wrt_cover_unordered.prev,
  rw h,
  refl,
end  

example (n : ℕ) : (complex_shape.up ℕ).next n = some ⟨n+1, rfl⟩ :=
begin
  rw [complex_shape.next_eq_some],
end

def Cech_Cohomology_Group_wrt_cover_unordered_nth.refinement (n : ℕ) :
  Cech_Cohomology_Group_wrt_cover_unordered_nth 𝓕 V n ⟶
  Cech_Cohomology_Group_wrt_cover_unordered_nth 𝓕 U n :=
homology.map _ _ 
{ left := Cech_complex_wrt_cover_unordered.prev 𝓕 r n,
  right := C.refine r,
  w' := begin
    simp only [category_theory.functor.id_map, arrow.mk_hom],
    ext f α,
    rw [comp_apply, comp_apply],
    by_cases h : (complex_shape.up ℕ).prev n = none,
    { rw Cech_complex_wrt_cover_unordered.prev_none,
      rw homological_complex.d_to_eq_zero,
      rw homological_complex.d_to_eq_zero,
      swap, exact h,
      swap, exact h,
      swap, exact h,
      simp only [AddCommGroup.zero_apply, C_pre.zero_apply, map_zero], },
    { change _ ≠ _ at h,
      rw option.ne_none_iff_exists at h,
      rcases h with ⟨m, hm⟩,
      rw Cech_Group_wrt_cover_unordered_nth.prev_some,
      swap, exact hm.symm,
      rw homological_complex.d_to_eq,
      swap, exact m.2,
      rw homological_complex.d_to_eq,
      swap, exact m.2,
      simp only [comp_apply, coe_inv_hom_id],
      rw Cech_complex_wrt_cover_unordered.d_to_rel,
      swap, exact hm.symm,
      rw Cech_complex_wrt_cover_unordered.d_to_rel,
      swap, exact hm.symm,
      rw comp_apply,
      rw comp_apply,
      rw ← C.refine_d_eq_d_refine',
      
      simp only [← comp_apply],
      congr' 1,
      simp only [category.assoc],
      apply whisker_eq,
      apply whisker_eq,
      
      rw C.refine_eq_to_hom,
      have : _ + 1 = _ := m.2, 
      rw this, },
  end } 
{ left := C.refine r,
  right := (@@homological_complex.X_next_iso _ _ (Cech_complex_wrt_cover_unordered 𝓕 V) 
      (abelian.has_zero_object) 
      (rfl : n + 1 = n + 1)).hom ≫ 
      C.refine r ≫ 
      (@@homological_complex.X_next_iso _ _ (Cech_complex_wrt_cover_unordered 𝓕 U) 
        (abelian.has_zero_object) 
        (rfl : n + 1 = n + 1)).inv,
  w' := begin
    simp only [category_theory.functor.id_map, arrow.mk_hom],
    ext f α,
    simp only [comp_apply, homological_complex.d_from_comp_X_next_iso_assoc],
    rw homological_complex.d_from_eq,
    swap 2, exact (rfl : n + 1 = n + 1),
    simp only [← comp_apply],
    congr' 1,
    simp only [← category.assoc],
    apply eq_whisker,
    change C.refine r ≫ d_from_to 𝓕 U _ _ = _,
    rw d_to_succ',
    change _ = d_from_to _ _ _ _ ≫ C.refine r,
    rw d_to_succ',
    rw C.refine_d_eq_d_refine,
  end } 
rfl

def Cech_Cohomology_Group_wrt_cover_unordered_nth.refinement_functor (n : ℕ) :
  X.ocᵒᵖ ⥤ Ab.{u} :=
{ obj := λ U, Cech_Cohomology_Group_wrt_cover_unordered_nth 𝓕 U.unop n,
  map := λ U V r, Cech_Cohomology_Group_wrt_cover_unordered_nth.refinement 𝓕 r.unop n,
  map_id' := λ U, begin
    rw [Cech_Cohomology_Group_wrt_cover_unordered_nth.refinement],
    ext f,
    simp only [unop_id, homology.π_map, comp_apply, id_apply],
    congr',
    sorry
  end,
  map_comp' := sorry }

include 𝓕
def Cech_Cohomology_Group_nth (n : ℕ) : Ab :=
limits.colim.obj $ (Cech_Cohomology_Group_wrt_cover_unordered_nth.refinement_functor 𝓕 r n) ⋙ AddCommGroup.ulift_functor.{u u+1}

end

end