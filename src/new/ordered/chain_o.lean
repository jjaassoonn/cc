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
-- Need correction
def Cech_complex_wrt_cover_ordered : cochain_complex Ab ℕ :=
{ X := λ n, C_o 𝓕 U n,
  d := λ i j, d_o_from_to 𝓕 U i j,
  shape' := λ i j h, begin
    ext f α,
    rw d_o_not_to_succ,
    rw [add_monoid_hom.zero_apply, pi.zero_apply],
    simp only [complex_shape.up_rel] at h,
    symmetry,
    exact h,
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
  d_o 𝓕 U m.1 ≫ eq_to_hom begin
    have := m.2,
    simp only [complex_shape.up_rel] at this,
    rw this,
    refl,
  end :=
begin
  change d_o_from_to 𝓕 U _ _ = _,
  rw [d_o_from_to, dif_pos],
  refl,
  exact m.2.symm,
end

noncomputable def Cech_Cohomology_Group_wrt_cover_ordered_nth (n : ℕ) : Ab :=
homological_complex.homology (Cech_complex_wrt_cover_ordered 𝓕 U) n

section zeroth

noncomputable def ex1 :
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
  kernel (d_o 𝓕 U 0) :=
eq_to_iso rfl

def ex3 :
  kernel (d_o 𝓕 U 0) ≅
  AddCommGroup.of (add_monoid_hom.ker (d_o 𝓕 U 0)) :=
AddCommGroup.kernel_iso_ker _

example :
  (Cech_Cohomology_Group_wrt_cover_ordered_nth 𝓕 U 0) ≅
  𝓕.1.obj (op ⊤) :=
sorry


end zeroth

end