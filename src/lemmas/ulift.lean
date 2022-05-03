import algebra.category.Group
import category_theory.limits.shapes.kernels

universes u v

namespace AddCommGroup

open ulift

variable (X : Ab.{u})

namespace ulift

instance : has_add (ulift.{v} X.α) :=
{ add := λ x y, ulift.rec_on x $ ulift.rec_on y $ λ a b, up (b + a) }

@[simp] lemma add_down (x y : ulift.{v} X.α) : down (x + y) = down x + down y := begin
  induction x,
  induction y,
  refl,
end

instance : has_zero (ulift.{v} X.α) :=
{ zero := up 0 }

@[simp] lemma zero_down : (0 : ulift.{v} X.α) .down = 0 := rfl

instance : add_zero_class (ulift.{v} X.α) :=
{ zero := 0,
  add := (+),
  zero_add := λ x, by induction x; ext; simp,
  add_zero := λ x, by induction x; ext; simp }

instance : add_semigroup (ulift.{v} X.α) :=
{ add := (+),
  add_assoc := λ a b c, by induction a; induction b; induction c; ext; simp [add_assoc] }

instance : add_monoid (ulift.{v} X.α) := 
{ ..(_ : add_zero_class (ulift.{v} X.α)),
  ..(_ : add_semigroup (ulift.{v} X.α)) }

instance : add_comm_monoid (ulift.{v} X.α) :=
{ add_comm := λ a b, by induction a; induction b; ext; simp [add_comm],
  ..(_ : add_monoid (ulift.{v} X.α)) }

instance : sub_neg_monoid (ulift.{v} X.α) :=
{ neg := λ x, ulift.rec_on x $ λ a, up (-a),
  nsmul := λ n x, ulift.rec_on x $ λ a, up (n • a),
  nsmul_zero' := λ x, by { induction x, dsimp only, ext, simp, },
  nsmul_succ' := λ n x, by { induction x, dsimp only, ext, simp [succ_nsmul], },
  zsmul := λ n x, ulift.rec_on x $ λ a, up (n • a),
  zsmul_zero' := λ x, by { induction x, dsimp only, ext, simp, },
  zsmul_succ' := λ n x, begin
    induction x,
    ext,
    dsimp only,
    simp [add_smul, add_comm],
  end,
  zsmul_neg' := λ n x, begin
    induction x,
    ext,
    dsimp only,
    simp only [zsmul_neg_succ_of_nat, int.coe_nat_succ, add_smul, one_nsmul, coe_nat_zsmul, one_zsmul],  
  end,
  ..(_ : add_monoid (ulift.{v} X.α)) }

@[simp] lemma neg_down (x : ulift.{v} X.α) : (-x).down = - x.down :=
begin
  induction x,
  dsimp,
  refl,
end

instance : add_group (ulift.{v} X.α) :=
{ add_left_neg := λ a, by induction a; ext; simp,
  ..(_ : sub_neg_monoid (ulift.{v} X.α))}

instance : add_comm_group (ulift.{v} X.α) := 
{ ..(_ : add_comm_monoid (ulift.{v} X.α)),
  ..(_ : add_group (ulift.{v} X.α))}

end ulift

def ulift (X : Ab.{u}) : Ab.{max u v} :=
{ α := ulift.{v} X.α,
  str := infer_instance }

def ulift_functor : Ab.{u} ⥤ Ab.{max u v} :=
{ obj := λ X, X.ulift,
  map := λ X Y f, 
  { to_fun := λ x, up $ f x.down,
    map_zero' := by ext; simp,
    map_add' := λ x y, by ext; simp },
  map_id' := λ X, by ext x; simp,
  map_comp' := λ X Y Z h g, by ext; simp }

lemma ulift_functor_map_down {X Y : Ab.{u}} (h : X ⟶ Y) (x : X.ulift) :
  (ulift_functor.map h x).down = h x.down := rfl

section

open category_theory.limits

def ulift_iso {X Y : Ab.{u}} (h : X ≅ Y) :
  ulift_functor.obj X ≅ ulift_functor.obj Y :=
{ hom := ulift_functor.map h.hom,
  inv := ulift_functor.map h.inv,
  hom_inv_id' := begin
    rw [← category_theory.functor.map_comp],
    simp only [category_theory.iso.hom_inv_id, category_theory.functor.map_id],
  end,
  inv_hom_id' := begin
    rw [← category_theory.functor.map_comp],
    simp only [category_theory.iso.inv_hom_id, category_theory.functor.map_id],
  end }

noncomputable def ulift_kernel_iso_kernel_ulift {X Y : Ab.{u}} (h : X ⟶ Y) :
  kernel (ulift_functor.map h) ≅ ulift_functor.obj (kernel h) :=
begin
  refine kernel_iso_ker _ ≪≫ _,
  refine _ ≪≫(ulift_iso (kernel_iso_ker h)).symm,
  refine { hom := _, inv := _, hom_inv_id' := _, inv_hom_id' := _ },
  { refine { to_fun := _, map_zero' := _, map_add' := _ },
    { intros x,
      refine up ⟨x.1.down, _⟩,
      have := x.2,
      rw add_monoid_hom.mem_ker at this ⊢,
      apply_fun ulift.down at this,
      rw ulift_functor_map_down at this,
      exact this, },
    { refl, },
    { intros x y, 
      apply_fun ulift.down,
      dsimp only,
      rw ulift.add_down,
      simp only [subtype.val_eq_coe, add_subgroup.coe_add, ulift.add_down, add_submonoid.mk_add_mk, subtype.mk_eq_mk],
      intros x y h,
      ext1,
      exact h, } },
    { refine { to_fun := _, map_zero' := _, map_add' := _ },
      { intros x,
        refine ⟨up x.down.1, _⟩,
        have := x.down.2,
        rw add_monoid_hom.mem_ker at this ⊢,
        ext,
        rw ulift_functor_map_down,
        exact this, },
      { refl },
      { intros x y,
        rw subtype.ext_iff_val,
        simp only [ulift.add_down],
        refl, }, },
    { ext1 x,
      simp only [subtype.val_eq_coe, add_subgroup.coe_mk, category_theory.comp_apply, add_monoid_hom.coe_mk, category_theory.id_apply],
      rw subtype.ext_iff_val,
      dsimp only,
      ext1,
      refl, },
    { ext1 x,
      simp only [subtype.val_eq_coe, category_theory.comp_apply, add_monoid_hom.coe_mk, add_subgroup.coe_mk, set_like.eta,
  category_theory.id_apply],
      ext1,
      refl, },
end

end

end AddCommGroup