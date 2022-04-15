import cech_d
import algebra.homology.homological_complex
import category_theory.opposites
import oc

section

open category_theory Top Top.presheaf category_theory.limits

universe u
variables {X : Top} (𝓕 : sheaf Ab X) (𝔘 : X.oc)

namespace d

def from_to (i j : ℕ) : C 𝓕 𝔘 i ⟶ C 𝓕 𝔘 j :=
dite (i + 1 = j) (λ h, begin subst h, exact d_pos (nat.zero_lt_succ _) end) (λ h, 0)

lemma to_succ (i : ℕ) :
  from_to 𝓕 𝔘 i i.succ = d_pos (nat.zero_lt_succ _) :=
dif_pos rfl

lemma not_succ (i j : ℕ) (h : i + 1 ≠ j) :
  from_to 𝓕 𝔘 i j = 0 :=
dif_neg h

end d

def  cech_chain : cochain_complex Ab ℕ :=
{ X := C 𝓕 𝔘,
  d := d.from_to 𝓕 𝔘,
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
    erw dd_pos.eq0 (nat.zero_lt_succ _) f,
    refl,
  end }

section

open topological_space opposite category_theory.opposite Top
open_locale big_operators

def simplex.refine {n : ℕ} {A B : X.oc} (h : A ⟶ B) (σ : simplex A n) : 
  simplex B n := 
{ to_finset := finset.image h.func σ.to_finset,
  card_eq := begin
    rw [← σ.2, finset.card_image_of_inj_on],
    apply function.injective.inj_on,
    exact h.is_inj,
  end }

lemma simplex.refine_self {n : ℕ} {A : oc X} (σ : simplex A n) :
  σ.refine (𝟙 A) = σ :=
begin
  ext i,
  split,
  { intros hi,
    unfold simplex.refine at hi,
    dsimp only at hi,
    change i ∈ finset.image id _ at hi,
    rw finset.mem_image at hi,
    rcases hi with ⟨a, ha, rfl⟩,
    exact ha },
  { intros hi,
    unfold simplex.refine,
    dsimp only,
    change i ∈ finset.image id _,
    rw finset.mem_image,
    refine ⟨i, hi, rfl⟩, },
end

lemma simplex.refine_nth  {n : ℕ} (hn : 0 < n) {A B : oc X} (h : A ⟶ B) (σ : simplex A n) (m : fin n.succ) :
  (σ.refine h).nth m = 
  h.func (σ.nth m) := 
begin
  change _ = (h.func ∘ σ.nth) m,
  symmetry,
  unfold simplex.nth,
  apply congr_fun,
  apply finset.order_emb_of_fin_unique (σ.refine h).2,
  { intros i,
    change h.func (σ.nth i) ∈ _,
    unfold simplex.refine,
    dsimp only,
    rw finset.mem_image,
    refine ⟨σ.nth i, _, rfl⟩,
    apply σ.nth_mem },
  { intros i j hh,
    change h.func (σ.nth i) < h.func (σ.nth j),
    apply h.strict_mono,
    unfold simplex.nth,
    apply (σ.to_finset.order_emb_of_fin σ.2).strict_mono,
    assumption }
end

lemma simplex.refine_comp {n : ℕ} {A B D : X.oc} (r1 : A ⟶ B) (r2 : B ⟶ D) (σ : simplex A n) :
  σ.refine (r1 ≫ r2) = (σ.refine r1).refine r2 :=
begin
  ext d,
  split;
  intros hd;
  unfold simplex.refine at hd ⊢;
  dsimp only at hd ⊢;
  rw finset.mem_image at hd ⊢,
  { rcases hd with ⟨a, ha, rfl⟩,
    refine ⟨r1.func a, _, rfl⟩,
    rw finset.mem_image,
    exact ⟨a, ha, rfl⟩, },
  { rcases hd with ⟨b, hb, rfl⟩, 
    rw finset.mem_image at hb,
    rcases hb with ⟨a, ha, rfl⟩,
    exact ⟨a, ha, rfl⟩, },
end

lemma simplex.refine_ignore {n : ℕ} (hn : 0 < n) {A B : oc X} (h : A ⟶ B) (σ : simplex A n) (m : fin n.succ) : 
  (σ.refine h).ignore hn m = (σ.ignore hn m).refine h := 
begin
  ext i,
  split,
  { rintros (hi : i ∈ simplex.ignore hn (simplex.refine h σ) m),
    rw simplex.mem_ignore at hi, 
    rcases hi with ⟨h1, h2⟩,
    change _ ∈ simplex.to_finset _ at h1,
    unfold simplex.refine at h1 ⊢,
    dsimp only at h1 ⊢,
    rw finset.mem_image at h1 ⊢,
    rcases h1 with ⟨a, ha, rfl⟩,
    refine ⟨a, _, rfl⟩,
    change a ∈ simplex.ignore hn σ m,
    rw simplex.mem_ignore,
    refine ⟨ha, _⟩,
    contrapose! h2,
    rw [simplex.refine_nth hn, h2] },
  { rintros hi,
    erw simplex.mem_ignore,
    change i ∈ simplex.to_finset _ ∧ _,
    unfold simplex.refine at hi,
    dsimp only at hi,
    rw finset.mem_image at hi,
    rcases hi with ⟨a, ha, rfl⟩,
    erw simplex.mem_ignore at ha,
    rcases ha with ⟨h1, h2⟩,
    refine ⟨_, _⟩,
    { change _ ∈ simplex.to_finset _,
      unfold simplex.refine,
      dsimp only,
      rw finset.mem_image,
      exact ⟨a, h1, rfl⟩, },
    { contrapose! h2,
      rw simplex.refine_nth hn at h2,
      exact h.is_inj h2, } },
end

lemma face.refine {n : ℕ} {A B : oc X} (h : A ⟶ B) (σ : simplex A n) :
  face A σ ≤ face B (σ.refine h) := 
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

def C.refine (n : ℕ) {A B : oc X} (h : A ⟶ B) :
  C 𝓕 B n ⟶ C 𝓕 A n :=
{ to_fun := λ f σ, 𝓕.1.map (hom_of_le $ face.refine h σ).op $ f (σ.refine h),
  map_zero' := begin
    ext σ,
    rw [C.zero_apply, map_zero, C.zero_apply],
  end,
  map_add' := λ f g, begin
    ext σ,
    rw [C.add_apply, map_add, C.add_apply],
  end }


lemma 𝓕_map_congr' {U V : opens X} (i1 i2 : U ⟶ V) (x y : 𝓕.1.obj (op V)) (h2 : x = y) :
  𝓕.1.map i1.op x = 𝓕.1.map i2.op y :=
have h : i1 = i2 := by ext,
by subst h; subst h2

lemma 𝓕_map_congr'' {n : ℕ} (A B : X.oc) (r : B ⟶ A) (σ : simplex B n) (σ1 σ2 : simplex A n.pred) (h : σ1 = σ2) (f : C 𝓕 A n.pred)
  (i1 : face B σ ⟶ face A σ1) (i2 : face B σ ⟶ face A σ2) :
  𝓕.1.map i1.op (f σ1) = 𝓕.1.map i2.op (f σ2) :=
begin
  subst h,
  congr,
end

lemma 𝓕_map_congr''' {n : ℕ} {A : X.oc} (f : C 𝓕 A n) 
  (σ1 σ2 : simplex A n) (h0 : σ1 = σ2)
  {U : opens X} (i1 : U ⟶ face A σ1) (i2 : U ⟶ face A σ2)  :
  𝓕.1.map i1.op (f σ1) = 𝓕.1.map i2.op (f σ2) := 
by { subst h0, apply 𝓕_map_congr', refl, }

lemma C.refine_comp (n : ℕ) {A B D : oc X} (r1 : A ⟶ B) (r2 : B ⟶ D) :
  C.refine 𝓕 n r2 ≫ C.refine 𝓕 n r1 = C.refine 𝓕 n (r1 ≫ r2) := 
begin
  ext1 f,
  change C.refine 𝓕 n r1 (C.refine 𝓕 n r2 f) = _,
  ext1 σ,
  change 𝓕.1.map _ (𝓕.1.map _ _) = 𝓕.1.map _ (f _),
  change (𝓕.1.map _ ≫ 𝓕.1.map _) _ = _,
  rw [← category_theory.functor.map_comp, ← category_theory.op_comp],
  apply 𝓕_map_congr''',
  symmetry,
  apply simplex.refine_comp,
end

def cech_chain.functor : X.ocᵒᵖ ⥤ cochain_complex Ab ℕ :=
{ obj := λ 𝔘, cech_chain 𝓕 𝔘.unop,
  map := λ A B r, 
  { f := λ i, C.refine 𝓕 i r.unop,
    comm' := λ i j h, begin
      simp only [complex_shape.up_rel] at h,
      subst h,
      ext f σ,
      change (d.from_to _ _ i (i + 1)) (C.refine 𝓕 _ r.unop f) σ = (C.refine 𝓕 _ r.unop) (d.from_to _ _ _ _ _) _,
      rw [d.to_succ, d_pos.def, d.to_succ],
      unfold C.refine,
      rw [add_monoid_hom.coe_mk, add_monoid_hom.coe_mk, d_pos.def, add_monoid_hom.map_sum],
      apply finset.sum_congr rfl (λ j hj, _),
      by_cases e : even j.1,
      { rw [if_pos e, id, if_pos e, id],
        change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map (der (unop A) _ (simplex.refine r.unop σ) ⟨j.val, _⟩).op ≫ _) _,
        rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
        apply 𝓕_map_congr'',
        exact r.unop,
        symmetry,
        apply simplex.refine_ignore, },
      { rw [if_neg e, if_neg e, map_neg],
        congr' 1,
        change (𝓕.val.map (hom_of_le _).op ≫ _) _ = (𝓕.val.map (der (unop A) _ (simplex.refine r.unop σ) ⟨j.val, _⟩).op ≫ _) _,
        rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp, ← category_theory.op_comp, ← category_theory.op_comp],
        apply 𝓕_map_congr'',
        exact r.unop,
        symmetry,
        apply simplex.refine_ignore, },
    end },
  map_id' := λ A, begin
    ext i f σ,
    simp only [unop_id, homological_complex.id_f, id_apply],
    change 𝓕.1.map _ _ = _,
    have eq1 : f σ = 𝓕.1.map (𝟙 _) (f σ),
    { rw category_theory.functor.map_id,
      refl, },
    conv_rhs { rw eq1 },
    symmetry,
    have := 𝓕_map_congr''' 𝓕 f σ (σ.refine (𝟙 _)) (σ.refine_self).symm,
    convert this _ _,
    exact 𝟙 _,
  end,
  map_comp' := λ A B D r1 r2, begin
    ext i f σ,
    simp only [unop_comp, homological_complex.comp_f, comp_apply],
    rw ← C.refine_comp,
    refl,
  end }

end

end