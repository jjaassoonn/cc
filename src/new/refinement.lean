import algebra.category.Group.colimits
import lemmas.ulift
import new.unordered.d

section

open topological_space Top Top.sheaf
open category_theory
open opposite
open nat

open_locale big_operators

universe u
variables {X : Top.{u}} (𝓕 : sheaf Ab X) (U V : X.oc)
variable (n : ℕ)

section

variables {n U V} (r : U ⟶ V)

def vec.refine (α : fin n → U.ι) : fin n → V.ι :=
r.func ∘ α

lemma vec.refine_apply (α : fin n → U.ι) (m : fin n) :
  vec.refine r α m = r.func (α m) := rfl

lemma vec.refine_comp_apply {U V W : X.oc} (r : U ⟶ V) (r' : V ⟶ W)
  (α : fin n → U.ι) (m : fin n) :
  vec.refine (r ≫ r') α m = vec.refine r' (vec.refine r α) m := rfl

lemma vec.refine_le (α : fin n → U.ι) :
  face α ≤ face (vec.refine r α) :=
begin
  intros p hp,
  rw opens.mem_coe at hp ⊢,
  unfold face at hp ⊢,
  rw opens.fintype_infi at hp ⊢,
  intros i,
  specialize hp i,
  apply r.is_refinement,
  exact hp,
end

lemma vec.refine_ignore (α : fin (n + 1) → U.ι) (k : fin (n + 1)) :
  vec.refine r (ignore α k) = ignore (vec.refine r α) k :=
begin
  ext1 m,
  rw vec.refine_apply,
  rw ignore.apply_ite,
  rw ignore.apply_ite,
  split_ifs,
  rw vec.refine_apply,
  rw vec.refine_apply,
end

variables {𝓕}
def C.refine.to_fun (f : C 𝓕 V n) : C 𝓕 U n :=
λ α, 𝓕.1.map (hom_of_le (vec.refine_le r α)).op (f (vec.refine r α))

lemma C.refine.to_fun_apply (f : C 𝓕 V n) (α : fin n → U.ι) :
  C.refine.to_fun r f α = 𝓕.1.map (hom_of_le (vec.refine_le r α)).op (f (vec.refine r α)) := 
rfl

def C.refine : C 𝓕 V n ⟶ C 𝓕 U n :=
{ to_fun := λ f, C.refine.to_fun r f,
  map_zero' := begin
    ext α,
    rw C.refine.to_fun_apply,
    simp only [C_pre.zero_apply, map_zero],
  end,
  map_add' := λ f g, begin
    ext α,
    rw [C.refine.to_fun_apply, pi.add_apply, map_add],
    refl,
  end }

lemma C.refine_d_eq_d_refine :
  C.refine r ≫ d 𝓕 U n = d 𝓕 V n ≫ C.refine r :=
begin
  ext f α,
  rw [comp_apply, comp_apply],
  rw [dd_aux.d_def],
  rw [C.refine, C.refine, add_monoid_hom.coe_mk, add_monoid_hom.coe_mk, C.refine.to_fun_apply],
  simp_rw [C.refine.to_fun_apply],
  rw [dd_aux.d_def],
  rw add_monoid_hom.map_sum,
  rw finset.sum_congr rfl,
  intros i _,
  split_ifs,
  { rw [id, ← comp_apply, ← 𝓕.1.map_comp, ← comp_apply, ← 𝓕.1.map_comp],
    rw map_congr.vec_eq f (_ : vec.refine r (ignore α i) = ignore (vec.refine r α) i),
    rw [← comp_apply, ← 𝓕.1.map_comp],
    congr,
    rw vec.refine_ignore, },
  { rw [pi.neg_apply, pi.neg_apply],
    simp only [pi.neg_apply, add_monoid_hom.neg_apply, map_neg, neg_inj],
    rw [← comp_apply, ← comp_apply, ← 𝓕.1.map_comp, ← 𝓕.1.map_comp],
    rw map_congr.vec_eq f (_ : vec.refine r (ignore α i) = ignore (vec.refine r α) i),
    rw [← comp_apply, ← 𝓕.1.map_comp],
    congr,
    rw vec.refine_ignore, },
end

lemma C.refine_d_eq_d_refine' (f) :
  C.refine r (d 𝓕 V n f)  = d 𝓕 U n (C.refine r f) := 
begin
  rw ← comp_apply,
  rw ← C.refine_d_eq_d_refine,
  rw comp_apply,
end

lemma C.refine_eq_to_hom {m n : ℕ} (h0 : m + 1 = n) (h1 : C 𝓕 U (m + 1) = C 𝓕 U n) (h2 : C 𝓕 V (m + 1) = C 𝓕 V n) :
  (@C.refine X 𝓕 U V (m+1) r ≫ eq_to_hom h1) = eq_to_hom h2 ≫ @C.refine X 𝓕 U V n r :=
begin
  ext f α,
  rw [comp_apply, comp_apply, C.refine, add_monoid_hom.coe_mk,  C.refine, add_monoid_hom.coe_mk, C.refine.to_fun_apply],
  
  have : @eq_to_hom Ab _ _ _ h2 f (vec.refine r α) = 𝓕.1.map _ (f (vec.refine r (λ i, α ⟨i.1, h0 ▸ i.2⟩))),
  work_on_goal 3
  { refine quiver.hom.op _,
    refine eq_to_hom _,
    sorry },
  { sorry },
  rw this,
  have : (@eq_to_hom Ab _ _ _ h1 (C.refine.to_fun r f)) α = 𝓕.1.map _ (C.refine.to_fun r f (λ i, α ⟨i.1, h0 ▸ i.2⟩)),
  work_on_goal 3
  { refine quiver.hom.op _,
    refine eq_to_hom _,
    unfold face,
    ext,
    split,

    { intros hp,
      rw opens.mem_coe at hp ⊢,
      rw opens.fintype_infi at hp ⊢,
      intros i,
      specialize hp ⟨i.1, h0 ▸ i.2⟩,
      exact hp },
    { intros hp,
      rw opens.mem_coe at hp ⊢,
      rw opens.fintype_infi at hp ⊢,
      intros i,
      specialize hp ⟨i.1, h0.symm ▸ i.2⟩,
      convert hp,
      rw subtype.ext_iff_val, }, },
    
  { sorry },
  rw this,
  rw ← comp_apply,
  rw ← 𝓕.1.map_comp,
  rw C.refine.to_fun_apply,
  rw ← comp_apply,
  rw ← 𝓕.1.map_comp,
  congr,
end


def C.refine_functor : X.ocᵒᵖ ⥤ Ab :=
{ obj := λ U, C 𝓕 (unop U) n,
  map := λ U V r, C.refine r.unop,
  map_id' := λ U, begin
    ext f α,
    simp only [unop_id, id_apply],
    change C.refine.to_fun _ f α = _,
    rw C.refine.to_fun_apply,
    rw map_congr.vec_eq f (_ : α = vec.refine (𝟙 _) α),
    congr,
    ext m,
    rw vec.refine_apply,
    refl,
  end,
  map_comp' := λ U V W rUV rVW, begin
    ext f α,
    rw comp_apply,
    change C.refine.to_fun _ f α = _,
    rw C.refine.to_fun_apply,
    rw C.refine,
    simp only [add_monoid_hom.coe_mk],
    rw C.refine,
    simp only [add_monoid_hom.coe_mk],

    rw C.refine.to_fun_apply,
    rw C.refine.to_fun_apply,
    rw ← comp_apply,
    rw ← 𝓕.1.map_comp,
    rw map_congr.vec_eq f (_ : vec.refine (rUV ≫ rVW).unop α = vec.refine rUV.unop (vec.refine rVW.unop α)),
    rw ← comp_apply,
    rw ← 𝓕.1.map_comp,
    congr,
    refl,
  end }

include 𝓕 n
noncomputable example : Ab :=
begin
  have := limits.colim.obj (@C.refine_functor _ 𝓕 n  ⋙ AddCommGroup.ulift_functor.{u u+1}),
  exact this,
end

end

end