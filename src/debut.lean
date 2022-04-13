import topology.category.Top
import topology.sheaves.sheaf
import sort'
import for_mathlib.lemmas
import data.nat.parity
import algebra.category.Group.limits

section

open category_theory Top Top.sheaf topological_space finset
open opposite

open_locale big_operators

variable (X : Top) 

structure oc :=
(ι : Type*)
[lo : linear_order ι] 
[wo : is_well_order ι ((≤) : ι → ι → Prop)]
(cover : ι → opens X)
(is_cover : supr cover = ⊤)

attribute [instance] oc.lo oc.wo
attribute [simp] oc.is_cover

variable {X}
variable (𝓕 : sheaf Ab X)
variable (𝔘 : oc X)

local notation `ι ` := 𝔘.ι
local notation `𝓕.obj` := 𝓕.1.obj
local notation `𝓕.map` := 𝓕.1.map

@[ext] structure simplex (n : ℕ) extends finset ι :=
(card_eq : to_finset.card = n.succ)

attribute [simp] simplex.card_eq

namespace simplex

variables {𝔘} {n : ℕ} (hn : 0 < n)

def ignore (σ : simplex 𝔘 n) (m : fin n.succ) : simplex 𝔘 n.pred :=
{ to_finset := σ.1.erase_nth σ.2 m,
  card_eq := (nat.succ_pred_eq_of_pos hn).symm ▸ σ.1.erase_nth_card _ m }

def ignore₂ (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) : simplex 𝔘 n.pred :=
(σ.ignore (nat.zero_lt_succ _) m).ignore hn m'

lemma ignore_subset (σ : simplex 𝔘 n) (m : fin n.succ) :
  (σ.ignore hn m).to_finset ⊆ σ.to_finset := λ x hx,
begin
  change x ∈ finset.erase _ _ at hx,
  rw finset.mem_erase at hx,
  exact hx.2,
end

lemma ignore₂_subset (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
  (σ.ignore₂ hn m m').to_finset ⊆ σ.to_finset :=
subset.trans ((σ.ignore (nat.zero_lt_succ _) m).ignore_subset hn m') $ σ.ignore_subset _ _

lemma ignore₂_to_finset_case1 (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
  (hmm' : m'.1 < m.1) :
  (σ.ignore₂ hn m m').to_finset =
  σ.to_finset \ 
  { σ.1.order_emb_of_fin σ.2 m, 
    σ.1.order_emb_of_fin σ.2 ⟨m'.1, lt_trans m'.2 (lt_add_one n.succ)⟩ } :=
begin
  unfold ignore₂ ignore,
  dsimp,
  ext i,
  split,
  { intros hi,
    erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m] at hi,
    unfold erase_order_emb_of_fin' at hi,
    simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth] at hi,
    rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
    tauto },
  { intros hi,
    erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m, mem_erase_nth],
    rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
    refine ⟨_, hi.2.1, hi.1⟩,
    convert hi.2.2,
    unfold erase_order_emb_of_fin',
    simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_pos hmm', mem_erase_nth],
    refl, }
end

lemma ignore₂_to_finset_case2 (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
  (hmm' : m.1 ≤ m'.1) :
  (σ.ignore₂ hn m m').to_finset =
  σ.to_finset \ 
  { σ.to_finset.order_emb_of_fin σ.2 m, 
    σ.to_finset.order_emb_of_fin σ.2 ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ } :=
begin
  have ineq : ¬ m'.1 < m.1,
  { rwa not_lt },
  unfold ignore₂ ignore,
  dsimp,
  ext i,
  split,
  { intros hi,
    erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m] at hi,
    unfold erase_order_emb_of_fin' at hi,
    simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth] at hi,
    rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib],
    tauto },
  { intros hi,
    erw [mem_erase_nth, σ.to_finset.erase_order_emb_of_fin'_eq σ.2 m, mem_erase_nth],
    rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi,
    refine ⟨_, hi.2.1, hi.1⟩,
    convert hi.2.2,
    unfold erase_order_emb_of_fin',
    simp only [rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk, ne.def, if_neg ineq, mem_erase_nth],
    refl, }
end

lemma ignore₂_eq_ignore₂.aux (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
  (hmm' : m.1 ≤ m'.1) :
  (σ.ignore₂ hn m m').to_finset = 
  (σ.ignore₂ hn ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ ⟨m.1, by linarith [m'.2]⟩).to_finset :=
begin
  rw [ignore₂_to_finset_case2 _ _ _ _ hmm', ignore₂_to_finset_case1],
  { ext i,
    split;
    { intros hi,
      rw [mem_sdiff, mem_insert, mem_singleton, not_or_distrib] at hi ⊢,
      tauto, } },
  { dsimp only,
    exact lt_of_le_of_lt hmm' (lt_add_one _), },
end

lemma ignore₂_eq_ignore₂ (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
  (hmm' : m.1 ≤ m'.1) :
  (σ.ignore₂ hn m m') = 
  (σ.ignore₂ hn ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ ⟨m.1, by linarith [m'.2]⟩) :=
by rw [simplex.ext_iff, ignore₂_eq_ignore₂.aux]

end simplex

def face {n : ℕ} (σ : simplex 𝔘 n) : opens X :=
infi (λ i : σ.to_finset, 𝔘.cover i.1)

def der {n : ℕ} (hn : 0 < n) (σ : simplex 𝔘 n) (m : fin n.succ) :
  face 𝔘 σ ⟶ face 𝔘 (σ.ignore hn m) := hom_of_le $ λ p hp, 
begin
  rw [opens.mem_coe] at hp ⊢,
  rcases hp with ⟨S, ⟨oS, hS⟩, p_mem⟩,
  refine ⟨S, ⟨oS, λ x x_mem, _⟩, p_mem⟩,
  specialize hS x_mem,
  simp only [subtype.val_eq_coe, set.Inf_eq_sInter, set.sInter_image, set.mem_range, 
    set.Inter_exists, set.Inter_Inter_eq', set.mem_Inter, opens.mem_coe] at hS ⊢,
  exact λ i, hS ⟨i.1, σ.ignore_subset hn m i.2⟩,
end

def dder {n : ℕ} (hn : 0 < n) (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ) :
  face 𝔘 σ ⟶ face 𝔘 (σ.ignore₂ hn m m') :=
der 𝔘 (nat.zero_lt_succ _) σ m ≫ der 𝔘 _ (σ.ignore _ m) m'

lemma dder_eq  {n : ℕ} (hn : 0 < n) (σ : simplex 𝔘 n.succ) (m : fin n.succ.succ) (m' : fin n.succ)
  (hmm' : m.1 ≤ m'.1) :
  dder 𝔘 hn σ m m' ≫ eq_to_hom (congr_arg _ (simplex.ignore₂_eq_ignore₂ hn σ m m' hmm')) = dder 𝔘 hn σ ⟨m'.1.succ, nat.succ_lt_succ m'.2⟩ ⟨m.1, by linarith [m'.2]⟩ :=
begin
  refl,
end

namespace C

def carrier (n : ℕ) : Type* :=
Π σ : simplex 𝔘 n, 𝓕.obj (op $ face 𝔘 σ)

instance (n : ℕ) : has_zero (carrier 𝓕 𝔘 n) :=
{ zero := λ σ, 0 }

instance (n : ℕ) : has_add (carrier 𝓕 𝔘 n) :=
{ add := λ f g σ, f σ + g σ }

lemma add_assoc' {n : ℕ} (f g h : carrier 𝓕 𝔘 n) : f + g + h = f + (g + h) := 
funext $ λ σ, add_assoc _ _ _

lemma zero_add' {n : ℕ} (f : carrier 𝓕 𝔘 n) : 0 + f = f :=
funext $ λ σ, zero_add _

lemma add_zero' {n : ℕ} (f : carrier 𝓕 𝔘 n) : f + 0 = f :=
funext $ λ σ, add_zero _

@[simp] lemma zero_apply {n : ℕ} (σ : simplex 𝔘 n) :
  (0 : carrier 𝓕 𝔘 n) σ = 0 := 
pi.zero_apply _

@[simp] lemma add_apply {n : ℕ} (x y : carrier 𝓕 𝔘 n) (σ : simplex 𝔘 n) :
  (x + y) σ = x σ + y σ := 
pi.add_apply _ _ _

section smul

variables (α : Type*) [Π U : (opens X)ᵒᵖ, has_scalar α (𝓕.obj U)]

instance (n : ℕ) : has_scalar α (carrier 𝓕 𝔘 n) :=
{ smul := λ a f σ, a • f σ }

end smul

instance (n : ℕ) : add_monoid (carrier 𝓕 𝔘 n) :=
{ add := (+),
  add_assoc := add_assoc' _ _,
  zero := 0,
  zero_add := zero_add' _ _,
  add_zero := add_zero' _ _,
  nsmul := (•),
  nsmul_zero' := λ f, funext $ λ σ, by simp,
  nsmul_succ' := λ m f, funext $ λ σ, by simp [nat.succ_eq_add_one, add_nsmul, one_nsmul, add_comm] }

instance (n : ℕ) : has_neg (carrier 𝓕 𝔘 n) :=
{ neg := λ f σ, - f σ }

instance (n : ℕ) : add_comm_group (carrier 𝓕 𝔘 n) :=
{ neg := has_neg.neg,
  add_left_neg := λ f, funext $ λ σ, by simp,
  add_comm := λ f g, funext $ λ σ, by simp [add_comm],
  ..(_ : add_monoid (carrier 𝓕 𝔘 n))}

end C

section

variable {X}
def C (n : ℕ) : Ab :=
⟨C.carrier 𝓕 𝔘 n⟩


lemma C.finset_sum_apply (n : ℕ) {α : Type*} [decidable_eq α] 
  (f : α → C 𝓕 𝔘 n) (s : finset α) (σ : simplex 𝔘 n) :
  (∑ i in s, f i) σ = ∑ i in s, f i σ :=
begin
  induction s using finset.induction_on with a s ha ih,
  { simp, },
  { rw [finset.sum_insert ha, finset.sum_insert ha, pi.add_apply, ih] },
end 

namespace d_pos

variables {n : ℕ} (hn : 0 < n) 

def to_fun.component (m : fin n.succ) : C 𝓕 𝔘 n.pred → C 𝓕 𝔘 n := λ f σ,
ite (even m.1) id has_neg.neg (𝓕.map (der 𝔘 hn σ m).op (f (σ.ignore hn m)))

def to_fun : C 𝓕 𝔘 n.pred → C 𝓕 𝔘 n := λ f,
∑ i in (range n.succ).attach, d_pos.to_fun.component 𝓕 𝔘 hn ⟨i.1, mem_range.mp i.2⟩ f

def map_zero' : to_fun 𝓕 𝔘 hn 0 = 0 := finset.sum_eq_zero $ λ ⟨m, hm⟩ h,
begin
  rw mem_range at hm,
  unfold to_fun.component,
  split_ifs;
  ext σ;
  simp,
end

def map_add' (x y : C 𝓕 𝔘 n.pred) :
  to_fun 𝓕 𝔘 hn (x + y) = to_fun 𝓕 𝔘 hn x + to_fun 𝓕 𝔘 hn y :=
begin
  unfold to_fun,
  rw ← sum_add_distrib,
  apply sum_congr rfl,
  rintros m hm,
  unfold to_fun.component,
  split_ifs,
  { ext σ, simp only [C.add_apply, map_add, id], },
  { ext σ, 
    change - _ = - _ + - _,
    rw [neg_eq_iff_neg_eq, neg_add, neg_neg, neg_neg, C.add_apply, map_add] },
end

end d_pos

variables {𝓕 𝔘}
def d_pos {n : ℕ} (hn : 0 < n) : C 𝓕 𝔘 n.pred ⟶ C 𝓕 𝔘 n :=
{ to_fun := d_pos.to_fun 𝓕 𝔘 hn,
  map_zero' := d_pos.map_zero' _ _ _,
  map_add' := d_pos.map_add' _ _ _ }

lemma d_pos.def {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) (σ : simplex 𝔘 n) :
  d_pos hn f σ = 
  ∑ i in (range n.succ).attach, 
    ite (even i.1) id has_neg.neg 
      (𝓕.map (der 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩).op (f (σ.ignore hn ⟨i.1, mem_range.mp i.2⟩))) := 
begin
  unfold d_pos d_pos.to_fun,
  rw [add_monoid_hom.coe_mk, C.finset_sum_apply],
  refine finset.sum_congr rfl (λ m hm, _),
  refl,
end

abbreviation dd_pos {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) : C 𝓕 𝔘 n.succ := d_pos (nat.zero_lt_succ _) (d_pos hn f)

section lemmas

variables {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) (σ : simplex 𝔘 n.succ)

lemma dd_pos.eq1 :
  dd_pos hn f σ = 
  d_pos (nat.zero_lt_succ _) (d_pos hn f) σ := rfl

lemma dd_pos.eq2 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (ite (even i.1) id has_neg.neg) 
      (𝓕.map (der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩).op 
        ((d_pos hn f) (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩))) := 
by rw [dd_pos.eq1, d_pos.def]

lemma dd_pos.eq3 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg
      (𝓕.map (der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩).op 
        (∑ j in (range n.succ).attach, 
          ite (even j.1) id has_neg.neg
            (𝓕.map (der 𝔘 hn (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩) ⟨j.1, mem_range.mp j.2⟩).op 
              (f ((σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩).ignore hn ⟨j.1, mem_range.mp j.2⟩))))) := 
begin
  rw dd_pos.eq2,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  congr' 1,
  rw d_pos.def
end

lemma dd_pos.eq4 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg 
      (∑ j in (range n.succ).attach,
        𝓕.map (der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩).op
        (ite (even j.1) id has_neg.neg
          (𝓕.map (der 𝔘 hn (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩) ⟨j.1, mem_range.mp j.2⟩).op 
            (f ((σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩).ignore hn ⟨j.1, mem_range.mp j.2⟩))))) := 
begin
  rw dd_pos.eq3,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  rw add_monoid_hom.map_sum,
end

lemma dd_pos.eq5 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg 
      (∑ j in (range n.succ).attach,
        ite (even j.1) id has_neg.neg
          (𝓕.map (der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩).op
            (𝓕.map (der 𝔘 hn (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩) ⟨j.1, mem_range.mp j.2⟩).op 
              (f ((σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩).ignore hn ⟨j.1, mem_range.mp j.2⟩))))) := 
begin
  rw dd_pos.eq4,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  apply sum_congr rfl (λ m' hm', _),
  by_cases e' : even m'.1,
  { rw [if_pos e', id, if_pos e', id] },
  { rw [if_neg e', if_neg e', map_neg] },
end

lemma dd_pos.eq6₀ :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg 
      (∑ j in (range n.succ).attach,
        ite (even j.1) id has_neg.neg
          (𝓕.map ((der 𝔘 hn (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩) ⟨j.1, mem_range.mp j.2⟩).op ≫ (der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩).op)
            (f ((σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩).ignore hn ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq5,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  apply sum_congr rfl (λ m' hm', _),
  apply congr_arg,
  rw category_theory.functor.map_comp,
  refl,
end

lemma dd_pos.eq6₁ :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg 
      (∑ j in (range n.succ).attach,
        ite (even j.1) id has_neg.neg
          (𝓕.map ((der 𝔘 (nat.zero_lt_succ _) σ ⟨i.1, mem_range.mp i.2⟩) ≫ (der 𝔘 hn (σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩) ⟨j.1, mem_range.mp j.2⟩)).op
            (f ((σ.ignore (nat.zero_lt_succ _) ⟨i.1, mem_range.mp i.2⟩).ignore hn ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq6₀,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  apply sum_congr rfl (λ m' hm', _),
  congr,
end

lemma dd_pos.eq6₂ :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ite (even i.1) id has_neg.neg 
      (∑ j in (range n.succ).attach,
        ite (even j.1) id has_neg.neg
          (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq6₁,
  apply sum_congr rfl (λ m hm, _),
  apply congr_arg,
  apply sum_congr rfl (λ m' hm', _),
  apply congr_arg,
  unfold dder simplex.ignore₂,
  refl,
end

lemma dd_pos.eq7 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ∑ j in (range n.succ).attach,
      ite (even i.1) id has_neg.neg 
        (ite (even j.1) id has_neg.neg
          (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq6₂,
  apply sum_congr rfl (λ m hm, _),
  by_cases e : even m.1,
  { rw [if_pos e, id],
    simp_rw [id], },
  { rw [if_neg e, neg_sum], },
end

lemma dd_pos.eq8 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    ∑ j in (range n.succ).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩))) := 
begin
  rw dd_pos.eq7,
  apply sum_congr rfl (λ m hm, _),
  apply sum_congr rfl (λ m' hm', _),
  by_cases e : even m.1;
  by_cases e' : even m'.1,
  { rw [if_pos e, id, if_pos e', id, if_pos (even.add_even e e'), id] },
  { rw [if_pos e, id, if_neg e', if_neg],
    contrapose! e',
    convert nat.even.sub_even e' e,
    rw [add_comm, nat.add_sub_cancel], },
  { rw [if_neg e, if_pos e', id, if_neg],
    contrapose! e,
    convert nat.even.sub_even e e',
    rw nat.add_sub_cancel },
  { rw [if_neg e, if_neg e', neg_neg, if_pos, id],
    rw [nat.even_add', nat.odd_iff_not_even, nat.odd_iff_not_even],
    exact ⟨λ _, e', λ _, e⟩, },
end

lemma dd_pos.eq9 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in (range n.succ).attach.filter (λ n, i.1 ≤ n.1),
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩))) +
    ∑ j in (range n.succ).attach.filter (λ n, n.1 < i.1),
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq8,
  apply sum_congr rfl (λ i hi, _),
  have set_eq : (range n.succ).attach =
    (range n.succ).attach.filter (λ n, i.1 ≤ n.1) ∪ (range n.succ).attach.filter (λ n, n.1 < i.1),
  { have := filter_union_filter_neg_eq (λ n : (range n.succ), i.1 ≤ n.1) (range n.succ).attach,
    conv_lhs { rw ← this },
    congr' 2,
    ext,
    dsimp only,
    rw not_le },
  conv_lhs { rw [set_eq] },
  rw sum_union,
  rintros ⟨k, hk⟩ h,
  simp only [inf_eq_inter, mem_inter, mem_filter, mem_attach, subtype.coe_mk, true_and] at h,
  linarith,
end

lemma dd_pos.eq10 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((range n.succ).filter (λ n, i.1 ≤ n)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩))) +
    ∑ j in (range n.succ).attach.filter (λ n, n.1 < i.1),
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp j.2⟩)))) := 
begin
  rw dd_pos.eq9,
  apply sum_congr rfl (λ i hi, _),
  congr' 1,
  apply sum_bij',
  work_on_goal 4 { intros a ha, refine ⟨a.1, mem_filter.mpr ⟨a.2, (mem_filter.mp ha).2⟩⟩ },
  work_on_goal 5 { intros a ha, refine ⟨a.1, (mem_filter.mp a.2).1⟩ },
  { intros a ha, rw mem_filter at ha, },
  { intros a ha, rw subtype.ext_iff_val, },
  { intros a ha, rw subtype.ext_iff_val, },
  { intros a ha, simp only [mem_attach], },
  { intros a ha, 
    simp only [mem_filter, mem_attach, subtype.coe_mk, true_and],
    exact (mem_filter.mp a.2).2, }
end

lemma dd_pos.eq11 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((range n.succ).filter (λ n, i.1 ≤ n)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩))) +
    ∑ j in ((range n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩)))) := 
begin
  rw dd_pos.eq10,
  apply sum_congr rfl (λ i hi, _),
  congr' 1,
  apply sum_bij',
  work_on_goal 4 { intros a ha, refine ⟨a.1, mem_filter.mpr ⟨a.2, (mem_filter.mp ha).2⟩⟩ },
  work_on_goal 5 { intros a ha, refine ⟨a.1, (mem_filter.mp a.2).1⟩ },
  { intros a ha, rw mem_filter at ha, },
  { intros a ha, rw subtype.ext_iff_val, },
  { intros a ha, rw subtype.ext_iff_val, },
  { intros a ha, simp only [mem_attach], },
  { intros a ha, 
    simp only [mem_filter, mem_attach, subtype.coe_mk, true_and],
    exact (mem_filter.mp a.2).2, }
end

lemma 𝓕_map_congr (σ1 σ2 : simplex 𝔘 n.pred) (h : σ1 = σ2) (f : C 𝓕 𝔘 n.pred)
  (i1 : face 𝔘 σ ⟶ face 𝔘 σ1) (i2 : face 𝔘 σ ⟶ face 𝔘 σ2) :
  𝓕.map i1.op (f σ1) = 𝓕.map i2.op (f σ2) :=
begin
  subst h,
  congr,
end

lemma dd_pos.eq12 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((range n.succ).filter (λ n, i.1 ≤ n)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1.succ, nat.succ_lt_succ (mem_range.mp (mem_filter.mp j.2).1)⟩ ⟨i.1, by { have h1 := (mem_filter.mp j.2).2, have h2 := mem_range.mp (mem_filter.mp j.2).1, linarith }⟩).op
            (f (σ.ignore₂ hn ⟨j.1.succ, nat.succ_lt_succ (mem_range.mp (mem_filter.mp j.2).1)⟩ ⟨i.1, by { have h1 := (mem_filter.mp j.2).2, have h2 := mem_range.mp (mem_filter.mp j.2).1, linarith }⟩))) +
    ∑ j in ((range n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩)))) := 
begin
  rw dd_pos.eq11,
  apply sum_congr rfl (λ i hi, _),
  apply congr_arg2 (+),
  { apply sum_congr rfl (λ j hj, _),
    by_cases e : even (i.val + j.val),
    { rw [if_pos e, id, id],
      apply 𝓕_map_congr,
      apply simplex.ignore₂_eq_ignore₂ },
    { rw [if_neg e],
      apply congr_arg has_neg.neg,
      apply 𝓕_map_congr,
      apply simplex.ignore₂_eq_ignore₂ } },
  { refl },
end

lemma dd_pos.eq13 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((Ico 1 n.succ.succ).filter (λ n, i.1 ≤ n-1)).attach,
      ite (even (i.1 + j.1 - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩ ⟨i.1, lt_of_le_of_lt ((mem_filter.mp j.2).2) begin
          have := (mem_Ico.mp (mem_filter.mp j.2).1).2,
          refine nat.pred_lt_pred _ this,
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          rw r at this,
          linarith only [this],
        end⟩).op
            (f (σ.ignore₂ hn ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩ ⟨i.1, lt_of_le_of_lt ((mem_filter.mp j.2).2) begin
          have := (mem_Ico.mp (mem_filter.mp j.2).1).2,
          refine nat.pred_lt_pred _ this,
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          rw r at this,
          linarith only [this],
        end⟩))) +
    ∑ j in ((range n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩)))) := 
begin
  rw dd_pos.eq12,
  apply sum_congr rfl (λ i hi, _),
  apply congr_arg2 (+),
  { apply sum_bij',
    work_on_goal 4 
    { rintros a ha,
      refine ⟨a.1 + 1, _⟩,
      rw mem_filter,
      refine ⟨_, (mem_filter.mp a.2).2⟩,
      rw mem_Ico,
      split,
      { linarith },
      { rcases mem_filter.mp a.2 with ⟨h1, h2⟩,
        rw mem_range at h1,
        apply nat.succ_lt_succ,
        exact h1 }, },
    work_on_goal 5
    { rintros a ha,
      refine ⟨a.1 - 1, _⟩,
      rw mem_filter,
      refine ⟨_, (mem_filter.mp a.2).2⟩,
      rw mem_range,
      refine nat.pred_lt_pred _ (mem_Ico.mp (mem_filter.mp a.2).1).2,
      have := (mem_Ico.mp (mem_filter.mp a.2).1).1,
      intro r,
      rw r at this,
      linarith only [this] },
    { intros a ha,
      dsimp only,
      have eq1 : i.val + (a.val + 1) - 1 = i.val + a.val,
      { rw [nat.add_sub_assoc, nat.add_sub_cancel],
        linarith },
      rw eq1, },
    { intros a ha,
      rw subtype.ext_iff_val,
      dsimp only,
      rw nat.add_sub_cancel, },
    { intros a ha,
      rw subtype.ext_iff_val,
      dsimp only,
      rw nat.sub_add_cancel,
      exact (mem_Ico.mp (mem_filter.mp a.2).1).1, },
    { intros a ha,
      dsimp only,
      apply mem_attach, },
    { intros a ha,
      dsimp only,
      apply mem_attach, }, },
  { refl, }
end

lemma dd_pos.eq14 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((Ico 1 n.succ).filter (λ n, i.1 ≤ n-1)).attach,
      ite (even (i.1 + j.1 - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩).op
            (f (σ.ignore₂ hn ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩))) +
    (dite (i.1 ≤ n.succ - 1)
      (λ le1, (ite (even (i.1 + n.succ - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩).op
            (f (σ.ignore₂ hn ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩))))) (λ r, 0)) +
    ∑ j in ((range n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, mem_range.mp (mem_filter.mp j.2).1⟩)))) := 
begin
  rw dd_pos.eq13,
  apply finset.sum_congr rfl (λ i hi, _),
  apply congr_arg2 (+),
  { have set_eq : Ico 1 n.succ.succ = insert n.succ (Ico 1 n.succ),
    { rw [nat.Ico_succ_right_eq_insert_Ico], 
      apply nat.succ_le_succ,
      exact nat.zero_le _, },
    
    sorry },
  { refl, }
end

lemma dd_pos.eq15 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((Ico 1 n.succ).filter (λ n, i.1 ≤ n-1)).attach,
      ite (even (i.1 + j.1 - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩).op
            (f (σ.ignore₂ hn ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩))) +
    (dite (i.1 ≤ n.succ - 1)
      (λ le1, (ite (even (i.1 + n.succ - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩).op
            (f (σ.ignore₂ hn ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩))))) (λ r, 0)) +
    ((dite (0 < i.1)
      (λ ineq1, ite (even (i.1 + 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩)))) (λ _, 0)) +
      ∑ j in ((Ico 1 n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩))))) := 
begin
  rw dd_pos.eq14,
  apply finset.sum_congr rfl (λ i hi, _),
  apply congr_arg2 (+),
  { refl, },
  { sorry },
end

lemma dd_pos.eq16 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (∑ j in ((Ico 1 n.succ).filter (λ n, i.1 ≤ n-1)).attach,
      ite (even (i.1 + j.1 - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩).op
            (f (σ.ignore₂ hn ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩))) +
      ∑ j in ((Ico 1 n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩))) +
    (dite (i.1 ≤ n.succ - 1)
      (λ le1, (ite (even (i.1 + n.succ - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩).op
            (f (σ.ignore₂ hn ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩))))) (λ r, 0)) +
    ((dite (0 < i.1)
      (λ ineq1, ite (even (i.1 + 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩)))) (λ _, 0)))) := 
begin
  rw dd_pos.eq15,
  apply finset.sum_congr rfl (λ i hi, _),
  rw show ∀ a b c d : 𝓕.val.obj (op (face 𝔘 σ)), (a + b) + (c + d) = (a + d) + b + c, from λ _ _ _ _, by abel,
end

lemma dd_pos.eq17 :
  dd_pos hn f σ =
  ∑ i in (range n.succ.succ).attach,
    (-∑ j in ((Ico 1 n.succ).filter (λ n, i.1 ≤ n-1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩).op
            (f (σ.ignore₂ hn ⟨j.1, lt_trans (mem_Ico.mp (mem_filter.mp j.2).1).2 (lt_add_one _)⟩ ⟨i.1, begin
          refine lt_of_le_of_lt (mem_filter.mp j.2).2 _,
          refine lt_trans (nat.pred_lt_pred _ ((mem_Ico.mp (mem_filter.mp j.2).1).2)) (lt_add_one _),
          have := (mem_Ico.mp (mem_filter.mp j.2).1).1,
          intro r,
          change j.1 = 0 at r,
          rw r at this,
          linarith only [this],
        end⟩))) +
      ∑ j in ((Ico 1 n.succ).filter (λ n, n < i.1)).attach,
      ite (even (i.1 + j.1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨j.1, (mem_Ico.mp (mem_filter.mp j.2).1).2⟩))) +
    (dite (i.1 ≤ n.succ - 1)
      (λ le1, (ite (even (i.1 + n.succ - 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩).op
            (f (σ.ignore₂ hn ⟨n.succ, lt_add_one _⟩ ⟨i.1, begin
          refine lt_of_le_of_lt le1 _,
          apply nat.pred_lt,
          exact nat.succ_ne_zero _,
        end⟩))))) (λ r, 0)) +
    ((dite (0 < i.1)
      (λ ineq1, ite (even (i.1 + 1)) id has_neg.neg 
        (𝓕.map (dder 𝔘 hn σ ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩).op
            (f (σ.ignore₂ hn ⟨i.1, mem_range.mp i.2⟩ ⟨0, nat.zero_lt_succ _⟩)))) (λ _, 0)))) := 
begin
  rw dd_pos.eq16,
  apply sum_congr rfl (λ i hi, _),
  apply congr_arg2 _ _ rfl,
  apply congr_arg2 _ _ rfl,
  apply congr_arg2 _ _ rfl,
  rw neg_sum,
  apply sum_congr rfl (λ j hj, _),
  by_cases e : even (i.val + j.val),
  { have o : ¬ even (i.val + j.val - 1),
    { sorry },
    rw [if_pos e, if_neg o],
    refl, },
  { have e' : even (i.1 + j.1 - 1),
    { sorry },
    rw [if_neg e, if_pos e', neg_neg, id] },
end

end lemmas

lemma dd {n : ℕ} (hn : 0 < n) (f : C 𝓕 𝔘 n.pred) : d_pos (nat.zero_lt_succ _) (d_pos hn f) = 0 :=
begin
  ext σ,
  rw [pi.zero_apply, d_pos.def],
  sorry
end

end

end
