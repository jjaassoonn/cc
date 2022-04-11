import algebra.hom.group
import algebra.big_operators

namespace finset

open_locale big_operators

variables {ι : Type*} (A: Type*) [comm_group A]

@[to_additive "neg_sum"] lemma inv_prod (a : ι → A) (s : finset ι) :
  (∏ i in s, a i)⁻¹ = ∏ i in s, (a i)⁻¹ :=
begin
  classical,
  induction s using finset.induction_on with i s hi ih,
  { simp only [finset.prod_empty, one_inv], },
  { rw [finset.prod_insert hi, mul_inv, ih, finset.prod_insert hi] },
end

end finset