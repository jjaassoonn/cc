import data.finset

section examples

variables {ι : Type*} [linear_order ι] [is_well_order ι ((≤) : ι → ι → Prop)]

def sort' (σ : finset ι) : fin σ.card → σ := λ n, 
{ val := (finset.sort ((≤) : ι → ι → Prop) σ).nth_le n.1 $ (finset.length_sort (≤) : _ = σ.card).symm ▸ n.2,
  property := (finset.mem_sort (≤)).mp $ list.nth_le_mem _ _ _ }

lemma sort'_monotone (σ : finset ι) : monotone (sort' σ) := λ x y h, 
list.sorted.rel_nth_le_of_le (finset.sort_sorted ((≤) : ι → ι → Prop) σ) 
    (by { rw finset.length_sort, exact x.2 } : x.val < (finset.sort (≤) σ).length) 
    (by { rw finset.length_sort, exact y.2 } : y.val < (finset.sort (≤) σ).length) h

lemma sort'_strict_mono (σ : finset ι) : strict_mono (sort' σ) := λ x y h, 
list.sorted.rel_nth_le_of_lt (finset.sort_sorted_lt σ) _ _ h

lemma sort'_injective (σ : finset ι) : function.injective (sort' σ) :=
strict_mono.injective $ sort'_strict_mono _

end examples