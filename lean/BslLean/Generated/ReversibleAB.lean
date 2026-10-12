import BslLean.ReversibleTwoSpecies

/- Auto-generated from model.bsl by `bsl certify`. -/
/- Instance of the general schema BSL.ReversibleTwoSpecies.schema. -/
namespace BSL.Generated.«ReversibleAB»

open BSL.ReversibleTwoSpecies in
theorem steady_state_bounds (kf' kr' «A» «B» : ℝ)
    (hkf' : 1 ≤ kf' ∧ kf' ≤ 2)
    (hkr' : 3 ≤ kr' ∧ kr' ≤ 4)
    (hmass' : «A» + «B» = 10)
    (hss' : IsSteadyState kf' kr' «A» «B») :
    6 ≤ «A» ∧ «A» ≤ 8 ∧ 2 ≤ «B» ∧ «B» ≤ 4 := by
  obtain ⟨h1', h2', h3', h4'⟩ := schema 1 2 3 4 10 kf' kr' «A» «B»
    (by norm_num) (by norm_num) (by norm_num) hkf' hkr' hmass' hss'
  exact ⟨le_trans (le_of_eq (by norm_num)) h1', le_trans h2' (le_of_eq (by norm_num)),
    le_trans (le_of_eq (by norm_num)) h3', le_trans h4' (le_of_eq (by norm_num))⟩

end BSL.Generated.«ReversibleAB»
