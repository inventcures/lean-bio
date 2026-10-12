import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Parameter-bounded steady state of a reversible two-species network

Reaction network:  `A ⇌ B`,  with  `A → B` at rate `kf * A`  and  `B → A` at
rate `kr * B` (mass action).

The model is stated here, in Lean, as an ODE vector field (`dA`, `dB`), and a
steady state is a zero of that field (`IsSteadyState`). Nothing about the
kinetics is assumed by hand: the bounds below are proved *from* the vector
field, so a mistake in the rate law could not slip past the kernel.

`schema` is the general theorem: for ANY box of rate constants with positive
lower bounds and any non-negative total, every mass-conserving steady state
lies in closed-form intervals. `bsl certify` emits each model's certificate as
a one-line application of `schema` to that model's numbers, so the trusted
Python shrinks to "recognize the network and copy five numbers".

This is a machine-checked proof of MODEL CONSISTENCY under explicitly stated,
bounded assumptions. It is not a claim about biological ground truth: the model
and the parameter ranges are hypotheses, and the theorem says only that the
conclusion follows from them.
-/

namespace BSL.ReversibleTwoSpecies

/-- Mass-action rate of change of `A` in `A ⇌ B`. -/
def dA (kf kr A B : ℝ) : ℝ := -(kf * A) + kr * B

/-- Mass-action rate of change of `B` in `A ⇌ B`. -/
def dB (kf kr A B : ℝ) : ℝ := kf * A - kr * B

/-- `(A, B)` is a steady state of `A ⇌ B` with rate constants `kf`, `kr`. -/
def IsSteadyState (kf kr A B : ℝ) : Prop := dA kf kr A B = 0 ∧ dB kf kr A B = 0

/-- `A + B` is conserved by the vector field, for every state. -/
theorem conservation (kf kr A B : ℝ) : dA kf kr A B + dB kf kr A B = 0 := by
  unfold dA dB; ring

/-- **General schema.** For every box `kf ∈ [kf_lo, kf_hi]`, `kr ∈ [kr_lo, kr_hi]`
with `0 < kf_lo`, `0 < kr_lo`, and every total `M ≥ 0`, any steady state with
`A + B = M` satisfies

  `M·kr_lo/(kf_hi+kr_lo) ≤ A ≤ M·kr_hi/(kf_lo+kr_hi)`, and `B = M - A`.

The steady state is `A* = M·kr/(kf+kr)`, increasing in `kr` and decreasing in
`kf`, so the extremes sit at opposite corners of the box. -/
theorem schema (kf_lo kf_hi kr_lo kr_hi M kf kr A B : ℝ)
    (hkf_pos : 0 < kf_lo) (hkr_pos : 0 < kr_lo) (hM : 0 ≤ M)
    (hkf : kf_lo ≤ kf ∧ kf ≤ kf_hi) (hkr : kr_lo ≤ kr ∧ kr ≤ kr_hi)
    (hmass : A + B = M) (hss : IsSteadyState kf kr A B) :
    M * kr_lo / (kf_hi + kr_lo) ≤ A ∧ A ≤ M * kr_hi / (kf_lo + kr_hi) ∧
    M - M * kr_hi / (kf_lo + kr_hi) ≤ B ∧ B ≤ M - M * kr_lo / (kf_hi + kr_lo) := by
  obtain ⟨hkf1, hkf2⟩ := hkf
  obtain ⟨hkr1, hkr2⟩ := hkr
  have hA0 : -(kf * A) + kr * B = 0 := hss.1
  -- Eliminate B via mass conservation: (kf + kr) * A = M * kr.
  have hsum : (kf + kr) * A = M * kr := by linear_combination -hA0 + kr * hmass
  have hk : 0 < kf + kr := by linarith
  have hd1 : 0 < kf_hi + kr_lo := by linarith
  have hd2 : 0 < kf_lo + kr_hi := by linarith
  -- Lower bound: (kf+kr)·(A·(kf_hi+kr_lo) − M·kr_lo) = M·(kr·kf_hi − kr_lo·kf) ≥ 0.
  have e1 : (kf + kr) * (A * (kf_hi + kr_lo) - M * kr_lo)
      = M * (kr * kf_hi - kr_lo * kf) := by linear_combination (kf_hi + kr_lo) * hsum
  have k1 : 0 ≤ kr * kf_hi - kr_lo * kf := by nlinarith
  have l1 : 0 ≤ A * (kf_hi + kr_lo) - M * kr_lo := by
    nlinarith [mul_nonneg hM k1]
  -- Upper bound: (kf+kr)·(M·kr_hi − A·(kf_lo+kr_hi)) = M·(kr_hi·kf − kr·kf_lo) ≥ 0.
  have e2 : (kf + kr) * (M * kr_hi - A * (kf_lo + kr_hi))
      = M * (kr_hi * kf - kr * kf_lo) := by linear_combination -(kf_lo + kr_hi) * hsum
  have k2 : 0 ≤ kr_hi * kf - kr * kf_lo := by nlinarith
  have l2 : 0 ≤ M * kr_hi - A * (kf_lo + kr_hi) := by
    nlinarith [mul_nonneg hM k2]
  have hlo : M * kr_lo / (kf_hi + kr_lo) ≤ A := by
    rw [div_le_iff₀ hd1]; linarith
  have hhi : A ≤ M * kr_hi / (kf_lo + kr_hi) := by
    rw [le_div_iff₀ hd2]; linarith
  refine ⟨hlo, hhi, ?_, ?_⟩ <;> linarith

/-- The flagship instance, stated with a hand-written steady-state equation.
For every pair of rate constants `k1 ∈ [1,2]`, `k2 ∈ [3,4]`, any
mass-conserving (`A + B = 10`) steady state (`k1 * A = k2 * B`) of the reversible
network `A ⇌ B` satisfies `A ∈ [6,8]` and `B ∈ [2,4]`. -/
theorem steady_state_bounds
    (k1 k2 A B : ℝ)
    (hk1lo : 1 ≤ k1) (hk1hi : k1 ≤ 2)
    (hk2lo : 3 ≤ k2) (hk2hi : k2 ≤ 4)
    (hmass : A + B = 10)
    (hss : k1 * A = k2 * B) :
    6 ≤ A ∧ A ≤ 8 ∧ 2 ≤ B ∧ B ≤ 4 := by
  have hpos : 0 < k1 + k2 := by linarith
  -- Eliminate B via mass conservation: (k1 + k2) * A = 10 * k2.
  have hsum : (k1 + k2) * A = 10 * k2 := by linear_combination hss + k2 * hmass
  -- Lower/upper bounds on A follow by multiplying through by (k1 + k2) > 0.
  have hA6 : 6 ≤ A := by nlinarith [hsum, hpos, hk1hi, hk2lo]
  have hA8 : A ≤ 8 := by nlinarith [hsum, hpos, hk1lo, hk2hi]
  -- B bounds are then linear, via A + B = 10.
  refine ⟨hA6, hA8, ?_, ?_⟩ <;> linarith

/-- The hand-written steady-state equation of `steady_state_bounds` is exactly
what the vector field gives: `IsSteadyState ↔ kf * A = kr * B`. -/
theorem isSteadyState_iff (kf kr A B : ℝ) :
    IsSteadyState kf kr A B ↔ kf * A = kr * B := by
  unfold IsSteadyState dA dB
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith

end BSL.ReversibleTwoSpecies
