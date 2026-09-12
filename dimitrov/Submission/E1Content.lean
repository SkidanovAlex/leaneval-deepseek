import Mathlib
import Submission.Conjugates
import Submission.DirSet
import Submission.StarBounds
import Submission.PolyaCore
import Submission.ChebPower
import Submission.Dubinin
import Submission.Dictionary

/-!
# E1: the single deep crux -- statement, decomposition, elementary part

`Submission.AnalyticEngine.hankel_eventually_zero` (the only remaining
`sorry` of the whole tree) needs, via the E2b/E2c shell and `ChebPower`,
exactly the following statement (E1):

    e1_hedgehogBound :  house α < 2^(1/(4·|argSet α|))
        ⟹  HedgehogBound (conjugateValues α)

where `HedgehogBound S` (`Submission.PolyaCore`) asks for monic polynomials
of every degree bounded by `C·θⁿ` (θ < 1) on some ε-fattening `FatStar S ε`
of the hedgehog `star S = ⋃_{z∈S} ([0,z²] ∪ [0,z⁴])`.

## Decomposition (informal proof, Dimitrov arXiv:1912.12545 / Dubinin)

Let `S := conjugateValues α`, `H := house α`, `m := |argSet α|`,
`s := |dirSet S|` (distinct spike directions of the hedgehog).

1. **Spike geometry (VERIFIED).**  `star S` is a hedgehog with `s ≤ 2m`
   spikes (`Submission.DirSet.dirSet_card_le_two_phases`), and every spike
   endpoint `w ∈ spikeEndpoints S` has `‖w‖ ≤ H⁴`
   (`Submission.StarBounds.star_subset_closedBall_house`).
2. **Margin arithmetic (PROVED below).**  From `H < 2^(1/(4m))`, `0 < m`,
   `s ≤ 2m`, `1 ≤ H`: `H⁴ < 4^(1/s)`, hence `∀ w ∈ spikeEndpoints S:
   ‖w‖ < 4^(1/s)` (`spike_norm_lt_four_rpow_inv` below).
3. **Dubinin's hedgehog inequality (DEEP -- stated as
   `hedgehogBound_of_short_spikes`).**  A hedgehog with `s` spikes all of
   length `< 4^(1/s)` has Chebyshev constant `< 1` on a small fattening.
   (Equivalently `cap(star S) ≤ 4^(−1/s)·max ‖w‖ < 1` + capacity continuity
   + Fekete–Chebyshev duality.)  NOT in Mathlib; requires potential theory.
4. **Assembly.**  `e1_hedgehogBound` follows from 3 instantiated with
   `S := conjugateValues α` and the facts of 1–2.

This file proves the elementary part (1–2) and *states* the two remaining
ingredients (3–4) marked `sorry`.  Do NOT import this module until they are
proved.
-/

noncomputable section

open scoped Real Polynomial Topology

namespace Submission.E1Content

open Submission.Conjugates
open Submission.DirSet
open Submission.PolyaCore

variable {K : Type*} [Field K] [NumberField K]

/-- The phase count equals the number of distinct phases (image of the
conjugate set under `arg`). -/
lemma argSet_eq_image (α : K) : argSet α = (conjugateValues α).image Complex.arg := rfl

/-- The direction set of the hedgehog over the conjugates is nonempty. -/
lemma dirSet_conjugateValues_nonempty (α : K) : (dirSet (conjugateValues α)).Nonempty := by
  classical
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨(σ α ^ 2).arg, ?_⟩
  rw [dirSet, Finset.mem_image]
  refine ⟨(σ α) ^ 2, ?_, rfl⟩
  rw [spikeEndpoints, Finset.mem_union]
  left
  rw [Finset.mem_image]
  refine ⟨σ α, ?_, rfl⟩
  rw [conjugateValues, Finset.mem_image]
  exact ⟨σ, Finset.mem_univ σ, rfl⟩

/-- The number of distinct spike directions of the hedgehog over the
conjugates is at most twice the number of phases. -/
lemma dirSet_card_le_two_argSet (α : K) :
    (dirSet (conjugateValues α)).card ≤ 2 * (argSet α).card := by
  simpa [argSet_eq_image] using (dirSet_card_le_two_phases (conjugateValues α))

/-- Every spike endpoint of the hedgehog over the conjugates has norm at most
`(house α) ^ 4` (the endpoint lies on the star, which is inside the closed
ball of radius `house⁴`). -/
lemma spike_endpoint_norm_le_house (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    ∀ w ∈ spikeEndpoints (conjugateValues α),
      ‖w‖ ≤ (NumberField.house α) ^ 4 := by
  classical
  intro w hw
  have hstar : w ∈ Submission.XTransfer.star (conjugateValues α) := by
    rw [spikeEndpoints] at hw
    rcases (Finset.mem_union.mp hw) with h2 | h4
    · rcases Finset.mem_image.mp h2 with ⟨z, hz, rfl⟩
      change z ^ 2 ∈ Submission.XTransfer.star (conjugateValues α)
      refine ⟨z, hz, Or.inl ?_⟩
      rw [Submission.XTransfer.mem_segment_zero_iff]
      refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp
    · rcases Finset.mem_image.mp h4 with ⟨z, hz, rfl⟩
      change z ^ 4 ∈ Submission.XTransfer.star (conjugateValues α)
      refine ⟨z, hz, Or.inr ?_⟩
      rw [Submission.XTransfer.mem_segment_zero_iff]
      refine ⟨1, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp
  have hb := StarBounds.star_subset_closedBall_house α hα hα0
  have hwball : w ∈ Metric.closedBall (0 : ℂ) ((NumberField.house α) ^ 4) := hb hstar
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hwball
  exact hwball

/-- **Margin arithmetic.**  If `1 ≤ H < 2^(1/(4m))` and `0 < s ≤ 2m`, then
`H⁴ < 4^(1/s)`.  (This is the strict margin behind Dubinin's bound:
`cap ≤ 4^(−1/s)·H⁴ < 4^(−1/s)·4^(1/s) = 1`.) -/
lemma house_pow4_lt_four_rpow_inv (H : ℝ) (m s : ℕ) (hm : 0 < m) (hH1 : 1 ≤ H)
    (hH : H < (2 : ℝ) ^ (1 / (4 * (m : ℝ)))) (hs : 0 < s) (hsm : s ≤ 2 * m) :
    H ^ 4 < (4 : ℝ) ^ (1 / (s : ℝ)) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hHnonneg : 0 ≤ H := le_trans (by norm_num) hH1
  -- Step 1: H^4 < ((2^(1/(4m)))^4) = 2^(1/m)
  have hH4 : H ^ 4 < ((2 : ℝ) ^ (1 / (4 * (m : ℝ)))) ^ 4 := by
    exact pow_lt_pow_left₀ (n := 4) hH hHnonneg (by norm_num)
  have hstep1 : ((2 : ℝ) ^ (1 / (4 * (m : ℝ)))) ^ 4 = (2 : ℝ) ^ (1 / (m : ℝ)) := by
    have hA : ((2 : ℝ) ^ (1 / (4 * (m : ℝ)))) ^ 4 =
        (2 : ℝ) ^ ((1 / (4 * (m : ℝ))) * 4) := by
      exact (Real.rpow_mul_natCast h2 (1 / (4 * (m : ℝ))) 4).symm
    rw [hA]
    congr 1
    field_simp [hmR.ne']
  have h1 : H ^ 4 < (2 : ℝ) ^ (1 / (m : ℝ)) := by
    rwa [hstep1] at hH4
  -- Step 2: 2^(1/m) ≤ 4^(1/s)  (since 4^(1/s) = 2^(2/s) and 1/m ≤ 2/s)
  have hstep2 : (2 : ℝ) ^ (1 / (m : ℝ)) ≤ (4 : ℝ) ^ (1 / (s : ℝ)) := by
    have h4eq : (4 : ℝ) ^ (1 / (s : ℝ)) = (2 : ℝ) ^ (2 / (s : ℝ)) := by
      have h42 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h42]
      have hmul := Real.rpow_mul h2 (2 : ℝ) (1 / (s : ℝ))
      rw [← hmul]
      congr 1
      ring
    rw [h4eq]
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · rw [div_le_div_iff₀ hmR hsR]
      norm_num
      exact_mod_cast hsm
  exact lt_of_lt_of_le h1 hstep2

/-- Every spike endpoint of the hedgehog over the conjugates is strictly
shorter than `4^(1/s)` (`s := number of distinct directions`) whenever the
house is strictly below the phase bound. -/
lemma spike_norm_lt_four_rpow_inv (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hH : NumberField.house α < (2 : ℝ) ^ (1 / (4 * ((argSet α).card : ℝ)))) :
    ∀ w ∈ spikeEndpoints (conjugateValues α),
      ‖w‖ < (4 : ℝ) ^ (1 / ((dirSet (conjugateValues α)).card : ℝ)) := by
  classical
  let H : ℝ := NumberField.house α
  let m : ℕ := (argSet α).card
  let s : ℕ := (dirSet (conjugateValues α)).card
  have hm : 0 < m := by
    dsimp [m]
    refine Finset.card_pos.mpr ?_
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    refine ⟨(σ α).arg, ?_⟩
    simp [argSet, conjugateValues]
  have hs : 0 < s := by
    dsimp [s]
    exact Finset.card_pos.mpr (dirSet_conjugateValues_nonempty α)
  have hsm : s ≤ 2 * m := by
    dsimp [s, m]
    exact dirSet_card_le_two_argSet α
  have hH1 : 1 ≤ H := by
    dsimp [H]
    exact one_le_house_of_isIntegral_ne_zero hα hα0
  have hmargin : H ^ 4 < (4 : ℝ) ^ (1 / (s : ℝ)) := by
    dsimp [H, s] at hH ⊢
    exact house_pow4_lt_four_rpow_inv (NumberField.house α) m s hm hH1 hH hs hsm
  intro w hw
  have hle : ‖w‖ ≤ H ^ 4 := by
    dsimp [H]
    exact spike_endpoint_norm_le_house α hα hα0 w hw
  exact lt_of_le_of_lt hle (by simpa [s] using hmargin)

/-- **Dubinin's hedgehog inequality.**  If the hedgehog over `S` (nonempty,
all spike endpoints nonzero) has `s := |dirSet S|` spikes all strictly
shorter than `4^(1/s)`, then it is polynomially controllable on a
fattening (`HedgehogBound S`).  This is the potential-theoretic content
(capacity ≤ 4^(−1/s)·max ‖w‖ + continuity + Fekete-Chebyshev); the deep
step is `Submission.Step3.sym_maximality` (Dubinin's theorem), everything
else in the reduction (SS1/SS2/SS3/Dubinin) is machine-verified. -/
theorem hedgehogBound_of_short_spikes (S : Finset ℂ) (hSne : S.Nonempty)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0)
    (hs : 0 < (dirSet S).card)
    (hshort : ∀ w ∈ spikeEndpoints S,
      ‖w‖ < (4 : ℝ) ^ (1 / ((dirSet S).card : ℝ))) :
    HedgehogBound S := by
  classical
  exact (Submission.Dubinin.polyDecay_fatStar_iff_hedgehogBound S).1
    (Submission.Dubinin.hedgehog_decay_of_short_spikes S hSne hw0 hs hshort)

/-- The set of conjugates is nonempty (there is at least one embedding). -/
lemma conjugateValues_nonempty (α : K) : (conjugateValues α).Nonempty := by
  classical
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨σ α, ?_⟩
  rw [conjugateValues, Finset.mem_image]
  exact ⟨σ, Finset.mem_univ σ, rfl⟩

/-- The conjugates of a nonzero algebraic integer are nonzero, so the spike
endpoints `z²`, `z⁴` are nonzero. -/
lemma spikeEndpoints_conjugateValues_ne_zero (α : K) (hα0 : α ≠ 0) :
    ∀ w ∈ spikeEndpoints (conjugateValues α), w ≠ 0 := by
  classical
  intro w hw
  rw [spikeEndpoints, Finset.mem_union] at hw
  rcases hw with hw | hw
  · rcases (Finset.mem_image.mp hw) with ⟨z, hz, rfl⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      exact Submission.Dictionary.zero_not_mem_conjugateValues (α := α) hα0 (by simpa [hz0] using hz)
    exact pow_ne_zero 2 hz0
  · rcases (Finset.mem_image.mp hw) with ⟨z, hz, rfl⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      exact Submission.Dictionary.zero_not_mem_conjugateValues (α := α) hα0 (by simpa [hz0] using hz)
    exact pow_ne_zero 4 hz0

/-- **E1 interface.**  Under the engine hypothesis `house α < 2^(1/(4·|argSet
α|))`, the hedgehog over the conjugates is polynomially controllable.  This
is what `AnalyticEngine.hankel_eventually_zero` (via E2b/E2c/ChebPower)
needs. -/
theorem e1_hedgehogBound (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hH : NumberField.house α < (2 : ℝ) ^ (1 / (4 * ((argSet α).card : ℝ)))) :
    HedgehogBound (conjugateValues α) := by
  classical
  exact hedgehogBound_of_short_spikes (conjugateValues α)
    (conjugateValues_nonempty α)
    (spikeEndpoints_conjugateValues_ne_zero α hα0)
    (by
      exact Finset.card_pos.mpr (dirSet_conjugateValues_nonempty α))
    (spike_norm_lt_four_rpow_inv α hα hα0 hH)

end Submission.E1Content

end
