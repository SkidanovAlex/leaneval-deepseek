import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.box_facts

/-!
# `Work.EKLC6Core.uniform_contraction_horo`

A subgroup `U ≤ SL₃(ℝ)` that is *contracted* by the diagonal flow `aDiag t` (in the sense that
`aDiag t ^ n · u · (aDiag t ^ n)⁻¹ → 1` for every `u ∈ U`) has two properties.

* **(Support/entry pattern.)**  Every `u ∈ U` has the identity entry in every direction that is
  *not* strictly contracted by `t`: `u i j = δᵢⱼ` whenever `t j ≤ t i`.  (The conjugated entry
  `e^{n (tᵢ - tⱼ)} uᵢⱼ` converges to `δᵢⱼ` while the exponential factor is bounded below by `1`
  whenever `tᵢ ≥ tⱼ`.)

* **(Uniform contraction.)**  For every `ε, δ > 0` there is `N` such that for all `n ≥ N` and all
  `u ∈ U ∩ V ε` the conjugate `aDiag t ^ n · u · (aDiag t ^ n)⁻¹` lies in `V δ`.  Crucially this
  is *uniform* in `u`: the entry pattern above fixes all the entries in the non-contracted
  directions to their identity values, so only the finitely many *strictly contracted* directions
  `t i < t j` can move, and there the factor `e^{n (tᵢ - tⱼ)} → 0` damps the entry `uᵢⱼ`
  (bounded by `ε` because `u ∈ V ε`) uniformly.

The two halves are exactly the "support" and "uniform contraction" inputs the entropy
computation of Pisa §7 uses for the stable horospherical subgroup of `aDiag t`.
-/

open Filter Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `n ↦ e^{n c}` tends to `0` when `c < 0`. -/
theorem tendsto_exp_nat_mul_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * c)) atTop (nhds 0) := by
  have hrw : (fun n : ℕ => Real.exp ((n : ℝ) * c)) = fun n => (Real.exp c) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
  rw [hrw]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
    (by rw [Real.exp_lt_one_iff]; exact hc)

theorem uniform_contraction_horo {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    (∀ u ∈ U, ∀ i j : Fin 3, t i ≥ t j →
        ((u : Matrix (Fin 3) (Fin 3) ℝ) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ U,
        u ∈ Work.EKLContract.V ε →
        Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈ Work.EKLContract.V δ) := by
  refine ⟨?_, ?_⟩
  · -- the entry pattern, immediate from the contraction hypothesis
    intro u hu i j hij
    exact box_facts_entry_eq_one hcontr hu hij
  · intro ε hε δ hδ
    -- Only the strictly contracted directions `t i < t j` can move; there, `e^{n (tᵢ-tⱼ)} → 0`.
    have hev : ∀ᶠ n : ℕ in atTop,
        ∀ i j : Fin 3, t i < t j → Real.exp ((n : ℝ) * (t i - t j)) * ε < δ := by
      have hkey : ∀ i j : Fin 3, t i < t j →
          ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ) * (t i - t j)) * ε < δ := by
        intro i j hlt
        have hlim := tendsto_exp_nat_mul_zero (c := t i - t j) (by linarith)
        have h1 : ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ) * (t i - t j)) < δ / ε :=
          hlim.eventually (isOpen_Iio.mem_nhds (div_pos hδ hε))
        filter_upwards [h1] with n hn
        rw [lt_div_iff₀ hε] at hn
        exact hn
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      by_cases hlt : t i < t j
      · exact (hkey i j hlt).mono (fun n hn _ => hn)
      · exact Filter.Eventually.of_forall (fun _ hn => absurd hn hlt)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun n hn u hu huV => ?_⟩
    intro i j
    rw [boxi_conj_pow_apply]
    by_cases hlt : t i < t j
    · -- strictly contracted direction: the entry is damped uniformly
      have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ hlt
      have h1 : Real.exp ((n : ℝ) * (t i - t j)) * ε < δ := hN n hn i j hlt
      have huij : |u i j| < ε := by
        have hh := huV i j
        rw [Matrix.one_apply_ne hij, sub_zero] at hh
        exact hh
      have hid : ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) = 0 := Matrix.one_apply_ne hij
      rw [hid, sub_zero]
      calc |Real.exp ((n : ℝ) * (t i - t j)) * u i j|
          ≤ Real.exp ((n : ℝ) * (t i - t j)) * ε := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (le_of_lt huij) (le_of_lt (Real.exp_pos _))
        _ < δ := h1
    · -- otherwise the entry already equals the identity entry, for every `u ∈ U`
      have hle : t j ≤ t i := not_lt.mp hlt
      have hzero : Real.exp ((n : ℝ) * (t i - t j)) * u i j
          = ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
        rcases eq_or_ne i j with rfl | h
        · rw [sub_self, mul_zero, Real.exp_zero, one_mul]
          exact box_facts_entry_eq_one hcontr hu (le_refl (t i))
        · have hu0 : u i j = 0 := by
            rw [box_facts_entry_eq_one hcontr hu hle]
            exact Matrix.one_apply_ne h
          rw [hu0, mul_zero, Matrix.one_apply_ne h]
      rw [hzero, sub_self, abs_zero]
      exact hδ

end Work.EKLC6Core
