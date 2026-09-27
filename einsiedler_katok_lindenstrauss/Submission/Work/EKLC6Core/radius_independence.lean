import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.growth_le_atomInfo
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.box_sandwich
import Submission.Work.EKLC6Core.conjBox_smul_mass_mul
import Submission.Work.EKLC6Core.conjBox_neg_nsmul_toReal
import Submission.Work.EKLC6Core.ae_forall_smul_mem
import Submission.Work.EKLC6Core.tendsto_inv_sum_shifted

/-!
# `EKLC6Core.radius_independence` — the rate of decay of the leafwise boxes is radius independent

Let `μ` be an `A`-invariant probability on `X₃`, `U ≤ SL₃(ℝ)` horospherical, `ν = μ_x^U` a
leaf-wise system for `U` (on `X'`), `A`-covariant on the conull set `X''`, and let `t : Fin 3 → ℝ`
contract `U` (`aDiag t^n u aDiag t^{-n} → 1` for `u ∈ U`).

Then for `μ`-a.e. `x` and every fixed `r > 0`,

`(1/n) log (ν (aDiag t^n • x)(V r ∩ U)).toReal → 0`.

The point is Pisa 7.18 ("independence of neighbourhood"): the *exponential rate* of the mass of
the boxes is independent of the radius `r`.  Indeed `V r ∩ U` is trapped between two conjugated
boxes, `conjBox U (k•t) ⊆ V r ∩ U ⊆ conjBox U (-(k•t))` for some `k` (`box_sandwich`), and by the
covariance `conjBox_smul_mass_mul` the masses of a contracted box at `aDiag (n•t)•x` and of the
dual expanded box at `aDiag ((n-k)•t)•x` multiply to `1`.  Writing the latter as the exponential
of a sum of `k` values of the Birkhoff summand `growthFun U ν t` (`conjBox_neg_nsmul_toReal`),
the two sides of the sandwich differ from the mass of `conjBox U (-(k•t))` — whose logarithm is a
sum of `k` Birkhoff summands — only by a *shifted* Birkhoff sum of `k` terms:
`exp(-Σ_{i<n} g(a^{n-k+i}) ) ≤ ν(a^n x)(V r ∩ U) ≤ exp(Σ_{i<n} g(a^{n+i}))` (with `k` fixed).

Dividing by `n` and letting `n → ∞`, the right-hand sides tend to `0` because the *averages*
`n⁻¹ Σ_{j<n} g(a^j x)` converge a.e. (Birkhoff, `P_Birkhoff`; here `Work.EKLComp.birkhoff_all`),
so the shifted windows of fixed length `k` contribute `o(n)` — this is
`tendsto_inv_sum_shifted`.  Integrability of `growthFun U ν t` (`hint`) is exactly the
hypothesis of the pointwise ergodic theorem.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Helpers -/

theorem ri_iterate_aDiag_smul (t : Fin 3 → ℝ) (j : ℕ) (x : X3) :
    (fun y : X3 => aDiag t • y)^[j] x = aDiag ((j : ℝ) • t) • x := by
  induction j with
  | zero => simp [aDiag_zero]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, aDiag_smul_mul]
      have hexp : (t + (j : ℝ) • t : Fin 3 → ℝ) = (((j + 1 : ℕ)) : ℝ) • t := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply]
        push_cast
        ring
      rw [hexp]

theorem ri_add_smul_nat (t : Fin 3 → ℝ) (j n : ℕ) :
    ((j : ℝ) • t + (n : ℝ) • t : Fin 3 → ℝ) = ((n + j : ℕ) : ℝ) • t := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply]
  push_cast
  ring

theorem ri_add_smul_nat' (t : Fin 3 → ℝ) {k n : ℕ} (h : k ≤ n) :
    ((k : ℝ) • t + ((n - k : ℕ) : ℝ) • t : Fin 3 → ℝ) = (n : ℝ) • t := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [Nat.cast_sub h]
  ring


/-- **Main theorem (assembly).** -/
theorem radius_independence {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ X''ᶜ = 0)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (Work.EKLContract.aDiag t ^ n • x)
          (Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3))).toReal))
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨k, hkpos, hsmall, hbig⟩ := box_sandwich hU hcontr hr
  have hT : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ := hAinv t
  have hBirk := Work.EKLComp.birkhoff_all μ (fun y : X3 => aDiag t • y) hT
      (growthFun U ν t) hint
  have hOrb := ae_forall_smul_mem hAinv t hL.conull hX''
  filter_upwards [hOrb, hBirk] with x hxOrb hxBirk
  -- the Birkhoff average is the average of the sequence `j ↦ growthFun U ν t (aDiag (j•t) • x)`
  have hces : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        growthFun U ν t (aDiag ((j : ℝ) • t) • x)) Filter.atTop
      (nhds (μ[growthFun U ν t |
        MeasurableSpace.invariants (fun y : X3 => aDiag t • y)] x)) := by
    refine hxBirk.congr' (Filter.Eventually.of_forall (fun n => ?_))
    simp only [Work.EKLComp.Birkhoff.birkA_def]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ri_iterate_aDiag_smul]
  obtain ⟨hA1, hA2⟩ := tendsto_inv_sum_shifted hces k
  -- the pointwise two-sided estimate
  have hest : ∀ n : ℕ, k ≤ n →
      -(∑ i ∈ Finset.Icc 1 k, growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))
          ≤ Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
              (V r ∩ (U : Set SL3))).toReal) ∧
        Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
              (V r ∩ (U : Set SL3))).toReal)
          ≤ ∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x) := by
    intro n hn
    -- orbit points shifted by an extra `m`
    have horb : ∀ (m j : ℕ), aDiag ((j : ℝ) • t) • (aDiag ((m : ℝ) • t) • x) ∈ X' ∩ X'' := by
      intro m j
      rw [aDiag_smul_mul, ri_add_smul_nat]
      exact hxOrb (m + j)
    -- masses of the two boxes at `aDiag (n•t) • x`
    have hFn : (ν (aDiag ((n : ℝ) • t) • x)
          (conjBox U (-((k : ℝ) • t)))).toReal
        = Real.exp (∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := by
      have h := conjBox_neg_nsmul_toReal hL hcov hU hcontr (m := k)
          (x := aDiag ((n : ℝ) • t) • x) (fun j _ => horb n j)
      rw [h]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [aDiag_smul_mul, ri_add_smul_nat]
    have hFne : ν (aDiag ((n : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t))) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.toReal_top] at hFn
      exact (Real.exp_ne_zero _) hFn.symm
    have hmLtop : ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3)) ≠ ⊤ :=
      ne_top_of_le_ne_top hFne (measure_mono hbig)
    have hMle : (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal
        ≤ Real.exp (∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := by
      calc (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal
          ≤ (ν (aDiag ((n : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t)))).toReal :=
            ENNReal.toReal_mono hFne (measure_mono hbig)
        _ = Real.exp (∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := hFn
    -- the reciprocal identity for the contracted box
    have hprod : ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t)) *
        ν (aDiag (((n - k : ℕ) : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t))) = 1 := by
      have h := conjBox_smul_mass_mul hL hcov hU ((k : ℝ) • t)
        (y := aDiag (((n - k : ℕ) : ℝ) • t) • x) (hxOrb (n - k)) (by
          rw [aDiag_smul_mul, ri_add_smul_nat' t hn]
          exact hxOrb n)
      rwa [show aDiag ((k : ℝ) • t) •
            (aDiag (((n - k : ℕ) : ℝ) • t) • x) = aDiag ((n : ℝ) • t) • x from by
          rw [aDiag_smul_mul, ri_add_smul_nat' t hn]] at h
    have hD : (ν (aDiag (((n - k : ℕ) : ℝ) • t) • x)
          (conjBox U (-((k : ℝ) • t)))).toReal
        = Real.exp (∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)) := by
      have h := conjBox_neg_nsmul_toReal hL hcov hU hcontr (m := k)
          (x := aDiag (((n - k : ℕ) : ℝ) • t) • x) (fun j _ => horb (n - k) j)
      rw [h]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [aDiag_smul_mul, ri_add_smul_nat]
    have hMge : Real.exp
          (-(∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)))
        ≤ (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal := by
      have hC : (ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t))).toReal
          = Real.exp (-(∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))) := by
        have hto : (ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t))).toReal
            * Real.exp (∑ i ∈ Finset.Icc 1 k,
                growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)) = 1 := by
          rw [← hD, ← ENNReal.toReal_mul, hprod, ENNReal.toReal_one]
        rw [Real.exp_neg]
        exact eq_inv_of_mul_eq_one_left hto
      rw [← hC]
      exact ENNReal.toReal_mono hmLtop (measure_mono hsmall)
    constructor
    · have h := Real.log_le_log (Real.exp_pos _) hMge
      rwa [Real.log_exp] at h
    · have hMpos : 0 < (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal :=
        lt_of_lt_of_le (Real.exp_pos _) hMge
      have h := Real.log_le_log hMpos hMle
      rwa [Real.log_exp] at h
  -- rewrite `aDiag t ^ n • x` as `aDiag (n • t) • x`
  have hrew : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (aDiag (((n : ℕ) : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal))
      = (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (aDiag t ^ n • x) (V r ∩ (U : Set SL3))).toReal)) := by
    funext n
    rw [aDiag_real_nsmul]
  rw [← hrew]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ => -((n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
        growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)))
    (h := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
        growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) ?_ ?_ ?_ ?_
  · have h := hA2.neg
    simpa using h
  · exact hA1
  · filter_upwards [Filter.eventually_ge_atTop k] with n hn
    have h := (hest n hn).1
    calc -((n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))
        = (n : ℝ)⁻¹ * (-(∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))) := by ring
      _ ≤ (n : ℝ)⁻¹ * Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
            (V r ∩ (U : Set SL3))).toReal) :=
          mul_le_mul_of_nonneg_left h (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop k] with n hn
    exact mul_le_mul_of_nonneg_left (hest n hn).2 (by positivity)

end Work.EKLC6Core

