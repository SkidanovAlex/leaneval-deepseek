import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.hopf_maximal_inequality
import Submission.Work.EKLComp.sum_avg_window
import Submission.Work.EKLComp.measurable_integrable_avg_over
import Submission.Work.EKLComp.exists_factorial_lt_intervalIntegral

open MeasureTheory Filter Topology
open scoped ENNReal

open Work.EKLContract

set_option linter.style.haveILetI false

noncomputable section
namespace Work.EKLComp

/-!
# C11b: the maximal inequality for the flows `τ ↦ α^{τ t}`

`Work.EKLContract.P_MaxFlow` (component C11b of the frozen EKL contract): for an `A`-invariant
probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a nonnegative integrable `f` and `α > 0`,

  `μ {x | ∃ T > 0, α T < ∫₀ᵀ f (α^{τ t} · x) dτ} ≤ ‖f‖₁ / α`

(the weak-`(1,1)` maximal inequality for the one-parameter flow `φ_τ x = α^{τ t} · x`).

## Proof

The continuous-time inequality is transferred from the discrete Hopf maximal inequality
(`Work.EKLComp.hopf_maximal_inequality`) along the time-`δ` maps:

* `winAvg φ f δ x = δ⁻¹ ∫₀^δ f (φ τ x) dτ` is the window average; by
  `Work.EKLComp.measurable_integrable_avg_over` it is measurable, integrable and has the same
  integral as `f`, and by `Work.EKLComp.sum_avg_window` the Riemann sums of the window averages
  reproduce the flow averages exactly:
  `∑_{k<m} winAvg φ f δ (φ^{kδ} x) = δ⁻¹ ∫₀^{mδ} f (φ τ x) dτ`.
* Hence for `δ = 1/n!` the set `B n = {x | ∃ m > 0, α m < ∑_{k<m} winAvg φ f δ (φ^{kδ} x)}`
  has `μ (B n) ≤ ENNReal.ofReal (‖f‖₁ / α)` by the discrete Hopf inequality.
* `E = {x | ∃ T > 0, α T < ∫₀^T f (φ τ x) dτ} ⊆ ⋃ n, D n` where
  `D n = {x | ∃ m > 0, α < winAvg φ f (m/n!) x}`: if the flow average at time `T` exceeds `α`,
  some rational `q = m/n! < T` does too, by continuity from below of the integral
  (`Work.EKLComp.exists_factorial_lt_intervalIntegral`).
* `D n ⊆ D (n+1) ⊆ B (n+1)` ((n+1)! = (n+1)·n!), so `μ E ≤ ⨆ n, μ (D n) ≤ ⨆ n, μ (B n) ≤ ‖f‖₁/α`.

The concrete flow is `φ τ x = aDiag (τ • t) • x`, whose one-parameter group law is `aDiag_add`
and whose measure preservation is the `A`-invariance of `μ`; its joint measurability comes from
the continuity of `aDiag` and of the action of `SL₃(ℝ)` on `X₃`.
-/

/-- The average of `f` along the flow `φ` over the time window `(0, d]` starting at `x`. -/
abbrev winAvg {X : Type*} (φ : ℝ → X → X) (f : X → ℝ) (d : ℝ) (x : X) : ℝ :=
  d⁻¹ * ∫ τ in (0:ℝ)..d, f (φ τ x)

/-- The `n`-th inverse factorial, `1/n!`. -/
abbrev invFact (n : ℕ) : ℝ := ((n.factorial : ℝ))⁻¹

theorem invFact_pos (n : ℕ) : 0 < invFact n :=
  inv_pos.mpr (by exact_mod_cast Nat.factorial_pos n)

theorem flow_maximal_inequality {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (φ : ℝ → X → X) (hφ0 : ∀ x, φ 0 x = x) (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hmp : ∀ s : ℝ, MeasurePreserving (φ s) μ μ)
    (f : X → ℝ) (hfm : Measurable (fun p : ℝ × X => f (φ p.1 p.2)))
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) (α : ℝ) (hα : 0 < α) :
    μ {x | ∃ T : ℝ, 0 < T ∧ α * T < ∫ τ in (0:ℝ)..T, f (φ τ x)}
      ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α) := by
  -- The sets `D n ⊆ B n`.
  set D : ℕ → Set X := fun n => {x | ∃ m : ℕ, 0 < m ∧ α < winAvg φ f ((m:ℝ) * invFact n) x}
    with hD
  set B : ℕ → Set X := fun n => {x | ∃ m : ℕ, 0 < m ∧
      α * (m:ℝ) < ∑ k ∈ Finset.range m, winAvg φ f (invFact n) ((φ (invFact n))^[k] x)} with hB
  -- elementary equivalence `α < s⁻¹ * I ↔ α * s < I` for `s > 0`
  have hlt : ∀ {s I : ℝ}, 0 < s → (α < s⁻¹ * I ↔ α * s < I) := by
    intro s I hs
    rw [mul_comm s⁻¹ I, ← div_eq_mul_inv, lt_div_iff₀ hs]
  -- (0) iterate identity: the k-th iterate of the time-`d` map is the time-`k*d` map.
  have hiter : ∀ (n k : ℕ) (x : X), (φ (invFact n))^[k] x = φ ((k:ℝ) * invFact n) x := by
    intro n k
    induction k with
    | zero => intro x; simp [hφ0]
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, ← hφadd]
        congr 1
        push_cast
        ring
  -- (1) Each `B n` satisfies the discrete Hopf bound.
  have hBbound : ∀ n : ℕ, μ (B n) ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α) := by
    intro n
    obtain ⟨hGm, hGi, hGe⟩ :=
      measurable_integrable_avg_over μ φ hmp f hfm hfi (invFact n) (invFact_pos n)
    have hnn : ∀ x : X, 0 ≤ winAvg φ f (invFact n) x := by
      intro x
      have h1 : 0 ≤ (invFact n)⁻¹ := le_of_lt (inv_pos.mpr (invFact_pos n))
      have h2 : 0 ≤ ∫ τ in (0:ℝ)..(invFact n), f (φ τ x) :=
        intervalIntegral.integral_nonneg (le_of_lt (invFact_pos n)) (fun u _ => hf0 _)
      exact mul_nonneg h1 h2
    have hGe' : (∫ x, winAvg φ f (invFact n) x ∂μ) = ∫ x, f x ∂μ := hGe
    have h := hopf_maximal_inequality μ (φ (invFact n)) (hmp (invFact n))
      (winAvg φ f (invFact n)) hGi hnn α hα
    rw [hGe'] at h
    exact h
  -- (2) `D n ⊆ B n`: the Riemann-sum identity plus integrability forced by a positive integral.
  have hDB : ∀ n : ℕ, D n ⊆ B n := by
    intro n x hx
    rw [hD] at hx
    obtain ⟨m, hm, hgt⟩ := hx
    have hs : 0 < (m:ℝ) * invFact n := mul_pos (by exact_mod_cast hm) (invFact_pos n)
    have hgt' : α * ((m:ℝ) * invFact n) < ∫ τ in (0:ℝ)..((m:ℝ) * invFact n), f (φ τ x) :=
      (hlt hs).mp hgt
    have hII : IntervalIntegrable (fun τ : ℝ => f (φ τ x)) volume 0 ((m:ℝ) * invFact n) := by
      by_contra hc
      rw [intervalIntegral.integral_undef hc] at hgt'
      have hpos : 0 < α * ((m:ℝ) * invFact n) := mul_pos hα hs
      linarith
    have hIO : IntegrableOn (fun τ : ℝ => f (φ τ x)) (Set.Ioc 0 ((m:ℝ) * invFact n)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hs)).mp hII
    have h2 := sum_avg_window (fun τ : ℝ => f (φ τ x)) (invFact n) (invFact_pos n) m hIO
    have hsum : ∑ k ∈ Finset.range m, winAvg φ f (invFact n) ((φ (invFact n))^[k] x)
        = (invFact n)⁻¹ * ∫ τ in (0:ℝ)..((m:ℝ) * invFact n), f (φ τ x) := by
      rw [← h2]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have heq : (fun τ : ℝ => f (φ τ ((φ (invFact n))^[k] x)))
          = fun τ : ℝ => f (φ (τ + (k:ℝ) * invFact n) x) := by
        funext τ
        rw [hφadd, ← hiter]
      unfold winAvg
      rw [heq]
    rw [hB]
    refine ⟨m, hm, ?_⟩
    rw [hsum]
    have hkey : (invFact n)⁻¹ * (α * ((m:ℝ) * invFact n)) = α * (m:ℝ) := by
      have h1 : (invFact n)⁻¹ * invFact n = 1 := inv_mul_cancel₀ (ne_of_gt (invFact_pos n))
      calc (invFact n)⁻¹ * (α * ((m:ℝ) * invFact n))
          = α * ((m:ℝ) * ((invFact n)⁻¹ * invFact n)) := by ring
        _ = α * (m:ℝ) := by rw [h1, mul_one]
    rw [← hkey]
    exact mul_lt_mul_of_pos_left hgt' (inv_pos.mpr (invFact_pos n))
  -- (3) The `D n` increase.
  have hDmono : Monotone D := by
    refine monotone_nat_of_le_succ (fun n x hx => ?_)
    rw [hD] at hx ⊢
    obtain ⟨m, hm, hgt⟩ := hx
    refine ⟨m * (n+1), Nat.mul_pos hm (Nat.succ_pos n), ?_⟩
    have hfac : (((n+1).factorial : ℝ)) = ((n:ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hkey : ((m * (n+1) : ℕ) : ℝ) * invFact (n+1) = (m:ℝ) * invFact n := by
      show ((m * (n+1) : ℕ) : ℝ) * (((n+1).factorial : ℝ))⁻¹ = (m:ℝ) * ((n.factorial : ℝ))⁻¹
      rw [hfac, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
      field_simp
      try ring
    rw [hkey]
    exact hgt
  -- (4) The flow maximal set is contained in `⋃ n, D n`.
  have hEsub : {x | ∃ T : ℝ, 0 < T ∧ α * T < ∫ τ in (0:ℝ)..T, f (φ τ x)} ⊆ ⋃ n, D n := by
    intro x hx
    obtain ⟨T, hT, hTx⟩ := hx
    obtain ⟨n, m, hm, h4⟩ := exists_factorial_lt_intervalIntegral hT hα hTx
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    rw [hD]
    refine ⟨m, hm, ?_⟩
    have h4' : α * ((m:ℝ) * invFact n) < ∫ τ in (0:ℝ)..((m:ℝ) * invFact n), f (φ τ x) := by
      have h := h4
      rw [div_eq_mul_inv] at h
      exact h
    have hs : 0 < (m:ℝ) * invFact n := mul_pos (by exact_mod_cast hm) (invFact_pos n)
    exact (hlt hs).mpr h4'
  -- (5) Put it together.
  calc μ {x | ∃ T : ℝ, 0 < T ∧ α * T < ∫ τ in (0:ℝ)..T, f (φ τ x)}
      ≤ μ (⋃ n, D n) := measure_mono hEsub
    _ = ⨆ n, μ (D n) := hDmono.measure_iUnion
    _ ≤ ⨆ n, μ (B n) := iSup_mono (fun n => measure_mono (hDB n))
    _ ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α) := iSup_le hBbound

/-- `t ↦ aDiag t` is continuous. -/
theorem continuous_aDiag__prove_MaxFlow : Continuous (fun v : Fin 3 → ℝ => aDiag v) := by
  have hmat : Continuous (fun v : Fin 3 → ℝ => toMat (aDiag v)) := by
    apply continuous_matrix
    intro i j
    rw [show (fun v : Fin 3 → ℝ => toMat (aDiag v) i j)
        = fun v : Fin 3 → ℝ => if i = j then Real.exp (v i - (∑ k, v k) / 3) else 0 from by
      funext v; rw [toMat_aDiag, Matrix.diagonal_apply]]
    split_ifs
    · fun_prop
    · exact continuous_const
  exact (IsInducing.subtypeVal.continuous_iff).mpr hmat

/-- Joint measurability of the diagonal flow on `X₃`. -/
theorem measurable_aDiag_smul (t : Fin 3 → ℝ) :
    Measurable (fun p : ℝ × X3 => aDiag (p.1 • t) • p.2) := by
  have h1 : Continuous (fun p : ℝ × X3 => aDiag (p.1 • t)) :=
    continuous_aDiag__prove_MaxFlow.comp (continuous_fst.smul continuous_const)
  have h2 : Continuous (fun p : SL3 × X3 => p.1 • p.2) := continuous_smul
  exact (h2.comp (h1.prodMk continuous_snd)).measurable

theorem prove_MaxFlow : Work.EKLContract.P_MaxFlow := by
  intro μ hμprob hAinv t f hfmeas hf0 hfint α hα
  haveI : IsProbabilityMeasure μ := hμprob
  refine flow_maximal_inequality μ (fun (τ : ℝ) (x : X3) => aDiag (τ • t) • x) ?_ ?_ ?_ f
    (hfmeas.comp (measurable_aDiag_smul t)) ?_ hfint α hα
  · intro x
    rw [zero_smul, aDiag_zero, one_smul]
  · intro s u x
    rw [add_smul, aDiag_smul_mul]
  · intro s
    exact hAinv (s • t)
  · intro x
    exact hf0 x

end Work.EKLComp
