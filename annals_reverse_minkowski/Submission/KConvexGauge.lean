import Mathlib
import Submission.KConvex
import Submission.Commons.Geometry.Convex.gauge_eq_sSup_inner_polar
import Submission.Commons.MeasureTheory.measurable_argmax_select
import Submission.Commons.Topology.exists_seq_denseRange_of_isCompact

/-!
# The test-free `ℓ`-position bound for the first chaos

This file removes the test field from `Submission.KConvex.kconvex_scalar`: the first Hermite-chaos
component `comp 1 s C` of a finite Hermite sum `hermSum s C` is bounded, in the `L²(μ N)` norm of
`gauge K`, by `4 (1 + log₂ d)` times the whole sum — Pisier's Theorem 2.5 (first step) in the
"scalar-tested" form turned into the operator-norm form.

The argument: choose a countable dense sequence `ψ : ℕ → polar K`; for each `M` let `Ψ_M` be the
*measurable* arg-max of `m ↦ ⟪ψ m, comp 1 s C x⟫` over `m ≤ M` (this is where
`Commons.MeasureTheory.measurable_argmax_select` is used); apply `kconvex_scalar` to `Ψ_M` and
then pass to the limit `M → ∞` by dominated convergence, using
`gauge K v = sSup {⟪z, v⟫ : z ∈ polar K}` (`Commons.Geometry.Convex.gauge_eq_sSup_inner_polar`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Pointwise Topology

namespace Submission.KConvexGauge

variable {n N : ℕ}

/-- Sup over a dense sequence equals the sup over the whole set for a continuous linear test. -/
theorem sSup_image_eq_sSup_range {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hKbdd : Bornology.IsBounded K) {ψ : ℕ → E} (hψ : ∀ m, ψ m ∈ K)
    (hdense : ∀ z ∈ K, ∀ ε > 0, ∃ m, dist (ψ m) z < ε) (u : E) :
    sSup ((fun z : E => inner ℝ z u) '' K) = sSup (Set.range (fun m => inner ℝ (ψ m) u)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hKbdd
  have hbound : ∀ z ∈ K, ‖z‖ ≤ R := by
    intro z hz
    have h := hR hz
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  set A : Set ℝ := (fun z : E => inner ℝ z u) '' K with hA
  set B : Set ℝ := Set.range (fun m => inner ℝ (ψ m) u) with hB
  have hBA : B ⊆ A := by rintro b ⟨m, rfl⟩; exact ⟨ψ m, hψ m, rfl⟩
  have hbddA : BddAbove A := by
    refine ⟨R * ‖u‖, ?_⟩
    rintro a ⟨z, hz, rfl⟩
    calc inner ℝ z u ≤ ‖inner ℝ z u‖ := le_abs_self _
      _ ≤ ‖z‖ * ‖u‖ := norm_inner_le_norm z u
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg u)
  have hbddB : BddAbove B := hbddA.mono hBA
  have hAne : A.Nonempty := ⟨_, ψ 0, hψ 0, rfl⟩
  refine le_antisymm (csSup_le hAne (fun a ha => ?_))
    (csSup_le ⟨inner ℝ (ψ 0) u, ⟨0, rfl⟩⟩ (fun b hb => le_csSup hbddA (hBA hb)))
  rcases ha with ⟨z, hz, rfl⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨m, hm⟩ := hdense z hz (ε / (‖u‖ + 1)) (by positivity)
  have hmem : inner ℝ (ψ m) u ∈ B := ⟨m, rfl⟩
  have h1 : inner ℝ (ψ m) u ≤ sSup B := le_csSup hbddB hmem
  have h2 : ‖ψ m - z‖ < ε / (‖u‖ + 1) := by rwa [dist_eq_norm] at hm
  have h3 : inner ℝ z u - inner ℝ (ψ m) u ≤ ε := by
    rw [← inner_sub_left]
    calc inner ℝ (z - ψ m) u ≤ ‖inner ℝ (z - ψ m) u‖ := le_abs_self _
      _ ≤ ‖z - ψ m‖ * ‖u‖ := norm_inner_le_norm _ _
      _ = ‖ψ m - z‖ * ‖u‖ := by rw [norm_sub_rev]
      _ ≤ (ε / (‖u‖ + 1)) * ‖u‖ := mul_le_mul_of_nonneg_right h2.le (norm_nonneg u)
      _ ≤ (ε / (‖u‖ + 1)) * (‖u‖ + 1) := by
          gcongr; linarith [norm_nonneg u]
      _ = ε := by field_simp
  linarith

open Submission.KConvex Submission.GaussianChaos

/-- **The `ℓ`-position of the first chaos (test-free form).**  For a symmetric convex body `K`,
a comparison map `T` with `‖T x‖ ≤ gauge K x ≤ d ‖T x‖` and a finite Hermite sum `hermSum s C`,

`∫ (gauge K (comp 1 s C x))² dμ ≤ (4 (1 + log₂ d))² ∫ (gauge K (hermSum s C x))² dμ`. -/
theorem kconvex_gauge (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (hcpt : IsCompact K) (hKnhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    {d : ℝ} (hd : 1 ≤ d) (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    ∫ x, (gauge K (comp 1 s C x)) ^ 2 ∂μ N
      ≤ (4 * (1 + Real.log d / Real.log 2)) ^ 2 *
        ∫ x, (gauge K (hermSum s C x)) ^ 2 ∂μ N := by
  classical
  set f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) := fun x => comp 1 s C x with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    simp only [comp, Submission.GaussianChaos.herm]
    fun_prop
  set A : ℝ := ∫ x, (gauge K (hermSum s C x)) ^ 2 ∂μ N with hA
  set C0 : ℝ := (4 * (1 + Real.log d / Real.log 2)) ^ 2 with hC0
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hintf : Integrable (fun x => (gauge K (f x)) ^ 2) (μ N) := by
    have h := integrable_sq_gauge_hermSum K hcvx hKnhds d hd0 T hT1 hT2
      (s.filter (fun α => deg α = 1)) C
    refine h.congr (Eventually.of_forall fun x => ?_)
    rfl
  have hP0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ polar K := fun y _ => by simp
  have hPbdd : Bornology.IsBounded (polar K) := by
    obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds h0)
    refine (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).mpr
      ⟨2 / r, ?_⟩
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rcases eq_or_ne z 0 with rfl | hz0
    · simp only [norm_zero]; exact div_nonneg (by norm_num) hr0.le
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hyb : (r / 2 / ‖z‖) • z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (div_nonneg hr0.le (by norm_num)) (norm_nonneg z))]
      rw [show r / 2 / ‖z‖ * ‖z‖ = r / 2 from div_mul_cancel₀ (r / 2) hzn.ne']
      linarith
    have hy : (r / 2 / ‖z‖) • z ∈ K := interior_subset (hr hyb)
    have h1 : inner ℝ z ((r / 2 / ‖z‖) • z) ≤ 1 := hz _ hy
    rw [inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h3 : (r / 2 / ‖z‖) * ‖z‖ ^ 2 = r / 2 * ‖z‖ := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hzn.ne']
    rw [h3] at h1
    rw [le_div_iff₀ hr0]
    nlinarith [h1]
  obtain ⟨ψ, hψP, hψdense⟩ := Commons.Topology.exists_seq_denseRange_of_isCompact (polar K) ⟨0, hP0⟩
  have hsup : ∀ x, gauge K (f x) = sSup (Set.range (fun m => inner ℝ (ψ m) (f x))) := by
    intro x
    rw [Commons.Geometry.Convex.gauge_eq_sSup_inner_polar K hcvx hcpt h0 (f x)]
    exact sSup_image_eq_sSup_range hPbdd hψP hψdense (f x)
  have htest : ∀ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n),
      AEStronglyMeasurable g (μ N) → (∀ x, g x ∈ polar K) →
      ∫ x, (inner ℝ (g x) (f x)) ^ 2 ∂μ N ≤ C0 * A := by
    intro g hgm hgP
    have hΨ : ∀ x, gauge (polar K) (g x) ≤ 1 := fun x => gauge_le_one_of_mem (hgP x)
    have h := kconvex_scalar K hcvx habs hbdd hbal hcpt hKnhds h0 hKsymm hd T hT1 hT2 s C g hΨ hgm
    simpa [hfdef, hC0, hA] using h
  have hsel : ∀ M : ℕ, ∃ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n),
      Measurable g ∧ (∀ x, ∃ m, m ≤ M ∧ g x = ψ m) ∧
      (∀ x, ∀ m, m ≤ M → inner ℝ (ψ m) (f x) ≤ inner ℝ (g x) (f x)) := fun M =>
    Commons.MeasureTheory.measurable_argmax_select ψ f (fun m => (continuous_const.inner hfcont).measurable) M
  choose g hgm hgset hgmax using hsel
  set u : ℕ → EuclideanSpace ℝ (Fin N) → ℝ := fun M x => inner ℝ (g M x) (f x) with hu
  have humeas : ∀ M, Measurable (u M) := fun M => (hgm M).inner hfcont.measurable
  have hugP : ∀ M x, g M x ∈ polar K := by
    intro M x
    obtain ⟨m, _, hm⟩ := hgset M x
    rw [hm]
    exact hψP m
  have hubound : ∀ M x, u M x ≤ gauge K (f x) := by
    intro M x
    have h1 := inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm (g M x) (f x)
    have h2 : gauge (polar K) (g M x) ≤ 1 := gauge_le_one_of_mem (hugP M x)
    calc u M x ≤ gauge (polar K) (g M x) * gauge K (f x) := h1
      _ ≤ 1 * gauge K (f x) := mul_le_mul_of_nonneg_right h2 (gauge_nonneg _)
      _ = gauge K (f x) := one_mul _
  have hubound2 : ∀ M x, |u M x| ≤ gauge K (f x) := by
    intro M x
    have h1 := abs_inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm (g M x) (f x)
    have h2 : gauge (polar K) (g M x) ≤ 1 := gauge_le_one_of_mem (hugP M x)
    calc |u M x| = |inner ℝ (g M x) (f x)| := rfl
      _ ≤ gauge (polar K) (g M x) * gauge K (f x) := h1
      _ ≤ 1 * gauge K (f x) := mul_le_mul_of_nonneg_right h2 (gauge_nonneg _)
      _ = gauge K (f x) := one_mul _
  have hu_mono : ∀ x, Monotone (fun M => u M x) := by
    intro x M M' hMM'
    show u M x ≤ u M' x
    obtain ⟨m₀, hm₀, heq⟩ := hgset M x
    have h2 : u M x = inner ℝ (ψ m₀) (f x) := by
      show inner ℝ (g M x) (f x) = inner ℝ (ψ m₀) (f x)
      rw [heq]
    rw [h2]
    exact le_trans (hgmax M' x m₀ (le_trans hm₀ hMM')) le_rfl
  have hu_bdd : ∀ x, BddAbove (Set.range (fun M => u M x)) := by
    intro x
    exact ⟨gauge K (f x), by rintro a ⟨M, rfl⟩; exact hubound M x⟩
  have hu_sup : ∀ x, (⨆ M, u M x) = gauge K (f x) := by
    intro x
    refine le_antisymm (ciSup_le (fun M => hubound M x)) ?_
    rw [hsup x]
    refine csSup_le ⟨inner ℝ (ψ 0) (f x), ⟨0, rfl⟩⟩ (fun b hb => ?_)
    obtain ⟨m, rfl⟩ := hb
    exact le_trans (hgmax m x m le_rfl) (le_ciSup (hu_bdd x) m)
  have hu_lim : ∀ x, Tendsto (fun M => u M x) atTop (𝓝 (gauge K (f x))) := by
    intro x
    rw [← hu_sup x]
    exact tendsto_atTop_ciSup (hu_mono x) (hu_bdd x)
  have hmean : Tendsto (fun M => ∫ x, (u M x) ^ 2 ∂μ N) atTop
      (𝓝 (∫ x, (gauge K (f x)) ^ 2 ∂μ N)) := by
    refine tendsto_integral_of_dominated_convergence
      (μ := μ N) (F := fun M x => (u M x) ^ 2) (f := fun x => (gauge K (f x)) ^ 2)
      (fun x => (gauge K (f x)) ^ 2)
      (fun M => ((humeas M).pow_const 2).aestronglyMeasurable) hintf ?_ ?_
    · intro M
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hubound2 M x) 2
    · exact Eventually.of_forall fun x => (hu_lim x).pow 2
  have hterm : ∀ M, ∫ x, (u M x) ^ 2 ∂μ N ≤ C0 * A := by
    intro M
    have h := htest (g M) (hgm M).aestronglyMeasurable (hugP M)
    simpa [hu] using h
  exact le_of_tendsto' hmean hterm

end Submission.KConvexGauge
