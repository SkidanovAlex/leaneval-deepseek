import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1B.chiSmallB_windowData
import Submission.Work.BoseFixB1B.cubeWordDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform`

Uniform `(1 + ‖p‖)⁻³` decay of the windowed `p`-amplitude

    `tBamp χ p Ψ i x = ∫_z χ(z) e^{−i⟪p,z⟫} Ψ(x_{i←z}) dz`

at the sliding cutoff `χ = chiSmallB M ℓ d u = χ(x/ℓ)·χ_M((ℓd)⁻¹•x − u)`, **uniformly in the
sliding parameter `u`**:

    ∃ C ≥ 0, ∀ u i (x ∈ abox N ℓ) p, ‖tBamp (chiSmallB M ℓ d u) p Ψ i x‖ ≤ C/(1+‖p‖)³ .

The cutoff `chiSmallB M ℓ d u` is only `C^{M−1}` (`chiSmall M = (ζζζ)^M/√…` has derivative jumps
of the cosine profile killed to order `M−1`), so `M ≥ 4` is exactly the threshold at which the
three-fold integration by parts below is legitimate — the `C^∞` theorem
`Work.SmallBoxTBWord.tBamp_decay` does *not* apply to it.

## Structure of the proof

* `chiSmallB_windowData` (`Submission/Work/BoseFixB1B/chiSmallB_windowData.lean`) supplies the
  three genuinely analytic inputs, all **uniform in `u`**: `C³`-regularity of every
  `chiSmallB M ℓ d u`, a single ball `closedBall 0 R` containing every `tsupport`, and a single
  sequence `G` bounding the iterated derivatives of order `≤ 3` of every complexified cutoff.
  Uniformity in `u` is exactly translation-invariance of `iteratedFDeriv`, the `u`-dependence of
  `chiSmallB` being a translation of its `(ℓd)`-scale factor.
* `tBamp_decay_uniform_family` is the Fourier-decay engine: the proof of
  `Work.BoseFixB1S.win.tBamp_decay_three` (which derives its data from a *single* window through
  `chi3_support_and_deriv_bound`) run with the data `(R, G)` supplied by the caller, so that **one**
  constant serves the whole family.  The engine is
  `Commons.Analysis.Fourier.fourier_decay_mul_update` (three-fold integration by parts in the
  compactly supported window), with the `Ψ`-data bounded on the fixed box of radius
  `S = max R (3ℓ)` by `Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound`.
* The target is the instantiation `ι := ℝ³`, `χ u := chiSmallB M ℓ d u`, `a := ℓ`.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- A vector of `ℝ³` all of whose coordinates are bounded by `C` has norm at most `√3·C`. -/
private lemma norm_le_of_coord_abs_le {C : ℝ} (hC : 0 ≤ C) {y : E3}
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ _k : Fin 3, C ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  · exact hb

/-- Absorption of the `(2π)` scaling of the Fourier variable:
`K·(1+r/c)⁻³ ≤ K·c³/(1+r)³` for `K ≥ 0`, `c ≥ 1`, `r ≥ 0`. -/
private lemma zpow_neg_three_le (K c r : ℝ) (hK : 0 ≤ K) (hc : 1 ≤ c) (hr : 0 ≤ r) :
    K * (1 + r / c) ^ (-(3:ℤ)) ≤ K * c ^ 3 / (1 + r) ^ 3 := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have h1r : 0 ≤ 1 + r := by linarith
  have hbase : 0 < 1 + r / c := by positivity
  have hdiv : 1 + r / c = (c + r) / c := by field_simp
  have hexp : (1 + r / c) ^ 3 = (c + r) ^ 3 / c ^ 3 := by rw [hdiv, div_pow]
  have hle : (1 + r) ^ 3 / c ^ 3 ≤ (1 + r / c) ^ 3 := by
    rw [hexp]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h1r (by linarith) 3) (by positivity)
  have hpos1 : 0 < (1 + r / c) ^ 3 := pow_pos hbase 3
  have hpos2 : 0 < (1 + r) ^ 3 / c ^ 3 := by positivity
  have hinv : ((1 + r / c) ^ 3)⁻¹ ≤ c ^ 3 / (1 + r) ^ 3 := by
    have h := (inv_le_inv₀ hpos1 hpos2).mpr hle
    rwa [inv_div] at h
  have hzpow : (1 + r / c) ^ (-(3:ℤ)) = ((1 + r / c) ^ 3)⁻¹ := by simp [zpow_neg]
  rw [hzpow]
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinv hK

/-! ## The Fourier-decay engine, with the window data supplied by the caller -/

/-- **Uniform `(1+‖p‖)⁻³` decay of the windowed amplitude for a family of windows with common
support and derivative data.**  The family `χ : ι → ℝ³ → ℝ` has all its members supported in the
same ball `closedBall 0 R` (`R > 0`) and all the iterated derivatives of the complexified members
of order `≤ 3` bounded by one sequence `G`; then a single constant `C` works for the whole family,
uniformly in the box point `x ∈ abox N a`, in the slot `i` and in the momentum `p`. -/
theorem tBamp_decay_uniform_family {ι : Type*} {N : ℕ} {a : ℝ} (ha : 0 < a)
    {χ : ι → E3 → ℝ} (hχd : ∀ u : ι, ContDiff ℝ 3 (χ u))
    {R : ℝ} (hRpos : 0 < R)
    (hRsupp : ∀ u : ι, tsupport (χ u) ⊆ Metric.closedBall (0 : E3) R)
    {G : ℕ → ℝ} (hGnn : ∀ k, 0 ≤ G k)
    (hGbd : ∀ (u : ι) (k : ℕ), k ≤ 3 → ∀ z : E3,
      ‖iteratedFDeriv ℝ k (fun z : E3 => (χ u z : ℂ)) z‖ ≤ G k)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ι) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N a → ∀ (i : Fin N) (p : E3),
      ‖Work.SmallBoxTBWord.tBamp (χ u) p Φ i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  set S : ℝ := max R (3 * a) with hSdef
  have hRS : R ≤ S := le_max_left _ _
  have hSnn : 0 ≤ S := le_of_lt (lt_of_lt_of_le hRpos hRS)
  obtain ⟨Cd, hCd0, hCd⟩ := Commons.Analysis.Fourier.fourier_decay_mul_update N R S hRpos hRS
  obtain ⟨M, hMnn, hMbd⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) hSnn hΦ
  refine ⟨Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) * (2*π)^3,
    by positivity, ?_⟩
  intro u x hx i p
  have hxS : ∀ j : Fin N, ‖x j‖ ≤ S := by
    intro j
    have hmem : x j ∈ Submission.BoseGases.acube a := hx j
    rw [Submission.BoseGases.mem_acube_iff] at hmem
    have habs : ∀ k : Fin 3, |(x j) k| ≤ a / 2 := by
      intro k
      rw [abs_le]
      exact ⟨by linarith [(hmem k).1], (hmem k).2⟩
    have h1 : ‖x j‖ ≤ Real.sqrt 3 * (a / 2) := norm_le_of_coord_abs_le (by positivity) habs
    have h2 : Real.sqrt 3 * (a / 2) ≤ 3 * a := by
      have hs : Real.sqrt 3 ≤ 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      nlinarith
    linarith [h1, h2, le_max_right R (3 * a)]
  have hchi3 : ContDiff ℝ 3 (fun z : E3 => (χ u z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχd u)
  have hPhi3 : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgsupp : ∀ z : E3, (fun z : E3 => (χ u z : ℂ)) z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz
    have hzmem : z ∈ tsupport (χ u) := subset_tsupport (χ u) (by simpa using hz)
    have h1 : z ∈ Metric.closedBall (0 : E3) R := hRsupp u hzmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    exact h1
  have hdec := hCd (fun z : E3 => (χ u z : ℂ)) G hchi3 hgsupp (hGbd u)
      (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) M hPhi3 hMbd x hxS i ((2*π)⁻¹ • p)
  have hconv : Work.SmallBoxTBWord.tBamp (χ u) p Φ i x = Submission.BoseGases.kinFT
      (fun z : E3 => (χ u z : ℂ) * (Φ (Function.update x i z) : ℂ)) p := by
    rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  refine hdec.trans ?_
  have hnorm_xi : ‖(2 * π)⁻¹ • p‖ = ‖p‖ / (2 * π) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2*π)⁻¹), inv_mul_eq_div]
  rw [hnorm_xi]
  have hK : 0 ≤ Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) :=
    mul_nonneg (mul_nonneg hCd0 (by positivity)) (by positivity)
  have := zpow_neg_three_le
    (Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|))
    (2*π) ‖p‖ hK (by linarith [Real.pi_gt_three]) (norm_nonneg p)
  simpa using this

/-! ## The target -/

theorem chiSmallB_tBamp_decay_uniform {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin 3)) (i : Fin N) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N ℓ → ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p Ψ i x‖
        ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨hcont, R, G, hRpos, hGnn, hsupp, hGbd⟩ := chiSmallB_windowData (M := M) hM hℓ hd
  obtain ⟨C, hC0, hC⟩ :=
    tBamp_decay_uniform_family (ι := E3) (N := N) (a := ℓ) hℓ
      (χ := fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u) hcont hRpos hsupp hGnn hGbd hΨ
  exact ⟨C, hC0, fun u i x hx p => hC u x hx i p⟩

end Work.BoseFixB1B
