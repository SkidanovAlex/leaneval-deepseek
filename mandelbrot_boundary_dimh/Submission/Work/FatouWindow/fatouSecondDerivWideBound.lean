import Mathlib
import Submission.Work.FatouL1.wStripBoundDefs
import Submission.Work.FatouL1.derivCocycleProduct
import Submission.Work.FatouL1.normOneSubMulDerivLe
import Submission.Work.FatouL1.sub_eq_integral_deriv_ball
import Submission.Work.FatouL1.preimage_nearTranslation
import Submission.Work.FatouWindow.fatouU_apriori_bound_wide
import Submission.Work.FatouWindow.fatouDerivBoundedStrip
import Submission.Work.FatouL1.fatouSecondDerivWStrip
import Submission.Work.FatouL1.unitShiftDerivBound
import Submission.Work.FatouWindow.fatouMassMBound

/-!
# `fatouSecondDerivWideBound`: `‖Φ''‖ ≤ 1/100` on the wide strip

Target (do not restate).

Route: with `u := Φ' - 1` and `m := Δ₁ u` for `Φ = fatouCoord hadm hF`,

1. Cauchy–Heine rigidity + the *first-derivative* `π`-trick (no `π` factor!) give
   `‖Φ'' z‖ = ‖u' z‖ ≤ sup_y ‖m (z - 1/2 + i y)‖` on `(x₀-1/2, x₀+5/2)`;
2. a pointwise bound `‖m w‖ ≤ (1/32) S + (1/136) P` on the shift range, where
   `S ≥ sup_Reg ‖Φ''‖` and `P ≥ sup_Reg ‖Φ'‖` on `Reg = (x₀-1/8, x₀+19/8)`;
3. the second-order Abel/Taylor bound gives `P ≤ (32/31) (32/31 + (33/64) S)`;
4. the fixed point closes: `S ≤ S/32 + (1/136) P ≤ 1/120`, hence `‖Φ'' z‖ ≤ 1/100` on `wStrip x₀`.
-/

open MandelDim Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Work.FatouWindow

open Work.FatouL1

set_option linter.unusedVariables false

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
variable (hadm : MandelDim.QAdm b₁ b₂)
variable (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))

/-! ## The regions -/

/-- The `S`/`P` region `(x₀ - 1/8, x₀ + 19/8)`, containing `wStrip x₀`. -/
def regS (x₀ : ℝ) : Set ℂ := strip (x₀ - 1 / 8) (x₀ + 19 / 8)

lemma mem_regS {z : ℂ} : z ∈ regS x₀ ↔ x₀ - 1 / 8 < z.re ∧ z.re < x₀ + 19 / 8 := Iff.rfl

lemma regS_isOpen (x₀ : ℝ) : IsOpen (regS x₀) := strip_isOpen

lemma regS_convex (x₀ : ℝ) : Convex ℝ (regS x₀) := by
  have h : regS x₀ = Complex.reLm ⁻¹' Set.Ioo (x₀ - 1 / 8) (x₀ + 19 / 8) := by
    ext z; simp [regS, strip]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.reLm

lemma wStrip_subset_regS (x₀ : ℝ) : wStrip x₀ ⊆ regS x₀ := by
  intro z hz
  have h := mem_wStrip.mp hz
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma regS_subset_wsPi' (x₀ : ℝ) : regS x₀ ⊆ strip (wsA x₀ + 1 / 2) (wsB x₀ + 1 / 2) := by
  intro z hz
  have h := hz
  simp only [regS, mem_strip, wsA, wsB] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma regS_subset_wsQ' (x₀ : ℝ) : regS x₀ ⊆ wsQ x₀ := by
  intro z hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

lemma regS_subset_wide (x₀ : ℝ) :
    regS x₀ ⊆ {z : ℂ | x₀ - 3 / 4 < z.re ∧ z.re < x₀ + 3} := by
  intro z hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- The convex combination form of a segment. -/
lemma re_smul_segment (a b : ℂ) (t : ℝ) : (1 - t) • a + t • b = a + t • (b - a) := by
  rw [sub_smul, one_smul, smul_sub]
  abel

/-! ## The cocycle identity in increment form and the fundamental theorem of calculus -/

theorem fatouU_sub_eq {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hzF : F z ∈ MandelDim.Qreg b₁ b₂) :
    fatouU hadm hF z - fatouU hadm hF (F z)
      = (deriv F z - 1) * deriv (fatouCoord hadm hF) (F z) := by
  have h := derivCocycleProduct (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := fatouCoord hadm hF)
    (fatouCoord_spec hadm hF) hF.1.1 hz hzF
  simp only [fatouU]
  rw [h]; ring

/-- `u = Φ' - 1` is a derivative: its increment along a segment inside the strip is the integral
of `Φ''`. -/
theorem deriv_sub_eq_integral (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {a b : ℂ} (ha : a ∈ wsQ x₀) (hb : b ∈ wsQ x₀) :
    deriv (fatouCoord hadm hF) b - deriv (fatouCoord hadm hF) a
      = (b - a) * ∫ t in (0 : ℝ)..1,
          iteratedDeriv 2 (fatouCoord hadm hF) (a + t • (b - a)) := by
  have hΦ := fatouCoord_spec hadm hF
  have hd : DifferentiableOn ℂ (fatouCoord hadm hF) (wsQ x₀) :=
    hΦ.1.mono (wsQ_subset_Qreg h₁ h₂)
  have hd1 : DifferentiableOn ℂ (deriv (fatouCoord hadm hF)) (wsQ x₀) :=
    hd.deriv (wsQ_isOpen x₀)
  have h := sub_eq_integral_deriv_ball (f := deriv (fatouCoord hadm hF)) (U := wsQ x₀)
    (wsQ_isOpen x₀) (wsQ_convex x₀) ha hb hd1
  have h2 : iteratedDeriv 2 (fatouCoord hadm hF) = deriv (deriv (fatouCoord hadm hF)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_one]
  rwa [← h2] at h

/-- The second derivative of the Fatou coordinate is the derivative of `u = Φ' - 1`. -/
lemma deriv_fatouU_eq {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) :
    deriv (fatouU hadm hF) z = iteratedDeriv 2 (fatouCoord hadm hF) z := by
  have hΦ := fatouCoord_spec hadm hF
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg_derivCocycle b₁ b₂
  have hd1 : DifferentiableOn ℂ (deriv (fatouCoord hadm hF)) (MandelDim.Qreg b₁ b₂) :=
    hΦ.1.deriv hQ
  have h2 : iteratedDeriv 2 (fatouCoord hadm hF) = deriv (deriv (fatouCoord hadm hF)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_one]
  have hsub : fatouU hadm hF = (deriv (fatouCoord hadm hF)) - fun _ : ℂ => (1 : ℂ) := by
    funext y; simp only [fatouU, Pi.sub_apply]
  rw [hsub, deriv_sub (hd1.differentiableAt (hQ.mem_nhds hz)) (differentiableAt_const 1),
    deriv_const, sub_zero, h2]

/-- Integrability of `Φ''` along a segment in the strip (needed for the interval estimates). -/
lemma intervalIntegrable_iteratedDeriv_segment (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) (a b : ℂ)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → a + t • (b - a) ∈ wsQ x₀) :
    IntervalIntegrable (fun t : ℝ => ‖iteratedDeriv 2 (fatouCoord hadm hF)
      (a + t • (b - a))‖) MeasureTheory.volume (0 : ℝ) 1 := by
  have hΦ := fatouCoord_spec hadm hF
  have hd2 : DifferentiableOn ℂ (iteratedDeriv 2 (fatouCoord hadm hF)) (wsQ x₀) := by
    have hd1 : DifferentiableOn ℂ (deriv (deriv (fatouCoord hadm hF))) (wsQ x₀) :=
      ((hΦ.1.mono (wsQ_subset_Qreg h₁ h₂)).deriv (wsQ_isOpen x₀)).deriv (wsQ_isOpen x₀)
    rwa [show iteratedDeriv 2 (fatouCoord hadm hF)
        = deriv (deriv (fatouCoord hadm hF)) from by
          rw [iteratedDeriv_succ', iteratedDeriv_one]]
  exact ((hd2.continuousOn.comp (by fun_prop) hseg).norm).intervalIntegrable_of_Icc (by norm_num)

/-- The integral of `Φ''` along a segment in `regS` is bounded by `S`. -/
lemma norm_integral_iteratedDeriv_le {S : ℝ} (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    {a b : ℂ} (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → a + t • (b - a) ∈ regS x₀) :
    ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF) (a + t • (b - a))‖ ≤ S := by
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDeriv 2 (fatouCoord hadm hF) (a + t • (b - a))‖ ≤ S := fun t ht => hS _ (hseg t ht)
  have hint : IntervalIntegrable (fun t : ℝ => ‖iteratedDeriv 2 (fatouCoord hadm hF)
      (a + t • (b - a))‖) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_iteratedDeriv_segment (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ a b (fun t ht => regS_subset_wsQ' x₀ (hseg t ht))
  calc ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF) (a + t • (b - a))‖
      ≤ ∫ t in (0 : ℝ)..1, ‖iteratedDeriv 2 (fatouCoord hadm hF) (a + t • (b - a))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, S :=
        intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const hpt
    _ = S := by simp

/-! ## The pointwise bound for `m = Δ₁ u` -/

/-- **Forward expansion of `m w`**, used when the tiny segment `[F w, w+1]` stays in `Reg`. -/
theorem fatouM_le_forward (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {S P : ℝ} (hSnn : 0 ≤ S) (hPnn : 0 ≤ P)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    (hP : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ P)
    {w : ℂ} (hw₁ : x₀ - 5 / 8 < w.re) (hw₂ : w.re < x₀ + 43 / 32) :
    ‖fatouM hadm hF w‖ ≤ 1 / 32 * S + 1 / 136 * P := by
  have hΦ := fatouCoord_spec hadm hF
  have hwQ : w ∈ MandelDim.Qreg b₁ b₂ :=
    mem_Qreg_of_re_strip h₁ h₂ (by linarith) (by linarith)
  obtain ⟨hre₁, hre₂⟩ := re_step (F := F) hF.1 hwQ
  have hFwQ : F w ∈ MandelDim.Qreg b₁ b₂ :=
    mem_Qreg_of_re_strip h₁ h₂ (by linarith) (by linarith)
  -- memberships of the two endpoints of the segment
  have hFwreg : F w ∈ regS x₀ := by
    rw [mem_regS]
    exact ⟨by linarith [hre₁], by linarith [hre₂, hw₂]⟩
  have hw1reg : w + 1 ∈ regS x₀ := by
    have h1 : (w + 1).re = w.re + 1 := by simp
    rw [mem_regS, h1]
    exact ⟨by linarith, by linarith⟩
  have hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → F w + t • ((w + 1) - F w) ∈ regS x₀ := by
    intro t ht
    rw [← re_smul_segment (F w) (w + 1) t]
    exact (convex_iff_add_mem.mp (regS_convex x₀)) hFwreg hw1reg
      (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
  have hInt : ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF)
      (F w + t • ((w + 1) - F w))‖ ≤ S :=
    norm_integral_iteratedDeriv_le (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hS hseg
  -- first difference: integral over `[F w, w+1]`
  have hftc := deriv_sub_eq_integral (b₁ := b₁) (b₂ := b₂) (F := F)
    (hadm := hadm) (hF := hF) h₁ h₂ (a := F w) (b := w + 1)
    (regS_subset_wsQ' x₀ (by simpa using hseg 0 (by norm_num)))
    (regS_subset_wsQ' x₀ (by simpa using hseg 1 (by norm_num)))
  have hnorm1 : ‖fatouU hadm hF (w + 1) - fatouU hadm hF (F w)‖ ≤ 1 / 32 * S := by
    have hfirst : fatouU hadm hF (w + 1) - fatouU hadm hF (F w)
        = deriv (fatouCoord hadm hF) (w + 1) - deriv (fatouCoord hadm hF) (F w) := by
      simp only [fatouU]; ring
    rw [hfirst, hftc, norm_mul]
    have hlen : ‖(w + 1) - F w‖ ≤ 1 / 32 := by
      have h1 := (hF.1.2 w hwQ).1
      have heq : (w + 1) - F w = - (F w - (w + 1)) := by ring
      rw [heq, norm_neg]
      exact h1
    calc ‖(w + 1) - F w‖ * ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF)
          (F w + t • ((w + 1) - F w))‖
        ≤ (1 / 32) * S := mul_le_mul hlen hInt (norm_nonneg _) (by norm_num)
      _ = 1 / 32 * S := by ring
  -- second difference: the cocycle at `w`
  have hcoc := fatouU_sub_eq (b₁ := b₁) (b₂ := b₂) (F := F)
    (hadm := hadm) (hF := hF) hwQ hFwQ
  have hnorm2 : ‖fatouU hadm hF (F w) - fatouU hadm hF w‖ ≤ 1 / 136 * P := by
    have heq : fatouU hadm hF (F w) - fatouU hadm hF w
        = -((deriv F w - 1) * deriv (fatouCoord hadm hF) (F w)) := by
      rw [← hcoc]; ring
    rw [heq, norm_neg, norm_mul]
    have hg : ‖deriv F w - 1‖ ≤ 1 / 136 :=
      wDerivSubOne_le_136 (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
        hadm hF h₁ h₂ hw₁ (by linarith)
    have hΦ' : ‖deriv (fatouCoord hadm hF) (F w)‖ ≤ P := hP (F w) hFwreg
    calc ‖deriv F w - 1‖ * ‖deriv (fatouCoord hadm hF) (F w)‖
        ≤ (1 / 136) * P := mul_le_mul hg hΦ' (norm_nonneg _) (by norm_num)
      _ = 1 / 136 * P := by ring
  have hsplit : fatouM hadm hF w
      = (fatouU hadm hF (w + 1) - fatouU hadm hF (F w))
        + (fatouU hadm hF (F w) - fatouU hadm hF w) := by
    simp only [fatouM]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  linarith

/-- **Backward expansion of `m w`**, used for `Re w` in the right part of the shift range: with
`w'` the unique preimage of `w+1` in `ball w (1/32)`, one has
`m w = (u (w+1) - u w') + (u w' - u w)`. -/
theorem fatouM_le_backward (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {S P : ℝ} (hSnn : 0 ≤ S) (hPnn : 0 ≤ P)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    (hP : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ P)
    {w : ℂ} (hw₁ : x₀ + 43 / 32 ≤ w.re) (hw₂ : w.re < x₀ + 15 / 8) :
    ‖fatouM hadm hF w‖ ≤ 1 / 32 * S + 1 / 136 * P := by
  have hΦ := fatouCoord_spec hadm hF
  have hwQ : w ∈ MandelDim.Qreg b₁ b₂ :=
    mem_Qreg_of_re_strip h₁ h₂ (by linarith) (by linarith)
  have hball : Metric.closedBall ((w + 1) - 1) (1 / 32) ⊆ wsQ x₀ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : |(y - ((w + 1) - 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) hy
    have h2 : (y - ((w + 1) - 1)).re = y.re - w.re := by simp
    rw [h2, abs_le] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  obtain ⟨w', hw'ball, hFw'⟩ := (preimage_nearTranslation (F := F) (U := wsQ x₀) (z₀ := w + 1)
    (wsQ_isOpen x₀) (wsQ_convex x₀) (hF.1.1.mono (wsQ_subset_Qreg h₁ h₂))
    (fun z hz => (hF.1.2 z (wsQ_subset_Qreg h₁ h₂ hz)).1)
    (fun z hz => (hF.1.2 z (wsQ_subset_Qreg h₁ h₂ hz)).2) hball).exists
  have hw'dist : ‖w' - w‖ ≤ 1 / 32 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw'ball
    simpa using hw'ball
  have hw're' : |w'.re - w.re| ≤ 1 / 32 := by
    have h1 := le_trans (Complex.abs_re_le_norm (w' - w)) hw'dist
    have h2 : (w' - w).re = w'.re - w.re := by simp
    rwa [h2] at h1
  have hw're₁ : w'.re ≤ w.re + 1 / 32 := by linarith [(abs_le.mp hw're').2]
  have hw're₂ : w.re - 1 / 32 ≤ w'.re := by linarith [(abs_le.mp hw're').1]
  have hwreg : w ∈ regS x₀ := by
    rw [mem_regS]
    exact ⟨by linarith, by linarith⟩
  have hw'reg : w' ∈ regS x₀ := by
    rw [mem_regS]
    exact ⟨by linarith [hw're₂], by linarith [hw're₁, hw₂]⟩
  have hw'Q : w' ∈ MandelDim.Qreg b₁ b₂ :=
    wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hw'reg)
  have hFw'Q : w + 1 ∈ MandelDim.Qreg b₁ b₂ := by
    have h1 : (w + 1).re = w.re + 1 := by simp
    refine mem_Qreg_of_re_strip h₁ h₂ ?_ ?_ <;> rw [h1] <;> linarith
  have hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → w + t • (w' - w) ∈ regS x₀ := by
    intro t ht
    rw [← re_smul_segment w w' t]
    exact (convex_iff_add_mem.mp (regS_convex x₀)) hwreg hw'reg
      (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
  have hInt : ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF) (w + t • (w' - w))‖ ≤ S :=
    norm_integral_iteratedDeriv_le (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hS hseg
  have hftc := deriv_sub_eq_integral (b₁ := b₁) (b₂ := b₂) (F := F)
    (hadm := hadm) (hF := hF) h₁ h₂ (a := w) (b := w')
    (regS_subset_wsQ' x₀ (by simpa using hseg 0 (by norm_num)))
    (regS_subset_wsQ' x₀ (by simpa using hseg 1 (by norm_num)))
  have hnorm2 : ‖fatouU hadm hF w' - fatouU hadm hF w‖ ≤ 1 / 32 * S := by
    have hfirst : fatouU hadm hF w' - fatouU hadm hF w
        = deriv (fatouCoord hadm hF) w' - deriv (fatouCoord hadm hF) w := by
      simp only [fatouU]; ring
    rw [hfirst, hftc, norm_mul]
    calc ‖w' - w‖ * ‖∫ t in (0 : ℝ)..1, iteratedDeriv 2 (fatouCoord hadm hF)
          (w + t • (w' - w))‖
        ≤ (1 / 32) * S := mul_le_mul hw'dist hInt (norm_nonneg _) (by norm_num)
      _ = 1 / 32 * S := by ring
  have hcoc := fatouU_sub_eq (b₁ := b₁) (b₂ := b₂) (F := F)
    (hadm := hadm) (hF := hF) hw'Q (by rw [hFw']; exact hFw'Q)
  have hnorm1 : ‖fatouU hadm hF (w + 1) - fatouU hadm hF w'‖ ≤ 1 / 136 * P := by
    have hval : fatouU hadm hF (w + 1) - fatouU hadm hF w'
        = -((deriv F w' - 1) * deriv (fatouCoord hadm hF) (w + 1)) := by
      rw [hFw'] at hcoc
      rw [← hcoc]; ring
    rw [hval, norm_neg, norm_mul]
    have hg : ‖deriv F w' - 1‖ ≤ 1 / 150 := by
      refine wDerivSubOne_le (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
        hadm hF h₁ h₂ ?_ ?_
      · rw [mem_regS] at hw'reg; linarith [hw'reg.1]
      · rw [mem_regS] at hw'reg; linarith [hw'reg.2]
    have hF'ge : (31 : ℝ) / 32 ≤ ‖deriv F w'‖ := by
      have h1 := (hF.1.2 w' hw'Q).2
      have h := abs_norm_sub_norm_le (deriv F w') (1 : ℂ)
      rw [norm_one] at h
      linarith [(abs_le.mp h).1]
    have hF'pos : 0 < ‖deriv F w'‖ := by linarith
    have hF'ne : deriv F w' ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hF'pos
      linarith
    have hcoc' : deriv (fatouCoord hadm hF) w' = deriv (fatouCoord hadm hF) (w + 1) * deriv F w' := by
      have h := derivCocycleProduct (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := fatouCoord hadm hF)
        hΦ hF.1.1 hw'Q (by rw [hFw']; exact hFw'Q)
      rwa [hFw'] at h
    have hΦ' : ‖deriv (fatouCoord hadm hF) (w + 1)‖ ≤ 32 / 31 * P := by
      have hval' : deriv (fatouCoord hadm hF) (w + 1)
          = deriv (fatouCoord hadm hF) w' / deriv F w' := by
        rw [eq_div_iff hF'ne]
        exact hcoc'.symm
      rw [hval', norm_div, div_le_iff₀ hF'pos]
      have hnum : ‖deriv (fatouCoord hadm hF) w'‖ ≤ P := hP w' hw'reg
      have hstep : (32 / 31 * P) * (31 / 32) ≤ (32 / 31 * P) * ‖deriv F w'‖ :=
        mul_le_mul_of_nonneg_left hF'ge (by positivity)
      have h32 : (32 / 31 * P) * (31 / 32) = P := by ring
      linarith [hnum, hstep, h32.symm.le, h32.le]
    calc ‖deriv F w' - 1‖ * ‖deriv (fatouCoord hadm hF) (w + 1)‖
        ≤ (1 / 150) * (32 / 31 * P) := mul_le_mul hg hΦ' (norm_nonneg _) (by norm_num)
      _ = (32 / 4650) * P := by ring
      _ ≤ 1 / 136 * P := by nlinarith [hPnn]
  have hsplit : fatouM hadm hF w
      = (fatouU hadm hF (w + 1) - fatouU hadm hF w')
        + (fatouU hadm hF w' - fatouU hadm hF w) := by
    simp only [fatouM]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  linarith

/-- **Pointwise bound for `m = Δ₁ u`** on the shift range `(x₀-5/8, x₀+15/8)`: the range of the
shifted lines `Re z - 1/2` for `z ∈ regS x₀`. -/
theorem fatouM_le (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {S P : ℝ} (hSnn : 0 ≤ S) (hPnn : 0 ≤ P)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    (hP : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ P)
    {w : ℂ} (hw₁ : x₀ - 5 / 8 < w.re) (hw₂ : w.re < x₀ + 15 / 8) :
    ‖fatouM hadm hF w‖ ≤ 1 / 32 * S + 1 / 136 * P := by
  rcases lt_or_ge w.re (x₀ + 43 / 32) with h | h
  · exact fatouM_le_forward (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hadm hF h₁ h₂
      hSnn hPnn hS hP hw₁ h
  · exact fatouM_le_backward (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hadm hF h₁ h₂
      hSnn hPnn hS hP h hw₂

/-! ## The derivative bound `P ≤ (32/31)(32/31 + (33/64) S)` -/

/-- The direct (Taylor) bound at a point `ζ` whose forward segment `[ζ, F ζ]` lies in
`regS x₀`. -/
theorem fatouDeriv_le_of_segment (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {S : ℝ} (hSnn : 0 ≤ S)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    {ζ : ℂ} (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ζ + t • (F ζ - ζ) ∈ regS x₀) :
    ‖deriv (fatouCoord hadm hF) ζ‖ ≤ 32 / 31 + 33 / 64 * S := by
  have hΦ := fatouCoord_spec hadm hF
  have hζreg : ζ ∈ regS x₀ := by simpa using hseg 0 (by norm_num)
  have hFζreg : F ζ ∈ regS x₀ := by simpa using hseg 1 (by norm_num)
  have hζQ : ζ ∈ MandelDim.Qreg b₁ b₂ := wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hζreg)
  have hFζQ : F ζ ∈ MandelDim.Qreg b₁ b₂ := wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hFζreg)
  have hAbel : fatouCoord hadm hF (ζ + (F ζ - ζ)) = fatouCoord hadm hF ζ + 1 := by
    rw [show ζ + (F ζ - ζ) = F ζ from by ring]
    exact hΦ.2.2 ζ hζQ hFζQ
  have hsegQ : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ζ + t • (F ζ - ζ) ∈ wsQ x₀ :=
    fun t ht => regS_subset_wsQ' x₀ (hseg t ht)
  have h2 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDeriv 2 (fatouCoord hadm hF) (ζ + t • (F ζ - ζ))‖ ≤ S :=
    fun t ht => hS _ (hseg t ht)
  have hT := normOneSubMulDerivLe (wsQ_isOpen x₀) (hΦ.1.mono (wsQ_subset_Qreg h₁ h₂)) hsegQ h2 hAbel
  have hv1 : ‖(F ζ - ζ) - 1‖ ≤ 1 / 32 := by
    have h1 := (hF.1.2 ζ hζQ).1
    have heq : F ζ - (ζ + 1) = (F ζ - ζ) - 1 := by ring
    rwa [heq] at h1
  have hv : (31 : ℝ) / 32 ≤ ‖F ζ - ζ‖ := by
    have h := abs_norm_sub_norm_le (F ζ - ζ) (1 : ℂ)
    rw [norm_one] at h
    linarith [(abs_le.mp h).1]
  have hvpos : 0 < ‖F ζ - ζ‖ := by linarith
  have hvub : ‖F ζ - ζ‖ ≤ 33 / 32 := by
    have h := abs_norm_sub_norm_le (F ζ - ζ) (1 : ℂ)
    rw [norm_one] at h
    linarith [(abs_le.mp h).2]
  have hne : F ζ - ζ ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hvpos
    linarith
  have hmain : ‖deriv (fatouCoord hadm hF) ζ - 1 / (F ζ - ζ)‖ ≤ 33 / 64 * S := by
    have hdiv : deriv (fatouCoord hadm hF) ζ - 1 / (F ζ - ζ)
        = ((F ζ - ζ) * deriv (fatouCoord hadm hF) ζ - 1) / (F ζ - ζ) := by
      rw [eq_div_iff hne]
      field_simp
    rw [hdiv, norm_div, div_le_iff₀ hvpos]
    have hstep : ‖F ζ - ζ‖ * (S / 2) ≤ (33 / 64) * S := by nlinarith [hvub, hSnn]
    have hnn : ‖(F ζ - ζ) * deriv (fatouCoord hadm hF) ζ - 1‖
        = ‖1 - (F ζ - ζ) * deriv (fatouCoord hadm hF) ζ‖ := norm_sub_rev _ _
    rw [hnn]
    calc ‖1 - (F ζ - ζ) * deriv (fatouCoord hadm hF) ζ‖
        ≤ ‖F ζ - ζ‖ ^ 2 * (S / 2) := hT
      _ = ‖F ζ - ζ‖ * (‖F ζ - ζ‖ * (S / 2)) := by ring
      _ ≤ ‖F ζ - ζ‖ * ((33 / 64) * S) := mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = (33 / 64 * S) * ‖F ζ - ζ‖ := by ring
  have hinv : ‖1 / (F ζ - ζ)‖ ≤ 32 / 31 := by
    rw [norm_div, norm_one, div_le_iff₀ hvpos]
    nlinarith [hv]
  have hfin : 33 / 64 * S + 32 / 31 ≤ 32 / 31 + 33 / 64 * S := by linarith
  refine le_trans ?_ hfin
  calc ‖deriv (fatouCoord hadm hF) ζ‖
      ≤ ‖deriv (fatouCoord hadm hF) ζ - 1 / (F ζ - ζ)‖ + ‖1 / (F ζ - ζ)‖ := by
        have h := norm_add_le (deriv (fatouCoord hadm hF) ζ - 1 / (F ζ - ζ)) (1 / (F ζ - ζ))
        rwa [sub_add_cancel] at h
    _ ≤ 33 / 64 * S + 32 / 31 := add_le_add hmain hinv

/-- **`Φ'` in terms of `S`.**  For every `ζ ∈ regS x₀`, `‖Φ' ζ‖ ≤ (32/31)(32/31 + (33/64)S)`:
if the forward segment `[ζ, F ζ]` lies in `regS` (i.e. `Re ζ < x₀ + 43/32`) we use the Taylor
bound directly; otherwise we move back to the unique predecessor `ζ'` of `ζ` in `ball (ζ-1) (1/32)`
and use the cocycle at `ζ'` together with the Taylor bound on the segment `[ζ', ζ]`. -/
theorem fatouDeriv_le (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {S : ℝ} (hSnn : 0 ≤ S)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S) :
    ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ 32 / 31 * (32 / 31 + 33 / 64 * S) := by
  intro ζ hζ
  have hζQ0 : ζ ∈ MandelDim.Qreg b₁ b₂ := wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hζ)
  have hmono : ∀ x : ℝ, 0 ≤ x → 32 / 31 + 33 / 64 * x ≤ 32 / 31 * (32 / 31 + 33 / 64 * x) := by
    intro x hx
    have hkey : 32 / 31 * (32 / 31 + 33 / 64 * x) = 1024 / 961 + (33 / 62) * x := by ring
    have hc : (32 : ℝ) / 31 ≤ 1024 / 961 := by norm_num
    have hx1 : 33 / 64 * x ≤ 33 / 62 * x := by nlinarith [hx]
    rw [hkey]
    linarith
  rcases lt_or_ge ζ.re (x₀ + 43 / 32) with hlt | hge
  · -- the forward segment stays in `regS`
    obtain ⟨hr₁, hr₂⟩ := re_step (F := F) hF.1 hζQ0
    have hFζreg : F ζ ∈ regS x₀ := by
      rw [mem_regS]
      exact ⟨by linarith [hr₁, hζ.1], by linarith [hr₂, hlt]⟩
    have hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ζ + t • (F ζ - ζ) ∈ regS x₀ := by
      intro t ht
      rw [← re_smul_segment ζ (F ζ) t]
      exact (convex_iff_add_mem.mp (regS_convex x₀)) hζ hFζreg
        (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
    exact le_trans (fatouDeriv_le_of_segment (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hSnn hS hseg) (hmono S hSnn)
  · -- move back to the predecessor
    have hΦ := fatouCoord_spec hadm hF
    have hball : Metric.closedBall (ζ - 1) (1 / 32) ⊆ wsQ x₀ := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      have h1 : |(y - (ζ - 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) hy
      have h2 : (y - (ζ - 1)).re = y.re - (ζ.re - 1) := by
        rw [Complex.sub_re, Complex.sub_re, Complex.one_re]
      rw [h2, abs_le] at h1
      refine ⟨?_, ?_⟩ <;> linarith [h1.1, h1.2, hζ.1, hζ.2]
    obtain ⟨ζ', hζ'ball, hFζ'⟩ := (preimage_nearTranslation (F := F) (U := wsQ x₀) (z₀ := ζ)
      (wsQ_isOpen x₀) (wsQ_convex x₀) (hF.1.1.mono (wsQ_subset_Qreg h₁ h₂))
      (fun z hz => (hF.1.2 z (wsQ_subset_Qreg h₁ h₂ hz)).1)
      (fun z hz => (hF.1.2 z (wsQ_subset_Qreg h₁ h₂ hz)).2) hball).exists
    have hζ'dist : ‖ζ' - (ζ - 1)‖ ≤ 1 / 32 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hζ'ball
      exact hζ'ball
    have hζ're : |ζ'.re - (ζ.re - 1)| ≤ 1 / 32 := by
      have h1 := le_trans (Complex.abs_re_le_norm (ζ' - (ζ - 1))) hζ'dist
      have h2 : (ζ' - (ζ - 1)).re = ζ'.re - (ζ.re - 1) := by
        rw [Complex.sub_re, Complex.sub_re, Complex.one_re]
      rwa [h2] at h1
    have hζ're₁ : ζ'.re ≤ ζ.re - 31 / 32 := by linarith [(abs_le.mp hζ're).2]
    have hζ're₂ : ζ.re - 33 / 32 ≤ ζ'.re := by linarith [(abs_le.mp hζ're).1]
    have hζ'reg : ζ' ∈ regS x₀ := by
      rw [mem_regS]
      exact ⟨by linarith [hζ're₂, hζ.1], by linarith [hζ're₁, hζ.2]⟩
    have hζ'Q : ζ' ∈ MandelDim.Qreg b₁ b₂ := wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hζ'reg)
    -- the segment `[ζ', F ζ'] = [ζ', ζ]` lies in `regS`
    have hseg' : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ζ' + t • (F ζ' - ζ') ∈ regS x₀ := by
      intro t ht
      rw [hFζ', ← re_smul_segment ζ' ζ t]
      exact (convex_iff_add_mem.mp (regS_convex x₀)) hζ'reg hζ
        (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
    have hdir := fatouDeriv_le_of_segment (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hSnn hS hseg'
    have hcoc' : deriv (fatouCoord hadm hF) ζ' = deriv (fatouCoord hadm hF) ζ * deriv F ζ' := by
      have h := derivCocycleProduct (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := fatouCoord hadm hF)
        hΦ hF.1.1 hζ'Q (by rw [hFζ']; exact hζQ0)
      rwa [hFζ'] at h
    have hF'ge : (31 : ℝ) / 32 ≤ ‖deriv F ζ'‖ := by
      have h1 := (hF.1.2 ζ' hζ'Q).2
      have h := abs_norm_sub_norm_le (deriv F ζ') (1 : ℂ)
      rw [norm_one] at h
      linarith [(abs_le.mp h).1]
    have hF'pos : 0 < ‖deriv F ζ'‖ := by linarith
    have hF'ne : deriv F ζ' ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hF'pos
      linarith
    have hval : deriv (fatouCoord hadm hF) ζ = deriv (fatouCoord hadm hF) ζ' / deriv F ζ' := by
      rw [eq_div_iff hF'ne]
      exact hcoc'.symm
    rw [hval, norm_div, div_le_iff₀ hF'pos]
    have hstep : (32 / 31 * (32 / 31 + 33 / 64 * S)) * (31 / 32)
        ≤ (32 / 31 * (32 / 31 + 33 / 64 * S)) * ‖deriv F ζ'‖ :=
      mul_le_mul_of_nonneg_left hF'ge (by positivity)
    have h32 : (32 / 31 * (32 / 31 + 33 / 64 * S)) * (31 / 32)
        = 32 / 31 + 33 / 64 * S := by ring
    linarith [hdir, hstep, h32.symm.le, h32.le]

/-! ## The `π`-trick: `Φ''` on `regS` in terms of `S` and `P` -/

/-- **The `π`-trick conclusion.**  With `u = Φ' - 1`, `m = Δ₁ u`, the shift rigidity on the strip
`(wsA + 1/4, wsB) = (x₀ - 3/4, x₀ + 2)` plus the *first-derivative* `π`-trick give, for
`z ∈ regS`,

`‖Φ'' z‖ = ‖u' z‖ ≤ sup_y ‖m (z - 1/2 + i y)‖ ≤ (1/32) S + (1/136) P`. -/
theorem fatouSecondDeriv_le_regS (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {m₀ B : ℝ}
    (hmass : ∀ x ∈ Set.Ioo (wsA x₀) (wsB x₀),
      MeasureTheory.Integrable (fun y : ℝ => fatouM hadm hF ((x : ℂ) + y * Complex.I)) ∧
      ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m₀)
    (hub : ∀ z : ℂ, wsA x₀ + 1 / 4 < z.re → z.re < wsB x₀ → ‖fatouU hadm hF z‖ ≤ B)
    {S P : ℝ} (hSnn : 0 ≤ S) (hPnn : 0 ≤ P)
    (hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S)
    (hP : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ P)
    {z : ℂ} (hz : z ∈ regS x₀) :
    ‖iteratedDeriv 2 (fatouCoord hadm hF) z‖ ≤ 1 / 32 * S + 1 / 136 * P := by
  have hΦ := fatouCoord_spec hadm hF
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg_derivCocycle b₁ b₂
  have hu_diff : DifferentiableOn ℂ (fatouU hadm hF) (MandelDim.Qreg b₁ b₂) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (deriv (fatouCoord hadm hF)) w :=
      ((hΦ.1.deriv hQ) w hw).differentiableAt (hQ.mem_nhds hw)
    have h2 : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) w := differentiableAt_const 1
    have h3 := h1.sub h2
    change DifferentiableWithinAt ℂ (fun z : ℂ => deriv (fatouCoord hadm hF) z - 1)
      (MandelDim.Qreg b₁ b₂) w
    exact h3.differentiableWithinAt
  have hsub : {z : ℂ | wsA x₀ + 1 / 4 < z.re ∧ z.re < wsB x₀} ⊆ MandelDim.Qreg b₁ b₂ := by
    intro w hw
    refine mem_Qreg_of_re_strip h₁ h₂ ?_ ?_
    · simp only [wsA] at hw; linarith [hw.1]
    · simp only [wsB] at hw; linarith [hw.2]
  have hsub2 : {z : ℂ | wsA x₀ + 1 / 4 + 1 / 2 < z.re ∧ z.re < wsB x₀ + 1 / 2} ⊆
      MandelDim.Qreg b₁ b₂ := by
    intro w hw
    refine mem_Qreg_of_re_strip h₁ h₂ ?_ ?_
    · simp only [wsA] at hw; linarith [hw.1]
    · simp only [wsB] at hw; linarith [hw.2]
  have hm_diff : DifferentiableOn ℂ (fatouM hadm hF)
      {z : ℂ | wsA x₀ + 1 / 4 < z.re ∧ z.re < wsB x₀} := by
    intro w hw
    have hwQ : w ∈ MandelDim.Qreg b₁ b₂ := hsub hw
    have hw1Q : w + 1 ∈ MandelDim.Qreg b₁ b₂ := by
      have h1 : (w + 1).re = w.re + 1 := by simp
      refine mem_Qreg_of_re_strip h₁ h₂ ?_ ?_ <;> rw [h1]
      · simp only [wsA] at hw; linarith [hw.1]
      · simp only [wsB] at hw; linarith [hw.2]
    have h1 : DifferentiableAt ℂ (fatouU hadm hF) w :=
      (hu_diff w hwQ).differentiableAt (hQ.mem_nhds hwQ)
    have h2 : DifferentiableAt ℂ (fatouU hadm hF) (w + 1) :=
      (hu_diff (w + 1) hw1Q).differentiableAt (hQ.mem_nhds hw1Q)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => fatouU hadm hF (w + 1)) w :=
      h2.comp w (differentiableAt_id.add_const 1)
    have h4 := h3.sub h1
    change DifferentiableWithinAt ℂ
      (fun z : ℂ => fatouU hadm hF (z + 1) - fatouU hadm hF z)
      {z : ℂ | wsA x₀ + 1 / 4 < z.re ∧ z.re < wsB x₀} w
    exact h4.differentiableWithinAt
  have heq : ∀ w : ℂ, wsA x₀ + 1 / 4 < w.re → w.re < wsB x₀ →
      fatouU hadm hF (w + 1) - fatouU hadm hF w = fatouM hadm hF w := fun w _ _ => rfl
  have hMnn : 0 ≤ 1 / 32 * S + 1 / 136 * P := by linarith
  have hM : ∀ y : ℝ, ‖fatouM hadm hF (z - 1 / 2 + y * Complex.I)‖ ≤ 1 / 32 * S + 1 / 136 * P := by
    intro y
    refine fatouM_le (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hadm hF h₁ h₂ hSnn hPnn hS hP ?_ ?_
    · have hre : (z - 1 / 2 + y * Complex.I).re = z.re - 1 / 2 := by simp
      rw [hre]; linarith [hz.1]
    · have hre : (z - 1 / 2 + y * Complex.I).re = z.re - 1 / 2 := by simp
      rw [hre]; linarith [hz.2]
  have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := wsQ_subset_Qreg h₁ h₂ (regS_subset_wsQ' x₀ hz)
  have hb := unitShiftDerivBound (a := wsA x₀ + 1 / 4) (b := wsB x₀) (m := m₀) (B := B)
    (by simp only [wsA, wsB]; linarith) (by simp only [wsA, wsB]; linarith)
    (hu_diff.mono hsub) (hu_diff.mono hsub2) hm_diff
    (fun x hx => (hmass x ⟨by linarith [hx.1], by linarith [hx.2]⟩).1)
    (fun x hx => (hmass x ⟨by linarith [hx.1], by linarith [hx.2]⟩).2) heq hub
    z (by simp only [wsA] at *; linarith [hz.1]) (by simp only [wsB] at *; linarith [hz.2])
    _ hMnn hM
  rwa [deriv_fatouU_eq (b₁ := b₁) (b₂ := b₂) (F := F) hadm hF hzQ] at hb

/-! ## Assembly -/

/-- The target, with the mass/integrability input isolated as a hypothesis. -/
theorem fatouSecondDerivWideBound_of_mass (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hmass : ∃ m₀ : ℝ, ∀ x ∈ Set.Ioo (wsA x₀) (wsB x₀),
      MeasureTheory.Integrable (fun y : ℝ => fatouM hadm hF ((x : ℂ) + y * Complex.I)) ∧
      ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouM hadm hF ((x : ℂ) + y * Complex.I)‖
        ≤ ENNReal.ofReal m₀) :
    ∃ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) ∧
      ∀ z : ℂ, z ∈ wStrip x₀ → ‖iteratedDeriv 2 Φ z‖ ≤ 1 / 100 := by
  obtain ⟨m₀, hmass⟩ := hmass
  obtain ⟨Bu, hBu⟩ := fatouU_apriori_bound_wide (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂
  obtain ⟨B1, hB1⟩ := fatouCoord_deriv_bounded_strip (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂
  have hub : ∀ z : ℂ, wsA x₀ + 1 / 4 < z.re → z.re < wsB x₀ → ‖fatouU hadm hF z‖ ≤ Bu := by
    intro z h1 h2
    refine (hBu z ?_ ?_).1
    · simp only [wsA] at h1; linarith
    · simp only [wsB] at h2; linarith
  have hzero : (x₀ : ℂ) ∈ regS x₀ := by
    rw [mem_regS, Complex.ofReal_re]; constructor <;> norm_num
  have hSbdd : BddAbove {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
      ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ = t} :=
    ⟨Bu, fun t ht => by
      obtain ⟨ζ, hζ, rfl⟩ := ht
      exact (hBu ζ (by rw [mem_regS] at hζ; linarith [hζ.1])
        (by rw [mem_regS] at hζ; linarith [hζ.2])).2⟩
  have hPbdd : BddAbove {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
      ‖deriv (fatouCoord hadm hF) ζ‖ = t} :=
    ⟨B1, fun t ht => by
      obtain ⟨ζ, hζ, rfl⟩ := ht
      exact hB1 ζ (by rw [mem_regS] at hζ; linarith [hζ.1])
        (by rw [mem_regS] at hζ; linarith [hζ.2])⟩
  have hSne : {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
      ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ = t}.Nonempty := ⟨_, x₀, hzero, rfl⟩
  have hPne : {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
      ‖deriv (fatouCoord hadm hF) ζ‖ = t}.Nonempty := ⟨_, x₀, hzero, rfl⟩
  set S : ℝ := sSup {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
    ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ = t} with hSdef
  set P : ℝ := sSup {t : ℝ | ∃ ζ : ℂ, ζ ∈ regS x₀ ∧
    ‖deriv (fatouCoord hadm hF) ζ‖ = t} with hPdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact le_trans (norm_nonneg _) (le_csSup hSbdd ⟨x₀, hzero, rfl⟩)
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact le_trans (norm_nonneg _) (le_csSup hPbdd ⟨x₀, hzero, rfl⟩)
  have hS : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖iteratedDeriv 2 (fatouCoord hadm hF) ζ‖ ≤ S := by
    intro ζ hζ
    rw [hSdef]
    exact le_csSup hSbdd ⟨ζ, hζ, rfl⟩
  have hP : ∀ ζ : ℂ, ζ ∈ regS x₀ → ‖deriv (fatouCoord hadm hF) ζ‖ ≤ P := by
    intro ζ hζ
    rw [hPdef]
    exact le_csSup hPbdd ⟨ζ, hζ, rfl⟩
  have hPbnd : P ≤ 1024 / 961 + (33 / 62) * S := by
    rw [hPdef]
    refine csSup_le hPne (fun t ht => ?_)
    obtain ⟨ζ, hζ, rfl⟩ := ht
    have h := fatouDeriv_le (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hSnn hS ζ hζ
    have hkey : 32 / 31 * (32 / 31 + 33 / 64 * S) = 1024 / 961 + (33 / 62) * S := by ring
    rwa [hkey] at h
  have hSle : S ≤ 1 / 32 * S + 1 / 136 * P := by
    rw [hSdef]
    refine csSup_le hSne (fun t ht => ?_)
    obtain ⟨ζ, hζ, rfl⟩ := ht
    exact fatouSecondDeriv_le_regS (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
      hadm hF h₁ h₂ hmass hub hSnn hPnn hS hP hζ
  have hS120 : S ≤ 1 / 120 := by
    nlinarith [hSle, hPbnd, hSnn]
  refine ⟨fatouCoord hadm hF, fatouCoord_spec hadm hF, ?_⟩
  intro z hz
  have hzreg : z ∈ regS x₀ := wStrip_subset_regS x₀ hz
  have hzle := fatouSecondDeriv_le_regS (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂ hmass hub hSnn hPnn hS hP hzreg
  have hfinal : 1 / 32 * S + 1 / 136 * P ≤ 1 / 100 := by
    nlinarith [hS120, hPbnd, hSnn]
  linarith [hzle, hfinal]

/-- **`fatouSecondDerivWideBound`**: the second derivative of the canonical Fatou coordinate is
bounded by `1/100` on the wide strip. -/
theorem fatouSecondDerivWideBound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) ∧
      ∀ z : ℂ, z ∈ Work.FatouL1.wStrip x₀ → ‖iteratedDeriv 2 Φ z‖ ≤ 1 / 100 :=
  fatouSecondDerivWideBound_of_mass (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂
    (fatouMassMBound (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hadm hF h₁ h₂)

end

end Work.FatouWindow
