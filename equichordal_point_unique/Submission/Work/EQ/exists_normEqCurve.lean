import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.normDefs
import Submission.Work.EQ.radFn_basic
import Submission.Work.EQ.continuous_radFn_comp
import Submission.Work.EQ.circle_param
import Submission.Work.EQ.chord_common

/-! # Normalisation of a two-point equichordal curve

Given a compact convex set `K` with nonempty interior and two distinct equichordal points
`P ≠ Q`, we produce `0 < a < 1` and radial functions `ρ₁ ρ₂` with `NormEqCurve a ρ₁ ρ₂`.

The construction: let `R_O v = 1 / gauge (K - O) v` be the radial function of `K` about the
interior point `O`.  The frontier of `K` is exactly the radial graph `O + R_O v • v` over the
unit sphere, and the equichordal hypothesis at `O` says `R_O u + R_O (-u) = L_O` for unit `u`.
The line `PQ` is a common chord, which gives `L_P = L_Q =: L` and `d := ‖Q - P‖ < L`; we set
`a := d / L`.  Finally the similarity `Φ X = (toC X - toC P) * conj c / L - a/2`, with
`c = (toC Q - toC P) / d` a unit complex number, sends `P ↦ -a/2`, `Q ↦ a/2` and `frontier K`
onto the polar graphs of `ρ₁ θ = R_P (toC.symm (exp (θ I) c)) / L` about `-a/2` and of
`ρ₂ θ = R_Q (toC.symm (exp (θ I) c)) / L` about `a/2`.
-/

namespace Work.EQ

open LeanEval.Geometry.Equichordal

set_option linter.unusedVariables false

/-- **Normalisation.** Two distinct equichordal points of a convex body give, after a
similarity putting them at `∓a/2` on the real axis of `ℂ` and scaling the common chord length
to `1`, a normalised two-point equichordal curve with `0 < a < 1`. -/
theorem exists_normEqCurve {K : Set Plane} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) {P Q : Plane} (hPQ : P ≠ Q)
    (hP : IsEquichordalPoint K P) (hQ : IsEquichordalPoint K Q) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ ρ₁ ρ₂ : ℝ → ℝ, NormEqCurve a ρ₁ ρ₂ := by
  have hPint : P ∈ interior K := hP.1
  have hQint : Q ∈ interior K := hQ.1
  have hRposP := (radFn_basic hK hconv hPint).1
  have hRP := (radFn_basic hK hconv hPint).2.1
  have hRsphereP := (radFn_basic hK hconv hPint).2.2
  have hRposQ := (radFn_basic hK hconv hQint).1
  have hRQ := (radFn_basic hK hconv hQint).2.1
  have hRsphereQ := (radFn_basic hK hconv hQint).2.2
  obtain ⟨L, hLpos, hPsum, hQsum, hdL⟩ := chord_common hK hconv hPQ hP hQ hRP hRQ
  have hLne : L ≠ 0 := ne_of_gt hLpos
  set d : ℝ := ‖Q - P‖ with hd
  have hdpos : 0 < d := by rw [hd]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hPQ))
  set a : ℝ := d / L with ha
  have hapos : 0 < a := by rw [ha]; exact div_pos hdpos hLpos
  have halt : a < 1 := by rw [ha, div_lt_one hLpos]; exact hdL
  -- complex setup
  set w : ℂ := toC Q - toC P with hw
  set cc : ℂ := w / (d : ℂ) with hcc
  set Ψ : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * Complex.I) with hΨ
  set uv : ℝ → Plane := fun θ => toC.symm (Ψ θ * cc) with huv
  set Φ : Plane → ℂ := fun X => (toC X - toC P) * (starRingEnd ℂ) cc / (L : ℂ) - ((a / 2 : ℝ) : ℂ)
    with hΦ
  set ρ₁ : ℝ → ℝ := fun θ => radFn K P (uv θ) / L with hρ₁
  set ρ₂ : ℝ → ℝ := fun θ => radFn K Q (uv θ) / L with hρ₂
  have hwd : ‖w‖ = d := by
    rw [hw, ← toC.map_sub, toC.norm_map, hd]
  have hcd : ‖((d : ℝ) : ℂ)‖ = d := by
    have h2 : ‖((d : ℝ) : ℂ)‖ ^ 2 = d ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    nlinarith [norm_nonneg ((d : ℝ) : ℂ), hdpos]
  have hccnorm : ‖cc‖ = 1 := by
    rw [hcc, norm_div, hwd, hcd, div_self (ne_of_gt hdpos)]
  have hcc1 : cc * (starRingEnd ℂ) cc = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hccnorm, one_pow, Complex.ofReal_one]
  have hwcc : w * (starRingEnd ℂ) cc = (d : ℂ) := by
    have hdz : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
    have h1 : w * (starRingEnd ℂ) w = ((d : ℝ) : ℂ) * ((d : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwd]
      push_cast
      ring
    rw [hcc]
    simp only [map_div₀, Complex.conj_ofReal]
    rw [mul_div_assoc', h1, mul_div_assoc, div_self hdz, mul_one]
  have h1gen : ∀ (θ : ℝ) (r : ℝ), (((r : ℝ) : ℂ) *
        (Complex.exp ((θ : ℂ) * Complex.I) * cc)) * (starRingEnd ℂ) cc
      = ((r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ r
    rw [mul_assoc, mul_assoc _ cc (starRingEnd ℂ cc), hcc1, mul_one]
  have huv_apply : ∀ θ, toC (uv θ) = Ψ θ * cc := by
    intro θ
    rw [huv]
    exact toC.apply_symm_apply _
  have huv_norm : ∀ θ, ‖uv θ‖ = 1 := by
    intro θ
    rw [← toC.norm_map (uv θ), huv_apply θ, hΨ]
    simpa using (circle_param cc hccnorm).1 θ
  have huv_sphere : ∀ θ, uv θ ∈ Metric.sphere (0 : Plane) 1 := by
    intro θ
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact huv_norm θ
  have huv_ne : ∀ θ, uv θ ≠ 0 := by
    intro θ h
    have := huv_norm θ
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  have hcont_uv : Continuous uv := by
    rw [huv]
    exact toC.symm.continuous.comp
      ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const)
  have hρ₁cont : Continuous ρ₁ := by
    rw [hρ₁]
    exact (continuous_radFn_comp hK hconv hPint hcont_uv huv_sphere).div_const L
  have hρ₂cont : Continuous ρ₂ := by
    rw [hρ₂]
    exact (continuous_radFn_comp hK hconv hQint hcont_uv huv_sphere).div_const L
  have hρ₁pos : ∀ θ, 0 < ρ₁ θ := by
    intro θ
    rw [hρ₁]
    exact div_pos (hRposP (uv θ) (huv_ne θ)) hLpos
  have hρ₂pos : ∀ θ, 0 < ρ₂ θ := by
    intro θ
    rw [hρ₂]
    exact div_pos (hRposQ (uv θ) (huv_ne θ)) hLpos
  have huv_anti : ∀ θ, uv (θ + Real.pi) = -uv θ := by
    intro θ
    rw [huv, hΨ]
    simp only
    rw [Complex.ofReal_add, (circle_param cc hccnorm).2.1 θ]
    exact toC.symm.map_neg _
  have hρ₁chord : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1 := by
    intro θ
    simp only [hρ₁]
    rw [huv_anti θ, ← add_div, hPsum (uv θ) (huv_sphere θ), div_self hLne]
  have hρ₂chord : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1 := by
    intro θ
    simp only [hρ₂]
    rw [huv_anti θ, ← add_div, hQsum (uv θ) (huv_sphere θ), div_self hLne]
  have keyP : ∀ θ, Φ (P + radFn K P (uv θ) • uv θ) = polarPt (-(a / 2)) (ρ₁ θ) θ := by
    intro θ
    rw [hΦ, hρ₁]
    simp only
    rw [toC.map_add, toC.map_smul, huv_apply θ, hΨ]
    simp only
    rw [add_sub_cancel_left, Complex.real_smul, h1gen θ]
    simp only [polarPt]
    push_cast
    ring
  have keyQ : ∀ θ, Φ (Q + radFn K Q (uv θ) • uv θ) = polarPt (a / 2) (ρ₂ θ) θ := by
    intro θ
    rw [hΦ, hρ₂]
    simp only
    rw [toC.map_add, toC.map_smul, huv_apply θ, hΨ]
    simp only
    rw [Complex.real_smul]
    have hqq : toC Q + ((radFn K Q (uv θ) : ℝ) : ℂ) *
        (Complex.exp ((θ : ℂ) * Complex.I) * cc) - toC P
        = w + ((radFn K Q (uv θ) : ℝ) : ℂ) *
          (Complex.exp ((θ : ℂ) * Complex.I) * cc) := by
      rw [hw]; ring
    rw [hqq, add_mul, h1gen θ, hwcc]
    simp only [polarPt]
    rw [ha]
    push_cast
    ring
  have hrangeP : Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) = Φ '' frontier K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨θ, rfl⟩
      refine ⟨P + radFn K P (uv θ) • uv θ, ?_, keyP θ⟩
      exact (hRP (uv θ) (huv_ne θ) (radFn K P (uv θ)) (hRposP (uv θ) (huv_ne θ))).mpr rfl
    · rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨v, hvsphere, rfl⟩ := (hRsphereP Y).mp hY
      have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hvsphere
      have htoCv : ‖toC v‖ = 1 := by rw [toC.norm_map]; exact hvnorm
      obtain ⟨θ, hθ⟩ := (circle_param cc hccnorm).2.2 (toC v) htoCv
      have huvθ : uv θ = v := by
        apply toC.injective
        rw [huv_apply θ, hΨ]
        simp only
        exact hθ
      have hthis : Φ (P + radFn K P v • v) = polarPt (-(a / 2)) (ρ₁ θ) θ := by
        rw [← huvθ]
        exact keyP θ
      exact ⟨θ, hthis.symm⟩
  have hrangeQ : Set.range (fun θ => polarPt (a / 2) (ρ₂ θ) θ) = Φ '' frontier K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨θ, rfl⟩
      refine ⟨Q + radFn K Q (uv θ) • uv θ, ?_, keyQ θ⟩
      exact (hRQ (uv θ) (huv_ne θ) (radFn K Q (uv θ)) (hRposQ (uv θ) (huv_ne θ))).mpr rfl
    · rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨v, hvsphere, rfl⟩ := (hRsphereQ Y).mp hY
      have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hvsphere
      have htoCv : ‖toC v‖ = 1 := by rw [toC.norm_map]; exact hvnorm
      obtain ⟨θ, hθ⟩ := (circle_param cc hccnorm).2.2 (toC v) htoCv
      have huvθ : uv θ = v := by
        apply toC.injective
        rw [huv_apply θ, hΨ]
        simp only
        exact hθ
      have hthis : Φ (Q + radFn K Q v • v) = polarPt (a / 2) (ρ₂ θ) θ := by
        rw [← huvθ]
        exact keyQ θ
      exact ⟨θ, hthis.symm⟩
  exact ⟨a, hapos, halt, ρ₁, ρ₂, hρ₁cont, hρ₂cont, hρ₁pos, hρ₂pos, hρ₁chord, hρ₂chord,
    hrangeP.trans hrangeQ.symm⟩

end Work.EQ
