import Mathlib
import Submission.Work.Drive.N2.contDiff_parametric_intervalIntegral

/-!
# Hadamard's lemma and the Alexander (radial scaling) family

Two reusable bricks for the globalisation step of the framing chart (L5,
`Work.Drive.PushDisc.exists_globalDiffeo_of_embedding`):

* `Work.Drive.PushDisc.sub_eq_integral_fderiv` -- Taylor's formula at order `0`:
  `g x - g 0 = ∫ t in 0..1, (fderiv ℝ g (t • x)) x`;
* `Work.Drive.PushDisc.hadamard` -- **Hadamard's lemma**: a `C^∞` map vanishing at the origin is
  `x ↦ G x x` for a `C^∞` map `G` into the continuous linear maps;
* `Work.Drive.PushDisc.contDiff_alexanderIntegral` and
  `Work.Drive.PushDisc.contDiff_alexanderFamily` -- the **Alexander family**
  `r ↦ r⁻¹ • g (r • ·)` (with value `fderiv ℝ g 0` at `r = 0`) is jointly `C^∞`.

All of this is proved from the already available
`Work.Drive.N2.contDiff_parametric_intervalIntegral` (smoothness of parametric interval
integrals), together with Mathlib's Taylor formula with integral remainder
(`map_add_eq_sum_add_integral_iteratedFDeriv`).
-/

namespace Work.Drive.PushDisc

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Taylor's formula at order `0`.**  For a `C^∞` map `g : E → F`,
`g x - g 0 = ∫ t in 0..1, (fderiv ℝ g (t • x)) x`. -/
theorem sub_eq_integral_fderiv (g : E → F) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : E) :
    g x - g 0 = ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • x)) x := by
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (f := g) (x := (0 : E)) (y := x)
    (n := 0) (fun t _ => hg.contDiffAt.of_le (by norm_num))
  have hT' : g x = g 0 + ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • x)) x := by simpa using hT
  rw [hT', add_sub_cancel_left]

/-- **Hadamard's lemma.**  A `C^∞` map `g : E → F` with `g 0 = 0` is `x ↦ G x x` for a `C^∞` map
`G : E → (E →L[ℝ] F)`; the witness is the parametric integral `G x = ∫ t in 0..1, fderiv ℝ g (t•x)`,
whose value at `0` is `fderiv ℝ g 0`. -/
theorem hadamard (g : E → F) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hg0 : g 0 = 0) :
    ∃ G : E → E →L[ℝ] F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      (∀ x, g x = G x x) ∧ G 0 = fderiv ℝ g 0 := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
    (contDiff_infty_iff_fderiv.mp hg).2
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ g (t • x), ?_, ?_, ?_⟩
  · refine Work.Drive.N2.contDiff_parametric_intervalIntegral (E := E) (F := E →L[ℝ] F)
      (f := fun p : E × ℝ => fderiv ℝ g (p.2 • p.1)) (a := 0) (b := 1) ?_
    fun_prop
  · intro x
    rw [ContinuousLinearMap.intervalIntegral_apply]
    · have h := sub_eq_integral_fderiv g hg x
      rw [hg0, sub_zero] at h
      exact h
    · exact (hfd.continuous.comp (continuous_id.smul continuous_const)).intervalIntegrable 0 1
  · have h1 : (fun t : ℝ => fderiv ℝ g (t • (0 : E))) = fun _ : ℝ => fderiv ℝ g 0 := by
      funext t; simp
    show (∫ t in (0 : ℝ)..1, fderiv ℝ g (t • (0 : E))) = fderiv ℝ g 0
    rw [h1]
    simp

/-- The **Alexander integral family** of a `C^∞` map `g`: the jointly `C^∞` map
`p ↦ ∫ t in 0..1, (fderiv ℝ g (t • (p.1 • p.2))) p.2`, whose value at `p.1 = 0` is
`(fderiv ℝ g 0) p.2` and which equals `r⁻¹ • g (r • x)` for `r ≠ 0` (see
`alexanderIntegral_apply_of_ne`). -/
theorem contDiff_alexanderIntegral (g : E → F) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × E => ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • (p.1 • p.2))) p.2) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
    (contDiff_infty_iff_fderiv.mp hg).2
  refine Work.Drive.N2.contDiff_parametric_intervalIntegral (E := ℝ × E) (F := F)
    (f := fun q : (ℝ × E) × ℝ => (fderiv ℝ g (q.2 • (q.1.1 • q.1.2))) q.1.2) (a := 0) (b := 1) ?_
  fun_prop

/-- For `r ≠ 0` the Alexander integral is `r⁻¹ • g (r • x)`. -/
theorem alexanderIntegral_apply_of_ne (g : E → F) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg0 : g 0 = 0) {r : ℝ} (hr : r ≠ 0) (x : E) :
    (∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • (r • x))) x) = r⁻¹ • g (r • x) := by
  have hsub := sub_eq_integral_fderiv g hg (r • x)
  rw [hg0, sub_zero] at hsub
  have h1 : (∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • (r • x))) (r • x))
      = r • ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • (r • x))) x := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp [ContinuousLinearMap.map_smul]
  rw [hsub, h1, inv_smul_smul₀ hr]

/-- **The Alexander family** `r ↦ r⁻¹ • g (r • ·)` of a `C^∞` map `g` with `g 0 = 0` (whose value
at `r = 0` is `fderiv ℝ g 0`) is jointly `C^∞`. -/
theorem contDiff_alexanderFamily (g : E → F) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg0 : g 0 = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E =>
      if p.1 = 0 then (fderiv ℝ g 0) p.2 else p.1⁻¹ • g (p.1 • p.2)) := by
  have hInt := contDiff_alexanderIntegral g hg
  have hcongr : (fun p : ℝ × E =>
        if p.1 = 0 then (fderiv ℝ g 0) p.2 else p.1⁻¹ • g (p.1 • p.2))
      = fun p : ℝ × E => ∫ t in (0 : ℝ)..1, (fderiv ℝ g (t • (p.1 • p.2))) p.2 := by
    funext p
    by_cases h : p.1 = 0
    · simp [h]
    · rw [if_neg h]
      exact (alexanderIntegral_apply_of_ne g hg hg0 h p.2).symm
  rw [hcongr]
  exact hInt

/-- The Alexander family of a self-map `g` equals `g` at `r = 1` (for `g 0 = 0`). -/
theorem alexanderFamily_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) (hg0 : g 0 = 0) (x : E) :
    (if (1 : ℝ) = 0 then (fderiv ℝ g 0) x else (1 : ℝ)⁻¹ • g ((1 : ℝ) • x)) = g x := by
  simp

/-- The Alexander family of a self-map `g` with `fderiv ℝ g 0 = 1` is the identity at `r = 0`. -/
theorem alexanderFamily_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) (h1 : fderiv ℝ g 0 = 1) (x : E) :
    (if (0 : ℝ) = 0 then (fderiv ℝ g 0) x else (0 : ℝ)⁻¹ • g ((0 : ℝ) • x)) = x := by
  simp [h1]

end Work.Drive.PushDisc
