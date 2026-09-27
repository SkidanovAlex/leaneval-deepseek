import Mathlib
import Submission.Work.Drive.N2.orientationFlipDefs
import Submission.Work.Drive.N2C.exists_reparam_unitCircle

/-!
# Reparametrising a periodic immersion of the circle onto the round parametrisation

`Work.N2C.reparamOnRoundCircle`: a smooth `1`-periodic curve `g : ℝ → ℝ³`, injective on `[0,1)`,
with nowhere-zero derivative, whose image lies on the round circle of radius `rad > 0` about `pos`,
is (up to the standard round parametrisation) a reparametrisation of that circle:
there are a smooth bijection `τ : ℝ → ℝ` with `τ (x+1) = τ x + ε`, `ε = ±1`, nowhere-zero
derivative, and a phase `φ` with
`g (τ x) = pos + rad • roundPic (φ + 2 π x)` for all `x`.

The proof reads `g` in the first two coordinates as a unit complex curve
`z x = rad⁻¹ • toC3 (g x - pos)` (the third coordinate of `g x - pos` vanishes because the curve
lies on the round circle), and applies the (proved) analytic input
`Work.Drive.N2C.exists_reparam_unitCircle`: a smooth `1`-periodic unit complex curve, injective on
`[0,1)` with nowhere-zero derivative, admits a smooth reparametrisation onto
`t ↦ exp (i (φ + 2 π t))`, with winding `±1`.
-/

namespace Work.N2C

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

private abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The two coordinate projections of `ℝ³` -/

/-- The last coordinate of `ℝ³`. -/
private def psi3 : E3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2

/-- The first two coordinates of `ℝ³`, read as a complex number. -/
private def toC3 : E3 →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0)) +
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1)).smulRight Complex.I)

private theorem psi3_apply (v : E3) : psi3 v = v.ofLp 2 := rfl

private theorem toC3_re (v : E3) : (toC3 v).re = v.ofLp 0 := by simp [toC3]

private theorem toC3_im (v : E3) : (toC3 v).im = v.ofLp 1 := by simp [toC3]

private theorem psi3_roundPic (t : ℝ) : psi3 (Work.Drive.N2.roundPic t) = 0 := by
  rw [psi3_apply]
  simp [Work.Drive.N2.roundPic]

private theorem toC3_roundPic (t : ℝ) :
    toC3 (Work.Drive.N2.roundPic t) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [toC3_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]
  · rw [toC3_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]

private theorem toC3_eq_zero_iff (v : E3) : toC3 v = 0 ↔ v.ofLp 0 = 0 ∧ v.ofLp 1 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Complex.re h
      simpa [toC3_re] using h1
    · have h1 := congrArg Complex.im h
      simpa [toC3_im] using h1
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [toC3_re, toC3_im, h1, h2]

private theorem eq_zero_of_toC3_eq_zero_of_psi3_eq_zero {v : E3} (h1 : toC3 v = 0)
    (h2 : psi3 v = 0) : v = 0 := by
  obtain ⟨ha, hb⟩ := (toC3_eq_zero_iff v).mp h1
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa [psi3_apply v] using h2

private theorem eq_of_toC3_eq_of_psi3_eq {v w : E3} (h1 : toC3 v = toC3 w)
    (h2 : psi3 v = psi3 w) : v = w := by
  have h0 : v.ofLp 0 = w.ofLp 0 := by
    have := congrArg Complex.re h1
    simpa [toC3_re] using this
  have h1' : v.ofLp 1 = w.ofLp 1 := by
    have := congrArg Complex.im h1
    simpa [toC3_im] using this
  have h2' : v.ofLp 2 = w.ofLp 2 := by
    rw [← psi3_apply v, ← psi3_apply w, h2]
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simpa using h0
  · simpa using h1'
  · simpa using h2'

/-- A vector of `ℝ³` whose third coordinate vanishes and whose complex coordinate is a real
multiple of `exp (i φ)` is that round-picture point. -/
private theorem eq_smul_roundPic_of_toC3 {v : E3} {r φ : ℝ} (h2 : psi3 v = 0)
    (h : toC3 v = r • Complex.exp ((φ : ℂ) * Complex.I)) :
    v = r • Work.Drive.N2.roundPic φ := by
  have hre : v.ofLp 0 = r * Real.cos φ := by
    have h1 := congrArg Complex.re h
    rw [toC3_re, Complex.exp_ofReal_mul_I, Complex.smul_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1
    simpa using h1
  have him : v.ofLp 1 = r * Real.sin φ := by
    have h1 := congrArg Complex.im h
    rw [toC3_im, Complex.exp_ofReal_mul_I, Complex.smul_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1
    simpa using h1
  have h3 : v.ofLp 2 = 0 := by rw [← psi3_apply v]; exact h2
  refine PiLp.ext fun j => ?_
  fin_cases j
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using hre
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using him
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using h3

private theorem normSq_exp_ofReal_mul_I (t : ℝ) :
    Complex.normSq (Complex.exp ((t : ℂ) * Complex.I)) = 1 := by
  have h1 : ((t : ℂ) * Complex.I).re = 0 := by simp
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, h1, Real.exp_zero, one_pow]

/-! ## Two one-dimensional chain rules for `deriv` -/

private theorem deriv_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (g : ℝ → F) (x : ℝ) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => L (g y)) x = L (deriv g x) := by
  have h : HasDerivAt (fun y => L (g y)) (L (deriv g x)) x :=
    (ContinuousLinearMap.hasFDerivAt L).comp_hasDerivAt x hg.hasDerivAt
  exact h.deriv

private theorem deriv_const_smul {g : ℝ → ℂ} (c : ℝ) (x : ℝ) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => c • g y) x = c • deriv g x :=
  (hg.hasDerivAt.const_smul c).deriv

/-! ## The main theorem -/

theorem reparamOnRoundCircle {g : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hper : ∀ x : ℝ, g (x + 1) = g x)
    (hinj : Set.InjOn g (Set.Ico 0 1))
    (hderiv : ∀ x : ℝ, deriv g x ≠ 0)
    {pos : EuclideanSpace ℝ (Fin 3)} {rad : ℝ} (hrad : 0 < rad)
    (hcircle : ∀ x : ℝ, ∃ t : ℝ, g x = pos + rad • Work.Drive.N2.roundPic t) :
    ∃ (τ : ℝ → ℝ) (φ : ℝ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ ∧
      (∀ x : ℝ, τ (x + 1) = τ x + (ε : ℝ)) ∧
      Function.Surjective τ ∧ Function.Injective τ ∧
      (∀ x : ℝ, deriv τ x ≠ 0) ∧
      (∀ x : ℝ, g (τ x) = pos + rad • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x)) := by
  have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => g y - pos) :=
    hsm.sub contDiff_const
  -- the unit complex curve attached to `g`
  set z : ℝ → ℂ := fun y => (rad)⁻¹ • toC3 (g y - pos) with hzdef
  have hzcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z := by
    rw [hzdef]
    exact (toC3.contDiff.comp hsub).const_smul ((rad)⁻¹)
  -- the third coordinate of `g x - pos` vanishes
  have hG3 : ∀ y : ℝ, psi3 (g y - pos) = 0 := by
    intro y
    obtain ⟨t, ht⟩ := hcircle y
    have h : g y - pos = rad • Work.Drive.N2.roundPic t := by
      rw [ht]
      simp
    rw [h, map_smul, psi3_roundPic, smul_zero]
  -- `z` is a unit complex curve
  have hunit : ∀ y : ℝ, Complex.normSq (z y) = 1 := by
    intro y
    obtain ⟨t, ht⟩ := hcircle y
    have hz : z y = Complex.exp ((t : ℂ) * Complex.I) := by
      rw [hzdef]
      simp only
      have h : g y - pos = rad • Work.Drive.N2.roundPic t := by
        rw [ht]
        simp
      rw [h, map_smul, toC3_roundPic, smul_smul, inv_mul_cancel₀ (ne_of_gt hrad), one_smul]
    rw [hz]
    exact normSq_exp_ofReal_mul_I t
  have hzper : ∀ y : ℝ, z (y + 1) = z y := by
    intro y
    rw [hzdef]
    simp only
    rw [hper y]
  have hzinj : Set.InjOn z (Set.Ico 0 1) := by
    intro x hx y hy hxy
    have htoC : toC3 (g x - pos) = toC3 (g y - pos) := by
      have h' : (rad)⁻¹ • toC3 (g x - pos) = (rad)⁻¹ • toC3 (g y - pos) := hxy
      exact (smul_right_inj (inv_ne_zero (ne_of_gt hrad))).mp h'
    have hGxy : g x - pos = g y - pos :=
      eq_of_toC3_eq_of_psi3_eq htoC (by rw [hG3 x, hG3 y])
    have heq : g x = g y := by
      have h2 := congrArg (fun w : E3 => w + pos) hGxy
      simpa using h2
    exact hinj hx hy heq
  have hzder : ∀ y : ℝ, deriv z y ≠ 0 := by
    intro y hzero
    have hGder : deriv (fun y : ℝ => g y - pos) y ≠ 0 := by
      rw [deriv_sub_const]
      exact hderiv y
    have hGdiff : DifferentiableAt ℝ (fun y : ℝ => g y - pos) y :=
      (hsub.contDiffAt (x := y)).differentiableAt (by simp)
    have htoCdiff : DifferentiableAt ℝ (fun y => toC3 (g y - pos)) y :=
      ((toC3.contDiff.comp hsub).contDiffAt (x := y)).differentiableAt (by simp)
    have hdz : deriv z y = (rad)⁻¹ • toC3 (deriv (fun y : ℝ => g y - pos) y) := by
      rw [hzdef]
      rw [deriv_const_smul (rad)⁻¹ y htoCdiff, deriv_clm_comp toC3 _ y hGdiff]
    have htoC : toC3 (deriv (fun y : ℝ => g y - pos) y) = 0 := by
      rw [hdz] at hzero
      rcases smul_eq_zero.mp hzero with h | h
      · exact absurd h (inv_ne_zero (ne_of_gt hrad))
      · exact h
    have hpsi : psi3 (deriv (fun y : ℝ => g y - pos) y) = 0 := by
      have hconst : (psi3 ∘ (fun y : ℝ => g y - pos)) = fun _ : ℝ => (0 : ℝ) := funext hG3
      have hd : deriv (psi3 ∘ (fun y : ℝ => g y - pos)) y = 0 := by rw [hconst]; simp
      have hcm : deriv (psi3 ∘ (fun y : ℝ => g y - pos)) y
          = psi3 (deriv (fun y : ℝ => g y - pos) y) := by
        rw [show (psi3 ∘ (fun y : ℝ => g y - pos)) = fun y => psi3 (g y - pos) from rfl]
        exact deriv_clm_comp psi3 _ y hGdiff
      rw [← hcm]
      exact hd
    exact hGder (eq_zero_of_toC3_eq_zero_of_psi3_eq_zero htoC hpsi)
  obtain ⟨τ, φ, ε, hτcd, hε, hτper, hτsurj, hτmono, hτder, hz⟩ :=
    Work.Drive.N2C.exists_reparam_unitCircle z hzcd hunit hzper hzinj hzder
  refine ⟨τ, φ, ε, hε, hτcd, hτper, hτsurj, ?_, hτder, ?_⟩
  · exact hτmono.elim StrictMono.injective StrictAnti.injective
  · intro x
    have h1 : toC3 (g (τ x) - pos) = rad • Complex.exp (((φ + 2 * Real.pi * x) : ℂ)
        * Complex.I) := by
      have h := hz x
      rw [hzdef] at h
      have h' : (rad)⁻¹ • toC3 (g (τ x) - pos) =
          Complex.exp (((φ + 2 * Real.pi * x) : ℂ) * Complex.I) := h
      have h2 := congrArg (fun w : ℂ => rad • w) h'
      have hW : rad • ((rad)⁻¹ • toC3 (g (τ x) - pos)) = toC3 (g (τ x) - pos) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hrad), one_smul]
      rw [hW] at h2
      exact h2
    have hGv : g (τ x) - pos = rad • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x) := by
      refine eq_smul_roundPic_of_toC3 (hG3 (τ x)) ?_
      convert h1 using 2
      push_cast
      ring
    have h3 := congrArg (fun w : E3 => w + pos) hGv
    simpa [add_comm] using h3

end

end Work.N2C
