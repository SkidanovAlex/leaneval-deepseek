import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.LC_A_defs
import Submission.Work.A14D.primSeg_hasDerivAt
import Submission.Work.A14D.integrandJFI_diffOn_upperHalf
import Submission.Work.A14D.exists_holo_ext_halfU

/-!
# `Work.A14D.decomp_I` — the `log`-decomposition of the jump of the three integral entries

The jump of the `i`-th integral entry of the fourteen functions is
`JFI D i z = ∫_{cSU}^{z} y'·y^{-i}·(D − D∘w)` (the segment primitive from the base point `cSU` of
`SU` of the integrand `dyC·yC^{-i}·jumpH D`).  On the upper half disc `halfU δ` the hypothesis
`LogCoeff y9 δ (halfU δ) D κU` gives

  `jumpH D z = D z − D (w z) = κU·y9 z·log (z − 1/9) + (h z − De z)`,

with `h` and `De` holomorphic on the whole disc `ball (1/9) δ`.  Since `z ↦ dyC z · yC z^{-i}` is
holomorphic on that disc too (the zero `0` of `yC` and its pole `1` stay outside when `δ ≤ 1/20`),
the integrand is

  `F(z) = κU·f₀(z)·log (z − 1/9) + G(z)`,   `f₀ = (yC·)^{-i}·dyC·y9`,   `G = (yC·)^{-i}·dyC·(h − De)`.

Both `f₀` and `G` are holomorphic on the whole disc, so `jPrim y9 i = ∫_{1/9}^{z} f₀` is a genuine
primitive of `f₀` there, and `G` — and the difference

  `Φ z = JFI D i z − κU·jPrim y9 i z·log (z − 1/9)`

has derivative

  `Φ' z = F z − κU·(f₀ z·log (z − 1/9) + jPrim y9 i z/(z − 1/9)) = G z − κU·jPrim y9 i z/(z − 1/9)`

on `halfU δ`: the two `log` terms cancel, and the pole `jPrim y9 i z/(z − 1/9)` is *removable*
(`jPrim y9 i` vanishes at `1/9`), hence is again holomorphic on the whole disc (as `dslope`).
Since `halfU δ` is a convex (hence connected) open subset of the convex disc, any holomorphic
primitive `B` of `G − κU·dslope (jPrim y9 i) 1/9` on the disc agrees with `Φ` on `halfU δ` up to a
constant; adjusting the constant gives `B = Φ` there, i.e.

  `JFI D i z = κU·jPrim y9 i z·log (z − 1/9) + B z`  on `halfU δ`

with `B` (so also `(z − 1/9)^0·B`) holomorphic on the whole disc.  This is the claimed
decomposition, with `m = 0`.

The only analytic input is the differentiability of the segment primitive `primSeg F cSU` on the
convex upper half plane (where the integrand is holomorphic because `w` maps the upper half plane
into the lower one, hence into `Om1`).
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- The open upper half plane, the convex open set on which the jump of the continued `H` is
holomorphic. -/
def UH : Set ℂ := {z : ℂ | 0 < z.im}

/-! ## Elementary geometry of the disc `ball (1/9) δ` for `δ ≤ 1/20`

The points `0` (zero of `yC`) and `1` (pole of `yC`, `dyC`) are outside `ball (1/9) δ` as soon as
`δ ≤ 1/20`, since `‖0 − 1/9‖ = 1/9` and `‖1 − 1/9‖ = 8/9`. -/

private lemma one_not_mem_ball_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) : (1 : ℂ) ∉ Metric.ball ninth δ := by
  intro h'
  have hle : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by norm_num [ninth]
  rw [Metric.mem_ball, Complex.dist_eq, hle] at h'
  linarith

private lemma zero_not_mem_ball_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) : (0 : ℂ) ∉ Metric.ball ninth δ := by
  intro h'
  have hle : ‖(0 : ℂ) - ninth‖ = 1 / 9 := by norm_num [ninth]
  rw [Metric.mem_ball, Complex.dist_eq, hle] at h'
  linarith

private lemma yC_diffOn_ball_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    DifferentiableOn ℂ yC (Metric.ball ninth δ) := by
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun hz1 => one_not_mem_ball_ninth hδ (by rwa [hz1] at hz)))

private lemma yC_ne_zero_ball_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    ∀ z ∈ Metric.ball ninth δ, yC z ≠ 0 := by
  intro z hz hz0
  have hz1 : z ≠ 1 := fun hz1 => one_not_mem_ball_ninth hδ (by rwa [hz1] at hz)
  have h : z ^ 2 = 0 := by
    have hh := hz0
    rw [yC] at hh
    field_simp at hh
    simpa using hh
  rw [sq_eq_zero_iff.mp h] at hz
  exact zero_not_mem_ball_ninth hδ hz

private lemma dyC_diffOn_ball_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    DifferentiableOn ℂ dyC (Metric.ball ninth δ) := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun hh => one_not_mem_ball_ninth hδ (by rwa [hh] at hz))))

/-- The integrand `(yC ·)^{-j}·dyC·y9` of the canonical primitive `jPrim y9 j` is holomorphic on
the disc. -/
private lemma jIntegrand_diffOn {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) (j : ℕ) :
    DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ j * dyC z * y9 z) (Metric.ball ninth δ) := by
  have hδ20 : δ ≤ 1 / 20 := hY.2.1
  have hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ) := hY.2.2.1
  exact (((yC_diffOn_ball_ninth hδ20).inv (yC_ne_zero_ball_ninth hδ20)).pow j).mul
    (dyC_diffOn_ball_ninth hδ20) |>.mul hy9d

/-! ## The target -/

theorem decomp_I {y9 D De : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κU : ℂ)
    (hY : Y9 y9 δ)
    (hU : LogCoeff y9 δ (halfU δ) D κU)
    (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfU δ, De z = D (wC z))
    (i : Fin 3) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ,
        JFI D i z = κU * jPrim y9 (i : ℕ) z * Complex.log (z - ninth) + B z := by
  obtain ⟨h, hh, hDval⟩ := hU
  have hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ) := hY.2.2.1
  -- the integrand of `JFI`, its `log`-coefficient `f0`, the "non-log part" `G` of the jump,
  -- the canonical primitive `P = jPrim y9 i` of `f0`, the remainder `Ψ` and the target `Φ`
  set F : ℂ → ℂ := fun z => dyC z * (yC z)⁻¹ ^ (i : ℕ) * jumpH D z with hFdef
  set f0 : ℂ → ℂ := fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z with hf0def
  set G : ℂ → ℂ := fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * (h z - De z) with hGdef
  set P : ℂ → ℂ := jPrim y9 (i : ℕ) with hPdef
  set Ψ : ℂ → ℂ := fun z => G z - κU * dslope P ninth z with hΨdef
  set Φ : ℂ → ℂ := fun z => JFI D i z - κU * (P z * Complex.log (z - ninth)) with hΦdef
  -- `P` is a primitive of `f0` on the disc, vanishing at the centre
  have hPderiv : ∀ z ∈ Metric.ball ninth δ, HasDerivAt P (f0 z) z := by
    intro z hz
    have h := primSeg_hasDerivAt (convex_ball ninth δ) isOpen_ball (Metric.mem_ball_self hδ)
      (jIntegrand_diffOn hY (i : ℕ)) z hz
    rw [hPdef, hf0def]
    exact h
  have hP9 : P ninth = 0 := by
    rw [hPdef, jPrim, primSeg]
    simp
  have hPdiff : DifferentiableOn ℂ P (Metric.ball ninth δ) :=
    fun z hz => (hPderiv z hz).differentiableAt.differentiableWithinAt
  -- the integrand is holomorphic on the convex upper half plane
  have hFU : DifferentiableOn ℂ F UH := by
    rw [hFdef]
    exact integrandJFI_diffOn_upperHalf hD (i : ℕ)
  have hUopen : IsOpen UH := isOpen_lt continuous_const Complex.continuous_im
  have hUconv : Convex ℝ UH := convex_halfSpace_im_gt 0
  have hcSU : cSU ∈ UH := by rw [UH]; norm_num [cSU]
  have hJFI_eq : JFI D i = primSeg F cSU := by unfold JFI; rw [← hFdef]
  -- hence `JFI` is differentiable on the upper half disc with derivative `F`
  have hJFId : ∀ z ∈ halfU δ, HasDerivAt (JFI D i) (F z) z := by
    have hprim := primSeg_hasDerivAt hUconv hUopen hcSU hFU
    intro z hz
    rw [hJFI_eq]
    exact hprim z hz.2
  -- the value of the integrand on the upper half disc
  have hFval : ∀ z ∈ halfU δ, F z = κU * f0 z * Complex.log (z - ninth) + G z := by
    intro z hz
    have h1 := hDval z hz
    have h2 := hDeeq z hz
    rw [hFdef, hf0def, hGdef]
    simp only [jumpH]
    rw [h1, ← h2]
    ring
  -- derivative of the product `P·log (· − 1/9)`
  have hPlogd : ∀ z ∈ halfU δ, HasDerivAt (fun w => P w * Complex.log (w - ninth))
      (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹) z := by
    intro z hz
    have hslit : z - ninth ∈ Complex.slitPlane := by
      show 0 < (z - ninth).re ∨ (z - ninth).im ≠ 0
      right
      simpa [ninth] using ne_of_gt hz.2
    have h1 : HasDerivAt (fun w : ℂ => w - ninth) 1 z := by
      simpa using (hasDerivAt_id z).sub_const ninth
    have h2 : HasDerivAt (fun w : ℂ => Complex.log (w - ninth)) ((z - ninth)⁻¹) z := by
      rw [← one_div]
      exact h1.clog hslit
    exact (hPderiv z hz.1).mul h2
  -- derivative of `Φ` on the upper half disc
  have hΦderiv : ∀ z ∈ halfU δ, HasDerivAt Φ (Ψ z) z := by
    intro z hz
    have h1 : HasDerivAt (JFI D i) (F z) z := hJFId z hz
    have h2 : HasDerivAt (fun w => κU * (P w * Complex.log (w - ninth)))
        (κU * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹)) z :=
      (hPlogd z hz).const_mul κU
    have h3 : HasDerivAt Φ
        (F z - κU * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹)) z := by
      rw [hΦdef]
      exact h1.sub h2
    have hz9 : z ≠ ninth := by
      intro hh
      have h2 : (0 : ℝ) < ninth.im := by rw [← hh]; exact hz.2
      have h3 : ninth.im = 0 := by norm_num [ninth]
      rw [h3] at h2
      exact lt_irrefl 0 h2
    -- the removable pole `P z/(z − 1/9)` is the `dslope`
    have hds : dslope P ninth z = P z / (z - ninth) := by
      rw [dslope_of_ne P hz9]
      simp only [slope, hP9, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hval : F z - κU * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹) = Ψ z := by
      rw [hFval z hz, hΨdef]
      dsimp only
      rw [hds]
      ring
    rwa [hval] at h3
  have hΦdiff : DifferentiableOn ℂ Φ (halfU δ) :=
    fun z hz => (hΦderiv z hz).differentiableAt.differentiableWithinAt
  -- the remainder `Ψ` is holomorphic on the whole disc
  have hGdiff : DifferentiableOn ℂ G (Metric.ball ninth δ) := by
    rw [hGdef]
    exact (((yC_diffOn_ball_ninth hδ20).inv (yC_ne_zero_ball_ninth hδ20)).pow (i : ℕ)).mul
      (dyC_diffOn_ball_ninth hδ20) |>.mul (hh.sub hDe)
  have hΨdiff : DifferentiableOn ℂ Ψ (Metric.ball ninth δ) := by
    rw [hΨdef]
    exact hGdiff.sub
      (((differentiableOn_dslope (Metric.ball_mem_nhds ninth hδ)).mpr hPdiff).const_mul κU)
  -- the primitive of `Ψ` on the disc, adjusted so that it matches `Φ` on the upper half disc
  obtain ⟨B, hBdiff, hBΦ⟩ := exists_holo_ext_halfU hδ hΨdiff hΦdiff hΦderiv
  refine ⟨0, B, ?_, ?_⟩
  · simpa using hBdiff
  · intro z hz
    rw [hBΦ z hz, hΦdef, hPdef]
    ring

end

end Work.A14D
