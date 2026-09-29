import Mathlib
import Submission.Work.A14D.decomp_I
import Submission.Work.A14D.LC_setup
import Submission.Work.A14.defs
import Submission.Work.A14D.jPrim_hasDerivAt

/-!
# `Work.A14D.decomp_I_L` — the `log`-decomposition of the jump integral on the lower half-disc

This is the lower-half mirror of the proved `Work.A14D.decomp_I`.  The jump of the `i`-th integral
entry of the fourteen functions is `primSeg (jIntJ D i) cSL`, the segment primitive from the base
point `cSL = 1/20 − i/8` of the integrand `z ↦ dyC z·(yC z)^{−i}·(D z − D (wC z))`.  On the lower
half-disc `halfL δ` the hypothesis `LogCoeff y9 δ (halfL δ) D κL` gives

  `jumpH D z = D z − D (wC z) = κL·y9 z·log (z − 1/9) + (h z − De z)`,

with `h` and `De` holomorphic on the whole disc `ball (1/9) δ`.  Since `z ↦ dyC z·(yC z)^{−i}` is
holomorphic on that disc (the zero `0` of `yC` and its pole `1` stay outside when `δ ≤ 1/20`), the
integrand is `F z = κL·f₀ z·log (z − 1/9) + G z` with `f₀ = (yC·)^{−i}·dyC·y9` and
`G = (yC·)^{−i}·dyC·(h − De)` both holomorphic on the disc.  `F` itself is holomorphic on the open
lower half plane (the deck involution `wC` sends the lower half plane into the upper one, hence into
`Om1`), so `primSeg F cSL` is a genuine primitive of `F` on that convex set, and the difference

  `Φ z = primSeg F cSL z − κL·jPrim y9 i z·log (z − 1/9)`

has derivative `Ψ z = G z − κL·dslope (jPrim y9 i) 1/9 z` on `halfL δ`: the two `log` terms cancel
and the apparent pole is removable (`jPrim y9 i` vanishes at `1/9`).  Extending the primitive of the
disc-holomorphic `Ψ` from the lower half-disc to the whole disc (`exists_holo_ext_halfL`) produces
`B` with `B = Φ` on `halfL δ`, which is the claim (with `m = 0`).
-/

namespace Work.A14D

open Complex Metric
open scoped Topology

noncomputable section

/-! ## Elementary geometry of the disc `ball (1/9) δ` for `δ ≤ 1/20`

The points `0` (zero of `yC`) and `1` (pole of `yC`, `dyC`) are outside `ball (1/9) δ` as soon as
`δ ≤ 1/20`, since `‖0 − 1/9‖ = 1/9` and `‖1 − 1/9‖ = 8/9`. -/

private lemma one_not_mem_ball_ninth_L {δ : ℝ} (hδ : δ ≤ 1 / 20) : (1 : ℂ) ∉ Metric.ball ninth δ := by
  intro h'
  have hle : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by norm_num [ninth]
  rw [Metric.mem_ball, Complex.dist_eq, hle] at h'
  linarith

private lemma zero_not_mem_ball_ninth_L {δ : ℝ} (hδ : δ ≤ 1 / 20) : (0 : ℂ) ∉ Metric.ball ninth δ := by
  intro h'
  have hle : ‖(0 : ℂ) - ninth‖ = 1 / 9 := by norm_num [ninth]
  rw [Metric.mem_ball, Complex.dist_eq, hle] at h'
  linarith

private lemma yC_diffOn_ball_ninth_L {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    DifferentiableOn ℂ yC (Metric.ball ninth δ) := by
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun hz1 => one_not_mem_ball_ninth_L hδ (by rwa [hz1] at hz)))

private lemma yC_ne_zero_ball_ninth_L {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    ∀ z ∈ Metric.ball ninth δ, yC z ≠ 0 := by
  intro z hz hz0
  have hz1 : z ≠ 1 := fun hz1 => one_not_mem_ball_ninth_L hδ (by rwa [hz1] at hz)
  have h : z ^ 2 = 0 := by
    have hh := hz0
    rw [yC] at hh
    field_simp at hh
    simpa using hh
  rw [sq_eq_zero_iff.mp h] at hz
  exact zero_not_mem_ball_ninth_L hδ hz

private lemma dyC_diffOn_ball_ninth_L {δ : ℝ} (hδ : δ ≤ 1 / 20) :
    DifferentiableOn ℂ dyC (Metric.ball ninth δ) := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun hh => one_not_mem_ball_ninth_L hδ (by rwa [hh] at hz))))


/-! ## The lower half plane and the lower half-disc

`wC` maps the open lower half plane into the open upper one (the sign-reversed companion of
`Work.A14D.wC_im_neg`), so that the integrand of the jump integral is holomorphic on the whole
lower half plane; and the lower half-disc `halfL δ` is an open convex (hence connected) subset of
the disc, on which the extension lemma `exists_holo_ext_halfL_aux` is used. -/

private lemma wC_im_pos_of_neg_L {z : ℂ} (hz : z.im < 0) : 0 < (wC z).im := by
  rw [wC, Complex.div_im]
  have h1 : (z - 1).im = z.im := by simp
  have h2 : (z - 1).re = z.re - 1 := by simp
  rw [h1, h2]
  have hN : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]
    intro hc
    have : (z - 1).im = 0 := by rw [hc]; simp
    simp at this
    linarith
  have hnum : z.im * (z.re - 1) - z.re * z.im = -z.im := by ring
  rw [← sub_div, hnum]
  exact div_pos (by linarith) hN

/-- The integrand `z ↦ dyC z · (yC z)⁻¹ ^ j · (D z − D (wC z))` of the `j`-th `y`-integral jump
is holomorphic on the open lower half plane: `yC` and `dyC` are rational with their only pole at
`1` and `yC` has its only zero at `0`, both off the lower half plane, while `wC` maps the lower
half plane into the upper one, hence into `Om1` where `D` is holomorphic. -/
private lemma integrandJFI_diffOn_lowerHalf_L {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z) {z : ℂ | z.im < 0} := by
  set s : Set ℂ := {z : ℂ | z.im < 0} with hs
  have hs1 : ∀ z ∈ s, z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    simp [s] at hz
  have hdydiff : DifferentiableOn ℂ dyC s := by
    unfold dyC
    exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
      ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
      (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (hs1 z hz)))
  have hyCdiff : DifferentiableOn ℂ yC s := by
    unfold yC
    exact (differentiableOn_id.pow 2).div
      (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (hs1 z hz))
  have hyCne : ∀ z ∈ s, yC z ≠ 0 := by
    intro z hz hz0
    have hz1 : z ≠ 1 := hs1 z hz
    have h : z ^ 2 = 0 := by
      have hh := hz0
      rw [yC] at hh
      field_simp at hh
      simpa using hh
    have hz0' : z = 0 := sq_eq_zero_iff.mp h
    rw [hz0'] at hz
    simp [s] at hz
  have hinv : DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ j) s := (hyCdiff.inv hyCne).pow j
  have hwCd : DifferentiableOn ℂ wC s := by
    unfold wC
    exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (hs1 z hz))
  -- `wC` maps the lower half plane into `Om1` (indeed into the upper half plane)
  have hmaps : Set.MapsTo wC s Om1 := by
    intro z hz
    rw [Om1]
    exact Or.inl (ne_of_gt (wC_im_pos_of_neg_L hz))
  have hDd : DifferentiableOn ℂ D s := hD.mono (fun z hz => by
    rw [Om1]; exact Or.inl (ne_of_lt hz))
  have hcomp : DifferentiableOn ℂ (fun z => D (wC z)) s := hD.comp hwCd hmaps
  have hkey : (fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z)
      = (fun z => dyC z * ((fun z => (yC z)⁻¹ ^ j) z) * (D z - D (wC z))) := by
    funext z; rw [jumpH]
  rw [hkey]
  exact (hdydiff.mul hinv).mul (hDd.sub hcomp)

private lemma convex_halfL_aux (δ : ℝ) : Convex ℝ (halfL δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_im_lt 0)

private lemma isOpen_halfL_aux (δ : ℝ) : IsOpen (halfL δ) :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

/-- Holomorphic extension of `Φ` from the lower half-disc `halfL δ` to the full disc `ball (1/9) δ`
whenever `Φ' = Ψ` on `halfL δ` and `Ψ` is holomorphic on the disc: if `F` is a primitive of `Ψ`
on the disc, then `F − Φ` is holomorphic on the lower half-disc with vanishing derivative, hence
constant there (the lower half-disc is convex, so preconnected). -/
private theorem exists_holo_ext_halfL_aux {δ : ℝ} (hδ : 0 < δ) {Φ Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball ninth δ))
    (hΦ : DifferentiableOn ℂ Φ (halfL δ))
    (hderiv : ∀ z ∈ halfL δ, HasDerivAt Φ (Ψ z) z) :
    ∃ B : ℂ → ℂ, DifferentiableOn ℂ B (Metric.ball ninth δ) ∧ ∀ z ∈ halfL δ, B z = Φ z := by
  -- `Ψ` has a primitive `F` on the disc
  obtain ⟨F, hF⟩ := hΨ.isExactOn_ball
  have hFd : DifferentiableOn ℂ F (Metric.ball ninth δ) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hsub : halfL δ ⊆ Metric.ball ninth δ := Set.inter_subset_left
  have hGd : DifferentiableOn ℂ (fun z => F z - Φ z) (halfL δ) :=
    (hFd.mono hsub).sub hΦ
  have hG' : (halfL δ).EqOn (deriv fun z => F z - Φ z) 0 := by
    intro z hz
    have h1 : HasDerivAt (fun z => F z - Φ z) (Ψ z - Ψ z) z :=
      (hF z (hsub hz)).sub (hderiv z hz)
    rw [sub_self] at h1
    exact h1.deriv
  -- hence `F − Φ` is constant on the (preconnected) lower half-disc
  obtain ⟨a, ha⟩ := (isOpen_halfL_aux δ).exists_is_const_of_deriv_eq_zero
    (convex_halfL_aux δ).isPreconnected hGd hG'
  refine ⟨fun z => F z - a, hFd.sub_const a, ?_⟩
  intro z hz
  have h := ha z hz
  rw [← h]; abel

/-! ## The target -/

theorem decomp_I_L {y9 D De : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κL : ℂ)
    (hY : Y9 y9 δ)
    (hL : LogCoeff y9 δ (halfL δ) D κL)
    (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfL δ, De z = D (wC z))
    (i : Fin 3) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfL δ,
        primSeg (fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ) * jumpH D ζ) cSL z
          = κL * jPrim y9 (i : ℕ) z * Complex.log (z - ninth) + B z := by
  obtain ⟨h, hh, hDval⟩ := hL
  -- the integrand of the jump integral, its `log`-coefficient `f0`, the "non-log part" `G` of the
  -- jump, the canonical primitive `P = jPrim y9 i` of `f0`, the remainder `Ψ` and the target `Φ`
  set F : ℂ → ℂ := fun z => dyC z * (yC z)⁻¹ ^ (i : ℕ) * jumpH D z with hFdef
  set f0 : ℂ → ℂ := fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z with hf0def
  set G : ℂ → ℂ := fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * (h z - De z) with hGdef
  set P : ℂ → ℂ := jPrim y9 (i : ℕ) with hPdef
  set Ψ : ℂ → ℂ := fun z => G z - κL * dslope P ninth z with hΨdef
  set Φ : ℂ → ℂ := fun z => primSeg F cSL z - κL * (P z * Complex.log (z - ninth)) with hΦdef
  -- `P` is a primitive of `f0` on the disc, vanishing at the centre
  have hPderiv : ∀ z ∈ Metric.ball ninth δ, HasDerivAt P (f0 z) z := by
    intro z hz
    rw [hPdef, hf0def]
    exact jPrim_hasDerivAt hY i z hz
  have hP9 : P ninth = 0 := by
    rw [hPdef, jPrim, primSeg]
    simp
  have hPdiff : DifferentiableOn ℂ P (Metric.ball ninth δ) :=
    fun z hz => (hPderiv z hz).differentiableAt.differentiableWithinAt
  -- the integrand is holomorphic on the (convex) open lower half plane
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | z.im < 0} := by
    rw [hFdef]
    exact integrandJFI_diffOn_lowerHalf_L hD (i : ℕ)
  have hLHopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hLHconv : Convex ℝ {z : ℂ | z.im < 0} := convex_halfSpace_im_lt 0
  have hcSL : cSL ∈ {z : ℂ | z.im < 0} := by
    simp [cSL, Complex.sub_im]
  have hprim := primSeg_hasDerivAt hLHconv hLHopen hcSL hFdiff
  have hFd : ∀ z ∈ halfL δ, HasDerivAt (primSeg F cSL) (F z) z := fun z hz => hprim z hz.2
  -- the value of the integrand on the lower half disc
  have hFval : ∀ z ∈ halfL δ, F z = κL * f0 z * Complex.log (z - ninth) + G z := by
    intro z hz
    have h1 := hDval z hz
    have h2 := hDeeq z hz
    rw [hFdef, hf0def, hGdef]
    simp only [jumpH]
    rw [h1, ← h2]
    ring
  -- derivative of the product `P·log (· − 1/9)`
  have hPlogd : ∀ z ∈ halfL δ, HasDerivAt (fun w => P w * Complex.log (w - ninth))
      (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹) z := by
    intro z hz
    have hslit : z - ninth ∈ Complex.slitPlane := by
      show 0 < (z - ninth).re ∨ (z - ninth).im ≠ 0
      right
      simpa [ninth] using ne_of_lt hz.2
    have h1 : HasDerivAt (fun w : ℂ => w - ninth) 1 z := by
      simpa using (hasDerivAt_id z).sub_const ninth
    have h2 : HasDerivAt (fun w : ℂ => Complex.log (w - ninth)) ((z - ninth)⁻¹) z := by
      rw [← one_div]
      exact h1.clog hslit
    exact (hPderiv z hz.1).mul h2
  -- derivative of `Φ` on the lower half disc
  have hΦderiv : ∀ z ∈ halfL δ, HasDerivAt Φ (Ψ z) z := by
    intro z hz
    have h1 : HasDerivAt (primSeg F cSL) (F z) z := hFd z hz
    have h2 : HasDerivAt (fun w => κL * (P w * Complex.log (w - ninth)))
        (κL * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹)) z :=
      (hPlogd z hz).const_mul κL
    have h3 : HasDerivAt Φ
        (F z - κL * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹)) z := by
      rw [hΦdef]
      exact h1.sub h2
    have hz9 : z ≠ ninth := by
      intro hh
      have h2 : ninth.im < 0 := by rw [← hh]; exact hz.2
      have h3 : ninth.im = 0 := by norm_num [ninth]
      rw [h3] at h2
      exact lt_irrefl 0 h2
    -- the removable pole `P z/(z − 1/9)` is the `dslope`
    have hds : dslope P ninth z = P z / (z - ninth) := by
      rw [dslope_of_ne P hz9]
      simp only [slope, hP9, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hval : F z - κL * (f0 z * Complex.log (z - ninth) + P z * (z - ninth)⁻¹) = Ψ z := by
      rw [hFval z hz, hΨdef]
      dsimp only
      rw [hds]
      ring
    rwa [hval] at h3
  have hΦdiff : DifferentiableOn ℂ Φ (halfL δ) :=
    fun z hz => (hΦderiv z hz).differentiableAt.differentiableWithinAt
  -- the remainder `Ψ` is holomorphic on the whole disc
  have hGdiff : DifferentiableOn ℂ G (Metric.ball ninth δ) := by
    rw [hGdef]
    exact (((yC_diffOn_ball_ninth_L hδ20).inv (yC_ne_zero_ball_ninth_L hδ20)).pow (i : ℕ)).mul
      (dyC_diffOn_ball_ninth_L hδ20) |>.mul (hh.sub hDe)
  have hΨdiff : DifferentiableOn ℂ Ψ (Metric.ball ninth δ) := by
    rw [hΨdef]
    exact hGdiff.sub
      (((differentiableOn_dslope (Metric.ball_mem_nhds ninth hδ)).mpr hPdiff).const_mul κL)
  -- the primitive of `Ψ` on the disc, adjusted so that it matches `Φ` on the lower half disc
  obtain ⟨B, hBdiff, hBΦ⟩ := exists_holo_ext_halfL_aux hδ hΨdiff hΦdiff hΦderiv
  refine ⟨0, B, ?_, ?_⟩
  · simpa using hBdiff
  · intro z hz
    rw [hBΦ z hz, hΦdef, hFdef, hPdef]
    ring

end

end Work.A14D
