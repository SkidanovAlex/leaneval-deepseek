import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar
open Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular derivative of the reassociated `EUz` field -/

/-- **The `∂_θ`-identity of the `EUz`-field**, in the reassociated form used by the flat
calculus: on the open quadrant,

`∂_θ (EUzR α Y) = EUzD α Y`

for a datum smooth on the quadrant.  The three inputs are the `θ`-derivative of the two `α`
terms (`EUzD` is exactly the sum of their derivatives) and the structural identity
`∂_θ (Yblk Y) = Yblk (∂_θ Y)` (`pth_zpz_smoothOpen`), the radial factor `(1+z)⁻¹` being
`θ`-free (`deriv_const_mul_field`). -/
theorem pth_EUzR_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzR α Y) z θ = EUzD α Y z θ := by
  intro z θ hz hθ hθ'
  have hsmr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_rhoinv hsm
  have hsmb : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hsm
  have hInv : Work.Spaces.pth (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) z θ
      = (1 + z)⁻¹ * Work.Spaces.pth Y z θ := by
    show deriv (fun θ' : ℝ => (1 + z)⁻¹ * Y z θ') θ
      = (1 + z)⁻¹ * deriv (fun θ' : ℝ => Y z θ') θ
    rw [deriv_const_mul_field]
  have hBlk : Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ :=
    pth_zpz_smoothOpen hsm z θ hz hθ hθ'
  have hG1 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ) z θ = 3 * Work.Spaces.pth Y z θ := by
    show deriv (fun θ' : ℝ => 3 * Y z θ') θ = 3 * deriv (fun θ' : ℝ => Y z θ') θ
    rw [deriv_const_mul_field]
  have hEuzR : Work.Spaces.pth (EUzR α Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
          + α * Yblk Y z θ)) z θ :=
    pth_congr_Q0 (fun z θ _ _ _ => by simp only [EUzR]) z θ hz hθ hθ'
  have hOuter : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ) z θ
      = 3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
        + α * Yblk (Work.Spaces.pth Y) z θ := by
    rw [pth_add_Q0 (f := fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ))
        (g := fun z θ : ℝ => α * Yblk Y z θ)
        (SmoothOpen.add (SmoothOpen.const_mul hsm 3) (SmoothOpen.const_mul hsmr α))
        (SmoothOpen.const_mul hsmb α) z θ hz hθ hθ']
    rw [pth_add_Q0 (f := fun z θ : ℝ => 3 * Y z θ)
        (g := fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ))
        (SmoothOpen.const_mul hsm 3) (SmoothOpen.const_mul hsmr α) z θ hz hθ hθ']
    rw [hG1, pth_const_mul α (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ)]
    simp only []
    rw [hInv, pth_const_mul α (Yblk Y)]
    simp only []
    rw [hBlk]
  have hNeg : Work.Spaces.pth (fun z θ : ℝ => -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ)) z θ
      = - Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)
        + α * Yblk Y z θ) z θ := by
    show deriv (fun θ' : ℝ => -(3 * Y z θ' + α * ((1 + z)⁻¹ * Y z θ')
        + α * Yblk Y z θ')) θ
      = - deriv (fun θ' : ℝ => 3 * Y z θ' + α * ((1 + z)⁻¹ * Y z θ') + α * Yblk Y z θ') θ
    exact deriv.neg
  rw [hEuzR, hNeg, hOuter]
  simp only [EUzD]

/-- **The order-six flat bound of the `EUz`-star-field**,
`EUz α Y = -(3Y + α(Y/(z+1) + z∂_zY)) = -Wone α Y`.

Prove `FlatW 6 (EUz α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD` (note the
factor `α` in front of the two `αY`-terms — this is where the `(α+1)` is genuinely needed, cf.
the refutation in `Submission/Work/FTS/StrongPersist/SP6/FlatW6Fields.lean` for the variant
without `(α+1)`).

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EUzR`/`EUzD` and `euzEUzR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`, `pth_thetaOnly`.
Natural route: `F0 6 (EUzR α Y)` and `F0 5 (pth (EUzR α Y)) = F0 5 (EUzD α Y)` (`pth (Yblk Y) =
Yblk (pth Y)` on `Q0` via `pth_zpz_smoothOpen`; `atomData` supplies every block bound), then
`F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EU_bound.lean` proves the order-**four** version of the
joint statement for `EUz` and `EU`. -/
theorem EUz6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  refine ⟨65 * A, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  obtain ⟨hY6, hP6, hD6, hPblk5, hDthP5⟩ := atomData hK hKY hKD hsm hW hFb hD
  -- ### the coefficient `(1+z)⁻¹` and the smoothness of the pieces
  have hRhoInv := hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])
  have hRhoInv6 : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹) := hRhoInv.1
  have hRhoInvS : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) := hRhoInv.2
  have hsmr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Fbq_smoothOpen_mul hRhoInvS hsm
  have hsmb : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hsm
  have hSm3Y : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    SmoothOpen.const_mul hsm 3
  have hSmαr : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    SmoothOpen.const_mul hsmr α
  have hSmαb : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Yblk Y z θ) :=
    SmoothOpen.const_mul hsmb α
  -- ### level `6`: the flat class of `EUzR`
  have hInvY6 : Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * KY) (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    F0_mul hA0 hKY hRhoInvS hsm hRhoInv6 hY6
  have hαInvY6 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) := by
    have h := F0_const_mul (n := 6) (K := 2 ^ 6 * A * KY) α hInvY6
    rwa [abs_of_nonneg hα] at h
  have hαYblk6 : Work.FTS.PhiStar.F0 6 (α * KD) (fun z θ : ℝ => α * Yblk Y z θ) := by
    have h := F0_const_mul (n := 6) (K := KD) α hD6
    rwa [abs_of_nonneg hα] at h
  have hSum6 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY) + α * KD)
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ) :=
    F0_add hSmαr hSmαb hαInvY6 hαYblk6
  have h3Y6 : Work.FTS.PhiStar.F0 6 (3 * KY) (fun z θ : ℝ => 3 * Y z θ) := by
    have h := F0_const_mul (n := 6) (K := KY) (3 : ℝ) hY6
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  have hBig6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => 3 * Y z θ + (α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ)) :=
    F0_add hSm3Y (SmoothOpen.add hSmαr hSmαb) h3Y6 hSum6
  have hAssoc6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Yblk Y z θ) :=
    F0_congr (fun z θ _ _ _ => by ring) hBig6
  have hEUzR6 : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (EUzR α Y) := by
    have h := F0_const_mul (n := 6) (K := 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (-1 : ℝ) hAssoc6
    rw [show |(-1 : ℝ)| * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
        = 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) by norm_num] at h
    refine F0_congr (fun z θ _ _ _ => ?_) h
    simp only [EUzR, Yblk]
    ring
  -- ### level `5`: the flat class of `EUzD`
  have hP5 : Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.pth Y) :=
    hP6.mono (by norm_num) le_rfl
  have hRhoInv5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => (1 + z)⁻¹) :=
    hRhoInv6.mono (by norm_num) le_rfl
  have hKN : 0 ≤ K + KY := by linarith
  have hInvP5 : Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * (K + KY))
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    F0_mul hA0 hKN hRhoInvS hsm.pth hRhoInv5 hP5
  have hαInvP5 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) := by
    have h := F0_const_mul (n := 5) (K := 2 ^ 5 * A * (K + KY)) α hInvP5
    rwa [abs_of_nonneg hα] at h
  have hαPblk5 : Work.FTS.PhiStar.F0 5 (α * (6 * (K + KY)))
      (fun z θ : ℝ => α * Yblk (Work.Spaces.pth Y) z θ) := by
    have h := F0_const_mul (n := 5) (K := 6 * (K + KY)) α hPblk5
    rwa [abs_of_nonneg hα] at h
  have hsmrP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul hRhoInvS hsm.pth
  have hsmbP : Work.FTS.EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) :=
    eh_smooth_yblk hsm.pth
  have hSmαrP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) :=
    SmoothOpen.const_mul hsmrP α
  have hSmαbP : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * Yblk (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.const_mul hsmbP α
  have hSm3P : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) :=
    SmoothOpen.const_mul hsm.pth 3
  have hSum5 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
        + α * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_add hSmαrP hSmαbP hαInvP5 hαPblk5
  have h3P5 : Work.FTS.PhiStar.F0 5 (3 * (K + KY))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) := by
    have h := F0_const_mul (n := 5) (K := K + KY) (3 : ℝ) hP5
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  have hBig5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ
        + (α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) + α * Yblk (Work.Spaces.pth Y) z θ)) :=
    F0_add hSm3P (SmoothOpen.add hSmαrP hSmαbP) h3P5 hSum5
  have hAssoc5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ
        + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) + α * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_congr (fun z θ _ _ _ => by ring) hBig5
  have hEUzD5 : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) (EUzD α Y) := by
    have h := F0_const_mul (n := 5)
      (K := 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (-1 : ℝ) hAssoc5
    rw [show |(-1 : ℝ)| * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
        = 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) by norm_num] at h
    refine F0_congr (fun z θ _ _ _ => ?_) h
    simp only [EUzD, Yblk]
    ring
  -- ### the arithmetic of the two constants
  have hS0 : (0 : ℝ) ≤ K + KY + KD := by linarith
  have hc6 : 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) ≤ 65 * A * (α + 1) * (K + KY + KD) := by
    have hKYle : KY ≤ K + KY + KD := by linarith
    have hKDle : KD ≤ K + KY + KD := by linarith
    have h1 : 3 * KY ≤ 3 * (K + KY + KD) := by linarith
    have h2 : α * (2 ^ 6 * A * KY) ≤ α * (2 ^ 6 * A * (K + KY + KD)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKYle (by norm_num; linarith)) hα
    have h3 : α * KD ≤ α * (K + KY + KD) := mul_le_mul_of_nonneg_left hKDle hα
    have h4 : 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD))
        ≤ (K + KY + KD) * (65 * A * (α + 1)) := by
      rw [show 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD))
          = (K + KY + KD) * (3 + (2 ^ 6 * A * α + α)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hS0
      have hA65 : (65 : ℝ) ≤ 65 * A := by linarith
      have hAα : α ≤ A * α := by nlinarith [hα, hA1]
      nlinarith
    calc 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)
        ≤ 3 * (K + KY + KD) + (α * (2 ^ 6 * A * (K + KY + KD)) + α * (K + KY + KD)) := by
          linarith
      _ ≤ (K + KY + KD) * (65 * A * (α + 1)) := h4
      _ = 65 * A * (α + 1) * (K + KY + KD) := by ring
  have hc5 : 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
      ≤ 65 * A * (α + 1) * (K + KY + KD) := by
    have hKNle : K + KY ≤ K + KY + KD := by linarith
    have h5 : 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
        ≤ (K + KY) * (65 * A * (α + 1)) := by
      rw [show 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
          = (K + KY) * (3 + (2 ^ 5 * A * α + 6 * α)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hKN
      have hA65 : (65 : ℝ) ≤ 65 * A := by linarith
      have hAα : α ≤ A * α := by nlinarith [hα, hA1]
      nlinarith
    calc 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))
        ≤ (K + KY) * (65 * A * (α + 1)) := h5
      _ ≤ (K + KY + KD) * (65 * A * (α + 1)) :=
          mul_le_mul_of_nonneg_right hKNle (by positivity)
      _ = 65 * A * (α + 1) * (K + KY + KD) := by ring
  -- ### conclusion
  have hEUz : Work.FTS.PhiStar.F0 6 (65 * A * (α + 1) * (K + KY + KD))
      (Work.FTS.PhiStar.EUz α Y) :=
    (F0_congr (fun z θ _ _ _ => euzEUzR_eq α Y z θ) hEUzR6).mono le_rfl hc6
  have hpth : Work.FTS.PhiStar.F0 5 (65 * A * (α + 1) * (K + KY + KD))
      (Work.Spaces.pth (Work.FTS.PhiStar.EUz α Y)) :=
    (F0_congr (fun z θ hz hθ hθ' =>
      (pth_congr_Q0 (fun z θ _ _ _ => euzEUzR_eq α Y z θ) z θ hz hθ hθ').trans
        (pth_EUzR_eq hsm z θ hz hθ hθ')) hEUzD5).mono le_rfl hc5
  exact flatW6_of_F0 hEUz hpth

end Work.FTS.StrongPersist.SP6
