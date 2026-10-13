/-
# `SharpAux/HonTerms/Base` — the elementary helpers of `SharpAux/HonestTermsBound`

* `negSinSq` — the angular profile `θ ↦ -sin²θ` whose `D_θ`-iterates vanish like `sin 2θ`
  (`RNP24.angProfile_sinSq`);
* `Xn_le_of_HkSq_le` — from an `HkSq`-comparison to the corresponding `Xn`-comparison;
* `sinSq_mul` — multiplication by `sin²θ` in `ℋ⁴`, transported through the sign from the general
  angular-multiplication estimate `L3Rhs.ang_mul_HkSq_le 4` applied to `-sin²θ`;
* `honest_mul`, `honest_mul_swap` — the `ℋ⁴`-product rule `Sharp.Xn_mul_honest` in the two
  orders of the factors, with the constant prefactor pulled out.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.SharpAux.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux.HonTerms

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular profile `θ ↦ -sin²θ`, whose `D_θ`-iterates vanish like `sin 2θ`
(`RNP24.angProfile_sinSq`). -/
def negSinSq : ℝ → ℝ := fun θ => -(Real.sin θ ^ 2)

theorem negSinSq_smooth :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => negSinSq θ) :=
  Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq

/-- From an `HkSq`-comparison, the corresponding `Xn`-comparison. -/
theorem Xn_le_of_HkSq_le {α : ℝ} {f g : Fn} {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Spaces.HkSq α 4 f ≤ C * Work.Spaces.HkSq α 4 g) :
    Work.FTS.Nonlin.Xn α f ≤ Real.sqrt C * Work.FTS.Nonlin.Xn α g := by
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt h
    _ = Real.sqrt C * Work.FTS.Nonlin.Xn α g := by rw [Real.sqrt_mul hC]; rfl

/-- **Multiplication by `sin²θ` in `ℋ⁴`**: from the `ℋ⁴`-honesty of the profile `-sin²θ` times
`f` (with the norm comparison against `Cang · Bsin ^ 2`), the product `sin²θ · f` is honest with
the same norm bound. -/
theorem sinSq_mul {α Cang Bsin : ℝ} (hCang : 0 < Cang) (hBsin : 0 < Bsin)
    {f : Fn} (hfS : Work.FTS.EllipticEst.SmoothOpen f)
    (hmemU : Work.Spaces.HkMem α 4 (fun z θ => negSinSq θ * f z θ))
    (hsqU : Work.Spaces.HkSq α 4 (fun z θ => negSinSq θ * f z θ)
      ≤ Cang * Bsin ^ 2 * Work.Spaces.HkSq α 4 f) :
    Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ) ∧
    Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ)
      ≤ Real.sqrt (Cang * Bsin ^ 2) * Work.FTS.Nonlin.Xn α f := by
  have hmemT : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ) :=
    Work.FTS.GalBasis.HkMem_congr_all
      (a := fun z θ => (-1 : ℝ) * ((fun z θ => negSinSq θ * f z θ) z θ))
      (b := fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ)
      (fun z θ => by simp only [Work.FTS.GalFields.RHS.Sharp.sinSq, negSinSq]; ring)
      α 4 (Work.FTS.LocData.HkMem_const_mul α 4 (-1) hmemU)
  have hnormT : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ)
      = Work.FTS.Nonlin.Xn α (fun z θ => negSinSq θ * f z θ) := by
    have hfun : (fun z θ => Work.FTS.GalFields.RHS.Sharp.sinSq θ * f z θ)
        = - (fun z θ => negSinSq θ * f z θ) := by
      funext z θ
      simp only [Work.FTS.GalFields.RHS.Sharp.sinSq, negSinSq, Pi.neg_apply]
      ring
    rw [hfun]
    exact Work.FTS.EllipticEst.HkNorm_neg α 4 (fun z θ => negSinSq θ * f z θ)
  refine ⟨?_, hmemT, ?_⟩
  · exact Work.FTS.NonlinRows.smoothOpen_mul Work.FTS.GalFields.RHS.smoothOpen_sin_sq hfS
  · rw [hnormT]
    exact Xn_le_of_HkSq_le (by positivity) hsqU

/-- **The `ℋ⁴`-product rule in the order of the arguments of `Xn_mul_honest`**: `F` carries the
`A·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})` factor, `U` the `B·|h|_{ℋ⁵}` factor. -/
theorem honest_mul {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) {g g' h : Fn}
    {F U : Fn} (hFS : Work.FTS.EllipticEst.SmoothOpen F)
    (hUS : Work.FTS.EllipticEst.SmoothOpen U)
    (hF : Work.Spaces.HkMem α 4 F) (hU : Work.Spaces.HkMem α 4 U)
    {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hFX : Work.FTS.Nonlin.Xn α F
      ≤ A * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g'))
    (hUX : Work.FTS.Nonlin.Xn α U ≤ B * Work.FTS.GalFields.Xn5 α h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (F z θ * U z θ)) ∧
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * U z θ)) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * U z θ))
      ≤ |c| * (Ci * α ^ (-(1 / 2 : ℝ)) * A * B
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h) := by
  obtain ⟨hmem, hX⟩ :=
    Work.FTS.GalFields.RHS.Sharp.Xn_mul_honest hN hα hαα₂ hFS hUS hF hU hA hB hFX hUX
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.NonlinRows.smoothOpen_const_mul c
      (Work.FTS.NonlinRows.smoothOpen_mul hFS hUS)
  · exact Work.FTS.LocData.HkMem_const_mul α 4 c hmem
  · rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
    exact mul_le_mul_of_nonneg_left hX (abs_nonneg c)

/-- **The `ℋ⁴`-product rule with the roles of the two factors exchanged** (the five terms whose
definition writes the `|h|`-carrying factor first): here `U` carries the
`A·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})` factor and `F` the `B·|h|_{ℋ⁵}` factor. -/
theorem honest_mul_swap {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) {g g' h : Fn}
    {F U : Fn} (hFS : Work.FTS.EllipticEst.SmoothOpen F)
    (hUS : Work.FTS.EllipticEst.SmoothOpen U)
    (hF : Work.Spaces.HkMem α 4 F) (hU : Work.Spaces.HkMem α 4 U)
    {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUX : Work.FTS.Nonlin.Xn α U
      ≤ A * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g'))
    (hFX : Work.FTS.Nonlin.Xn α F ≤ B * Work.FTS.GalFields.Xn5 α h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * (F z θ * U z θ)) ∧
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * U z θ)) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * U z θ))
      ≤ |c| * (Ci * α ^ (-(1 / 2 : ℝ)) * A * B
          * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h) := by
  obtain ⟨_, hmem0, hX0⟩ :=
    honest_mul (U := F) (F := U) hN hα hαα₂ hUS hFS hU hF hA hB hUX hFX
  have hnorm : Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * U z θ))
      = Work.FTS.Nonlin.Xn α (fun z θ => c * (U z θ * F z θ)) := by
    show Work.Spaces.HkNorm α 4 (fun z θ => c * (F z θ * U z θ))
        = Work.Spaces.HkNorm α 4 (fun z θ => c * (U z θ * F z θ))
    exact Work.FTS.GalBasis.HkNorm_congr_all (fun z θ => by ring) α 4
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.NonlinRows.smoothOpen_const_mul c
      (Work.FTS.NonlinRows.smoothOpen_mul hFS hUS)
  · refine Work.FTS.GalBasis.HkMem_congr_all
      (a := fun z θ => c * (U z θ * F z θ)) (b := fun z θ => c * (F z θ * U z θ))
      (fun z θ => by ring) α 4 hmem0
  · rw [hnorm]
    exact hX0

end Work.FTS.GalFields.RHS.SharpAux.HonTerms
