/-
# `SharpAux/WlInfTermsAux` — the generic tools for the ten `𝒲^{4,∞}`-term bounds

This module collects the four re-usable lemmas of `SharpAux/WlInfTermsBound` (which is kept small
enough for the build guard by importing them from here):

* `Xn_le_Xn5_aux` — `|f|_{ℋ⁴} ≤ |f|_{ℋ⁵}` for honest `f`;
* `wl_term_bound` — the `𝒲^{4,∞}`-product rule in the shape used by the ten monomials
  (`Sharp.Xn_mul_wlInf` plus the scalar conjugation laws);
* `sinSq_mul_bound` — multiplication by `sin²θ` is honest in `ℋ⁴`, with the `sin²θ`-profile
  rescaled so that the `angmul` clause of `N4Norm'` applies (row 24's trick);
* `scale_le_max` — the only sign-sensitive step (`Ce` may be negative);
* `le_K_mul_Xn5` — the final comparison with the shape `K·(1+|g|_{ℋ⁵}+|g'|_{ℋ⁵})·|h|_{ℋ⁵}`.

Nothing here is `sorry`-free-critical: the file contains no `sorry`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.SharpAux.Defs
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `Xn` is monotone in the order: `|f|_{ℋ⁴} ≤ |f|_{ℋ⁵}` for honest `f`. -/
theorem Xn_le_Xn5_aux {α : ℝ} {f : Fn} (h5 : Work.Spaces.HkMem α 5 f) :
    Work.FTS.Nonlin.Xn α f ≤ Work.FTS.GalFields.Xn5 α f :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5)

/-- **The `𝒲^{4,∞}`-product rule in the shape used by the ten terms**: a coefficient `f` priced by
the `𝒲^{4,∞}`-norm `Cw` times an honest `u` carrying `B·|h|_{ℋ⁵}`, scaled by `a`, is honest in
`ℋ⁴` with `|·|_{ℋ⁴} ≤ |a|·Ci·α^{-1/2}·Cw·B·|h|_{ℋ⁵}`. -/
theorem wl_term_bound {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) {f u h : Fn}
    (hfS : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu : Work.Spaces.HkMem α 4 u)
    {Cw B : ℝ} (hCw : Work.Spaces.WlInf α 4 f ≤ Cw)
    (huX : Work.FTS.Nonlin.Xn α u ≤ B * Work.FTS.GalFields.Xn5 α h) (a : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a * (f z θ * u z θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => a * (f z θ * u z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a * (f z θ * u z θ))
        ≤ |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B) * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨hmem, hbd⟩ :=
    Work.FTS.GalFields.RHS.Sharp.Xn_mul_wlInf hN hα hαα₂ hfS hfm huS hu hCw huX
  have hXeq : Work.FTS.Nonlin.Xn α (fun z θ => a * (f z θ * u z θ))
      = |a| * Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ) :=
    Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α a (fun z θ => f z θ * u z θ)
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.NonlinRows.smoothOpen_const_mul a
      (Work.FTS.NonlinRows.smoothOpen_mul hfS huS)
  · exact Work.FTS.LocData.HkMem_const_mul α 4 a hmem
  · rw [hXeq]
    calc |a| * Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ)
        ≤ |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B * Work.FTS.GalFields.Xn5 α h) :=
          mul_le_mul_of_nonneg_left hbd (abs_nonneg a)
      _ = |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B) * Work.FTS.GalFields.Xn5 α h := by ring

/-- **Multiplication by `sin²θ`**: the angular multiple `sin²θ·u` of an honest `ℋ⁴`-function `u`
is honest, with `|sin²θ·u|_{ℋ⁴} ≤ B·Ci·Bu·|h|_{ℋ⁵}` whenever `|u|_{ℋ⁴} ≤ Bu·|h|_{ℋ⁵}`.

The proof is the rescaling trick of row 24: the angular profile `-sin²θ` (with iteration constants
`B`) is scaled by `c = Ci/B`, so that its `L^∞`-data fits the `Ci`-budget of `N4Norm'.angmul`; the
scaling is undone with `Xn_const_mul`, and `c^{-1}·Ci² = B·Ci`. -/
theorem sinSq_mul_bound {α α₂ Ci B Bu : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) (hBpos : 0 < B)
    (hSI : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)))
    (hbnd : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ) ^ 2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)) 0 θ|
        ≤ B * Real.sin (2 * θ))
    {u h : Fn} (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu : Work.Spaces.HkMem α 4 u)
    (huX : Work.FTS.Nonlin.Xn α u ≤ Bu * Work.FTS.GalFields.Xn5 α h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * u z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ => Real.sin θ ^ 2 * u z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Real.sin θ ^ 2 * u z θ)
        ≤ (B * Ci * Bu) * Work.FTS.GalFields.Xn5 α h := by
  have hCi : 0 < Ci := hN.pos.1
  have hCine : Ci ≠ 0 := ne_of_gt hCi
  have hBne : B ≠ 0 := ne_of_gt hBpos
  set c : ℝ := Ci / B with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos hCi hBpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcB : c * B = Ci := by rw [hc]; field_simp
  have hcore := Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen hN hBpos hcB hSI hbnd hdth
    huS hu ⟨hα, hαα₂⟩
  have hkey : (fun z θ => Real.sin θ ^ 2 * u z θ)
      = fun z θ => (1 / (-c)) * (c * (-(Real.sin θ ^ 2)) * u z θ) := by
    funext z θ
    field_simp
  have hXeq : Work.FTS.Nonlin.Xn α (fun z θ => Real.sin θ ^ 2 * u z θ)
      = |1 / (-c)| * Work.FTS.Nonlin.Xn α (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ) := by
    rw [hkey]
    exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (1 / (-c))
      (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ)
  refine ⟨?_, ?_, ?_⟩
  · rw [hkey]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (-c))
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul c
          (Work.FTS.EllipticEst.smoothOpen_of_smoothInt hSI)) huS)
  · rw [hkey]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / (-c)) hcore.1
  · rw [hXeq]
    have habs : |1 / (-c)| = 1 / c := by
      rw [abs_of_neg (div_neg_of_pos_of_neg one_pos (by linarith : -c < 0))]
      field_simp
    rw [habs]
    calc (1 / c) * Work.FTS.Nonlin.Xn α (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ)
        ≤ (1 / c) * (Ci * Ci * Work.FTS.Nonlin.Xn α u) :=
          mul_le_mul_of_nonneg_left hcore.2 (by positivity)
      _ ≤ (1 / c) * (Ci * Ci * (Bu * Work.FTS.GalFields.Xn5 α h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huX (by positivity))
            (by positivity)
      _ = (B * Ci * Bu) * Work.FTS.GalFields.Xn5 α h := by
          have hcinv : (1 : ℝ) / c = B / Ci := by
            rw [hc]
            field_simp
          rw [hcinv]
          field_simp

/-- **The `max`-trick for a constant of unknown sign**: if `A ≤ B·Y` with `Y ≤ Yh` and both
`A, Y, Yh ≥ 0`, then `A ≤ max B 0 · Yh`. -/
theorem scale_le_max {A B Y Yh : ℝ} (hA0 : 0 ≤ A) (hY0 : 0 ≤ Y) (hYh0 : 0 ≤ Yh)
    (hAY : A ≤ B * Y) (hYY : Y ≤ Yh) : A ≤ max B 0 * Yh := by
  have h1 : B * Y ≤ max B 0 * Y := mul_le_mul_of_nonneg_right (le_max_left B 0) hY0
  have h2 : max B 0 * Y ≤ max B 0 * Yh :=
    mul_le_mul_of_nonneg_left hYY (le_max_right B 0)
  exact le_trans (le_trans hAY h1) h2

/-- **The final comparison**: `A ≤ K` turns the `A`-bound of a term into the shape required by the
statement, because `1 ≤ 1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵}`. -/
theorem le_K_mul_Xn5 {α K A : ℝ} {g g' h : Fn} (hK : 0 ≤ K) (hAK : A ≤ K) :
    A * Work.FTS.GalFields.Xn5 α h
      ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
  have hY : 0 ≤ Work.FTS.GalFields.Xn5 α g := Real.sqrt_nonneg _
  have hY' : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Real.sqrt_nonneg _
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Real.sqrt_nonneg _
  have hone : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by
    linarith
  have hKm : K ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    simpa using mul_le_mul_of_nonneg_left hone hK
  calc A * Work.FTS.GalFields.Xn5 α h ≤ K * Work.FTS.GalFields.Xn5 α h :=
        mul_le_mul_of_nonneg_right hAK hYh
    _ ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
        mul_le_mul_of_nonneg_right hKm hYh

end Work.FTS.GalFields.RHS.SharpAux
