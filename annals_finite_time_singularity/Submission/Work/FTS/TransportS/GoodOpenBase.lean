/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.TransportS`: the open-class (`SmoothOpen`) base of the `D_z`-pairing

The `f`-side of `Work.FTS.TransportS.T3Good` is only assumed to be
`Work.FTS.EllipticEst.SmoothOpen` — `C^∞` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)` —
whereas the proved `Work.FTS.H2.T3Q.GoodZPt` (the pointwise bound on the good part of the
`D_z`-pairing) is stated for the larger class `Work.FTS.LocData.SmoothQuad` (`C^∞` on
`(-1,∞) × (0,π/2)`), which `SmoothOpen` does *not* imply.  This module collects the two
ingredients of `GoodZPt` that are class-sensitive, in the open class:

* the multiplier bound `|D_z^bD_θ^a f| ≤ 200 |f|_{𝒲^{4,∞}}` (`abs_mixed_le_WlInf_open`) for
  `1 ≤ a`, `a + b ≤ 4`, at interior points — the open-class analogue of
  `Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (same statement with the constant `30`), built from
  `Work.FTS.OpenPkg.DzIter_le_WlInf_open` and `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (the
  open-quadrant Stirling expansion `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`, which is what
  makes interior smoothness enough);
* the two Leibniz rules for the factor `D_z g`
  (`DzIter_mul_Dz_open`, `mixed_mul_Dz_open`), built from the general open-quadrant Leibniz
  rules `Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz` / `leibniz_open_mixed` and the
  commutation `D_θ^n (D_z g) = D_z (D_θ^n g)` in the general open-set form
  `Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen`.

These are the inputs of the delegated pieces `GoodIdOpen.lean` (the bookkeeping identity
`H4PairInt α (f · D_z g) g - Badz = Z3.easyZ + Z3.easyM`) and the per-term estimates
`GoodTZOpen.lean`, `GoodEasyZOpen.lean`, `GoodTMOpen.lean`, `GoodMsurvOpen.lean`; the
assembly is `Work.FTS.TransportS.t3Good` in `t3Good.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.T3S
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two smoothness bridges -/

/-- `SmoothQuad` implies `SmoothOpen` (`Q0 ⊆ quadU`). -/
theorem smoothOpen_of_smoothQuad {F : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad F) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  h.mono fun p hp =>
    ⟨show (-1 : ℝ) < p.1 by linarith [show (0 : ℝ) < p.1 from hp.1], hp.2⟩

/-- `SmoothOpen` implies the finite-order form `∀ n, C^n` on the open quadrant, which is the
hypothesis shape of the open-set commutation lemmas. -/
theorem smoothOpen_forall_nat {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp h

/-- `D_z` preserves `SmoothOpen`. -/
theorem smoothOpen_Dz {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz F) :=
  Work.FTS.LocData.contDiffOn_Dz Work.FTS.EllipticEst.isOpen_Q0 h

/-! ## The multiplier bound in the open class -/

/-- **The `f`-side bound for mixed derivatives in the open class.**  Every mixed derivative
`D_z^bD_θ^a f` of total order at most `4` of a `SmoothOpen` function `f` of class
`𝒲^{4,∞}` is bounded at every interior point by `200 |f|_{𝒲^{4,∞}}`.

This is the `SmoothOpen` analogue of `Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (whose constant
is `30`); the constant is larger here because the open-quadrant estimates give
`100|f|_𝒲 · (α + sin 2θ)sin(2θ)^{α/5}` and only `(α + sin 2θ)sin(2θ)^{α/5} ≤ 2` is available
for `0 < α ≤ 1`. -/
theorem abs_mixed_le_WlInf_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 200 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hmem
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
          Work.FTS.OpenPkg.DzIter_le_WlInf_open hf hmem (by omega) hz hθ
      _ ≤ 200 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b a f z θ|
        ≤ 100 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.FTS.OpenPkg.Mixed_le_WlInf_open hα hf hmem ha (by omega) hz hθ
      _ ≤ 100 * (Work.Spaces.WlInf α 4 f * 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 200 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The two Leibniz rules for the factor `D_z g` -/

/-- **Leibniz expansion of `D_z^i (f · D_zg)` in the open class.** -/
theorem DzIter_mul_Dz_open (i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)
            * (Work.Spaces.DzIter k f z θ * Work.Spaces.DzIter (i + 1 - k) g z θ) := by
  intro z θ hz hθ0 hθ1
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f (Work.Spaces.Dz g) hf (smoothOpen_Dz hg)
    z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Work.FTS.H2.Transport3Aux.Z3.DzIter_Dz (i - k) g, show i - k + 1 = i + 1 - k by omega]

/-- **`D_θ^n (D_z g) = D_z (D_θ^n g)`, hence `D_z^mD_θ^n (D_z g) = D_z^{m+1}D_θ^n g` on the
open quadrant**, for `g` of class `SmoothOpen`. -/
theorem mixed_Dz_eq_open {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m n : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed m n (Work.Spaces.Dz g) z θ = Work.Spaces.mixed (m + 1) n g z θ := by
  intro z θ hz hθ0 hθ1
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hcomm : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter n (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter n g)))
      Work.FTS.EllipticEst.Q0 := by
    have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 (smoothOpen_forall_nat hg) 1 n
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.mixed] using h
  have hc := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm m hy
  show Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
      = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter n g) z θ
  rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
        = Work.Spaces.DzIter m (Work.Spaces.Dz (Work.Spaces.DthIter n g)) z θ from hc]
  exact congrFun (congrFun
    (Work.FTS.H2.Transport3Aux.Z3.DzIter_Dz m (Work.Spaces.DthIter n g)) z) θ

/-- **Leibniz expansion of `D_z^jD_θ^i (f · D_zg)` in the open class.** -/
theorem mixed_mul_Dz_open (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b + 1) (i - a) g z θ) := by
  intro z θ hz hθ0 hθ1
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i f (Work.Spaces.Dz g) hf
    (smoothOpen_Dz hg) z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [mixed_Dz_eq_open hg (j - b) (i - a) z θ hz hθ0 hθ1]

end Work.FTS.TransportS
