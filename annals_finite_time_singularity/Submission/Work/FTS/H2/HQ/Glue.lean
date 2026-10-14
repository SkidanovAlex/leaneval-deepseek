import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.RegQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The data class in the interior vocabulary -/

/-- **The data class of the elliptic chapter, in the lead's interior vocabulary.**  This is
`EllHyp` with `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open quadrant) and
`Work.FTS.Nonlin.RegQ` (which bundles `HkMem` and the boundary traces) in place of the
analyticity requirement `Work.Spaces.SmoothNbhd`. -/
structure EllHypQ (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- genuine `C^∞` on the open quadrant -/
  quadF : Work.FTS.LocData.SmoothQuad F
  quadPsi : Work.FTS.LocData.SmoothQuad Ψ
  /-- the solution of (PolarBSL) with source `F`, Dirichlet data and decay -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- the interior class of the source -/
  regF : RegQ α k F
  /-- the interior class of the solution and of the quantities the estimates bound -/
  regPsi : RegQ α k Ψ
  regDth : RegQ α k (Work.Spaces.pth Ψ)
  regDth2 : RegQ α k (Work.Spaces.pthIter 2 Ψ)
  regZ2 : RegQ α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  regDivCos : RegQ α k (fun z θ => Ψ z θ / Real.cos θ)
  /-- honesty of the unweighted `L²`-integrals of the `L²`-level estimate -/
  l2Psi : Work.Spaces.L2Mem Ψ
  l2Dth : Work.Spaces.L2Mem (Work.Spaces.pth Ψ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2DthDivCos : Work.Spaces.L2Mem (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ))
  l2F : Work.Spaces.L2Mem F




/-! ## The restated targets (interior class) and the `EllPkgG` assembly -/

/-- The straightened stream function `Φ̃ = Φ - Θ(α,F)` of `Work.Construction.PhiTil` is the
`EllResid` of this chapter. -/
theorem PhiTil_eq_EllResid (α : ℝ) (F Φ : ℝ → ℝ → ℝ) :
    Work.Construction.PhiTil α F Φ = Work.Elliptic.EllResid α F Φ := by
  funext z θ
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Elliptic.EllResid,
    Work.Construction.s2, Work.Elliptic.L12_eq_FM, Work.FM.L12]
  rfl


theorem Uop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ) :
    Work.Construction.Uop α (Work.Construction.PhiTil α g Φg)
      = Uop α (Work.Elliptic.EllResid α g Φg) := by
  rw [PhiTil_eq_EllResid]
  rfl

theorem Vop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ) :
    Work.Construction.Vop (Work.Construction.PhiTil α g Φg)
      = Vop α (Work.Elliptic.EllResid α g Φg) := by
  rw [PhiTil_eq_EllResid]
  funext z θ
  rfl

theorem Uop_eq (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Work.Construction.Uop α Φ = Uop α Φ := rfl
theorem Vop_eq (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Work.Construction.Vop Φ = Vop α Φ := by
  funext z θ; rfl


/-! ## The consumable package: `EllPkgG` with the trace-free interior class

The frozen `EllPkgG` asks for `RegQ` of the three operator outputs; as `NOTES.md` §A4 records,
the `BdryTraces` conjunct of `RegQ` is *not* implied for those outputs (they do not vanish at the
angular endpoints in general), so the provable bounds deliver `SmoothQuad ∧ HkMem ∧ bound`
instead.  `EllPkgQ` is the corresponding package — everything `EllPkgG` has, with `RegQ`
replaced by the pair `(SmoothQuad, HkMem)` on the three operator fields. -/
structure EllPkgQ (α Ce : ℝ) (g Φg : ℝ → ℝ → ℝ) : Prop where
  sol : Work.Elliptic.IsBslSol α g Φg
  smooth : Work.FTS.LocData.SmoothQuad Φg
  R : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  U : Work.FTS.LocData.SmoothQuad (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ∧
      Xn α (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ≤ Ce * Xn α g
  V : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop
        (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.Construction.PhiTil α g Φg))



/-! ## The trace-free data class `EllHypT`

`BdryTraces` (inside `RegQ`) demands, in its `(a,b) = (0,0)` slot, that the function itself
vanish at both angular endpoints — true for the perturbation `g` (`VanishTheta`) but *not* for the
derived quantities `∂_θΨ`, `∂_θ²Ψ`, `Ψ/cos θ` of a solution of (PolarBSL), whose boundary values
are free.  `EllHypT` keeps, for those derived quantities, only the honesty of the weighted
integrals (`HkMem`/`L2Mem`), and keeps the boundary decay in `z` in the form of this chapter's
`ZDecay` (which is what the integrations by parts in `z` use).  It is the natural trace-free
analogue of `EllHyp` with `SmoothQuad` in place of the analyticity requirement `SmoothNbhd`. -/
structure EllHypT (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  quadF : Work.FTS.LocData.SmoothQuad F
  quadPsi : Work.FTS.LocData.SmoothQuad Ψ
  sol : Work.Elliptic.IsBslSol α F Ψ
  regF : RegQ α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Psi : Work.Spaces.L2Mem Ψ
  l2Dth : Work.Spaces.L2Mem (Work.Spaces.pth Ψ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2DthDivCos : Work.Spaces.L2Mem (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ))
  l2F : Work.Spaces.L2Mem F
  zdecay : ZDecay Ψ



end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.Glue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2
namespace HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
abbrev quadQ : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The open quadrant is contained in the strip `(-1,∞) × (0,π/2)` on which `SmoothQuad`
lives. -/
theorem quadQ_subset_quadU : quadQ ⊆ Work.Spaces.quadU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  have hz' : (0 : ℝ) < z := hz
  refine ⟨?_, hθ⟩
  show (-1 : ℝ) < z
  linarith

/-- `sin (2θ) > 0` on the open quadrant. -/
theorem sin_pos_of_quadQ (p : ℝ × ℝ) (hp : p ∈ quadQ) : 0 < Real.sin (2 * p.2) := by
  obtain ⟨hz, hθ⟩ := hp
  have h1 : (0 : ℝ) < p.2 := hθ.1
  have h2 : p.2 < π / 2 := hθ.2
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-! ## The derivation-like structures for `D_z`, `D_θ` in the genuine smooth class

`SmoothQuad f` is smoothness of the *uncurried* `f` on `(-1,∞) × (0,π/2)` in the genuine smooth
order `Work.Stability.smoothOrder` (the analytic order `⊤` would force `f` to be analytic and
is *false* for the cut-off).  The instances `Zb_DerivLike`/`Tb_DerivLike` of
`Work.Spaces.MixedMulDefs` are formulated for the analytic class `SmoothU`; the two below are
the genuine-smooth versions needed by the interior product rule. \-/

/-- The class of uncurried functions which are `C^∞` (genuine smooth order) on the strip
`(-1,∞) × (0,π/2)`; `SmoothQuad f` is `SmoothStr (Function.uncurry f)` by definition. -/
def SmoothStr (F : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder F Work.Spaces.quadU

theorem SmoothStr.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothStr F) {p : ℝ × ℝ}
    (hp : p ∈ Work.Spaces.quadU) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hp)).differentiableAt
    Work.FTS.LocData.smoothOrder_ne_zero

theorem SmoothStr_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothStr where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => ContDiffOn.const_smul c hA

/-- `D_z` is a derivation-like operator for the genuine smooth class on the strip `quadU`. -/
theorem Zb_DerivLike_smoothStr :
    Work.Spaces.DerivLike Work.Spaces.quadU SmoothStr Work.Spaces.Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (SmoothStr.differentiableAt hA hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (SmoothStr.differentiableAt hB hp)
    show Work.Spaces.Zb (A + B) (z, θ)
        = Work.Spaces.Zb A (z, θ) + Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (SmoothStr.differentiableAt hA hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (SmoothStr.differentiableAt hB hp)
    show Work.Spaces.Zb (A * B) (z, θ)
        = Work.Spaces.Zb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (-1)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have h' : ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.Dz (fun z θ => A (z, θ)))) Work.Spaces.quadU :=
      Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hA
    exact h'
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (SmoothStr.differentiableAt hA hp)
    show Work.Spaces.Zb (fun p => c * A p) (z, θ) = c * Work.Spaces.Zb A (z, θ)
    simp only [Work.Spaces.Zb]
    rw [deriv_const_mul c hA']
    ring

/-- `D_θ` is a derivation-like operator for the genuine smooth class on the strip `quadU`. -/
theorem Tb_DerivLike_smoothStr :
    Work.Spaces.DerivLike Work.Spaces.quadU SmoothStr Work.Spaces.Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (SmoothStr.differentiableAt hA hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (SmoothStr.differentiableAt hB hp)
    show Work.Spaces.Tb (A + B) (z, θ)
        = Work.Spaces.Tb A (z, θ) + Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (SmoothStr.differentiableAt hA hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (SmoothStr.differentiableAt hB hp)
    show Work.Spaces.Tb (A * B) (z, θ)
        = Work.Spaces.Tb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π / 2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have h' : ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.Dth (fun z θ => A (z, θ)))) Work.Spaces.quadU :=
      Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU hA
    exact h'
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (SmoothStr.differentiableAt hA hp)
    show Work.Spaces.Tb (fun p => c * A p) (z, θ) = c * Work.Spaces.Tb A (z, θ)
    simp only [Work.Spaces.Tb]
    rw [deriv_const_mul c hA']
    ring

/-! ## Leibniz rules in the interior class `SmoothQuad` -/

/-- **The Leibniz rule for `D_z^i` in the interior class.** -/
theorem DzIter_mul_quad (j : ℕ) (f g : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ∀ z ∈ Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      DzIter j (fun z θ => f z θ * g z θ) z θ =
        ∑ b ∈ Finset.range (j + 1),
          (j.choose b : ℝ) * (DzIter b f z θ * DzIter (j - b) g z θ) := by
  intro z hz θ hθ
  exact Work.FTS.LocData.DzIter_mul_smoothQuad j f g hz (hf.curry_z hθ) (hg.curry_z hθ)


/-- **The Leibniz rule for `D_z^j D_θ^i` in the interior class `SmoothQuad`** (the
two-operator rule of `Work.Spaces.DerivLike.twoOp_iterate_mul`, on the open quadrant).

`mixed j i (f g) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (mixed b a f) (mixed (j-b) (i-a) g)`
for `z ∈ Iz` and `0 < θ < π/2`.  This is the `RegQ` replacement of
`Work.Spaces.mixed_mul_eq` (which asks `SmoothInt`, i.e. smoothness in `z` down to `z = 0`
*and* at the angular boundary). -/
theorem mixed_mul_eq_quad (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ∀ z ∈ Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      mixed j i (fun z θ => f z θ * g z θ) z θ =
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a f z θ * mixed (j - b) (i - a) g z θ) := by
  intro z hz θ hθ
  have hz1 : (-1 : ℝ) < z := by
    rw [Iz, Set.mem_Ici] at hz
    linarith
  have hp : (z, θ) ∈ Work.Spaces.quadU := ⟨hz1, hθ⟩
  have hF : SmoothStr (Function.uncurry f) := hf
  have hG : SmoothStr (Function.uncurry g) := hg
  have h2 := (Work.Spaces.DerivLike.twoOp_iterate_mul (X := ℝ × ℝ)
      (s := Work.Spaces.quadU) (P := SmoothStr) (Z := Work.Spaces.Zb)
      (Θb := Work.Spaces.Tb) SmoothStr_FunClass Zb_DerivLike_smoothStr
      Tb_DerivLike_smoothStr j i hF hG) hp
  have h2' : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * ((Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f))) (z, θ)
               * (Work.Spaces.Zb^[j - b] (Work.Spaces.Tb^[i - a]
                   (Function.uncurry g))) (z, θ)) := by
    simpa using h2
  have hL : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = mixed j i (fun z θ => f z θ * g z θ) z θ := by
    rw [Work.Spaces.uncurry_mul f g, Work.Spaces.Tb_iterate_uncurry i
          (fun z θ => f z θ * g z θ),
        Work.Spaces.Zb_iterate_uncurry j
          (Work.Spaces.DthIter i (fun z θ => f z θ * g z θ))]
    rfl
  have e_f : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f)) (z, θ)
      = mixed b a f z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a f,
        Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a f)]
    rfl
  have e_g : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry g)) (z, θ)
      = mixed b a g z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a g,
        Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a g)]
    rfl
  rw [← hL, h2']
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [e_f a b, e_g (i - a) (j - b)]

/-! ## The weights on the open quadrant -/

/-- `(Wt α z θ)² = (w z)² sin(2θ)^{-γ}` on the open quadrant. -/
theorem Wt_sq_quad (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Wt α z θ) ^ 2 = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Wt, wTheta, mul_pow, h1]


/-- The product weight is continuous on the open quadrant. -/
theorem continuousOn_Wt_quad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wt α p.1 p.2) quadQ := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) quadQ := by
    have hfun : (fun p : ℝ × ℝ => w p.1) = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsp : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(gam α / 2))) quadQ :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_pos_of_quadQ p hp)))
  have hmul := hw.mul hsp
  have heq : (fun p : ℝ × ℝ => Wt α p.1 p.2)
      = (fun p : ℝ × ℝ => w p.1)
        * (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(gam α / 2))) := rfl
  rw [heq]
  exact hmul

/-- The light weight `w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_light_quad :
    ContinuousOn (fun p : ℝ × ℝ => w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)) quadQ := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) quadQ := by
    have hfun : (fun p : ℝ × ℝ => w p.1) = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsp : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (eta / 2)) quadQ :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_pos_of_quadQ p hp)))
  refine hw.div hsp (fun p hp => ?_)
  exact (Real.rpow_pos_of_pos (sin_pos_of_quadQ p hp) (eta / 2)).ne'

/-- The a.e. domination of a mixed slot by the `ℋ⁴`-integrand, in the norm form required by
`Integrable.mono'`. -/
theorem slot_norm_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) (z θ : ℝ) :
    ‖(mixed j i f z θ * Wt α z θ) ^ 2‖ ≤ HkIntegrand α 4 f z θ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-! ## Almost everywhere strong measurability -/

/-- The weighted square of a mixed derivative of a `SmoothQuad` function is almost everywhere
strongly measurable for the product of the restricted Lebesgue measures. -/
theorem aesm_mixed_Wt_sq_prod_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        quadQ_subset_quadU).mul (continuousOn_Wt_quad α)).pow 2)

/-- The `θ`-slice of the weighted square of a mixed derivative is a.e. strongly measurable. -/
theorem aesm_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) :=
  aesm_slice_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        quadQ_subset_quadU).mul (continuousOn_Wt_quad α)).pow 2) hz

/-- The light-weighted `D_z^m`-slot is a.e. strongly measurable on the product measure. -/
theorem aesm_light_prod (h : ℝ → ℝ → ℝ) (hsq : SmoothQuad h) (m : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => DzIter m h p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _
    (((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsq m).continuousOn.mono
        quadQ_subset_quadU).mul continuousOn_light_quad)

/-- The `θ`-slice of the light-weighted `D_z^m`-slot is a.e. strongly measurable. -/
theorem aesm_light_slice (h : ℝ → ℝ → ℝ) (hsq : SmoothQuad h) (m : ℕ) {z : ℝ}
    (hz : z ∈ Iz) :
    AEStronglyMeasurable
      (fun θ : ℝ => DzIter m h z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
      (volume.restrict Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    have hz0 : (fun θ : ℝ => DzIter m h 0 θ * (w 0 / (Real.sin (2 * θ)) ^ (eta / 2)))
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ; simp [w]
    rw [hz0]
    exact aestronglyMeasurable_const
  · exact aesm_slice_of_continuousOn_Qd _
      (((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hsq m).continuousOn.mono
        quadQ_subset_quadU).mul continuousOn_light_quad) hpos

/-! ## Integrability of the slots -/

/-- The `θ`-slice of a weighted mixed slot is integrable on `Iθ` for every `z ∈ Iz`, by
domination by the corresponding summand of `HkIntegrand α 4 f`. -/
theorem integrableOn_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f)
    (hmem : HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ => (mixed j i f 0 θ * Wt α 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      simp [Wt, w]
    rw [hzero]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
      (aesm_slice_mixed_Wt_sq α f hf j i hzpos) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-- `L2Mem` for a weighted mixed slot of order between `1` and `4`, together with the value of
its product-measure integral.  (`bt_prod_integrable` of `Work.Spaces` with `SmoothNbhd`
replaced by `SmoothQuad`.) -/
theorem bt_prod_integrable_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f)
    (hmem : HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    Integrable (fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ))
      ∧ integral ((volume.restrict Iz).prod (volume.restrict Iθ))
          (fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2)
        = L2Sq (fun z θ => mixed j i f z θ * Wt α z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (mixed j i f z θ * Wt α z θ) ^ 2 := fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod_quad α f hf j i
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz_meas hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hz_meas ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    exact slot_norm_le_HkIntegrand α f j i hi hij z θ
  have houter : Integrable
      (fun z => ∫ θ, (mixed j i f z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
    refine MeasureTheory.Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij))
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hnn hAE hslice houter
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [L2Sq]

/-- `L2Mem` for the pure `D_z`-slot of the `ℋ⁴`-integrand (light weight `w/sin(2θ)^{η/2}`). -/
theorem L2Mem_light_quad (α : ℝ) (h : ℝ → ℝ → ℝ) (hsq : SmoothQuad h) (hmem : HkMem α 4 h)
    (b : ℕ) (hb : b ≤ 4) :
    L2Mem (fun z θ => DzIter b h z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) := by
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz) ((aesm_light_slice h hsq b hz).pow 2) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_le_HkIntegrand_z α 4 h z θ b hb
  · have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (DzIter b h p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
      (aesm_light_prod h hsq b).pow 2
    refine Integrable.mono' hmem.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ hθ => sq_le_HkIntegrand_z α 4 h z θ b hb))

/-! ## The pointwise `L^∞`-bound of order `≤ 2` -/

/-- The pointwise `L^∞`-bound of order `≤ 2` on the **open quadrant**, with the constant
`Cf/(γ-1)` in front of `|f|²_{ℋ⁴}`: this is how the product-rule summands consume Elgindi's
Corollary `SecondDerivativesBounded` (tex 1094).  The bound is *only* claimed on `z > 0`,
`0 < θ < π/2`: `RegQ` constrains nothing on the boundary lines, where `RegQ` functions with
vanishing norm may be large. -/
structure PwBd (α : ℝ) (f : ℝ → ℝ → ℝ) (Cf : ℝ) : Prop where
  nonneg : 0 ≤ Cf
  bound : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
    (mixed b a f z θ) ^ 2 ≤ Cf / (gam α - 1) * HkSq α 4 f

/-- The pointwise form of the interior Corollary `SecondDerivativesBounded` gives `PwBd`. -/
theorem pwBd_of_pointwise (α C : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (hpt : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |mixed b a f z θ| ≤ C / Real.sqrt (gam α - 1) * HkNorm α 4 f) :
    PwBd α f (C ^ 2) := by
  refine ⟨sq_nonneg C, ?_⟩
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  intro b a hab z hz θ hθ0 hθ1
  have hsq : (mixed b a f z θ) ^ 2
      ≤ (C / Real.sqrt (gam α - 1) * HkNorm α 4 f) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpt b a hab z hz θ hθ0 hθ1) 2
  have hval : (C / Real.sqrt (gam α - 1) * HkNorm α 4 f) ^ 2
      = C ^ 2 / (gam α - 1) * HkSq α 4 f := by
    rw [mul_pow, div_pow, Real.sq_sqrt hγ.le, HkNorm,
      Real.sq_sqrt (HkSq_nonneg α 4 f)]
  rw [hval] at hsq
  exact hsq

/-! ## The boundary limits supplied by `BdryTraces`

`BdryTraces α k f` records, for every `a + b ≤ k`, the two limits `z·(D_z^bD_θ^a f·w)² → 0`
(as `z → 0⁺` and as `z → ∞`) and the two limits `sin(2θ)^{1-γ}·(D_z^bD_θ^a f)² → 0`
(as `θ → 0⁺` and as `θ → (π/2)⁻`).  Since `1 - γ < 0`, the angular clause *does* force the
mixed derivative itself to tend to `0` at the angular boundary, and the radial clause forces it
to tend to `0` at `z = ∞`.  These are the limits needed by the two one-dimensional Hardy
inequalities. -/

/-- `sin(2θ)^c → 0` as `θ → 0⁺`, for `c > 0`. -/
theorem tendsto_sin_rpow_zero_right {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) (0 : ℝ) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa using h
  have hcomp := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto.comp hsin
  have hval : (0 : ℝ) ^ c = 0 := Real.zero_rpow (ne_of_gt hc)
  rw [hval] at hcomp
  exact hcomp

/-- `sin(2θ)^c → 0` as `θ → (π/2)⁻`, for `c > 0`. -/
theorem tendsto_sin_rpow_zero_left {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) (π / 2) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    have hval : Real.sin (2 * (π / 2)) = 0 := by
      rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] (π / 2) ≤ 𝓝 (π / 2))
    simpa [hval] using h
  have hcomp := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto.comp hsin
  have hval : (0 : ℝ) ^ c = 0 := Real.zero_rpow (ne_of_gt hc)
  rw [hval] at hcomp
  exact hcomp

/-- `sin(2θ)^{γ-1}·(g θ)² → 0` forces `g → 0` at `θ → 0⁺` (here `γ - 1 > 0`, so the factor
`sin(2θ)^{γ-1}` tends to `0`). -/
theorem tendsto_nhdsGT_zero_of_traces (α : ℝ) (hα : 0 < α) {u : ℝ → ℝ}
    (h : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hsin0 : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_sin_rpow_zero_right hγ
  have hprod : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1)
      * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsin0.mul h
  have hlt : Set.Iio (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      (isOpen_Iio.mem_nhds (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos]))
  have heq : (fun θ => (u θ) ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ0 hθlt
    have h1 : (0 : ℝ) < θ := hθ0
    have h2 : θ < π / 2 := hθlt
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [← mul_assoc, ← Real.rpow_add hsin, show (gam α - 1) + (1 - gam α) = 0 by ring,
      Real.rpow_zero, one_mul]
  have hsq : Tendsto (fun θ => (u θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hprod.congr' heq.symm
  have habs : Tendsto (fun θ => |u θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcomp : Tendsto (fun θ : ℝ => Real.sqrt ((u θ) ^ 2)) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    convert hcomp using 1
    · funext θ; rw [Real.sqrt_sq_eq_abs]
    · rw [Real.sqrt_zero]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- `sin(2θ)^{γ-1}·(g θ)² → 0` forces `g → 0` at `θ → (π/2)⁻`. -/
theorem tendsto_nhdsLT_zero_of_traces (α : ℝ) (hα : 0 < α) {u : ℝ → ℝ}
    (h : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)
      (𝓝[<] (π / 2)) (𝓝 0)) :
    Tendsto u (𝓝[<] (π / 2)) (𝓝 0) := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hsin0 : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
      (𝓝[<] (π / 2)) (𝓝 0) := tendsto_sin_rpow_zero_left hγ
  have hprod : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1)
      * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
    simpa using hsin0.mul h
  have hgt : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (π / 2) :=
    (nhdsWithin_le_nhds : 𝓝[<] (π / 2) ≤ 𝓝 (π / 2))
      (isOpen_Ioi.mem_nhds (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos]))
  have heq : (fun θ => (u θ) ^ 2) =ᶠ[𝓝[<] (π / 2)]
      fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hgt] with θ hθπ hθ0
    have h1 : (0 : ℝ) < θ := hθ0
    have h2 : θ < π / 2 := hθπ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [← mul_assoc, ← Real.rpow_add hsin, show (gam α - 1) + (1 - gam α) = 0 by ring,
      Real.rpow_zero, one_mul]
  have hsq : Tendsto (fun θ => (u θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := hprod.congr' heq.symm
  have habs : Tendsto (fun θ => |u θ|) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hcomp : Tendsto (fun θ : ℝ => Real.sqrt ((u θ) ^ 2)) (𝓝[<] (π / 2))
        (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    convert hcomp using 1
    · funext θ; rw [Real.sqrt_sq_eq_abs]
    · rw [Real.sqrt_zero]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- `w z ≥ 1` for `z ≥ 1`. -/
theorem one_le_w {z : ℝ} (hz : 1 ≤ z) : (1 : ℝ) ≤ w z := by
  rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The radial clause of `BdryTraces` forces the mixed derivative to vanish at `z → ∞`. -/
theorem tendsto_atTop_zero_of_traces {u : ℝ → ℝ}
    (h : Tendsto (fun z => z * (u z * w z) ^ 2) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  have hinv : Tendsto (fun z : ℝ => 1 / z) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have hF : Tendsto (fun z : ℝ => (u z * w z) ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun z : ℝ => (z * (u z * w z) ^ 2) * (1 / z)) atTop (𝓝 (0 * 0)) :=
      h.mul hinv
    have h3 : Tendsto (fun z : ℝ => (z * (u z * w z) ^ 2) * (1 / z)) atTop (𝓝 0) := by
      simpa using h2
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with z hz
    have hz0 : z ≠ 0 := by linarith
    field_simp
  have hgm : Tendsto (fun z : ℝ => |u z * w z|) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun z : ℝ => Real.sqrt ((u z * w z) ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hF
    convert hcomp using 1
    · funext z; rw [Real.sqrt_sq_eq_abs]
    · rw [Real.sqrt_zero]
  have hub : Tendsto (fun z : ℝ => |u z|) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hgm
    · filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      exact abs_nonneg _
    · filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      have hw1 : (1 : ℝ) ≤ w z := one_le_w hz
      calc |u z| = |u z| * 1 := by ring
        _ ≤ |u z| * w z := mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
        _ = |u z| * |w z| := by rw [abs_of_nonneg (le_trans zero_le_one hw1)]
        _ = |u z * w z| := by rw [abs_mul]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hub)

/-- The `z → ∞` limits of all mixed derivatives of order `≤ 4` of a `RegQ` function. -/
theorem BdryTraces.tendsto_atTop_zero {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.BdryTraces α k f) {a b : ℕ} (hab : a + b ≤ k) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Tendsto (fun z => mixed b a f z θ) atTop (𝓝 0) :=
  tendsto_atTop_zero_of_traces ((h a b hab).1 θ hθ).2

/-- The `θ → 0⁺` limits of all mixed derivatives of order `≤ k` of a `RegQ` function. -/
theorem BdryTraces.tendsto_theta_zero {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.BdryTraces α k f) {a b : ℕ} (hab : a + b ≤ k) {z : ℝ}
    (hz : 0 < z) :
    Tendsto (fun θ => mixed b a f z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_nhdsGT_zero_of_traces α hα ((h a b hab).2 z hz).1

/-- The `θ → (π/2)⁻` limits of all mixed derivatives of order `≤ k` of a `RegQ` function. -/
theorem BdryTraces.tendsto_theta_pi {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.BdryTraces α k f) {a b : ℕ} (hab : a + b ≤ k) {z : ℝ}
    (hz : 0 < z) :
    Tendsto (fun θ => mixed b a f z θ) (𝓝[<] (π / 2)) (𝓝 0) :=
  tendsto_nhdsLT_zero_of_traces α hα ((h a b hab).2 z hz).2

/-! ## Strong measurability of products -/

/-- Strong measurability of the squared weighted product `(A·B·Wt)²` on the product measure and
on every angular slice, for `SmoothQuad` factors.  (The `SmoothNbhd` version is
`Work.Spaces.AesmSqProdSmooth`.) -/
theorem aesm_sq_prod_quad (α : ℝ) {A B : ℝ → ℝ → ℝ} (hA : SmoothQuad A) (hB : SmoothQuad B) :
    AEStronglyMeasurable
        (fun p : ℝ × ℝ => (A p.1 p.2 * B p.1 p.2 * Wt α p.1 p.2) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ))
      ∧ ∀ z ∈ Iz, AEStronglyMeasurable
        (fun θ : ℝ => (A z θ * B z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
  have hAB : SmoothQuad (fun z θ => A z θ * B z θ) :=
    Work.FTS.LocData.smoothQuad_mul hA hB
  refine ⟨?_, ?_⟩
  · have h := aesm_mixed_Wt_sq_prod_quad α (fun z θ => A z θ * B z θ) hAB 0 0
    simpa only [mixed_zero_left, DthIter_zero] using h
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (A 0 θ * B 0 θ * Wt α 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp [Wt, wTheta, w]
      rw [hzero]
      exact aestronglyMeasurable_const
    · have h := aesm_slice_mixed_Wt_sq α (fun z θ => A z θ * B z θ) hAB 0 0 hpos
      simpa only [mixed_zero_left, DthIter_zero] using h


end HQ
end Work.FTS.H2
end
end
