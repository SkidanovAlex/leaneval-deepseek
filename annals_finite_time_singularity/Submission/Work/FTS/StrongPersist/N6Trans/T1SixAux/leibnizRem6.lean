import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongPersist.IP6Clauses =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.Coercivity (HkIPStep H1IP LGammaT)
open Work.FTS.CoercivityFix.Assembly (H1IP_comm vc_symm vc_smul vc_nonneg)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Symmetry -/

/-- **The concrete `ℋ⁶` pairing is symmetric**, for *arbitrary* coefficients: the recursion
`HkIPStep` preserves symmetry (`vc_symm`) and its base `H1IP` is symmetric
(`H1IP_comm`). -/
theorem IP6_symm (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (u v : Fn) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u v
      = IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α v u :=
  vc_symm (c₁ := e₁) (c₂ := e₂)
    (vc_symm (c₁ := f₁) (c₂ := f₂)
      (vc_symm (c₁ := c₁'') (c₂ := c₂'')
        (vc_symm (c₁ := c₁') (c₂ := c₂')
          (vc_symm (c₁ := c₁) (c₂ := c₂)
            (fun u v => H1IP_comm α u v))))) u v

/-! ## Homogeneity and negation in the first argument -/

/-- **Homogeneity of the concrete `ℋ⁶` pairing in its first argument**, for arbitrary
coefficients: `D_θ` and `D_z` are unconditionally scalar-homogeneous and `H1IP` is
(`H1IP_homog`), which `vc_smul` transports through the recursion. -/
theorem IP6_smul (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (c : ℝ) (u v : Fn) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * u z θ) v
      = c * IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u v :=
  vc_smul (c₁ := e₁) (c₂ := e₂)
    (vc_smul (c₁ := f₁) (c₂ := f₂)
      (vc_smul (c₁ := c₁'') (c₂ := c₂'')
        (vc_smul (c₁ := c₁') (c₂ := c₂')
          (vc_smul (c₁ := c₁) (c₂ := c₂)
            (fun u v => Work.Coercivity.H1IP_homog α c u v))))) u v

/-- **Negation covariance of the concrete `ℋ⁶` pairing in its first argument**: the instance
`c = -1` of `IP6_smul`.  This is the structural half of the coercivity clause `coerNeg` of
`H6Coer`, which is the form the level-six energy estimate consumes. -/
theorem IP6_neg (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (u v : Fn) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => -(u z θ)) v
      = - IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u v := by
  have h : (fun z θ => -(u z θ)) = fun z θ => (-1 : ℝ) * u z θ := by
    funext z θ
    ring
  rw [h, IP6_smul]
  ring

/-! ## Nonnegativity of the diagonal -/




/-! ## Additivity and congruence on the honest class

The two remaining *structural* clauses of `H6Coer` for the concrete `IP6` are the ones that need
genuine integrability bookkeeping: additivity of a weighted integral over a sum requires both
halves to be honest, and the *open-quadrant* class `HQo α 6` (interior `C^∞` plus `HkMem α 6`) is
exactly the class in which they are.  Both are obtained by climbing the recursion of the
`IP`-chapter twice: `IPGen.Comm2o_three` gives the package at the level of `IP4`, and
`IPGen.Comm2o_succ` transports it through the two top `HkIPStep`s.  (This is the `add`/`congr`
content of `OpenPkg.N4ExtraQ` at level six.) -/

/-- **Additivity of the concrete `ℋ⁶` pairing in its first argument**, on the honest class
`HQo α 6`: the first argument is split inside every `wip`-pairing of the recursion, each half
being honest by `HkMem α 6` and additive on the open quadrant by interior smoothness. -/
theorem IP6_add (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (hα : 0 < α)
    {u₁ u₂ v : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen u₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen u₂)
    (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (m₁ : Work.Spaces.HkMem α 6 u₁) (m₂ : Work.Spaces.HkMem α 6 u₂)
    (mv : Work.Spaces.HkMem α 6 v) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => u₁ z θ + u₂ z θ) v
      = IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u₁ v
        + IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u₂ v :=
  (Work.FTS.IPGen.Comm2o_succ α (by linarith) 4
    (Work.FTS.IPGen.Comm2o_succ α (by linarith) 3
      (Work.FTS.IPGen.Comm2o_three α (by linarith)))).add u₁ u₂ v h₁ h₂ hv m₁ m₂ mv

/-- **Congruence of the concrete `ℋ⁶` pairing in its first argument on the open quadrant**: the
pairing only sees the values of its first argument on `Qd` (the weights make the boundary of the
quadrant null, and the derivatives are local there).  No membership is needed. -/
theorem IP6_congr (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (hα : 0 < α)
    {u u' v : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → u z θ = u' z θ) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u v
      = IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u' v :=
  (Work.FTS.IPGen.Comm2o_succ α (by linarith) 4
    (Work.FTS.IPGen.Comm2o_succ α (by linarith) 3
      (Work.FTS.IPGen.Comm2o_three α (by linarith)))).congr u u' v h

/-! ## Reducing the `H6Coer` obligation to its analytic content

The structural clauses of `H6Coer` for the concrete `IP6` are the three lemmas above; only the
compatibility with the `ℋ⁶` norm (`cs`, `lo`, `up`) is analytic.
The constructor below records that reduction: to inhabit `H6Coer (IP6 …) α₂ cc CC` it is enough to
supply those analytic clauses, provided the ten recursion coefficients are nonnegative.

(There is **no** coercivity field in `H6Coer`: design `FTS_HARD_DESIGN.md` (C) replaces it by the
one-sided bound `H6Lin` of `Defs.lean`, which is not a statement about `H6Coer` at all.  The lemma
`IP6_coerNeg_of_coer` below is retained only as a standalone transfer lemma: should a lower bound
on the pairing of `𝓛_Γ^T` ever be available, it gives the sign-normalised form without extra
work.) -/





end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two halves -/

/-- The `f`-dependent part of the factor multiplying `L₁₂(f)` in `N0gSum`. -/
def Vf (α : ℝ) (f : Fn) : Fn := fun z θ =>
  (1 / α) * f z θ
    + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth f z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz f z θ

/-- The `F_*`-dependent part of the factor multiplying `L₁₂(f)` in `N0gSum`. -/
def Vfs (α : ℝ) : Fn := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The factor multiplying `L₁₂(f)` in the block `N0gSum`. -/
def Bf (α : ℝ) (f : Fn) : Fn := fun z θ => Vf α f z θ + Vfs α z θ

/-- The row-7 term of the block: `c₂(θ)·L₁₂(F_*)(z)·D_z f`. -/
def Wf (α : ℝ) (f : Fn) : Fn := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.Dz f z θ

/-- The radial factor `z ↦ L₁₂(f)(z)`. -/
def Mf (f : Fn) : Fn := fun z _ => Work.Construction.L12 f z

/-- **The decomposition of `N0gSum`.** -/
theorem N0gSum_eq (α : ℝ) (f : Fn) :
    N0gSum α f = fun z θ => Mf f z θ * Bf α f z θ - Wf α f z θ := by
  funext z θ
  simp only [N0gSum, Bf, Vf, Vfs, Wf, Mf,
    Work.FTS.Nonlin.N03g, Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF,
    Work.FTS.Nonlin.N05aF, Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F,
    Work.Construction.N03, Work.Construction.N04a, Work.Construction.N04b,
    Work.Construction.N05a, Work.Construction.N05b, Work.Construction.N06]
  ring

/-! ## The `C³`-regularity on the open quadrant -/

private theorem contDiffOn_three_s2 : ContDiffOn ℝ 3 Work.Construction.s2
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  unfold Work.Construction.s2
  fun_prop

private theorem contDiffOn_three_c2m : ContDiffOn ℝ 3 Work.Construction.c2m
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  unfold Work.Construction.c2m
  fun_prop

/-- The `(z,θ) ↦ R z` form of a radial `C³` function. -/
private theorem cd_radial {R : ℝ → ℝ} (hR : ContDiffOn ℝ 3 R (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => R p.1) Work.FTS.EllipticEst.Q0 := by
  have hc := hR.comp contDiff_fst.contDiffOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  simpa only [Function.comp_def] using hc

/-- The `(z,θ) ↦ C θ` form of a `C³` angular function. -/
private theorem cd_angular {C : ℝ → ℝ} (hC : ContDiffOn ℝ 3 C (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => C p.2) Work.FTS.EllipticEst.Q0 := by
  have hc := hC.comp contDiff_snd.contDiffOn
    (fun p hp => by
      obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ⟨h0, h1⟩)
  simpa only [Function.comp_def] using hc

/-- `Bf α f` is `C³` on the open quadrant, for `f` smooth there. -/
private theorem cd_Bf {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Bf α f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hf3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf 3
  have hpthf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf.pth 3
  have hDzf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Dz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf.Dz 3
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.Degen.smoothOpen_Fstar α
  have hpthF : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF.pth 3
  have hDzF : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF.Dz 3
  have hs2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_s2
  have hc2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_c2m
  have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / α) * f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul hf3
  have h2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * (Work.Construction.s2 p.2 * Work.Spaces.pth f p.1 p.2))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul (hs2.mul hpthf)
  have h3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Spaces.Dz f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hc2m.mul hDzf
  have h4 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * (Work.Construction.s2 p.2
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hs2.mul hpthF)
  have h5 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hc2m.mul hDzF
  refine (((h1.add h2).sub h3).add h4).sub h5 |>.congr (fun p _ => ?_)
  simp only [Bf, Vf, Vfs]
  ring

/-- **The smoothness of the coupled half** `Mf f · Bf α f`, `C³` on the open quadrant. -/
theorem contDiffOn_three_Mf_mul_Bf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : H6Adm α f) :
    ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Bf α f z θ))
      Work.FTS.EllipticEst.Q0 := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem3 : Work.Spaces.HkMem α 3 f :=
    HkMem_of_le_of_smoothOpen α (by norm_num) hsm hf.reg.2
  have hL12 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 3 f hα hα1 hsm hmem3 (by norm_num)
  have hMf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1)
      Work.FTS.EllipticEst.Q0 := cd_radial hL12
  have hBf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Bf α f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := cd_Bf hsm
  refine (hMf.mul hBf).congr (fun p _ => ?_)
  simp only [Function.uncurry, Mf]

/-- **The smoothness of the local half** `Wf α f`, `C³` on the open quadrant. -/
theorem contDiffOn_three_Wf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 3 (Function.uncurry (Wf α f)) Work.FTS.EllipticEst.Q0 := by
  have hDzf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Dz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm.Dz 3
  have hc2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_c2m
  have hL12F : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Construction.L12 (Work.Construction.Fstar α) p.1)
      Work.FTS.EllipticEst.Q0 := by
    have hrad : ContDiffOn ℝ 3 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
      have hnum : ContDiffOn ℝ 3 (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
      have hden : ContDiffOn ℝ 3 (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
        contDiffOn_const.add contDiffOn_id
      have hdiv := hnum.div hden
        (fun z hz => ne_of_gt (by linarith [show (0 : ℝ) < z from hz]))
      refine hdiv.congr (fun z _ => ?_)
      simp only [Pi.div_apply]
    refine (cd_radial hrad).congr (fun p hp => ?_)
    obtain ⟨hz, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  refine (hc2m.mul (hL12F.mul hDzf)).congr (fun p _ => ?_)
  simp only [Function.uncurry, Wf]
  ring

/-- **The smoothness conjunct**: `N0gSum α f` is `C³` on the open quadrant. -/
theorem contDiffOn_three_N0gSum {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : H6Adm α f) :
    ContDiffOn ℝ 3 (Function.uncurry (N0gSum α f)) Work.FTS.EllipticEst.Q0 := by
  have h1 := contDiffOn_three_Mf_mul_Bf (f := f) hα hα1 hf
  have h2 := contDiffOn_three_Wf (f := f) hα hα1 hf.reg.1
  rw [N0gSum_eq α f]
  exact (h1.sub h2).congr (fun p _ => by simp only [Function.uncurry])

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option autoImplicit false

/-! ## The `(0,0)`-deleted double `range`-sum

The Leibniz rule `leibniz_Dth` of `SlicePrep` expands `mixed b a (f · D_θ g)` into a double
`Finset.range`-sum over `i ∈ range (a+1)`, `j ∈ range (b+1)`; the summand at `(i,j) = (0,0)`
is the pure angular transport term `f · D_θ (D_z^b D_θ^a g)`.  The statement `leibnizRem6`
deletes that single summand, so the combinatorial content of its proof is the elementary
identity

`∑_i ∑_j (if (i,j) = (0,0) then 0 else C i j) = (∑_i ∑_j C i j) - C 0 0`. -/

private lemma sum_range_sum_range_ite_zero (a b : ℕ) (C : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j) - C 0 0 := by
  have hzero : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then C i j else 0)) = C 0 0 := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then C i j else 0)) = if i = 0 then C 0 0 else 0 := by
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl]
        rw [show (∑ j ∈ Finset.range (b + 1), (if 0 = 0 ∧ j = 0 then C 0 j else 0))
            = ∑ j ∈ Finset.range (b + 1), (if j = 0 then C 0 j else 0) from by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = 0 <;> simp [hj]]
        rw [Finset.sum_ite_eq']
        simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        rintro ⟨h, -⟩
        exact hi h
    calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then C i j else 0))
        = ∑ i ∈ Finset.range (a + 1), (if i = 0 then C 0 0 else 0) :=
          Finset.sum_congr rfl fun i _ => hinner i
      _ = C 0 0 := by
          rw [Finset.sum_ite_eq']
          simp
  have hpt : ∀ i j : ℕ, (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j)
      = C i j - (if i = 0 ∧ j = 0 then C i j else 0) := by
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (C i j - (if i = 0 ∧ j = 0 then C i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
        - ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then C i j else 0) := by
        simp only [Finset.sum_sub_distrib]
    _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j) - C 0 0 := by
        rw [hzero]

/-- **The Leibniz rule for `mixed b a (f · D_θ g)` with the transport term deleted.**  With
`leibniz_Dth` (`SlicePrep`) in hand this is pure bookkeeping: the deleted `(0,0)`-summand of
that expansion is exactly `f · D_θ (D_z^b D_θ^a g)`, since `D_θ` commutes with `D_z` on the
open quadrant (`DthIter_DzIter_eq_mixed_open`). -/
theorem leibnizRem6 {f g : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (a b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
        - f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i f z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) g z θ)) := by
  intro z θ hz hθ0 hθ1
  -- The transport term `D_θ (D_z^b D_θ^a g)` is the `(0,0)`-summand of the expansion.
  have hshift : Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed b (a + 1) g z θ := by
    have hda : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.Spaces.DthIter a g))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hG.DthIter a)
    have h := Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hda b 1 hz ⟨hθ0, hθ1⟩
    simpa [Work.Spaces.mixed] using h
  have hB : f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = (a.choose 0 : ℝ) * (b.choose 0 : ℝ)
          * (Work.Spaces.mixed 0 0 f z θ
              * Work.Spaces.mixed (b - 0) (a - 0 + 1) g z θ) := by
    rw [Nat.choose_zero_right, Nat.choose_zero_right, Nat.sub_zero, Nat.sub_zero, hshift]
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
    ring
  rw [leibniz_Dth hF hG b a z θ hz hθ0 hθ1, hB]
  exact (sum_range_sum_range_ite_zero a b
    (fun i j => (a.choose i : ℝ) * (b.choose j : ℝ)
      * (Work.Spaces.mixed j i f z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) g z θ))).symm

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
