/-
# `Work.FTS.StrongPersist.Basic` — the elementary API of the chapter

This file holds the parts of the `StrongPersist` interface a caller (S1 `lwp_H6`, S4/S5
`StrongGlobal`, the regularity transfer `RegPkgGal`) needs without going through the
persistence proof itself:

* nonnegativity of the level-six energy and norm, and the identification of `Xn6` with the
  square root of `Sq6`;
* the pointwise monotonicity of the `ℋ^k`-integrand in the order `k` (taken from the sibling
  area `FTS/StrongLWP`, where the whole monotonicity API of the strong route is proved) and the
  consequences `ℋ⁶ ⊂ ℋ⁴` at the level of `HkMem`, `HkSq`, `HkNorm`, the bound predicates
  `XnBddOn`, and `RegPkgMin.mem4`;
* the existence of the square-root form of `Xn6`;
* the projections of the clause packages `N6Norm`, `N6Trans`, `H6Coer`, `H6Pair`, `L6Ctx`,
  `RegPkgMin`, `RegPkgH6`;
* the **bridges** between this chapter's copies of `IsBslSolPos` / `RegPkgMin` / `Xn6` and the
  sibling area's (`Work.FTS.StrongLWP`), so that S2/S6 can be consumed in either vocabulary.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity and the square-root form -/

theorem Sq6_nonneg (α : ℝ) (f : Fn) : 0 ≤ Sq6 α f := Work.Spaces.HkSq_nonneg α 6 f

theorem Xn6_nonneg (α : ℝ) (f : Fn) : 0 ≤ Xn6 α f := Real.sqrt_nonneg _

/-- `Xn6` is the square root of `Sq6`, definitionally. -/
theorem Xn6_eq_sqrt (α : ℝ) (f : Fn) : Xn6 α f = Real.sqrt (Sq6 α f) := rfl

theorem Xn6_sq (α : ℝ) (f : Fn) : Xn6 α f ^ 2 = Sq6 α f := Real.sq_sqrt (Sq6_nonneg α f)

theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : Fn) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ

/-! ## Monotonicity in the order -/

/-- **Pointwise monotonicity of the `ℋ^k`-integrand in the order** (`k' ≤ k ⟹ ≤`).  This is
`Work.FTS.StrongLWP.HkIntegrand_mono`, the pointwise half of `ℋ^k ⊂ ℋ^{k'}`. -/
theorem HkIntegrand_le_of_le (α : ℝ) {k k' : ℕ} (hkk : k ≤ k') (f : Fn) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α k' f z θ :=
  Work.FTS.StrongLWP.HkIntegrand_mono α f hkk z θ

/-- **`ℋ⁶ ⊂ ℋ⁴` at the level of the norm**: the order-`6` norm dominates the order-`4` one
(the order-`6` membership is what makes the comparison meaningful). -/
theorem Xn_le_Xn6 (α : ℝ) {f : Fn} (hf : H6Mem α f) : Xn α f ≤ Xn6 α f :=
  Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4) (by norm_num) hf

/-- **`ℋ^k`-membership descends in the order**, for data smooth on the open quadrant: the
level-`k` integrand is a sub-sum of the level-`k'` one and `SmoothOpen` supplies the a.e. strong
measurability of the smaller one.  (Thin wrapper around
`Work.FTS.EllipticEst.TT.HkMem_descend_open`; it is what turns S2's order-`6` output into the
order-`4` membership `RegPkgMin.mem4` asks for.) -/
theorem HkMem_of_le_of_smoothOpen (α : ℝ) {k k' : ℕ} (hkk : k ≤ k') {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.Spaces.HkMem α k' f) :
    Work.Spaces.HkMem α k f :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open hkk
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm) hf

/-- The `ℋ⁴`-membership of a slice whose `ℋ⁶`-membership and interior smoothness are known —
the form in which S2's output feeds `RegPkgMin.mem4`. -/
theorem HkMem_four_of_six {α : ℝ} {f : Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hf : H6Mem α f) : Work.Spaces.HkMem α 4 f :=
  HkMem_of_le_of_smoothOpen α (by norm_num) hsm hf

/-- **A uniform `ℋ⁶`-bound gives a uniform `ℋ⁴`-bound** on `[0,T)`: the transfer that the
a-priori argument needs when S2 supplies the order-`6` package.  (Only the *bound* is
transferred; the `ℋ⁴`-*membership* of the slice is a separate obligation — the order-`4`
integrand need not be a.e. strongly measurable for a bare `HkMem α 6` datum, which is why
`StrongLWP.RegPkgH6.mem4_of` takes the monotonicity of membership as a hypothesis.) -/
theorem Xn4_le_of_Xn6BddOn {α T M : ℝ} {g : Fam} (h : Xn6BddOn α g T M) :
    ∀ τ, 0 ≤ τ → τ < T → Xn α (slice g τ) ≤ M := by
  intro τ hτ hτT
  obtain ⟨hmem, hbnd⟩ := h τ hτ hτT
  exact le_trans (Xn_le_Xn6 α hmem) hbnd

/-! ## The integrand vanishes on the axis -/

/-- At `z = 0` the radial weight `w 0 = (1+0)²/0²` is `0` by the totalised division of `ℝ`, so
**every** summand of the `ℋ^k`-integrand vanishes.  This is the null-set fact which makes the
`z = 0` end of the domain harmless in all a.e. arguments of the chapter. -/
theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : Fn) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hWt : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, hw]
  unfold Work.Spaces.HkIntegrand
  simp only [hw, hWt, mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

/-! ## Projections of the clause packages -/

theorem N6Norm.prod' {Xi Cpow α₂ α : ℝ} (h : N6Norm Xi Cpow α₂)
    (hα : α ∈ Set.Ioc 0 α₂) {f g : Fn} (hf : HQo α 6 f) (hg : HQo α 6 g) :
    H6Mem α (fun z θ => f z θ * g z θ) ∧
      Xn6 α (fun z θ => f z θ * g z θ) ≤ Xi * α ^ (-Cpow) * Xn6 α f * Xn6 α g :=
  h.prod α hα f g hf hg

theorem N6Trans.t2' {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (h : N6Trans IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {f g : Fn} (hf₁ : Work.FTS.EllipticEst.SmoothOpen f)
    (hf₂ : H6Mem α f) (hf₃ : Work.FTS.VocabO.CoefThMem 1 f) (hg₁ : HQo α 6 g)
    (hg₂ : Work.Spaces.HkMem α 7 g) (hg₃ : Work.Spaces.DecayAll 6 g) :
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Xn6 α f + Work.FTS.VocabO.CoefTh 1 f) * Xn6 α g ^ 2 :=
  h.t2 α hα f g hf₁ hf₂ hf₃ hg₁ hg₂ hg₃

theorem H6Pair.pair' {IP : ℝ → Fn → Fn → ℝ} {α₂ Ce Cp α M τ Cs : ℝ} (h : H6Pair IP α₂ Ce Cp)
    {g Φ : Fam} {E : Fn → Fn} {Φs : Fn} (hα : α ∈ Set.Ioc 0 α₂) (hτ : 0 ≤ τ)
    (hcx : L6Ctx IP α M Ce Cs E Φs g Φ τ) :
    |IP α (dynRHS α Φ g τ) (slice g τ)|
      ≤ Cp * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
          * (1 + Sq6 α (slice g τ)) :=
  h.pair α hα g Φ τ M Cs E Φs hτ hcx

/-! ## The `XnBddOn` API -/

theorem XnBddOn.mono_M {α : ℝ} {k : ℕ} {g : Fam} {T M M' : ℝ} (h : XnBddOn α k g T M)
    (hM : M ≤ M') : XnBddOn α k g T M' :=
  fun τ hτ hτT => ⟨(h τ hτ hτT).1, le_trans (h τ hτ hτT).2 hM⟩

theorem XnBddOn.mono_T {α : ℝ} {k : ℕ} {g : Fam} {T T' M : ℝ} (h : XnBddOn α k g T M)
    (hT : T' ≤ T) : XnBddOn α k g T' M :=
  fun τ hτ hτT => h τ hτ (lt_of_lt_of_le hτT hT)

theorem XnBddOn_mem {α : ℝ} {k : ℕ} {g : Fam} {T M : ℝ} (h : XnBddOn α k g T M)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) : Work.Spaces.HkMem α k (slice g τ) :=
  (h τ hτ hτT).1

/-! ## Projections of the regularity packages -/

theorem RegPkgMin.mem4' {α : ℝ} {g : Fam} (h : RegPkgMin α g) {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.Spaces.HkMem α 4 (slice g τ) := h.mem4 τ hτ

theorem RegPkgH6.mem6' {α C : ℝ} {g : Fam} (h : RegPkgH6 α C g) {τ : ℝ} (hτ : 0 ≤ τ) :
    H6Mem α (slice g τ) := h.mem6 τ hτ

theorem RegPkgH6.bd6' {α C : ℝ} {g : Fam} (h : RegPkgH6 α C g) {τ : ℝ} (hτ : 0 ≤ τ) :
    Xn6 α (slice g τ) ≤ C := h.bd6 τ hτ

/-- **`RegPkgMin` plus a uniform `ℋ⁶` bound on `[0,T)` gives the `RegPkgMin.mem4`-compatible
form of S2's conclusion** on that interval, and (through `Xn4BddOn_of_Xn6BddOn`) the `ℋ⁴`-bound
the continuation argument consumes. -/
theorem RegPkgMin.xn6BddOn {α M T : ℝ} {g : Fam} (h : RegPkgMin α g)
    (h6 : ∀ τ, 0 ≤ τ → τ < T → H6Mem α (slice g τ) ∧ Xn6 α (slice g τ) ≤ M) :
    Xn6BddOn α g T M := h6

/-- **`RegPkgMin` together with a uniform `ℋ⁶`-bound on `[0,T)` is `RegPkgH6`** (in the sense of
this chapter's `RegPkgH6`, i.e. the bound is part of the conclusion): the bridge the
continuation argument S5 uses. -/
theorem RegPkgH6.of_bdd {α C T : ℝ} {g : Fam} (h : RegPkgMin α g)
    (h6 : ∀ τ, 0 ≤ τ → H6Mem α (slice g τ)) (hb : ∀ τ, 0 ≤ τ → Xn6 α (slice g τ) ≤ C) :
    RegPkgH6 α C g :=
  ⟨h, h6, hb⟩

/-! ## Bridges to the sibling area `FTS/StrongLWP`

The S1/S3 area (`Work.FTS.StrongLWP`) carries its own copies of `IsBslSolPos`, `RegPkgMin`,
`RegPkgH6` and `Xn6`.  The two `IsBslSolPos` differ only in the bracketing of the two Dirichlet
identities; the two `RegPkgMin` have the same fields in the same order.  The bridges below let a
consumer use S2 (`persist_H6`) and S6 (`dbd_of_eq`) together with S1/S3 in either vocabulary. -/

theorem isBslSolPos_iff_lwp {α : ℝ} {F Ψ : Fn} :
    IsBslSolPos α F Ψ ↔ Work.FTS.StrongLWP.IsBslSolPos α F Ψ :=
  Iff.rfl

theorem RegPkgMin.toLWP {α : ℝ} {g : Fam} (h : RegPkgMin α g) :
    Work.FTS.StrongLWP.RegPkgMin α g :=
  ⟨h.c1, h.c4, h.cont, h.mem4, h.dbd, h.vanish⟩

theorem RegPkgMin.ofLWP {α : ℝ} {g : Fam} (h : Work.FTS.StrongLWP.RegPkgMin α g) :
    RegPkgMin α g :=
  ⟨h.c1, h.c4, h.cont, h.mem4, h.dbd, h.vanish⟩

theorem Xn6_eq_LWP (α : ℝ) (f : Fn) : Xn6 α f = Work.FTS.StrongLWP.Xn6 α f := rfl

theorem isStrongSolOn_iff_lwp {α T : ℝ} {Φ g : Fam} :
    IsStrongSolOn α Φ g T ↔
      ((∀ τ, 0 ≤ τ → τ < T → Work.FTS.StrongLWP.IsBslSolPos α
          (Work.Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEqOnUpTo α Φ g T) := by
  constructor
  · intro h
    exact ⟨fun τ hτ hτT => (isBslSolPos_iff_lwp).1 (h.1 τ hτ hτT), h.2⟩
  · intro h
    exact ⟨fun τ hτ hτT => (isBslSolPos_iff_lwp).2 (h.1 τ hτ hτT), h.2⟩

end Work.FTS.StrongPersist
