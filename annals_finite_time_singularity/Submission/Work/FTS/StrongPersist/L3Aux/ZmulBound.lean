import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.IPGen.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false

/-! ## The coefficient constant -/

/-- The single constant dominating the six step coefficients of the coercive recursion
`Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''`: `max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))))`.

It is the constant appearing in the design's `ip4SlotDomGen` (`FTS_ELL_GALERKIN.md` §2), and
the reason the statement there is phrased with `0 ≤ cᵢ`: any choice of `c₁ = 1` for the `D_θ`
slots works, while the `D_z` coefficients must be taken small, so the coefficients cannot be
pinned to `1` (`CoercivityFix/NOTES.md` §1: unit steps force the unsatisfiable balance
`CC√κ ≤ cc/2`). -/
def CoefMax (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℝ :=
  max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))))

theorem one_le_coefMax (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : 1 ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' :=
  le_max_left _ _








theorem le_coefMax₁ {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₁ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₁ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_left _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem le_coefMax₂ {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₂ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₂ ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) := le_max_left _ _
    _ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem le_coefMax₁' {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₁' ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₁' ≤ max c₁' (max c₂' (max c₁'' c₂'')) := le_max_left _ _
    _ ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) := le_max_right _ _
    _ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem le_coefMax₂' {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₂' ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₂' ≤ max c₂' (max c₁'' c₂'') := le_max_left _ _
    _ ≤ max c₁' (max c₂' (max c₁'' c₂'')) := le_max_right _ _
    _ ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) := le_max_right _ _
    _ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem le_coefMax₁'' {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₁'' ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₁'' ≤ max c₁'' c₂'' := le_max_left _ _
    _ ≤ max c₂' (max c₁'' c₂'') := le_max_right _ _
    _ ≤ max c₁' (max c₂' (max c₁'' c₂'')) := le_max_right _ _
    _ ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) := le_max_right _ _
    _ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem le_coefMax₂'' {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    c₂'' ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  calc c₂'' ≤ max c₁'' c₂'' := le_max_right _ _
    _ ≤ max c₂' (max c₁'' c₂'') := le_max_right _ _
    _ ≤ max c₁' (max c₂' (max c₁'' c₂'')) := le_max_right _ _
    _ ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) := le_max_right _ _
    _ ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _
    _ ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _


/-! ## The recursion with arbitrary step coefficients -/

/-- The paper's step recursion `HkIPStep c₁ c₂`, iterated `n` times from the base `H1IP α`:
`IPnG c₁ c₂ α 0 = H1IP α`, `IPnG c₁ c₂ α (n+1) = HkIPStep c₁ c₂ (IPnG c₁ c₂ α n)`. -/
def IPnG (c₁ c₂ : ℝ) (α : ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | n + 1 => Work.Coercivity.HkIPStep c₁ c₂ (IPnG c₁ c₂ α n)

@[simp] theorem IPnG_zero (c₁ c₂ α : ℝ) : IPnG c₁ c₂ α 0 = Work.Coercivity.H1IP α := rfl
@[simp] theorem IPnG_succ (c₁ c₂ α : ℝ) (n : ℕ) :
    IPnG c₁ c₂ α (n + 1) = Work.Coercivity.HkIPStep c₁ c₂ (IPnG c₁ c₂ α n) := rfl



/-- **`Assembly.IP4` is the three-step composite of `IPnG`**, i.e. the recursion with the three
explicit coefficient pairs. -/
theorem IPnG_eq_IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) :
    Work.Coercivity.HkIPStep c₁'' c₂''
        (Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1))
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α := rfl

/-! ## The corrected `N4Extra'` contract

`Work.FTS.OpenPkg.N4Extra' IP α₂ Ct` is the primed `IP`-level contract consumed by the rows.
Its five algebraic clauses take `Work.Spaces.HkMem α 4` of the first argument(s) — a
hypothesis that records the *integrability* of the `ℋ⁴`-integrand but **no smoothness**.  The
design (`FTS_ELL_GALERKIN.md`, "New defects") observes that this makes `cs` and `add` junk
traps: the pairing `IP4` is built out of the derivatives `D_z^bD_θ^a f`, and `HkMem α 4 f`
says nothing about them when `f` is not smooth (take `f₁ = h` nowhere differentiable,
`f₂ = s − h` smooth; then `HkMem α 4 fᵢ` holds with `f = h` and `f = s − h` while the
derivative slots of `f₁` are Lean's junk value, so `IP(f₁ + f₂, g) ≠ IP(f₁, g) + IP(f₂, g)`).

The repair is to strengthen those five clauses to the class `VocabO.HQo α 4`
(`= SmoothOpen ∧ HkMem α 4`, interior `C^∞` plus honesty).  Everything else is copied
verbatim from `N4Extra'`: in particular the *second* argument of `cs`/`add`/`smul`/`neg`/
`congr` keeps the frozen class `RegQ α 4` (the design's fix concerns the hypotheses on the
first argument(s) only), and `t2`/`t3` are the frozen `VocabO.T2Clause`/`T3Clause`, which
already carry the flat coefficient norm and the order-5 honesty that remove the corresponding
junk traps. -/
structure N4ExtraQ (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm, with a `C^∞`-and-honest first argument. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f →
    Work.FTS.Nonlin.RegQ α 4 g → |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- Additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, Work.FTS.VocabO.HQo α 4 f₁ →
    Work.FTS.VocabO.HQo α 4 f₂ → Work.FTS.Nonlin.RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- Homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), Work.FTS.VocabO.HQo α 4 f →
    Work.FTS.Nonlin.RegQ α 4 g → IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Negation in the first argument. -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f →
    Work.FTS.Nonlin.RegQ α 4 g → IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, Work.FTS.VocabO.HQo α 4 f →
    Work.FTS.VocabO.HQo α 4 f' → Work.FTS.Nonlin.RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- The `D_z`-self-pairing, lossless (design §5 T5). -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g →
    |IP α (Work.Spaces.Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2S`: transport with `D_z` and a flat angular coefficient (`VocabO.T2Clause`). -/
  t2 : Work.FTS.VocabO.T2Clause IP α₂ Ct
  /-- `T3S`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient (`VocabO.T3Clause`). -/
  t3 : Work.FTS.VocabO.T3Clause IP α₂ Ct
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient, in the `D`-sup norm. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.VocabO.WDMem 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 f * Xn α g ^ 2
  /-- `STQ`: `SpecialTransport` (tex 1258), the derivative falling on a coefficient which
  vanishes at the angular ends. -/
  st : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.VanishTheta f →
    Work.FTS.VocabO.WDMem 4 (Work.Spaces.pth f) → Work.FTS.Nonlin.RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.pth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 (Work.Spaces.pth f) * Xn α g ^ 2

/-! ## The linearity package `IPLinHQo` (design §4, item "IP linearity on the open class") -/


end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Slices of the `D_z`-iterates

`D_z` sees its argument only through the `θ`-slices, so an iterated `D_z` is the corresponding
one-variable iterate of the slice. -/
theorem DzIter_slice (f : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter k f z θ = Work.Elliptic.DzdIter k (fun z' => f z' θ) z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.DzIter_succ, Work.Elliptic.DzdIter_succ]
      show z * deriv (fun z' => Work.Spaces.DzIter k f z' θ) z
        = z * deriv (Work.Elliptic.DzdIter k (fun z' => f z' θ)) z
      congr 1
      exact congrFun (congrArg deriv (funext (fun z' => ih z'))) z

/-! ## The `D_z`-iterates of `L₁₂(g)` and the angular moments of `g`

`Q_k(g)(z) = ∫_θ K(θ)·D_z^k g(z,θ) dθ` is the angular moment, and `D_z^{k+1}L₁₂(g) = -Q_k(g)`.
This repackages the argument that already occurs *inside* the proof of `Work.FTS.H2.L12HQ`. -/
theorem L12_dzdIter_moment (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z)
    ∧ (∀ b : ℕ, b ≤ 3 → ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z)) z) := by
  have hEE : Work.Construction.L12 g = Work.Elliptic.L12 g :=
    Work.FTS.H2.constructionL12_eq_ellipticL12 g
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.FTS.H2.L12densIntegrable α g hα hα1 hsm hmem
  have h0' : Work.Elliptic.L12 g 0 = 0 := by rw [← hEE]; exact h0
  obtain ⟨hval, htend, hcont⟩ := Work.Elliptic.L12_values g hint h0'
  obtain ⟨hQang_deriv, hQang_cont⟩ := Work.FTS.H2.QangDiff α g hα hα1 hsm hmem
  have hdens_contOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    have hdiv : ContinuousOn (fun z => Work.Elliptic.Qang g 0 z / z) (Set.Ioi 0) :=
      (hQang_cont 0 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
    exact hdiv.congr (fun z _ => Work.Elliptic.L12dens_eq_Qang_div g z)
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have hintv : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact hint.mono_set Set.Ioc_subset_Ioi_self
    have hprim := intervalIntegral.integral_hasDerivAt_right hintv
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hdens_contOn z hz)
      (hdens_contOn.continuousAt (isOpen_Ioi.mem_nhds hz))
    refine hprim.neg.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact hval y hy.le
  have hgen : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
    intro k
    induction k with
    | zero =>
        intro _ z hz
        have hd : deriv (fun z => Work.Elliptic.L12 g z) z
            = -(Work.Elliptic.L12dens g z) := (hderiv z hz).deriv
        change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
        rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
          mul_div_cancel₀ _ (ne_of_gt hz)]
    | succ n ih =>
        intro hn z hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, mul_neg, neg_inj, (hQang_deriv n (by omega) z hz).deriv,
          mul_div_cancel₀ _ (ne_of_gt hz)]
  have hgenC : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
    intro k hk z hz
    rw [show (fun z => Work.Construction.L12 g z) = (fun z => Work.Elliptic.L12 g z) from
      funext fun z => congrFun hEE z]
    exact hgen k hk z hz
  refine ⟨hgenC, ?_⟩
  intro b hb z hz
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    rw [Work.Elliptic.DzdIter_zero]
    exact (hderiv z hz).differentiableAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrFun hEE y)
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hc2 : c ≤ 2 := by omega
    have hev : Work.Elliptic.DzdIter (c + 1) (fun z => Work.Construction.L12 g z)
        =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g c z') := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact hgenC c (by omega) z' hz'
    exact ((hQang_deriv c hc2 z hz).differentiableAt.neg).congr_of_eventuallyEq hev

/-! ## A pointwise Leibniz rule for a *radial* factor

`Work.Spaces.mixed_mul_eq` (and its radial specialisation in `RadialProd`) requires the radial
factor to be `SmoothQuad`, i.e. `C^∞` on `(-1,∞)`.  `L₁₂(g)` only has three derivatives on
`(0,∞)` (that is all `HkMem α 4 g` gives), so we need the Leibniz rule under the pointwise
differentiability of the iterates of the radial factor. -/

/-- The `θ`-derivatives do not see a factor of `z` alone.  (Pointwise in `z`; no regularity of
`r` is used, only the unconditional constant rule `RowsN0Aux.deriv_const_mul'`.) -/
theorem dthIter_mul_radial (r : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => r z * h z θ)
      = fun z θ => r z * Work.Spaces.DthIter i h z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => r z * Work.Spaces.DthIter i h z θ') θ
        = r z * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i h z θ') θ)
      rw [RowsN0Aux.deriv_const_mul']
      ring

/-- **The one-variable Leibniz rule for `DzdIter = (z ∂_z)^j`**, with the differentiability of
the iterates assumed on the open half-line (which is where `L₁₂(g)` is differentiable).  The
hypotheses `b < j` are exactly what the induction consumes: differentiating the identity for
`j = n` needs the summands `(DzdIter b u)(DzdIter (n-b) v)`, `b ≤ n`, to be differentiable,
i.e. `DzdIter b u` for `b < n+1` and `DzdIter (n-b) v` for `n-b < n+1`. -/
theorem dzdIter_mul_leibniz (j : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ
      (Work.Elliptic.DzdIter b u) z')
    (hv : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ
      (Work.Elliptic.DzdIter b v) z') :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z' => u z' * v z') z
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (j - b) v z) := by
  induction j with
  | zero =>
      intro z _
      rw [Finset.sum_range_one, Nat.choose_zero_right, Work.Elliptic.DzdIter_zero]
      norm_num
  | succ n ih =>
      intro z hz
      have hu' : ∀ b : ℕ, b < n → ∀ w ∈ Set.Ioi (0 : ℝ),
          DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) w := fun b hb => hu b (by omega)
      have hv' : ∀ b : ℕ, b < n → ∀ w ∈ Set.Ioi (0 : ℝ),
          DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) w := fun b hb => hv b (by omega)
      have hih := ih hu' hv'
      -- the identity holds on `(0,∞)`, hence eventually at `z`
      have hev : (fun w => Work.Elliptic.DzdIter n (fun z' => u z' * v z') w)
          =ᶠ[𝓝 z] (fun w => ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)
              * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (n - b) v w)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hih w hw
      rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      rw [hev.deriv_eq]
      -- differentiate the finite sum
      have hder : deriv (fun w => ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)
            * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (n - b) v w)) z
          = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)
              * (deriv (Work.Elliptic.DzdIter b u) z * Work.Elliptic.DzdIter (n - b) v z
                + Work.Elliptic.DzdIter b u z * deriv (Work.Elliptic.DzdIter (n - b) v) z) := by
        rw [show (fun w => ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)
              * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (n - b) v w))
            = (∑ b ∈ Finset.range (n + 1), fun w => (n.choose b : ℝ)
              * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (n - b) v w)) from by
          funext w; rw [Finset.sum_apply]]
        rw [deriv_sum]
        · refine Finset.sum_congr rfl fun b hb => ?_
          have hb' : b < n + 1 := Finset.mem_range.mp hb
          rw [deriv_const_mul]
          · rw [show (fun w => Work.Elliptic.DzdIter b u w
                * Work.Elliptic.DzdIter (n - b) v w)
                = (Work.Elliptic.DzdIter b u * Work.Elliptic.DzdIter (n - b) v) from rfl]
            rw [deriv_mul (hu b hb' z hz) (hv (n - b) (by omega) z hz)]
          · exact (hu b hb' z hz).mul (hv (n - b) (by omega) z hz)
        · intro b hb
          have hb' : b < n + 1 := Finset.mem_range.mp hb
          exact ((hu b hb' z hz).mul (hv (n - b) (by omega) z hz)).const_mul _
      rw [hder, Finset.mul_sum]
      -- rewrite each summand with `z * deriv (DzdIter b u) z = DzdIter (b+1) u z`, then Pascal
      have hstep : (∑ b ∈ Finset.range (n + 1),
            z * ((n.choose b : ℝ)
              * (deriv (Work.Elliptic.DzdIter b u) z * Work.Elliptic.DzdIter (n - b) v z
                + Work.Elliptic.DzdIter b u z * deriv (Work.Elliptic.DzdIter (n - b) v) z)))
          = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)
              * (Work.Elliptic.DzdIter (b + 1) u z * Work.Elliptic.DzdIter (n - b) v z
                + Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (n - b + 1) v z) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have h1 : Work.Elliptic.DzdIter (b + 1) u z
            = z * deriv (Work.Elliptic.DzdIter b u) z := rfl
        have h2 : Work.Elliptic.DzdIter (n - b + 1) v z
            = z * deriv (Work.Elliptic.DzdIter (n - b) v) z := rfl
        rw [h1, h2]
        ring
      rw [hstep]
      exact Work.Spaces.leibniz_step n (fun b => Work.Elliptic.DzdIter b u z)
        (fun b => Work.Elliptic.DzdIter b v z)


/-! ## The pointwise bounds on `L₁₂(g)` and its iterates

`B(z) := ∫_θ HkIntegrand α 4 g z θ dθ` is the `θ`-slice of the `ℋ⁴`-density of `g`; it is
integrable on `Iz` with `∫_z B = HkSq α 4 g`. -/

/-- The `z`-pointwise slot bound for the iterates of `L₁₂(g)`: `D_z^bL₁₂(g) = -Q_{b-1}(g)` and
the angular moment is dominated by the weighted `θ`-mass of the corresponding slot of `g`. -/
theorem L12_iterate_sq_slot_le (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0)
    {b : ℕ} (hb1 : 1 ≤ b) (hb4 : b ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * (z ^ 4 / (1 + z) ^ 4)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
  have hk : b - 1 ≤ 3 := by omega
  have hgen := (L12_dzdIter_moment α hα hα1 hsm hmem h0).1 (b - 1) hk z hz
  have hbsucc : b = (b - 1) + 1 := by omega
  rw [hbsucc, hgen, neg_sq]
  have h1 := Work.FTS.H2.Qang_sq_leQ α g hsm hmem (b - 1) (by omega) hz
  -- the weighted `θ`-slice bound
  have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (b - 1) g z θ) ^ 2)
      * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.DzIter (b - 1) g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [Work.Spaces.Iθ]
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        have h2 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g (b - 1) (by omega) hz hθ
        have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Work.Spaces.w z))
        rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h3)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hmem.1 z (le_of_lt hz)) hae
    simpa only [MeasureTheory.integral_mul_const] using hmono
  have hw2 : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
  have hK1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  calc (Work.Elliptic.Qang g (b - 1) z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (b - 1) g z θ) ^ 2) := h1
    _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (b - 1) g z θ) ^ 2)
              * (Work.Spaces.w z) ^ 2) / (Work.Spaces.w z) ^ 2) := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hw2)]
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
              / (Work.Spaces.w z) ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hslice hw2.le) hK1nn
    _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * (z ^ 4 / (1 + z) ^ 4)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
          have hwinv : ((Work.Spaces.w z) ^ 2)⁻¹ = z ^ 4 / (1 + z) ^ 4 := by
            rw [Work.Spaces.w, div_pow, inv_div]
            congr 1 <;> ring
          rw [div_eq_mul_inv, ← hwinv]
          ring

/-- `w²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-- **The `z`-uniform bound on the angular moments.**  For `i ≤ 3`,
`(Q_i(g)(z))² ≤ (∫_θ K²)·|g|²_{ℋ⁴}` at *every* `z > 0`: the `z`-direction Hardy inequality
applied to the slices `s ↦ D_z^i g(s,θ)` removes the `z`-dependence, and the resulting
`θ`-integral is the `ℋ⁴`-mass of `g` (`HkSqSwapQ`). -/
theorem Qang_sq_le_const (α : ℝ) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hdec : ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0))
    {i : ℕ} (hi : i ≤ 3) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  obtain ⟨hswap_eq, hswap_int, hswap_slice⟩ := Work.H2.T1Q.HkSqSwapQ α g hsm hmem
  have hK1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := π / 2)).symm
  have hmemIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [hIoo]; exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- the Hardy bound, for a.e. angle
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DzIter i g z θ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ := by
    filter_upwards [hswap_slice, hmemIoo] with θ hslice hθ
    -- the Hardy integrand of the `θ`-slice
    have hφint : MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.DzIter (i + 1) g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hslice
        (Work.H2.T1Q.aesm_Iz_of_continuousOn ?_) ?_
      · exact (((hsm.DzIter (i + 1)).curry_z hθ).mono
            (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).continuousOn.pow 2 |>.mul
          (continuousOn_w_sq.mono (Set.Ioi_subset_Ioi le_rfl))
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with s hs
        have hs' : 0 ≤ s := hs
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        rcases lt_or_eq_of_le hs' with hspos | rfl
        · have h2 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g (i + 1) (by omega)
            hspos hθ
          have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Work.Spaces.w s))
          rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hspos)))] at h3
        · simpa [Work.Spaces.w] using Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
    have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.DzIter i g s θ) (Set.Ioi (0 : ℝ)) :=
      ((hsm.DzIter i).curry_z hθ).mono
        (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) |>.of_le (by
          simp [Work.Stability.smoothOrder])
    have hH := Work.FTS.H2.HQ.HardyZQ (fun s => Work.Spaces.DzIter i g s θ) hcd
      (hdec i hi θ (Set.Ioo_subset_Icc_self hθ)) hφint z hz
    refine hH.trans ?_
    -- the dominated `θ`-slice integral
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hslice ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with s hs
    have hs' : 0 ≤ s := hs
    rcases lt_or_eq_of_le hs' with hspos | rfl
    · have h2 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g (i + 1) (by omega) hspos hθ
      have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Work.Spaces.w s))
      rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hspos)))] at h3
    · simpa [Work.Spaces.w] using Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
  have hInt : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 g s θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) hswap_int hae
  calc (Work.Elliptic.Qang g i z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2) :=
        Work.FTS.H2.Qang_sq_leQ α g hsm hmem i (by omega) hz
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α 4 g s θ) :=
        mul_le_mul_of_nonneg_left hInt hK1nn
    _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
        rw [hswap_eq]

/-- Cauchy–Schwarz in the form `(∫ √B·u)² ≤ (∫B)(∫u²)`, for `B ≥ 0`. -/
private theorem cs_sqrt_mul {B u : ℝ → ℝ} {s : Set ℝ} (hBnn : ∀ x, 0 ≤ B x)
    (hBint : MeasureTheory.IntegrableOn B s)
    (hBaesm : MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s))
    (huint : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s)
    (huaesm : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s)) :
    (∫ x in s, Real.sqrt (B x) * u x) ^ 2 ≤ (∫ x in s, B x) * (∫ x in s, (u x) ^ 2) := by
  have h1 : MeasureTheory.MemLp (fun x => Real.sqrt (B x)) 2 (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hBaesm)]
    exact hBint.congr (Filter.Eventually.of_forall fun x => (Real.sq_sqrt (hBnn x)).symm)
  have h2 : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr huint
  have h := Work.Spaces.cs_integral h1 h2
  rw [show (∫ x in s, (Real.sqrt (B x)) ^ 2) = ∫ x in s, B x from
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))] at h
  exact h

/-- `∫_{(0,z)} (x/(1+x)²)² ≤ z³/3`. -/
private theorem u_sq_Ioc_le {z : ℝ} (hz : 0 ≤ z) :
    ∫ x in Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ z ^ 3 / 3 := by
  have hle : ∀ x ∈ Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < ((1 + x) ^ 2) ^ 2)]
    have h2 : (1:ℝ) ≤ (1 + x) ^ 4 := by
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x))]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioc 0 z) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (z ^ 2) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (continuousOn_id.pow 2).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg x)]
      exact pow_le_pow_left₀ hx.1.le hx.2 2
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hle)
  refine h.trans ?_
  rw [← intervalIntegral.integral_of_le hz, integral_pow]
  norm_num

/-- `∫_{x>z} (x/(1+x)²)² ≤ 1/z` for `z > 0`. -/
private theorem u_sq_Ioi_le {z : ℝ} (hz : 0 < z) :
    ∫ x in Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ 1 / z := by
  have hle : ∀ x ∈ Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ (-(2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [div_pow, Real.rpow_neg hx0.le, Real.rpow_two, inv_eq_one_div,
      le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(2 : ℝ))) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hz
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle)
  refine h.trans ?_
  rw [integral_Ioi_rpow_of_lt (by norm_num) hz,
    show ((-2:ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

-- (proof to be filled in)
theorem L12_sq_le_growth (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3)
    ∧ (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 / z) := by
  have hEE : Work.Construction.L12 g = Work.Elliptic.L12 g :=
    Work.FTS.H2.constructionL12_eq_ellipticL12 g
  have hintL : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.FTS.H2.L12densIntegrable α g hα hα1 hsm hmem
  have h0' : Work.Elliptic.L12 g 0 = 0 := by rw [← hEE]; exact h0
  obtain ⟨hval, -, -⟩ := Work.Elliptic.L12_values g hintL h0'
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hXdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  set B : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hBdef
  set u : ℝ → ℝ := fun s => s / (1 + s) ^ 2 with hudef
  have hBnn : ∀ s, 0 ≤ B s := fun s => MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hu0 : ∀ s, 0 < s → 0 ≤ u s := by
    intro s hs; rw [hudef]; positivity
  have hBint : MeasureTheory.IntegrableOn B Work.Spaces.Iz := hmem.2
  -- (1) the density bound
  have hdens : ∀ s : ℝ, 0 < s → (Work.Elliptic.L12dens g s) ^ 2 ≤ K1 * B s * (u s) ^ 2 := by
    intro s hs
    have hb := L12_iterate_sq_slot_le α hα hα1 hsm hmem h0 (b := 1) le_rfl (by norm_num) hs
    have hQ : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 g z) s
        = - Work.Elliptic.Qang g 0 s :=
      (L12_dzdIter_moment α hα hα1 hsm hmem h0).1 0 (by norm_num) s hs
    rw [hQ, neg_sq] at hb
    rw [Work.Elliptic.L12dens_eq_Qang_div g s, div_pow, div_le_iff₀ (pow_pos hs 2)]
    refine hb.trans (le_of_eq ?_)
    rw [hK1def, hBdef, hudef]
    field_simp
  -- (2) the pointwise bound on the density
  have hdens' : ∀ s : ℝ, 0 < s → |Work.Elliptic.L12dens g s|
      ≤ Real.sqrt K1 * (Real.sqrt (B s) * u s) := by
    intro s hs
    have hKb : 0 ≤ K1 * B s := mul_nonneg hK1nn (hBnn s)
    have h := Real.sqrt_le_sqrt (hdens s hs)
    rw [Real.sqrt_mul hKb] at h
    rw [Real.sqrt_sq_eq_abs] at h
    rw [Real.sqrt_mul hK1nn] at h
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hu0 s hs)] at h
    simpa only [mul_assoc] using h
  -- (3) measurability and integrability of the auxiliary functions
  have hu_cont : ContinuousOn u (Set.Ioi (0:ℝ)) := by
    rw [hudef]
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have : (0:ℝ) < 1 + x := by linarith
    positivity
  have hu_aesm : ∀ {s : Set ℝ}, s ⊆ Set.Ioi (0:ℝ) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) := by
    intro s hs
    exact (hu_cont.aestronglyMeasurable measurableSet_Ioi).mono_measure
      (MeasureTheory.Measure.restrict_mono hs le_rfl)
  have hu_int_Ioc : ∀ z : ℝ, MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc 0 z) := by
    intro z
    refine MeasureTheory.IntegrableOn.of_bound ?_
      ((hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1)).pow 2) 1 ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow,
        div_le_one (by
          have h2 : (1:ℝ) ≤ (1 + x) ^ 2 := by nlinarith [hx0.le]
          exact pow_pos (lt_of_lt_of_le one_pos h2) 2)]
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)),
        sq_nonneg (1 + x * x + x)]
  have hu_int_Ioi : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioi z) := by
    intro z hz
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hz)
      ((hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx)).pow 2) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow, Real.rpow_neg hx0.le,
      Real.rpow_two, inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2),
      div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  -- (4) integrability of `sqrt B * u`
  have hsqu : ∀ {s : Set ℝ}, MeasureTheory.IntegrableOn B s →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s →
      MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) →
      MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) s := by
    intro s hBi hui hBa hua
    refine MeasureTheory.Integrable.mono' ((hBi.add hui).const_mul (1/2))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hBa).mul hua) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (B x))]
    show Real.sqrt (B x) * |u x| ≤ 1 / 2 * (B x + (u x) ^ 2)
    nlinarith [sq_nonneg (Real.sqrt (B x) - |u x|), Real.sq_sqrt (hBnn x), sq_abs (u x)]
  have hHk : Work.Spaces.HkSq α 4 g = X ^ 2 := by
    have h0H : (0:ℝ) ≤ Work.Spaces.HkSq α 4 g :=
      MeasureTheory.integral_nonneg fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    rw [hXdef, show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl]
    exact (Real.sq_sqrt h0H).symm
  refine ⟨?_, ?_⟩
  · intro z hz
    have hB_ioc : MeasureTheory.IntegrableOn B (Set.Ioc 0 z) :=
      hBint.mono_set (fun s hs => hs.1.le)
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioc 0 z) :=
      hsqu hB_ioc (hu_int_Ioc z) hB_ioc.aestronglyMeasurable
        (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hcs := cs_sqrt_mul hBnn hB_ioc hB_ioc.aestronglyMeasurable (hu_int_Ioc z)
      (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hBle : (∫ s in Set.Ioc 0 z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioc 0 z) => hs.1.le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 * z ^ 3 := by
      refine hcs.trans ?_
      have hule := u_sq_Ioc_le hz.le
      have h1 : (∫ s in Set.Ioc 0 z, B s) * (∫ s in Set.Ioc 0 z, (u s) ^ 2)
          ≤ X ^ 2 * (z ^ 3 / 3) :=
        mul_le_mul hBle hule (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
      have h2 : X ^ 2 * (z ^ 3 / 3) ≤ X ^ 2 * z ^ 3 := by
        have : (0:ℝ) ≤ z ^ 3 / 3 := by positivity
        nlinarith [sq_nonneg X]
      linarith
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in (0)..z, Work.Elliptic.L12dens g s| := by
        rw [hval z hz.le]; simp
      rw [habs]
      refine (intervalIntegral.abs_integral_le_integral_abs hz.le).trans ?_
      rw [intervalIntegral.integral_of_le hz.le]
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
        (fun s hs => hdens' s hs.1)
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 * z ^ 3) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 * z ^ 3) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 * z ^ 3 := by positivity
    simpa [mul_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz
  · intro z hz
    have hB_ioi : MeasureTheory.IntegrableOn B (Set.Ioi z) :=
      hBint.mono_set (fun s hs => (lt_trans hz hs).le)
    have huioi := hu_int_Ioi z hz
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioi z) :=
      hsqu hB_ioi huioi hB_ioi.aestronglyMeasurable
        (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hcs := cs_sqrt_mul hBnn hB_ioi hB_ioi.aestronglyMeasurable huioi
      (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hBle : (∫ s in Set.Ioi z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioi z) => (lt_trans hz hs).le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 / z := by
      refine hcs.trans ?_
      have hule := u_sq_Ioi_le hz
      have h1 : (∫ s in Set.Ioi z, B s) * (∫ s in Set.Ioi z, (u s) ^ 2)
          ≤ X ^ 2 / z := by
        have h2 := mul_le_mul hBle hule
          (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
        simpa only [hudef, mul_one_div] using h2
      exact h1
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in Set.Ioi z, Work.Elliptic.L12dens g s| := by
        rw [show Work.Elliptic.L12 g z = ∫ s in Set.Ioi z, Work.Elliptic.L12dens g s from rfl]
      rw [habs]
      refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => hdens' s (lt_trans hz hs))
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 / z) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 / z) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 / z := by positivity
    simpa [mul_div_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz

/-! ## The seven rows, one at a time

Each row is proved with its own constant; the final theorem takes the maximum.  Rows 1, 4, 6, 7
are direct consequences of the interface (`N4Norm.l12H`, the transport clauses `t1`–`t3`), while
rows 2, 3, 5 use the `L₁₂`-bounds established above. -/




/-! ## Separation of an angular profile and a radial function

`(a(θ)·r(z))`'s `ℋ⁴`-slots factor into an angular bound and a radial slot, because `D_z` sees
only the radial part (`D_z^i(a·r) = a·D_z^ir`) and `D_θ` only the angular one
(`D_z^jD_θ^i(a·r) = (D_θ^ia)(θ)·(D_z^jr)(z)`). -/

/-- The `θ`-iterates do not see a factor of `z` alone (constant on the left). -/
private theorem dthIter_rad_mul_ang (a : ℝ → ℝ) (r : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => r z * a θ)
      = fun z θ => r z * (Work.Spaces.dthU^[i]) a θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Function.iterate_succ_apply']
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => r z * (Work.Spaces.dthU^[i]) a θ') θ
        = r z * (Real.sin (2 * θ) * deriv ((Work.Spaces.dthU^[i]) a) θ)
      rw [RowsN0Aux.deriv_const_mul']
      ring

/-- The `θ`-iterates do not see the radial factor. -/
theorem dthIter_ang_mul_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => a θ * r z)
      = fun z θ => (Work.Spaces.dthU^[i]) a θ * r z := by
  have hswap : (fun z θ => a θ * r z) = fun z θ => r z * a θ := by
    funext z θ; ring
  rw [hswap, dthIter_rad_mul_ang a r i]
  funext z θ
  ring

/-- `D_z` of a product of a `θ`-only and a `z`-only function. -/
theorem dzIter_ang_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => a θ * r z) z θ = a θ * Work.Elliptic.DzdIter j r z := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Elliptic.DzdIter_succ]
      show z * deriv (fun z' => Work.Spaces.DzIter j (fun z θ => a θ * r z) z' θ) z
        = a θ * (z * deriv (Work.Elliptic.DzdIter j r) z)
      rw [show (fun z' => Work.Spaces.DzIter j (fun z θ => a θ * r z) z' θ)
          = (fun z' => a θ * Work.Elliptic.DzdIter j r z') from funext fun z' => ih z',
        RowsN0Aux.deriv_const_mul']
      ring

/-- The mixed iterates of an angular `×` radial product. -/
theorem mixed_ang_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
      = Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ * Work.Elliptic.DzdIter j r z := by
  rw [Work.Spaces.mixed, dthIter_ang_mul_rad a r i]
  rw [dzIter_ang_rad (fun θ' => (Work.Spaces.dthU^[i]) a θ') r j z θ,
    Work.FTS.LocData.DthIter_rad_eq i a 0 θ]


/-! ## The angular profiles carried by rows 3, 5 and 6

With `Γ = Spaces.Gam α` and `q = Spaces.qfun = cos 2θ - 1/3` one has `c2m = (3/2)q` and,
crucially, `D_θΓ = α·q·Γ`; hence every profile occurring in `N₀₄ᵃ`, `N₀₅ᵃ` and `N₀₅ᵇ` is a
multiple of `Γ·q` (respectively of `q`), and its `D_θ`-iterates are controlled by the
`Spaces.Tfun`-sequence. -/

/-- `c2m = (3/2)·qfun`. -/
theorem c2m_eq_three_halves_qfun (θ : ℝ) :
    Work.Construction.c2m θ = (3 / 2) * Work.Spaces.qfun θ := by
  rw [Work.Construction.c2m, Work.Spaces.qfun, Real.sin_sq, Real.cos_two_mul]
  ring

/-- **The `D_θ`-iterates of `Γ·q`**: on `(0,π/2)`, `D_θ^i(Γq) = Γ·Tfun i α`. -/
theorem dthU_iter_Gam_mul_qfun (i : ℕ) (α : ℝ) (hα : 0 < α) :
    Set.EqOn (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t))
      (fun θ => Work.Spaces.Gam α θ * Work.Spaces.Tfun i α θ) (Set.Ioo 0 (π/2)) := by
  induction i with
  | zero =>
      intro θ _
      rw [Function.iterate_zero_apply]
      show Work.Spaces.Gam α θ * Work.Spaces.qfun θ
        = Work.Spaces.Gam α θ * Work.Spaces.Tfun 0 α θ
      rw [Work.Spaces.Tfun_zero]
  | succ i ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hmem : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hev := ih.eventuallyEq_of_mem hmem
      have hderiv := hev.deriv_eq
      have hstep : Work.Spaces.dthU
            (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ
          = Work.Spaces.dthU
            (fun θ => Work.Spaces.Gam α θ * Work.Spaces.Tfun i α θ) θ := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hderiv]
      rw [hstep]
      show Work.Spaces.dthU (fun θ => Work.Spaces.Gam α θ * Work.Spaces.Tfun i α θ) θ
        = Work.Spaces.Gam α θ * Work.Spaces.Tfun (i + 1) α θ
      have hG : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      have hT : DifferentiableAt ℝ (Work.Spaces.Tfun i α) θ :=
        ((Work.Spaces.Tfun_smooth i α).differentiable (by simp)).differentiableAt
      rw [show (fun θ => Work.Spaces.Gam α θ * Work.Spaces.Tfun i α θ)
            = (fun t => Work.Spaces.Gam α t) * (Work.Spaces.Tfun i α) from rfl,
        Work.Spaces.dthU_mul_apply _ _ θ hG hT,
        show Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
            = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ from
          Work.Spaces.dthU_Gam α θ hα hθ,
        Work.Spaces.Tfun_succ]
      simp only [Work.Spaces.dthU_apply]
      ring





/-! ## The `(z∂_z)`-iterates of the profile `F_*`

The radial factors of rows 3 and 5 are `F_*(z) = 2z/(1+z)²` and `z∂_zF_*(z)`; both are
bounded together with their `D_z`-iterates, with a universal constant. -/

theorem smoothOrder_Fstar :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z)
      (Set.Ioi (-1 : ℝ)) := by fun_prop
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2)
      (Set.Ioi (-1 : ℝ)) := by fun_prop
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < 1 + z := by simp only [Set.mem_Ioi] at hz; linarith
    positivity
  have hinv : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => ((1 + z) ^ 2)⁻¹)
      (Set.Ioi (-1 : ℝ)) := hden.inv hne
  have h := hnum.mul hinv
  simpa only [Work.FM.Fstar, div_eq_mul_inv] using h

theorem deriv_iter_Fstar (m : ℕ) :
    deriv^[m] Work.FM.Fstar = fun z => 2 * deriv^[m] (fun z => z / (1 + z) ^ 2) z := by
  have hF : Work.FM.Fstar = fun z => 2 * (z / (1 + z) ^ 2) := by
    funext w
    rw [Work.FM.Fstar]
    ring
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      exact hF
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext w
      rw [RowsN0Aux.deriv_const_mul']

/-- **`|(z∂_z)^k F_*(z)| ≤ 200000` for `k ≤ 5`, `z ≥ 0`.** -/
theorem dzdIter_Fstar_bound (k : ℕ) (hk : k ≤ 5) :
    ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter k Work.FM.Fstar z| ≤ 200000 := by
  intro z hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hexp := Work.FTS.H2.Q.DzIter_eq_sum_scoef_sm
    (h := fun z' (_ : ℝ) => Work.FM.Fstar z') (θ := 0) smoothOrder_Fstar k z hz1
  set x : ℕ → ℝ := fun j =>
    z ^ j * Work.Spaces.pzIter j (fun z' (_ : ℝ) => Work.FM.Fstar z') z 0 with hxdef
  have hpz : ∀ j ≤ k, |x j| ≤ 1440 := by
    intro j hj
    have hj5 : j ≤ 5 := le_trans hj hk
    have hjfact : (j.factorial : ℝ) * ((j : ℝ) + 1) ≤ 720 := by
      interval_cases j <;> norm_num
    simp only [hxdef]
    have h1 : Work.Spaces.pzIter j (fun z' (_ : ℝ) => Work.FM.Fstar z') z 0
        = 2 * deriv^[j] (fun z => z / (1 + z) ^ 2) z := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv, iteratedDeriv_eq_iterate]
      exact congrFun (deriv_iter_Fstar j) z
    have hz0 : (0 : ℝ) < 1 + z := by linarith
    have hratio : |z / (1 + z)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one hz0]
      linarith
    have hratioj : |(z / (1 + z)) ^ j| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (by positivity) j)]
      exact pow_le_one₀ (by positivity) (le_of_abs_le hratio)
    have hker : |(1 + z) ^ j * deriv^[j] (fun z => z / (1 + z) ^ 2) z|
        ≤ (j.factorial : ℝ) * ((j : ℝ) + 1) := by
      have h := Work.Spaces.pzIter_hKer_bound j z hz
      rw [show z + 1 = (1 + z : ℝ) from by ring] at h
      exact h
    have hsplit : z ^ j * (2 * deriv^[j] (fun z => z / (1 + z) ^ 2) z)
        = 2 * ((z / (1 + z)) ^ j * ((1 + z) ^ j * deriv^[j] (fun z => z / (1 + z) ^ 2) z)) := by
      have hne : ((1 : ℝ) + z) ≠ 0 := by positivity
      have hc : z ^ j = (z / (1 + z)) ^ j * (1 + z) ^ j := by
        rw [div_pow, div_mul_cancel₀]
        exact pow_ne_zero j hne
      rw [hc]
      ring
    rw [h1, hsplit, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul]
    have hstep : |(z / (1 + z)) ^ j| * |(1 + z) ^ j * deriv^[j] (fun z => z / (1 + z) ^ 2) z|
        ≤ 1 * 720 :=
      mul_le_mul hratioj (le_trans hker hjfact) (abs_nonneg _) (by norm_num)
    calc 2 * (|(z / (1 + z)) ^ j| * |(1 + z) ^ j * deriv^[j] (fun z => z / (1 + z) ^ 2) z|)
        ≤ 2 * (1 * 720) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 1440 := by norm_num
  have hsum := Work.Spaces.abs_sum_scoef_mul_le k 1440 x (fun j hj => hpz j hj)
  have hbell : (Work.Spaces.bell k : ℝ) ≤ 100 := by
    have hb : Work.Spaces.bell k ≤ 100 := by
      interval_cases k <;> decide
    exact_mod_cast hb
  have hexp2 : Work.Elliptic.DzdIter k Work.FM.Fstar z
      = ∑ j ∈ Finset.range (k + 1), (Work.Spaces.scoef k j : ℝ) * x j := by
    simp only [hxdef]
    rw [← Work.Elliptic.DzIter_rad Work.FM.Fstar k z 0]
    exact hexp
  rw [hexp2]
  calc |∑ j ∈ Finset.range (k + 1), (Work.Spaces.scoef k j : ℝ) * x j|
      ≤ (Work.Spaces.bell k : ℝ) * 1440 := hsum
    _ ≤ 100 * 1440 := mul_le_mul_of_nonneg_right hbell (by norm_num)
    _ ≤ 200000 := by norm_num

/-! ## Row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³`

`N₀₅ᵇ = -c2m(θ)·L₁₂(g)(z)·D_zg`, i.e. `f·D_zg` with `f = -c2m·L₁₂(g)`; the transport clause
`N4Extra.t2` gives `Ct α^{-1/2}·|f|_{ℋ⁴}·X²` and `|f|_{ℋ⁴} ≤ C|L₁₂(g)|_{ℋ⁴} ≤ C·Ci·X` by the
angular `×` radial separation (`Xn_ang_rad_le`) applied to the profile `c2m`. -/

/-! ## Row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³`

`N₀₅ᵇ = -c2m(θ)·L₁₂(g)(z)·D_zg`, i.e. `f·D_zg` with `f = -c2m·L₁₂(g)`; the transport clause
`N4Extra.t2` gives `Ct α^{-1/2}·|f|_{ℋ⁴}·X²` and `|f|_{ℋ⁴} ≤ C|L₁₂(g)|_{ℋ⁴} ≤ C·Ci·X` by the
angular `×` radial separation (`Xn_ang_rad_le`) applied to the profile `c2m`. -/

/-! ## Row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³`

`N₀₅ᵇ = -c2m(θ)·L₁₂(g)(z)·D_zg`, i.e. `f·D_zg` with `f = -c2m·L₁₂(g)`; the transport clause
`N4Extra.t2` gives `Ct α^{-1/2}·|f|_{ℋ⁴}·X²` and `|f|_{ℋ⁴} ≤ C|L₁₂(g)|_{ℋ⁴} ≤ C·Ci·X` by the
angular `×` radial separation (`Xn_ang_rad_le`) applied to the profile `c2m`. -/

/-- `sin(2θ)^p` is integrable on `Iθ` for `p ≥ 0`. -/
theorem sin_two_rpow_integrableOn {p : ℝ} (hp : 0 ≤ p) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  have hne : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono'
    (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) hne) ?_ ?_
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p)
      |>.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
    exact Real.rpow_le_one h0 (Real.sin_le_one _) hp

/-- `∫_θ sin(2θ)^p ≤ π/2` for `p ≥ 0`. -/
theorem integral_sin_two_rpow_le {p : ℝ} (hp : 0 ≤ p) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ Real.pi / 2 := by
  have hne : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) hne
  have h2 : (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun _ : ℝ => (1 : ℝ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact Real.rpow_le_one h0 (Real.sin_le_one _) hp
  have := MeasureTheory.integral_mono_ae (sin_two_rpow_integrableOn hp) h1 h2
  rwa [Work.FTS.Nonlinear.RadialProd.integral_one_Iθ] at this

/-- `|c2m(θ)| ≤ 2` on `Iθ`. -/
theorem abs_c2m_le_two {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.c2m θ| ≤ 2 := by
  rw [c2m_eq_three_halves_qfun, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
    rw [Work.Spaces.qfun, abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
  calc (3 / 2) * |Work.Spaces.qfun θ| ≤ (3 / 2) * (4 / 3) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 2 := by norm_num

/-- The `D_θ`-iterates of `c2m` are bounded by `1000·sin(2θ)²`. -/
theorem DthIter_c2m_le (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) (θ : ℝ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * (Real.sin (2 * θ)) ^ (2 : ℝ) := by
  have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound i hi hi4 θ
  rw [Work.FTS.LocData.DthIter_rad_eq i Work.Construction.c2m 0 θ]
  rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
    Real.rpow_natCast _ 2]
  exact h


/-! ## Row 2: `|(1/α)L₁₂(g)·g|_{ℋ⁴} ≤ Cα^{-1}X²`

The radial factor `r = L₁₂(g)` is not `C^∞` at `z = 0`, so neither `radial_prod` nor the
interface field `radialMul` applies; instead the pointwise Leibniz rule `radial_leibniz` is used
slot by slot, with the two input bounds on the iterates of `L₁₂(g)`:
`(D_z^bL₁₂(g))² ≤ KX²` for `1 ≤ b ≤ 4` (the angular-moment bound `Qang_sq_le_const`, since
`D_z^{b}L₁₂(g) = -Q_{b-1}(g)`) and `(L₁₂(g))² ≤ KX²` for the `b = 0` slot (the growth estimates
`L12_sq_le_growth`, whose two constants combine because `min(z³,1/z) ≤ 1`). -/

/-- Cauchy–Schwarz for a binomial slot sum: `(∑ c_b(x_by_b))² ≤ 256·card·Kc·∑ y_b²` when the
coefficients `c_b` are bounded by `16` and the first factors satisfy `x_b² ≤ Kc`. -/
private theorem slot_sum_sq_le {ι : Type*} (s : Finset ι) (c x y : ι → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hc : ∀ b ∈ s, |c b| ≤ 16) (hx : ∀ b ∈ s, (x b) ^ 2 ≤ Kc) :
    (∑ b ∈ s, c b * (x b * y b)) ^ 2 ≤ 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by
  have h1 : (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 :=
    _root_.sq_sum_le_card_mul_sum_sq
  have h2 : ∑ b ∈ s, (c b * (x b * y b)) ^ 2 ≤ ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc2 : (c b) ^ 2 ≤ 256 := by
      have h := hc b hb
      nlinarith [sq_nonneg (c b), sq_abs (c b), abs_nonneg (c b)]
    have hx2 := hx b hb
    have hy2 : 0 ≤ (y b) ^ 2 := sq_nonneg _
    have hxy : (x b) ^ 2 * (y b) ^ 2 ≤ Kc * (y b) ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 hy2
    have hcx : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * (Kc * (y b) ^ 2) := by
      have h1 : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) :=
        mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      calc (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) := h1
        _ ≤ 256 * (Kc * (y b) ^ 2) := mul_le_mul_of_nonneg_left hxy (by norm_num)
    calc (c b * (x b * y b)) ^ 2 = (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) := by ring
      _ ≤ 256 * (Kc * (y b) ^ 2) := hcx
  have h3 : ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) = 256 * Kc * ∑ b ∈ s, (y b) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 := h1
    _ ≤ (s.card : ℝ) * (256 * Kc * ∑ b ∈ s, (y b) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (Nat.cast_nonneg _)
    _ = 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by ring


/-! ## Radial multipliers and rows 3, 5

Rows 3 and 5 carry the explicit `F_*`-factors: writing `Γ = Spaces.Gam α`, `q = Spaces.qfun`
(so that `D_θΓ = αqΓ` and `c2m = (3/2)q`) one has, on the open quadrant,

* `N₀₄ᵃ = (3α/(2c))·qΓ·(F_*·L₁₂(g))`,
* `N₀₅ᵃ = -(3α/(2c))·qΓ·(D_zF_*·L₁₂(g))`,

so both rows are products of the *same* angular profile `(3α/(2c))qΓ` (bounded by `2α/c`, with
`D_θ`-iterates bounded by `(3α/(2c))·GamQBound·sin(2θ)^{α/5}`) and a *radial* factor
`φ·L₁₂(g)` with `φ` smooth and of bounded `D_z`-iterates (`Rint_mul_le` + `Xn_rad_mul_le`). -/

/-- `F_*` is smooth on the open quadrant (as a function of `z` alone). -/
theorem smoothQuad_Fstar : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => Work.FM.Fstar z) := by
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => p.1)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) (Set.Ioi (-1)) := fun p hp => hp.1
  have h := ContDiffOn.comp smoothOrder_Fstar contDiff_fst.contDiffOn hmaps
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z (_ : ℝ) => Work.FM.Fstar z))
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    h.congr (fun p _ => rfl)
  exact h2

/-- `D_z^k F_*` is differentiable on `(0,∞)`. -/
theorem differentiableAt_dzdIter_Fstar (b : ℕ) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter b Work.FM.Fstar) z :=
  (((Work.FTS.Nonlinear.RadialProd.contDiffOn_DzdIter Work.FM.Fstar smoothQuad_Fstar b).contDiffAt
    (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)))).differentiableAt (by simp)

/-- The radial multiplier bound: `Rint (φ·r) ≤ 6400M²·Rint r` for `|D_z^kφ| ≤ M`. -/
theorem Rint_mul_le (φ r : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ k ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter k φ z| ≤ M)
    (hφdiff : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b φ) z)
    (hrdiff : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b r) z)
    {z : ℝ} (hz : 0 < z) :
    Work.FTS.Nonlinear.RadialProd.Rint (fun z => φ z * r z) z
      ≤ 6400 * M ^ 2 * Work.FTS.Nonlinear.RadialProd.Rint r z := by
  have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hterm : ∀ i ≤ 4, (Work.Elliptic.DzdIter i (fun z => φ z * r z) z) ^ 2
      ≤ 1280 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by
    intro i hi
    have hleib := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz i φ r
      (fun b hb z' hz' => hφdiff b (by omega) z' hz')
      (fun b hb z' hz' => hrdiff b (by omega) z' hz') z hz
    rw [hleib]
    have hCS := slot_sum_sq_le (Finset.range (i + 1)) (fun b => (i.choose b : ℝ))
      (fun b => Work.Elliptic.DzdIter b φ z)
      (fun b => Work.Elliptic.DzdIter (i - b) r z)
      (Kc := M ^ 2) (by positivity)
      (fun b hb => by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (le_trans
          (by have := Finset.mem_range.mp hb; omega) hi))
      (fun b hb => by
        have h := hφ b (by have := Finset.mem_range.mp hb; omega) z hz
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        rwa [sq_abs] at h2)
    refine hCS.trans ?_
    have hsub : ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2
        ≤ ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by
      have hreflect : (∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2)
          = ∑ k ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter k r z) ^ 2 := by
        rw [← Finset.sum_range_reflect (fun k => (Work.Elliptic.DzdIter k r z) ^ 2) (i + 1)]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [show i + 1 - 1 - b = i - b from by
          have := Finset.mem_range.mp hb; omega]
      rw [hreflect]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => Finset.mem_range.mpr (by have := Finset.mem_range.mp hb; omega))
        (fun b _ _ => sq_nonneg _)
    have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
      rw [Finset.card_range]
      exact_mod_cast (by omega : i + 1 ≤ 5)
    have hstep : 256 * ((Finset.range (i + 1)).card : ℝ) * M ^ 2
          * ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2
        ≤ 256 * 5 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by
      have hS0 : 0 ≤ ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2 :=
        Finset.sum_nonneg fun b _ => sq_nonneg _
      have hA : 256 * ((Finset.range (i + 1)).card : ℝ) ≤ 256 * 5 :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      have hB : (M ^ 2) * ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2
          ≤ (M ^ 2) * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (sq_nonneg M)
      have h1 := mul_le_mul hA hB (mul_nonneg (sq_nonneg M) hS0) (by norm_num : (0:ℝ) ≤ 256 * 5)
      have h2 : (256 * ((Finset.range (i + 1)).card : ℝ))
            * ((M ^ 2) * ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2)
          = 256 * ((Finset.range (i + 1)).card : ℝ) * M ^ 2
            * ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2 := by ring
      have h3 : (256 * 5) * ((M ^ 2) * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2)
          = 256 * 5 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by ring
      rw [h2, h3] at h1
      exact h1
    calc 256 * ((Finset.range (i + 1)).card : ℝ) * M ^ 2
          * ∑ b ∈ Finset.range (i + 1), (Work.Elliptic.DzdIter (i - b) r z) ^ 2
        ≤ 256 * 5 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := hstep
      _ = 1280 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by ring
  rw [Work.FTS.Nonlinear.RadialProd.Rint, Work.FTS.Nonlinear.RadialProd.Rint]
  have hsum : ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i (fun z => φ z * r z) z) ^ 2
      ≤ ∑ _i ∈ Finset.range 5, 1280 * M ^ 2
        * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 :=
    Finset.sum_le_sum fun i hi => hterm i (by have := Finset.mem_range.mp hi; omega)
  have hsum' : ∑ _i ∈ Finset.range 5, 1280 * M ^ 2
        * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2
      = 6400 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  calc ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i (fun z => φ z * r z) z) ^ 2
        * (Work.Spaces.w z) ^ 2
      = (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i (fun z => φ z * r z) z) ^ 2)
        * (Work.Spaces.w z) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (6400 * M ^ 2 * ∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2)
        * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_right (hsum.trans (le_of_eq hsum')) hw
    _ = 6400 * M ^ 2 * (∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2
        * (Work.Spaces.w z) ^ 2) := by
        rw [show (6400 * M ^ 2 * (∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2))
              * (Work.Spaces.w z) ^ 2
            = (6400 * M ^ 2) * ((∑ k ∈ Finset.range 5, (Work.Elliptic.DzdIter k r z) ^ 2)
                * (Work.Spaces.w z) ^ 2) from by ring,
          Finset.sum_mul]


open Work.FTS.Nonlinear.RadialProd in
theorem HkIntegrand_ang_rad_sin_le (α : ℝ) (a : ℝ → ℝ) (r : ℝ → ℝ) {B0 B1 κ : ℝ}
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ B1 * (Real.sin (2 * θ)) ^ κ)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Rint r z * (B0 ^ 2 * smE θ
          + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  obtain ⟨hain, hain'⟩ := abs_le.mp (ha0 θ hθI)
  -- the pure slots
  have hpure : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (a θ) ^ 2 * smE θ * Rint r z := by
    have hterm : ∀ i : ℕ, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (a θ) ^ 2 * smE θ
          * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i
      rw [dzIter_ang_rad,
        show (a θ * Work.Elliptic.DzdIter i r z
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((a θ * Work.Elliptic.DzdIter i r z)
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          from by ring,
        light_sq _ z θ hsin]
      ring
    calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range 5, (a θ) ^ 2 * smE θ
            * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (a θ) ^ 2 * smE θ * Rint r z := by
          rw [← Finset.mul_sum, Rint]
  -- the mixed slots
  have hmix : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
    have hterm2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
          * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ 4
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                  * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2 from by ring,
            heavy_sq α _ z θ hsin]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (smG_nonneg hθI))
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
              * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
          rw [← Finset.sum_mul_sum, Rint]
          ring
  -- the comparison of the two profiles
  have hMsum : (∑ i ∈ Finset.range 5, if 1 ≤ i then
        (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
      ≤ ∑ i ∈ Finset.range 5, if 1 ≤ i then
          B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) else 0 := by
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1]
      have hi4 : i ≤ 4 := by
        have := Finset.mem_range.mp hi
        omega
      have hb := ha1 i h1 hi4 θ hθI
      have h3 : (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2
          ≤ B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ) := by
        have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs] at h4
        rw [mul_pow, pow_two ((Real.sin (2 * θ)) ^ κ), ← Real.rpow_add hsin,
          show κ + κ = 2 * κ by ring] at h4
        exact h4
      calc (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ
          ≤ B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ) * smG α θ :=
            mul_le_mul_of_nonneg_right h3 (smG_nonneg hθI)
        _ = B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
            rw [show B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ) * smG α θ
                = B1 ^ 2 * ((Real.sin (2 * θ)) ^ (2 * κ) * smG α θ) from by ring,
              smG, ← Real.rpow_add hsin,
              show 2 * κ + -(Work.Spaces.gam α)
                = 2 * κ - Work.Spaces.gam α by ring]
    · rw [if_neg h1, if_neg h1]
  have hMs : (∑ i ∈ Finset.range 5, if 1 ≤ i then
        B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) else 0)
      = 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
    rw [← Finset.sum_filter]
    rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
      Finset.sum_const, Nat.card_Icc]
    norm_num
    ring
  have hM : (a θ) ^ 2 * smE θ + (∑ i ∈ Finset.range 5, if 1 ≤ i then
        (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
      ≤ B0 ^ 2 * smE θ
        + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) := by
    refine add_le_add ?_ ?_
    · have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (abs_le.mpr ⟨hain, hain'⟩) 2
        rwa [sq_abs] at h3
      exact mul_le_mul_of_nonneg_right h2 (smE_nonneg hθI)
    · exact hMsum.trans (le_of_eq hMs)
  calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
          rw [Work.Spaces.HkIntegrand]
    _ ≤ (a θ) ^ 2 * smE θ * Rint r z
          + Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) :=
        add_le_add (le_of_eq hpure) hmix
    _ = Rint r z * ((a θ) ^ 2 * smE θ
          + (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)) := by
        ring
    _ ≤ Rint r z * (B0 ^ 2 * smE θ
          + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left hM (Rint_nonneg r z)

open Work.FTS.Nonlinear.RadialProd in
/-- **From a pointwise bound on the `ℋ⁴`-integrand to the `HkSq`-bound**, with a general
dominating radial density `Rint r` and an arbitrary multiplicative constant `C`. -/
theorem HkSq_ang_rad_of_le (α : ℝ) (hα : 0 < α) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (r : ℝ → ℝ)
    {B0 B1 κ M1 C : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hM1 : 0 ≤ M1) (hC : 0 ≤ C)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ
        ≤ C * Rint r z * (B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)))
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) Work.Spaces.Iθ)
    (hm1 : ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α) ≤ M1)
    (hRintint : MeasureTheory.IntegrableOn (Rint r) Work.Spaces.Iz) :
    Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
      ≤ C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * ∫ z in Work.Spaces.Iz, Rint r z := by
  have hexp1 : -1 < -(Work.Spaces.eta) := by
    have := Work.Spaces.eta_lt_one; linarith
  have hle0 : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have hIf : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ) Work.Spaces.Iθ := by
    change MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ
    exact (Work.Spaces.sin_two_rpow _ hexp1 hle0).1.const_mul _
  have hIg : MeasureTheory.IntegrableOn (fun θ : ℝ => 4 * B1 ^ 2
      * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    hI1.const_mul _
  have hIntA : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ
      + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
      Work.Spaces.Iθ := hIf.add hIg
  have hA : (∫ θ in Work.Spaces.Iθ, smE θ) ≤ 10000 := by
    change (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hexp1 hle0).2
    have h1 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [h1] at h
    norm_num at h
    exact h
  have hboundA : (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
        + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α))
      ≤ B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1 := by
    rw [MeasureTheory.integral_add hIf hIg, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg B0)
    have h2 := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 4 * B1 ^ 2)
    linarith
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
        ≤ C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * Rint r z := by
    intro z hzmem
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (C * Rint r z) * (B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
            (hIntA.const_mul _) ?_
          filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
          exact (hpt z hzmem θ hθ).trans (le_of_eq (by ring))
      _ = (C * Rint r z) * (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (Real.sin (2 * θ)) ^ (2 * κ - Work.Spaces.gam α)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (C * Rint r z) * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) :=
          mul_le_mul_of_nonneg_left hboundA (mul_nonneg hC (Rint_nonneg r z))
      _ = C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * Rint r z := by ring
  have houter : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
      ≤ C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * ∫ z in Work.Spaces.Iz, Rint r z := by
    rw [Work.Spaces.HkSq]
    have hEq : (∫ z in Work.Spaces.Iz, C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Rint r z)
        = C * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * ∫ z in Work.Spaces.Iz, Rint r z := by
      rw [MeasureTheory.integral_const_mul]
    rw [← hEq]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      (hRintint.const_mul _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => hinner z (by simpa [Work.Spaces.Iz] using hz)))
  exact houter


/-! ## Rows 3 and 5 -/

/-! ## Rows 3 and 5 -/

/-- The iterate of `z ∂_z` is additive in the exponent. -/
theorem DzdIter_add (a b : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter a (Work.Elliptic.DzdIter b u)
      = Work.Elliptic.DzdIter (a + b) u := by
  induction a with
  | zero => rw [Work.Elliptic.DzdIter_zero, Nat.zero_add]
  | succ a ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, ← Work.Elliptic.DzdIter_succ]
      rw [show a + b + 1 = a + 1 + b from by omega]

/-! ### The shared angular profile of rows 3 and 5 -/





/-! ## Rows 3 and 5 -/


end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

/-- **The multiplier bound on the open quadrant.** -/
theorem zmul_open (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hφ : ∀ n : ℕ, ContDiffOn ℝ n φ (Set.Ioi 0) := fun n =>
    (contDiffOn_nat_of_smoothOrder n hsm).mono (fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)
  have hgz : ∀ n : ℕ, ContDiffOn ℝ n (fun z' => g z' θ) (Set.Ioi 0) := fun n =>
    Work.FTS.FinalClock.contDiffOn_zslice (hg.forall n) hθ
  have hgij : ∀ n i : ℕ,
      ContDiffOn ℝ n (fun z' => Work.Spaces.DthIter i g z' θ) (Set.Ioi 0) := fun n i =>
    Work.FTS.FinalClock.contDiffOn_zslice ((hg.DthIter i).forall n) hθ
  refine zmul_pt α k φ g hK (fun b hb => hB b hb z hz) ?_ ?_
  · intro i _
    exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ g isOpen_Ioi (hφ i) (hgz i) z hz
  · intro j i _ _
    exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ g isOpen_Ioi (hφ j) (hgij j i) z hz

/-- **The multiplier bound on the closed quadrant** `Iz ×ˢ Iθ`. -/
theorem zmul_quad (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hCnn : 0 ≤ zmulConst k * (1 + K) ^ 2 :=
    mul_nonneg (zmulConst_pos k).le (sq_nonneg _)
  have hRnn : 0 ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ :=
    mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k g z θ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · -- `z = 0`: the integrand vanishes (the radial weight is `0`)
    subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
  by_cases hs : Real.sin (2 * θ) = 0
  · -- `sin(2θ) = 0`: the integrand vanishes
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => φ z * g z θ) z θ hs]
    linarith
  · -- interior point of the quadrant
    have hbnd : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases lt_or_eq_of_le hbnd.1 with h | h
        · exact h
        · exact absurd (by rw [← h]; simp) hs
      · rcases lt_or_eq_of_le hbnd.2 with h | h
        · exact h
        · refine absurd ?_ hs
          rw [h]
          have hpi : 2 * (Real.pi / 2) = Real.pi := by ring
          rw [hpi, Real.sin_pi]
    exact zmul_open α k φ g hK hB hsm hg z hzpos θ hθ'

/-- **`ℋᵏ`-membership by domination on the closed quadrant.** -/
theorem hkMem_of_open_dominated (α : ℝ) (k : ℕ) {F g : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α k g)
    (hub : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α k F := by
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume]
      Set.Icc (0 : ℝ) (Real.pi / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hF α k
  constructor
  · -- the angular slices of the integrand are integrable on `Iθ`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero
        (fun θ _ => (Work.FTS.LocData.HkIntegrand_zero_fst α k F θ).symm) measurableSet_Icc
    · -- `z > 0`: dominate by the (integrable) slice of `g` on the open interval
      have hdom : IntegrableOn (fun θ => C * Work.Spaces.HkIntegrand α k g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        MeasureTheory.IntegrableOn.congr_set_ae ((hm.1 z hz).const_mul C) hIoo
      have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k F z θ)
          (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
        (Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k F)
          hcont hz0).aestronglyMeasurable measurableSet_Ioo
      have hle : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
          ‖Work.Spaces.HkIntegrand α k F z θ‖ ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)]
        exact hub z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      exact MeasureTheory.IntegrableOn.congr_set_ae
        (MeasureTheory.Integrable.mono' hdom haesm hle) hIoo.symm
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    have hdom : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iz := by
      show MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        C * Work.Spaces.HkIntegrand α k g z θ) (volume.restrict Work.Spaces.Iz)
      simpa only [MeasureTheory.integral_const_mul] using (hm.2).const_mul C
    have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        (volume.restrict Work.Spaces.Iz) := by
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α k F z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.Spaces.HkIntegrand α k F z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.HkIntegrand α k F z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ‖
          ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k g z θ := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        ((hm.1 z hz).const_mul C) ?_
      exact (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => hub z hz θ hθ)
    exact MeasureTheory.Integrable.mono' hdom haesm hle

end Work.FTS.StrongPersist.L3Aux
end
end
