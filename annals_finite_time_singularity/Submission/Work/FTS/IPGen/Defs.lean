/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/IPGen/` — the `IP`-generation chapter (design §2 of `FTS_ELL_GALERKIN.md`)

This is the interface chapter of the subproject `IPGen`.  It fixes

* `CoefMax c₁ … c₂''`, the single constant that dominates the six step coefficients of the
  coercive recursion `Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''`;
* `IPnG c₁ c₂ α n`, the same recursion with a *single* coefficient pair, iterated from
  `H1IP α` (so that `Assembly.IP4 c₁ … c₂''` becomes a three-step composite of it);
* `N4ExtraQ`, the **corrected** `N4Extra'` contract: the design (`FTS_ELL_GALERKIN.md` §New
  defects) shows that the clauses `cs`, `add`, `smul`, `neg`, `congr` of
  `Work.FTS.OpenPkg.N4Extra'` are *junk traps* as stated, because `HkMem` carries no
  smoothness: for `f₁ = h` nowhere differentiable and `f₂ = s − h` smooth, the derivative
  slots of `IP(f₁, g)` fade out and additivity fails.  The repair is to replace `HkMem α 4`
  by `HQo α 4 = SmoothOpen ∧ HkMem α 4` in exactly those five clauses;
* `IPLinHQo`, the linearity/Cauchy–Schwarz/congruence package consumed by
  `Work.FTS.ScratchC46.weakDetermines'_of` (design §4).

The analytic content (the slot domination `ip4SlotDomGen`, the leaf Cauchy–Schwarz, the
clauses for the concrete `Assembly.IP4`, the exposed headline and the `IPLinHQo` instance)
lives in the sibling modules of this directory.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.TransportS.Slots

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

theorem coefMax_pos (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : 0 < CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' :=
  lt_of_lt_of_le one_pos (one_le_coefMax _ _ _ _ _ _)

theorem coefMax_nonneg (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    0 ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_of_lt (coefMax_pos _ _ _ _ _ _)

/-- `CoefMax` is the outermost of a chain of six `max`es; these are the successive links. -/
theorem coefMax_le₁ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))
      ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := le_max_right _ _

theorem coefMax_le₂ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))
      ≤ max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂'')))) := le_max_right _ _

theorem coefMax_le₃ (c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    max c₁' (max c₂' (max c₁'' c₂'')) ≤ max c₂ (max c₁' (max c₂' (max c₁'' c₂''))) :=
  le_max_right _ _

theorem coefMax_le₄ (c₁' c₂' c₁'' c₂'' : ℝ) :
    max c₂' (max c₁'' c₂'') ≤ max c₁' (max c₂' (max c₁'' c₂'')) := le_max_right _ _

theorem coefMax_le₅ (c₂' c₁'' c₂'' : ℝ) :
    max c₁'' c₂'' ≤ max c₂' (max c₁'' c₂'') := le_max_right _ _

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

/-- Each of the three *pair* maxima is dominated by `CoefMax`. -/
theorem max_pair_le_coefMax (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    max 1 (max c₁ c₂) ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂''
      ∧ max 1 (max c₁' c₂') ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂''
      ∧ max 1 (max c₁'' c₂'') ≤ CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' := by
  refine ⟨max_le (one_le_coefMax _ _ _ _ _ _) (max_le le_coefMax₁ le_coefMax₂),
    max_le (one_le_coefMax _ _ _ _ _ _) (max_le le_coefMax₁' le_coefMax₂'), ?_⟩
  exact max_le (one_le_coefMax _ _ _ _ _ _) (max_le le_coefMax₁'' le_coefMax₂'')

/-! ## The recursion with arbitrary step coefficients -/

/-- The paper's step recursion `HkIPStep c₁ c₂`, iterated `n` times from the base `H1IP α`:
`IPnG c₁ c₂ α 0 = H1IP α`, `IPnG c₁ c₂ α (n+1) = HkIPStep c₁ c₂ (IPnG c₁ c₂ α n)`. -/
def IPnG (c₁ c₂ : ℝ) (α : ℝ) : ℕ → Fn → Fn → ℝ
  | 0 => Work.Coercivity.H1IP α
  | n + 1 => Work.Coercivity.HkIPStep c₁ c₂ (IPnG c₁ c₂ α n)

@[simp] theorem IPnG_zero (c₁ c₂ α : ℝ) : IPnG c₁ c₂ α 0 = Work.Coercivity.H1IP α := rfl
@[simp] theorem IPnG_succ (c₁ c₂ α : ℝ) (n : ℕ) :
    IPnG c₁ c₂ α (n + 1) = Work.Coercivity.HkIPStep c₁ c₂ (IPnG c₁ c₂ α n) := rfl

/-- The level-`2` inner product of `CoercivityFix` is `IPnG` at level `1`. -/
theorem IPnG_one_eq_IP2 (c₁ c₂ α : ℝ) :
    IPnG c₁ c₂ α 1 = Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α := rfl

/-- The level-`3` inner product of `CoercivityFix` is one more step of `IPnG`. -/
theorem IPnG_two_eq_IP3 (c₁ c₂ c₁' c₂' α : ℝ) :
    Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1)
      = Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α := rfl

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

/-- **`IP` linearity, Cauchy–Schwarz and congruence on the open class** `HQo α 4`.

This is the interface consumed by `Work.FTS.ScratchC46.weakDetermines'_of` (design §4,
"Replace `hRegLin`/`hRegRHS` by `HQo α 4` versions plus `IPLinHQo`"): the weak form of the
Galerkin equation is tested against compactly supported basis elements, where only the open
class `HQo α 4` (interior `C^∞` plus honesty, no boundary traces) is available, and the two
ingredients used are additivity/homogeneity in the first argument and the `ℋ⁴`-Cauchy–
Schwarz bound. -/
def IPLinHQo (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, Work.FTS.VocabO.HQo α 4 f₁ →
    Work.FTS.VocabO.HQo α 4 f₂ → Work.FTS.VocabO.HQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g ∧
    (∀ c : ℝ, IP α (fun z θ => c * f₁ z θ) g = c * IP α f₁ g) ∧
    |IP α f₁ g| ≤ Ct * Xn α f₁ * Xn α g ∧
    (∀ f', (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f₁ z θ = f' z θ) → IP α f₁ g = IP α f' g)

end Work.FTS.IPGen
