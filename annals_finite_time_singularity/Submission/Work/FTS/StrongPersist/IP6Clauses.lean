/-
# `Work.FTS.StrongPersist.IP6Clauses` — the structural clauses of the concrete `ℋ⁶` pairing

`H6Coer` (in `Defs.lean`) is the package the level-six energy estimate of `Persist.lean`
consumes: nonnegativity of the diagonal, additivity and homogeneity in the first argument,
Cauchy–Schwarz, comparability with the `ℋ⁶`-norm, and coercivity of `𝓛_Γ^T`.  This file
discharges the **structural** clauses for the concrete nested pairing

`IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α = HkIPStep e₁ e₂ (HkIPStep f₁ f₂ IP4)`

by transporting the generic lemmas of the coercivity chapter through the two top recursion
steps:

* `IP6_symm` — symmetry, from `Work.Coercivity.H1IP_comm` through
  `CoercivityFix.Assembly.vc_symm` (no hypotheses at all);
* `IP6_smul` — homogeneity in the first argument, from `Work.Coercivity.H1IP_homog` through
  `vc_smul` (no hypotheses);
* `IP6_neg` — negation covariance, the instance `c = -1` of `IP6_smul`;
* `IP6_nonneg` — nonnegativity of the diagonal for nonnegative coefficients, from
  `Work.Coercivity.H1IP_nonneg` through `vc_nonneg`.

What remains of `H6Coer` for the concrete `IP6` is the *analytic* content: additivity/congruence
on the honest `HQo α 6` class (the two-step iteration of `IPGen.Comm2o_succ`, requested
separately), Cauchy–Schwarz, comparability (`lo`/`up`), and the coercivity of `𝓛_Γ^T` at level
six (`coer`/`coerNeg`), which is the level-six instance of the corrected induction of
`FTS/CoercivityFix`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.V_core
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.FTS.IPGen.IP4Add

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

/-- **The diagonal of the concrete `ℋ⁶` pairing is nonnegative** as soon as the ten recursion
coefficients are: the recursion is a positive combination of the pairings
`wip ρ (D u) (D u) = ∫∫ (D u)² ρ` with nonnegative weights, and nonnegativity is transported by
`vc_nonneg` from `H1IP_nonneg`. -/
theorem IP6_self_nonneg {e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂') (hc₁'' : 0 ≤ c₁'')
    (hc₂'' : 0 ≤ c₂'') (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂)
    (α : ℝ) (u : Fn) :
    0 ≤ IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u u :=
  vc_nonneg he₁ he₂
    (vc_nonneg hf₁ hf₂
      (vc_nonneg hc₁'' hc₂''
        (vc_nonneg hc₁' hc₂'
          (vc_nonneg hc₁ hc₂
            (fun u => Work.Coercivity.H1IP_nonneg α u))))) u



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

/-- **`coerNeg` from `coer`.**  The negation-normal form of a coercivity lower bound is not an
independent obligation: `linPart α f = -𝓛_Γ^T f` is *definitionally* the negation of `LGammaT α f`,
and `IP6_neg` is negation covariance of the pairing. -/
theorem IP6_coerNeg_of_coer (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α cc : ℝ) {f : Fn}
    (h : cc * Sq6 α f ≤ IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (LGammaT α f) f) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (linPart α f) f ≤ -(cc * Sq6 α f) := by
  have hneg := IP6_neg e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α (LGammaT α f) f
  have hlp : linPart α f = fun z θ => -(LGammaT α f z θ) := rfl
  rw [hlp, hneg]
  linarith

/-- **The `H6Coer` package for the concrete `IP6` from its analytic content.**  All the
structural clauses are supplied by `IP6_self_nonneg`, `IP6_add` and `IP6_smul`; what remains to be
proved for the concrete pairing is `cs` (Cauchy–Schwarz) and `lo`/`up` (compatibility with the
`ℋ⁶` norm). -/
theorem H6Coer_of_clauses {e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂') (hc₁'' : 0 ≤ c₁'') (hc₂'' : 0 ≤ c₂'')
    {α₂ cc CC : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc) (hCC : 0 < CC)
    (hcs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
      |IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Xn6 α f * Xn6 α g)
    (hlo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f →
      Sq6 α f ≤ IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f)
    (hup : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, H6Adm α f →
      IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f ≤ CC * Sq6 α f) :
    H6Coer (IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc CC :=
  { pos := ⟨hcc, hCC, hα₂⟩
    nonneg := fun α _ f _ =>
      IP6_self_nonneg hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂'' he₁ he₂ hf₁ hf₂ α f
    add := fun α hα u v w h₁ h₂ h₃ =>
      IP6_add e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α hα.1 h₁.1 h₂.1 h₃.1 h₁.2 h₂.2 h₃.2
    smul := fun α hα c f g h₁ h₂ =>
      IP6_smul e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α c f g
    cs := hcs
    lo := hlo
    up := hup }

/-- **`up` from `cs`.**  The comparability clause `IP6 f f ≤ CC |f|²_{ℋ⁶}` of `H6Coer` is not an
independent obligation: Cauchy–Schwarz against the `ℋ⁶`-norm, applied to the pair `(f, f)`, gives
`IP6 f f ≤ |IP6 f f| ≤ CC |f|_{ℋ⁶}²`. -/
theorem IP6_up_of_cs (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ CC : ℝ)
    (hcs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
      |IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g| ≤ CC * Xn6 α f * Xn6 α g) :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 6 f →
      IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f ≤ CC * Sq6 α f := by
  intro α hα f hf
  have h := hcs α hα f f hf hf
  have hle : IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f
      ≤ |IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f| := le_abs_self _
  have hsq : Xn6 α f * Xn6 α f = Sq6 α f := by
    rw [← sq, Xn6_sq]
  calc IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f
      ≤ |IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f| := hle
    _ ≤ CC * Xn6 α f * Xn6 α f := h
    _ = CC * Sq6 α f := by rw [mul_assoc, hsq]

/-- **The `H6Coer` package from `cs` and `lo`.**  With `up` reduced to Cauchy–Schwarz
(`IP6_up_of_cs`), the level-six inner-product package of the concrete `IP6` needs only two
analytic inputs, together with the nonnegativity of the ten recursion coefficients:

* `cs` — Cauchy–Schwarz against the honest `ℋ⁶`-norm on `HQo α 6`;
* `lo` — the `ℋ⁶`-norm squared dominated by the diagonal. -/
theorem H6Coer_of_cs_lo {e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂') (hc₁'' : 0 ≤ c₁'') (hc₂'' : 0 ≤ c₂'')
    {α₂ cc CC : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc) (hCC : 0 < CC)
    (hcs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 6 f → HQo α 6 g →
      |IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g| ≤ CC * Xn6 α f * Xn6 α g)
    (hlo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 6 f →
      Sq6 α f ≤ IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f) :
    H6Coer (IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc CC :=
  H6Coer_of_clauses he₁ he₂ hf₁ hf₂ hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂'' hα₂ hcc hCC hcs
    (fun α hα f hf => hlo α hα f hf.reg)
    (fun α hα f hf => IP6_up_of_cs _ _ _ _ _ _ _ _ _ _ α₂ CC hcs α hα f hf.reg)

end Work.FTS.StrongPersist
