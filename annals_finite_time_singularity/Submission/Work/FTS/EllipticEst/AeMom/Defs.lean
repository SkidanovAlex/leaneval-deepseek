/-
# The weak elliptic class with the angular moment conditions required only a.e.

## Why this class

`Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` requires the two angular moment conditions
`Fstar F z = 0` and `Fstar Ψ z = 0` **pointwise** for `z > 0`.  The induction of the elliptic
chapter applies the level-`(k-1)` estimate to the *radially differentiated* datum
`(D_z F, D_z Ψ)`, which requires that datum to be in the class, i.e. the pointwise moments of
`D_z F` and `D_z Ψ`.  Those are obtained from the moments of `F`, `Ψ` through the moment chain
`Fstar (D_z f)(z) - Fstar (D_z f)(s) = ∫_s^z Fstar (D_z² f)(r)/r dr`, whose hypotheses are
`SmoothOpen f` and `HkMem α l f` for `l ≥ 2` — so the chain yields only the **a.e.** statement
at level `1` (`Mine.FstarDzOneF.FstarDzOneF_ae`, `H2W.Fstar_DzIter_two_F_ae`), and the pointwise
upgrade needs one further level of `ℋ`-honesty (`HkMem α 3 F`).  Consequently

* `Mine.ShiftLevel`'s `k = 1` instance is **false** as stated,
* `remov.Fstar_DzIter_one_F` (the pointwise `F`-half with only `1 ≤ k`) is an open `sorry`,
* `Mine.LevelOne` (the level-`1` estimate from `EllWeak0`) is built on that false instance, and
  hence so is the base case of the induction — the whole `prop:Hk` chain is blocked there.

But the moment conditions are consumed only *slicewise inside the `z`-integral* by the level-`0`
estimate, so a null set of `z`-slices is harmless: the estimate, and every estimate above it, is
an integral statement.  Hence the class in which the induction actually closes has the moment
conditions only **a.e.** in `z`.  `EllWeakPosAe` below is that class; `EllWeakPos.toAe` records
that it is weaker than the pointwise class, so every theorem proved for `EllWeakPosAe` — in
particular the level-`0` estimate and each level of the induction — immediately yields the
corresponding statement for `EllWeakPos`.  The reverse direction is what fails, and it is
exactly what the radial shift needs.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeMom

/-- **The weak elliptic class with a.e. angular moment conditions.**  Same fields as
`Work.FTS.EllipticEst.TT.EllWeakPos`, except that the two moment conditions
`Fstar F ≡ 0`, `Fstar Ψ ≡ 0` are required only almost everywhere on `(0,∞)`. -/
def EllWeakPosAe (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
  (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
  (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0) ∧
  (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0) ∧
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
  Work.Spaces.HkMem α k F ∧
  Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)

/-- The pointwise-moment class is contained in the a.e.-moment class: a theorem about
`EllWeakPosAe` applies in particular to every datum of `TT.EllWeakPos`. -/
theorem EllWeakPos.toAe {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) : EllWeakPosAe α k F Ψ :=
  ⟨h.1, h.2.1, h.2.2.1,
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => h.2.2.2.1 z hz),
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => h.2.2.2.2.1 z hz),
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- **The level-`0` estimate in the a.e.-moment class** — the same statement as
`TT.EllWeak0`, with `EllWeakPosAe` in place of `EllWeakPos`.  This is the form in which the
estimate is *provable* and in which the radial shift is admissible at every level, hence the
form that carries the induction of `prop:Hk`; `TT.EllWeak0` follows from it by `toAe`. -/
def EllWeak0Ae (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPosAe α 0 F Ψ →
    α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkSq α 0 F

/-- **The level-`k` estimate in the a.e.-moment class** — the same statement as
`TT.EllEstUnif`, with `EllWeakPosAe` in place of `EllWeakPos`. -/
def EllEstUnifAe (k : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPosAe α k F Ψ →
    α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkNorm α k F

/-! ## Accessors, mirroring `TT.EllWeakPos`'s

These are named exactly as the ones of `TT.EllWeakPos` (`TT/WeakDefs.lean`), so that a proof
written for `TT.EllWeakPos` can be re-pointed at `EllWeakPosAe` by replacing the class name: the
only two fields whose *shape* differs are `orthF`/`orthPsi` (the a.e. moment conditions). -/

theorem EllWeakPosAe.eq {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ := h.1

theorem EllWeakPosAe.zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, Ψ z 0 = 0 := h.2.1

theorem EllWeakPosAe.pi_half {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ z, Ψ z (Real.pi / 2) = 0 := h.2.2.1

theorem EllWeakPosAe.orthF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0 := h.2.2.2.1

theorem EllWeakPosAe.orthPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0 := h.2.2.2.2.1

theorem EllWeakPosAe.smooth {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.1

theorem EllWeakPosAe.memF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k F := h.2.2.2.2.2.2.1

theorem EllWeakPosAe.memA {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  h.2.2.2.2.2.2.2.1

theorem EllWeakPosAe.memB {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPosAe α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.2.2.2.2.2.2.2.2

/-- **The a.e.-class induction, packaged from its two bases and its general step.**  The
level-`1` estimate (`AeMom.EllEstUnifAe_one`), the level-`2` estimate
(`AeMom.EllEstUnifAe_two`) and the step (`AeMom.EllEstUnifAe_step_of_pieces`, instantiated) give
the level-`k` estimate for every `k ≥ 2`. -/
theorem AeEllEstUnif_all_of_step
    (h1 : ∃ C : ℝ, 0 < C ∧ EllEstUnifAe 1 C)
    (h2 : ∃ C : ℝ, 0 < C ∧ EllEstUnifAe 2 C)
    (hstep : ∀ k : ℕ, 3 ≤ k → (∃ C : ℝ, 0 < C ∧ EllEstUnifAe (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ EllEstUnifAe k C) :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧ EllEstUnifAe k C := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases eq_or_lt_of_le hk with heq | hlt
    · subst heq
      exact h2
    · exact hstep k (by omega) (ih (k - 1) (by omega) (by omega))

end Work.FTS.EllipticEst.AeMom
