/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.RulingELF` — the installed ruling vocabulary (lead, 2026-10-11)

Verbatim copy of the statements of `sources/ftsV2/fts_ellimok_ruling.lean` (namespace
`Work.FTS_EllLimOK.RulingELF` there; not a workspace module, so the copy lives here), together with
the proof of the proved helper `existsEllSolC8_of_threshold`.

The ruling **denies** `ExistsEllSolCF` because `HasPkgF` is false:

* `PkgMemSq` / `PkgSlice` fail by homogeneity (`HkSq` is quadratic in `g`, the bound linear) —
  machine-checked in the ruling as `pkgMemSq_degenerate` / `not_hasPkgF_of_pos`;
* `PkgDecay` is false (class `C` allows `z^{-s}` tails, `s ∈ (1/2,3/2)`, and `bslOp` is Euler in
  `z`), so the `1/(1+z)` rate of `Defs3.LocalBound4` is retired as well;
* `PkgStrip`/`PkgCorner` are false (`z^s`, `s ∈ (3/2,2)`; `θ^σ`, `σ < 1`).

Kept: `HasPkg`, `PkgCos`, the minimal limit package `FatouPkgG` (the frozen `FatouPkg` is dead
because of `ZDecay`), the uniqueness chain and `EllLimOK3`.  Replaced by the honest internal
hypothesis

```
HasPkgH α Ce E := HasPkg α Ce E ∧ PkgCos α E ∧ PkgMemSqH α Ce E ∧ PkgBoxH α E
```

whose producers `L1` (`PkgCos`), `L2` (`PkgMemSqH`), `L3` (`PkgBoxH`) are bundled as `ProducerH`
and are to be proved from route (b), i.e. from the level-8 existence class
`∀ g ∈ ClassC, ∃ Ψ, EllClassOk 8 α g Ψ`.

The frozen target's hypothesis also changed: `FinalV2.Producers.core1_1a3` now takes the route (b)
input `hb`, and the wire passes `ClassC.ellClassOk_exists_of_classC`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.FatouG
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ellPkgConj_of_classOk
import Submission.Work.FTS.EllSol.existsEllSolC_classC_noEst
import Submission.Work.FTS.EllSol.existsEllSolC_classC_of
import Submission.Work.FTS.ClassC.A6
import Submission.Work.FTS.ClassC.ellClassOk_add_gen
import Submission.Work.FTS.ClassC.ellClassOk_exists_of_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.RulingELF

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## (A) `PkgMemSq` is degenerate (homogeneity): `HkSq` is quadratic, `Xn6` linear. -/

/-- Any linear `E` with `PkgMemSq` has `HkSq α 0 (E g) ≤ 0` on the whole class `C`,
i.e. `E g = 0` in weighted `L²` — impossible for a solution operator.  Hence `HasPkgF` and
`ExistsEllSolCF` are false as stated. -/
theorem pkgMemSq_degenerate {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : PkgMemSq α Ce E)
    {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) : Work.Spaces.HkSq α 0 (E g) ≤ 0 := by
  set S := Work.Spaces.HkSq α 0 (E g) with hSdef
  set X := Work.FTS.StrongGlobal.Xn6 α g with hXdef
  have key : ∀ t : ℝ, 0 < t → t ^ 2 * S ≤ Ce * (t * X) := by
    intro t ht
    have h1 := (h (t • g) (Work.FTS.ClassC.classC_smul t hg)).1.2.1
    rw [map_smul, Work.FTS.EllipticEst.HkSq_smul] at h1
    have h2 : Work.FTS.StrongGlobal.Xn6 α (t • g) = t * X := by
      simp only [Work.FTS.StrongGlobal.Xn6, Work.FTS.EllipticEst.HkNorm_smul, abs_of_pos ht, hXdef]
    rw [h2] at h1
    exact h1
  by_contra hS
  rw [not_le] at hS
  set t : ℝ := (|Ce| * |X| + 1) / S with htdef
  have ht : 0 < t := by positivity
  have htS : t * S = |Ce| * |X| + 1 := by rw [htdef]; field_simp
  have h1 := key t ht
  have h2 : t ^ 2 * S = t * (|Ce| * |X| + 1) := by rw [← htS]; ring
  have h3 : Ce * (t * X) ≤ t * (|Ce| * |X|) := by
    have : Ce * X ≤ |Ce| * |X| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith
  nlinarith

theorem not_hasPkgF_of_pos {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {g : Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hpos : 0 < Work.Spaces.HkSq α 0 (E g)) :
    ¬ HasPkgF α Ce E :=
  fun h => absurd (pkgMemSq_degenerate h.memSq hg) (not_le.mpr hpos)

/-! ## (B) Route (b) keeps `EllClassOk 8` (same proof as `existsEllSolC_of_threshold`). -/

/-- `ExistsEllSolC` plus the level-`8` existence class at the selected operator. -/
def ExistsEllSolC8 : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ E : Fn →ₗ[ℝ] Fn, ∀ g, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)

theorem existsEllSolC8_of_threshold
    (hb : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ g : Fn,
      Work.FTS.ClassC.ClassC α g → ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    ExistsEllSolC8 := by
  obtain ⟨α₁, hα₁, hb⟩ := hb
  obtain ⟨Ce, α₀, hCe, hα₀, hPkg⟩ :=
    Work.FTS.EllSol.ellPkgConj_of_classOk (Work.FTS.EllSol.ellEstUnifAll 4 (by norm_num))
      (Work.FTS.EllSol.ellEstUnifAll 6 (by norm_num))
  refine ⟨Ce, hCe, min α₀ α₁, lt_min hα₀ hα₁, ?_⟩
  intro α hα hαm
  have hα₀' : α ≤ α₀ := le_trans hαm (min_le_left _ _)
  have hα₁' : α ≤ α₁ := le_trans hαm (min_le_right _ _)
  let P : Fn → Fn → Prop := fun g Ψ =>
    Work.FTS.EllExist.EllClassOk 8 α g Ψ ∧ Work.FTS.VocabO.EllPkgGo α Ce g Ψ ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce g Ψ
  have hPkg' : ∀ g Ψ : Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ → P g Ψ := by
    intro g Ψ hg hok
    have h := hPkg α g Ψ hα hα₀' (Work.FTS.EllSol.classC_to_ellSolClassC hg) hok
    exact ⟨hok, h.1, Work.FTS.EllSol.EllPkgK_of_ellSol h.2⟩
  have hP0 : P 0 0 :=
    hPkg' 0 0 (Work.FTS.ClassC.classC_zero α) (Work.FTS.EllSol.ellClassOk_zero_eight_fts α)
  have hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, Work.FTS.ClassC.ClassC α g →
      Work.FTS.ClassC.ClassC α g' → P g Ψ → P g' Ψ' →
      P (g + c • g') (Ψ + c • Ψ') := by
    intro g g' Ψ Ψ' c hg hg' hP hP'
    exact hPkg' (g + c • g') (Ψ + c • Ψ')
      (Work.FTS.ClassC.classC_add hg (Work.FTS.ClassC.classC_smul c hg'))
      (Work.FTS.ClassC.ellClassOk_add_gen 8 hα c hg hg' hP.1 hP'.1)
  have hex : ∀ g, Work.FTS.ClassC.ClassC α g → ∃ Ψ, P g Ψ := by
    intro g hg
    obtain ⟨Ψ, hok⟩ := hb α hα hα₁' g hg
    exact ⟨Ψ, hPkg' g Ψ hg hok⟩
  obtain ⟨E, hE⟩ := Work.FTS.ClassC.exists_linear_selector_classC hP0 hPlin hex
  exact ⟨E, hE⟩

/-- The wire input: A2 gives `ExistsEllSolC8`. -/
theorem existsEllSolC8_routeB : ExistsEllSolC8 :=
  existsEllSolC8_of_threshold Work.FTS.ClassC.ellClassOk_exists_of_classC

/-! ## (C) The honest replacement fields (producers L1–L3 are the open part). -/

/-- Quantitative level-0 memberships, squared norm, `z`-local slice bound. -/
def PkgMemSqH (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ Ψ : Fn, (Ψ = E g ∨ Ψ = fun z θ => E g z θ / Real.cos θ) →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkSq α 0 Ψ ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g ^ 2 ∧
      ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          ≤ Ce * (1 + 1 / z) * Work.FTS.StrongGlobal.Xn6 α g ^ 2

/-- Closed-box `C²` with a box-local sup bound and a uniform Hölder modulus of the second
derivative (replaces `PkgStrip` + `PkgCorner`, both false).

**CORRECTION of the lead's statement (2026-10-11, after the ruling).**  The two
`iteratedFDerivWithin` clauses carry the extra guard `a < b`.  Without it the statement is
**underivable**: for `a = b` the box `cbox a a = {a} × [0,π/2]` is a segment, hence not
`UniqueDiffWithinAt`, so `HasFDerivWithinAt` there constrains the derivative only in the vertical
direction and the within-derivatives form an *unbounded affine line*; `fderivWithin` is an opaque
`Classical.choose`, so clauses 2 and 3 cannot hold.  Machine-checked witnesses (sorry-free):
`ProducerH/BoxAux/_probe_degenerate.lean` (`degBox_witness_line`,
`degBox_not_uniqueDiffWithinAt`); the full analysis is in `ProducerH/NOTES_pkgBoxH.md`.  Clause 1
(`ContDiffOn`) is fine for `a ≤ b`: the degenerate box follows from `cbox a (a+1)` by
`ContDiffOn.mono` (see `ClosedCompact3H_of_bounds_fatou`). -/
def PkgBoxH (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∃ K β : ℝ, 0 < K ∧ 0 < β ∧
    ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) (cbox a b) ∧
      (a < b → ∀ k : ℕ, k ≤ 2 → ∀ p ∈ cbox a b,
        ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g)) (cbox a b) p‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (a < b → ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
        ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (cbox a b) p
          - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (cbox a b) q‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β)

/-- The honest repaired hypothesis (internal to `FTS_EllLimOK`). -/
def HasPkgH (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkg α Ce E ∧ PkgCos α E ∧ PkgMemSqH α Ce E ∧ PkgBoxH α E

/-- L1+L2+L3 (open): route (b)'s level-8 class gives the honest fields. -/
def ProducerH : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, ∀ E : Fn →ₗ[ℝ] Fn,
    (∀ g, Work.FTS.ClassC.ClassC α g → Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) →
    ∃ Ce' : ℝ, 0 < Ce' ∧ HasPkgH α (max Ce Ce') E

end Work.FTS_EllLimOK.RulingELF
