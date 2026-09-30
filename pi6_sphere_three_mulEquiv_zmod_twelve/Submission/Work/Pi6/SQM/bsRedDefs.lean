import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Reduction of integral cochains (`Work.Pi6.SQM.BS`, private to `bocksteinSqTwo`)

A cochain on a simplicial set is a linear functional on the chain module, so it is determined by
its values on the generators (the simplices); `vals` is the cochain with prescribed values.
The reduction maps `red2 : C^n(X;ℤ) → C^n(X;𝔽₂)`, `red4 : C^n(X;ℤ) → C^n(X;ℤ/4)` and
`red42map : C^n(X;ℤ/4) → C^n(X;𝔽₂)` are all defined through their values, which is what makes
them usable.  (`red2`/`red4` are not the base-change maps of chain complexes: they are defined on
cochains by reducing values, which is what the cochain-level arguments of `REFS/NOTES_LEAD_SQM.md`
§3–§4 need.)

The degree of the cochain is an *implicit* argument: it is read off from the cochain to which the
reduction is applied.  This matters for rewriting: with an explicit degree, a lemma such as
`red2 (u ∪₁ v) = red2 u ∪₁ red2 v` would only match goals in which the degree is literally
`syntactically` `n + m - 1`, while implicit degrees make the degree slot a metavariable, so the
match is driven by the cochain argument alone.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff genEval_ext)

/-! Namespace for the cochain-level reduction calculus used by `bocksteinSqTwo`.  It is kept
separate because the sibling files of area `SQM` use their own (chain-level) reduction vocabulary. -/
namespace BS

/-- **The cochain with prescribed values on the generators.** -/
def vals (R : Type) [CommRing R] (X : SSet) (n : ℕ) (v : X _⦋n⦌ → R) :
    Cochain R X n :=
  ((X.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk (ModuleCat.of R R)
      (fun σ : X _⦋n⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton R R (v σ))))).hom

theorem genEval_vals (R : Type) [CommRing R] (X : SSet) (n : ℕ) (v : X _⦋n⦌ → R)
    (σ : X _⦋n⦌) : genEval R X (vals R X n v) σ = v σ := by
  have h1 := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun σ : X _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (v σ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1 : R)) h1
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h2
  exact h2

/-- **Reduction of an integral cochain mod `2`.** -/
def red2 (X : SSet) {n : ℕ} (α : Cochain ℤ X n) : Cochain F2 X n :=
  vals F2 X n (fun σ => ((genEval ℤ X α σ : ℤ) : F2))

theorem genEval_red2 (X : SSet) {n : ℕ} (α : Cochain ℤ X n) (σ : X _⦋n⦌) :
    genEval F2 X (red2 X α) σ = ((genEval ℤ X α σ : ℤ) : F2) := by
  rw [red2, genEval_vals]

/-- **Reduction of an integral cochain mod `4`.** -/
def red4 (X : SSet) {n : ℕ} (α : Cochain ℤ X n) : Cochain (ZMod 4) X n :=
  vals (ZMod 4) X n (fun σ => ((genEval ℤ X α σ : ℤ) : ZMod 4))

theorem genEval_red4 (X : SSet) {n : ℕ} (α : Cochain ℤ X n) (σ : X _⦋n⦌) :
    genEval (ZMod 4) X (red4 X α) σ = ((genEval ℤ X α σ : ℤ) : ZMod 4) := by
  rw [red4, genEval_vals]

/-- **Reduction of a `ℤ/4`-cochain mod `2`** (via `ZMod.castHom`). -/
def red42map (X : SSet) {n : ℕ} (Y : Cochain (ZMod 4) X n) : Cochain F2 X n :=
  vals F2 X n (fun σ => r42 (genEval (ZMod 4) X Y σ))

theorem genEval_red42map (X : SSet) {n : ℕ} (Y : Cochain (ZMod 4) X n) (σ : X _⦋n⦌) :
    genEval F2 X (red42map X Y) σ = r42 (genEval (ZMod 4) X Y σ) := by
  rw [red42map, genEval_vals]

/-- Reducing an integral cochain to `𝔽₂` is reducing it to `ℤ/4` first. -/
theorem red2_red4 (X : SSet) {n : ℕ} (α : Cochain ℤ X n) :
    red2 X α = red42map X (red4 X α) := by
  apply genEval_ext
  intro σ
  rw [genEval_red2, genEval_red42map, genEval_red4]
  norm_num

end BS

end

end Work.Pi6.SQM
