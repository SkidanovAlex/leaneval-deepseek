import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift/selection combinatorics of the tower recursion

`Work.Diff.EXT.ConnCov.honestTower` defines the *honest* recursion `hstep = step + drop` and the
honest tower `htower`.  Since `step = hstep - drop` *definitionally*, the tower `tower cov base` and
the honest tower `htower cov base` are related by a fixed ℤ-combination of "selection objects":

  `tower cov base m = Σ_{j ≤ m} (-1)^{m+j} (m-j)! · Σ_{f : Fin j ↪o Fin m} (htower cov base j) ∘ f`.

The combinatorial skeleton of this identity is the pair of *insertion* maps on strictly monotone
maps `Fin j ↪o Fin n`:

* `insF` inserts a new *first* index (`0 ↦ 0`, `l.succ ↦ (f l).succ`), and
* `shiftF` shifts everything by one (`l ↦ (f l).succ`),

together with the two "inverse" maps `tailF` (remove the leading `0`) and `shiftInvF` (subtract one).
The strictly monotone maps `Fin k ↪o Fin (n+1)` split, according to whether their value at `0` is `0`
or not, into the images of `insF` and `shiftF`; this is the reindexing that produces the recursion
`c(m+1,j) = c(m,j-1) - (m-j+1)c(m,j)` for the coefficients.

This module provides the vocabulary (`Hom`, `insF`, `shiftF`, `tailF`, `shiftInvF`, `sel`, `SelSum`,
`SelSumIns`, `SelSumSh`) and the basic value/injectivity lemmas.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicTr

open Work.Diff.EXT.ATower Work.Diff.EXT.ConnCov

/-- Strictly monotone maps `Fin j → Fin n`.  They index the selections of `j` direction slots out
of `n`. -/
abbrev Hom (j n : ℕ) : Type := {f : Fin j → Fin n // StrictMono f}

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The selection of direction slots -/

/-- `sel τ f` is `τ` with the direction tuple read through `f`. -/
noncomputable def sel {j n : ℕ} (τ : Op3 (I := I) (M := M) j) (f : Fin j → Fin n) :
    Op3 (I := I) (M := M) n :=
  fun v A B C => τ (fun l => v (f l)) A B C

@[simp] theorem sel_apply {j n : ℕ} (τ : Op3 (I := I) (M := M) j) (f : Fin j → Fin n)
    (v : Fin n → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) :
    sel τ f v A B C = τ (fun l => v (f l)) A B C := rfl

/-! ## The two insertions and their inverses -/

/-- The underlying function of `insF`. -/
noncomputable def insFFun {j n : ℕ} (f : Hom j n) : Fin (j + 1) → Fin (n + 1) :=
  fun i => Fin.cases (0 : Fin (n + 1)) (fun l : Fin j => (f.val l).succ) i

/-- Insert a new first slot `0` at the front (`insF f 0 = 0`, `insF f l.succ = (f l).succ`). -/
noncomputable def insF {j n : ℕ} (f : Hom j n) : Hom (j + 1) (n + 1) :=
  ⟨insFFun f,
    Fin.strictMono_cons.2 ⟨fun l => Fin.succ_pos _, Fin.strictMono_succ.comp f.property⟩⟩

@[simp] theorem insF_val_zero {j n : ℕ} (f : Hom j n) : (insF f).val 0 = 0 := by
  show insFFun f 0 = 0
  simp only [insFFun, Fin.cases_zero]

@[simp] theorem insF_val_succ {j n : ℕ} (f : Hom j n) (l : Fin j) :
    (insF f).val l.succ = (f.val l).succ := by
  show insFFun f l.succ = (f.val l).succ
  simp only [insFFun, Fin.cases_succ]

/-- Shift all values up by one (`shiftF f l = (f l).succ`). -/
noncomputable def shiftF {j n : ℕ} (f : Hom j n) : Hom j (n + 1) :=
  ⟨fun l => (f.val l).succ, Fin.strictMono_succ.comp f.property⟩

@[simp] theorem shiftF_val {j n : ℕ} (f : Hom j n) (l : Fin j) :
    (shiftF f).val l = (f.val l).succ := rfl

theorem insF_val_ne_zero {j n : ℕ} (f : Hom j n) {l : Fin (j + 1)} (hl : l ≠ 0) :
    (insF f).val l ≠ 0 := by
  obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.mpr hl
  rw [insF_val_succ]
  exact Fin.succ_ne_zero _

theorem shiftF_val_ne_zero {j n : ℕ} (f : Hom j n) {l : Fin j} : (shiftF f).val l ≠ 0 := by
  rw [shiftF_val]
  exact Fin.succ_ne_zero _

theorem insF_injective {j n : ℕ} : Function.Injective (insF : Hom j n → Hom (j + 1) (n + 1)) := by
  intro f f' h
  have hval : (insF f).val = (insF f').val := congrArg Subtype.val h
  refine Subtype.ext (funext fun l => ?_)
  have := congrFun hval l.succ
  rw [insF_val_succ, insF_val_succ] at this
  exact Fin.succ_injective n this

theorem shiftF_injective {j n : ℕ} : Function.Injective (shiftF : Hom j n → Hom j (n + 1)) := by
  intro f f' h
  have hval : (shiftF f).val = (shiftF f').val := congrArg Subtype.val h
  refine Subtype.ext (funext fun l => ?_)
  have := congrFun hval l
  rw [shiftF_val, shiftF_val] at this
  exact Fin.succ_injective n this

theorem tailF_ne {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 = 0) (l : Fin k) :
    g.val l.succ ≠ 0 := by
  have hlt : g.val 0 < g.val l.succ := g.property (Fin.succ_pos l)
  rw [hg] at hlt
  exact Fin.ne_of_gt hlt

/-- The inverse of `insF`: delete the leading `0` and subtract one. -/
noncomputable def tailF {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 = 0) : Hom k n :=
  ⟨fun l => Fin.pred (g.val l.succ) (tailF_ne g hg l),
    Fin.strictMono_pred_comp (tailF_ne g hg) (g.property.comp Fin.strictMono_succ)⟩

@[simp] theorem tailF_val_succ {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 = 0)
    (l : Fin k) : ((tailF g hg).val l).succ = g.val l.succ :=
  Fin.succ_pred (g.val l.succ) (tailF_ne g hg l)

theorem shiftInvF_ne {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 ≠ 0) (l : Fin (k + 1)) :
    g.val l ≠ 0 := by
  intro h0
  have hle : g.val 0 ≤ g.val l := g.property.monotone (Fin.zero_le l)
  rw [h0] at hle
  exact hg (le_antisymm hle (Fin.zero_le _))

/-- The inverse of `shiftF`: subtract one (possible because the value at `0` is nonzero). -/
noncomputable def shiftInvF {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 ≠ 0) :
    Hom (k + 1) n :=
  ⟨fun l => Fin.pred (g.val l) (shiftInvF_ne g hg l),
    Fin.strictMono_pred_comp (shiftInvF_ne g hg) g.property⟩

@[simp] theorem shiftInvF_val_succ {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 ≠ 0)
    (l : Fin (k + 1)) : ((shiftInvF g hg).val l).succ = g.val l :=
  Fin.succ_pred (g.val l) (shiftInvF_ne g hg l)

theorem tailF_insF {j n : ℕ} (f : Hom j n) : tailF (insF f) (insF_val_zero f) = f := by
  refine Subtype.ext (funext fun l => Fin.succ_injective n ?_)
  rw [tailF_val_succ, insF_val_succ]

theorem insF_tailF {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 = 0) :
    insF (tailF g hg) = g := by
  refine Subtype.ext (funext fun l => ?_)
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
  · rw [insF_val_zero, hg]
  · rw [insF_val_succ, tailF_val_succ]

theorem shiftInvF_shiftF {k n : ℕ} (f : Hom (k + 1) n) :
    shiftInvF (shiftF f) (shiftF_val_ne_zero f) = f := by
  refine Subtype.ext (funext fun l => Fin.succ_injective n ?_)
  rw [shiftInvF_val_succ, shiftF_val]

theorem shiftF_shiftInvF {k n : ℕ} (g : Hom (k + 1) (n + 1)) (hg : g.val 0 ≠ 0) :
    shiftF (shiftInvF g hg) = g := by
  refine Subtype.ext (funext fun l => ?_)
  rw [shiftF_val, shiftInvF_val_succ]

/-! ## The selection sums

`SelSum F j n` is the sum of `sel (F j) f` over all strictly monotone `f : Fin j → Fin n`; the
shift identity expresses `tower cov base m` in terms of `SelSum (htower cov base) j m`.  The two
components of the decomposition of `SelSum F k (m+1)` according to the value at `0` of `f` are
`SelSumIns` (the `0`-case) and `SelSumSh` (the nonzero case). -/

/-- The sum of `sel (F j) f` over all strictly monotone `f : Fin j → Fin n`. -/
noncomputable def SelSum (F : (k : ℕ) → Op3 (I := I) (M := M) k) (j n : ℕ) :
    Op3 (I := I) (M := M) n :=
  ∑ f : Hom j n, sel (F j) f.val

/-- The `0`-case of `SelSum F (j+1) (n+1)`: the selections through `insF`. -/
noncomputable def SelSumIns (F : (k : ℕ) → Op3 (I := I) (M := M) k) (j n : ℕ) :
    Op3 (I := I) (M := M) (n + 1) :=
  ∑ f : Hom j n, sel (F (j + 1)) (insF f).val

/-- The nonzero case of `SelSum F j (n+1)`: the selections through `shiftF`. -/
noncomputable def SelSumSh (F : (k : ℕ) → Op3 (I := I) (M := M) k) (j n : ℕ) :
    Op3 (I := I) (M := M) (n + 1) :=
  ∑ f : Hom j n, sel (F j) (shiftF f).val

end Work.Diff.EXT.ConnCov.RicTr
