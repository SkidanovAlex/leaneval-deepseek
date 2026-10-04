import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A clash-free kit for the fixed/moving connection flip

The workspace contains two *incompatible* chains of duplicate declarations: the
`deltaTower` chain (`Op2`, `vstep`, `vtower`, …) and the `RicTowerDefs`/`RicTowerKit` chain
(`Op2`, `vstep`, `vtower`, `dvVal`, `deltaOf`, `SlotAddNoC`, …).  No module may import both, but
`ricTowerBound_fixed` needs the δ-tower bounds (available only in the `deltaTower` chain) and the
Ricci tower machinery.

This module therefore re-states, with **fresh names**, the handful of small declarations of the
`RicTowerKit` chain that the flip of `ricTowerBound_fixed` needs (`SlotAddNoC2`, `selTower2`,
`embSucc2`/`embCons2` with their elementary lemmas, `valOp_eq_of_CIndep2`, the third-slot
independence of the `baseRic` towers, and the *slot-additivity-free* change-of-connection identity
`step_flip_NoC2`).  It imports only `honestTower` and `Kit`, so it is compatible with **both**
chains.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Slot additivity without the third slot -/

/-- Additivity of an `Op3` in its direction slots and in its first two value slots, **on smooth
fields**, the third value slot being deliberately excluded.  (A copy of
`Work.Diff.EXT.ConnCov.SlotAddNoC` with a fresh name, so that both declaration chains can be used
in one file.) -/
def SlotAddNoC2 {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) : Prop :=
  (∀ (i : Fin k) (v : Fin k → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (W W' : Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (A B C : Work.Diff.EXT.ATower.TF (I := I) (M := M)),
    (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M W →
    Work.Diff.EXT.ATower.SmE I M W' → Work.Diff.EXT.ATower.SmE I M A →
    Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M C →
    τ (Function.update v i (W + W')) A B C = τ (Function.update v i W) A B C
      + τ (Function.update v i W') A B C) ∧
  (∀ (v : Fin k → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (A A' B C : Work.Diff.EXT.ATower.TF (I := I) (M := M)),
    (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M A →
    Work.Diff.EXT.ATower.SmE I M A' → Work.Diff.EXT.ATower.SmE I M B →
    Work.Diff.EXT.ATower.SmE I M C →
    τ v (A + A') B C = τ v A B C + τ v A' B C) ∧
  (∀ (v : Fin k → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (A B B' C : Work.Diff.EXT.ATower.TF (I := I) (M := M)),
    (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M A →
    Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
    Work.Diff.EXT.ATower.SmE I M C →
    τ v A (B + B') C = τ v A B C + τ v A B' C)

/-- **The change of connection without third-slot additivity**: if `τ` is additive in its direction
slots and in its first two value slots and is third-slot independent, then changing the connection
in one recursion step is the omission of the `C`-correction, i.e. only the `insD`/`insA`/`insB`
insertions appear. -/
theorem step_flip_NoC2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (hτ : SlotAddNoC2 τ) (hCind : CIndep τ)
    {cov cov' : CovariantDerivative I E (TangentSpace I (M := M))}
    (δ : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => cov Y y (Z y)))
    (hcov' : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => cov' Y y (Z y)))
    (hδsm : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (fun y => δ Y Z y))
    (hδ : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z → ∀ y : M, cov' Y y (Z y) = cov Y y (Z y) + δ Y Z y)
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B Cc : Π y : M, TangentSpace I y)
    (hv : ∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) (hA : Work.Diff.EXT.ATower.SmE I M A)
    (hB : Work.Diff.EXT.ATower.SmE I M B) (hCc : Work.Diff.EXT.ATower.SmE I M Cc) :
    Work.Diff.EXT.ATower.step cov τ v A B Cc = fun x =>
      Work.Diff.EXT.ATower.step cov' τ v A B Cc x
        + (∑ i : Fin k, Work.Diff.EXT.ATower.insD i δ τ v A B Cc x)
        + Work.Diff.EXT.ATower.insA δ τ v A B Cc x
        + Work.Diff.EXT.ATower.insB δ τ v A B Cc x := by
  funext x
  have hsum' : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => cov' (v i.succ) y (v 0 y))) A B Cc x)
      = (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => cov (v i.succ) y (v 0 y))) A B Cc x)
        + (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => δ (v i.succ) (v 0) y)) A B Cc x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      have hfield : (fun y : M => cov' (v i.succ) y (v 0 y))
          = (fun y : M => cov (v i.succ) y (v 0 y))
            + (fun y : M => δ (v i.succ) (v 0) y) := by
        funext y
        exact hδ (v i.succ) (v 0) (hv _) (hv 0) y
      rw [hfield]
      exact congrFun (hτ.1 i (fun j : Fin k => v j.succ) (fun y => cov (v i.succ) y (v 0 y))
        (fun y => δ (v i.succ) (v 0) y) A B Cc (fun j => hv j.succ)
        (hcov (v i.succ) (v 0) (hv _) (hv 0)) (hδsm (v i.succ) (v 0) (hv _) (hv 0)) hA hB hCc) x
  have hA' : τ (fun j : Fin k => v j.succ) (fun y => cov' A y (v 0 y)) B Cc x
      = τ (fun j : Fin k => v j.succ) (fun y => cov A y (v 0 y)) B Cc x
        + τ (fun j : Fin k => v j.succ) (fun y => δ A (v 0) y) B Cc x := by
    have hfield : (fun y : M => cov' A y (v 0 y))
        = (fun y : M => cov A y (v 0 y)) + (fun y : M => δ A (v 0) y) := by
      funext y
      exact hδ A (v 0) hA (hv 0) y
    rw [hfield]
    exact congrFun (hτ.2.1 (fun j : Fin k => v j.succ) (fun y => cov A y (v 0 y))
      (fun y => δ A (v 0) y) B Cc (fun j => hv j.succ) (hcov A (v 0) hA (hv 0))
      (hδsm A (v 0) hA (hv 0)) hB hCc) x
  have hB' : τ (fun j : Fin k => v j.succ) A (fun y => cov' B y (v 0 y)) Cc x
      = τ (fun j : Fin k => v j.succ) A (fun y => cov B y (v 0 y)) Cc x
        + τ (fun j : Fin k => v j.succ) A (fun y => δ B (v 0) y) Cc x := by
    have hfield : (fun y : M => cov' B y (v 0 y))
        = (fun y : M => cov B y (v 0 y)) + (fun y : M => δ B (v 0) y) := by
      funext y
      exact hδ B (v 0) hB (hv 0) y
    rw [hfield]
    exact congrFun (hτ.2.2 (fun j : Fin k => v j.succ) A (fun y => cov B y (v 0 y))
      (fun y => δ B (v 0) y) Cc (fun j => hv j.succ) hA (hcov B (v 0) hB (hv 0))
      (hδsm B (v 0) hB (hv 0)) hCc) x
  have hC' : τ (fun j : Fin k => v j.succ) A B (fun y => cov' Cc y (v 0 y)) x
      = τ (fun j : Fin k => v j.succ) A B (fun y => cov Cc y (v 0 y)) x :=
    hCind (fun j : Fin k => v j.succ) A B (fun y => cov' Cc y (v 0 y))
      (fun y => cov Cc y (v 0 y)) x
  simp only [Work.Diff.EXT.ATower.step, Work.Diff.EXT.ATower.insD, Work.Diff.EXT.ATower.insA,
    Work.Diff.EXT.ATower.insB]
  rw [hsum', hA', hB', hC']
  ring

/-! ## Third-slot independence at the value level -/

/-- For a third-slot-independent operator, the value `valOp τ x v a b c` does not depend on the
third argument vector `c`. -/
theorem valOp_eq_of_CIndep2 {k : ℕ} {τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k}
    (h : CIndep τ)
    (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    Work.Diff.EXT.ATower.valOp τ x v a b c
      = Work.Diff.EXT.ATower.valOp τ x v a b 0 := by
  simp only [Work.Diff.EXT.ATower.valOp]
  exact h _ _ _ _ _ _

/-- The honest tower of `baseRic` is third-slot independent. -/
theorem CIndep_htower_baseRic2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : SMet I M) (k : ℕ) : CIndep (htower cov (baseRic g) k) :=
  cIndep_htower cov (cIndep_baseRic g) k

/-- The (shifted) tower of `baseRic` is third-slot independent. -/
theorem CIndep_tower_baseRic2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : SMet I M) : ∀ k : ℕ, CIndep (Work.Diff.EXT.ATower.tower cov (baseRic g) k)
  | 0 => cIndep_baseRic g
  | k + 1 => cIndep_step cov (CIndep_tower_baseRic2 cov g k)

/-! ## A clash-free name for the pointwise scalar multiple of a tangent field

Delegated statements are elaborated in files with no `open` commands, where the fibre instances
(`SMul ℝ (TangentSpace I y)`) are not synthesised; the wrapper below lets such statements mention
`f • A` as `smulTF f A`. -/

/-- The pointwise scalar multiple `f • A` of a tangent field `A`. -/
noncomputable def smulTF (f : M → ℝ) (A : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun y => f y • A y

@[simp] theorem smulTF_apply (f : M → ℝ) (A : Π y : M, TangentSpace I y) (y : M) :
    smulTF f A y = f y • A y := rfl

/-! ## The selection-booking kit of the shift identity -/

/-- **The selection object of the shift expansion.**  For a map `f : Fin j → Fin m`,
`selTower2 cov base f` is the honest `j`-th tower `htower cov base j` evaluated on the sub-tuple
`v ∘ f`, regarded as an `Op3 m` (the `m - j` unused direction slots are ignored). -/
noncomputable def selTower2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) {m j : ℕ} (f : Fin j → Fin m) :
    Work.Diff.EXT.ATower.Op3 (I := I) (M := M) m :=
  fun v A B C x => htower cov base j (fun l : Fin j => v (f l)) A B C x

/-- `f^{+1}`: shift `f` up by one, as a map `Fin j → Fin (m+1)`. -/
def embSucc2 {m j : ℕ} (f : Fin j → Fin m) : Fin j → Fin (m+1) :=
  fun l => Fin.succ (f l)

/-- `f^{+0}`: insert `0` at the front of the shifted `f`, as a map `Fin (j+1) → Fin (m+1)`. -/
def embCons2 {m j : ℕ} (f : Fin j → Fin m) : Fin (j+1) → Fin (m+1) :=
  Fin.cons 0 (embSucc2 f)

@[simp] theorem embSucc2_apply {m j : ℕ} (f : Fin j → Fin m) (l : Fin j) :
    embSucc2 f l = Fin.succ (f l) := rfl

@[simp] theorem embCons2_zero {m j : ℕ} (f : Fin j → Fin m) : embCons2 f 0 = 0 := rfl

@[simp] theorem embCons2_succ {m j : ℕ} (f : Fin j → Fin m) (l : Fin j) :
    embCons2 f l.succ = Fin.succ (f l) := rfl

/-- `f^{+1}` is strictly monotone when `f` is. -/
theorem strictMono_embSucc2 {m j : ℕ} {f : Fin j → Fin m} (hf : StrictMono f) :
    StrictMono (embSucc2 f) := by
  intro a b hab
  exact Fin.succ_lt_succ_iff.mpr (hf hab)

/-- `f^{+0}` is strictly monotone when `f` is. -/
theorem strictMono_embCons2 {m j : ℕ} {f : Fin j → Fin m} (hf : StrictMono f) :
    StrictMono (embCons2 f) := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨a', rfl⟩
  · subst h
    rw [embCons2_zero]
    rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · subst hb; exact absurd hab (lt_irrefl _)
    · rw [embCons2_succ]; exact Fin.succ_pos _
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · subst hb; exact absurd hab (not_lt_of_ge (Fin.zero_le _))
    · rw [embCons2_succ, embCons2_succ]
      exact Fin.succ_lt_succ_iff.mpr (hf (Fin.succ_lt_succ_iff.mp hab))

/-- `embSucc2` is injective. -/
theorem embSucc2_injective {m j : ℕ} :
    Function.Injective (fun f : Fin j → Fin m => embSucc2 f) := by
  intro f f' h
  funext l
  have hl := congrFun h l
  simp only [embSucc2_apply] at hl
  exact Fin.succ_inj.mp hl

/-- `embCons2` is injective. -/
theorem embCons2_injective {m j : ℕ} :
    Function.Injective (fun f : Fin j → Fin m => embCons2 f) := by
  intro f f' h
  funext l
  have hl := congrFun h l.succ
  simp only [embCons2_succ] at hl
  exact Fin.succ_inj.mp hl

/-- **The `g 0 = 0` branch of the reindexing**: such a strictly monotone `g` is `embCons2` applied
to the predecessor of its tail. -/
theorem embCons2_predecessor {m j : ℕ} {g : Fin (j+1) → Fin (m+1)}
    (hg : StrictMono g) (h0 : g 0 = 0) :
    ∃ f : Fin j → Fin m, StrictMono f ∧ embCons2 f = g := by
  have hne : ∀ l : Fin j, g l.succ ≠ 0 := by
    intro l hc
    have hlt : g 0 < g l.succ := hg (Fin.succ_pos l)
    rw [h0, hc] at hlt
    exact absurd hlt (lt_irrefl 0)
  have hsucc : ∀ l : Fin j, (Fin.pred (g l.succ) (hne l)).succ = g l.succ := by
    intro l
    exact Fin.succ_pred _ _
  refine ⟨fun l => Fin.pred (g l.succ) (hne l), ?_, ?_⟩
  · intro a b hab
    exact Fin.pred_lt_pred_iff.mpr (hg (Fin.succ_lt_succ_iff.mpr hab))
  · funext s
    rcases Fin.eq_zero_or_eq_succ s with h | ⟨s', rfl⟩
    · rw [h, embCons2_zero, h0]
    · rw [embCons2_succ, hsucc]

/-- **The nonzero branch of the reindexing**: a strictly monotone `g` with `g 0 ≠ 0` is `embSucc2`
applied to a strictly monotone map into `Fin m`. -/
theorem embSucc2_surj {m j : ℕ} {g : Fin (j+1) → Fin (m+1)}
    (hg : StrictMono g) (h0 : g 0 ≠ 0) :
    ∃ f : Fin (j+1) → Fin m, StrictMono f ∧ embSucc2 f = g := by
  have hpos : ∀ l : Fin (j+1), g l ≠ 0 := by
    intro l hc
    have hle : g 0 ≤ g l := hg.monotone (Fin.zero_le l)
    rw [hc] at hle
    exact h0 (le_antisymm hle (Fin.zero_le _))
  refine ⟨fun l => Fin.pred (g l) (hpos l), ?_, ?_⟩
  · intro a b hab
    have h : (Fin.pred (g a) (hpos a)).succ < (Fin.pred (g b) (hpos b)).succ := by
      rw [Fin.succ_pred, Fin.succ_pred]
      exact hg hab
    exact Fin.succ_lt_succ_iff.mp h
  · funext s
    rw [embSucc2_apply]
    exact Fin.succ_pred _ _
