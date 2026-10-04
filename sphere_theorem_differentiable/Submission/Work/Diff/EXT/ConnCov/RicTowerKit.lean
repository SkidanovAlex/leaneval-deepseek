import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.ConnCov.aOf_hasDerivAt
import Submission.Work.Diff.EXT.ConnCov.dtMet
import Submission.Work.Diff.EXT.ATower.step_flip
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
import Submission.Work.Diff.EXT.ATower.KaLinD_holds
import Submission.Work.Diff.EXT.conn_diff_bound_of_shibounds
import Submission.Work.Diff.EXT.covKAExt_tensorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- Vector-valued operators with `k` derivative slots and two section slots (the shape of the
iterated covariant derivatives `∇^{cov,k}δ` of a `(1,2)`-tensor `δ`). -/
abbrev VOpM (k : ℕ) : Type _ := (Fin k → Work.Diff.EXT.ATower.TF (I := I) (M := M)) →
  Work.Diff.EXT.ATower.TF (I := I) (M := M) → Work.Diff.EXT.ATower.TF (I := I) (M := M) →
    Work.Diff.EXT.ATower.TF (I := I) (M := M)

/-- **The norm of the value of a vector-valued `(1,2+c)`-tensor** (a `VOpM c`), evaluated on the
`smoothExt` extensions of `c` direction vectors and two section vectors, measured in a metric `g`.
This is the value functional for the connection-difference towers `∇^{cov,c}δ`. -/
noncomputable def dvVal (g : SMet I M) {c : ℕ}
    (Θ : VOpM (I := I) (M := M) c) (x : M)
    (v : Fin c → TangentSpace I x) (X Y : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x
    (Θ (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x X)
      (Submission.Diff.smoothExt x Y) x)
    (Θ (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x X)
      (Submission.Diff.smoothExt x Y) x))

/-- The connection-difference `(1,2)`-tensor of two metrics. -/
noncomputable def deltaOf (g₀ g₁ : SMet I M) :
    Work.Diff.EXT.ATower.TF (I := I) (M := M) → Work.Diff.EXT.ATower.TF (I := I) (M := M) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M) :=
  fun X Y y => (lcOf g₁) X y (Y y) - (lcOf g₀) X y (Y y)

/-- The covariant-derivative recursion for a vector-valued `(1,2)`-tensor (`VOpM`), with the
connection of `g`: the value slot gets the covariant derivative along `v 0`, the two section slots
their connection corrections. -/
noncomputable def vstep (g : SMet I M) {k : ℕ} (τ : VOpM (I := I) (M := M) k) :
    VOpM (I := I) (M := M) (k + 1) :=
  fun v X Y x =>
    (lcOf g) (τ (fun i : Fin k => v i.succ) X Y) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => (lcOf g) (v i.succ) y (v 0 y))) X Y x
      - τ (fun i : Fin k => v i.succ) (fun y => (lcOf g) X y (v 0 y)) Y x
      - τ (fun i : Fin k => v i.succ) X (fun y => (lcOf g) Y y (v 0 y)) x

/-- The iterated covariant derivatives of a vector-valued `(1,2)`-tensor. -/
noncomputable def vtower (g : SMet I M) (base : VOpM (I := I) (M := M) 0) :
    ∀ k : ℕ, VOpM (I := I) (M := M) k
  | 0 => base
  | k + 1 => vstep g (vtower g base k)

/-! ## The structural hypotheses on `baseRic` needed for the assembly

`towerBound_of_htowerBound` (delegated) requires of its base: third-slot independence (`CIndep`),
smoothness on smooth fields, smooth-coefficient linearity in the first two value slots, and
value-dependence.  For `baseRic (G t)` these are collected here, so that the final instantiation is
pure plumbing. -/

section BaseRicFacts

variable {g : SMet I M} [T2Space M]

/-- `baseRic` is independent of its third value slot. -/
theorem baseRic_cind (g : SMet I M) : CIndep (Work.Diff.EXT.ConnCov.baseRic g) :=
  cIndep_baseRic g

/-- Smooth-coefficient linearity of `baseRic` in its first value slot. -/
theorem baseRic_linA (hcov : (lcOf g).ContMDiffCovariantDerivative ∞)
    (v : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (A₁ A₂ : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (f₁ f₂ : M → ℝ)
    (B C : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.baseRic g v (f₁ • A₁ + f₂ • A₂) B C x
      = f₁ x * Work.Diff.EXT.ConnCov.baseRic g v A₁ B C x
        + f₂ x * Work.Diff.EXT.ConnCov.baseRic g v A₂ B C x := by
  have hpt : (f₁ • A₁ + f₂ • A₂) x = f₁ x • A₁ x + f₂ x • A₂ x := by simp
  simp only [Work.Diff.EXT.ConnCov.baseRic]
  rw [hpt, Work.Diff.EXT.ricAt_add_middle_L g hcov x (f₁ x • A₁ x) (f₂ x • A₂ x) (B x),
    Work.Diff.EXT.ricAt_smul_middle_L g hcov x (f₁ x) (A₁ x) (B x),
    Work.Diff.EXT.ricAt_smul_middle_L g hcov x (f₂ x) (A₂ x) (B x)]

/-- Smooth-coefficient linearity of `baseRic` in its second value slot. -/
theorem baseRic_linB (hcov : (lcOf g).ContMDiffCovariantDerivative ∞)
    (v : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (B₁ B₂ : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (f₁ f₂ : M → ℝ)
    (A C : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.baseRic g v A (f₁ • B₁ + f₂ • B₂) C x
      = f₁ x * Work.Diff.EXT.ConnCov.baseRic g v A B₁ C x
        + f₂ x * Work.Diff.EXT.ConnCov.baseRic g v A B₂ C x := by
  have hpt : (f₁ • B₁ + f₂ • B₂) x = f₁ x • B₁ x + f₂ x • B₂ x := by simp
  simp only [Work.Diff.EXT.ConnCov.baseRic]
  rw [hpt, Work.Diff.EXT.ricAt_add_last_L g hcov x (A x) (f₁ x • B₁ x) (f₂ x • B₂ x),
    Work.Diff.EXT.ricAt_smul_last_L g hcov x (f₁ x) (A x) (B₁ x),
    Work.Diff.EXT.ricAt_smul_last_L g hcov x (f₂ x) (A x) (B₂ x)]

/-- Value-dependence of `baseRic` in its value slots. -/
theorem baseRic_vd
    (v : Fin 0 → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (A A' B B' C C' : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M)
    (hA : A x = A' x) (hB : B x = B' x) :
    Work.Diff.EXT.ConnCov.baseRic g v A B C x
      = Work.Diff.EXT.ConnCov.baseRic g v A' B' C' x := by
  simp only [Work.Diff.EXT.ConnCov.baseRic, hA, hB]

end BaseRicFacts

/-- Additivity of an `Op3` in its direction slots and in its first two value slots, **on smooth
fields**.  The third value slot is deliberately excluded: for a `CIndep` base the honest recursion
cancels the corresponding constant (`hstep = step + drop`), so the third slot is *not* additive,
while the tower is. -/
def SlotAddNoC {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) : Prop :=
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

/-- **The selection object of the shift expansion.**  For a map `f : Fin j → Fin m`,
`selTower cov base f` is the honest `j`-th tower `htower cov base j` evaluated on the sub-tuple
`v ∘ f`, regarded as an `Op3 m` (the `m - j` unused direction slots are ignored).  The shift
identity says that `tower cov base m` is a signed sum of these, one term per strictly monotone
selection `f`, with coefficient `(-1)^(m+j) * (m-j)!`. -/
noncomputable def selTower (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) {m j : ℕ} (f : Fin j → Fin m) :
    Work.Diff.EXT.ATower.Op3 (I := I) (M := M) m :=
  fun v A B C x =>
    Work.Diff.EXT.ConnCov.htower cov base j (fun l : Fin j => v (f l)) A B C x

/-- The `√`-norm product appearing in the honest-tower bounds: one factor per direction slot and
one per value slot (no third-slot factor: the honest towers ignore it). -/
noncomputable def sqrtProd (g : SMet I M) (x : M) {m : ℕ} (v : Fin m → TangentSpace I x)
    (A B : TangentSpace I x) : ℝ :=
  Finset.univ.prod (fun i : Fin m => Real.sqrt (g.inner x (v i) (v i)))
    * Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)

/-- The `(1 + √)`-norm product of the *shifted*-tower bound: the extra `1` is what absorbs the sum
over the direction-selections of the shift identity. -/
noncomputable def oneAddSqrtProd (g : SMet I M) (x : M) {m : ℕ}
    (v : Fin m → TangentSpace I x) : ℝ :=
  Finset.univ.prod (fun i : Fin m => (1 + Real.sqrt (g.inner x (v i) (v i))))

/-- `f^{+1}`: shift `f` up by one (`f^{+1} l = f l + 1`), as a map `Fin j → Fin (m+1)`. -/
def embSucc {m j : ℕ} (f : Fin j → Fin m) : Fin j → Fin (m+1) :=
  fun l => Fin.succ (f l)

/-- `f^{+0}`: insert `0` at the front of the shifted `f` (`f^{+0} 0 = 0`, `f^{+0} (l+1) = f l + 1`),
as a map `Fin (j+1) → Fin (m+1)`. -/
def embCons {m j : ℕ} (f : Fin j → Fin m) : Fin (j+1) → Fin (m+1) :=
  Fin.cons 0 (embSucc f)

@[simp] theorem embSucc_apply {m j : ℕ} (f : Fin j → Fin m) (l : Fin j) :
    embSucc f l = Fin.succ (f l) := rfl

@[simp] theorem embCons_zero {m j : ℕ} (f : Fin j → Fin m) : embCons f 0 = 0 := rfl

@[simp] theorem embCons_succ {m j : ℕ} (f : Fin j → Fin m) (l : Fin j) :
    embCons f l.succ = Fin.succ (f l) := rfl

/-- `f^{+1}` is strictly monotone when `f` is. -/
theorem strictMono_embSucc {m j : ℕ} {f : Fin j → Fin m} (hf : StrictMono f) :
    StrictMono (embSucc f) := by
  intro a b hab
  exact Fin.succ_lt_succ_iff.mpr (hf hab)

/-- `f^{+0}` is strictly monotone when `f` is. -/
theorem strictMono_embCons {m j : ℕ} {f : Fin j → Fin m} (hf : StrictMono f) :
    StrictMono (embCons f) := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨a', rfl⟩
  · subst h
    rw [embCons_zero]
    rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · subst hb; exact absurd hab (lt_irrefl _)
    · rw [embCons_succ]; exact Fin.succ_pos _
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨b', rfl⟩
    · subst hb; exact absurd hab (not_lt_of_ge (Fin.zero_le _))
    · rw [embCons_succ, embCons_succ]
      exact Fin.succ_lt_succ_iff.mpr (hf (Fin.succ_lt_succ_iff.mp hab))


/-- `embSucc` is injective (immediate from `Fin.succ_inj`). -/
theorem embSucc_injective {m j : ℕ} :
    Function.Injective (fun f : Fin j → Fin m => embSucc f) := by
  intro f f' h
  funext l
  have hl := congrFun h l
  simp only [embSucc_apply] at hl
  exact Fin.succ_inj.mp hl

/-- `embCons` is injective (immediate from `Fin.succ_inj`, read at the successors). -/
theorem embCons_injective {m j : ℕ} :
    Function.Injective (fun f : Fin j → Fin m => embCons f) := by
  intro f f' h
  funext l
  have hl := congrFun h l.succ
  simp only [embCons_succ] at hl
  exact Fin.succ_inj.mp hl


/-- **The `g 0 = 0` branch of the reindexing**: such a `g` is `embCons` applied to the predecessor
of its tail. -/
theorem embCons_predecessor {m j : ℕ} {g : Fin (j+1) → Fin (m+1)}
    (hg : StrictMono g) (h0 : g 0 = 0) :
    ∃ f : Fin j → Fin m, StrictMono f ∧ embCons f = g := by
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
    · rw [h, embCons_zero, h0]
    · rw [embCons_succ, hsucc]


/-! ## Consequences of third-slot independence at the value level -/

/-- For a third-slot-independent operator, the value `valOp τ x v a b c` does not depend on the
third argument vector `c`. -/
theorem valOp_eq_of_CIndep {k : ℕ} {τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k}
    (h : CIndep τ)
    (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    Work.Diff.EXT.ATower.valOp τ x v a b c
      = Work.Diff.EXT.ATower.valOp τ x v a b 0 := by
  simp only [Work.Diff.EXT.ATower.valOp]
  exact h _ _ _ _ _ _

/-- The honest tower of `baseRic` is third-slot independent. -/
theorem CIndep_htower_baseRic (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : SMet I M) (k : ℕ) : CIndep (htower cov (baseRic g) k) :=
  cIndep_htower cov (cIndep_baseRic g) k

/-- The (shifted) tower of `baseRic` is third-slot independent. -/
theorem CIndep_tower_baseRic' (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : SMet I M) : ∀ k : ℕ, CIndep (Work.Diff.EXT.ATower.tower cov (baseRic g) k)
  | 0 => cIndep_baseRic g
  | k + 1 => cIndep_step cov (CIndep_tower_baseRic' cov g k)

end Work.Diff.EXT.ConnCov
