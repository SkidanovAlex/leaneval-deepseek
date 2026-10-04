import Mathlib
import Submission.Work.Diff.EXT.ConnCov.FlipKit
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.GE.ricAt_eq_sum_frame
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.ric_bound_of_curvBound
import Submission.Work.Diff.Evol.covDLC_B_identity
import Submission.Work.Diff.EXT.ConnCov.HonestTower.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tensoriality of the honest tower of `Ric`: the value at a point depends only on the values

`Work.Diff.EXT.ConnCov.htower (lcOf g) (baseRic g) j` is the `j`-th covariant derivative of the
Ricci tensor of `g`, as a field-level operator with `j` differentiation slots and three value slots
(the third one unused).  Since it is the iterated covariant derivative of a smooth `(0,2)`-tensor
field, its value at `x` depends only on the *values* of the slot fields at `x`.  That is the target
`Work.Diff.EXT.ConnCov.RicTr.htowerTensorialH`.

## Route

The packed form of the honest tower, `Work.Diff.EXT.ConnCov.HonestTower.gP g base k` (with the two
relevant value slots `A B` and the unused third slot set to `0`), satisfies, for a base which is
third-slot independent, smooth on smooth fields, `C^∞`-linear in the two value slots and
value-dependent, the value-dependence `HonestTower.gP_val_dep` in a *single* slot (obtained there
from the invariant `TensPropG`: smoothness, slotwise linearity and locality of `gP`).  The bridge
`gP_eq_htower_self` relates the packed tower to `htower`; then `gP_val_dep_all` chains the
single-slot statement over the `k + 2` slots (replace them one at a time, keeping the others fixed),
giving the full value-dependence.

The four facts about the base `baseRic g` are: smoothness
(`Work.Diff.Evol.covDLC_B_ricF_smooth`), `C^∞`-linearity in the two value slots
(`Work.Diff.EXT.ricAt_add_middle_L`/`ricAt_smul_middle_L` and their `last` variants) and
value-dependence (immediate from the definition).  The unused hypothesis `hcan` is not needed: the
cancellation of the `∇`-corrections is built into the honest recursion (`hstep`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.Diff.EXT.ConnCov.RicTr

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Elementary facts about `pack2` -/

/-- The first value slot of `pack2`. -/
lemma pack2_natAdd0 {k : ℕ} (v : Fin k → (Π y : M, TangentSpace I y))
    (A B : Π y : M, TangentSpace I y) :
    HonestTower.pack2 v A B (Fin.natAdd k (0 : Fin 2)) = A := by
  rw [HonestTower.pack2_natAdd, HonestTower.pairF_zero]

/-- The second value slot of `pack2`. -/
lemma pack2_natAdd1 {k : ℕ} (v : Fin k → (Π y : M, TangentSpace I y))
    (A B : Π y : M, TangentSpace I y) :
    HonestTower.pack2 v A B (Fin.natAdd k (1 : Fin 2)) = B := by
  rw [HonestTower.pack2_natAdd, HonestTower.pairF_one]

/-- The head slot of `pack2` for a nonempty direction tuple. -/
lemma pack2_head {k : ℕ} (v : Fin (k + 1) → (Π y : M, TangentSpace I y))
    (A B : Π y : M, TangentSpace I y) :
    HonestTower.pack2 v A B (0 : Fin (k + 3)) = v 0 :=
  HonestTower.pack2_castAdd v A B (0 : Fin (k + 1))

/-! ## The bridge: the packed honest tower is the honest tower -/

/-- **The bridge**: the packed honest tower (with the unused third value slot set to `0`) is the
honest tower of a third-slot independent base.  This is the statement of
`Work.Diff.EXT.ConnCov.HonestTower.gP_eq_htower`; it is re-proved here (the colleague's module
`HonestTower.Bridge` does not currently compile) so that this file only depends on the compiling
part of the `HonestTower` development. -/
theorem gP_eq_htower_self
    (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (hbaseC : CIndep base) :
    ∀ (k : ℕ) (v : Fin k → (Π y : M, TangentSpace I y))
      (A B : Π y : M, TangentSpace I y) (y : M),
      HonestTower.gP g base k (HonestTower.pack2 v A B) y
        = htower (Submission.Diff.lcOf g) base k v A B
            (0 : Π y : M, TangentSpace I y) y := by
  intro k
  induction k with
  | zero =>
      intro v A B y
      have hv : v = fun i : Fin 0 => i.elim0 := by funext i; exact i.elim0
      rw [hv, htower_zero, HonestTower.gP_zero_apply]
      have h0 : HonestTower.pack2 (fun i : Fin 0 => i.elim0) A B (0 : Fin 2) = A :=
        pack2_natAdd0 (fun i : Fin 0 => i.elim0) A B
      have h1 : HonestTower.pack2 (fun i : Fin 0 => i.elim0) A B (1 : Fin 2) = B :=
        pack2_natAdd1 (fun i : Fin 0 => i.elim0) A B
      rw [h0, h1]
  | succ k ih =>
      intro v A B y
      -- ## the honest recursion
      have hR : htower (Submission.Diff.lcOf g) base (k + 1) v A B
            (0 : Π y : M, TangentSpace I y) y
          = mvfderiv I (htower (Submission.Diff.lcOf g) base k
                (fun i : Fin k => v i.succ) A B (0 : Π y : M, TangentSpace I y)) y (v 0 y)
            - (∑ i : Fin k, htower (Submission.Diff.lcOf g) base k
                (Function.update (fun j : Fin k => v j.succ) i
                  (fun z => (Submission.Diff.lcOf g) (v i.succ) z (v 0 z))) A B
                (0 : Π y : M, TangentSpace I y) y)
            - htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ)
                (fun z => (Submission.Diff.lcOf g) A z (v 0 z)) B
                (0 : Π y : M, TangentSpace I y) y
            - htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ) A
                (fun z => (Submission.Diff.lcOf g) B z (v 0 z))
                (0 : Π y : M, TangentSpace I y) y := by
        rw [show htower (Submission.Diff.lcOf g) base (k + 1) v A B
              (0 : Π y : M, TangentSpace I y)
            = hstep (Submission.Diff.lcOf g) (htower (Submission.Diff.lcOf g) base k) v A B
              (0 : Π y : M, TangentSpace I y) from rfl]
        exact hstep_apply (Submission.Diff.lcOf g)
          (cIndep_htower (Submission.Diff.lcOf g) (base := base) hbaseC k) v A B
          (0 : Π y : M, TangentSpace I y) y
      -- ## the packed recursion: the sum
      have hsum : (∑ s : Fin (k + 2), HonestTower.gP g base k
            (Function.update (fun i : Fin (k + 2) => HonestTower.pack2 v A B i.succ) s
              (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => HonestTower.pack2 v A B i.succ) s)
                (HonestTower.pack2 v A B (0 : Fin (k + 3))))) y)
          = (∑ i : Fin k, HonestTower.gP g base k (HonestTower.pack2
                (Function.update (fun j : Fin k => v j.succ) i
                  (fun z => (Submission.Diff.lcOf g) (v i.succ) z (v 0 z))) A B) y)
            + (HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ)
                  (fun z => (Submission.Diff.lcOf g) A z (v 0 z)) B) y
              + HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ) A
                  (fun z => (Submission.Diff.lcOf g) B z (v 0 z))) y) := by
        rw [HonestTower.pack2_comp_succ]
        rw [Fin.sum_univ_add, Fin.sum_univ_two]
        congr 1
        · refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [HonestTower.pack2_castAdd, pack2_head, HonestTower.update_castAdd_pack2]
          rfl
        · congr 1
          · rw [HonestTower.pack2_natAdd, HonestTower.pairF_zero, pack2_head,
              HonestTower.update_natAdd_pack2, if_pos (rfl : (0 : Fin 2) = 0),
              if_neg (by decide : ¬ ((0 : Fin 2) = 1))]
            rfl
          · rw [HonestTower.pack2_natAdd, HonestTower.pairF_one, pack2_head,
              HonestTower.update_natAdd_pack2, if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
              if_pos (rfl : (1 : Fin 2) = 1)]
            rfl
      -- ## the packed recursion
      have hL : HonestTower.gP g base (k + 1) (HonestTower.pack2 v A B) y
          = mvfderiv I (HonestTower.gP g base k
                (HonestTower.pack2 (fun i : Fin k => v i.succ) A B)) y (v 0 y)
            - (∑ i : Fin k, HonestTower.gP g base k (HonestTower.pack2
                  (Function.update (fun j : Fin k => v j.succ) i
                    (fun z => (Submission.Diff.lcOf g) (v i.succ) z (v 0 z))) A B) y)
            - HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ)
                (fun z => (Submission.Diff.lcOf g) A z (v 0 z)) B) y
            - HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ) A
                (fun z => (Submission.Diff.lcOf g) B z (v 0 z))) y := by
        rw [HonestTower.gP_succ]
        simp only [Pi.sub_apply, Finset.sum_apply]
        rw [hsum, HonestTower.pack2_comp_succ, pack2_head]
        ring
      rw [hL, hR]
      have ihfun : HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ) A B)
          = fun z : M => htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ) A B
              (0 : Π y : M, TangentSpace I y) z :=
        funext fun z => ih (fun i : Fin k => v i.succ) A B z
      have hX : mvfderiv I (HonestTower.gP g base k
            (HonestTower.pack2 (fun i : Fin k => v i.succ) A B)) y (v 0 y)
          = mvfderiv I (htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ) A B
              (0 : Π y : M, TangentSpace I y)) y (v 0 y) :=
        congrArg (fun F : M → ℝ => mvfderiv I F y (v 0 y)) ihfun
      have hS : (∑ i : Fin k, HonestTower.gP g base k (HonestTower.pack2
            (Function.update (fun j : Fin k => v j.succ) i
              (fun z => (Submission.Diff.lcOf g) (v i.succ) z (v 0 z))) A B) y)
          = (∑ i : Fin k, htower (Submission.Diff.lcOf g) base k
              (Function.update (fun j : Fin k => v j.succ) i
                (fun z => (Submission.Diff.lcOf g) (v i.succ) z (v 0 z))) A B
              (0 : Π y : M, TangentSpace I y) y) :=
        Finset.sum_congr rfl (fun i _ => ih _ A B y)
      have hAeq : HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ)
            (fun z => (Submission.Diff.lcOf g) A z (v 0 z)) B) y
          = htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ)
              (fun z => (Submission.Diff.lcOf g) A z (v 0 z)) B
              (0 : Π y : M, TangentSpace I y) y :=
        ih _ _ _ y
      have hBeq : HonestTower.gP g base k (HonestTower.pack2 (fun i : Fin k => v i.succ) A
            (fun z => (Submission.Diff.lcOf g) B z (v 0 z))) y
          = htower (Submission.Diff.lcOf g) base k (fun i : Fin k => v i.succ) A
              (fun z => (Submission.Diff.lcOf g) B z (v 0 z))
              (0 : Π y : M, TangentSpace I y) y :=
        ih _ _ _ y
      first
        | linarith [hX, hS, hAeq, hBeq]
        | (simp only [hX, hS, hAeq, hBeq]; ring)

/-! ## Chaining the single-slot value dependence -/

/-- **Value dependence of the packed honest tower, slot by slot.**  If, for every tuple of smooth
fields and every slot, replacing the field in that slot by another smooth field with the same value
at `x` does not change the value of `gP g base k` at `x`, then the same holds for *all* slots at
once (replace them one after the other, keeping the hybrid tuple in a `Finset`). -/
theorem gP_val_dep_all
    (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ) (x : M)
    (hstep : ∀ (FS : Fin (k + 2) → (Π y : M, TangentSpace I y)) (s : Fin (k + 2))
      (X X' : Π y : M, TangentSpace I y),
      (∀ q, HonestTower.Sm (I := I) (M := M) (FS q)) →
      HonestTower.Sm (I := I) (M := M) X → HonestTower.Sm (I := I) (M := M) X' → X x = X' x →
      HonestTower.gP g base k (Function.update FS s X) x
        = HonestTower.gP g base k (Function.update FS s X') x)
    (F F' : Fin (k + 2) → (Π y : M, TangentSpace I y))
    (hF : ∀ s, HonestTower.Sm (I := I) (M := M) (F s))
    (hF' : ∀ s, HonestTower.Sm (I := I) (M := M) (F' s))
    (h : ∀ s, F s x = F' s x) :
    HonestTower.gP g base k F x = HonestTower.gP g base k F' x := by
  classical
  -- the hybrid tuple: the slots in `t` are taken from `F'`, the others from `F`
  set H : Finset (Fin (k + 2)) → (Fin (k + 2) → (Π y : M, TangentSpace I y)) :=
    fun t s => if s ∈ t then F' s else F s with hHdef
  have hH : ∀ t s, HonestTower.Sm (I := I) (M := M) (H t s) := by
    intro t s
    rw [hHdef]
    by_cases hs : s ∈ t
    · simp only [if_pos hs]
      exact hF' s
    · simp only [if_neg hs]
      exact hF s
  have hHself : ∀ t s, s ∉ t → H t s = F s := by
    intro t s hs
    rw [hHdef]
    simp only [if_neg hs]
  -- replacing one more slot of the hybrid tuple does not change the value at `x`
  have hstep' : ∀ (t : Finset (Fin (k + 2))) (s : Fin (k + 2)), s ∉ t →
      HonestTower.gP g base k (H t) x = HonestTower.gP g base k (H (insert s t)) x := by
    intro t s hs
    have hupd : H (insert s t) = Function.update (H t) s (F' s) := by
      funext u
      simp only [hHdef, Function.update_apply]
      by_cases hu : u = s
      · subst hu; simp
      · rw [if_neg hu]
        simp only [Finset.mem_insert, hu, false_or]
    rw [hupd]
    have hsd := hstep (H t) s (F s) (F' s) (hH t) (hF s) (hF' s) (h s)
    have hsame : Function.update (H t) s (F s) = H t := by
      funext u
      by_cases hu : u = s
      · rw [hu, Function.update_self, hHself t s hs]
      · rw [Function.update_of_ne hu]
    rwa [hsame] at hsd
  have hchain : HonestTower.gP g base k (H ∅) x = HonestTower.gP g base k (H Finset.univ) x :=
    Finset.induction_on (motive := fun t =>
        HonestTower.gP g base k (H ∅) x = HonestTower.gP g base k (H t) x)
      (Finset.univ : Finset (Fin (k + 2))) rfl
      (fun a t ha ih => by rw [ih, hstep' t a ha])
  have h0 : H ∅ = F := by funext s; simp [hHdef]
  have h1 : H Finset.univ = F' := by funext s; simp [hHdef]
  rwa [h0, h1] at hchain

theorem htowerTensorialH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hcan : ∀ (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
      (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
      (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M v0 →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      (∀ m, Work.Diff.EXT.ATower.SmE I M (W m)) →
      (∀ᶠ y in nhds x, Submission.Diff.IsONFrame g y (fun m => W m y)) →
      (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
        + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0)
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (j : ℕ)
    (v v' : Fin j → (Π y : M, TangentSpace I y))
    (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i))
    (hv' : ∀ i, Work.Diff.EXT.ATower.SmE I M (v' i))
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hA' : Work.Diff.EXT.ATower.SmE I M A')
    (hB : Work.Diff.EXT.ATower.SmE I M B) (hB' : Work.Diff.EXT.ATower.SmE I M B')
    (hC : Work.Diff.EXT.ATower.SmE I M C) (hC' : Work.Diff.EXT.ATower.SmE I M C')
    (hvx : ∀ i, v i x = v' i x) (hAx : A x = A' x) (hBx : B x = B' x) (hCx : C x = C' x) :
    Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j v A B C x
      = Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j v' A' B' C' x := by
  have hcov : (Submission.Diff.lcOf g).ContMDiffCovariantDerivative (⊤ : ℕ∞) := (hLC g).1.some
  -- ## the four facts about the base `baseRic g`
  have hsm : ∀ (v0 : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C →
      Work.Diff.EXT.ATower.SmF I M
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v0 A B C) := by
    intro v0 A B C hA hB hC
    have hric : Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g v0 A B C
        = Work.Diff.Evol.ricF g A B := rfl
    rw [hric]
    exact Work.Diff.Evol.covDLC_B_ricF_smooth hLC g A B hA hB
  have hlinA : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (B C : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 X₁ B C x
          + f₂ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 X₂ B C x := by
    intro b0 X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ B C x
    have hpt : (f₁ • X₁ + f₂ • X₂) x = f₁ x • X₁ x + f₂ x • X₂ x := by simp
    simp only [Work.Diff.EXT.ConnCov.baseRic]
    rw [hpt, Work.Diff.EXT.ricAt_add_middle_L g hcov x (f₁ x • X₁ x) (f₂ x • X₂ x) (B x),
      Work.Diff.EXT.ricAt_smul_middle_L g hcov x (f₁ x) (X₁ x) (B x),
      Work.Diff.EXT.ricAt_smul_middle_L g hcov x (f₂ x) (X₂ x) (B x)]
  have hlinB : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A C : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 A X₁ C x
          + f₂ x * Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 A X₂ C x := by
    intro b0 X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂ A C x
    have hpt : (f₁ • X₁ + f₂ • X₂) x = f₁ x • X₁ x + f₂ x • X₂ x := by simp
    simp only [Work.Diff.EXT.ConnCov.baseRic]
    rw [hpt, Work.Diff.EXT.ricAt_add_last_L g hcov x (A x) (f₁ x • X₁ x) (f₂ x • X₂ x),
      Work.Diff.EXT.ricAt_smul_last_L g hcov x (f₁ x) (A x) (X₁ x),
      Work.Diff.EXT.ricAt_smul_last_L g hcov x (f₂ x) (A x) (X₂ x)]
  have hvd : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 A B C x
        = Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g b0 A' B' C' x := by
    intro b0 A A' B B' C C' x _ _ _ _ _ _ hAx hBx _
    simp only [Work.Diff.EXT.ConnCov.baseRic, hAx, hBx]
  -- ## single-slot value dependence of the packed honest tower of `baseRic g`
  have hstep : ∀ (FS : Fin (j + 2) → (Π y : M, TangentSpace I y)) (s : Fin (j + 2))
      (X X' : Π y : M, TangentSpace I y),
      (∀ q, HonestTower.Sm (I := I) (M := M) (FS q)) →
      HonestTower.Sm (I := I) (M := M) X → HonestTower.Sm (I := I) (M := M) X' → X x = X' x →
      HonestTower.gP g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j
        (Function.update FS s X) x
        = HonestTower.gP g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j
          (Function.update FS s X') x :=
    fun FS s X X' hFS hX hX' hxx =>
      HonestTower.gP_val_dep (I := I) (M := M) hLC g hsm hlinA hlinB hvd j x
        hFS s hX hX' hxx
  -- ## the slotwise value equality for the two packed tuples
  have hslot : ∀ s : Fin (j + 2),
      HonestTower.pack2 v A B s x = HonestTower.pack2 v' A' B' s x := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [HonestTower.pack2_castAdd, HonestTower.pack2_castAdd]
      exact hvx i
    · intro p
      fin_cases p
      · rw [HonestTower.pack2_natAdd, HonestTower.pack2_natAdd]
        simpa using hAx
      · rw [HonestTower.pack2_natAdd, HonestTower.pack2_natAdd]
        simpa using hBx
  have hsmF : ∀ s : Fin (j + 2),
      HonestTower.Sm (I := I) (M := M) (HonestTower.pack2 v A B s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [HonestTower.pack2_castAdd]
      exact hv i
    · intro p
      fin_cases p
      · rw [HonestTower.pack2_natAdd]
        exact hA
      · rw [HonestTower.pack2_natAdd]
        exact hB
  have hsmF' : ∀ s : Fin (j + 2),
      HonestTower.Sm (I := I) (M := M) (HonestTower.pack2 v' A' B' s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [HonestTower.pack2_castAdd]
      exact hv' i
    · intro p
      fin_cases p
      · rw [HonestTower.pack2_natAdd]
        exact hA'
      · rw [HonestTower.pack2_natAdd]
        exact hB'
  -- ## the third value slot is unused
  have hCI : CIndep (htower (Submission.Diff.lcOf g)
      (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j) :=
    cIndep_htower (Submission.Diff.lcOf g)
      (base := Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g)
      (cIndep_baseRic (I := I) (M := M) g) j
  rw [hCI v A B C (0 : Π y : M, TangentSpace I y) x,
    hCI v' A' B' C' (0 : Π y : M, TangentSpace I y) x]
  -- ## pass to the packed tower
  have e1 : htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j v A B
        (0 : Π y : M, TangentSpace I y) x
      = HonestTower.gP g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j
        (HonestTower.pack2 v A B) x :=
    (gP_eq_htower_self (I := I) (M := M) g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g)
      (cIndep_baseRic (I := I) (M := M) g) j v A B x).symm
  have e2 : htower (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j v' A' B'
        (0 : Π y : M, TangentSpace I y) x
      = HonestTower.gP g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j
        (HonestTower.pack2 v' A' B') x :=
    (gP_eq_htower_self (I := I) (M := M) g (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g)
      (cIndep_baseRic (I := I) (M := M) g) j v' A' B' x).symm
  rw [e1, e2]
  exact gP_val_dep_all (I := I) (M := M) g
    (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) j x hstep
    (HonestTower.pack2 v A B) (HonestTower.pack2 v' A' B') hsmF hsmF' hslot

end Work.Diff.EXT.ConnCov.RicTr
