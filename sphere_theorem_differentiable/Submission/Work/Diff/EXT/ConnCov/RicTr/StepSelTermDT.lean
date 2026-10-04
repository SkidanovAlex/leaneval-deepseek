import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxKernel
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTowerSm
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVStep
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVKit

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step rule of the Leibniz expansion (the `RicTr`/`DT` version)

`Work.Diff.EXT.ConnCov.RicTr.StepSelTermDT` is the `DT`-counterpart of the one-step rule
`Work.Diff.EXT.ConnCov.DTB.step_pairOp`: one recursion step of the twisted pairing
`Work.Diff.EXT.ConnCov.DT.selTerm G t c i j F G'` (`∇^{g_0,i}g_t` paired with `∇^{g_0,j}δ`) is the
sum of the two terms in which the new direction `v 0` is given to the metric factor (`gstep`, the
metric-tower recursion, with the selections `FTen F`/`Gshift G'`) or to the δ-factor (`vstep`, the
δ-tower recursion, with the selections `Fshift F`/`GTen G'`).

The identity is *not* a definitional property of the recursion: the correction terms in the value
slots of `step` see the field `∇_{V₀}(δ-tower value)`, into which the second term's `vstep` splits;
the two cancel only because the metric tower is *additive* in that slot (`hadd`), which is why the
statement is conditional on `hadd`.  On non-smooth fields the identity genuinely fails (the
recursion uses `mvfderiv`, the junk value `0` where the function is not differentiable), which is
why every field below is assumed `C^∞` (`SmE`).

## Contents

* bookkeeping of `Function.update` under the two selections (`upd_FF`, `upd_FG`, `upd_GF`,
  `upd_GG`), of the `Fin.cons`-shift (`cons_FTen`, `cons_GTen`) and the reindexing of a sum over
  `Fin c` by the two selections (`sum_fin_reindex`);
* `StepSelTermDT` — the one-step rule.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ConnCov.RicTr

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

lemma cons_FTen {i c : ℕ} (v : Fin (c+1) → TF (I := I) (M := M)) (F : Fin i → Fin c) :
    (fun k : Fin (i+1) => v (Work.Diff.EXT.ConnCov.DT.FTen F k))
      = Fin.cons (v 0) (fun a : Fin i => v (F a).succ) := by
  funext k
  induction k using Fin.cases with
  | zero => rfl
  | succ a => rfl

lemma fshift_eq {i c : ℕ} (v : Fin (c+1) → TF (I := I) (M := M)) (F : Fin i → Fin c) :
    (fun k : Fin i => v (Work.Diff.EXT.ConnCov.DT.Fshift F k)) = fun a : Fin i => v (F a).succ :=
  rfl

lemma gshift_eq {j c : ℕ} (v : Fin (c+1) → TF (I := I) (M := M)) (G' : Fin j → Fin c) :
    (fun k : Fin j => v (Work.Diff.EXT.ConnCov.DT.Gshift G' k))
      = fun b : Fin j => v (G' b).succ :=
  rfl

lemma cons_GTen {j c : ℕ} (v : Fin (c+1) → TF (I := I) (M := M)) (G' : Fin j → Fin c) :
    (fun k : Fin (j+1) => v (Work.Diff.EXT.ConnCov.DT.GTen G' k))
      = Fin.cons (v 0) (fun b : Fin j => v (G' b).succ) := by
  funext k
  induction k using Fin.cases with
  | zero => rfl
  | succ b => rfl

/-- Bookkeeping of `Function.update` at a slot of the `F`-selection: the update acts on the
`F`-indexed tuple of direction fields as the corresponding update. -/
lemma upd_FF {i c : ℕ} {F : Fin i → Fin c} (hf : Function.Injective F)
    (w : Fin c → TF (I := I) (M := M)) (X : TF (I := I) (M := M)) (a : Fin i) :
    (fun k : Fin i => Function.update w (F a) X (F k))
      = Function.update (fun a' : Fin i => w (F a')) a X := by
  funext k
  by_cases h : k = a
  · subst h; simp
  · rw [Function.update_of_ne (show F k ≠ F a from fun hc => h (hf hc)) X w,
      Function.update_of_ne h X (fun a' => w (F a'))]

/-- Bookkeeping of `Function.update` at a slot of the `F`-selection: the `G'`-indexed tuple of
direction fields is unchanged. -/
lemma upd_FG {i j c : ℕ} {F : Fin i → Fin c} {G' : Fin j → Fin c}
    (hdisj : Disjoint (Set.range F) (Set.range G'))
    (w : Fin c → TF (I := I) (M := M)) (X : TF (I := I) (M := M)) (a : Fin i) :
    (fun k : Fin j => Function.update w (F a) X (G' k)) = fun k : Fin j => w (G' k) := by
  funext k
  have h : G' k ≠ F a := fun hc => Set.disjoint_left.mp hdisj ⟨a, rfl⟩ ⟨k, hc⟩
  rw [Function.update_of_ne h X w]

/-- Bookkeeping of `Function.update` at a slot of the `G'`-selection: the `F`-indexed tuple of
direction fields is unchanged. -/
lemma upd_GF {i j c : ℕ} {F : Fin i → Fin c} {G' : Fin j → Fin c}
    (hdisj : Disjoint (Set.range F) (Set.range G'))
    (w : Fin c → TF (I := I) (M := M)) (X : TF (I := I) (M := M)) (b : Fin j) :
    (fun k : Fin i => Function.update w (G' b) X (F k)) = fun k : Fin i => w (F k) := by
  funext k
  have h : F k ≠ G' b := fun hc => Set.disjoint_left.mp hdisj ⟨k, rfl⟩ ⟨b, hc.symm⟩
  rw [Function.update_of_ne h X w]

/-- Bookkeeping of `Function.update` at a slot of the `G'`-selection: the update acts on the
`G'`-indexed tuple of direction fields as the corresponding update. -/
lemma upd_GG {j c : ℕ} {G' : Fin j → Fin c} (hg : Function.Injective G')
    (w : Fin c → TF (I := I) (M := M)) (X : TF (I := I) (M := M)) (b : Fin j) :
    (fun k : Fin j => Function.update w (G' b) X (G' k))
      = Function.update (fun b' : Fin j => w (G' b')) b X := by
  funext k
  by_cases h : k = b
  · subst h; simp
  · rw [Function.update_of_ne (show G' k ≠ G' b from fun hc => h (hg hc)) X w,
      Function.update_of_ne h X (fun b' => w (G' b'))]

/-- Smoothness of a one-slot update of a tuple of smooth fields. -/
lemma smE_update {k : ℕ} {w : Fin k → TF (I := I) (M := M)} (n : Fin k)
    {X : TF (I := I) (M := M)} (hw : ∀ j, SmE I M (w j)) (hX : SmE I M X) :
    ∀ j, SmE I M (Function.update w n X j) := by
  intro j
  by_cases h : j = n
  · rw [h, Function.update_self]; exact hX
  · rw [Function.update_of_ne h X w]; exact hw j

/-- Smoothness of the zero tangent field. -/
lemma smE_zero : SmE I M (0 : TF (I := I) (M := M)) := by
  have h := contMDiff_zeroSection (𝕜 := ℝ) (F := E) (E := fun y : M => TangentSpace I y)
    (n := ∞) (IB := I)
  rw [SmE]
  exact h

/-- **Reindexing a sum over `Fin c` by the two selections.**  The two injective selections `F` and
`G'` with disjoint ranges and `i + j = c` partition `Fin c`, so summing over `Fin c` is summing over
the `F`-range and the `G'`-range. -/
lemma sum_fin_reindex {i j c : ℕ} (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hf : Function.Injective F) (hg : Function.Injective G')
    (hdisj : Disjoint (Set.range F) (Set.range G')) (hc : i + j = c) (g : Fin c → ℝ) :
    (∑ m : Fin c, g m) = (∑ a : Fin i, g (F a)) + (∑ b : Fin j, g (G' b)) := by
  have hφinj : Function.Injective (Sum.elim F G') := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (hf h)
    · exact absurd (Set.disjoint_left.mp hdisj ⟨a, rfl⟩ ⟨b, h.symm⟩) not_false
    · exact absurd (Set.disjoint_left.mp hdisj ⟨b, rfl⟩ ⟨a, h⟩) not_false
    · exact congrArg Sum.inr (hg h)
  have hcard : Fintype.card (Fin i ⊕ Fin j) = Fintype.card (Fin c) := by
    simp [Fintype.card_sum, hc]
  have hbij : Function.Bijective (Sum.elim F G') :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hφinj, hcard⟩
  let e : Fin i ⊕ Fin j ≃ Fin c := Equiv.ofBijective (Sum.elim F G') hbij
  have hes : ∀ s : Fin i ⊕ Fin j, e s = Sum.elim F G' s := fun s => rfl
  rw [show (∑ m : Fin c, g m) = ∑ s : Fin i ⊕ Fin j, g (e s) from
      Fintype.sum_equiv e.symm g (fun s => g (e s)) (fun m => by simp),
    Fintype.sum_sum_type]
  simp only [hes, Sum.elim_inl, Sum.elim_inr]

/-! ## Consequences of the additivity of the operator in its value slot

These are the elementary consequences of the hypothesis `haddS` (additivity in the *first value
slot*) that are needed to split the compound field produced by `vstep` (the same chain as
`Work.Diff.EXT.ConnCov.DTB.add_slot_zero`/`add_slot_split`). -/

/-- `SlotAddS` is the only hypothesis on the operator used below. -/
def SlotAddS {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M)) : Prop :=
  ∀ (Y₁ Y₂ : TF (I := I) (M := M)),
    SmE I M Y₁ → SmE I M Y₂ → S d (Y₁ + Y₂) Z = S d Y₁ Z + S d Y₂ Z

lemma add_slot_zero {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z) :
    S d (0 : TF (I := I) (M := M)) Z = 0 := by
  have h := haddS 0 0 smE_zero smE_zero
  have h0 : S d (0 : TF (I := I) (M := M)) Z
      = S d (0 : TF (I := I) (M := M)) Z + S d (0 : TF (I := I) (M := M)) Z := by
    simpa only [add_zero] using h
  have h1 : S d (0 : TF (I := I) (M := M)) Z + 0
      = S d (0 : TF (I := I) (M := M)) Z + S d (0 : TF (I := I) (M := M)) Z := by
    rw [add_zero]; exact h0
  exact (add_left_cancel h1).symm

lemma add_slot_neg {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {Y : TF (I := I) (M := M)} (hY : SmE I M Y) :
    S d (-Y) Z = -S d Y Z := by
  have h := haddS Y (-Y) hY hY.neg_section
  have hneg0 : Y + (-Y) = (0 : TF (I := I) (M := M)) := by funext y; simp
  rw [hneg0, add_slot_zero (I := I) (M := M) S d Z haddS hZ] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

lemma add_slot_sub {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {Y₁ Y₂ : TF (I := I) (M := M)} (h₁ : SmE I M Y₁) (h₂ : SmE I M Y₂) :
    S d (Y₁ - Y₂) Z = S d Y₁ Z - S d Y₂ Z := by
  have h := haddS Y₁ (-Y₂) h₁ h₂.neg_section
  have hsub : Y₁ - Y₂ = Y₁ + (-Y₂) := by funext y; exact sub_eq_add_neg (Y₁ y) (Y₂ y)
  have hneg := add_slot_neg (I := I) (M := M) S d Z haddS hZ h₂
  rw [hsub, h, hneg, sub_eq_add_neg]

lemma add_slot_finset {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {ι : Type*} (s : Finset ι) (F : ι → TF (I := I) (M := M))
    (hF : ∀ n ∈ s, SmE I M (F n)) :
    S d (fun y : M => ∑ n ∈ s, F n y) Z = ∑ n ∈ s, S d (F n) Z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y : M => ∑ n ∈ (∅ : Finset ι), F n y) = (0 : TF (I := I) (M := M)) := by
        funext y; simp
      rw [h0, Finset.sum_empty]
      exact add_slot_zero (I := I) (M := M) S d Z haddS hZ
  | insert a s ha ih =>
      have haS : SmE I M (F a) := hF a (Finset.mem_insert_self a s)
      have hsS : SmE I M (fun y : M => ∑ n ∈ s, F n y) :=
        ContMDiff.sum_section (fun n hn => hF n (Finset.mem_insert_of_mem hn))
      have hsplit : (fun y : M => ∑ n ∈ insert a s, F n y)
          = F a + (fun y : M => ∑ n ∈ s, F n y) := by
        funext y
        rw [Pi.add_apply, Finset.sum_insert ha]
      rw [hsplit, haddS (F a) _ haS hsS, Finset.sum_insert ha,
        ih (fun n hn => hF n (Finset.mem_insert_of_mem hn))]

lemma add_slot_sum {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {ι : Type*} [Fintype ι] (F : ι → TF (I := I) (M := M))
    (hF : ∀ n, SmE I M (F n)) :
    S d (fun y : M => ∑ n : ι, F n y) Z = ∑ n : ι, S d (F n) Z :=
  add_slot_finset (I := I) (M := M) S d Z haddS hZ Finset.univ F (fun n _ => hF n)

/-- **Splitting a four-term combination of sections in the value slot of the operator**: the
combination `A − Σ B − C − D` (which is how `vstep` splits) is additive. -/
lemma add_slot_split {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {ι : Type*} [Fintype ι] (A : TF (I := I) (M := M)) (B : ι → TF (I := I) (M := M))
    (C D : TF (I := I) (M := M))
    (hA : SmE I M A) (hB : ∀ n, SmE I M (B n)) (hC : SmE I M C) (hD : SmE I M D) :
    S d (fun y : M => A y - (∑ n : ι, B n y) - C y - D y) Z
      = S d A Z - (∑ n : ι, S d (B n) Z) - S d C Z - S d D Z := by
  have hS : SmE I M (fun y : M => ∑ n : ι, B n y) :=
    ContMDiff.sum_section (fun n _ => hB n)
  have hsub1 : (fun y : M => A y - (∑ n : ι, B n y) - C y - D y)
      = A - (fun y : M => ∑ n : ι, B n y) - C - D := by
    funext y; simp only [Pi.sub_apply]
  rw [hsub1,
    add_slot_sub (I := I) (M := M) S d Z haddS hZ ((hA.sub_section hS).sub_section hC) hD,
    add_slot_sub (I := I) (M := M) S d Z haddS hZ (hA.sub_section hS) hC,
    add_slot_sub (I := I) (M := M) S d Z haddS hZ hA hS,
    add_slot_sum (I := I) (M := M) S d Z haddS hZ B hB]

/-- Additivity of the metric tower in its first value slot, as a `SlotAddS` hypothesis. -/
lemma SlotAddSplit {i : ℕ} (S : Work.Diff.EXT.ConnCov.DT.Op2 (I := I) (M := M) i)
    (d : Fin i → TF (I := I) (M := M)) (Z : TF (I := I) (M := M))
    (hd : ∀ p, SmE I M (d p))
    (haddS : ∀ (d : Fin i → TF (I := I) (M := M)) (Y₁ Y₂ Z : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M Y₁ → SmE I M Y₂ → SmE I M Z →
      S d (Y₁ + Y₂) Z = S d Y₁ Z + S d Y₂ Z)
    (hZ : SmE I M Z) {ι : Type*} [Fintype ι]
    (A : TF (I := I) (M := M)) (B : ι → TF (I := I) (M := M)) (C D : TF (I := I) (M := M))
    (hA : SmE I M A) (hB : ∀ n, SmE I M (B n)) (hC : SmE I M C) (hD : SmE I M D) :
    S d (fun y : M => A y - (∑ n : ι, B n y) - C y - D y) Z
      = S d A Z - (∑ n : ι, S d (B n) Z) - S d C Z - S d D Z :=
  add_slot_split (I := I) (M := M) S d Z (fun Y₁ Y₂ h₁ h₂ => haddS d Y₁ Y₂ Z hd h₁ h₂ hZ) hZ
    A B C D hA hB hC hD

theorem StepSelTermDT
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {c i j : ℕ} (hc : i + j = c) (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hf : Function.Injective F) (hg : Function.Injective G')
    (hdisj : Disjoint (Set.range F) (Set.range G'))
    (hcov : ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G')
    (hadd : ∀ (d : Fin i → Work.Diff.EXT.ATower.TF (I := I) (M := M))
      (Y₁ Y₂ Z : Work.Diff.EXT.ATower.TF (I := I) (M := M)),
      (∀ p, Work.Diff.EXT.ATower.SmE I M (d p)) → Work.Diff.EXT.ATower.SmE I M Y₁ →
      Work.Diff.EXT.ATower.SmE I M Y₂ → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ConnCov.DT.gtTower G t i d (Y₁ + Y₂) Z
        = Work.Diff.EXT.ConnCov.DT.gtTower G t i d Y₁ Z
          + Work.Diff.EXT.ConnCov.DT.gtTower G t i d Y₂ Z)
    (v : Fin (c + 1) → Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (A B C : Work.Diff.EXT.ATower.TF (I := I) (M := M))
    (hv : ∀ k, Work.Diff.EXT.ATower.SmE I M (v k))
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) (x : M) :
    Work.Diff.EXT.ATower.step (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.DT.selTerm G t c i j F G') v A B C x
      = Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) (i + 1) j
          (Work.Diff.EXT.ConnCov.DT.FTen F) (Work.Diff.EXT.ConnCov.DT.Gshift G') v A B C x
        + Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) i (j + 1)
          (Work.Diff.EXT.ConnCov.DT.Fshift F) (Work.Diff.EXT.ConnCov.DT.GTen G') v A B C x := by
  -- the δ-tower value, and its smoothness
  have hDsm : SmE I M (Work.Diff.EXT.ConnCov.DT.deltaTower G t j
      (fun b : Fin j => v (G' b).succ) B A) :=
    Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTowerSm hLC G t j (fun b : Fin j => v (G' b).succ) B A
      (fun b => hv (G' b).succ) hB hA
  -- one recursion step with the new direction given to the metric factor
  have key1 : Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) (i + 1) j
        (Work.Diff.EXT.ConnCov.DT.FTen F) (Work.Diff.EXT.ConnCov.DT.Gshift G') v A B C x
      = mvfderiv I (fun y : M => Work.Diff.EXT.ConnCov.DT.gtTower G t i
            (fun a : Fin i => v (F a).succ)
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B A)
            C y) x (v 0 x)
        - (∑ a : Fin i, Work.Diff.EXT.ConnCov.DT.gtTower G t i
              (Function.update (fun a' : Fin i => v (F a').succ) a
                (fun y : M => (Submission.Diff.lcOf (G 0)) (v (F a).succ) y (v 0 y)))
              (Work.Diff.EXT.ConnCov.DT.deltaTower G t j
                (fun b : Fin j => v (G' b).succ) B A) C x)
        - Work.Diff.EXT.ConnCov.DT.gtTower G t i (fun a : Fin i => v (F a).succ)
            (fun y : M => (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.DT.deltaTower G t j
                (fun b : Fin j => v (G' b).succ) B A) y (v 0 y)) C x
        - Work.Diff.EXT.ConnCov.DT.gtTower G t i (fun a : Fin i => v (F a).succ)
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B A)
            (fun y : M => (Submission.Diff.lcOf (G 0)) C y (v 0 y)) x := by
    have hsel : Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) (i + 1) j
          (Work.Diff.EXT.ConnCov.DT.FTen F) (Work.Diff.EXT.ConnCov.DT.Gshift G') v A B C x
        = Work.Diff.EXT.ConnCov.DT.gtTower G t (i + 1)
            (Fin.cons (v 0) (fun a : Fin i => v (F a).succ))
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j
              (fun b : Fin j => v (G' b).succ) B A) C x := by
      simp only [Work.Diff.EXT.ConnCov.DT.selTerm, cons_FTen, gshift_eq]
    rw [hsel, show Work.Diff.EXT.ConnCov.DT.gtTower G t (i + 1)
        = Work.Diff.EXT.ConnCov.DT.gstep (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.DT.gtTower G t i) from rfl]
    simp only [Work.Diff.EXT.ConnCov.DT.gstep, Fin.cons_zero, Fin.cons_succ, Finset.sum_apply]
  -- one recursion step with the new direction given to the δ-factor
  have key2a : Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) i (j + 1)
        (Work.Diff.EXT.ConnCov.DT.Fshift F) (Work.Diff.EXT.ConnCov.DT.GTen G') v A B C x
      = Work.Diff.EXT.ConnCov.DT.gtTower G t i (fun a : Fin i => v (F a).succ)
          (Work.Diff.EXT.ConnCov.DT.vstep (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j)
            (Fin.cons (v 0) (fun b : Fin j => v (G' b).succ)) B A) C x := by
    have hsel : Work.Diff.EXT.ConnCov.DT.selTerm G t (c + 1) i (j + 1)
          (Work.Diff.EXT.ConnCov.DT.Fshift F) (Work.Diff.EXT.ConnCov.DT.GTen G') v A B C x
        = Work.Diff.EXT.ConnCov.DT.gtTower G t i (fun a : Fin i => v (F a).succ)
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t (j + 1)
              (Fin.cons (v 0) (fun b : Fin j => v (G' b).succ)) B A) C x := by
      simp only [Work.Diff.EXT.ConnCov.DT.selTerm, fshift_eq, cons_GTen]
    rw [hsel, show Work.Diff.EXT.ConnCov.DT.deltaTower G t (j + 1)
        = Work.Diff.EXT.ConnCov.DT.vstep (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j) from rfl]
  rw [key1, key2a]
  -- the recursion step of the δ-tower, as an explicit four-term combination
  have hvstep : Work.Diff.EXT.ConnCov.DT.vstep (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.DT.deltaTower G t j)
        (Fin.cons (v 0) (fun b : Fin j => v (G' b).succ)) B A
      = (fun y : M => (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.DT.deltaTower G t j
              (fun b : Fin j => v (G' b).succ) B A) y (v 0 y)
          - (∑ b : Fin j, Work.Diff.EXT.ConnCov.DT.deltaTower G t j
              (Function.update (fun b' : Fin j => v (G' b').succ) b
                (fun y' : M => (Submission.Diff.lcOf (G 0)) (v (G' b).succ) y' (v 0 y'))) B A y)
          - Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ)
              (fun y' : M => (Submission.Diff.lcOf (G 0)) B y' (v 0 y')) A y
          - Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B
              (fun y' : M => (Submission.Diff.lcOf (G 0)) A y' (v 0 y')) y) := by
    funext y
    simp only [Work.Diff.EXT.ConnCov.DT.vstep, Fin.cons_zero, Fin.cons_succ, Finset.sum_apply]
  rw [hvstep]
  -- split the compound field in the value slot of the metric tower
  have hsplit := SlotAddSplit (S := Work.Diff.EXT.ConnCov.DT.gtTower G t i)
    (d := fun a : Fin i => v (F a).succ) (Z := C) (fun p => hv (F p).succ) hadd hC
    (A := (fun y : M => (Submission.Diff.lcOf (G 0))
      (Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B A) y (v 0 y)))
    (B := fun b : Fin j => Work.Diff.EXT.ConnCov.DT.deltaTower G t j
      (Function.update (fun b' : Fin j => v (G' b').succ) b
        (fun y' : M => (Submission.Diff.lcOf (G 0)) (v (G' b).succ) y' (v 0 y'))) B A)
    (C := Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ)
      (fun y' : M => (Submission.Diff.lcOf (G 0)) B y' (v 0 y')) A)
    (D := Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B
      (fun y' : M => (Submission.Diff.lcOf (G 0)) A y' (v 0 y')))
    (ATower.lcOf_apply_smE hLC (G 0)
      (Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B A) (v 0)
      hDsm (hv 0))
    (fun b => Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTowerSm hLC G t j
      (Function.update (fun b' : Fin j => v (G' b').succ) b
        (fun y' : M => (Submission.Diff.lcOf (G 0)) (v (G' b).succ) y' (v 0 y'))) B A
      (smE_update b (fun b' => hv (G' b').succ)
        (ATower.lcOf_apply_smE hLC (G 0) (v (G' b).succ) (v 0) (hv _) (hv 0))) hB hA)
    (Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTowerSm hLC G t j (fun b : Fin j => v (G' b).succ)
      (fun y' : M => (Submission.Diff.lcOf (G 0)) B y' (v 0 y')) A
      (fun b => hv (G' b).succ)
      (ATower.lcOf_apply_smE hLC (G 0) B (v 0) hB (hv 0)) hA)
    (Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTowerSm hLC G t j (fun b : Fin j => v (G' b).succ) B
      (fun y' : M => (Submission.Diff.lcOf (G 0)) A y' (v 0 y'))
      (fun b => hv (G' b).succ) hB
      (ATower.lcOf_apply_smE hLC (G 0) A (v 0) hA (hv 0)))
  rw [congrFun hsplit x]
  simp only [Pi.sub_apply, Finset.sum_apply]
  -- expand the left-hand side
  simp only [Work.Diff.EXT.ATower.step]
  rw [sum_fin_reindex F G' hf hg hdisj hc]
  simp only [Work.Diff.EXT.ConnCov.DT.selTerm, upd_FF hf, upd_FG hdisj, upd_GF hdisj, upd_GG hg]
  rw [show mvfderiv I (Work.Diff.EXT.ConnCov.DT.selTerm G t c i j F G'
        (fun i : Fin c => v i.succ) A B C) x (v 0 x)
      = mvfderiv I (fun y : M => Work.Diff.EXT.ConnCov.DT.gtTower G t i
          (fun a : Fin i => v (F a).succ)
          (Work.Diff.EXT.ConnCov.DT.deltaTower G t j (fun b : Fin j => v (G' b).succ) B A)
          C y) x (v 0 x) from rfl]
  ring

end Work.Diff.EXT.ConnCov.RicTr
