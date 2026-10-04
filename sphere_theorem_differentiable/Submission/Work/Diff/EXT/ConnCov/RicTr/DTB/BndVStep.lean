import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.DeltaTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVKit
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.GtTowerSuccEqSwap
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.SlotAddAOfLocal
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-step rule of the Leibniz expansion (the twisted pairing)

`Work.Diff.EXT.ConnCov.DTB.Wins G t c = g_t ⊙ V_c` is the lowering of the δ-tower
`V_c = ∇^{g_0,c}(∇^{g_t} − ∇^{g_0})`.  The bound of `V_c` from the known bounds on the tower of
`aOf G t = g_t ⊙ δ` rests on the **Leibniz expansion** of the tower of the twisted pairing

  `pairOp e S T`,   `(pairOp e S T) v A B C y = S (v ∘ e ∘ inl) (T (v ∘ e ∘ inr) B A) C y`,

of a `(0,2+i)`-tensor `S` (the metric tower `∇^{g_0,i}g_t`) with a vector-valued `(1,2+j)`-tensor `T`
(the δ-tower `∇^{g_0,j}δ`); the `c = i + j` direction slots are distributed by the equivalence `e`.

The expansion is the iteration of the **one-step rule** `step_pairOp`: the replacement of the
connection in one recursion step produces exactly the two terms in which the new direction goes to
`S` (giving `gstep S`, the metric-tower recursion) or to `T` (giving `vstep T`, the δ-tower
recursion).

The one-step rule is where the whole difficulty of the expansion sits: the recursion `step` is *not*
a derivation on the nose — the correction terms in the *value slots* of `step` see the fields
`∇_{V₀}(Y₁ + Y₂) = ∇_{V₀}Y₁ + ∇_{V₀}Y₂` into which `vstep T` splits, so the rule holds only because
`S` is additive in the slot that receives `T (…) B A` (`haddS` below).  On non-smooth fields the
identity genuinely **fails** (the recursion uses `mvfderiv`, which is the junk value `0` where the
function is not differentiable), which is why every statement below is made on `C^∞` fields only.

## Contents

* `pairOp` — the twisted pairing;
* `smE_zero`, `update_comp_inl`, `update_comp_inl_inr`, `update_comp_inr_inl`, `update_comp_inr` —
  bookkeeping of `Function.update` under the index equivalence `e`;
* `add_slot_zero`, `add_slot_neg`, `add_slot_sub`, `add_slot_sum`, `add_slot_finset_of_forall` —
  the consequences of the slot additivity `haddS` of `S` used by the one-step rule;
* `step_pairOp` — **the one-step rule**.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.DTB

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## 1. The twisted pairing -/

/-- **The twisted pairing** of a `(0,2+i)`-tensor `S` (the metric tower) with a vector-valued
`(1,2+j)`-tensor `T` (the δ-tower): the `c = i + j` direction slots are distributed by the
equivalence `e`, the `S`-factor receiving the directions `e ∘ inl` and the `T`-factor the directions
`e ∘ inr`.  The two field slots of `T` are exchanged (`B A`), so that at `i = j = 0` the pairing is
the lowered connection difference `aOf`. -/
noncomputable def tpair {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (S : Op2 (I := I) (M := M) i) (T : VOp (I := I) (M := M) j) :
    Op3 (I := I) (M := M) c :=
  fun v A B C y =>
    S (fun a : Fin i => v (e (Sum.inl a)))
      (T (fun b : Fin j => v (e (Sum.inr b))) B A) C y

theorem tpair_apply {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (S : Op2 (I := I) (M := M) i) (T : VOp (I := I) (M := M) j)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (y : M) :
    tpair e S T v A B C y
      = S (fun a : Fin i => v (e (Sum.inl a)))
          (T (fun b : Fin j => v (e (Sum.inr b))) B A) C y := rfl

/-! ## 2. Bookkeeping of `Function.update` under the index equivalence

The one recursion step splits the `Fin c`-indexed tuple of direction fields according to `e`; the
`Function.update` at a slot of `Fin c` becomes a `Function.update` of the `Fin i`-tuple (if the slot
is `e ∘ inl`) or of the `Fin j`-tuple (if it is `e ∘ inr`), and leaves the other tuple unchanged. -/

/-- Smoothness of the zero tangent field. -/
lemma smE_zero : SmE I M (0 : TF (I := I) (M := M)) := by
  have h := contMDiff_zeroSection (𝕜 := ℝ) (F := E) (E := fun y : M => TangentSpace I y)
    (n := ∞) (IB := I)
  rw [SmE]
  exact h

/-- An update at `e ∘ inl` acts on the `inl`-part as an update at the corresponding index. -/
lemma update_comp_inl {X : Type*} {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (u : Fin c → X) (a : Fin i) (F : X) :
    (fun a' : Fin i => Function.update u (e (Sum.inl a)) F (e (Sum.inl a')))
      = Function.update (fun a' : Fin i => u (e (Sum.inl a'))) a F := by
  funext a'
  by_cases h : a' = a
  · subst h; simp
  · rw [Function.update_of_ne (fun hc => h (by simpa using e.injective hc)) F u,
      Function.update_of_ne h F (fun a' => u (e (Sum.inl a')))]

/-- An update at `e ∘ inl` leaves the `inr`-part unchanged. -/
lemma update_comp_inl_inr {X : Type*} {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (u : Fin c → X) (a : Fin i) (F : X) :
    (fun b : Fin j => Function.update u (e (Sum.inl a)) F (e (Sum.inr b)))
      = fun b : Fin j => u (e (Sum.inr b)) := by
  funext b
  exact Function.update_of_ne (fun hc => by
    have h2 : (Sum.inr b : Fin i ⊕ Fin j) = Sum.inl a := e.injective hc
    cases h2) F u

/-- An update at `e ∘ inr` leaves the `inl`-part unchanged. -/
lemma update_comp_inr_inl {X : Type*} {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (u : Fin c → X) (b : Fin j) (F : X) :
    (fun a' : Fin i => Function.update u (e (Sum.inr b)) F (e (Sum.inl a')))
      = fun a' : Fin i => u (e (Sum.inl a')) := by
  funext a'
  exact Function.update_of_ne (fun hc => by
    have h2 : (Sum.inl a' : Fin i ⊕ Fin j) = Sum.inr b := e.injective hc
    cases h2) F u

/-- An update at `e ∘ inr` acts on the `inr`-part as an update at the corresponding index. -/
lemma update_comp_inr {X : Type*} {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (u : Fin c → X) (b : Fin j) (F : X) :
    (fun b' : Fin j => Function.update u (e (Sum.inr b)) F (e (Sum.inr b')))
      = Function.update (fun b' : Fin j => u (e (Sum.inr b'))) b F := by
  funext b'
  by_cases h : b' = b
  · subst h; simp
  · rw [Function.update_of_ne (fun hc => h (by simpa using e.injective hc)) F u,
      Function.update_of_ne h F (fun b' => u (e (Sum.inr b')))]

/-- Reindexing a sum over `Fin c` by the equivalence `e`. -/
lemma sum_comp_equiv {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (g : Fin c → ℝ) :
    (∑ m : Fin c, g m) = ∑ s : Fin i ⊕ Fin j, g (e s) :=
  Fintype.sum_equiv e.symm g (fun s => g (e s)) (fun m => by simp)

/-- Smoothness of a one-slot update of a tuple of smooth fields. -/
lemma smE_update {k : ℕ} {w : Fin k → TF (I := I) (M := M)} (n : Fin k) {W : TF (I := I) (M := M)}
    (hw : ∀ j, SmE I M (w j)) (hW : SmE I M W) : ∀ j, SmE I M (Function.update w n W j) := by
  intro j
  by_cases h : j = n
  · rw [h, Function.update_self]; exact hW
  · rw [Function.update_of_ne h W w]; exact hw j

/-- The `shiftL`-bookkeeping on the `inl`-part: the new direction is put in front. -/
lemma shiftL_inl_cons {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (v : Fin (c + 1) → TF (I := I) (M := M)) :
    (fun a : Fin (i + 1) => v (shiftL e (Sum.inl a)))
      = Fin.cons (v 0) (fun a : Fin i => v ((e (Sum.inl a)).succ)) := by
  funext a
  induction a using Fin.cases with
  | zero => rw [shiftL_inl_zero, Fin.cons_zero]
  | succ a' => rw [shiftL_inl_succ, Fin.cons_succ]

/-- The `shiftL`-bookkeeping on the `inr`-part. -/
lemma shiftL_inr_cons {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (v : Fin (c + 1) → TF (I := I) (M := M)) :
    (fun b : Fin j => v (shiftL e (Sum.inr b)))
      = fun b : Fin j => v ((e (Sum.inr b)).succ) := by
  funext b; rw [shiftL_inr]

/-- The `shiftR`-bookkeeping on the `inl`-part. -/
lemma shiftR_inl_cons {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (v : Fin (c + 1) → TF (I := I) (M := M)) :
    (fun a : Fin i => v (shiftR e (Sum.inl a)))
      = fun a : Fin i => v ((e (Sum.inl a)).succ) := by
  funext a; rw [shiftR_inl]

/-- The `shiftR`-bookkeeping on the `inr`-part: the new direction is put in front. -/
lemma shiftR_inr_cons {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (v : Fin (c + 1) → TF (I := I) (M := M)) :
    (fun b : Fin (j + 1) => v (shiftR e (Sum.inr b)))
      = Fin.cons (v 0) (fun b : Fin j => v ((e (Sum.inr b)).succ)) := by
  funext b
  induction b using Fin.cases with
  | zero => rw [shiftR_inr_zero, Fin.cons_zero]
  | succ b' => rw [shiftR_inr_succ, Fin.cons_succ]

/-! ## 3. Consequences of the slot additivity of `S` -/

section Slot

variable {i : ℕ} (S : Op2 (I := I) (M := M) i) (d : Fin i → TF (I := I) (M := M))
  (Z : TF (I := I) (M := M))

/-- **Slot additivity of `S`**: the only hypothesis on `S` that the one-step rule needs. -/
def SlotAddS : Prop :=
  ∀ (Y₁ Y₂ : TF (I := I) (M := M)),
    SmE I M Y₁ → SmE I M Y₂ → S d (Y₁ + Y₂) Z = S d Y₁ Z + S d Y₂ Z

theorem add_slot_zero (haddS : SlotAddS (I := I) (M := M) S d Z)
    (hZ : SmE I M Z) : S d (0 : TF (I := I) (M := M)) Z = 0 := by
  have h := haddS 0 0 smE_zero smE_zero
  have h0 : S d (0 : TF (I := I) (M := M)) Z
      = S d (0 : TF (I := I) (M := M)) Z + S d (0 : TF (I := I) (M := M)) Z := by
    simpa only [add_zero] using h
  have h1 : S d (0 : TF (I := I) (M := M)) Z + 0
      = S d (0 : TF (I := I) (M := M)) Z + S d (0 : TF (I := I) (M := M)) Z := by
    rw [add_zero]; exact h0
  exact (add_left_cancel h1).symm

theorem add_slot_neg (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {Y : TF (I := I) (M := M)} (hY : SmE I M Y) :
    S d (-Y) Z = -S d Y Z := by
  have h := haddS Y (-Y) hY hY.neg_section
  have hneg0 : Y + (-Y) = (0 : TF (I := I) (M := M)) := by funext y; simp
  rw [hneg0, add_slot_zero (I := I) (M := M) S d Z haddS hZ] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

theorem add_slot_sub (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {Y₁ Y₂ : TF (I := I) (M := M)} (h₁ : SmE I M Y₁) (h₂ : SmE I M Y₂) :
    S d (Y₁ - Y₂) Z = S d Y₁ Z - S d Y₂ Z := by
  have h := haddS Y₁ (-Y₂) h₁ h₂.neg_section
  have hsub : Y₁ - Y₂ = Y₁ + (-Y₂) := by funext y; exact sub_eq_add_neg (Y₁ y) (Y₂ y)
  have hneg := add_slot_neg (I := I) (M := M) S d Z haddS hZ h₂
  rw [hsub, h, hneg, sub_eq_add_neg]

theorem add_slot_finset (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
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

theorem add_slot_sum (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
    {ι : Type*} [Fintype ι] (F : ι → TF (I := I) (M := M))
    (hF : ∀ n, SmE I M (F n)) :
    S d (fun y : M => ∑ n : ι, F n y) Z = ∑ n : ι, S d (F n) Z := by
  exact add_slot_finset (I := I) (M := M) S d Z haddS hZ Finset.univ F
    (fun n _ => hF n)

end Slot

/-- **Splitting a four-term combination of sections in the value slot of `S`**: the combination
`A − Σ_n B_n − C − D` (which is how `vstep` splits) is additive. -/
theorem add_slot_split {i : ℕ} (S : Op2 (I := I) (M := M) i) (d : Fin i → TF (I := I) (M := M))
    (Z : TF (I := I) (M := M)) (haddS : SlotAddS (I := I) (M := M) S d Z) (hZ : SmE I M Z)
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
  rw [hsub1, add_slot_sub (I := I) (M := M) S d Z haddS hZ ((hA.sub_section hS).sub_section hC) hD,
    add_slot_sub (I := I) (M := M) S d Z haddS hZ (hA.sub_section hS) hC,
    add_slot_sub (I := I) (M := M) S d Z haddS hZ hA hS,
    add_slot_sum (I := I) (M := M) S d Z haddS hZ B hB]

/-! ## 4. Additivity of the metric tower in its value slot -/

/-- Slot additivity and smoothness of the `aOf`-tower `∇^{g_0,k}(g_t ⊙ δ)`. -/
theorem aOf_tower_slotAdd_sm [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ k : ℕ,
      SlotAdd (tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) k)
      ∧ ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
          (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmE I M C →
          SmF I M (tower (lcOf (G 0)) (fun _ => aOf G t) k v A B C) :=
  tower_slotAdd_smF (I := I) (M := M) hLC (G 0) (base := fun _ => aOf G t)
    (slotAdd_aOf_local (I := I) (M := M) hLC G t)
    (fun _ A B C hA hB hC => aOf_smF hLC G t hA hB hC)

/-- **The metric tower is additive in its first value slot** (this is the hypothesis `haddS` of
`step_pairOp` instantiated at the metric tower). -/
theorem gtTower_add_val0 [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ i : ℕ, ∀ (d : Fin i → TF (I := I) (M := M)) (Y₁ Y₂ Z : TF (I := I) (M := M)),
      (∀ j, SmE I M (d j)) → SmE I M Y₁ → SmE I M Y₂ → SmE I M Z →
      gtTower G t i d (Y₁ + Y₂) Z = gtTower G t i d Y₁ Z + gtTower G t i d Y₂ Z := by
  intro i
  induction i with
  | zero =>
      intro d Y₁ Y₂ Z hd hY₁ hY₂ hZ
      funext x
      show (G t).inner x ((Y₁ + Y₂) x) (Z x)
        = (G t).inner x (Y₁ x) (Z x) + (G t).inner x (Y₂ x) (Z x)
      rw [show (Y₁ + Y₂) x = Y₁ x + Y₂ x from rfl, map_add, ContinuousLinearMap.add_apply]
  | succ i ih =>
      intro d Y₁ Y₂ Z hd hY₁ hY₂ hZ
      have hdc : ∀ j : Fin i, SmE I M ((fun j : Fin i => d (Fin.castSucc j)) j) :=
        fun j => hd (Fin.castSucc j)
      have hν : gtTower G t (i + 1) d (Y₁ + Y₂) Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) (Y₁ + Y₂) Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z (Y₁ + Y₂) := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d (Y₁ + Y₂) Z hd
          (hY₁.add_section hY₂) hZ x
      have h1 : gtTower G t (i + 1) d Y₁ Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₁ Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₁ := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y₁ Z hd hY₁ hZ x
      have h2 : gtTower G t (i + 1) d Y₂ Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₂ Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₂ := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y₂ Z hd hY₂ hZ x
      have hadd := (aOf_tower_slotAdd_sm (I := I) (M := M) hLC G t i).1
      rw [hν, h1, h2,
        hadd.2.2.1 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₁ Y₂ Z
          hdc (hd (Fin.last i)) hY₁ hY₂ hZ,
        hadd.2.2.2 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₁ Y₂
          hdc (hd (Fin.last i)) hZ hY₁ hY₂]
      funext x
      simp only [Pi.add_apply]
      ring

/-! ## 4. The one-step rule -/

/-- **The one-step rule of the Leibniz expansion.**  One recursion step of the twisted pairing is
the sum of the two terms in which the new direction field `v 0` is given to the metric factor
(`gstep cov S`, the metric-tower recursion, with the index bookkeeping `shiftL`) or to the δ factor
(`vstep cov T`, the δ-tower recursion, with the index bookkeeping `shiftR`).

The identity is *not* a definitional property of the recursion: it holds because `S` is additive in
the value slot that receives `T (…) B A` (`haddS`), which is what allows the sum
`∇_{V₀}(T (…) B A)` of the second term to cancel the slot correction of the first. -/
theorem step_pairOp
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (S : Op2 (I := I) (M := M) i) (T : VOp (I := I) (M := M) j)
    (haddS : ∀ (d : Fin i → TF (I := I) (M := M)) (Y₁ Y₂ Z : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M Y₁ → SmE I M Y₂ → SmE I M Z →
      S d (Y₁ + Y₂) Z = S d Y₁ Z + S d Y₂ Z)
    (hsmT : ∀ (d : Fin j → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M X → SmE I M Y → SmE I M (T d X Y))
    (hsmcov : ∀ (W W' : TF (I := I) (M := M)), SmE I M W → SmE I M W' →
      SmE I M (fun y : M => cov W y (W' y)))
    (v : Fin (c + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ k, SmE I M (v k)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    step cov (tpair (I := I) (M := M) e S T) v A B C x
      = tpair (I := I) (M := M) (shiftL e) (gstep cov S) T v A B C x
        + tpair (I := I) (M := M) (shiftR e) S (vstep cov T) v A B C x := by
  have hv0 : SmE I M (v 0) := hv 0
  -- the `L`-side expansion (`step` of the pairing)
  have keyL : step cov (tpair (I := I) (M := M) e S T) v A B C x
      = mvfderiv I (fun y : M => S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) C y) x (v 0 x)
        - (∑ a : Fin i, S (Function.update (fun a' : Fin i => v ((e (Sum.inl a')).succ)) a
              (fun y : M => cov (v ((e (Sum.inl a)).succ)) y (v 0 y)))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) C x)
        - (∑ b : Fin j, S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (Function.update (fun b' : Fin j => v ((e (Sum.inr b')).succ)) b
              (fun y : M => cov (v ((e (Sum.inr b)).succ)) y (v 0 y))) B A) C x)
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) (fun y : M => cov B y (v 0 y)) A) C x
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B (fun y : M => cov A y (v 0 y))) C x
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) (fun y : M => cov C y (v 0 y)) x := by
    simp only [step, tpair, sum_comp_equiv e, Fintype.sum_sum_type, update_comp_inl,
      update_comp_inl_inr, update_comp_inr_inl, update_comp_inr, Finset.sum_apply]
    rw [show mvfderiv I (tpair (I := I) (M := M) e S T (fun i : Fin c => v i.succ) A B C) x (v 0 x)
        = mvfderiv I (fun y : M => S (fun a : Fin i => v ((e (Sum.inl a)).succ))
              (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) C y) x (v 0 x) from rfl]
    ring
  -- the metric-factor term of the right-hand side
  have key1 : tpair (I := I) (M := M) (shiftL e) (gstep cov S) T v A B C x
      = mvfderiv I (fun y : M => S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) C y) x (v 0 x)
        - (∑ a : Fin i, S (Function.update (fun a' : Fin i => v ((e (Sum.inl a')).succ)) a
              (fun y : M => cov (v ((e (Sum.inl a)).succ)) y (v 0 y)))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) C x)
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (fun y : M => cov (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) y (v 0 y)) C x
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) (fun y : M => cov C y (v 0 y)) x := by
    simp only [tpair]
    rw [shiftL_inl_cons e v, shiftL_inr_cons e v]
    simp only [gstep, Fin.cons_zero, Fin.cons_succ, Finset.sum_apply]
  -- the δ-factor term of the right-hand side
  have key2 : tpair (I := I) (M := M) (shiftR e) S (vstep cov T) v A B C x
      = S (fun a : Fin i => v ((e (Sum.inl a)).succ))
          (fun y : M => cov (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) y (v 0 y)) C x
        - (∑ b : Fin j, S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (Function.update (fun b' : Fin j => v ((e (Sum.inr b')).succ)) b
              (fun y : M => cov (v ((e (Sum.inr b)).succ)) y (v 0 y))) B A) C x)
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) (fun y : M => cov B y (v 0 y)) A) C x
        - S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B (fun y : M => cov A y (v 0 y))) C x := by
    have hvstep : vstep cov T (Fin.cons (v 0) (fun b : Fin j => v ((e (Sum.inr b)).succ))) B A
        = (fun y : M => cov (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) y (v 0 y)
            - (∑ b : Fin j, T (Function.update (fun b' : Fin j => v ((e (Sum.inr b')).succ)) b
                (fun y : M => cov (v ((e (Sum.inr b)).succ)) y (v 0 y))) B A y)
            - T (fun b : Fin j => v ((e (Sum.inr b)).succ)) (fun y : M => cov B y (v 0 y)) A y
            - T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B
                (fun y : M => cov A y (v 0 y)) y) := by
      funext y
      simp only [vstep, Pi.sub_apply, Fin.cons_zero, Fin.cons_succ, Finset.sum_apply]
    have hstep2 : tpair (I := I) (M := M) (shiftR e) S (vstep cov T) v A B C x
        = S (fun a : Fin i => v ((e (Sum.inl a)).succ))
            (vstep cov T (Fin.cons (v 0) (fun b : Fin j => v ((e (Sum.inr b)).succ))) B A) C x := by
      simp only [tpair]
      rw [shiftR_inl_cons e v, shiftR_inr_cons e v]
    rw [hstep2]
    rw [hvstep]
    rw [
      add_slot_split (I := I) (M := M) S (fun a : Fin i => v ((e (Sum.inl a)).succ)) C
        (fun Y₁ Y₂ h₁ h₂ => haddS _ Y₁ Y₂ C (fun p => hv _) h₁ h₂ hC) hC
        (fun y : M => cov (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B A) y (v 0 y))
        (fun b : Fin j => T (Function.update (fun b' : Fin j => v ((e (Sum.inr b')).succ)) b
          (fun y : M => cov (v ((e (Sum.inr b)).succ)) y (v 0 y))) B A)
        (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) (fun y : M => cov B y (v 0 y)) A)
        (T (fun b : Fin j => v ((e (Sum.inr b)).succ)) B (fun y : M => cov A y (v 0 y)))
        (hsmcov _ _ (hsmT _ B A (fun b => hv _) hB hA) hv0)
        (fun b => hsmT _ B A
          (smE_update b (fun b' => hv _) (hsmcov _ _ (hv _) hv0)) hB hA)
        (hsmT _ _ A (fun b => hv _) (hsmcov _ _ hB hv0) hA)
        (hsmT _ B _ (fun b => hv _) hB (hsmcov _ _ hA hv0))]
    simp only [Pi.sub_apply, Finset.sum_apply]
  rw [keyL, key1, key2]
  ring

end Work.Diff.EXT.ConnCov.DTB
