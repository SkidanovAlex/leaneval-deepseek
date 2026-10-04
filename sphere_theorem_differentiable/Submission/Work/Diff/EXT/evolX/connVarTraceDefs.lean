import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace operator of the connection-variation pairing: definitions and slot bookkeeping

The target `Work.Diff.EXT.evolX.connVar_pair_trace` computes the `a`-th jet of the frame-traced
level-`1` curvature tower

`cvTr0ρ g ef ρ Z y = ∑ m ckt g 1 (cvHins (a := 0) ρ Z (ef m)) y`:

covariant differentiation commutes with the trace over the frame, so the answer is the level-`(a+1)`
tower evaluated on the tuples `cvHins (a := a) ρ F (ef m)`.

The proof (`Work.Diff.EXT.evolX.jetAll_TOp_all`) is the induction on the jet order `a`.  At each step
the frame fields travel from the slots `cvUslot0 n`, `cvUslot1 n` of the tuple into the same slots of
the longer tuple; the two "extra" Leibniz corrections created by the frame slots cancel in the sum
over the frame (`Work.Diff.EXT.evolX.frameSlot_cancel_field`), because the frame velocity is
skew-adjoint while the two curvature slots traced against the frame sum are symmetric.

This module is *self-contained* (it imports only the definitions `connVarPairDefs`) and collects

* the elementary slot bookkeeping of the insertion `cvHins` (`cvHins_left`, `cvHins_right`,
  `cvHins_hpos`, `cvHins_update`, `cvHins_zero`, `cvDrop0_cvHins`, `cv_sum_univ_Hins`, …), re-derived
  here so that the proof of the target does not depend on the volatile sibling module
  `connVarPairIns`;
* `cvHins2`, the insertion with *two possibly different* fields in the two frame slots (the
  cancellation argument replaces one of them by the frame velocity `∇_X ef m`);
* `TOp`/`TOpJ`, the level-`n` frame-traced tower operator whose `n`-th jet is computed:
  `TOp g n ρ u G y = ckt g (n+1) (cvHins (a := n) ρ G u) y`, and its `Fin (3+n)`-reindexed form
  `TOpJ` matching the tuple convention of `jetAll`.

Everything lives in the namespace `Work.Diff.EXT.evolX.Trace`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX
namespace Trace

variable {α : Type*}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The `5`-block -/

@[simp] theorem cvIns5_0' (Z : Fin 3 → α) (u : α) : cvIns5 Z u 0 = Z 0 := rfl
@[simp] theorem cvIns5_1' (Z : Fin 3 → α) (u : α) : cvIns5 Z u 1 = u := rfl
@[simp] theorem cvIns5_2' (Z : Fin 3 → α) (u : α) : cvIns5 Z u 2 = Z 1 := rfl
@[simp] theorem cvIns5_3' (Z : Fin 3 → α) (u : α) : cvIns5 Z u 3 = u := rfl
@[simp] theorem cvIns5_4' (Z : Fin 3 → α) (u : α) : cvIns5 Z u 4 = Z 2 := rfl

/-- The reindexing `Fin (3+n) → Fin (n+3)` is bijective. -/
theorem cvCast3'_bijective (n : ℕ) : Function.Bijective (cvCast3' n) :=
  ⟨fun a b h => by
      have hh := congrArg (cvCast3 n) h
      rwa [cvCast3_cast3', cvCast3_cast3'] at hh,
   fun b => ⟨cvCast3 n b, cvCast3'_cvCast3 b⟩⟩

@[simp] theorem cvEven_val' (t : Fin 3) : (cvEven t).val = 2 * t.val := rfl

@[simp] theorem cv_natAdd_val' {n m : ℕ} (i : Fin m) : (Fin.natAdd n i).val = n + i.val := rfl

@[simp] theorem cv_castAdd_val' {n m : ℕ} (i : Fin n) : (Fin.castAdd m i).val = i.val := rfl

/-- The even slots of the `5`-block carry the entries of `Z`. -/
theorem cvIns5_even (Z : Fin 3 → α) (u : α) (t : Fin 3) : cvIns5 Z u (cvEven t) = Z t := by
  fin_cases t
  · exact cvIns5_0' Z u
  · exact cvIns5_2' Z u
  · exact cvIns5_4' Z u

theorem cvEven_injective : Function.Injective (cvEven) := by
  intro t t' h
  have hv := congrArg Fin.val h
  simp only [cvEven_val'] at hv
  exact Fin.ext (by omega)

/-- The odd slots of the `5`-block do not depend on the entries of `Z`. -/
theorem cvIns5_agree_ne (Z : Fin 3 → α) (A B : α) (j : Fin 5) (h1 : j ≠ 1) (h2 : j ≠ 3) :
    cvIns5 Z A j = cvIns5 Z B j := by
  fin_cases j
  · exact (cvIns5_even Z A 0).trans (cvIns5_even Z B 0).symm
  · exact absurd rfl h1
  · exact (cvIns5_even Z A 1).trans (cvIns5_even Z B 1).symm
  · exact absurd rfl h2
  · exact (cvIns5_even Z A 2).trans (cvIns5_even Z B 2).symm

/-! ## Index arithmetic -/

theorem castAdd5_succ {n : ℕ} (r : Fin n) :
    (Fin.castAdd 5 r : Fin (n + 5)).succ = Fin.castAdd 5 (Fin.succ r) := Fin.ext rfl

theorem castAdd3_succ {n : ℕ} (r : Fin n) :
    (Fin.castAdd 3 r : Fin (n + 3)).succ = Fin.castAdd 3 (Fin.succ r) := Fin.ext rfl

theorem natAdd_succ5 {n : ℕ} (j : Fin 5) :
    (Fin.natAdd n j : Fin (n + 5)).succ = Fin.natAdd (n + 1) j :=
  Fin.ext (by simp only [Fin.val_succ, cv_natAdd_val']; omega)

theorem natAdd_inj_iff {n m : ℕ} (i j : Fin m) :
    (Fin.natAdd n i : Fin (n + m)) = Fin.natAdd n j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (by have hv := congrArg Fin.val h; simp at hv; omega)
  · intro h; rw [h]

/-! ## Evaluations of the insertion `cvHins` -/

theorem cvHins_left' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) (r : Fin a) :
    cvHins ρ F u (Fin.castAdd 5 r) = F (Fin.castAdd 3 r) := by
  simp [cvHins]

theorem cvHins_right' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) (j : Fin 5) :
    cvHins ρ F u (Fin.natAdd a j)
      = cvIns5 (fun t : Fin 3 => F (Fin.natAdd a (ρ t))) u j := by
  simp [cvHins]

theorem cvHpos_left' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (r : Fin a) :
    cvHpos a ρ (Fin.castAdd 3 r) = Fin.castAdd 5 r := by
  simp [cvHpos]

theorem cvHpos_natAdd' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (t : Fin 3) :
    cvHpos a ρ (Fin.natAdd a t) = Fin.natAdd a (cvEven (ρ.symm t)) := by
  simp [cvHpos]

theorem cvUslot0_eq' (a : ℕ) : cvUslot0 a = Fin.natAdd a (1 : Fin 5) := rfl

theorem cvUslot1_eq' (a : ℕ) : cvUslot1 a = Fin.natAdd a (3 : Fin 5) := rfl

theorem cvHins_uslot0' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    cvHins ρ F u (cvUslot0 a) = u := by
  rw [cvUslot0_eq', cvHins_right', cvIns5_1']

theorem cvHins_uslot1' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    cvHins ρ F u (cvUslot1 a) = u := by
  rw [cvUslot1_eq', cvHins_right', cvIns5_3']

/-- **The entry of the insertion at the position of `s` is `F s`.** -/
theorem cvHins_hpos' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α)
    (s : Fin (a + 3)) : cvHins ρ F u (cvHpos a ρ s) = F s := by
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) =>
    cvHins ρ F u (cvHpos a ρ s) = F s) ?_ ?_
  · intro r
    rw [cvHpos_left', cvHins_left']
  · intro t
    rw [cvHpos_natAdd', cvHins_right', cvIns5_even]
    exact congrArg F (congrArg (Fin.natAdd a) (Equiv.apply_symm_apply ρ t))

/-- The first slot of the insertion of a nonempty block is the first entry of `F`. -/
theorem cvHins_zero' {a : ℕ} (ha : 1 ≤ a) (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    cvHins ρ F u 0 = F 0 := by
  have h0 : (0 : Fin (a + 5)) = Fin.castAdd 5 (⟨0, ha⟩ : Fin a) := by
    ext; simp
  rw [h0, cvHins_left']
  exact congrArg F (Fin.ext rfl)

/-- The tail of the insertion is the insertion of the tail. -/
theorem cvDrop0_cvHins' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin ((a + 1) + 3) → α) (u : α) :
    cvDrop0 (cvHins ρ F u) = cvHins ρ (fun i : Fin (a + 3) => F (Fin.succ i)) u := by
  funext j
  revert j
  refine Fin.addCases (motive := fun j : Fin (a + 5) =>
    cvDrop0 (cvHins ρ F u) j = cvHins ρ (fun i : Fin (a + 3) => F (Fin.succ i)) u j) ?_ ?_
  · intro r
    simp only [cvDrop0]
    rw [castAdd5_succ, cvHins_left', cvHins_left', castAdd3_succ]
  · intro j5
    simp only [cvDrop0]
    rw [natAdd_succ5, cvHins_right', cvHins_right']
    refine congrArg (fun W : Fin 3 → α => cvIns5 W u j5) ?_
    funext t
    refine congrArg F (Fin.ext ?_)
    simp only [cv_natAdd_val', Fin.val_succ]
    omega

/-! ## `Fin.append` and the update of a slot -/

theorem finAppend_update_castAdd {m k : ℕ} (A : Fin m → α) (B : Fin k → α) (r : Fin m) (w : α) :
    Function.update (Fin.append A B) (Fin.castAdd k r) w = Fin.append (Function.update A r w) B := by
  funext j
  revert j
  refine Fin.addCases (motive := fun j : Fin (m + k) =>
    Function.update (Fin.append A B) (Fin.castAdd k r) w j
      = Fin.append (Function.update A r w) B j) ?_ ?_
  · intro r'
    rw [Function.update_apply]
    conv_rhs => rw [Fin.append_left, Function.update_apply]
    by_cases h : r' = r
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh))),
        Fin.append_left]
  · intro j5
    rw [Function.update_apply]
    conv_rhs => rw [Fin.append_right]
    have hne : (Fin.natAdd m j5 : Fin (m + k)) ≠ Fin.castAdd k r := by
      intro hh
      have hv : (Fin.natAdd m j5 : Fin (m + k)).val = (Fin.castAdd k r).val := congrArg Fin.val hh
      have h1 : (Fin.natAdd m j5 : Fin (m + k)).val = m + (j5 : ℕ) := rfl
      have h2 : (Fin.castAdd k r).val = (r : ℕ) := rfl
      omega
    rw [if_neg hne, Fin.append_right]

theorem finAppend_update_natAdd {m k : ℕ} (A : Fin m → α) (B : Fin k → α) (j : Fin k) (w : α) :
    Function.update (Fin.append A B) (Fin.natAdd m j) w = Fin.append A (Function.update B j w) := by
  funext s
  revert s
  refine Fin.addCases (motive := fun s : Fin (m + k) =>
    Function.update (Fin.append A B) (Fin.natAdd m j) w s
      = Fin.append A (Function.update B j w) s) ?_ ?_
  · intro r
    rw [Function.update_apply]
    conv_rhs => rw [Fin.append_left]
    have hne : (Fin.castAdd k r : Fin (m + k)) ≠ Fin.natAdd m j := by
      intro hh
      have hv : (Fin.castAdd k r : Fin (m + k)).val = (Fin.natAdd m j).val := congrArg Fin.val hh
      have h1 : (Fin.castAdd k r : Fin (m + k)).val = (r : ℕ) := rfl
      have h2 : (Fin.natAdd m j).val = m + (j : ℕ) := rfl
      omega
    rw [if_neg hne, Fin.append_left]
  · intro j5
    rw [Function.update_apply]
    conv_rhs => rw [Fin.append_right, Function.update_apply]
    by_cases h : j5 = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh))),
        Fin.append_right]

/-- Updating an even slot of the `5`-block. -/
theorem update_cvIns5_even (Z : Fin 3 → α) (u w : α) (t : Fin 3) :
    Function.update (cvIns5 Z u) (cvEven t) w = cvIns5 (Function.update Z t w) u := by
  funext j
  rw [Function.update_apply]
  by_cases hj : j = cvEven t
  · rw [if_pos hj, hj, cvIns5_even, Function.update_self]
  · rw [if_neg hj]
    fin_cases t <;> fin_cases j <;> simp_all [cvIns5, cvEven]

/-- **The insertion commutes with updating a slot of the arity-`3` block.** -/
theorem cvHins_update' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (s : Fin (a + 3))
    (w u : α) :
    cvHins ρ (Function.update F s w) u = Function.update (cvHins ρ F u) (cvHpos a ρ s) w := by
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) =>
    cvHins ρ (Function.update F s w) u
      = Function.update (cvHins ρ F u) (cvHpos a ρ s) w) ?_ ?_
  · intro r
    rw [cvHpos_left']
    show Fin.append (fun r' : Fin a => (Function.update F (Fin.castAdd 3 r) w)
          (Fin.castAdd 3 r'))
        (cvIns5 (fun t => (Function.update F (Fin.castAdd 3 r) w) (Fin.natAdd a (ρ t))) u)
      = Function.update (Fin.append (fun r' : Fin a => F (Fin.castAdd 3 r'))
          (cvIns5 (fun t => F (Fin.natAdd a (ρ t))) u)) (Fin.castAdd 5 r) w
    rw [finAppend_update_castAdd]
    congr 1
    · funext r'
      rw [Function.update_apply, Function.update_apply]
      by_cases h : r' = r
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh)))]
    · refine congrArg (fun W : Fin 3 → α => cvIns5 W u) ?_
      funext t
      rw [Function.update_apply]
      have hne : (Fin.natAdd a (ρ t) : Fin (a + 3)) ≠ Fin.castAdd 3 r := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [cv_natAdd_val', cv_castAdd_val'] at hv
        omega
      rw [if_neg hne]
  · intro t
    rw [cvHpos_natAdd']
    show Fin.append (fun r' : Fin a => (Function.update F (Fin.natAdd a t) w)
          (Fin.castAdd 3 r'))
        (cvIns5 (fun t' => (Function.update F (Fin.natAdd a t) w) (Fin.natAdd a (ρ t'))) u)
      = Function.update (Fin.append (fun r' : Fin a => F (Fin.castAdd 3 r'))
          (cvIns5 (fun t' => F (Fin.natAdd a (ρ t'))) u))
          (Fin.natAdd a (cvEven (ρ.symm t))) w
    rw [finAppend_update_natAdd]
    congr 1
    · funext r'
      rw [Function.update_apply]
      have hne : (Fin.castAdd 3 r' : Fin (a + 3)) ≠ Fin.natAdd a t := by
        intro hh
        have hv := congrArg Fin.val hh
        simp at hv
        omega
      rw [if_neg hne]
    · rw [update_cvIns5_even]
      refine congrArg (fun W : Fin 3 → α => cvIns5 W u) ?_
      funext t'
      rw [Function.update_apply, Function.update_apply]
      by_cases h : t' = ρ.symm t
      · subst h
        rw [if_pos rfl, if_pos (congrArg (Fin.natAdd a) (Equiv.apply_symm_apply ρ t))]
      · have hne : (Fin.natAdd a (ρ t') : Fin (a + 3)) ≠ Fin.natAdd a t :=
          fun hh => h ((Equiv.eq_symm_apply ρ).mpr
            ((natAdd_inj_iff (n := a) (ρ t') t).mp hh))
        rw [if_neg h, if_neg hne]

/-! ## The two frame slots are not in the arity-`3` block -/

theorem cvHpos_ne_uslot0' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (s : Fin (a + 3)) :
    cvHpos a ρ s ≠ cvUslot0 a := by
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) => cvHpos a ρ s ≠ cvUslot0 a) ?_ ?_
  · intro r h
    rw [cvHpos_left', cvUslot0_eq'] at h
    have hv : (Fin.castAdd 5 r : Fin (a + 5)).val = (cvUslot0 a).val := congrArg Fin.val h
    have h1 : (Fin.castAdd 5 r : Fin (a + 5)).val = (r : ℕ) := rfl
    have h2 : (cvUslot0 a).val = a + 1 := rfl
    omega
  · intro t h
    rw [cvHpos_natAdd', cvUslot0_eq'] at h
    have hv : (Fin.natAdd a (cvEven (ρ.symm t)) : Fin (a + 5)).val = (cvUslot0 a).val :=
      congrArg Fin.val h
    have h1 : (Fin.natAdd a (cvEven (ρ.symm t)) : Fin (a + 5)).val
        = a + 2 * (ρ.symm t).val := rfl
    have h2 : (cvUslot0 a).val = a + 1 := rfl
    omega

theorem cvHpos_ne_uslot1' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (s : Fin (a + 3)) :
    cvHpos a ρ s ≠ cvUslot1 a := by
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) => cvHpos a ρ s ≠ cvUslot1 a) ?_ ?_
  · intro r h
    rw [cvHpos_left', cvUslot1_eq'] at h
    have hv : (Fin.castAdd 5 r : Fin (a + 5)).val = (cvUslot1 a).val := congrArg Fin.val h
    have h1 : (Fin.castAdd 5 r : Fin (a + 5)).val = (r : ℕ) := rfl
    have h2 : (cvUslot1 a).val = a + 3 := rfl
    omega
  · intro t h
    rw [cvHpos_natAdd', cvUslot1_eq'] at h
    have hv : (Fin.natAdd a (cvEven (ρ.symm t)) : Fin (a + 5)).val = (cvUslot1 a).val :=
      congrArg Fin.val h
    have h1 : (Fin.natAdd a (cvEven (ρ.symm t)) : Fin (a + 5)).val
        = a + 2 * (ρ.symm t).val := rfl
    have h2 : (cvUslot1 a).val = a + 3 := rfl
    omega

/-! ## Reindexing a sum over the slots of the insertion -/

/-- The sum over the five slots of the `5`-block is the sum over the three (permuted) free slots
plus the two frame slots. -/
theorem cv_sum_univ_five' (ρ : Fin 3 ≃ Fin 3) (H : Fin 5 → ℝ) :
    (∑ j : Fin 5, H j) = (∑ t : Fin 3, H (cvEven (ρ.symm t))) + H 1 + H 3 := by
  have h1 : (∑ t : Fin 3, H (cvEven (ρ.symm t))) = ∑ t : Fin 3, H (cvEven t) := by
    refine Fintype.sum_equiv ρ.symm _ _ (fun t => ?_)
    rfl
  rw [h1, Fin.sum_univ_three, Fin.sum_univ_five]
  norm_num [cvEven]
  ring

/-- **The reindexing of a sum over the slots of the insertion.** -/
theorem cv_sum_univ_Hins' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (H : Fin (a + 5) → ℝ) :
    (∑ j : Fin (a + 5), H j)
      = (∑ s : Fin (a + 3), H (cvHpos a ρ s)) + H (cvUslot0 a) + H (cvUslot1 a) := by
  rw [Fin.sum_univ_add (f := H),
    Fin.sum_univ_add (f := fun s : Fin (a + 3) => H (cvHpos a ρ s))]
  have h1 : (∑ r : Fin a, H (Fin.castAdd 5 r))
      = ∑ r : Fin a, H (cvHpos a ρ (Fin.castAdd 3 r)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cvHpos_left']
  rw [h1, cvUslot0_eq', cvUslot1_eq']
  have h2 : (∑ j : Fin 5, H (Fin.natAdd a j))
      = (∑ t : Fin 3, H (cvHpos a ρ (Fin.natAdd a t))) + H (Fin.natAdd a 1)
        + H (Fin.natAdd a 3) := by
    rw [cv_sum_univ_five' ρ (fun j : Fin 5 => H (Fin.natAdd a j))]
    have h3 : (∑ t : Fin 3, H (Fin.natAdd a (cvEven (ρ.symm t))))
        = ∑ t : Fin 3, H (cvHpos a ρ (Fin.natAdd a t)) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cvHpos_natAdd']
    rw [h3]
  rw [h2]
  ring

/-! ## The two-frame insertion -/

theorem cvUslot0_ne_cvUslot1' (a : ℕ) : cvUslot0 a ≠ cvUslot1 a := by
  intro h
  have hv := congrArg Fin.val h
  rw [cvUslot0_eq', cvUslot1_eq'] at hv
  simp only [cv_natAdd_val'] at hv
  omega

/-- **The insertion with two fields in the frame slots.**  `cvHins2 ρ F A B` is the tuple
`cvHins ρ F A` with the second frame slot `cvUslot1 a` filled by `B`. -/
noncomputable def cvHins2 {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α) :
    Fin (a + 5) → α :=
  Function.update (cvHins ρ F A) (cvUslot1 a) B

theorem cvHins2_uslot0 {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α) :
    cvHins2 ρ F A B (cvUslot0 a) = A := by
  rw [cvHins2, Function.update_of_ne (cvUslot0_ne_cvUslot1' a)]
  exact cvHins_uslot0' ρ F A

theorem cvHins2_uslot1 {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α) :
    cvHins2 ρ F A B (cvUslot1 a) = B := by
  rw [cvHins2, Function.update_self]

theorem cvHins2_hpos {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α)
    (s : Fin (a + 3)) : cvHins2 ρ F A B (cvHpos a ρ s) = F s := by
  rw [cvHins2, Function.update_of_ne (cvHpos_ne_uslot1' ρ s)]
  exact cvHins_hpos' ρ F A s

/-- `cvHins` agrees with itself off the two frame slots. -/
theorem cvHins_agree_off' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α)
    (j : Fin (a + 5)) (h0 : j ≠ cvUslot0 a) (h1 : j ≠ cvUslot1 a) :
    cvHins ρ F A j = cvHins ρ F B j := by
  revert j
  refine Fin.addCases (motive := fun j : Fin (a + 5) => j ≠ cvUslot0 a → j ≠ cvUslot1 a →
    cvHins ρ F A j = cvHins ρ F B j) ?_ ?_
  · intro r h0 h1
    rw [cvHins_left', cvHins_left']
  · intro j5 h0 h1
    rw [cvHins_right', cvHins_right']
    refine cvIns5_agree_ne _ A B j5 ?_ ?_
    · intro hh; exact h0 (by rw [hh, cvUslot0_eq'])
    · intro hh; exact h1 (by rw [hh, cvUslot1_eq'])

/-- **Updating the first frame slot** of `cvHins` turns the insertion into `cvHins2`. -/
theorem update_cvHins_uslot0' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α) :
    Function.update (cvHins ρ F A) (cvUslot0 a) B = cvHins2 ρ F B A := by
  funext j
  by_cases h0 : j = cvUslot0 a
  · rw [h0, Function.update_self, cvHins2_uslot0]
  · by_cases h1 : j = cvUslot1 a
    · rw [Function.update_of_ne h0, h1, cvHins2_uslot1, cvHins_uslot1']
    · rw [Function.update_of_ne h0]
      rw [show cvHins2 ρ F B A j = cvHins ρ F B j from by
        rw [cvHins2, Function.update_of_ne h1]]
      exact (cvHins_agree_off' ρ F B A j h0 h1).symm

/-- **Updating the second frame slot** of `cvHins`. -/
theorem update_cvHins_uslot1' {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (A B : α) :
    Function.update (cvHins ρ F A) (cvUslot1 a) B = cvHins2 ρ F A B := rfl

/-- Updating a slot of a `Fin (3+n)`-tuple, transported to the `Fin (n+3)` world. -/
theorem update_comp_cvCast3 {n : ℕ} (H : Fin (3 + n) → α) (s : Fin (3 + n)) (w : α) :
    (fun i' : Fin (n + 3) => (Function.update H s w) (cvCast3 n i'))
      = Function.update (fun i' : Fin (n + 3) => H (cvCast3 n i')) (cvCast3' n s) w := by
  funext i'
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i' = cvCast3' n s
  · rw [if_pos h, h, cvCast3_cast3', if_pos rfl]
  · rw [if_neg h, if_neg (fun hh => h ((cvCast3'_cvCast3 (a := n) i').symm.trans
      (congrArg (cvCast3' n) hh)))]

/-- **`Function.update` commutes with the pointwise evaluation of a tuple of fields.** -/
theorem update_pointwise {ι : Type*} [DecidableEq ι]
    (T : ι → Work.Diff.EXT.TField (I := I) (M := M)) (i : ι)
    (B : Work.Diff.EXT.TField (I := I) (M := M)) (x : M) :
    (fun r => (Function.update T i B) r x) = Function.update (fun r => T r x) i (B x) := by
  funext r
  rw [Function.update_apply, Function.update_apply]
  by_cases h : r = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-! ## Smoothness of the inserted tuples -/

/-- The entries of `cvHins` are smooth if those of `F` and the inserted field are. -/
theorem cvHins_smooth {a : ℕ} {ρ : Fin 3 ≃ Fin 3}
    (F : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ s, SmoothF (F s)) {A : Work.Diff.EXT.TField (I := I) (M := M)} (hA : SmoothF A) :
    ∀ j : Fin (a + 5), SmoothF (cvHins ρ F A j) := by
  intro j
  refine Fin.addCases (motive := fun j : Fin (a + 5) => SmoothF (cvHins ρ F A j)) ?_ ?_ j
  · intro r
    rw [cvHins_left']
    exact hF _
  · intro j5
    rw [cvHins_right']
    fin_cases j5
    · exact hF _
    · exact hA
    · exact hF _
    · exact hA
    · exact hF _

/-! ## The frame-traced tower operator -/

/-- **The level-`n` frame-traced tower operator.**  `TOp g n ρ u G y` is the level-`(n+1)` tower of
`g` evaluated on the tuple in which the `n` differentiation slots are `G 0, …, G (n-1)`, the
arity-`3` block is permuted by `ρ` and the field `u` fills the two traced curvature slots. -/
noncomputable def TOp (g : SMet I M) (n : ℕ) (ρ : Fin 3 ≃ Fin 3)
    (u : Work.Diff.EXT.TField (I := I) (M := M)) :
    (Fin (n + 3) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun G y => ckt g (n + 1) (cvHins ρ G u) y

@[simp] theorem TOp_apply (g : SMet I M) (n : ℕ) (ρ : Fin 3 ≃ Fin 3)
    (u : Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (n + 3) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) :
    TOp g n ρ u G y = ckt g (n + 1) (cvHins ρ G u) y := rfl

/-- `TOp` reindexed to the tuple convention of `jetAll` (whose tuples are `Fin (3+n)`). -/
noncomputable def TOpJ (g : SMet I M) (n : ℕ) (ρ : Fin 3 ≃ Fin 3)
    (u : Work.Diff.EXT.TField (I := I) (M := M)) :
    (Fin (3 + n) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun G y => TOp g n ρ u (fun i : Fin (n + 3) => G (cvCast3 n i)) y

theorem TOpJ_apply' (g : SMet I M) (n : ℕ) (ρ : Fin 3 ≃ Fin 3)
    (u : Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (3 + n) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) :
    TOpJ g n ρ u G y = ckt g (n + 1) (cvHins ρ (fun i : Fin (n + 3) => G (cvCast3 n i)) u) y :=
  rfl


end Trace
end Work.Diff.EXT.evolX
