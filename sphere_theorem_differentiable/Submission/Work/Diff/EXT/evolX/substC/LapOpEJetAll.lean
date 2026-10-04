import Mathlib
import Submission.Work.Diff.EXT.evolX.substC.LapOpEDefs
import Submission.Work.Diff.EXT.lapComm_tower
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- Splitting a sum over `Fin (A + 2 + B)` after the `A` initial and before the `B` final terms. -/
theorem sum_fin_split_midC {A B : ℕ} (f : Fin (A + 2 + B) → ℝ) :
    (∑ u : Fin (A + 2 + B), f u)
      = (∑ s : Fin A, f (Fin.castAdd B (Fin.castAdd 2 s)))
        + f (Fin.castAdd B (Fin.natAdd A 0)) + f (Fin.castAdd B (Fin.natAdd A 1))
        + (∑ s : Fin B, f (Fin.natAdd (A + 2) s)) := by
  rw [Fin.sum_univ_add (a := A + 2) (b := B), Fin.sum_univ_add (a := A) (b := 2),
    Fin.sum_univ_two]
  ring

/-- Sum over `Fin ((m+2+n)+4)` split at the two frame slots `n`, `n+1`, in value form. -/
theorem sum_fin_skip_rangeC {m n : ℕ} (h h' : ℕ → ℝ)
    (hn : ∀ i, i < n → h' i = h i)
    (hs : ∀ i, i < (m + 2 + n) + 4 → n + 2 ≤ i → h' i = h (i - 2)) :
    (∑ u : Fin ((m + 2 + n) + 4), h' ↑u)
      = (∑ s : Fin (m + 4 + n), h ↑s) + h' n + h' (n + 1) := by
  have hL : (∑ u : Fin ((m + 2 + n) + 4), h' ↑u)
      = (∑ i ∈ Finset.range n, h i) + h' n + h' (n + 1)
        + (∑ i ∈ Finset.range (m + 4), h (n + i)) := by
    rw [Fin.sum_univ_eq_sum_range h' ((m + 2 + n) + 4),
      show (m + 2 + n) + 4 = n + 2 + (m + 4) from by omega,
      Finset.sum_range_add (n := n + 2) (m := m + 4),
      Finset.sum_range_add (n := n) (m := 2), Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.add_zero]
    have h1 : (∑ x ∈ Finset.range n, h' x) = ∑ x ∈ Finset.range n, h x :=
      Finset.sum_congr rfl (fun x hx => hn x (Finset.mem_range.mp hx))
    have h2 : (∑ x ∈ Finset.range (m + 4), h' (n + 2 + x))
        = ∑ x ∈ Finset.range (m + 4), h (n + x) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [hs (n + 2 + x) (by have := Finset.mem_range.mp hx; omega) (by omega)]
      congr 1
      omega
    rw [h1, h2]
    ring
  have hR : (∑ s : Fin (m + 4 + n), h ↑s)
      = (∑ i ∈ Finset.range n, h i) + (∑ i ∈ Finset.range (m + 4), h (n + i)) := by
    rw [Fin.sum_univ_eq_sum_range h (m + 4 + n),
      show m + 4 + n = n + (m + 4) from by omega, Finset.sum_range_add (n := n) (m := m + 4)]
  rw [hL, hR]
  ring

/-- The entries of `insTC` are smooth if the inserted fields and `G` are. -/
theorem smoothTField_insTC {m n : ℕ} {A B : Work.Diff.EXT.TField (I := I) (M := M)}
    (hA : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B)
    (G : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    ∀ r : Fin ((m + 2 + n) + 4), Work.Diff.GE.SmoothFieldT (I := I) (M := M)
      (insTC (I := I) (M := M) m n A B G r) := by
  intro r
  by_cases hr : (r : ℕ) < n
  · rw [insT_apply_ltC (A := A) (B := B) (F := G) (r := r) hr]; exact hG _
  · by_cases h1 : (r : ℕ) = n
    · rw [show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := G)]; exact hA
    · by_cases h2 : (r : ℕ) = n + 1
      · rw [show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := G)]; exact hB
      · rw [insT_apply_geC (A := A) (B := B) (F := G) (r := r) (by omega)]; exact hG _

/-- The head of the `(n+1)`-level insertion is the head of `F`. -/
theorem insT_succ_headC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    insTC (I := I) (M := M) m (n + 1) A B F 0 = F 0 := by
  rw [insT_apply_ltC (A := A) (B := B) (F := F) (r := (0 : Fin (((m + 2) + (n + 1)) + 4)))
    (by simp)]
  rfl

/-- The tail of the `(n+1)`-level insertion is the `n`-level insertion of the tail. -/
theorem insT_succ_tailC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun r : Fin ((m + 2 + n) + 4) => insTC (I := I) (M := M) m (n + 1) A B F r.succ)
      = insTC (I := I) (M := M) m n A B (fun s : Fin (m + 4 + n) => F s.succ) := by
  funext r
  by_cases hr : (r : ℕ) < n
  · rw [insT_apply_ltC (A := A) (B := B) (F := F) (r := r.succ)
        (by simp only [Fin.val_succ]; omega),
      insT_apply_ltC (A := A) (B := B) (F := fun s : Fin (m + 4 + n) => F s.succ) (r := r) hr]
    rfl
  · by_cases h1 : (r : ℕ) = n
    · have hrn : (r.succ : Fin ((m + 2 + (n + 1)) + 4)) = ⟨n + 1, by omega⟩ := by
        ext; simp only [Fin.val_succ, Fin.val_mk]; omega
      rw [hrn, insT_apply_leftC (A := A) (B := B) (F := F),
        show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := fun s : Fin (m + 4 + n) => F s.succ)]
    · by_cases h2 : (r : ℕ) = n + 1
      · have hrn : (r.succ : Fin ((m + 2 + (n + 1)) + 4)) = ⟨n + 2, by omega⟩ := by
          ext; simp only [Fin.val_succ, Fin.val_mk]; omega
        rw [hrn, insT_apply_rightC (A := A) (B := B) (F := F),
          show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := fun s : Fin (m + 4 + n) => F s.succ)]
      · rw [insT_apply_geC (A := A) (B := B) (F := F) (r := r.succ)
            (by simp only [Fin.val_succ]; omega),
          insT_apply_geC (A := A) (B := B) (F := fun s : Fin (m + 4 + n) => F s.succ)
            (r := r) (by omega)]
        refine congrArg F (Fin.ext ?_)
        simp only [Fin.val_mk, Fin.val_succ]
        omega

/-- Updating the left frame slot of `insTC`. -/
theorem insT_update_frame_leftC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (insTC (I := I) (M := M) m n A B F) ⟨n, by omega⟩ W
      = insTC (I := I) (M := M) m n W B F := by
  funext r
  rw [Function.update_apply]
  by_cases hr : (r : ℕ) < n
  · have hrne : r ≠ (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
      intro hh
      have h' : (r : ℕ) = n := by simpa only [Fin.val_mk] using congrArg Fin.val hh
      omega
    rw [if_neg hrne, insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hr,
      insT_apply_ltC (A := W) (B := B) (F := F) (r := r) hr]
  · by_cases h1 : (r : ℕ) = n
    · rw [show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1, if_pos rfl,
        insT_apply_leftC (A := W) (B := B) (F := F)]
    · by_cases h2 : (r : ℕ) = n + 1
      · have hrne : r ≠ (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
          intro hh
          have h' : (r : ℕ) = n := by simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega
        rw [if_neg hrne,
          show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := F),
          insT_apply_rightC (A := W) (B := B) (F := F)]
      · have hrne : r ≠ (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
          intro hh
          have h' : (r : ℕ) = n := by simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega
        rw [if_neg hrne,
          insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := W) (B := B) (F := F) (r := r) (by omega)]

/-- Updating the right frame slot of `insTC`. -/
theorem insT_update_frame_rightC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (insTC (I := I) (M := M) m n A B F) ⟨n + 1, by omega⟩ W
      = insTC (I := I) (M := M) m n A W F := by
  funext r
  rw [Function.update_apply]
  by_cases hr : (r : ℕ) < n
  · have hrne : r ≠ (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
      intro hh
      have h' : (r : ℕ) = n + 1 := by simpa only [Fin.val_mk] using congrArg Fin.val hh
      omega
    rw [if_neg hrne, insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hr,
      insT_apply_ltC (A := A) (B := W) (F := F) (r := r) hr]
  · by_cases h1 : (r : ℕ) = n
    · have hrne : r ≠ (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
        intro hh
        have h' : (r : ℕ) = n + 1 := by simpa only [Fin.val_mk] using congrArg Fin.val hh
        omega
      rw [if_neg hrne,
        show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := F),
        insT_apply_leftC (A := A) (B := W) (F := F)]
    · by_cases h2 : (r : ℕ) = n + 1
      · rw [show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2, if_pos rfl,
          insT_apply_rightC (A := A) (B := W) (F := F)]
      · have hrne : r ≠ (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) := by
          intro hh
          have h' : (r : ℕ) = n + 1 := by simpa only [Fin.val_mk] using congrArg Fin.val hh
          omega
        rw [if_neg hrne,
          insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := A) (B := W) (F := F) (r := r) (by omega)]


/-- `insTC` above the frame slots, with the index written in the arithmetic form `j`. -/
theorem insT_apply_ge'C {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (j : ℕ) (hj : j < (m + 2 + n) + 4) (hge : n + 2 ≤ j) :
    insTC (I := I) (M := M) m n A B F ⟨j, hj⟩ = F ⟨j - 2, by omega⟩ :=
  insT_apply_geC (A := A) (B := B) (F := F) (r := ⟨j, hj⟩) hge

/-- The update lemma above the frame slots, with the index written in the arithmetic form `j`. -/
theorem insT_update_of_ge'C {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (j : ℕ) (hj : j < (m + 2 + n) + 4) (hge : n + 2 ≤ j)
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (insTC (I := I) (M := M) m n A B F) ⟨j, hj⟩ W
      = insTC (I := I) (M := M) m n A B (Function.update F ⟨j - 2, by omega⟩ W) := by
  have h1 : (⟨j, hj⟩ : Fin ((m + 2 + n) + 4)) = ⟨(j - 2) + 2, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_mk]; omega)
  rw [h1, insT_update_of_geC (m := m) (n := n) (A := A) (B := B) (F := F)
    (s := ⟨j - 2, by omega⟩) (show n ≤ ((⟨j - 2, by omega⟩ : Fin (m + 4 + n)) : ℕ)
      from by show n ≤ j - 2; omega)]


/-- The pointwise form of `insT_succ_tailC`. -/
theorem insT_succ_tail_applyC {m n : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (s : Fin ((m + 2 + n) + 4)) :
    insTC (I := I) (M := M) m (n + 1) A B F s.succ
      = insTC (I := I) (M := M) m n A B (fun r : Fin (m + 4 + n) => F r.succ) s := by
  have h := insT_succ_tailC (I := I) (M := M) (m := m) (n := n) (A := A) (B := B) (F := F)
  exact congrFun h s

/-- The per-`i` identity: the correction sum of `extStep (SOpC m n)` and the correction sum of
`ckt (k+1) (insTC m (n+1) ...)` differ exactly by the two frame-motion terms. -/
theorem SOp_step_bracketC {m n : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (i : Fin (Module.finrank ℝ E))
    (G : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G r))
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X) (y : M) :
    (∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
        (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
          (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u) X)) y)
      = (∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
          (insTC (I := I) (M := M) m n (Ef i) (Ef i)
            (Function.update G s (Work.Diff.EXT.dirF g (G s) X))) y)
        + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) G) y
        + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) G) y := by
  set h : ℕ → ℝ := fun s => if hs : s < m + 4 + n then Work.Diff.EXT.ckt g (m + 2 + n)
    (insTC (I := I) (M := M) m n (Ef i) (Ef i) (Function.update G ⟨s, hs⟩
      (Work.Diff.EXT.dirF g (G ⟨s, hs⟩) X))) y else 0 with hhdef
  set h' : ℕ → ℝ := fun u => if hu : u < (m + 2 + n) + 4 then Work.Diff.EXT.ckt g (m + 2 + n)
    (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) ⟨u, hu⟩
      (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G ⟨u, hu⟩) X)) y
    else 0 with hh'def
  have hleft : (∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
        (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
          (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u) X)) y)
      = ∑ u : Fin ((m + 2 + n) + 4), h' ↑u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hh'def]
    beta_reduce
    rw [dif_pos u.isLt]
  have hright : (∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
          (insTC (I := I) (M := M) m n (Ef i) (Ef i)
            (Function.update G s (Work.Diff.EXT.dirF g (G s) X))) y)
      = ∑ s : Fin (m + 4 + n), h ↑s := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hhdef]
    beta_reduce
    rw [dif_pos s.isLt]
  have hframe1 : h' n = Work.Diff.EXT.ckt g (m + 2 + n)
      (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) G) y := by
    rw [hh'def]
    beta_reduce
    rw [dif_pos (show n < (m + 2 + n) + 4 by omega)]
    rw [insT_apply_leftC (A := Ef i) (B := Ef i) (F := G)]
    rw [insT_update_frame_leftC (m := m) (n := n) (A := Ef i) (B := Ef i) (F := G)
      (W := Work.Diff.EXT.dirF g (Ef i) X)]
  have hframe2 : h' (n + 1) = Work.Diff.EXT.ckt g (m + 2 + n)
      (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) G) y := by
    rw [hh'def]
    beta_reduce
    rw [dif_pos (show n + 1 < (m + 2 + n) + 4 by omega)]
    rw [insT_apply_rightC (A := Ef i) (B := Ef i) (F := G)]
    rw [insT_update_frame_rightC (m := m) (n := n) (A := Ef i) (B := Ef i) (F := G)
      (W := Work.Diff.EXT.dirF g (Ef i) X)]
  have hn : ∀ j, j < n → h' j = h j := by
    intro j hj
    rw [hh'def]
    beta_reduce
    rw [dif_pos (show j < (m + 2 + n) + 4 by omega)]
    rw [hhdef]
    beta_reduce
    rw [dif_pos (show j < m + 4 + n by omega)]
    rw [insT_update_of_ltC (m := m) (n := n) (A := Ef i) (B := Ef i) (F := G)
      (s := ⟨j, by omega⟩) hj]
    rw [insT_apply_ltC (A := Ef i) (B := Ef i) (F := G) (r := ⟨j, by omega⟩) hj]
  have hs : ∀ j, j < (m + 2 + n) + 4 → n + 2 ≤ j → h' j = h (j - 2) := by
    intro j hj hge
    rw [hh'def]
    beta_reduce
    rw [dif_pos hj]
    rw [hhdef]
    beta_reduce
    rw [dif_pos (show j - 2 < m + 4 + n by omega)]
    rw [insT_apply_ge'C (A := Ef i) (B := Ef i) (F := G) (j := j) hj hge]
    rw [insT_update_of_ge'C (m := m) (n := n) (A := Ef i) (B := Ef i) (F := G) (j := j) hj hge]
  rw [hleft, hright, sum_fin_skip_rangeC (m := m) (n := n) h h' hn hs, hframe1, hframe2]

/-- **The step of the frame-traced tower.**  One `extStep` moves the frame slots of `SOpC` from
`n, n+1` to `n+1, n+2`; the additional terms produced by the two frame slots cancel by the
antisymmetry of the frame velocities (`hcancel`). -/
theorem SOp_stepC {m n : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (F : Fin (m + 4 + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) {x : M}
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => Ef i y))
    (hcancel : ∀ y : M, (∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => Ef i z)) →
      (∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i)
              (fun s : Fin (m + 4 + n) => F s.succ)) y
          + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0))
              (fun s : Fin (m + 4 + n) => F s.succ)) y)) = 0) :
    Work.Diff.EXT.extStep (I := I) (M := M) g (SOpC g m n Ef) F
      =ᶠ[𝓝 x] SOpC g m (n + 1) Ef F := by
  set G : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun s => F s.succ with hGdef
  have hGs : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G s) := fun s => hF s.succ
  obtain ⟨V, hVopen, hxV, hV⟩ : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ z ∈ V, Submission.Diff.IsONFrame g z (fun i => Ef i z) := by
    obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp hON
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    exact ⟨V, hVopen, hxV, fun z hz => hUsub z (hVU hz)⟩
  have hVmem : V ∈ 𝓝 x := mem_nhds_iff.mpr ⟨V, subset_rfl, hVopen, hxV⟩
  filter_upwards [hVmem] with y hyV
  have hVy : V ∈ 𝓝 y := mem_nhds_iff.mpr ⟨V, subset_rfl, hVopen, hyV⟩
  have hgerm : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => Ef i z) :=
    Filter.mem_of_superset hVy (fun z hz => hV z hz)
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.ckt g (m + 2 + (n + 1))
          (insTC (I := I) (M := M) m (n + 1) (Ef i) (Ef i) F) y
        = mvfderiv I (fun z : M => Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) y (F 0 y)
          - ∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
              (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
                (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u)
                  (F 0))) y := by
    intro i
    have heta : ∀ f : Fin ((m + 2 + n) + 4) → Work.Diff.EXT.TField (I := I) (M := M),
        (fun x => f x) = f := fun f => rfl
    have hcs := Work.Diff.EXT.ckt_succ (I := I) (M := M) g (m + 2 + n)
      (insTC (I := I) (M := M) m (n + 1) (Ef i) (Ef i) F)
    rw [show Work.Diff.EXT.ckt g (m + 2 + (n + 1))
          (insTC (I := I) (M := M) m (n + 1) (Ef i) (Ef i) F)
        = Work.Diff.EXT.ckt g ((m + 2 + n) + 1)
          (insTC (I := I) (M := M) m (n + 1) (Ef i) (Ef i) F) from rfl, hcs]
    simp only [insT_succ_tail_applyC (I := I) (M := M) (m := m) (n := n) (A := Ef i) (B := Ef i)
        (F := F), insT_succ_headC (I := I) (M := M) (m := m) (n := n) (A := Ef i) (B := Ef i) (F := F),
      ← hGdef, heta (insTC (I := I) (M := M) m n (Ef i) (Ef i) G)]
    conv_lhs => rw [show Work.Diff.EXT.ckt g (m + 2 + n) (insTC (I := I) (M := M) m n (Ef i) (Ef i) G)
        = (fun z : M => Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) from rfl]
    rw [Pi.sub_apply, Finset.sum_apply]
  have hmv : mvfderiv I (fun z : M => ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
        (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) y (F 0 y)
      = ∑ i : Fin (Module.finrank ℝ E), mvfderiv I (fun z : M => Work.Diff.EXT.ckt g (m + 2 + n)
          (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) y (F 0 y) := by
    rw [Work.Diff.GE.Kato3.mvfderiv_sum]
    intro i
    exact (Work.Diff.EXT.tensProp_all hLC g (m + 2 + n) _
      (smoothTField_insTC (I := I) (M := M) (hEf i) (hEf i) G hGs)).1
  have hL : mvfderiv I (SOpC g m n Ef G) y (F 0 y)
        - ∑ s : Fin (m + 4 + n), SOpC g m n Ef (Function.update G s
            (Work.Diff.EXT.dirF g (G s) (F 0))) y
      = (∑ i : Fin (Module.finrank ℝ E), mvfderiv I (fun z : M => Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) y (F 0 y))
        - ∑ s : Fin (m + 4 + n), ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i)
              (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y := by
    have hmvf : mvfderiv I (SOpC g m n Ef G) y (F 0 y)
        = mvfderiv I (fun z : M => ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) z) y (F 0 y) := by
      congr 1
    have hcorr : (∑ s : Fin (m + 4 + n), SOpC g m n Ef (Function.update G s
          (Work.Diff.EXT.dirF g (G s) (F 0))) y)
        = ∑ s : Fin (m + 4 + n), ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i)
              (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y :=
      Finset.sum_congr rfl (fun s _ => by simp only [SOpC])
    rw [hmvf, hmv, hcorr]
  have hkey : (∑ s : Fin (m + 4 + n), ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
          (insTC (I := I) (M := M) m n (Ef i) (Ef i)
            (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
            (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
              (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u) (F 0))) y := by
    have hb : ∀ i : Fin (Module.finrank ℝ E),
        (∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
            (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
              (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u) (F 0))) y)
          = ((∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
            + (Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
              + Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y)) := by
      intro i
      have h := SOp_step_bracketC (I := I) (M := M) hLC g Ef hEf i G hGs (F 0) (hF 0) y
      rw [h, add_assoc]
    have hfr : (∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i)
              (fun s : Fin (m + 4 + n) => F s.succ)) y
          + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0))
              (fun s : Fin (m + 4 + n) => F s.succ)) y)) = 0 := hcancel y hgerm
    have hfr' : (∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
          + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y)) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hfr
      rw [← hGdef]
    have h1 : (∑ i : Fin (Module.finrank ℝ E), ∑ u : Fin ((m + 2 + n) + 4), Work.Diff.EXT.ckt g (m + 2 + n)
            (Function.update (insTC (I := I) (M := M) m n (Ef i) (Ef i) G) u
              (Work.Diff.EXT.dirF g (insTC (I := I) (M := M) m n (Ef i) (Ef i) G u) (F 0))) y)
        = ∑ i : Fin (Module.finrank ℝ E), ((∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
            + (Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
              + Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y)) :=
      Finset.sum_congr rfl (fun i _ => hb i)
    have h2 : (∑ i : Fin (Module.finrank ℝ E), ((∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
            + (Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
              + Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y)))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Ef i)
              (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y := by
      calc (∑ i : Fin (Module.finrank ℝ E), ((∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
            + (Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
              + Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y)))
          = (∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y)
            + ∑ i : Fin (Module.finrank ℝ E),
              (Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) (F 0)) (Ef i) G) y
              + Work.Diff.EXT.ckt g (m + 2 + n)
                (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) (F 0)) G) y) :=
            Finset.sum_add_distrib
        _ = (∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y) + 0 := by
            rw [hfr']
        _ = ∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (m + 4 + n), Work.Diff.EXT.ckt g (m + 2 + n)
              (insTC (I := I) (M := M) m n (Ef i) (Ef i)
                (Function.update G s (Work.Diff.EXT.dirF g (G s) (F 0)))) y := add_zero _
    exact (Finset.sum_comm).trans (h2.symm.trans h1.symm)
  rw [Work.Diff.EXT.extStep]
  rw [← hGdef, hL, show SOpC g m (n + 1) Ef F y
      = ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + (n + 1))
          (insTC (I := I) (M := M) m (n + 1) (Ef i) (Ef i) F) y from rfl,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, hkey]

/-- Off-slot agreement of `insTC` in the left frame slot. -/
theorem insT_agree_off_leftC {m n : ℕ} (A A' B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin ((m + 2 + n) + 4)) (hr : r ≠ (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4))) :
    insTC (I := I) (M := M) m n A B F r = insTC (I := I) (M := M) m n A' B F r := by
  by_cases hlt : (r : ℕ) < n
  · rw [insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hlt,
        insT_apply_ltC (A := A') (B := B) (F := F) (r := r) hlt]
  · by_cases h1 : (r : ℕ) = n
    · exact absurd (Fin.ext h1) hr
    · by_cases h2 : (r : ℕ) = n + 1
      · rw [show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
          insT_apply_rightC (A := A) (B := B) (F := F),
          insT_apply_rightC (A := A') (B := B) (F := F)]
      · rw [insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := A') (B := B) (F := F) (r := r) (by omega)]

/-- Off-slot agreement of `insTC` in the right frame slot. -/
theorem insT_agree_off_rightC {m n : ℕ} (A B B' : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin ((m + 2 + n) + 4)) (hr : r ≠ (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4))) :
    insTC (I := I) (M := M) m n A B F r = insTC (I := I) (M := M) m n A B' F r := by
  by_cases hlt : (r : ℕ) < n
  · rw [insT_apply_ltC (A := A) (B := B) (F := F) (r := r) hlt,
        insT_apply_ltC (A := A) (B := B') (F := F) (r := r) hlt]
  · by_cases h1 : (r : ℕ) = n
    · rw [show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
        insT_apply_leftC (A := A) (B := B) (F := F),
        insT_apply_leftC (A := A) (B := B') (F := F)]
    · by_cases h2 : (r : ℕ) = n + 1
      · exact absurd (Fin.ext h2) hr
      · rw [insT_apply_geC (A := A) (B := B) (F := F) (r := r) (by omega),
          insT_apply_geC (A := A) (B := B') (F := F) (r := r) (by omega)]

/-- The value-level frame-motion cancellation (own copy). -/
theorem frame_motion_cancel_valC {m : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (n : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => Ef i y))
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (G : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    (∑ i : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.Kpt g x (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef i) (Ef i) G r x)
            ⟨n, by omega⟩ (Submission.Diff.lcOf g (Ef i) x (X x))))
      + (∑ i : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.Kpt g x (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef i) (Ef i) G r x)
            ⟨n + 1, by omega⟩ (Submission.Diff.lcOf g (Ef i) x (X x)))) = 0 := by
  classical
  by_cases hfr : 0 < Module.finrank ℝ E
  · have hONx : Submission.Diff.IsONFrame g x (fun m => Ef m x) := hON.self_of_nhds
    have hskew : ∀ m p : Fin (Module.finrank ℝ E),
        g.inner x (Submission.Diff.lcOf g (Ef m) x (X x)) (Ef p x)
          = - g.inner x (Submission.Diff.lcOf g (Ef p) x (X x)) (Ef m x) := by
      intro m p
      have h := Work.Diff.GE.covRic_frame_skew (I := I) (M := M) hLC g x (X x) Ef hEf hON m p
      rw [← g.symm x (Submission.Diff.lcOf g (Ef p) x (X x)) (Ef m x)] at h
      linarith [h]
    have hexp : ∀ m : Fin (Module.finrank ℝ E), Submission.Diff.lcOf g (Ef m) x (X x)
        = ∑ p, g.inner x (Submission.Diff.lcOf g (Ef m) x (X x)) (Ef p x) • Ef p x :=
      fun m => (Work.Diff.GE.sum_smul_inner_eq_self g x hfr (fun i => Ef i x) hONx
        (Submission.Diff.lcOf g (Ef m) x (X x))).symm
    have hP : (∑ u : Fin (Module.finrank ℝ E), Work.Diff.EXT.Kpt g x (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
            ⟨n, by omega⟩ (Submission.Diff.lcOf g (Ef u) x (X x))))
        = ∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
            g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
              * Work.Diff.EXT.Kpt g x (m + 2 + n)
                  (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                      insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
                    ⟨n, by omega⟩ (Ef v x)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      conv_lhs => rw [hexp u]
      rw [show Work.Diff.EXT.Kpt g x (m + 2 + n)
            (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n, by omega⟩
              (∑ v, g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x) • Ef v x))
          = Work.Diff.EXT.KptLin hLC g x (m + 2 + n)
              (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                  insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n, by omega⟩
                (∑ v, g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x) • Ef v x))
          from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      rfl
    have hQ : (∑ u : Fin (Module.finrank ℝ E), Work.Diff.EXT.Kpt g x (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
            ⟨n + 1, by omega⟩ (Submission.Diff.lcOf g (Ef u) x (X x))))
        = ∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
            g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
              * Work.Diff.EXT.Kpt g x (m + 2 + n)
                  (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                      insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
                    ⟨n + 1, by omega⟩ (Ef v x)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      conv_lhs => rw [hexp u]
      rw [show Work.Diff.EXT.Kpt g x (m + 2 + n)
            (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n + 1, by omega⟩
              (∑ v, g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x) • Ef v x))
          = Work.Diff.EXT.KptLin hLC g x (m + 2 + n)
              (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                  insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n + 1, by omega⟩
                (∑ v, g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x) • Ef v x))
          from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      rfl
    rw [hP, hQ]
    have e1 : (∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
          g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
            * Work.Diff.EXT.Kpt g x (m + 2 + n)
                (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                    insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n, by omega⟩ (Ef v x)))
        = ∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
            g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
              * Work.Diff.EXT.Kpt g x (m + 2 + n)
                  (fun r : Fin ((m + 2 + n) + 4) =>
                    insTC (I := I) (M := M) m n (Ef v) (Ef u) G r x) := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      congr 1
      rw [show Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x) ⟨n, by omega⟩ (Ef v x)
          = (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef v) (Ef u) G r x) from by
        funext r
        rw [Function.update_apply]
        by_cases hr : r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4))
        · rw [if_pos hr, hr, insT_apply_leftC (A := Ef v) (B := Ef u) (F := G)]
        · rw [if_neg hr]
          rw [insT_agree_off_leftC (A := Ef u) (A' := Ef v) (B := Ef u) (F := G) r hr]]
    have e2 : (∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
          g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
            * Work.Diff.EXT.Kpt g x (m + 2 + n)
                (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
                    insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
                  ⟨n + 1, by omega⟩ (Ef v x)))
        = ∑ u : Fin (Module.finrank ℝ E), ∑ v : Fin (Module.finrank ℝ E),
            g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x)
              * Work.Diff.EXT.Kpt g x (m + 2 + n)
                  (fun r : Fin ((m + 2 + n) + 4) =>
                    insTC (I := I) (M := M) m n (Ef u) (Ef v) G r x) := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      congr 1
      rw [show Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef u) (Ef u) G r x)
            ⟨n + 1, by omega⟩ (Ef v x)
          = (fun r : Fin ((m + 2 + n) + 4) =>
              insTC (I := I) (M := M) m n (Ef u) (Ef v) G r x) from by
        funext r
        rw [Function.update_apply]
        by_cases hr : r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4))
        · rw [if_pos hr, hr, insT_apply_rightC (A := Ef u) (B := Ef v) (F := G)]
        · rw [if_neg hr]
          rw [insT_agree_off_rightC (A := Ef u) (B := Ef u) (B' := Ef v) (F := G) r hr]]
    rw [e1, e2]
    exact Work.Diff.GE.covRic_skew_sum_zero
      (fun u v => g.inner x (Submission.Diff.lcOf g (Ef u) x (X x)) (Ef v x))
      (fun u v => Work.Diff.EXT.Kpt g x (m + 2 + n)
        (fun r : Fin ((m + 2 + n) + 4) => insTC (I := I) (M := M) m n (Ef u) (Ef v) G r x))
      hskew
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-- **The field-level frame-motion cancellation**, from the value-level statement at each point:
replacing the two frame slots of `insTC` by the frame velocity `∇_X Ef i` produces two families of
tower values whose sums cancel by the antisymmetry of the frame velocities. -/
theorem frame_motion_cancel_fieldC {m : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (n : ℕ) (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (Y : Fin (m + 4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Y i)) :
    ∀ y : M, (∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => Ef i z)) →
      (∑ i : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) Y) y
          + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) Y) y)) = 0 := by
  intro y hy
  have hupd_n : ∀ (i : Fin (Module.finrank ℝ E)) (r : Fin ((m + 2 + n) + 4)),
      r ≠ (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) →
      insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) Y r
        = insTC (I := I) (M := M) m n (Ef i) (Ef i) Y r := by
    intro i r hr
    by_cases hlt : (r : ℕ) < n
    · rw [insT_apply_ltC (A := Work.Diff.EXT.dirF g (Ef i) X) (B := Ef i) (F := Y) (r := r) hlt,
        insT_apply_ltC (A := Ef i) (B := Ef i) (F := Y) (r := r) hlt]
    · by_cases h1 : (r : ℕ) = n
      · exact absurd (Fin.ext h1) hr
      · by_cases h2 : (r : ℕ) = n + 1
        · rw [show r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h2,
            insT_apply_rightC (A := Work.Diff.EXT.dirF g (Ef i) X) (B := Ef i) (F := Y),
            insT_apply_rightC (A := Ef i) (B := Ef i) (F := Y)]
        · rw [insT_apply_geC (A := Work.Diff.EXT.dirF g (Ef i) X) (B := Ef i) (F := Y)
              (r := r) (by omega),
            insT_apply_geC (A := Ef i) (B := Ef i) (F := Y) (r := r) (by omega)]
  have hupd_n1 : ∀ (i : Fin (Module.finrank ℝ E)) (r : Fin ((m + 2 + n) + 4)),
      r ≠ (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4)) →
      insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) Y r
        = insTC (I := I) (M := M) m n (Ef i) (Ef i) Y r := by
    intro i r hr
    by_cases hlt : (r : ℕ) < n
    · rw [insT_apply_ltC (A := Ef i) (B := Work.Diff.EXT.dirF g (Ef i) X) (F := Y) (r := r) hlt,
        insT_apply_ltC (A := Ef i) (B := Ef i) (F := Y) (r := r) hlt]
    · by_cases h1 : (r : ℕ) = n
      · rw [show r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4)) from Fin.ext h1,
          insT_apply_leftC (A := Ef i) (B := Work.Diff.EXT.dirF g (Ef i) X) (F := Y),
          insT_apply_leftC (A := Ef i) (B := Ef i) (F := Y)]
      · by_cases h2 : (r : ℕ) = n + 1
        · exact absurd (Fin.ext h2) hr
        · rw [insT_apply_geC (A := Ef i) (B := Work.Diff.EXT.dirF g (Ef i) X) (F := Y)
              (r := r) (by omega),
            insT_apply_geC (A := Ef i) (B := Ef i) (F := Y) (r := r) (by omega)]
  have h1i : ∀ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
        (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) Y) y
      = Work.Diff.EXT.Kpt g y (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              Work.Diff.EXT.evolX.insTC (I := I) (M := M) m n (Ef i) (Ef i) Y r y)
            ⟨n, by omega⟩ (Submission.Diff.lcOf g (Ef i) y (X y))) := by
    intro i
    rw [Work.Diff.EXT.ckt_eq_Kpt' (I := I) (M := M) hLC g (m + 2 + n) y
      (hT := fun r => smoothTField_insTC (I := I) (M := M)
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hEf i) hX) (hEf i) Y hY r)]
    congr 1
    funext r
    rw [Function.update_apply]
    by_cases hr : r = (⟨n, by omega⟩ : Fin ((m + 2 + n) + 4))
    · rw [if_pos hr, hr,
        insT_apply_leftC (A := Work.Diff.EXT.dirF g (Ef i) X) (B := Ef i) (F := Y)]
      rfl
    · rw [if_neg hr]
      exact congrArg (fun T => T y) (hupd_n i r hr)
  have h2i : ∀ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
        (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) Y) y
      = Work.Diff.EXT.Kpt g y (m + 2 + n)
          (Function.update (fun r : Fin ((m + 2 + n) + 4) =>
              Work.Diff.EXT.evolX.insTC (I := I) (M := M) m n (Ef i) (Ef i) Y r y)
            ⟨n + 1, by omega⟩ (Submission.Diff.lcOf g (Ef i) y (X y))) := by
    intro i
    rw [Work.Diff.EXT.ckt_eq_Kpt' (I := I) (M := M) hLC g (m + 2 + n) y
      (hT := fun r => smoothTField_insTC (I := I) (M := M) (hEf i)
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hEf i) hX) Y hY r)]
    congr 1
    funext r
    rw [Function.update_apply]
    by_cases hr : r = (⟨n + 1, by omega⟩ : Fin ((m + 2 + n) + 4))
    · rw [if_pos hr, hr,
        insT_apply_rightC (A := Ef i) (B := Work.Diff.EXT.dirF g (Ef i) X) (F := Y)]
      rfl
    · rw [if_neg hr]
      exact congrArg (fun T => T y) (hupd_n1 i r hr)
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) Y) y
          + Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) Y) y))
      = (∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Work.Diff.EXT.dirF g (Ef i) X) (Ef i) Y) y)
        + ∑ i : Fin (Module.finrank ℝ E), Work.Diff.EXT.ckt g (m + 2 + n)
            (insTC (I := I) (M := M) m n (Ef i) (Work.Diff.EXT.dirF g (Ef i) X) Y) y
      from Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => h1i i), Finset.sum_congr rfl (fun i _ => h2i i)]
  exact frame_motion_cancel_valC (I := I) (M := M) (m := m) hLC g y n Ef hEf hy X hX Y hY

/-- `insTC` at `n = 0` prepends the two fields. -/
theorem insT_zeroC {m : ℕ} (A B : Work.Diff.EXT.TField (I := I) (M := M))
    (F : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    insTC (I := I) (M := M) m 0 A B F = Fin.cons A (Fin.cons B F) := by
  funext r
  rw [show (insTC (I := I) (M := M) m 0 A B F) r
      = Fin.append (fun t : Fin 0 => F ⟨t.val, by omega⟩)
          (Fin.cons A (Fin.cons B (fun t : Fin (m + 4) => F ⟨0 + t.val, by omega⟩)))
          (Fin.cast (by omega) r) from rfl]
  rw [show (Fin.cast (show (m + 2 + 0) + 4 = 0 + (m + 4 + 2) by omega) r :
        Fin (0 + (m + 4 + 2))) = Fin.natAdd 0 (Fin.cast (by omega) r) from
      Fin.ext (by simp)]
  rw [Fin.append_right]
  rw [show (fun t : Fin (m + 4) => F ⟨0 + t.val, by omega⟩) = F from by
    funext t
    exact congrArg F (Fin.ext (by simp))]
  have hcast : (Fin.cast (show (m + 2 + 0) + 4 = m + 4 + 2 by omega) r : Fin (m + 4 + 2)) = r :=
    Fin.ext (Fin.val_cast _ r)
  rw [hcast]

/-- The row of the `i`-th summand of `lapOpE`: `insTC` does not see the two inserted fields when
they are the leading ones. -/
theorem lapOpE_eq_SOpC (g : Submission.Diff.SMet I M) (m : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) :
    ∀ F : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M),
      Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g m F = SOpC g m 0 Ef F := by
  intro F
  funext y
  simp only [Work.Diff.EXT.lapOpE, SOpC]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [insT_zeroC (I := I) (M := M)]

/-- **The `j`-fold `extStep` of the level-`0` frame-traced tower is the level-`j` one.** -/
theorem jetAll_SOp_allC {m : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i)) {x : M}
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => Ef i y)) :
    ∀ (j : ℕ) (F : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) →
      Work.Diff.EXT.jetAll g j (m + 4) (SOpC g m 0 Ef) F =ᶠ[𝓝 x] SOpC g m j Ef F := by
  intro j
  induction j with
  | zero =>
    intro F hF
    exact Filter.EventuallyEq.refl _ _
  | succ l ih =>
    intro F hF
    have hstep := SOp_stepC (I := I) (M := M) hLC g Ef hEf F hF hON
      (frame_motion_cancel_fieldC (I := I) (M := M) hLC g Ef hEf l (F 0) (hF 0)
        (fun s : Fin (m + 4 + l) => F s.succ) (fun s => hF s.succ))
    refine Filter.EventuallyEq.trans ?_ hstep
    have hcongr := Work.Diff.EXT.extStep_congr_at (I := I) (M := M) g
      (Work.Diff.EXT.jetAll g l (m + 4) (SOpC g m 0 Ef)) (SOpC g m l Ef) F x
      (ih (fun i : Fin (m + 4 + l) => F i.succ) (fun i => hF i.succ))
      (fun s : Fin (m + 4 + l) => ih _ (Work.Diff.EXT.smoothF_update'
        (K := m + 4 + l) (fun i => hF i.succ) s
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hF s.succ) (hF 0))))
    simpa only [Work.Diff.EXT.jetAll] using hcongr




/-- **The `j`-th jet of the frame-traced rough Laplacian of the tower.** -/
theorem lapOpE_jetAllC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (m j : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun i => Ef i y)) (nhds x))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    Work.Diff.EXT.jetAll g j (m + 4) (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g m) G x
      = ∑ i : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.ckt g (m + 2 + j)
            (Work.Diff.EXT.evolX.tupIns (I := I) (M := M) m j Ef G i) x := by
  have hop : ∀ F : Fin (m + 4) → Work.Diff.EXT.TField (I := I) (M := M),
      ∀ y, Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g m F y = SOpC g m 0 Ef F y :=
    fun F y => congrFun (lapOpE_eq_SOpC (I := I) (M := M) g m Ef F) y
  rw [Work.Diff.EXT.evolX.jetAll_congr_of_eventuallyEq (I := I) (M := M)
    (K := m + 4) (j := j) (g := g)
    (S := Work.Diff.EXT.lapOpE (I := I) (M := M) Ef g m) (S' := SOpC g m 0 Ef)
    (x := x) (G := G) (fun F => Filter.EventuallyEq.of_eq (funext (hop F)))]
  rw [(jetAll_SOp_allC (I := I) (M := M) hLC g Ef hEf hON j G hG).eq_of_nhds]
  simp only [SOpC]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl


end Work.Diff.EXT.evolX
