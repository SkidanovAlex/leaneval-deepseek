import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.PairSum
import Submission.Potential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

noncomputable section

open Filter Metric MeasureTheory Laplacian
open scoped ENNReal NNReal ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev Y (N : ℕ) := Fin N → ℝ³

noncomputable section

/-! ## Section 0 : the block split of particle coordinates -/

/-- Combine two blocks. -/
def combine {N1 N2 : ℕ} (u : Y N1) (w : Y N2) : Y (N1 + N2) :=
  fun c => Sum.elim u w (finSumFinEquiv.symm c)

lemma combine_left {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (i : Fin N1) :
    combine u w (Fin.castAdd N2 i) = u i := by
  change Sum.elim u w (finSumFinEquiv.symm (Fin.castAdd N2 i)) = u i
  simp

lemma combine_right {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (j : Fin N2) :
    combine u w (Fin.natAdd N1 j) = w j := by
  change Sum.elim u w (finSumFinEquiv.symm (Fin.natAdd N1 j)) = w j
  simp

lemma combine_inl {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (i : Fin N1) :
    combine u w (finSumFinEquiv (Sum.inl i)) = u i := by
  change Sum.elim u w (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = u i
  simp

lemma combine_inr {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (j : Fin N2) :
    combine u w (finSumFinEquiv (Sum.inr j)) = w j := by
  change Sum.elim u w (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = w j
  simp

/-- The block-1 (left) part of a function on `Fin (N1+N2)`. -/
def leftBlock {N1 N2 : ℕ} (x : Y (N1 + N2)) : Y N1 := fun i => x (Fin.castAdd N2 i)

/-- The block-2 (right) part. -/
def rightBlock {N1 N2 : ℕ} (x : Y (N1 + N2)) : Y N2 := fun j => x (Fin.natAdd N1 j)

lemma combine_leftBlock {N1 N2 : ℕ} (u : Y N1) (w : Y N2) :
    leftBlock (combine u w) = u := by
  funext i
  simp [leftBlock, combine_left]

lemma combine_rightBlock {N1 N2 : ℕ} (u : Y N1) (w : Y N2) :
    rightBlock (combine u w) = w := by
  funext j
  simp [rightBlock, combine_right]

lemma combine_leftBlock_rightBlock {N1 N2 : ℕ} (x : Y (N1 + N2)) :
    combine (leftBlock x) (rightBlock x) = x := by
  funext c
  cases h : finSumFinEquiv.symm c with
  | inl i =>
      have hc : c = Fin.castAdd N2 i := by
        have h' := congrArg finSumFinEquiv h
        simpa using h'
      rw [hc]
      simp [combine, leftBlock]
  | inr j =>
      have hc : c = Fin.natAdd N1 j := by
        have h' := congrArg finSumFinEquiv h
        simpa using h'
      rw [hc]
      simp [combine, rightBlock]

/-- update lemma: changing slot `castAdd N2 i` only affects the `u`-block. -/
lemma update_combine_left {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (i : Fin N1) (y : ℝ³) :
    Function.update (combine u w) (Fin.castAdd N2 i) y = combine (Function.update u i y) w := by
  funext c
  by_cases hc : Fin.castAdd N2 i = c
  · subst c
    simp [combine_left]
  · rw [Function.update_of_ne (a := c) (a' := Fin.castAdd N2 i) (Ne.symm hc) y (combine u w)]
    unfold combine
    cases h : finSumFinEquiv.symm c with
    | inl i' =>
        have hii' : i' ≠ i := by
          intro hii'
          apply hc
          have hc' : c = Fin.castAdd N2 i' := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc', hii']
        simp [h, hii', Function.update_of_ne (a := i') (a' := i) hii' y u]
    | inr j =>
        simp [h]

/-- update lemma: changing slot `natAdd N1 j` only affects the `w`-block. -/
lemma update_combine_right {N1 N2 : ℕ} (u : Y N1) (w : Y N2) (j : Fin N2) (y : ℝ³) :
    Function.update (combine u w) (Fin.natAdd N1 j) y = combine u (Function.update w j y) := by
  funext c
  by_cases hc : Fin.natAdd N1 j = c
  · subst c
    simp [combine_right]
  · rw [Function.update_of_ne (a := c) (a' := Fin.natAdd N1 j) (Ne.symm hc) y (combine u w)]
    unfold combine
    cases h : finSumFinEquiv.symm c with
    | inl i =>
        simp [h]
    | inr j' =>
        have hjj' : j' ≠ j := by
          intro hjj'
          apply hc
          have hc' : c = Fin.natAdd N1 j' := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc', hjj']
        simp [h, hjj', Function.update_of_ne (a := j') (a' := j) hjj' y w]

/-- Laplacian of the block-1 slice equals the big Laplacian restricted to the block-1 slot. -/
lemma partialLaplacian_combine_left {N1 N2 : ℕ} (f : Y (N1 + N2) → ℝ)
    (u : Y N1) (w : Y N2) (i : Fin N1) :
    partialLaplacian (Fin.castAdd N2 i) f (combine u w) =
      partialLaplacian i (fun u' => f (combine u' w)) u := by
  unfold partialLaplacian
  simp only [combine_left]
  apply congrArg (fun g : ℝ³ → ℝ => Δ g (u i))
  funext y
  exact congrArg f (update_combine_left u w i y)

/-- Laplacian of the block-2 slice equals the big Laplacian restricted to the block-2 slot. -/
lemma partialLaplacian_combine_right {N1 N2 : ℕ} (f : Y (N1 + N2) → ℝ)
    (u : Y N1) (w : Y N2) (j : Fin N2) :
    partialLaplacian (Fin.natAdd N1 j) f (combine u w) =
      partialLaplacian j (fun w' => f (combine u w')) w := by
  unfold partialLaplacian
  simp only [combine_right]
  apply congrArg (fun g : ℝ³ → ℝ => Δ g (w j))
  funext y
  exact congrArg f (update_combine_right u w j y)

/-- combining respects subtraction in the first block: `combine (u1 - u2) (w1 - w2) = combine u1 w1 - combine u2 w2`. -/
lemma combine_sub {N1 N2 : ℕ} (u1 u2 : Y N1) (w1 w2 : Y N2) :
    combine (u1 - u2) (w1 - w2) = combine u1 w1 - combine u2 w2 := by
  funext c
  unfold combine
  cases h : finSumFinEquiv.symm c with
  | inl i => simp [h]
  | inr j => simp [h]

/-- combine respects addition in the first block. -/
lemma combine_add {N1 N2 : ℕ} (u1 u2 : Y N1) (w1 w2 : Y N2) :
    combine (u1 + u2) (w1 + w2) = combine u1 w1 + combine u2 w2 := by
  funext c
  unfold combine
  cases h : finSumFinEquiv.symm c with
  | inl i => simp [h]
  | inr j => simp [h]

/-- combine respects scalar multiplication. -/
lemma combine_smul {N1 N2 : ℕ} (a : ℝ) (u : Y N1) (w : Y N2) :
    combine (a • u) (a • w) = a • combine u w := by
  funext c
  unfold combine
  cases h : finSumFinEquiv.symm c with
  | inl i => simp [h]
  | inr j => simp [h]

/-! ## Section 1 : boxes and the block product -/

/-- `x` lies in the box iff each coordinate does. -/
lemma mem_box_iff_coord (N : ℕ) (L : ℝ) (x : Y N) :
    x ∈ box N L ↔ ∀ c : Fin N, ∀ k : Fin 3, x c k ∈ Set.Icc 0 L := by
  rfl

/-- box membership respects combine. -/
lemma box_combine_mem {N1 N2 : ℕ} {L : ℝ} (u : Y N1) (w : Y N2) :
    combine u w ∈ box (N1 + N2) L ↔ u ∈ box N1 L ∧ w ∈ box N2 L := by
  constructor
  · intro hx
    constructor
    · rw [mem_box_iff_coord]
      intro i k
      have hc := (mem_box_iff_coord (N1 + N2) L (combine u w)).mp hx (Fin.castAdd N2 i) k
      simpa [combine_left] using hc
    · rw [mem_box_iff_coord]
      intro j k
      have hc := (mem_box_iff_coord (N1 + N2) L (combine u w)).mp hx (Fin.natAdd N1 j) k
      simpa [combine_right] using hc
  · intro hx
    rw [mem_box_iff_coord]
    intro c k
    cases h : finSumFinEquiv.symm c with
    | inl i =>
        have hu := (mem_box_iff_coord N1 L u).mp hx.1 i k
        rw [← combine_inl u w i] at hu
        rw [show c = finSumFinEquiv (Sum.inl i) by
          have h' := congrArg finSumFinEquiv h
          simpa using h']
        exact hu
    | inr j =>
        have hw := (mem_box_iff_coord N2 L w).mp hx.2 j k
        rw [← combine_inr u w j] at hw
        rw [show c = finSumFinEquiv (Sum.inr j) by
          have h' := congrArg finSumFinEquiv h
          simpa using h']
        exact hw

/-- projecting an element of the big box onto the first block stays in the box. -/
lemma leftBlock_mem_box_of_mem {N1 N2 : ℕ} {L : ℝ} {x : Y (N1 + N2)}
    (hx : x ∈ box (N1 + N2) L) : leftBlock x ∈ box N1 L := by
  rw [mem_box_iff_coord]
  intro i k
  exact (mem_box_iff_coord (N1 + N2) L x).mp hx (Fin.castAdd N2 i) k

/-- combine respects subtraction of the constant second block. -/
lemma combine_sub_same {N1 N2 : ℕ} (u1 u2 : Y N1) (w : Y N2) :
    combine (u1 - u2) (0 : Y N2) = combine u1 w - combine u2 w := by
  funext c
  unfold combine
  cases h : finSumFinEquiv.symm c with
  | inl i => simp [h]
  | inr j => simp [h]

lemma combine_sub_same_right {N1 N2 : ℕ} (u : Y N1) (w1 w2 : Y N2) :
    combine (0 : Y N1) (w1 - w2) = combine u w1 - combine u w2 := by
  funext c
  unfold combine
  cases h : finSumFinEquiv.symm c with
  | inl i => simp [h]
  | inr j => simp [h]

/-- Norm of a first-block-only vector equals the norm of the block. -/
lemma norm_combine_zero_left {N1 N2 : ℕ} (v : Y N1) :
    ‖combine v (0 : Y N2)‖ = ‖v‖ := by
  have h1 : (Finset.univ.sup fun c : Fin (N1 + N2) => ‖(combine v (0 : Y N2)) c‖₊) =
      (Finset.univ.sup fun i : Fin N1 => ‖v i‖₊) := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro c hc
      cases h : finSumFinEquiv.symm c with
      | inl i =>
          have hc' : c = Fin.castAdd N2 i := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc']
          rw [combine_left]
          exact Finset.le_sup (s := (Finset.univ : Finset (Fin N1)))
            (f := fun i : Fin N1 => ‖v i‖₊) (b := i) (Finset.mem_univ i)
      | inr j =>
          have hc' : c = Fin.natAdd N1 j := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc']
          rw [combine_right]
          simp
    · rw [Finset.sup_le_iff]
      intro i hi
      have hle : ‖v i‖₊ ≤ (Finset.univ.sup fun c : Fin (N1 + N2) => ‖(combine v (0 : Y N2)) c‖₊) := by
        rw [← combine_left v (0 : Y N2) i]
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (N1 + N2))))
          (f := fun c : Fin (N1 + N2) => ‖(combine v (0 : Y N2)) c‖₊)
          (b := Fin.castAdd N2 i) (Finset.mem_univ (Fin.castAdd N2 i))
      exact hle
  rw [Pi.norm_def, Pi.norm_def]
  exact_mod_cast h1

/-- The section `u ↦ combine u w` is distance-non-expanding (in fact isometric on block 1). -/
lemma dist_combine_left_le {N1 N2 : ℕ} (u1 u2 : Y N1) (w : Y N2) :
    dist (combine u1 w) (combine u2 w) ≤ dist u1 u2 := by
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖combine u1 w - combine u2 w‖ ≤ ‖combine (u1 - u2) (0 : Y N2)‖ := by
        rw [← combine_sub_same u1 u2 w]
    _ = ‖u1 - u2‖ := norm_combine_zero_left (u1 - u2)

/-- Norm of a second-block-only vector equals the norm of the block. -/
lemma norm_combine_zero_right {N1 N2 : ℕ} (w : Y N2) :
    ‖combine (0 : Y N1) w‖ = ‖w‖ := by
  have h1 : (Finset.univ.sup fun c : Fin (N1 + N2) => ‖(combine (0 : Y N1) w) c‖₊) =
      (Finset.univ.sup fun j : Fin N2 => ‖w j‖₊) := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro c hc
      cases h : finSumFinEquiv.symm c with
      | inl i =>
          have hc' : c = Fin.castAdd N2 i := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc']
          rw [combine_left]
          simp
      | inr j =>
          have hc' : c = Fin.natAdd N1 j := by
            have hh := congrArg finSumFinEquiv h
            simpa using hh
          rw [hc']
          rw [combine_right]
          exact Finset.le_sup (s := (Finset.univ : Finset (Fin N2)))
            (f := fun j : Fin N2 => ‖w j‖₊) (b := j) (Finset.mem_univ j)
    · rw [Finset.sup_le_iff]
      intro j hj
      have hle : ‖w j‖₊ ≤ (Finset.univ.sup fun c : Fin (N1 + N2) => ‖(combine (0 : Y N1) w) c‖₊) := by
        rw [← combine_right (0 : Y N1) w j]
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (N1 + N2))))
          (f := fun c : Fin (N1 + N2) => ‖(combine (0 : Y N1) w) c‖₊)
          (b := Fin.natAdd N1 j) (Finset.mem_univ (Fin.natAdd N1 j))
      exact hle
  rw [Pi.norm_def, Pi.norm_def]
  exact_mod_cast h1

/-- The section `w ↦ combine u w` is distance-non-expanding. -/
lemma dist_combine_right_le {N1 N2 : ℕ} (u : Y N1) (w1 w2 : Y N2) :
    dist (combine u w1) (combine u w2) ≤ dist w1 w2 := by
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖combine u w1 - combine u w2‖ ≤ ‖combine (0 : Y N1) (w1 - w2)‖ := by
        rw [← combine_sub_same_right u w1 w2]
    _ = ‖w1 - w2‖ := norm_combine_zero_right (w1 - w2)

/-- If the whole point is in the interior of the big box, the first block is in the
interior of its box. -/
lemma interior_box_left {N1 N2 : ℕ} {L : ℝ} {u : Y N1} {w : Y N2}
    (hx : combine u w ∈ interior (box (N1 + N2) L)) : u ∈ interior (box N1 L) := by
  rw [mem_interior_iff_mem_nhds] at hx ⊢
  rcases Metric.mem_nhds_iff.mp hx with ⟨δ, hδpos, hball⟩
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδpos, ?_⟩
  intro u' hu'
  have hc : combine u' w ∈ box (N1 + N2) L := by
    exact hball (Metric.mem_ball.mpr (lt_of_le_of_lt (dist_combine_left_le u' u w) (Metric.mem_ball.mp hu')))
  exact (box_combine_mem (L := L) u' w).mp hc |>.1

/-- The block-2 analogue. -/
lemma interior_box_right {N1 N2 : ℕ} {L : ℝ} {u : Y N1} {w : Y N2}
    (hx : combine u w ∈ interior (box (N1 + N2) L)) : w ∈ interior (box N2 L) := by
  rw [mem_interior_iff_mem_nhds] at hx ⊢
  rcases Metric.mem_nhds_iff.mp hx with ⟨δ, hδpos, hball⟩
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδpos, ?_⟩
  intro w' hw'
  have hc : combine u w' ∈ box (N1 + N2) L := by
    exact hball (Metric.mem_ball.mpr (lt_of_le_of_lt (dist_combine_right_le u w' w) (Metric.mem_ball.mp hw')))
  exact (box_combine_mem (L := L) u w').mp hc |>.2

end

/-! ## Section 2 : measure-preservation and Fubini for the block split -/

/-- The canonical measurable equivalence from the block product to the big function space:
`(u, w) ↦ combine u w`. -/
def blockEquiv (N1 N2 : ℕ) : Y N1 × Y N2 ≃ᵐ Y (N1 + N2) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (N1 + N2) => ℝ³)
      (finSumFinEquiv (m := N1) (n := N2)))

lemma blockEquiv_apply {N1 N2 : ℕ} (u : Y N1) (w : Y N2) :
    blockEquiv N1 N2 (u, w) = combine u w := by
  funext c
  unfold blockEquiv combine
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rfl

lemma measurePreserving_blockEquiv (N1 N2 : ℕ) :
    MeasurePreserving (blockEquiv N1 N2) volume volume := by
  unfold blockEquiv
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (N1 + N2) => ℝ³)
      (finSumFinEquiv (m := N1) (n := N2))).comp
    (MeasurePreserving.symm (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³))
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³)))

/-- Change of variables + Fubini: the integral over the big space equals the iterated integral
over the two blocks. -/
lemma integral_combine {N1 N2 : ℕ} (G : Y (N1 + N2) → ℝ)
    (hG : Integrable G) :
    (∫ u : Y N1, ∫ w : Y N2, G (combine u w)) = ∫ x : Y (N1 + N2), G x := by
  have hmp : MeasurePreserving (blockEquiv N1 N2) volume volume := measurePreserving_blockEquiv N1 N2
  have hprod : Integrable (fun p : Y N1 × Y N2 => G ((blockEquiv N1 N2) p))
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := G))
    exact hi.2 hG
  have hEqInt : (fun p : Y N1 × Y N2 => G (combine p.1 p.2)) = fun p => G ((blockEquiv N1 N2) p) := by
    funext p
    congr 1
    exact (blockEquiv_apply p.1 p.2).symm
  have hstep1 : (∫ u : Y N1, ∫ w : Y N2, G (combine u w))
      = ∫ p : Y N1 × Y N2, G (combine p.1 p.2) := by
    exact (integral_prod (μ := (volume : Measure (Y N1))) (ν := (volume : Measure (Y N2)))
      (f := fun p : Y N1 × Y N2 => G (combine p.1 p.2)) (by simpa [hEqInt] using hprod)).symm
  have hstep2 : (∫ p : Y N1 × Y N2, G (combine p.1 p.2)) = ∫ x : Y (N1 + N2), G x := by
    have hmpInv := (MeasurePreserving.integral_comp (f := blockEquiv N1 N2) (g := G) hmp
      (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2)))
    rw [hEqInt]
    exact hmpInv
  exact hstep1.trans hstep2

/-! ## Section 3 : slice functions and their admissibility -/

/-- The linear map `u ↦ combine u 0` (embeds the first block as the first coordinates). -/
def sliceL (N1 N2 : ℕ) : Y N1 →L[ℝ] Y (N1 + N2) := by
  refine LinearMap.mkContinuousOfExistsBound { toFun := fun u => combine u (0 : Y N2), map_add' := ?_, map_smul' := ?_ } ?_
  · intro u v
    simpa using (combine_add u v (0 : Y N2) (0 : Y N2))
  · intro a u
    simpa using (combine_smul a u (0 : Y N2))
  · refine ⟨1, ?_⟩
    intro u
    change ‖combine u (0 : Y N2)‖ ≤ 1 * ‖u‖
    rw [norm_combine_zero_left]
    simp

lemma sliceL_apply {N1 N2 : ℕ} (u : Y N1) : sliceL N1 N2 u = combine u (0 : Y N2) := rfl

/-- linear map embedding the second block. -/
def sliceR (N1 N2 : ℕ) : Y N2 →L[ℝ] Y (N1 + N2) := by
  refine LinearMap.mkContinuousOfExistsBound { toFun := fun w => combine (0 : Y N1) w, map_add' := ?_, map_smul' := ?_ } ?_
  · intro u v
    simpa using (combine_add (0 : Y N1) (0 : Y N1) u v)
  · intro a u
    simpa using (combine_smul a (0 : Y N1) u)
  · refine ⟨1, ?_⟩
    intro u
    change ‖combine (0 : Y N1) u‖ ≤ 1 * ‖u‖
    rw [norm_combine_zero_right]
    simp

lemma sliceR_apply {N1 N2 : ℕ} (w : Y N2) : sliceR N1 N2 w = combine (0 : Y N1) w := rfl

/-- The section `u ↦ combine u w` is smooth. -/
lemma contDiff_section_left {N1 N2 : ℕ} (w : Y N2) :
    ContDiff ℝ ∞ (fun u : Y N1 => combine u w) := by
  have h : (fun u : Y N1 => combine u w) = fun u => combine u (0 : Y N2) + combine (0 : Y N1) w := by
    funext u
    have hc := combine_add u (0 : Y N1) (0 : Y N2) w
    -- combine (u + 0) (0 + w) = combine u 0 + combine 0 w
    simpa using hc
  rw [h]
  exact ContDiff.add (sliceL N1 N2).contDiff contDiff_const

/-- The section `w ↦ combine u w` is smooth. -/
lemma contDiff_section_right {N1 N2 : ℕ} (u : Y N1) :
    ContDiff ℝ ∞ (fun w : Y N2 => combine u w) := by
  have h : (fun w : Y N2 => combine u w) = fun w => combine (0 : Y N1) w + combine u (0 : Y N2) := by
    funext w
    have hc := combine_add (0 : Y N1) u w (0 : Y N2)
    -- combine (0 + u) (w + 0) = combine 0 w + combine u 0
    simpa [add_comm] using hc
  rw [h]
  exact ContDiff.add (sliceR N1 N2).contDiff contDiff_const

/-- Block-1 slice of a state. -/
def slice1 {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2) : Y N1 → ℝ :=
  fun u => (Ψ : Y (N1 + N2) → ℝ) (combine u w)

/-- Block-2 slice of a state. -/
def slice2 {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1) : Y N2 → ℝ :=
  fun w => (Ψ : Y (N1 + N2) → ℝ) (combine u w)

lemma slice1_smooth {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2) :
    ContDiff ℝ ∞ (slice1 Ψ w) := by
  change ContDiff ℝ ∞ (fun u : Y N1 => (Ψ : Y (N1 + N2) → ℝ) (combine u w))
  exact (psi_contDiff Ψ).comp (contDiff_section_left w)

lemma slice2_smooth {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1) :
    ContDiff ℝ ∞ (slice2 Ψ u) := by
  change ContDiff ℝ ∞ (fun w : Y N2 => (Ψ : Y (N1 + N2) → ℝ) (combine u w))
  exact (psi_contDiff Ψ).comp (contDiff_section_right u)

/-- The support of a slice is carried by the support of the state. -/
lemma support_slice1_subset_section {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L)
    (w : Y N2) :
    Function.support (slice1 Ψ w) ⊆
      {u : Y N1 | (combine u w) ∈ Function.support (Ψ : Y (N1 + N2) → ℝ)} := by
  intro u hu
  exact hu

lemma tsupport_slice1_subset {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L)
    (w : Y N2) :
    tsupport (slice1 Ψ w) ⊆ interior (box N1 L) := by
  have hcont : Continuous (fun u : Y N1 => combine u w) := (contDiff_section_left w).continuous
  have hsubs : Function.support (slice1 Ψ w) ⊆
      (fun u : Y N1 => combine u w) ⁻¹' tsupport (Ψ : Y (N1 + N2) → ℝ) := by
    intro u hu
    exact subset_tsupport (Ψ : Y (N1 + N2) → ℝ) hu
  have hclosed : IsClosed ((fun u : Y N1 => combine u w) ⁻¹'
      tsupport (Ψ : Y (N1 + N2) → ℝ)) :=
    (isClosed_tsupport (Ψ : Y (N1 + N2) → ℝ)).preimage hcont
  intro u hu
  have hmem : u ∈ (fun u : Y N1 => combine u w) ⁻¹' tsupport (Ψ : Y (N1 + N2) → ℝ) := by
    exact closure_minimal hsubs hclosed hu
  have hint : combine u w ∈ interior (box (N1 + N2) L) := Ψ.support hmem
  exact interior_box_left (N1 := N1) (N2 := N2) (L := L) hint

lemma tsupport_slice2_subset {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L)
    (u : Y N1) :
    tsupport (slice2 Ψ u) ⊆ interior (box N2 L) := by
  have hcont : Continuous (fun w : Y N2 => combine u w) := (contDiff_section_right u).continuous
  have hsubs : Function.support (slice2 Ψ u) ⊆
      (fun w : Y N2 => combine u w) ⁻¹' tsupport (Ψ : Y (N1 + N2) → ℝ) := by
    intro w hw
    exact subset_tsupport (Ψ : Y (N1 + N2) → ℝ) hw
  have hclosed : IsClosed ((fun w : Y N2 => combine u w) ⁻¹'
      tsupport (Ψ : Y (N1 + N2) → ℝ)) :=
    (isClosed_tsupport (Ψ : Y (N1 + N2) → ℝ)).preimage hcont
  intro w hw
  have hmem : w ∈ (fun w : Y N2 => combine u w) ⁻¹' tsupport (Ψ : Y (N1 + N2) → ℝ) := by
    exact closure_minimal hsubs hclosed hw
  have hint : combine u w ∈ interior (box (N1 + N2) L) := Ψ.support hmem
  exact interior_box_right (N1 := N1) (N2 := N2) (L := L) hint

/-- A nonzero block-1 slice is an admissible state of the `N1`-body problem. -/
def slice1Elem {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2)
    (hne : slice1 Ψ w ≠ 0) : CInfty0Box N1 L where
  toFun := slice1 Ψ w
  contDiff := (slice1_smooth Ψ w).contDiffOn
  support := tsupport_slice1_subset Ψ w
  nezero := hne

/-- A nonzero block-2 slice is an admissible state of the `N2`-body problem. -/
def slice2Elem {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1)
    (hne : slice2 Ψ u ≠ 0) : CInfty0Box N2 L where
  toFun := slice2 Ψ u
  contDiff := (slice2_smooth Ψ u).contDiffOn
  support := tsupport_slice2_subset Ψ u
  nezero := hne

/-- Symmetry of the iterated integral. -/
lemma integral_iterated_swap {N1 N2 : ℕ} (H : Y N1 → Y N2 → ℝ)
    (hH : Integrable (fun p : Y N1 × Y N2 => H p.1 p.2)) :
    (∫ u : Y N1, ∫ w : Y N2, H u w) = ∫ w : Y N2, ∫ u : Y N1, H u w := by
  have h1 : (∫ u : Y N1, ∫ w : Y N2, H u w) = ∫ p : Y N1 × Y N2, H p.1 p.2 := by
    exact (integral_prod (μ := (volume : Measure (Y N1))) (ν := (volume : Measure (Y N2)))
      (f := fun p : Y N1 × Y N2 => H p.1 p.2) hH).symm
  have hq : Integrable (fun q : Y N2 × Y N1 => H q.2 q.1)
      ((volume : Measure (Y N2)).prod (volume : Measure (Y N1))) := by
    simpa [Function.comp_def, Prod.swap_prod_mk] using hH.swap
  have hq2 : (∫ w : Y N2, ∫ u : Y N1, H u w) = ∫ q : Y N2 × Y N1, H q.2 q.1 := by
    exact (integral_prod (μ := (volume : Measure (Y N2))) (ν := (volume : Measure (Y N1)))
      (f := fun q : Y N2 × Y N1 => H q.2 q.1) hq).symm
  have h2 : (∫ w : Y N2, ∫ u : Y N1, H u w) = ∫ p : Y N1 × Y N2, H p.1 p.2 := by
    rw [hq2]
    have hsw := MeasureTheory.integral_prod_swap (μ := (volume : Measure (Y N1)))
      (ν := (volume : Measure (Y N2))) (f := fun p : Y N1 × Y N2 => H p.1 p.2)
    -- hsw : ∫ (z : Y N2 × Y N1), f z.swap = ∫ (z : Y N1 × Y N2), f z; f z.swap = H z.2 z.1
    exact hsw
  exact h1.trans h2.symm



/-! ## Section 4 : pointwise decomposition of the big numerator into blocks and cross terms -/

/-- the pointwise numerator integrand of the big problem. -/
def bigNumInt {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    Y (N1 + N2) → ℝ :=
  fun x => (Ψ : Y (N1 + N2) → ℝ) x * (_root_.BoseGases.𝓗 (N1 + N2) v (Ψ : Y (N1 + N2) → ℝ)) x

/-- block-1 pointwise part: kinetic terms of block 1 plus pair terms inside block 1. -/
def block1NumInt {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    Y (N1 + N2) → ℝ :=
  fun x =>
    (∑ i : Fin N1, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.castAdd N2 i) (Ψ : Y (N1 + N2) → ℝ) x)) +
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
      ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 * v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2)))

/-- block-2 pointwise part. -/
def block2NumInt {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    Y (N1 + N2) → ℝ :=
  fun x =>
    (∑ j : Fin N2, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.natAdd N1 j) (Ψ : Y (N1 + N2) → ℝ) x)) +
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
      ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 * v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2)))

/-- cross pointwise part (always ≥ 0 for `v ≥ 0`). -/
def crossNumInt {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    Y (N1 + N2) → ℝ :=
  fun x =>
    ∑ i : Fin N1, ∑ j : Fin N2,
      ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 * v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))

/-- kinetic sum splits over the blocks. -/
lemma kin_split {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (x : Y (N1 + N2)) :
    ((Ψ : Y (N1 + N2) → ℝ) x) * (∑ i : Fin (N1 + N2),
        - partialLaplacian i (Ψ : Y (N1 + N2) → ℝ) x)
    = (∑ i1 : Fin N1, ((Ψ : Y (N1 + N2) → ℝ) x) *
        (- partialLaplacian (Fin.castAdd N2 i1) (Ψ : Y (N1 + N2) → ℝ) x))
    + (∑ j2 : Fin N2, ((Ψ : Y (N1 + N2) → ℝ) x) *
        (- partialLaplacian (Fin.natAdd N1 j2) (Ψ : Y (N1 + N2) → ℝ) x)) := by
  rw [Fin.sum_univ_add (a := N1) (b := N2)
      (f := fun i : Fin (N1 + N2) => - partialLaplacian i (Ψ : Y (N1 + N2) → ℝ) x)]
  rw [mul_add]
  rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin N1)))]
  rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin N2)))]

/-- The full numerator integrand splits as block1 + block2 + cross. -/
lemma bigNumInt_eq {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    bigNumInt v Ψ = block1NumInt v Ψ + block2NumInt v Ψ + crossNumInt v Ψ := by
  funext x
  unfold bigNumInt block1NumInt block2NumInt crossNumInt
  unfold _root_.BoseGases.𝓗
  rw [mul_add]
  -- rewrite the kinetic piece
  rw [kin_split Ψ x]
  -- interaction piece: push the factor Ψx inside, then split the pair sums
  have hInt : ((Ψ : Y (N1 + N2) → ℝ) x) *
        (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)),
          v (x p.1 - x p.2) * (Ψ : Y (N1 + N2) → ℝ) x)
      = (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)),
          ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 * v (x p.1 - x p.2)) := by
        rw [Finset.mul_sum (s := (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)))]
        refine Finset.sum_congr rfl ?_
        intro p hp
        ring
  rw [hInt]
  rw [pairSum_eq_blocks (fun i : Fin (N1 + N2) => fun j : Fin (N1 + N2) =>
      ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 * v (x i - x j))]
  -- evaluate the function additions on the right and group the terms
  simp only [Pi.add_apply]
  ring_nf

/-- the cross part is nonnegative pointwise. -/
lemma crossNumInt_nonneg {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (Ψ : CInfty0Box (N1 + N2) L) (x : Y (N1 + N2)) :
    0 ≤ crossNumInt v Ψ x := by
  unfold crossNumInt
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (sq_nonneg _) (hv _)))

/-! ## Section 5 : the numerator/denominator of a state and the variational inequality -/

/-- The Rayleigh numerator of a (possibly non-admissible) function on the box. -/
noncomputable def boxNum (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (f : Y N → ℝ) : ℝ :=
  ∫ x in box N L, f x * (_root_.BoseGases.𝓗 N v f) x

/-- The denominator `∫ Ψ²` on the box. -/
noncomputable def boxDen (N : ℕ) (L : ℝ) (f : Y N → ℝ) : ℝ :=
  ∫ x in box N L, (f x) ^ 2

lemma boxDen_zero {N : ℕ} {L : ℝ} : boxDen N L (0 : Y N → ℝ) = 0 := by
  unfold boxDen
  simp

lemma boxNum_zero {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} : boxNum N L v (0 : Y N → ℝ) = 0 := by
  unfold boxNum
  simp

/-- The box integral of the square of an admissible state is positive. -/
lemma box_integral_sq_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (Φ : CInfty0Box N L) :
    0 < ∫ x in box N L, ((Φ : Y N → ℝ) x) ^ 2 := by
  let f : Y N → ℝ := fun x => ((Φ : Y N → ℝ) x) ^ 2
  have hnonneg : 0 ≤ᵐ[volume.restrict (box N L)] f := ae_of_all _ (fun x => sq_nonneg _)
  have hcontf : Continuous f := by
    dsimp [f]
    exact (psi_contDiff Φ).continuous.pow 2
  have hfi : IntegrableOn f (box N L) volume := by
    dsimp [f]
    rcases exists_bound_psi_sq hL Φ with ⟨M, hM0, hM⟩
    have hb : ∀ᵐ (x : Y N) ∂(volume.restrict (box N L)), ‖((Φ : Y N → ℝ) x) ^ 2‖ ≤ M :=
      ae_of_all _ (fun x => by
        rw [show ‖((Φ : Y N → ℝ) x) ^ 2‖ = ((Φ : Y N → ℝ) x) ^ 2 by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((Φ : Y N → ℝ) x))]]
        exact hM x)
    have hconst : Integrable (fun _ : Y N => M) (volume.restrict (box N L)) :=
      (integrableOn_const (s := box N L) (C := M)
        (hs := ne_of_lt (IsCompact.measure_lt_top (box_compact hL)))).integrable
    exact Integrable.mono' hconst hcontf.aestronglyMeasurable hb
  have hne : ∃ x0 : Y N, (Φ : Y N → ℝ) x0 ≠ 0 := by
    by_contra h
    apply Φ.nezero
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  rcases hne with ⟨x0, hx0⟩
  let S : Set (Y N) := {x | (Φ : Y N → ℝ) x ≠ 0}
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_ne.preimage (psi_contDiff Φ).continuous
  have hx0S : x0 ∈ S := hx0
  rcases (Metric.isOpen_iff.mp hSopen x0 hx0S) with ⟨ε, hε, hball⟩
  have hμball : 0 < (volume : Measure (Y N)) (Metric.ball x0 ε) := Metric.measure_ball_pos volume x0 hε
  have hsub : Metric.ball x0 ε ⊆ S ∩ box N L := by
    intro y hy
    constructor
    · exact hball hy
    · have hyS : y ∈ S := hball hy
      have hysupp : y ∈ Function.support (Φ : Y N → ℝ) := by
        exact hyS
      have hyt : y ∈ tsupport (Φ : Y N → ℝ) := subset_tsupport (Φ : Y N → ℝ) hysupp
      exact interior_subset (Φ.support hyt)
  have hSbox : S ∩ box N L ⊆ Function.support f ∩ box N L := by
    intro y hy
    constructor
    · dsimp [f]
      exact pow_ne_zero 2 hy.1
    · exact hy.2
  have hpos : 0 < (volume : Measure (Y N)) (Function.support f ∩ box N L) := by
    exact lt_of_lt_of_le hμball (measure_mono (hsub.trans hSbox))
  have hres := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume) (s := box N L) hnonneg hfi).2 hpos
  simpa [f] using hres

/-- The denominator of an admissible state is positive. -/
lemma boxDen_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (Φ : CInfty0Box N L) :
    0 < boxDen N L (Φ : Y N → ℝ) := by
  unfold boxDen
  exact box_integral_sq_pos hL Φ

/-- The Rayleigh quotient denominator equals `∫ Ψ²` (nonneg). -/
lemma boxDen_sqsqrt {N : ℕ} {L : ℝ} (f : Y N → ℝ) :
    (Real.sqrt (boxDen N L f)) ^ 2 = boxDen N L f := by
  rw [Real.sq_sqrt]
  unfold boxDen
  exact integral_nonneg (fun x => sq_nonneg (f x))

/-- The quotient appearing in `boxEnergy` equals `boxNum / boxDen` for admissible states. -/
lemma boxEnergy_quotient_eq {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Φ : CInfty0Box N L) :
    ((∫ x in box N L, (Φ : Y N → ℝ) x * (_root_.BoseGases.𝓗 N v (Φ : Y N → ℝ)) x) /
      (Real.sqrt (∫ x in box N L, (Φ : Y N → ℝ) x * (Φ : Y N → ℝ) x)) ^ 2)
    = boxNum N L v (Φ : Y N → ℝ) / boxDen N L (Φ : Y N → ℝ) := by
  unfold boxNum boxDen
  have hden : (∫ x in box N L, (Φ : Y N → ℝ) x * (Φ : Y N → ℝ) x) =
        ∫ x in box N L, ((Φ : Y N → ℝ) x) ^ 2 := by
        apply setIntegral_congr_fun
        · exact (box_measurable N L)
        · intro x hx; ring
  rw [hden]
  rw [Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ((Φ : Y N → ℝ) x)))]

/-- The box energy is at most the Rayleigh quotient of every admissible state. -/
lemma boxEnergy_le_quotient {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Φ : CInfty0Box N L) :
    boxEnergy N L v ≤ boxNum N L v (Φ : Y N → ℝ) / boxDen N L (Φ : Y N → ℝ) := by
  have hquot : boxEnergy N L v ≤
      ((∫ x in box N L, (Φ : Y N → ℝ) x * (_root_.BoseGases.𝓗 N v (Φ : Y N → ℝ)) x) /
      (Real.sqrt (∫ x in box N L, (Φ : Y N → ℝ) x * (Φ : Y N → ℝ) x)) ^ 2) := by
    unfold boxEnergy
    apply ciInf_le
    · -- the family is bounded below by 0
      refine ⟨0, ?_⟩
      intro y hy
      rcases hy with ⟨Θ, rfl⟩
      have hswap : (∫ x in box N L, (Θ : Y N → ℝ) x * (Θ : Y N → ℝ) x) =
          ∫ x in box N L, ((Θ : Y N → ℝ) x) ^ 2 := by
          apply setIntegral_congr_fun
          · exact (box_measurable N L)
          · intro x hx; ring
      change 0 ≤ (∫ x in box N L, (Θ : Y N → ℝ) x * (_root_.BoseGases.𝓗 N v (Θ : Y N → ℝ)) x) /
        (Real.sqrt (∫ x in box N L, (Θ : Y N → ℝ) x * (Θ : Y N → ℝ) x)) ^ 2
      rw [hswap]
      exact rayleigh_quot_nonneg hL hv Θ
  rw [boxEnergy_quotient_eq Φ] at hquot
  exact hquot

/-- Variational inequality: `E · ∫ Ψ² ≤ ∫ Ψ · 𝓗 Ψ` for every admissible state. -/
lemma boxEnergy_mul_den_le_num {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Φ : CInfty0Box N L) :
    boxEnergy N L v * boxDen N L (Φ : Y N → ℝ) ≤ boxNum N L v (Φ : Y N → ℝ) := by
  have hle := boxEnergy_le_quotient (N := N) (L := L) (v := v) hL hv Φ
  have hden : 0 < boxDen N L (Φ : Y N → ℝ) := boxDen_pos hL Φ
  -- from E ≤ num/den and den > 0 get E·den ≤ num
  rwa [le_div_iff₀ hden] at hle

/-! ## Section 6 : assembly - the per-state superadditivity inequality -/

/-- The box-integral of the big numerator equals its full-space integral. -/
lemma bigNumInt_integral_eq {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L) :
    (∫ x in box (N1 + N2) L, bigNumInt v Ψ x) = ∫ x : Y (N1 + N2), bigNumInt v Ψ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  unfold bigNumInt
  -- Ψ vanishes outside the box
  have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
  simp [hz]

/-- the big numerator integrand is integrable on the box. -/
lemma integrableOn_bigNumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    IntegrableOn (bigNumInt v Ψ) (box (N1 + N2) L) volume := by
  have hbox : Integrable (bigNumInt v Ψ) (volume.restrict (box (N1 + N2) L)) := by
    have hk : Integrable (kinIntegrand (N1 + N2) L Ψ)
        (volume.restrict (box (N1 + N2) L)) :=
      (integrableOn_kinIntegrand (N := N1 + N2) (L := L) hL Ψ).integrable
    have hi : Integrable (intIntegrand (N1 + N2) L v Ψ)
        (volume.restrict (box (N1 + N2) L)) :=
      (integrableOn_intIntegrand (N := N1 + N2) (L := L) hL (v := v) hv1 Ψ).integrable
    have hsum := Integrable.add hk hi
    have hEq : bigNumInt v Ψ =
        (kinIntegrand (N1 + N2) L Ψ + intIntegrand (N1 + N2) L v Ψ) := by
      funext x
      unfold bigNumInt
      rw [← numerator_integrand_eq (N1 + N2) L v Ψ]
    rwa [hEq]
  exact hbox

/-- the big numerator integrand is integrable on the whole space. -/
lemma integrable_bigNumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    Integrable (bigNumInt v Ψ) := by
  have hsup : Function.support (bigNumInt v Ψ) ⊆ box (N1 + N2) L := by
    intro x hx
    by_contra h
    have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ h
    unfold bigNumInt at hx
    simp [hz] at hx
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp (integrableOn_bigNumInt hL v hv1 Ψ)

/-- Ψ² is integrable on the whole space. -/
lemma integrable_Ψ2 {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box (N1 + N2) L) :
    Integrable (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) := by
  have hcont : Continuous (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) :=
    (psi_contDiff Ψ).continuous.pow 2
  have hmul : HasCompactSupport (fun x : Y (N1 + N2) => (Ψ : Y (N1 + N2) → ℝ) x * (Ψ : Y (N1 + N2) → ℝ) x) :=
    (hasCompactSupport_Ψ hL Ψ).mul_right
  have hcs : HasCompactSupport (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) := by
    simpa [pow_two] using hmul
  exact Continuous.integrable_of_hasCompactSupport hcont hcs

/-- Ψ² vanishes outside the box, so the full integral equals the box integral. -/
lemma Ψ2_integral_eq {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) :
    (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) =
      ∫ x in box (N1 + N2) L, ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box (N1 + N2) L) (f := fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
    (by
      intro x hx
      have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
      simp [hz])).symm

/-- each block integrand vanishes outside the box. -/
lemma block1NumInt_eq_zero_of_not_mem {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ)
    (Ψ : CInfty0Box (N1 + N2) L) {x : Y (N1 + N2)} (hx : x ∉ box (N1 + N2) L) :
    block1NumInt v Ψ x = 0 := by
  unfold block1NumInt
  have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
  simp [hz]

lemma block2NumInt_eq_zero_of_not_mem {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ)
    (Ψ : CInfty0Box (N1 + N2) L) {x : Y (N1 + N2)} (hx : x ∉ box (N1 + N2) L) :
    block2NumInt v Ψ x = 0 := by
  unfold block2NumInt
  have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
  simp [hz]

/-- the cross integrand vanishes outside the box. -/
lemma crossNumInt_eq_zero_of_not_mem {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ)
    (Ψ : CInfty0Box (N1 + N2) L) {x : Y (N1 + N2)} (hx : x ∉ box (N1 + N2) L) :
    crossNumInt v Ψ x = 0 := by
  unfold crossNumInt
  have hz : (Ψ : Y (N1 + N2) → ℝ) x = 0 := psi_eq_zero_of_not_mem_box Ψ hx
  simp [hz]

/-! ### expansion of a one-body numerator at a point -/

/-- expansion of `f u * 𝓗 N v f u` into kinetic and pair sums. -/
lemma num_expand {N : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (f : Y N → ℝ) (u : Y N) :
    f u * (_root_.BoseGases.𝓗 N v f) u
    = (∑ i : Fin N, f u * (- partialLaplacian i f u))
      + (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
          v (u p.1 - u p.2) * (f u) ^ 2) := by
  unfold _root_.BoseGases.𝓗
  rw [mul_add]
  rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin N)))
      (f := fun i : Fin N => - partialLaplacian i f u)]
  have hint : f u * (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
        v (u p.1 - u p.2) * f u)
      = ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
          v (u p.1 - u p.2) * (f u) ^ 2 := by
    rw [Finset.mul_sum (s := (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)))]
    refine Finset.sum_congr rfl ?_
    intro p hp
    ring
  rw [hint]

/-- block-1 numerator value at a combined point equals the N1-numerator of the slice. -/
lemma block1NumInt_combine {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L)
    (u : Y N1) (w : Y N2) :
    block1NumInt v Ψ (combine u w)
      = (slice1 Ψ w u) * (_root_.BoseGases.𝓗 N1 v (slice1 Ψ w)) u := by
  unfold block1NumInt slice1
  -- kinetic: compare with the slice kinetic sum via partialLaplacian_combine_left
  have hkin : (∑ i : Fin N1, (Ψ : Y (N1 + N2) → ℝ) (combine u w) *
        (- partialLaplacian (Fin.castAdd N2 i) (Ψ : Y (N1 + N2) → ℝ) (combine u w)))
      = ∑ i : Fin N1, (fun u' : Y N1 => (Ψ : Y (N1 + N2) → ℝ) (combine u' w)) u *
        (- partialLaplacian i (fun u' : Y N1 => (Ψ : Y (N1 + N2) → ℝ) (combine u' w)) u) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [partialLaplacian_combine_left (f := (Ψ : Y (N1 + N2) → ℝ)) u w i]
  have hpair : (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) (combine u w)) ^ 2 *
          v ((combine u w) (Fin.castAdd N2 p.1) - (combine u w) (Fin.castAdd N2 p.2)))
      = (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
          v (u p.1 - u p.2) * ((fun u' : Y N1 => (Ψ : Y (N1 + N2) → ℝ) (combine u' w)) u) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [combine_left, combine_left]
    ring
  rw [hkin, hpair]
  -- the two sums equal φ u · 𝓗 N1 v φ u via the expansion (in reverse)
  rw [← num_expand (N := N1) (L := L) v (fun u' : Y N1 => (Ψ : Y (N1 + N2) → ℝ) (combine u' w)) u]

/-- block-2 version. -/
lemma block2NumInt_combine {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L)
    (u : Y N1) (w : Y N2) :
    block2NumInt v Ψ (combine u w)
      = (slice2 Ψ u w) * (_root_.BoseGases.𝓗 N2 v (slice2 Ψ u)) w := by
  unfold block2NumInt slice2
  have hkin : (∑ j : Fin N2, (Ψ : Y (N1 + N2) → ℝ) (combine u w) *
        (- partialLaplacian (Fin.natAdd N1 j) (Ψ : Y (N1 + N2) → ℝ) (combine u w)))
      = ∑ j : Fin N2, (fun w' : Y N2 => (Ψ : Y (N1 + N2) → ℝ) (combine u w')) w *
        (- partialLaplacian j (fun w' : Y N2 => (Ψ : Y (N1 + N2) → ℝ) (combine u w')) w) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [partialLaplacian_combine_right (f := (Ψ : Y (N1 + N2) → ℝ)) u w j]
  have hpair : (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) (combine u w)) ^ 2 *
          v ((combine u w) (Fin.natAdd N1 p.1) - (combine u w) (Fin.natAdd N1 p.2)))
      = (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
          v (w p.1 - w p.2) * ((fun w' : Y N2 => (Ψ : Y (N1 + N2) → ℝ) (combine u w')) w) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [combine_right, combine_right]
    ring
  rw [hkin, hpair]
  rw [← num_expand (N := N2) (L := L) v (fun w' : Y N2 => (Ψ : Y (N1 + N2) → ℝ) (combine u w')) w]

/-! ### the slice variational inequalities -/

/-- a slice vanishes outside its own box. -/
lemma slice1_eq_zero_of_not_mem_box {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L)
    {w : Y N2} {u : Y N1} (hu : u ∉ box N1 L) : slice1 Ψ w u = 0 := by
  unfold slice1
  by_contra h
  have hsupp : combine u w ∈ Function.support (Ψ : Y (N1 + N2) → ℝ) := h
  have hb : combine u w ∈ box (N1 + N2) L := psi_support_box Ψ hsupp
  exact hu ((box_combine_mem (L := L) u w).mp hb).1

/-- a slice vanishes outside its own box. -/
lemma slice2_eq_zero_of_not_mem_box {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L)
    {u : Y N1} {w : Y N2} (hw : w ∉ box N2 L) : slice2 Ψ u w = 0 := by
  unfold slice2
  by_contra h
  have hsupp : combine u w ∈ Function.support (Ψ : Y (N1 + N2) → ℝ) := h
  have hb : combine u w ∈ box (N1 + N2) L := psi_support_box Ψ hsupp
  exact hw ((box_combine_mem (L := L) u w).mp hb).2

/-- full-space integral = box integral when the integrand vanishes outside the box. -/
lemma integral_full_eq_box_of_vanish {N : ℕ} {L : ℝ} (f : Y N → ℝ)
    (hvan : ∀ x ∉ box N L, f x = 0) :
    (∫ x : Y N, f x) = ∫ x in box N L, f x := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (f := f) hvan).symm

/-- the full-space denominator of a block-1 slice. -/
lemma slice1_full_den {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2) :
    (∫ u : Y N1, (slice1 Ψ w u) ^ 2) = boxDen N1 L (slice1 Ψ w) := by
  unfold boxDen
  exact integral_full_eq_box_of_vanish (N := N1) (L := L)
    (fun u => (slice1 Ψ w u) ^ 2) (by
      intro u hu
      have hz := slice1_eq_zero_of_not_mem_box (Ψ := Ψ) (w := w) hu
      simp [hz])

/-- the full-space numerator of a block-1 slice. -/
lemma slice1_full_num {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L)
    (w : Y N2) :
    (∫ u : Y N1, (slice1 Ψ w u) * (_root_.BoseGases.𝓗 N1 v (slice1 Ψ w)) u)
      = boxNum N1 L v (slice1 Ψ w) := by
  unfold boxNum
  exact integral_full_eq_box_of_vanish (N := N1) (L := L)
    (fun u => (slice1 Ψ w u) * (_root_.BoseGases.𝓗 N1 v (slice1 Ψ w)) u) (by
      intro u hu
      have hz := slice1_eq_zero_of_not_mem_box (Ψ := Ψ) (w := w) hu
      simp [hz])

/-- the full-space denominator of a block-2 slice. -/
lemma slice2_full_den {N1 N2 : ℕ} {L : ℝ} (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1) :
    (∫ w : Y N2, (slice2 Ψ u w) ^ 2) = boxDen N2 L (slice2 Ψ u) := by
  unfold boxDen
  exact integral_full_eq_box_of_vanish (N := N2) (L := L)
    (fun w => (slice2 Ψ u w) ^ 2) (by
      intro w hw
      have hz := slice2_eq_zero_of_not_mem_box (Ψ := Ψ) (u := u) hw
      simp [hz])

/-- the full-space numerator of a block-2 slice. -/
lemma slice2_full_num {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : CInfty0Box (N1 + N2) L)
    (u : Y N1) :
    (∫ w : Y N2, (slice2 Ψ u w) * (_root_.BoseGases.𝓗 N2 v (slice2 Ψ u)) w)
      = boxNum N2 L v (slice2 Ψ u) := by
  unfold boxNum
  exact integral_full_eq_box_of_vanish (N := N2) (L := L)
    (fun w => (slice2 Ψ u w) * (_root_.BoseGases.𝓗 N2 v (slice2 Ψ u)) w) (by
      intro w hw
      have hz := slice2_eq_zero_of_not_mem_box (Ψ := Ψ) (u := u) hw
      simp [hz])

/-- the block-1 slice satisfies the variational inequality pointwise in `w`. -/
lemma slice1_var {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2) :
    boxEnergy N1 L v * (∫ u : Y N1, (slice1 Ψ w u) ^ 2)
      ≤ ∫ u : Y N1, (slice1 Ψ w u) * (_root_.BoseGases.𝓗 N1 v (slice1 Ψ w)) u := by
  by_cases h0 : slice1 Ψ w = 0
  · -- zero slice: trivial
    rw [h0]
    simp
  · -- nonzero slice: use the element
    let Φ := slice1Elem Ψ w h0
    have hvar := boxEnergy_mul_den_le_num (N := N1) (L := L) (v := v) hL hv Φ
    -- boxDen/boxNum of the element equal those of the underlying slice function
    have hden : boxDen N1 L (Φ : Y N1 → ℝ) = boxDen N1 L (slice1 Ψ w) := rfl
    have hnum : boxNum N1 L v (Φ : Y N1 → ℝ) = boxNum N1 L v (slice1 Ψ w) := rfl
    rw [hden, hnum] at hvar
    -- connect box quantities to full-space quantities
    rw [slice1_full_den Ψ w, slice1_full_num v Ψ w]
    exact hvar

/-- the block-2 slice satisfies the variational inequality pointwise in `u`. -/
lemma slice2_var {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1) :
    boxEnergy N2 L v * (∫ w : Y N2, (slice2 Ψ u w) ^ 2)
      ≤ ∫ w : Y N2, (slice2 Ψ u w) * (_root_.BoseGases.𝓗 N2 v (slice2 Ψ u)) w := by
  by_cases h0 : slice2 Ψ u = 0
  · rw [h0]
    simp
  · let Φ := slice2Elem Ψ u h0
    have hvar := boxEnergy_mul_den_le_num (N := N2) (L := L) (v := v) hL hv Φ
    have hden : boxDen N2 L (Φ : Y N2 → ℝ) = boxDen N2 L (slice2 Ψ u) := rfl
    have hnum : boxNum N2 L v (Φ : Y N2 → ℝ) = boxNum N2 L v (slice2 Ψ u) := rfl
    rw [hden, hnum] at hvar
    rw [slice2_full_den Ψ u, slice2_full_num v Ψ u]
    exact hvar

/-! ### integrability of the block parts -/

/-- `Ψ²·w(x_i − x_j)` is integrable over the box for distinct `i, j` and measurable `w` of
finite `L¹`-norm. -/
lemma integrableOn_Ψ2_w_of_measurable {N : ℕ} {L : ℝ} (hL : 0 < L) {w : ℝ³ → ℝ}
    (hwm : Measurable w) (hfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (⊤ : ℝ≥0∞)) (Ψ : CInfty0Box N L)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)) (box N L) volume := by
  let μ_box : Measure (Y N) := volume.restrict (box N L)
  rcases exists_bound_psi_sq hL Ψ with ⟨M, hM0, hM⟩
  have hw : IntegrableOn (fun x : Y N => |w (x i - x j)|) (box N L) volume :=
    integrableOn_abs_pair_of_measurable hL hwm hfin i j hij
  have hmeas : AEStronglyMeasurable
      (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)) μ_box := by
    have hw' : Measurable (fun x : Y N => w (x i - x j)) := by fun_prop
    exact (measurable_Ψ2_mul Ψ hw').aestronglyMeasurable
  refine Integrable.mono' (μ := μ_box)
    (f := fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j))
    (g := fun x : Y N => M * |w (x i - x j)|) ?_ hmeas ?_
  · exact (hw.integrable.const_mul M)
  · filter_upwards with x
    have hb : |((Ψ : Y N → ℝ) x)^2| ≤ M := by
      rw [abs_of_nonneg (sq_nonneg ((Ψ : Y N → ℝ) x))]
      exact hM x
    calc
      ‖((Ψ : Y N → ℝ) x)^2 * w (x i - x j)‖
          = |((Ψ : Y N → ℝ) x)^2| * |w (x i - x j)| := by simp
      _ ≤ M * |w (x i - x j)| := by
          exact mul_le_mul hb le_rfl (abs_nonneg _) hM0

/-- `Ψ²·v(x_i − x_j)` is integrable over the box for distinct `i, j`. -/
lemma integrableOn_Ψ2_v {N : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    (Ψ : CInfty0Box N L) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * v (x i - x j)) (box N L) volume := by
  have hvInt : Integrable v := (memLp_one_iff_integrable.mp hv1)
  have hvae : AEMeasurable v := hvInt.aemeasurable
  let w : ℝ³ → ℝ := AEMeasurable.mk v hvae
  have hwm : Measurable w := AEMeasurable.measurable_mk hvae
  have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
  have hwInt : Integrable w := hvInt.congr hvw
  have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (⊤ : ℝ≥0∞) := hwInt.hasFiniteIntegral
  have hmain : IntegrableOn (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j))
      (box N L) volume := integrableOn_Ψ2_w_of_measurable hL hwm hwfin Ψ hij
  -- a.e. equality of the two integrands on the box
  have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (Y N)).restrict (box N L) {x : Y N | x i - x j ∈ t} = 0 :=
    null_preimage_pair hL htm ht0 i j hij
  have hfail : (volume : Measure (Y N)).restrict (box N L)
      {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) ≠ ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)} = 0 := by
    have hsub : {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) ≠ ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)}
        ⊆ {x : Y N | x i - x j ∈ t} := by
      intro x hx
      apply hNt
      intro hEq
      exact hx (by rw [hEq])
    apply le_antisymm
    · calc
        (volume : Measure (Y N)).restrict (box N L)
            {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) ≠ ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)}
            ≤ (volume : Measure (Y N)).restrict (box N L) {x : Y N | x i - x j ∈ t} :=
              measure_mono hsub
        _ = 0 := hpre
    · positivity
  have hmem : {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) = ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)} ∈
      ae (volume.restrict (box N L)) := by
    rw [mem_ae_iff]
    rw [show ({x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) = ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)}ᶜ) =
        {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) ≠ ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)} by ext x; simp]
    exact hfail
  have hae_eq : (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * v (x i - x j)) =ᵐ[volume.restrict (box N L)]
      (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)) := by
    rw [show (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * v (x i - x j)) =ᵐ[volume.restrict (box N L)]
          (fun x : Y N => ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)) ↔
        {x : Y N | ((Ψ : Y N → ℝ) x)^2 * v (x i - x j) = ((Ψ : Y N → ℝ) x)^2 * w (x i - x j)} ∈
          ae (volume.restrict (box N L)) by rfl]
    exact hmem
  exact hmain.integrable.congr hae_eq.symm

/-- the block-1 integrand is integrable over the box. -/
lemma integrableOn_block1NumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    IntegrableOn (block1NumInt v Ψ) (box (N1 + N2) L) volume := by
  let μ : Measure (Y (N1 + N2)) := volume.restrict (box (N1 + N2) L)
  have h1 : Integrable (fun x : Y (N1 + N2) =>
      ∑ i : Fin N1, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.castAdd N2 i) (Ψ : Y (N1 + N2) → ℝ) x)) μ := by
    refine integrable_finsetSum (s := (Finset.univ : Finset (Fin N1))) (f := fun i x =>
      (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.castAdd N2 i) (Ψ : Y (N1 + N2) → ℝ) x)) ?_
    intro i hi
    exact (integrableOn_kinetic_term (N := N1 + N2) (L := L) hL Ψ (Fin.castAdd N2 i)).integrable
  have h2 : Integrable (fun x : Y (N1 + N2) =>
      ∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) x)^2 * v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2))) μ := by
    refine integrable_finsetSum (s := (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)))
      (f := fun p x => ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2))) ?_
    intro p hp
    have hne : Fin.castAdd N2 p.1 ≠ Fin.castAdd N2 p.2 := by
      intro h
      have hvlt : (Fin.castAdd N2 p.1).val < (Fin.castAdd N2 p.2).val := by
        simpa using (Finset.mem_filter.mp hp).2
      rw [h] at hvlt
      exact (lt_irrefl _) hvlt
    exact (integrableOn_Ψ2_v (N := N1 + N2) (L := L) hL hv1 Ψ hne).integrable
  have hsum := Integrable.add h1 h2
  have hEq : block1NumInt v Ψ = (fun x : Y (N1 + N2) =>
      (∑ i : Fin N1, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.castAdd N2 i) (Ψ : Y (N1 + N2) → ℝ) x)) +
      (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) x)^2 * v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2)))) := by
    rfl
  exact (hEq ▸ hsum)

/-- the block-2 integrand is integrable over the box. -/
lemma integrableOn_block2NumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    IntegrableOn (block2NumInt v Ψ) (box (N1 + N2) L) volume := by
  let μ : Measure (Y (N1 + N2)) := volume.restrict (box (N1 + N2) L)
  have h1 : Integrable (fun x : Y (N1 + N2) =>
      ∑ j : Fin N2, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.natAdd N1 j) (Ψ : Y (N1 + N2) → ℝ) x)) μ := by
    refine integrable_finsetSum (s := (Finset.univ : Finset (Fin N2))) (f := fun j x =>
      (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.natAdd N1 j) (Ψ : Y (N1 + N2) → ℝ) x)) ?_
    intro j hj
    exact (integrableOn_kinetic_term (N := N1 + N2) (L := L) hL Ψ (Fin.natAdd N1 j)).integrable
  have h2 : Integrable (fun x : Y (N1 + N2) =>
      ∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) x)^2 * v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2))) μ := by
    refine integrable_finsetSum (s := (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)))
      (f := fun p x => ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2))) ?_
    intro p hp
    have hne : Fin.natAdd N1 p.1 ≠ Fin.natAdd N1 p.2 := by
      intro h
      have hvlt : (Fin.natAdd N1 p.1).val < (Fin.natAdd N1 p.2).val := by
        simpa using (Finset.mem_filter.mp hp).2
      rw [h] at hvlt
      exact (lt_irrefl _) hvlt
    exact (integrableOn_Ψ2_v (N := N1 + N2) (L := L) hL hv1 Ψ hne).integrable
  have hsum := Integrable.add h1 h2
  have hEq : block2NumInt v Ψ = (fun x : Y (N1 + N2) =>
      (∑ j : Fin N2, (Ψ : Y (N1 + N2) → ℝ) x *
        (- partialLaplacian (Fin.natAdd N1 j) (Ψ : Y (N1 + N2) → ℝ) x)) +
      (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
        ((Ψ : Y (N1 + N2) → ℝ) x)^2 * v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2)))) := by
    rfl
  exact (hEq ▸ hsum)

/-- the cross integrand is integrable over the box. -/
lemma integrableOn_crossNumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    IntegrableOn (crossNumInt v Ψ) (box (N1 + N2) L) volume := by
  let μ : Measure (Y (N1 + N2)) := volume.restrict (box (N1 + N2) L)
  -- cross = sum over i1 : Fin N1 of (sum over j2 : Fin N2 ...)
  have hterm : ∀ i : Fin N1, Integrable (fun x : Y (N1 + N2) =>
      ∑ j : Fin N2, ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))) μ := by
    intro i
    refine integrable_finsetSum (s := (Finset.univ : Finset (Fin N2))) (f := fun j x =>
      ((Ψ : Y (N1 + N2) → ℝ) x)^2 * v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))) ?_
    intro j hj
    have hne : Fin.castAdd N2 i ≠ Fin.natAdd N1 j := by
      -- values: < N1 vs ≥ N1
      intro h
      have hv1' : (Fin.castAdd N2 i).val < N1 := by simpa using i.isLt
      have hv2 : N1 ≤ (Fin.natAdd N1 j).val := by
        dsimp [Fin.natAdd]
        exact Nat.le_add_right N1 j.val
      rw [h] at hv1'
      exact (not_lt_of_ge hv2) hv1'
    exact (integrableOn_Ψ2_v (N := N1 + N2) (L := L) hL hv1 Ψ hne).integrable
  have hsum : Integrable (fun x : Y (N1 + N2) =>
      ∑ i : Fin N1, ∑ j : Fin N2, ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))) μ := by
    refine integrable_finsetSum (s := (Finset.univ : Finset (Fin N1))) (f := fun i x =>
      ∑ j : Fin N2, ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))) ?_
    intro i hi
    exact hterm i
  have hEq : crossNumInt v Ψ = (fun x : Y (N1 + N2) =>
      ∑ i : Fin N1, ∑ j : Fin N2, ((Ψ : Y (N1 + N2) → ℝ) x)^2 *
        v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j))) := by
    rfl
  exact (hEq ▸ hsum)

/-- the block-1 integrand is integrable over the whole space. -/
lemma integrable_block1NumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    Integrable (block1NumInt v Ψ) := by
  have hsup : Function.support (block1NumInt v Ψ) ⊆ box (N1 + N2) L := by
    intro x hx
    by_contra h
    exact hx (block1NumInt_eq_zero_of_not_mem v Ψ h)
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp (integrableOn_block1NumInt hL v hv1 Ψ)

/-- the block-2 integrand is integrable over the whole space. -/
lemma integrable_block2NumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    Integrable (block2NumInt v Ψ) := by
  have hsup : Function.support (block2NumInt v Ψ) ⊆ box (N1 + N2) L := by
    intro x hx
    by_contra h
    exact hx (block2NumInt_eq_zero_of_not_mem v Ψ h)
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp (integrableOn_block2NumInt hL v hv1 Ψ)

/-- the cross integrand is integrable over the whole space. -/
lemma integrable_crossNumInt {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) (v : ℝ³ → ℝ)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    Integrable (crossNumInt v Ψ) := by
  have hsup : Function.support (crossNumInt v Ψ) ⊆ box (N1 + N2) L := by
    intro x hx
    by_contra h
    exact hx (crossNumInt_eq_zero_of_not_mem v Ψ h)
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp (integrableOn_crossNumInt hL v hv1 Ψ)

/-! ### the block bounds -/

/-- slice-1 variational inequality, expressed in `blockEquiv` coordinates. -/
lemma slice1_var_block {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box (N1 + N2) L) (w : Y N2) :
    boxEnergy N1 L v * (∫ u : Y N1, ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2)
      ≤ ∫ u : Y N1, block1NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
  have hvar := slice1_var (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv Ψ w
  have h1 : (∫ u : Y N1, (slice1 Ψ w u) ^ 2) =
      ∫ u : Y N1, ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with u
    congr 1
    simp [slice1, blockEquiv_apply]
  have h2 : (∫ u : Y N1, (slice1 Ψ w u) * (_root_.BoseGases.𝓗 N1 v (slice1 Ψ w)) u)
      = ∫ u : Y N1, block1NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
    apply integral_congr_ae
    filter_upwards with u
    rw [blockEquiv_apply]
    rw [block1NumInt_combine v Ψ u w]
  rw [h1, h2] at hvar
  exact hvar

/-- slice-2 variational inequality, expressed in `blockEquiv` coordinates. -/
lemma slice2_var_block {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box (N1 + N2) L) (u : Y N1) :
    boxEnergy N2 L v * (∫ w : Y N2, ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2)
      ≤ ∫ w : Y N2, block2NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
  have hvar := slice2_var (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv Ψ u
  have h1 : (∫ w : Y N2, (slice2 Ψ u w) ^ 2) =
      ∫ w : Y N2, ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with w
    congr 1
    simp [slice2, blockEquiv_apply]
  have h2 : (∫ w : Y N2, (slice2 Ψ u w) * (_root_.BoseGases.𝓗 N2 v (slice2 Ψ u)) w)
      = ∫ w : Y N2, block2NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [blockEquiv_apply]
    rw [block2NumInt_combine v Ψ u w]
  rw [h1, h2] at hvar
  exact hvar

/-- Change of variables + Fubini in the `w`-outer order. -/
lemma integral_combine_swapped {N1 N2 : ℕ} (G : Y (N1 + N2) → ℝ)
    (hG : Integrable G) :
    (∫ w : Y N2, ∫ u : Y N1, G (combine u w)) = ∫ x : Y (N1 + N2), G x := by
  have hmp : MeasurePreserving (blockEquiv N1 N2) volume volume := measurePreserving_blockEquiv N1 N2
  have hprod : Integrable (fun p : Y N1 × Y N2 => G ((blockEquiv N1 N2) p))
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := G))
    exact hi.2 hG
  rw [← integral_iterated_swap (H := fun (u : Y N1) (w : Y N2) => G (combine u w))]
  · exact integral_combine G hG
  · have hpe : (fun p : Y N1 × Y N2 => G (combine p.1 p.2)) =
        fun p => G ((blockEquiv N1 N2) p) := by
      funext p
      congr 1
      exact (blockEquiv_apply p.1 p.2).symm
    rw [hpe]
    exact hprod

/-- Change of variables + Fubini in the `w`-outer order, `blockEquiv` form. -/
lemma integral_blockEquiv_swapped {N1 N2 : ℕ} (G : Y (N1 + N2) → ℝ)
    (hG : Integrable G) :
    (∫ w : Y N2, ∫ u : Y N1, G (blockEquiv N1 N2 (u, w))) = ∫ x : Y (N1 + N2), G x := by
  calc
    (∫ w : Y N2, ∫ u : Y N1, G (blockEquiv N1 N2 (u, w)))
        = ∫ w : Y N2, ∫ u : Y N1, G (combine u w) := by
          apply integral_congr_ae
          filter_upwards with w
          apply integral_congr_ae
          filter_upwards with u
          congr 1
          rw [blockEquiv_apply]
    _ = ∫ x : Y (N1 + N2), G x := integral_combine_swapped G hG


/-- Change of variables + Fubini in the `u`-outer order, `blockEquiv` form. -/
lemma integral_blockEquiv {N1 N2 : ℕ} (G : Y (N1 + N2) → ℝ)
    (hG : Integrable G) :
    (∫ u : Y N1, ∫ w : Y N2, G (blockEquiv N1 N2 (u, w))) = ∫ x : Y (N1 + N2), G x := by
  calc
    (∫ u : Y N1, ∫ w : Y N2, G (blockEquiv N1 N2 (u, w)))
        = ∫ u : Y N1, ∫ w : Y N2, G (combine u w) := by
          apply integral_congr_ae
          filter_upwards with u
          apply integral_congr_ae
          filter_upwards with w
          congr 1
          rw [blockEquiv_apply]
    _ = ∫ x : Y (N1 + N2), G x := integral_combine G hG

/-- lower bound of the block-1 part: `E1·∫Ψ² ≤ ∫ block1NumInt`. -/
lemma block1_bound {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    boxEnergy N1 L v * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
      ≤ ∫ x : Y (N1 + N2), block1NumInt v Ψ x := by
  let E1 := boxEnergy N1 L v
  have hmp : MeasurePreserving (blockEquiv N1 N2) volume volume := measurePreserving_blockEquiv N1 N2
  have hB1full : Integrable (block1NumInt v Ψ) := integrable_block1NumInt hL v hv1 Ψ
  have hP2full : Integrable (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) :=
    integrable_Ψ2 hL Ψ
  have hB1 : Integrable (fun p : Y N1 × Y N2 => block1NumInt v Ψ (blockEquiv N1 N2 p))
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := block1NumInt v Ψ))
    exact hi.2 hB1full
  have hP2 : Integrable (fun p : Y N1 × Y N2 => ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 p)) ^ 2)
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2))
    exact hi.2 hP2full
  -- section integrals are integrable in w
  have hS1 : Integrable (fun w : Y N2 => ∫ u : Y N1,
      block1NumInt v Ψ (blockEquiv N1 N2 (u, w))) := by
    exact Integrable.integral_prod_right hB1
  have hT1 : Integrable (fun w : Y N2 => ∫ u : Y N1,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2) := by
    exact Integrable.integral_prod_right hP2
  -- pointwise inequality and integrate over w
  have hpt : ∀ w : Y N2, E1 * (∫ u : Y N1,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2)
      ≤ ∫ u : Y N1, block1NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
    intro w
    exact slice1_var_block (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv Ψ w
  have hineq : (∫ w : Y N2, E1 * (∫ u : Y N1,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      ≤ ∫ w : Y N2, (∫ u : Y N1, block1NumInt v Ψ (blockEquiv N1 N2 (u, w))) := by
    refine integral_mono ?_ hS1 ?_
    · -- integrability of the constant-multiple function
      have hc : Integrable (fun w : Y N2 => E1 * (∫ u : Y N1,
          ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2)) := by
        exact hT1.const_mul E1
      exact hc
    · intro w
      exact hpt w
  have hstep1 : (∫ w : Y N2, (∫ u : Y N1, block1NumInt v Ψ (blockEquiv N1 N2 (u, w))))
      = ∫ x : Y (N1 + N2), block1NumInt v Ψ x := by
    exact integral_blockEquiv_swapped (block1NumInt v Ψ) hB1full
  have hstep2 : E1 * (∫ w : Y N2, (∫ u : Y N1,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      = E1 * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) := by
    have hT : (∫ w : Y N2, (∫ u : Y N1,
        ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
        = ∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 := by
      exact integral_blockEquiv_swapped
        (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) hP2full
    rw [hT]
  have hconst : (∫ w : Y N2, E1 * (∫ u : Y N1,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      = E1 * (∫ w : Y N2, ∫ u : Y N1,
          ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2) := by
    rw [integral_const_mul]
  rw [hconst, hstep2] at hineq
  rw [hstep1] at hineq
  exact hineq

/-- lower bound of the block-2 part: `E2·∫Ψ² ≤ ∫ block2NumInt`. -/
lemma block2_bound {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    boxEnergy N2 L v * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
      ≤ ∫ x : Y (N1 + N2), block2NumInt v Ψ x := by
  let E2 := boxEnergy N2 L v
  have hmp : MeasurePreserving (blockEquiv N1 N2) volume volume := measurePreserving_blockEquiv N1 N2
  have hB2full : Integrable (block2NumInt v Ψ) := integrable_block2NumInt hL v hv1 Ψ
  have hP2full : Integrable (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) :=
    integrable_Ψ2 hL Ψ
  have hB2 : Integrable (fun p : Y N1 × Y N2 => block2NumInt v Ψ (blockEquiv N1 N2 p))
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := block2NumInt v Ψ))
    exact hi.2 hB2full
  have hP2 : Integrable (fun p : Y N1 × Y N2 => ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 p)) ^ 2)
      ((volume : Measure (Y N1)).prod (volume : Measure (Y N2))) := by
    have hi := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (blockEquiv N1 N2))
      (g := fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2))
    exact hi.2 hP2full
  have hS2 : Integrable (fun u : Y N1 => ∫ w : Y N2,
      block2NumInt v Ψ (blockEquiv N1 N2 (u, w))) := by
    exact Integrable.integral_prod_left hB2
  have hT2 : Integrable (fun u : Y N1 => ∫ w : Y N2,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2) := by
    exact Integrable.integral_prod_left hP2
  have hpt : ∀ u : Y N1, E2 * (∫ w : Y N2,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2)
      ≤ ∫ w : Y N2, block2NumInt v Ψ (blockEquiv N1 N2 (u, w)) := by
    intro u
    exact slice2_var_block (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv Ψ u
  have hineq : (∫ u : Y N1, E2 * (∫ w : Y N2,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      ≤ ∫ u : Y N1, (∫ w : Y N2, block2NumInt v Ψ (blockEquiv N1 N2 (u, w))) := by
    refine integral_mono ?_ hS2 ?_
    · exact hT2.const_mul E2
    · intro u
      exact hpt u
  have hstep1 : (∫ u : Y N1, (∫ w : Y N2, block2NumInt v Ψ (blockEquiv N1 N2 (u, w))))
      = ∫ x : Y (N1 + N2), block2NumInt v Ψ x := by
    exact integral_blockEquiv (block2NumInt v Ψ) hB2full
  have hstep2 : E2 * (∫ u : Y N1, (∫ w : Y N2,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      = E2 * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) := by
    have hT : (∫ u : Y N1, (∫ w : Y N2,
        ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
        = ∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 := by
      exact integral_blockEquiv
        (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) hP2full
    rw [hT]
  have hconst : (∫ u : Y N1, E2 * (∫ w : Y N2,
      ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2))
      = E2 * (∫ u : Y N1, ∫ w : Y N2,
          ((Ψ : Y (N1 + N2) → ℝ) (blockEquiv N1 N2 (u, w))) ^ 2) := by
    rw [integral_const_mul]
  rw [hconst, hstep2] at hineq
  rw [hstep1] at hineq
  exact hineq

/-! ### the per-state superadditivity inequality -/

/-- for every state of `N1+N2` particles, `(E1+E2)·‖Ψ‖² ≤ ⟨Ψ, H Ψ⟩`. -/
lemma superadd_state {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box (N1 + N2) L) :
    (boxEnergy N1 L v + boxEnergy N2 L v) *
        (∫ x in box (N1 + N2) L, ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
      ≤ ∫ x in box (N1 + N2) L, bigNumInt v Ψ x := by
  let E1 := boxEnergy N1 L v
  let E2 := boxEnergy N2 L v
  let B1 := block1NumInt v Ψ
  let B2 := block2NumInt v Ψ
  let C := crossNumInt v Ψ
  let G := bigNumInt v Ψ
  have h1i : Integrable B1 := integrable_block1NumInt hL v hv1 Ψ
  have h2i : Integrable B2 := integrable_block2NumInt hL v hv1 Ψ
  have hci : Integrable C := integrable_crossNumInt hL v hv1 Ψ
  have hgi : Integrable G := integrable_bigNumInt hL v hv1 Ψ
  have hP2i : Integrable (fun x : Y (N1 + N2) => ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) :=
    integrable_Ψ2 hL Ψ
  have hEq' : G = B1 + B2 + C := by
    dsimp [G, B1, B2, C]
    exact bigNumInt_eq v Ψ
  -- the decomposition of the full-space integral
  have hdecomp : (∫ x : Y (N1 + N2), G x) = (∫ x : Y (N1 + N2), B1 x)
      + (∫ x : Y (N1 + N2), B2 x) + (∫ x : Y (N1 + N2), C x) := by
    have hsum12 : Integrable (B1 + B2) := Integrable.add h1i h2i
    calc
      (∫ x : Y (N1 + N2), G x) = (∫ x : Y (N1 + N2), ((B1 + B2) + C) x) := by
            rw [hEq']
      _ = (∫ x : Y (N1 + N2), (B1 + B2) x) + ∫ x : Y (N1 + N2), C x := by
            change (∫ x : Y (N1 + N2), (B1 + B2) x + C x)
              = (∫ x : Y (N1 + N2), (B1 + B2) x) + ∫ x : Y (N1 + N2), C x
            rw [integral_add (f := (fun x : Y (N1 + N2) => (B1 + B2) x)) (g := C) hsum12 hci]
      _ = ((∫ x : Y (N1 + N2), B1 x) + ∫ x : Y (N1 + N2), B2 x)
          + ∫ x : Y (N1 + N2), C x := by
            change (∫ x : Y (N1 + N2), B1 x + B2 x) + ∫ x : Y (N1 + N2), C x
              = ((∫ x : Y (N1 + N2), B1 x) + ∫ x : Y (N1 + N2), B2 x)
                + ∫ x : Y (N1 + N2), C x
            rw [integral_add (f := B1) (g := B2) h1i h2i]
  have hCnn : 0 ≤ ∫ x : Y (N1 + N2), C x := integral_nonneg (fun x => crossNumInt_nonneg hv Ψ x)
  have hGge : (∫ x : Y (N1 + N2), B1 x) + (∫ x : Y (N1 + N2), B2 x)
      ≤ ∫ x : Y (N1 + N2), G x := by
    rw [hdecomp]
    linarith
  have hb1 := block1_bound (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv hv1 Ψ
  have hb2 := block2_bound (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv hv1 Ψ
  have hfull : (E1 + E2) * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
      ≤ ∫ x : Y (N1 + N2), G x := by
    have hbb1 : E1 * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) ≤ ∫ x : Y (N1 + N2), B1 x := by
      simpa [E1, B1] using hb1
    have hbb2 : E2 * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2) ≤ ∫ x : Y (N1 + N2), B2 x := by
      simpa [E2, B2] using hb2
    have hb : (E1 + E2) * (∫ x : Y (N1 + N2), ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
        ≤ (∫ x : Y (N1 + N2), B1 x) + ∫ x : Y (N1 + N2), B2 x := by
      nlinarith
    exact le_trans hb hGge
  -- move to the box integrals
  dsimp [G] at hfull
  rw [Ψ2_integral_eq Ψ] at hfull
  rw [← bigNumInt_integral_eq v Ψ] at hfull
  simpa [E1, E2] using hfull

/-- Superadditivity of the box energy in the particle number (fixed box side `L`,
nonnegative potential): `E(N1+N2, L) ≥ E(N1, L) + E(N2, L)`. -/
lemma boxEnergy_superadd {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) :
    boxEnergy N1 L v + boxEnergy N2 L v ≤ boxEnergy (N1 + N2) L v := by
  have hper : ∀ Ψ : CInfty0Box (N1 + N2) L,
      (boxEnergy N1 L v + boxEnergy N2 L v) *
        (∫ x in box (N1 + N2) L, ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2)
      ≤ ∫ x in box (N1 + N2) L, bigNumInt v Ψ x := by
    intro Ψ
    exact superadd_state (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv hv1 Ψ
  -- each Rayleigh quotient is ≥ the sum of the two energies
  have hquot : ∀ Ψ : CInfty0Box (N1 + N2) L,
      boxEnergy N1 L v + boxEnergy N2 L v ≤
        (∫ x in box (N1 + N2) L,
            (Ψ : Y (N1 + N2) → ℝ) x * (_root_.BoseGases.𝓗 (N1 + N2) v (Ψ : Y (N1 + N2) → ℝ)) x) /
        (Real.sqrt (∫ x in box (N1 + N2) L, (Ψ : Y (N1 + N2) → ℝ) x * (Ψ : Y (N1 + N2) → ℝ) x)) ^ 2 := by
    intro Ψ
    have hstate := hper Ψ
    have hpos : 0 < ∫ x in box (N1 + N2) L, ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 :=
      box_integral_sq_pos hL Ψ
    have hnum : (∫ x in box (N1 + N2) L,
            (Ψ : Y (N1 + N2) → ℝ) x * (_root_.BoseGases.𝓗 (N1 + N2) v (Ψ : Y (N1 + N2) → ℝ)) x)
        = ∫ x in box (N1 + N2) L, bigNumInt v Ψ x := by
      rfl
    have hden : (∫ x in box (N1 + N2) L, (Ψ : Y (N1 + N2) → ℝ) x * (Ψ : Y (N1 + N2) → ℝ) x)
        = ∫ x in box (N1 + N2) L, ((Ψ : Y (N1 + N2) → ℝ) x) ^ 2 := by
      apply setIntegral_congr_fun
      · exact (box_measurable (N1 + N2) L)
      · intro x hx; ring
    -- divide the per-state inequality by the positive denominator
    rw [hden]
    rw [Real.sq_sqrt (le_of_lt hpos)]
    rw [hnum]
    exact (le_div_iff₀ hpos).mpr hstate
  unfold boxEnergy
  haveI : Nonempty (CInfty0Box (N1 + N2) L) := nonempty_CInfty0Box (N1 + N2) hL
  exact le_ciInf hquot

end

end BoseGases

end Submission
