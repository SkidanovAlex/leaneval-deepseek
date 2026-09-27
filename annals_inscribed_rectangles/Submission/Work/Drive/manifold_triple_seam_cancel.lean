import Mathlib
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.TripleMeetDefs
import Submission.Work.Drive.manifold_triple_inter_boundary_parity
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.even_ncard_of_involution

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-! ## Elementary facts about the seam involution

`Work.Drive.seamInv` replaces the first two coordinates of a parameter by their complements and
leaves the sweep coordinate alone; it is an involution, it preserves the seam `onSeam` (and reflects
it), it preserves the unit box, and it has no fixed point on the seam. -/

private lemma seamInv_seamInv (x : EuclideanSpace ℝ (Fin 3)) : seamInv (seamInv x) = x := by
  ext i
  fin_cases i <;> simp [seamInv_apply_zero, seamInv_apply_one, seamInv_apply_two]

private lemma onSeam_seamInv (x : EuclideanSpace ℝ (Fin 3)) : onSeam (seamInv x) ↔ onSeam x := by
  have h0 : (1 - x 0 = 0) ↔ (x 0 = 1) := by constructor <;> intro h <;> linarith
  have h0' : (1 - x 0 = 1) ↔ (x 0 = 0) := by constructor <;> intro h <;> linarith
  have h1 : (1 - x 1 = 0) ↔ (x 1 = 1) := by constructor <;> intro h <;> linarith
  have h1' : (1 - x 1 = 1) ↔ (x 1 = 0) := by constructor <;> intro h <;> linarith
  simp only [onSeam, seamInv_apply_zero, seamInv_apply_one]
  rw [h0, h0', h1, h1']
  tauto

/-- `seamInv` has no fixed point on the seam: on the seam the first two coordinates are `0` or `1`, so
complementing them moves the point.  This is the fixed-point-freeness of the antipodal map, and it is
what makes the seam cancellation strict. -/
private lemma seamInv_ne_self_of_onSeam (x : EuclideanSpace ℝ (Fin 3)) (h : onSeam x) :
    seamInv x ≠ x := by
  intro heq
  rcases h with h | h | h | h
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 0) heq
    simp [seamInv_apply_zero] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 0) heq
    simp [seamInv_apply_zero] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 1) heq
    simp [seamInv_apply_one] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 1) heq
    simp [seamInv_apply_one] at hc; linarith

private lemma seamTriple_seamTriple (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    seamTriple k (seamTriple k x) = x := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [seamTriple, seamInv_seamInv]
  · simp [seamTriple, Function.update_of_ne hj]

private lemma seamTriple_ne_self_of_onSeam (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h : onSeam (x k)) : seamTriple k x ≠ x := by
  intro heq
  have hc : seamTriple k x k = x k := by rw [heq]
  rw [seamTriple_apply_self] at hc
  exact seamInv_ne_self_of_onSeam (x k) h hc

private lemma seamInv_mem_unitBox_iff (y : EuclideanSpace ℝ (Fin 3)) :
    seamInv y ∈ Submission.Drive.unitBox 2 ↔ y ∈ Submission.Drive.unitBox 2 := by
  simp only [Submission.Drive.unitBox, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> intro h i <;> have hi := h i <;>
    fin_cases i <;> simp [seamInv_apply_zero, seamInv_apply_one, seamInv_apply_two] at hi ⊢ <;>
    constructor <;> linarith

private lemma seamInv_mem_unitBoxBdry (y : EuclideanSpace ℝ (Fin 3))
    (hy : y ∈ Submission.Drive.unitBox 2) (h : onSeam y) :
    seamInv y ∈ Submission.Drive.unitBoxBdry 2 := by
  refine ⟨(seamInv_mem_unitBox_iff y).mpr hy, ?_⟩
  rcases h with h | h | h | h
  · exact ⟨0, by simp [seamInv_apply_zero, h]⟩
  · exact ⟨0, by simp [seamInv_apply_zero, h]⟩
  · exact ⟨1, by simp [seamInv_apply_one, h]⟩
  · exact ⟨1, by simp [seamInv_apply_one, h]⟩

/-! ## The involution on the seam boundary triple intersections

The seam involution acts on the `k`-th parameter block only.  Because the chain `D k` is invariant on
the seam (`hseam`), replacing the `k`-th block by its antipode does not change the point of `M` it
realises, so the three chains still meet; and since the `k`-th block was on the seam, the new block is
again on the seam (with the same `k`-th parameter on a seam face of the box). -/

private lemma seamTriple_mem_seamBdryMeet {M : Type*} [TopologicalSpace M]
    {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M}
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x))
    (k : Fin 3) {x : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ seamBdryMeet M D k) : seamTriple k x ∈ seamBdryMeet M D k := by
  obtain ⟨hb, hsk⟩ := hx
  obtain ⟨hbox, hm01, hm02, _hbd⟩ := hb
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  -- the `k`-th block stays in the unit box, the other two blocks are untouched
  have hunit : ∀ k' : Fin 3, seamTriple k x k' ∈ Submission.Drive.unitBox 2 := by
    intro k'
    by_cases hkk : k' = k
    · rw [hkk, seamTriple_apply_self]
      exact (seamInv_mem_unitBox_iff (x k)).mpr (hbox k)
    · rw [seamTriple_apply_of_ne hkk x]
      exact hbox k'
  -- the seam invariance of the chain turns the `k`-th block into its antipode
  have hD0 : D 0 (seamTriple k x 0) = D 0 (x 0) := by
    rcases hk3 with hk3 | hk3 | hk3 <;> subst hk3
    · rw [seamTriple_apply_self]; exact (hseam 0 (x 0) hsk).symm
    · simp [seamTriple]
    · simp [seamTriple]
  have hD1 : D 1 (seamTriple k x 1) = D 1 (x 1) := by
    rcases hk3 with hk3 | hk3 | hk3 <;> subst hk3
    · simp [seamTriple]
    · rw [seamTriple_apply_self]; exact (hseam 1 (x 1) hsk).symm
    · simp [seamTriple]
  have hD2 : D 2 (seamTriple k x 2) = D 2 (x 2) := by
    rcases hk3 with hk3 | hk3 | hk3 <;> subst hk3
    · simp [seamTriple]
    · simp [seamTriple]
    · rw [seamTriple_apply_self]; exact (hseam 2 (x 2) hsk).symm
  refine ⟨⟨hunit, ?_, ?_, ?_⟩, ?_⟩
  · exact hD0.trans (hm01.trans hD1.symm)
  · exact hD0.trans (hm02.trans hD2.symm)
  · rw [seamTriple_apply_self]
    exact seamInv_mem_unitBoxBdry (x k) (hbox k) hsk
  · rw [seamTriple_apply_self]
    exact (onSeam_seamInv (x k)).mpr hsk

/-- **The seam faces of a parametrised plane cancel.**  For a triple of transverse `3`-chains
`D 0, D 1, D 2` in a smooth `4`-manifold whose first two parameters are the parameters of the plane's
own `2`-chain presentation and whose third parameter is the sweep parameter
(`Work.Drive.seamInv` is the antipodal involution `(y 0, y 1, s) ↦ (1 - y 0, 1 - y 1, s)` of the
parameter square, `Work.Drive.onSeam` says that `(y 0, y 1)` lies on the boundary of the square, and
`Work.Drive.seamBdryMeet M D k` is the set of boundary triple intersections of
`Work.Drive.manifold_triple_inter_boundary_parity` whose `k`-th parameter lies on one of the four
*seam* faces `x 0 ∈ {0,1}`, `x 1 ∈ {0,1}`), if each chain is **invariant under the antipodal
involution on the seam** (`hseam`: `D k x = D k (seamInv x)` whenever `onSeam x`), then the seam
boundary triple intersections are finite and their number is even.

This is the second of the two inputs that convert the coarse triple-intersection parity into the
identity `n_P + n_Q + n_R ≡ 1` used by Hugelmeyer's Lemma 4 (`ENDS_AND_SEAMS_NOTES.md`): the coarse
result gives `Σ_k (top_k + bottom_k + seam_k)` even, the bottom faces are dealt with by choosing them
to be three linear projective planes (`Work.Drive.projective_planes_meet_oddly`), and the present one
gives `Σ_k seam_k ≡ 0`.  Its proof is the fixed-point-free involution `x ↦ seamTriple k x` of
`seamBdryMeet M D k` — which preserves the triple intersection because the chain is seam-invariant, and
has no fixed point because `onSeam` forbids `x k 0 = x k 1 = 1/2` — together with the finiteness coming
from `Work.Drive.manifold_triple_inter_boundary_parity`. -/
theorem manifold_triple_seam_cancel (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      Work.Drive.TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)))
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          Work.Drive.TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0)
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      D k x = D k (Work.Drive.seamInv x)) :
    (∀ k : Fin 3, (Work.Drive.seamBdryMeet M D k).Finite) ∧
      (∀ k : Fin 3, Even (Work.Drive.seamBdryMeet M D k).ncard) := by
  classical
  -- the coarse boundary parity: the three blocks of boundary triple intersections are finite
  obtain ⟨hfin, _⟩ := manifold_triple_inter_boundary_parity M D hD htrans hface
  have hsub : ∀ k : Fin 3, Work.Drive.seamBdryMeet M D k ⊆ Work.Drive.tripleBdryMeet M D k :=
    fun k x hx => hx.1
  refine ⟨fun k => (hfin k).subset (hsub k), fun k => ?_⟩
  -- the fixed-point-free involution `x ↦ seamTriple k x` pairs the seam intersections up
  exact even_ncard_of_involution ((hfin k).subset (hsub k)) (seamTriple k)
    (fun x hx => seamTriple_mem_seamBdryMeet hseam k hx)
    (fun x _ => seamTriple_seamTriple k x)
    (fun x hx => seamTriple_ne_self_of_onSeam k x hx.2)

end Work.Drive
