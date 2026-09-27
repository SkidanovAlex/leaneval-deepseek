import Mathlib
import Submission.Work.Drive.ppParity.Good
import Submission.Work.Drive.hVStability

/-!
# The perturbed pair locus stays in a compact: the containment bookkeeping of S3

The assembly of the localized pair Sard needs the standard compactness statement that the *perturbed*
pair locus does not escape the union of the pieces' interiors: if every base pair meet in the nine-box
lies in an open `U`, then for all parameters sufficiently close to `0` every pair meet of the perturbed
family lies in `U`.  This is the pair analogue of `Work.Drive.eventually_meet3_subset_of_isOpen`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]

/-- The perturbed pair meet condition is closed. -/
theorem isClosed_ppMeetSet (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (w : ℝ → ℝ)
    (hPc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)))
    (hPc' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)))
    (hVc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (ftY q.2)))
    (hWc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (ftZ q.2))) :
    IsClosed {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ Submission.Drive.unitBox 8 ∧
      q.2 ∈ ppMeet (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W} := by
  have hbox : IsClosed {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ Submission.Drive.unitBox 8} :=
    (isClosed_unitBox 8).preimage continuous_snd
  have hZeq : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        q.2 ∈ Submission.Drive.unitBox 8 ∧
        q.2 ∈ ppMeet (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W} =
      ({q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
          q.2 ∈ Submission.Drive.unitBox 8} ∩
        {q | ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) = V (ftY q.2)}) ∩
        {q | ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) = W (ftZ q.2)} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ppMeet]
    tauto
  exact hZeq.symm ▸ ((hbox.inter (isClosed_eq hPc hVc)).inter (isClosed_eq hPc' hWc))

/-- **The perturbed pair locus stays inside an open set containing the base one.** -/
theorem eventually_ppMeet_subset_of_isOpen
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} {w : ℝ → ℝ}
    (hPc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)))
    (hPc' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)))
    (hVc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (ftY q.2)))
    (hWc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (ftZ q.2)))
    (hΞ0 : ∀ p : M, Ξ 0 p = p) (hw : Continuous w)
    {U : Set (EuclideanSpace ℝ (Fin 9))} (hU : IsOpen U)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 8, y ∈ ppMeet E E' V W → y ∈ U) :
    ∀ᶠ τ in 𝓝 (0 : EuclideanSpace ℝ (Fin 8)), ∀ y ∈ Submission.Drive.unitBox 8,
      y ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W → y ∈ U := by
  classical
  have hZcl := isClosed_ppMeetSet (M := M) E E' V W Ξ w hPc hPc' hVc hWc
  have hsub : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        q.2 ∈ Submission.Drive.unitBox 8 ∧
        q.2 ∈ ppMeet (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W} ∩
      ({(0 : EuclideanSpace ℝ (Fin 8))} ×ˢ Submission.Drive.unitBox 8) ⊆
      (Set.univ : Set (EuclideanSpace ℝ (Fin 8))) ×ˢ U := by
    rintro ⟨τ, y⟩ ⟨⟨hy, hmeet⟩, hτ, -⟩
    refine ⟨trivial, hbase y hy ?_⟩
    have hτ0 : τ = 0 := Set.mem_singleton_iff.mp hτ
    subst hτ0
    have h1 : ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E (ftS y) (ftU y)
        = E (ftS y) (ftU y) := by
      rw [ppShift, map_zero, smul_zero, hΞ0]
    have h2 : ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E' (ftS y) (ftU y)
        = E' (ftS y) (ftU y) := by
      rw [ppShift, map_zero, smul_zero, hΞ0]
    simp only [ppMeet] at hmeet
    exact ⟨hmeet.1, by rw [← h1]; exact hmeet.2.1, by rw [← h2]; exact hmeet.2.2⟩
  obtain ⟨W', hW'0, hW'open, hW'sub⟩ := exists_prod_nhds_subset_of_isCompact_set hZcl
    (isOpen_univ.prod hU) (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin 8))))
    (isCompact_unitBox 8) hsub
  filter_upwards [hW'open.mem_nhds (hW'0 (Set.mem_singleton 0))] with τ hτ y hy hmeet
  have hZmem : ((τ, y) : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) ∈
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        q.2 ∈ Submission.Drive.unitBox 8 ∧
        q.2 ∈ ppMeet (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W} :=
    ⟨hy, hmeet⟩
  exact (hW'sub ⟨hZmem, ⟨hτ, hy⟩⟩).2

end

end Work.Drive
