/-
  WilE9 / Sharp / AE — density of the complement of the `ψV`-preimage of a null set.

  The AE covering produced by `Work.WilE9G.EffStratAE` misses a null set `N ⊆ ℝⁿ`; the E9 layer
  has to approach a point of interest through base points `x'` with `ψV x' ∉ N`.  This file
  supplies the density that makes that possible: `(ψV ⁻¹' N)ᶜ` is dense whenever `volume N = 0`.

  The proof is elementary.  `ψV` is the coordinatewise `ψ = x/√(1+x²)`, which is strictly
  increasing (`psi_strictMono`) with inverse `psiInv` on `(-1,1)` (`psi_psiInv`).  Hence `ψV` maps
  the open box `(x i - ε, x i + ε)ᵢ` *onto* the open box `(ψ (x i - ε), ψ (x i + ε))ᵢ`
  (`box_subset_psiV_image` is the inclusion needed here).  So if `ψV ⁻¹' N` had nonempty
  interior, `N` would contain a nonempty open box; but a null set has empty interior
  (`MeasureTheory.Measure.interior_eq_empty_of_null`).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.hasDerivAt_psi
import Submission.Work.WilE9.Psi.psig_pos

namespace Work.WilE9.Sharp.AE

open MeasureTheory Set Topology

/-- `ψ = x/√(1+x²)` is strictly increasing; its derivative is `psig x ^ 3 > 0`. -/
theorem psi_strictMono : StrictMono (WilkiesDesign.E.psi : ℝ → ℝ) :=
  strictMono_of_hasDerivAt_pos (fun x => Work.WilE9.Psi.hasDerivAt_psi x)
    (fun x => pow_pos (Work.WilE9.Psi.psig_pos x) 3)

/-- The open box spanned by the images of the endpoints of an open ball lies in the `ψV`-image of
that ball.  (`ψV` maps the box *onto* the box of images; only this inclusion is needed below.) -/
theorem box_subset_psiV_image {n : ℕ} (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Set.pi univ (fun i => Ioo (WilkiesDesign.E.psi (x i - ε))
      (WilkiesDesign.E.psi (x i + ε)))
      ⊆ WilkiesDesign.E.psiV '' (Metric.ball x ε) := by
  intro z hz
  -- `z i` lies strictly between the two images, and `|ψ| ≤ 1`, so `|z i| < 1`
  have habs : ∀ i, |z i| < 1 := by
    intro i
    have hi : z i ∈ Ioo (WilkiesDesign.E.psi (x i - ε)) (WilkiesDesign.E.psi (x i + ε)) :=
      hz i (mem_univ i)
    rw [mem_Ioo] at hi
    have h1 : -1 < z i :=
      lt_of_le_of_lt (abs_le.mp (WilkiesDesign.E.psi_abs_le_one (x i - ε))).1 hi.1
    have h2 : z i < 1 :=
      lt_of_lt_of_le hi.2 (abs_le.mp (WilkiesDesign.E.psi_abs_le_one (x i + ε))).2
    exact abs_lt.mpr ⟨h1, h2⟩
  refine ⟨fun i => Work.WilE9.psiInv (z i), ?_, ?_⟩
  · rw [ball_pi x hε, Set.mem_pi]
    intro i _
    rw [Real.ball_eq_Ioo, mem_Ioo]
    have hi : z i ∈ Ioo (WilkiesDesign.E.psi (x i - ε)) (WilkiesDesign.E.psi (x i + ε)) :=
      hz i (mem_univ i)
    rw [mem_Ioo] at hi
    constructor
    · rw [← psi_strictMono.lt_iff_lt, Work.WilE9.Psi.psi_psiInv (z i) (habs i)]
      exact hi.1
    · rw [← psi_strictMono.lt_iff_lt, Work.WilE9.Psi.psi_psiInv (z i) (habs i)]
      exact hi.2
  · funext i
    exact Work.WilE9.Psi.psi_psiInv (z i) (habs i)

theorem dense_compl_psiV_preimage {n : ℕ} {N : Set (Fin n → ℝ)}
    (hN : MeasureTheory.volume N = 0) :
    Dense ((WilkiesDesign.E.psiV ⁻¹' N)ᶜ) := by
  -- a null set has empty interior
  have hNint : interior N = ∅ := MeasureTheory.Measure.interior_eq_empty_of_null hN
  -- so does the preimage
  have hpre : interior (WilkiesDesign.E.psiV ⁻¹' N) = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    -- the ball around `x` sits inside the preimage
    have hxsub : Metric.ball x ε ⊆ WilkiesDesign.E.psiV ⁻¹' N :=
      fun y hy => interior_subset (hball hy)
    have himg : WilkiesDesign.E.psiV '' Metric.ball x ε ⊆ N := by
      rintro z ⟨y, hy, rfl⟩
      exact hxsub hy
    -- the image box is open, nonempty, and inside `N`
    have hCopen : IsOpen (Set.pi univ fun i =>
        Ioo (WilkiesDesign.E.psi (x i - ε)) (WilkiesDesign.E.psi (x i + ε))) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
    have hCsub : Set.pi univ (fun i => Ioo (WilkiesDesign.E.psi (x i - ε))
        (WilkiesDesign.E.psi (x i + ε))) ⊆ N :=
      (box_subset_psiV_image x hε).trans himg
    have hle : Set.pi univ (fun i => Ioo (WilkiesDesign.E.psi (x i - ε))
        (WilkiesDesign.E.psi (x i + ε))) ⊆ interior N :=
      interior_maximal hCsub hCopen
    have hmem : WilkiesDesign.E.psiV x ∈ Set.pi univ (fun i =>
        Ioo (WilkiesDesign.E.psi (x i - ε)) (WilkiesDesign.E.psi (x i + ε))) := by
      intro i _
      exact ⟨psi_strictMono (by linarith), psi_strictMono (by linarith)⟩
    have : WilkiesDesign.E.psiV x ∈ interior N := hle hmem
    rw [hNint] at this
    exact this
  rw [dense_iff_closure_eq, closure_compl, hpre]
  simp

end Work.WilE9.Sharp.AE
