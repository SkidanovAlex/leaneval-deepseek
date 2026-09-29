import Mathlib
import Submission.Work.A14D.setup
import Submission.Work.A14D.slitPieces
import Submission.Work.A14D.PZ_ne_zero_of_mem_slitDisk
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.glue_three_LZ

/-!
# A14D: continuation of solutions of `LZ = 0` from a convex piece of the slit disc

`Work.A14D.slitDisk_continuation`: a solution `f` of `LZ f = 0` on an open convex
`V ⊆ slitDisk δ` (`δ ≤ 8/9`) extends to a solution on the whole slit disc.

The slit disc is the union of the three convex pieces `halfUp δ`, `halfDn δ`, `halfRt δ`
(`Submission.Work.A14D.slitPieces`), on which `PZ` does not vanish
(`Submission.Work.A14D.PZ_ne_zero_of_mem_slitDisk`).  On each convex piece a solution with
prescribed value and derivative at a point exists (`exists_sol_LZ_convex`), any two solutions
agreeing in value and derivative at a point coincide on a preconnected piece
(`eqOn_of_sol_LZ`), which lets us *extend* a solution from one piece to an overlapping piece
(`extend_sol_LZ` below).  Chaining the three pieces and gluing (`glue_three_LZ`) produces, for any
initial data at any point of the slit disc, a global solution (`exists_global_sol`); matching the
data of `f` at a point of `V` and using uniqueness on the convex `V` finishes the proof.
-/

namespace Work.A14D

open Complex Metric
open scoped Topology

noncomputable section

/-- A solution of `LZ = 0` on a set. -/
def IsSolLZ (g : ℂ → ℂ) (S : Set ℂ) : Prop :=
  DifferentiableOn ℂ g S ∧ ∀ z ∈ S, LZ g z = 0

lemma eqOn_inter_comm {f g : ℂ → ℂ} {s t : Set ℂ} (h : Set.EqOn f g (s ∩ t)) :
    Set.EqOn f g (t ∩ s) := fun z hz => h ⟨hz.2, hz.1⟩

lemma nonempty_inter_comm {s t : Set ℂ} (h : (s ∩ t).Nonempty) : (t ∩ s).Nonempty :=
  h.mono (fun z hz => ⟨hz.2, hz.1⟩)

/-- Extend a solution from one convex piece to another convex piece meeting it. -/
lemma extend_sol_LZ {S₁ S₂ : Set ℂ} (h₁o : IsOpen S₁) (h₁c : Convex ℝ S₁) (h₂o : IsOpen S₂)
    (h₂c : Convex ℝ S₂) (hP : ∀ z ∈ S₁ ∪ S₂, PZ z ≠ 0) {g₁ : ℂ → ℂ}
    (hg₁ : IsSolLZ g₁ S₁) (hne : (S₁ ∩ S₂).Nonempty) :
    ∃ g₂ : ℂ → ℂ, IsSolLZ g₂ S₂ ∧ Set.EqOn g₂ g₁ (S₁ ∩ S₂) := by
  obtain ⟨p, hp₁, hp₂⟩ := hne
  obtain ⟨g₂, hg₂d, hg₂p, hg₂p', -, hg₂L⟩ :=
    exists_sol_LZ_convex h₂o h₂c (fun z hz => hP z (Or.inr hz)) hp₂ (g₁ p) (deriv g₁ p)
  refine ⟨g₂, ⟨hg₂d, hg₂L⟩, ?_⟩
  refine eqOn_of_sol_LZ (h₁o.inter h₂o) (h₁c.inter h₂c).isPreconnected
    (fun z hz => hP z (Or.inl hz.1)) ?_ ?_ ?_ ?_ ⟨hp₁, hp₂⟩ hg₂p ?_
  · exact hg₂d.mono Set.inter_subset_right
  · exact hg₁.1.mono Set.inter_subset_left
  · exact fun z hz => hg₂L z hz.2
  · exact fun z hz => hg₁.2 z hz.1
  · exact hg₂p'

/-- Any initial data at any point of the slit disc is realised by a global solution. -/
lemma exists_global_sol {δ : ℝ} (hδ : 0 < δ) (hPZS : ∀ z ∈ slitDisk δ, PZ z ≠ 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ slitDisk δ) (a b : ℂ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (slitDisk δ) ∧ (∀ z ∈ slitDisk δ, LZ F z = 0) ∧
      F z₁ = a ∧ deriv F z₁ = b := by
  classical
  have hPu : ∀ z ∈ halfUp δ, PZ z ≠ 0 := fun z hz => hPZS z (halfUp_subset_slitDisk δ hz)
  have hPd : ∀ z ∈ halfDn δ, PZ z ≠ 0 := fun z hz => hPZS z (halfDn_subset_slitDisk δ hz)
  have hPr : ∀ z ∈ halfRt δ, PZ z ≠ 0 := fun z hz => hPZS z (halfRt_subset_slitDisk δ hz)
  have hPru : ∀ z ∈ halfRt δ ∪ halfUp δ, PZ z ≠ 0 := fun z hz =>
    hz.elim (fun h => hPr z h) (fun h => hPu z h)
  have hPrd : ∀ z ∈ halfRt δ ∪ halfDn δ, PZ z ≠ 0 := fun z hz =>
    hz.elim (fun h => hPr z h) (fun h => hPd z h)
  have hPur : ∀ z ∈ halfUp δ ∪ halfRt δ, PZ z ≠ 0 := fun z hz =>
    hz.elim (fun h => hPu z h) (fun h => hPr z h)
  have hPdr : ∀ z ∈ halfDn δ ∪ halfRt δ, PZ z ≠ 0 := fun z hz =>
    hz.elim (fun h => hPd z h) (fun h => hPr z h)
  rcases slitDisk_subset_union δ hz₁ with hU | hR
  · rcases hU with hU | hD
    · -- ## the seed lies in the upper half-disc
      obtain ⟨gA, hAd, hAv, hAv', -, hAL⟩ :=
        exists_sol_LZ_convex (isOpen_halfUp δ) (convex_halfUp δ) hPu hU a b
      obtain ⟨gC, hCsol, hCA⟩ := extend_sol_LZ (isOpen_halfUp δ) (convex_halfUp δ)
        (isOpen_halfRt δ) (convex_halfRt δ) hPur ⟨hAd, hAL⟩ (halfUp_inter_halfRt_nonempty hδ)
      obtain ⟨gB, hBsol, hBC⟩ := extend_sol_LZ (isOpen_halfRt δ) (convex_halfRt δ)
        (isOpen_halfDn δ) (convex_halfDn δ) hPrd hCsol
        (nonempty_inter_comm (halfDn_inter_halfRt_nonempty hδ))
      obtain ⟨F, hFd, hFL, hFA, -, -⟩ := glue_three_LZ hAd hBsol.1 hCsol.1 hAL hBsol.2
        hCsol.2 hCA.symm (eqOn_inter_comm hBC)
      have hzA : z₁ ∈ halfUp δ := hU
      refine ⟨F, hFd, hFL, hFA hzA ▸ hAv, ?_⟩
      have hev : F =ᶠ[𝓝 z₁] gA :=
        hFA.eventuallyEq_of_mem ((isOpen_halfUp δ).mem_nhds hzA)
      rw [Filter.EventuallyEq.deriv_eq hev, hAv']
    · -- ## the seed lies in the lower half-disc
      obtain ⟨gB, hBd, hBv, hBv', -, hBL⟩ :=
        exists_sol_LZ_convex (isOpen_halfDn δ) (convex_halfDn δ) hPd hD a b
      obtain ⟨gC, hCsol, hCB⟩ := extend_sol_LZ (isOpen_halfDn δ) (convex_halfDn δ)
        (isOpen_halfRt δ) (convex_halfRt δ) hPdr ⟨hBd, hBL⟩ (halfDn_inter_halfRt_nonempty hδ)
      obtain ⟨gA, hAsol, hAC⟩ := extend_sol_LZ (isOpen_halfRt δ) (convex_halfRt δ)
        (isOpen_halfUp δ) (convex_halfUp δ) hPru hCsol
        (nonempty_inter_comm (halfUp_inter_halfRt_nonempty hδ))
      obtain ⟨F, hFd, hFL, -, hFB, -⟩ := glue_three_LZ hAsol.1 hBd hCsol.1 hAsol.2 hBL
        hCsol.2 (eqOn_inter_comm hAC) hCB.symm
      have hzB : z₁ ∈ halfDn δ := hD
      refine ⟨F, hFd, hFL, hFB hzB ▸ hBv, ?_⟩
      have hev : F =ᶠ[𝓝 z₁] gB :=
        hFB.eventuallyEq_of_mem ((isOpen_halfDn δ).mem_nhds hzB)
      rw [Filter.EventuallyEq.deriv_eq hev, hBv']
  · -- ## the seed lies in the right half-disc
    obtain ⟨gC, hCd, hCv, hCv', -, hCL⟩ :=
      exists_sol_LZ_convex (isOpen_halfRt δ) (convex_halfRt δ) hPr hR a b
    obtain ⟨gA, hAsol, hAC⟩ := extend_sol_LZ (isOpen_halfRt δ) (convex_halfRt δ)
      (isOpen_halfUp δ) (convex_halfUp δ) hPru ⟨hCd, hCL⟩
      (nonempty_inter_comm (halfUp_inter_halfRt_nonempty hδ))
    obtain ⟨gB, hBsol, hBC⟩ := extend_sol_LZ (isOpen_halfRt δ) (convex_halfRt δ)
      (isOpen_halfDn δ) (convex_halfDn δ) hPrd ⟨hCd, hCL⟩
      (nonempty_inter_comm (halfDn_inter_halfRt_nonempty hδ))
    obtain ⟨F, hFd, hFL, -, -, hFC⟩ := glue_three_LZ hAsol.1 hBsol.1 hCd hAsol.2 hBsol.2
      hCL (eqOn_inter_comm hAC) (eqOn_inter_comm hBC)
    refine ⟨F, hFd, hFL, hFC hR ▸ hCv, ?_⟩
    have hev : F =ᶠ[𝓝 z₁] gC := hFC.eventuallyEq_of_mem ((isOpen_halfRt δ).mem_nhds hR)
    rw [Filter.EventuallyEq.deriv_eq hev, hCv']

theorem slitDisk_continuation {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 8 / 9) {V : Set ℂ} (hV : IsOpen V)
    (hVc : Convex ℝ V) (hVsub : V ⊆ slitDisk δ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (hL : ∀ z ∈ V, LZ f z = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (slitDisk δ) ∧ (∀ z ∈ slitDisk δ, LZ F z = 0) ∧
      Set.EqOn F f V := by
  classical
  have hPZS : ∀ z ∈ slitDisk δ, PZ z ≠ 0 := fun z hz => PZ_ne_zero_of_mem_slitDisk hδ8 hz
  by_cases hVne : V = ∅
  · obtain ⟨z₁, hz₁⟩ := halfUp_nonempty hδ
    obtain ⟨F, hFd, hFL, -, -⟩ :=
      exists_global_sol hδ hPZS (halfUp_subset_slitDisk δ hz₁) 0 0
    exact ⟨F, hFd, hFL, fun z hz => absurd hz (by simp [hVne])⟩
  · obtain ⟨z₁, hz₁V⟩ := Set.nonempty_iff_ne_empty.mpr hVne
    obtain ⟨F, hFd, hFL, hFv, hFd'⟩ :=
      exists_global_sol hδ hPZS (hVsub hz₁V) (f z₁) (deriv f z₁)
    refine ⟨F, hFd, hFL, ?_⟩
    exact eqOn_of_sol_LZ hV hVc.isPreconnected (fun z hz => hPZS z (hVsub hz))
      (hFd.mono hVsub) hf (fun z hz => hFL z (hVsub hz)) hL hz₁V hFv hFd'

end

end Work.A14D
