import Mathlib
import Submission.Work.Smooth.Morse.Defs

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.MorseModel

noncomputable section

/-- **A sublevel region cannot be the lower piece of a disc attachment at a level below it.**

If `region ψ g b = region ψ g a ∪ D.interior` with the two pieces disjoint, then `region ψ g a`
is a subset of the torus which is both open and closed in the surface: it is the trace of the open
set `{g < a}` (`IsOpenInCarrier`), and its complement is covered by `{g > a}` (open, by continuity)
together with the points `{g = a}`, which lie in `D.interior` (`levelSet ψ g a ⊆ D.interior`
because `a < b`).

Since the torus is connected (`IsPreconnected` as the continuous image of `ℝ × ℝ`), such a clopen
piece is either empty or the whole surface; the second alternative is impossible because the
interior of the disc `D` is nonempty and disjoint from `region ψ g a`. -/
theorem region_eq_empty_of_cover (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a < b) {D : Work.SurgeryInvariance.DiscRegion (torus ψ)}
    (hcover : region ψ g b = region ψ g a ∪ D.interior)
    (hdisj : Disjoint (region ψ g a) D.interior) :
    region ψ g a = ∅ := by
  -- the torus is preconnected, as the continuous image of `ℝ × ℝ`
  have hSpre : IsPreconnected (torus ψ).carrier := by
    rw [Work.Smooth.Morse.torus_carrier]
    simpa only [Set.image_univ] using
      (isPreconnected_univ (α := ℝ × ℝ)).image (fun p : ℝ × ℝ => param ψ p)
        (param_continuous ψ).continuousOn
  have hpreuniv : IsPreconnected (univ : Set ↥((torus ψ).carrier)) :=
    preconnectedSpace_iff_univ.mp (isPreconnected_iff_preconnectedSpace.mp hSpre)
  -- the region below `a`, as a subset of the surface
  set A : Set ↥((torus ψ).carrier) := {x | g (x : R3) < a} with hAdef
  set B : Set ↥((torus ψ).carrier) :=
    {x | a < g (x : R3)} ∪ {x | (x : R3) ∈ D.interior} with hBdef
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact isOpen_lt (hg.comp continuous_subtype_val) continuous_const
  have hBopen : IsOpen B := by
    rw [hBdef]
    refine (isOpen_lt continuous_const (hg.comp continuous_subtype_val)).union ?_
    have := D.open_interior'
    rw [Work.SurgeryInvariance.IsOpenInCarrier] at this
    exact this
  have hdisjAB : Disjoint A B := by
    rw [hAdef, hBdef, Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      rw [Set.mem_ofPred_eq] at hxA
      rcases hxB with hgt | hDint
      · exact absurd hxA (not_lt.mpr hgt.le)
      · rw [Set.mem_ofPred_eq] at hDint
        exact absurd (hdisj.le_bot ⟨⟨x.2, hxA⟩, hDint⟩) (Set.notMem_empty _)
    · intro h
      exact absurd h (Set.notMem_empty _)
  -- the complement is covered by `{g > a} ∪ D.interior`
  have hcoverAB : (univ : Set ↥((torus ψ).carrier)) ⊆ A ∪ B := by
    intro x _
    rw [hAdef, hBdef]
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases lt_or_ge (g (x : R3)) a with hlt | hge
    · exact Or.inl hlt
    · rcases lt_or_eq_of_le hge with hgt | heq
      · exact Or.inr (Or.inl hgt)
      · have hgxa : g (x : R3) = a := heq.symm
        refine Or.inr (Or.inr ?_)
        have hxreg : (x : R3) ∈ region ψ g b := by
          rw [mem_region]
          exact ⟨x.2, by rw [hgxa]; exact hab⟩
        rw [hcover] at hxreg
        rcases hxreg with hreg | hDint
        · rw [mem_region] at hreg
          rw [hgxa] at hreg
          exact absurd hreg.2 (lt_irrefl a)
        · exact hDint
  have hAempty : A = ∅ := by
    rcases IsPreconnected.subset_or_subset hAopen hBopen hdisjAB hcoverAB hpreuniv with h | h
    · exfalso
      let z₀ : Metric.closedBall (0 : ℂ) 1 := ⟨0, by simp [Metric.mem_closedBall]⟩
      have hz₀ : ‖(z₀ : ℂ)‖ < 1 := by simp [z₀]
      have hDint : D.e z₀ ∈ D.interior := ⟨z₀, hz₀, rfl⟩
      have hmemA : (⟨D.e z₀, D.mem z₀⟩ : ↥((torus ψ).carrier)) ∈ A := h (Set.mem_univ _)
      have hmemB : (⟨D.e z₀, D.mem z₀⟩ : ↥((torus ψ).carrier)) ∈ B := by
        rw [hBdef]
        exact Or.inr hDint
      exact absurd (hdisjAB.le_bot ⟨hmemA, hmemB⟩) (Set.notMem_empty _)
    · rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact absurd (hdisjAB.le_bot ⟨hx, h (Set.mem_univ x)⟩) (Set.notMem_empty x)
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_region] at hx
  have hmem : (⟨x, hx.1⟩ : ↥((torus ψ).carrier)) ∈ A := by
    rw [hAdef, Set.mem_ofPred_eq]
    exact hx.2
  rw [hAempty] at hmem
  exact hmem

/-- **`DiscModel ψ g t₀` forces `t₀` to be a lower bound for `g` on the surface.**

If for all small `ε > 0` the region `{g < t₀ + ε}` is the region `{g < t₀ - ε}` together with the
interior of an embedded disc, then no point of the surface lies below `t₀`: otherwise some point
lies in `region ψ g (t₀ - ε)`, which is empty by `region_eq_empty_of_cover`. -/
theorem not_discModel_of_lt (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : Continuous g) {t₀ : ℝ} (h : Work.Smooth.Morse.DiscModel ψ g t₀) {x : LeanEval.KnotTheory.PardonDistortion.R3} (hx : x ∈ (Work.Smooth.Morse.torus ψ).carrier) : t₀ ≤ g x := by
  obtain ⟨ε₀, hε₀, hD⟩ := h
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (ε₀ / 2) ((t₀ - g x) / 2) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (half_pos hε₀) (half_pos (sub_pos.mpr hcon))
  have hεlt : ε < ε₀ := by
    rw [hεdef]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  have hεlt' : ε < t₀ - g x := by
    have hle : ε ≤ (t₀ - g x) / 2 := by
      rw [hεdef]
      exact min_le_right _ _
    linarith
  obtain ⟨D, hcover, hdisj⟩ := hD ε hεpos hεlt
  have hempty : region ψ g (t₀ - ε) = ∅ :=
    region_eq_empty_of_cover (a := t₀ - ε) (b := t₀ + ε) ψ hg (by linarith) hcover hdisj
  have hmem : x ∈ region ψ g (t₀ - ε) := by
    rw [mem_region]
    exact ⟨hx, by linarith⟩
  rw [hempty] at hmem
  exact hmem

end

end Work.Smooth.Morse.MorseModel
