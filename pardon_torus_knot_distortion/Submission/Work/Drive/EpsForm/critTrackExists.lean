import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.EpsForm.critBranchLocal
import Submission.Work.Drive.EpsForm.critNearBase
import Submission.Work.Drive.EpsForm.critTracks_separated

namespace Work.Drive.EpsForm

theorem critTrackExists (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (hn₀ : ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q))) p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ m : ℕ, ∃ q : Fin m → ℝ × ℝ, ∃ x : Fin m → LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ,
      (∀ i, q i ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) ∧
      (∀ i, x i n₀ = q i) ∧
      (∀ i n, n ∈ Metric.ball n₀ ρ → DifferentiableAt ℝ (x i) n) ∧
      (∀ i n, n ∈ Metric.ball n₀ ρ →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) (x i n) = 0) ∧
      (∀ n ∈ Metric.ball n₀ ρ, ∀ p ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi),
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        ∃ i, Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ (x i n)) ∧
      (∀ i j, i ≠ j →
        (∀ k l : ℤ, q i - q j ≠ (2 * Real.pi * k, 2 * Real.pi * l)) →
        ∀ n ∈ Metric.ball n₀ ρ,
          Work.BoxShrink.Pinch.par ψ (x i n) ≠ Work.BoxShrink.Pinch.par ψ (x j n)) := by
  classical
  -- ## 1. The critical set of the base height inside the fundamental square
  have hnd : ∀ p : ℝ × ℝ, fderiv ℝ (heightOf ψ n₀) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (heightOf ψ n₀)) p) :=
    fun p hp => hn₀ p hp
  have hfin : ({p : ℝ × ℝ | fderiv ℝ (heightOf ψ n₀) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    finite_critSet_box (heightOf_contDiff_two ψ n₀) hnd
  set X : Finset (ℝ × ℝ) := hfin.toFinset with hXdef
  have memX : ∀ p : ℝ × ℝ, p ∈ X ↔
      fderiv ℝ (heightOf ψ n₀) p = 0 ∧
        p ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) := by
    intro p
    rw [hXdef, Set.Finite.mem_toFinset]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  -- ## 2. Local branches of the critical points near the base direction
  obtain ⟨y, εb, δb, hεb, hδb, hy0, hydiff, hycrit, hyuniq⟩ :=
    critBranchLocal ψ n₀ X (fun x hx => by
      obtain ⟨h1, _⟩ := (memX x).mp hx
      exact ⟨h1, hnd x h1⟩)
  -- ## 3. Nearby directions have all their critical points near the base critical set
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := critNearBase ψ n₀ εb hεb
  -- ## 4. Distinct branches stay distinct
  have hcont : ∀ x ∈ X, ContinuousAt (y x) n₀ :=
    fun x hx => (hydiff x hx n₀ (by simpa using hδb)).continuousAt
  obtain ⟨ρd, hρdpos, hρd⟩ := critTracks_separated ψ n₀ X y hcont hy0
  -- ## 5. The radius
  set ρ : ℝ := min δb (min δ₂ ρd) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hδb (lt_min hδ₂pos hρdpos)
  have hρb : ρ ≤ δb := by rw [hρdef]; exact min_le_left _ _
  have hρ₂ : ρ ≤ δ₂ := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρdρ : ρ ≤ ρd := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρpos, X.card, (fun i => (X.equivFin.symm i : ℝ × ℝ)),
    (fun i => y (X.equivFin.symm i : ℝ × ℝ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((memX _).mp (X.equivFin.symm i).2).2
  · intro i
    exact hy0 _ (X.equivFin.symm i).2
  · intro i n hn
    have hnρ : ‖n - n₀‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hn
    exact hydiff _ (X.equivFin.symm i).2 n (lt_of_lt_of_le hnρ hρb)
  · intro i n hn
    have hnρ : ‖n - n₀‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hn
    exact hycrit _ (X.equivFin.symm i).2 n (lt_of_lt_of_le hnρ hρb)
  · -- covering: every critical point in the square comes from a branch
    intro n hn p hp hcrit
    have hnρ : ‖n - n₀‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hn
    have hn₂ : ‖n - n₀‖ < δ₂ := lt_of_lt_of_le hnρ hρ₂
    have hnb : ‖n - n₀‖ < δb := lt_of_lt_of_le hnρ hρb
    obtain ⟨x', hx'crit, hpx'⟩ := hδ₂ n hn₂ p hp hcrit
    obtain ⟨x'', hx''box, hx''crit, -, -, hpar⟩ := exists_fundBox_of_crit ψ n₀ hx'crit
    have hx''X : x'' ∈ X := (memX x'').mpr ⟨hx''crit, hx''box⟩
    obtain ⟨k, m, hk, hm⟩ := (par_eq_iff ψ x' x'').mp hpar.symm
    have hcrit₂ : fderiv ℝ (heightOf ψ n)
        (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = 0 := by
      rw [fderiv_heightOf_periodic ψ n k m p]
      exact hcrit
    have hvec : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) - x'' = p - x' := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> linarith [hk, hm]
    have hlt : ‖(p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) - x''‖ < εb := by
      rw [hvec]; exact hpx'
    have huniq : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = y x'' n :=
      hyuniq x'' hx''X n hnb _ hlt hcrit₂
    refine ⟨X.equivFin ⟨x'', hx''X⟩, ?_⟩
    have hqi : (X.equivFin.symm (X.equivFin ⟨x'', hx''X⟩) : ℝ × ℝ) = x'' := by
      have h1 := Equiv.symm_apply_apply X.equivFin ⟨x'', hx''X⟩
      exact congrArg (fun z : ↥X => (z : ℝ × ℝ)) h1
    have hpar1 : Work.BoxShrink.Pinch.par ψ p
        = Work.BoxShrink.Pinch.par ψ
            (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) := by
      have hass := par_add_shift ψ k m
        (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      have hkey : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
          + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)) = p := by
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
      rwa [hkey] at hass
    have hmain : Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ (y x'' n) := by
      rw [← huniq]
      exact hpar1
    rw [← hqi] at hmain
    exact hmain
  · intro i j hij hnc n hn
    have hnρ : ‖n - n₀‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hn
    exact hρd n (lt_of_lt_of_le hnρ hρdρ) _ (X.equivFin.symm i).2 _ (X.equivFin.symm j).2 hnc

end Work.Drive.EpsForm
