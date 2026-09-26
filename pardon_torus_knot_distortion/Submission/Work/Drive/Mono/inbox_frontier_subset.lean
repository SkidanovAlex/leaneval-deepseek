import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- For `U` open and `y ∈ U`, a frontier point of `U \ B` is a frontier point of `B`. -/
theorem frontier_sdiff_of_mem_open {α : Type*} [TopologicalSpace α] {U B : Set α} {y : α}
    (hU : IsOpen U) (hyU : y ∈ U) (hy : y ∈ frontier (U \ B)) : y ∈ frontier B := by
  rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff] at hy ⊢
  obtain ⟨hcl, hint⟩ := hy
  have hnotUc : y ∉ closure Uᶜ := by
    intro h
    have hne : (U ∩ Uᶜ).Nonempty := mem_closure_iff.mp h U hU hyU
    obtain ⟨z, hz⟩ := hne
    exact hz.2 hz.1
  have h2 : y ∈ closure (Uᶜ ∪ B) := by
    have heq : (U \ B)ᶜ = Uᶜ ∪ B := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
      tauto
    rwa [heq] at hint
  have h3 : y ∈ closure Uᶜ ∪ closure B := by rwa [closure_union] at h2
  exact ⟨h3.resolve_left hnotUc, closure_mono (fun z hz => hz.2) hcl⟩

/-- A C¹ function which crosses the level `a + h` or `a - h` transversally at `t` takes values
strictly inside `(a - h, a + h)` arbitrarily close to `t`. -/
theorem exists_near_abs_sub_lt_of_deriv_ne_zero {ψ : ℝ → ℝ} {t a h : ℝ} (hh : 0 < h)
    (hcont : Continuous ψ) (hdcont : Continuous (deriv ψ)) (hderiv : deriv ψ t ≠ 0)
    (hface : |ψ t - a| = h) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ |ψ r - a| < h := by
  have hcross := Work.Drive.EpsFormSphere.exists_near_lt_self_and_gt hcont hdcont hderiv
  have hnhds : {r : ℝ | |ψ r - ψ t| < 2 * h} ∈ nhds t := by
    have hopen : IsOpen {r : ℝ | |ψ r - ψ t| < 2 * h} :=
      isOpen_lt ((hcont.sub continuous_const).abs) continuous_const
    refine hopen.mem_nhds ?_
    show |ψ t - ψ t| < 2 * h
    rw [sub_self, abs_zero]; linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hnhds
  intro ε hε
  rcases (abs_eq (le_of_lt hh)).mp hface with hup | hdn
  · obtain ⟨r, hr, hlt⟩ := hcross.1 (min ε δ) (lt_min hε hδpos)
    have h2 : Metric.ball t δ r :=
      Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right _ _))
    have h3 := hδ h2
    simp only [Set.mem_ofPred_eq] at h3
    rw [abs_lt] at h3
    refine ⟨r, lt_of_lt_of_le hr (min_le_left _ _), ?_⟩
    rw [abs_lt]
    exact ⟨by linarith [h3.1, hup], by linarith [h3.2, hlt, hup]⟩
  · obtain ⟨r, hr, hgt⟩ := hcross.2 (min ε δ) (lt_min hε hδpos)
    have h2 : Metric.ball t δ r :=
      Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right _ _))
    have h3 := hδ h2
    simp only [Set.mem_ofPred_eq] at h3
    rw [abs_lt] at h3
    refine ⟨r, lt_of_lt_of_le hr (min_le_left _ _), ?_⟩
    rw [abs_lt]
    exact ⟨by linarith [h3.1, hdn, hgt], by linarith [h3.2, hdn]⟩


theorem inbox_frontier_subset {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ} (hh : 0 < h) :
    {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)} ⊆
      frontier {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) < lam} ∪
        {t : ℝ | deriv (fun s : ℝ => ℓ (K.curve s)) t = 0} ∪
        {t : ℝ | |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h ∧
          deriv (fun s : ℝ => inner ℝ v (K.curve s)) t = 0} ∪
        {t : ℝ | |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h ∧ ℓ (K.curve t) = lam} := by
  rintro t ⟨htIco, htbox, htfr⟩
  set X : Set ℝ := {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h ∧ ℓ (K.curve t) < lam} with hX
  have hfrSL : K.curve t ∈ frontier
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) := by
    rw [Work.Drive.Mono.tiltedLevelRemoved] at htfr
    exact frontier_sdiff_of_mem_open (Work.Topology.SphereSlicing.isOpen_PBox s c σ) htbox htfr
  have hclSL : K.curve t ∈ closure
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) :=
    frontier_subset_closure hfrSL
  have hℓ_le : ℓ (K.curve t) ≤ lam :=
    closure_minimal (fun z hz => le_of_lt hz.2)
      (isClosed_le ℓ.continuous continuous_const) hclSL
  have hwall := Work.Drive.EpsFormSphere.frontier_tiltedSlab_wall_subset
    (inner ℝ v c + u) lam v h ℓ hfrSL
  have hcK : Continuous K.curve := K.smooth.continuous
  have hcψ : Continuous (fun s : ℝ => inner ℝ v (K.curve s)) := continuous_const.inner hcK
  have hdψ : Continuous (deriv (fun s : ℝ => inner ℝ v (K.curve s))) :=
    (show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => inner ℝ v (K.curve s)) from
      (ContinuousLinearMap.contDiff ((innerSL ℝ) v)).comp K.smooth).continuous_deriv (by simp)
  have hcφ : Continuous (fun s : ℝ => ℓ (K.curve s)) := ℓ.continuous.comp hcK
  have hdφ : Continuous (deriv (fun s : ℝ => ℓ (K.curve s))) :=
    (show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ℓ (K.curve s)) from
      (ContinuousLinearMap.contDiff ℓ).comp K.smooth).continuous_deriv (by simp)
  have htrans_slab : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
      ℓ (K.curve t) < lam →
      deriv (fun s : ℝ => inner ℝ v (K.curve s)) t ≠ 0 → t ∈ frontier X := by
    intro hface hℓlt hderiv
    have hnotX : t ∉ X := by
      intro htX
      rw [hX] at htX
      simp only [Set.mem_ofPred_eq] at htX
      linarith [htX.2.1]
    have hcl : t ∈ closure X := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hnhdsP : {r : ℝ | K.curve r ∈ Submission.PBox s c σ} ∈ nhds t :=
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage hcK).mem_nhds htbox
      have hnhdsL : {r : ℝ | ℓ (K.curve r) < lam} ∈ nhds t :=
        (isOpen_lt hcφ continuous_const).mem_nhds hℓlt
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hnhdsP hnhdsL)
      obtain ⟨r, hr, hrface⟩ :=
        exists_near_abs_sub_lt_of_deriv_ne_zero hh hcψ hdψ hderiv hface (min ε δ)
          (lt_min hε hδpos)
      have hrε : |r - t| < ε := lt_of_lt_of_le hr (min_le_left _ _)
      have hrd : Metric.ball t δ r :=
        Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right _ _))
      obtain ⟨hrP, hrL⟩ := hδ hrd
      exact ⟨r, ⟨hrP, hrface, hrL⟩, by rw [Real.dist_eq, abs_sub_comm]; exact hrε⟩
    rw [frontier, Set.mem_sdiff]
    exact ⟨hcl, fun h => hnotX (interior_subset h)⟩
  have htrans_wall : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| < h →
      ℓ (K.curve t) = lam →
      deriv (fun s : ℝ => ℓ (K.curve s)) t ≠ 0 → t ∈ frontier X := by
    intro hlt hℓeq hderiv
    have hnotX : t ∉ X := by
      intro htX
      rw [hX] at htX
      simp only [Set.mem_ofPred_eq] at htX
      linarith [htX.2.2]
    have hcl : t ∈ closure X := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hnhdsP : {r : ℝ | K.curve r ∈ Submission.PBox s c σ} ∈ nhds t :=
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage hcK).mem_nhds htbox
      have hnhdsS : {r : ℝ | |inner ℝ v (K.curve r) - (inner ℝ v c + u)| < h} ∈ nhds t :=
        (isOpen_lt ((hcψ.sub continuous_const).abs) continuous_const).mem_nhds hlt
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hnhdsP hnhdsS)
      obtain ⟨r, hr, hrlt⟩ :=
        (Work.Drive.EpsFormSphere.exists_near_lt_self_and_gt hcφ hdφ hderiv).1 (min ε δ)
          (lt_min hε hδpos)
      have hrε : |r - t| < ε := lt_of_lt_of_le hr (min_le_left _ _)
      have hrd : Metric.ball t δ r :=
        Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right _ _))
      obtain ⟨hrP, hrS⟩ := hδ hrd
      have hrL : ℓ (K.curve r) < lam := by
        rw [← hℓeq]
        exact hrlt
      exact ⟨r, ⟨hrP, hrS, hrL⟩, by rw [Real.dist_eq, abs_sub_comm]; exact hrε⟩
    rw [frontier, Set.mem_sdiff]
    exact ⟨hcl, fun h => hnotX (interior_subset h)⟩
  rcases hwall with hface | ⟨hlt, hℓeq⟩
  · rcases lt_or_eq_of_le hℓ_le with hℓlt | hℓeq
    · by_cases hd : deriv (fun s : ℝ => inner ℝ v (K.curve s)) t = 0
      · exact Or.inl (Or.inr ⟨hface, hd⟩)
      · exact Or.inl (Or.inl (Or.inl (htrans_slab hface hℓlt hd)))
    · exact Or.inr ⟨hface, hℓeq⟩
  · by_cases hd : deriv (fun s : ℝ => ℓ (K.curve s)) t = 0
    · exact Or.inl (Or.inl (Or.inr hd))
    · exact Or.inl (Or.inl (Or.inl (htrans_wall hlt hℓeq hd)))

end

end Work.Drive.Mono
