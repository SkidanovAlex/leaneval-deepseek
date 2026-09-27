import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2Lead.chartJunkZero

namespace Work.Drive.N2Lead

/-- **Wiping the junk values of the marked chart of a window datum to zero.**

`Work.Drive.N2Lead.chartJunkZero` replaces the forward map of a chart by "the chart on its source,
`0` off it", keeping source, target and inverse.  Applied to the marked chart `D.φ D.j` of a window
datum, the whole datum may be rebuilt with that chart: every field of the datum that mentions the
chart does so only through its source, its target, its inverse and its values *on the source*
(`modelBall`, `chartQ`, the disjointness of the sources, the continuity of the chart and of its
inverse, the closedness of `C i` inside the source, the value separation `hsepK`), and all of these
are unchanged.  The marked point `p`, the parameters `s₁, s₂, ρ, C, ηd`, the critical enumeration
`x` and the flow `Φ` are untouched, and the pin set `saddlePin D v m` — which tests source
membership before looking at the chart values — is unchanged as well.

This is the "junk-zero normalisation" lemma: it turns the partial chart into a globally defined map
while preserving every piece of data a consumer of the window datum can see. -/
theorem exists_junkZeroDatum {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) :
    ∃ D' : Work.Drive.N2.WindowDatum f p,
      (D'.φ D'.j).source = (D.φ D.j).source ∧
      (∀ y : M, y ∈ (D.φ D.j).source → D'.φ D'.j y = D.φ D.j y) ∧
      (∀ y : M, y ∉ (D.φ D.j).source → D'.φ D'.j y = 0) ∧
      D'.s₁ D'.j = D.s₁ D.j ∧ D'.s₂ D'.j = D.s₂ D.j ∧
      D'.ρ D'.j = D.ρ D.j ∧ D'.C D'.j = D.C D.j ∧ D'.ηd = D.ηd ∧
      D'.x D'.j = D.x D.j ∧ (∀ y : ℝ × M, D'.Φ y = D.Φ y) ∧
      (∀ (v m : ℝ), Work.Drive.N2Lead.saddlePin D' v m =
        Work.Drive.N2Lead.saddlePin D v m) := by
  classical
  obtain ⟨ψ, hψsrc, hψtgt, hψon, hψoff, hψsymm, hψball⟩ :=
    Work.Drive.N2Lead.chartJunkZero (D.φ D.j)
  -- the modified chart family: `ψ` at the marked index, `D.φ i` elsewhere
  let φ' : Fin D.N → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    fun i => if i = D.j then ψ else D.φ i
  have hsrcj : ∀ i, (φ' i).source = (D.φ i).source := by
    intro i
    by_cases hi : i = D.j
    · subst hi
      simp only [φ', if_pos rfl]
      exact hψsrc
    · simp only [φ', if_neg hi]
  have hagree : ∀ i y, y ∈ (D.φ i).source → φ' i y = D.φ i y := by
    intro i y hy
    by_cases hi : i = D.j
    · subst hi
      simp only [φ', if_pos rfl]
      exact hψon y hy
    · simp only [φ', if_neg hi]
  have htarget : ∀ i, (φ' i).target = (D.φ i).target := by
    intro i
    by_cases hi : i = D.j
    · subst hi
      simp only [φ', if_pos rfl]
      exact hψtgt
    · simp only [φ', if_neg hi]
  have hsymm : ∀ i z, (φ' i).symm z = (D.φ i).symm z := by
    intro i z
    by_cases hi : i = D.j
    · subst hi
      simp only [φ', if_pos rfl]
      exact hψsymm z
    · simp only [φ', if_neg hi]
  have hball : ∀ i r, Work.Drive.N2.modelBall (φ' i) r =
      Work.Drive.N2.modelBall (D.φ i) r := by
    intro i r
    ext y
    simp only [Work.Drive.N2.modelBall, Set.mem_setOf_eq, hsrcj i]
    by_cases hy : y ∈ (D.φ i).source
    · have h1 : φ' i y = D.φ i y := hagree i y hy
      simp [hy, h1]
    · simp [hy]
  have hagree' : ∀ i y, y ∈ (φ' i).source → φ' i y = D.φ i y := by
    intro i y hy
    exact hagree i y (by rwa [hsrcj i] at hy)
  have hφ'j : φ' D.j = ψ := by
    simp only [φ', if_pos rfl]
  let D' : Work.Drive.N2.WindowDatum f p :=
    { N := D.N
      x := D.x
      φ := φ'
      s₁ := D.s₁
      s₂ := D.s₂
      ρ := D.ρ
      C := D.C
      j := D.j
      hxj := D.hxj
      hinj := D.hinj
      hcrit := D.hcrit
      hcover := D.hcover
      hρ := D.hρ
      hsrc := by
        intro i
        rw [hsrcj i]
        exact D.hsrc i
      hcen := by
        intro i
        rw [hagree i (D.x i) (D.hsrc i)]
        exact D.hcen i
      hsgn := D.hsgn
      hval := by
        intro i y hy
        have hy' : y ∈ (D.φ i).source := by rwa [hsrcj i] at hy
        have hvy : φ' i y = D.φ i y := hagree i y hy'
        simp only [Work.Drive.N2.chartQ, hvy]
        exact D.hval i y hy'
      hφ := by
        intro i
        have h := D.hφ i
        rw [← hsrcj i] at h
        refine h.congr ?_
        intro y hy
        exact hagree' i y hy
      hφ' := by
        intro i
        have h := D.hφ' i
        rw [← htarget i] at h
        refine h.congr ?_
        intro z hz
        exact hsymm i z
      hdisj := by
        intro i j' hij
        rw [hsrcj i, hsrcj j']
        exact D.hdisj i j' hij
      hCsub := by
        intro i
        rw [hsrcj i]
        exact D.hCsub i
      hCclosed := D.hCclosed
      hCcl := by
        intro i
        rw [hsrcj i]
        exact D.hCcl i
      hCball := by
        intro i
        rw [hball i (D.ρ i / 8)]
        exact D.hCball i
      hCop := by
        intro i
        change Work.Drive.N2.modelBall (φ' i) (D.ρ i) ⊆ D.C i
        rw [hball i (D.ρ i)]
        exact D.hCop i
      ηd := D.ηd
      hηd := D.hηd
      hηd' := D.hηd'
      hsep := D.hsep
      hsepK := by
        intro i j' hij z hz
        rw [hball i (D.ρ i / 8)] at hz
        exact D.hsepK i j' hij z hz
      Φ := D.Φ
      hΦsm := D.hΦsm
      hΦ0 := D.hΦ0
      hΦcomp := D.hΦcomp
      hlevel := by
        intro y t hy
        refine D.hlevel y t ?_
        intro u hu i
        have h1 : D.Φ (u, y) ∉ Work.Drive.N2.modelBall (φ' i) (D.ρ i / 8) := hy u hu i
        rwa [hball i (D.ρ i / 8)] at h1
      hODE := by
        intro i y t ht
        have hsrc_t : D.Φ (t, y) ∈ (D.φ i).source :=
          D.hCsub i (ht t ⟨min_le_right 0 t, le_max_right 0 t⟩)
        have hcont : Continuous fun σ : ℝ => D.Φ (σ, y) :=
          D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
        have hmem : ∀ᶠ σ in nhds t, D.Φ (σ, y) ∈ (D.φ i).source :=
          hcont.continuousAt.preimage_mem_nhds
            ((D.φ i).open_source.mem_nhds hsrc_t)
        have hval : φ' i (D.Φ (t, y)) = D.φ i (D.Φ (t, y)) :=
          hagree i (D.Φ (t, y)) hsrc_t
        have hev0 : (fun σ : ℝ => φ' i (D.Φ (σ, y)) 0) =ᶠ[nhds t]
            (fun σ : ℝ => D.φ i (D.Φ (σ, y)) 0) := by
          filter_upwards [hmem] with σ hσ
          rw [hagree i (D.Φ (σ, y)) hσ]
        have hev1 : (fun σ : ℝ => φ' i (D.Φ (σ, y)) 1) =ᶠ[nhds t]
            (fun σ : ℝ => D.φ i (D.Φ (σ, y)) 1) := by
          filter_upwards [hmem] with σ hσ
          rw [hagree i (D.Φ (σ, y)) hσ]
        obtain ⟨h0, h1⟩ := D.hODE i y t ht
        refine ⟨?_, ?_⟩
        · rw [hval]
          exact h0.congr_of_eventuallyEq hev0
        · rw [hval]
          exact h1.congr_of_eventuallyEq hev1
      hmono := D.hmono }
  have hDφ : D'.φ = φ' := rfl
  have hDj : D'.j = D.j := rfl
  have hDs₁ : D'.s₁ = D.s₁ := rfl
  have hDs₂ : D'.s₂ = D.s₂ := rfl
  have hDρ : D'.ρ = D.ρ := rfl
  have hDC : D'.C = D.C := rfl
  have hDη : D'.ηd = D.ηd := rfl
  have hDx : D'.x = D.x := rfl
  have hDΦ : D'.Φ = D.Φ := rfl
  refine ⟨D', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDφ, hDj, hφ'j]
    exact hψsrc
  · intro y hy
    rw [hDφ, hDj, hφ'j]
    exact hψon y hy
  · intro y hy
    rw [hDφ, hDj, hφ'j]
    exact hψoff y hy
  · rw [hDs₁, hDj]
  · rw [hDs₂, hDj]
  · rw [hDρ, hDj]
  · rw [hDC, hDj]
  · rw [hDη]
  · rw [hDx, hDj]
  · intro y
    rw [hDΦ]
  · intro v m
    ext x
    simp only [Work.Drive.N2Lead.saddlePin, Set.mem_setOf_eq]
    rw [hDφ, hDj, hDρ, hsrcj D.j]
    by_cases hx : x ∈ (D.φ D.j).source
    · have hxx : φ' D.j x = D.φ D.j x := hagree D.j x hx
      simp [hx, hxx]
    · simp [hx]

end Work.Drive.N2Lead
