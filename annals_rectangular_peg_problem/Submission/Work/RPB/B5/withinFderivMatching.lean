import Mathlib

namespace Work.RPB.B5

/-- Two functions `u`, `v : ℝ × P → E` that agree on the slice `x = x₀` and whose one-sided
`x`-derivatives along that slice agree have the same Fréchet derivative at `(x₀, p)` when taken
within the two half-boxes `(a, x₀] × univ` and `[x₀, b) × univ`.

The derivative in the `P`-direction is the full derivative of the slice `z ↦ u (x₀, z)`, common to
both functions; the derivative in the `x`-direction is the one-sided `x`-derivative, which is
matched by `hder`. -/
theorem withinFderivMatching {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : ℝ × P → E) (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b)
    (hval : ∀ p, u (x₀, p) = v (x₀, p))
    (hder : ∀ p, derivWithin (fun x : ℝ => u (x, p)) (Set.Iic x₀) x₀
              = derivWithin (fun x : ℝ => v (x, p)) (Set.Ici x₀) x₀)
    (p : P) (L₁ L₂ : ℝ × P →L[ℝ] E)
    (h₁ : HasFDerivWithinAt u L₁ (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) (x₀, p))
    (h₂ : HasFDerivWithinAt v L₂ (Set.Icc x₀ b ×ˢ (Set.univ : Set P)) (x₀, p)) :
    L₁ = L₂ := by
  have hmem1 : ∀ z : P, (x₀, z) ∈ (Set.Ioc a x₀ ×ˢ (Set.univ : Set P)) :=
    fun z => by simp only [Set.mem_prod]; exact ⟨⟨ha, le_refl x₀⟩, trivial⟩
  have hmem2 : ∀ z : P, (x₀, z) ∈ (Set.Icc x₀ b ×ˢ (Set.univ : Set P)) :=
    fun z => by simp only [Set.mem_prod]; exact ⟨⟨le_refl x₀, hb.le⟩, trivial⟩
  -- Agreement of the two derivatives on the `P`-direction `{0} × P`.
  have hA : L₁.comp (ContinuousLinearMap.inr ℝ ℝ P)
      = L₂.comp (ContinuousLinearMap.inr ℝ ℝ P) := by
    have hπ : HasFDerivAt (fun z : P => (x₀, z)) (ContinuousLinearMap.inr ℝ ℝ P) p := by
      have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ ℝ P)
        (x := p)).const_add (x₀, (0 : P))
      simpa using h
    have hu := h₁.comp_hasFDerivAt p hπ (Filter.Eventually.of_forall hmem1)
    have hv := h₂.comp_hasFDerivAt p hπ (Filter.Eventually.of_forall hmem2)
    have heq : (u ∘ fun z : P => (x₀, z)) = (v ∘ fun z : P => (x₀, z)) := by
      funext z; exact hval z
    rw [heq] at hu
    exact hu.unique hv
  -- Agreement of the two derivatives on the `x`-direction `(1, 0)`.
  have hB : L₁ (1, 0) = L₂ (1, 0) := by
    have hcurve : HasDerivAt (fun x : ℝ => (x, p)) ((1 : ℝ), (0 : P)) x₀ := by
      simpa using (hasDerivAt_id x₀).prodMk (hasDerivAt_const x₀ p)
    have hu : HasDerivWithinAt (fun x : ℝ => u (x, p)) (L₁ (1, 0)) (Set.Ioc a x₀) x₀ := by
      have h := h₁.comp_hasDerivWithinAt x₀ hcurve.hasDerivWithinAt
        (fun x hx => by simp only [Set.mem_prod]; exact ⟨hx, trivial⟩)
      simpa [Function.comp_def] using h
    have hv : HasDerivWithinAt (fun x : ℝ => v (x, p)) (L₂ (1, 0)) (Set.Icc x₀ b) x₀ := by
      have h := h₂.comp_hasDerivWithinAt x₀ hcurve.hasDerivWithinAt
        (fun x hx => by simp only [Set.mem_prod]; exact ⟨hx, trivial⟩)
      simpa [Function.comp_def] using h
    have ud1 : UniqueDiffWithinAt ℝ (Set.Ioc a x₀) x₀ := by
      have h : UniqueDiffWithinAt ℝ (Set.Iic x₀ ∩ Set.Ioi a) x₀ :=
        (uniqueDiffWithinAt_Iic x₀).inter (Ioi_mem_nhds ha)
      have heq : (Set.Iic x₀ ∩ Set.Ioi a) = Set.Ioc a x₀ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]; tauto
      rwa [heq] at h
    have ud2 : UniqueDiffWithinAt ℝ (Set.Icc x₀ b) x₀ := by
      have h : UniqueDiffWithinAt ℝ (Set.Ici x₀ ∩ Set.Iio b) x₀ :=
        (uniqueDiffWithinAt_Ici x₀).inter (Iio_mem_nhds hb)
      exact h.mono (fun x hx => ⟨hx.1, le_of_lt hx.2⟩)
    have e1 : (Set.Ioc a x₀) =ᶠ[nhds x₀] (Set.Iic x₀) := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [Ioi_mem_nhds ha] with x hx
      simp only [Set.mem_Ioc, Set.mem_Iic]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    have e2 : (Set.Icc x₀ b) =ᶠ[nhds x₀] (Set.Ici x₀) := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [Iio_mem_nhds hb] with x hx
      simp only [Set.mem_Icc, Set.mem_Ici]
      exact ⟨fun h => h.1, fun h => ⟨h, le_of_lt hx⟩⟩
    have hd1 : derivWithin (fun x : ℝ => u (x, p)) (Set.Ioc a x₀) x₀ = L₁ (1, 0) :=
      hu.derivWithin ud1
    have hd2 : derivWithin (fun x : ℝ => v (x, p)) (Set.Icc x₀ b) x₀ = L₂ (1, 0) :=
      hv.derivWithin ud2
    have hc1 := derivWithin_congr_set (f := fun x : ℝ => u (x, p)) e1
    have hc2 := derivWithin_congr_set (f := fun x : ℝ => v (x, p)) e2
    exact (hc1.symm.trans hd1).symm.trans ((hder p).trans (hc2.symm.trans hd2))
  -- Assemble from the two coordinate directions.
  have key : ∀ (L : ℝ × P →L[ℝ] E) (t : ℝ) (w : P),
      L (t, w) = t • L (1, 0) + L (0, w) := by
    intro L t w
    have hz : ((t, w) : ℝ × P) = t • (1, 0) + (0, w) := by ext <;> simp
    rw [hz, map_add, map_smul]
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨t, w⟩ := z
  have hw : L₁ (0, w) = L₂ (0, w) := by
    have h := congrArg (fun M : P →L[ℝ] E => M w) hA
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using h
  calc L₁ (t, w) = t • L₁ (1, 0) + L₁ (0, w) := key L₁ t w
    _ = t • L₂ (1, 0) + L₂ (0, w) := by rw [hB, hw]
    _ = L₂ (t, w) := (key L₂ t w).symm

end Work.RPB.B5
