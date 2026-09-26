import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Covering
import Submission.Work.TorusCover.Lifting
import Submission.Work.TorusCover.hasWinding_eq_of_homotopicClosed
import Submission.Work.TorusCover.homotopicClosed_of_hasWinding

/-!
# The winding vector is a complete homotopy invariant

`Work.TorusCover.HomotopicClosed psi γ₀ γ₁` is the relation "the closed curves `γ₀` and `γ₁`
(with values in the range of `psi`) are homotopic through closed curves in the range of `psi`".

The main results:

* `Work.TorusCover.HomotopicClosed.hasWinding_eq` — homotopic closed curves have the same
  winding vector (the `⟹` direction of the characterisation), so the winding vector is an
  invariant of the free homotopy class, and an essential curve is not null-homotopic;
* `Work.TorusCover.homotopicClosed_iff_hasWinding` — for two curves with the same value at `0`,
  being homotopic through closed curves in the range is *equivalent* to having the same winding
  vector.  Thus the winding vector is a complete invariant of the free homotopy class of closed
  curves in the range of `psi`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-! ### Basic projections of a homotopy -/

section Projections

variable {psi : ℝ → ℝ → R3} {γ₀ γ₁ : ℝ → R3}

lemma HomotopicClosed.continuous_left (h : HomotopicClosed psi γ₀ γ₁) : Continuous γ₀ := by
  obtain ⟨H, hc, h0, -, -, -⟩ := h
  have : Continuous fun t : ℝ => H (0, t) := hc.comp (continuous_const.prodMk continuous_id)
  simpa [Function.comp_def, h0] using this

lemma HomotopicClosed.continuous_right (h : HomotopicClosed psi γ₀ γ₁) : Continuous γ₁ := by
  obtain ⟨H, hc, -, h1, -, -⟩ := h
  have : Continuous fun t : ℝ => H (1, t) := hc.comp (continuous_const.prodMk continuous_id)
  simpa [Function.comp_def, h1] using this

lemma HomotopicClosed.periodic_right (h : HomotopicClosed psi γ₀ γ₁) (t : ℝ) :
    γ₁ (t + 2 * Real.pi) = γ₁ t := by
  obtain ⟨H, -, -, h1, hper, -⟩ := h
  simp only [← h1 t, ← h1 (t + 2 * Real.pi)]
  exact hper 1 t

lemma HomotopicClosed.periodic_left (h : HomotopicClosed psi γ₀ γ₁) (t : ℝ) :
    γ₀ (t + 2 * Real.pi) = γ₀ t := by
  obtain ⟨H, -, h0, -, hper, -⟩ := h
  simp only [← h0 t, ← h0 (t + 2 * Real.pi)]
  exact hper 0 t

lemma HomotopicClosed.mem_range_right (h : HomotopicClosed psi γ₀ γ₁) (t : ℝ) :
    γ₁ t ∈ Set.range (psiMap psi) := by
  obtain ⟨H, -, -, h1, -, hmem⟩ := h
  rw [← h1 t]
  exact hmem 1 t

lemma HomotopicClosed.mem_range_left (h : HomotopicClosed psi γ₀ γ₁) (t : ℝ) :
    γ₀ t ∈ Set.range (psiMap psi) := by
  obtain ⟨H, -, h0, -, -, hmem⟩ := h
  rw [← h0 t]
  exact hmem 0 t

end Projections

/-! ### Homotopy invariance -/

/-- **Homotopic closed curves have the same winding vector.** -/
theorem HomotopicClosed.hasWinding_eq (P : TorusParam) {γ₀ γ₁ : ℝ → R3} {v w : ℤ × ℤ}
    (h : HomotopicClosed P.psi γ₀ γ₁) (hv : HasWinding P.psi γ₀ v)
    (hw : HasWinding P.psi γ₁ w) : v = w :=
  _root_.Work.TorusCover.hasWinding_eq_of_homotopicClosed P P.isCoveringMap_psiMapToRange h hv hw

/-- **Two closed curves in the range of `psi` with the same winding vector are homotopic through
closed curves in the range of `psi`.**  If `Λ₀` and `Λ₁` are periodic lifts with the same winding
vector `v`, the straight-line interpolation `Λ_s := (1 - s) • Λ₀ + s • Λ₁` still satisfies
`Λ_s (t + 2π) = Λ_s t + periodShift v`, so `H (s, t) = psi (Λ_s t)` is a homotopy through closed
curves in the range.  No base-point matching is needed. -/
theorem homotopicClosed_of_same_winding (P : TorusParam) {γ₀ γ₁ : ℝ → R3} {v : ℤ × ℤ}
    (hv₀ : HasWinding P.psi γ₀ v) (hv₁ : HasWinding P.psi γ₁ v) :
    HomotopicClosed P.psi γ₀ γ₁ := by
  obtain ⟨Λ₀, hΛ₀⟩ := hv₀
  obtain ⟨Λ₁, hΛ₁⟩ := hv₁
  have hc₀ : Continuous Λ₀ := hΛ₀.continuous
  have hc₁ : Continuous Λ₁ := hΛ₁.continuous
  have hlip : Continuous fun st : ℝ × ℝ =>
      (1 - st.1) • Λ₀ st.2 + st.1 • Λ₁ st.2 :=
    (((continuous_const.sub continuous_fst).smul (hc₀.comp continuous_snd)).add
      (continuous_fst.smul (hc₁.comp continuous_snd)))
  refine ⟨fun st : ℝ × ℝ => psiMap P.psi ((1 - st.1) • Λ₀ st.2 + st.1 • Λ₁ st.2),
    P.contDiff.continuous.comp hlip, ?_, ?_, ?_, ?_⟩
  · intro t
    change psiMap P.psi ((1 - (0 : ℝ)) • Λ₀ t + (0 : ℝ) • Λ₁ t) = γ₀ t
    simp only [sub_zero, one_smul, zero_smul, add_zero, psiMap_apply]
    exact hΛ₀.1.2 t
  · intro t
    change psiMap P.psi ((1 - (1 : ℝ)) • Λ₀ t + (1 : ℝ) • Λ₁ t) = γ₁ t
    simp only [sub_self, zero_smul, one_smul, zero_add, psiMap_apply]
    exact hΛ₁.1.2 t
  · intro s t
    have harg : (1 - s) • Λ₀ (t + 2 * Real.pi) + s • Λ₁ (t + 2 * Real.pi)
        = ((1 - s) • Λ₀ t + s • Λ₁ t) + periodShift v := by
      rw [hΛ₀.2 t, hΛ₁.2 t]
      module
    simp only [harg, P.psiMap_add_periodShift]
  · intro s t
    exact Set.mem_range_self _

/-- **Homotopy classification of closed curves in the range of `psi`.**  Two closed curves in the
range of `psi` are homotopic through closed curves in the range of `psi` *iff* they have the same
winding vector. -/
theorem homotopicClosed_iff_hasWinding (P : TorusParam) {γ₀ γ₁ : ℝ → R3} {v w : ℤ × ℤ}
    (hv₀ : HasWinding P.psi γ₀ v) (hw : HasWinding P.psi γ₁ w) :
    HomotopicClosed P.psi γ₀ γ₁ ↔ v = w := by
  refine ⟨fun h => h.hasWinding_eq P hv₀ hw, fun h => ?_⟩
  subst h
  exact homotopicClosed_of_same_winding P hv₀ hw

/-- An essential closed curve is not null-homotopic: it is not homotopic through closed curves
in the range of `psi` to a curve whose image lies in a simply connected piece of the torus
(e.g. a constant curve). -/
theorem not_homotopicClosed_of_isEssential_of_hasWinding_zero (P : TorusParam)
    {γ₀ γ₁ : ℝ → R3} {v : ℤ × ℤ} (hv : HasWinding P.psi γ₀ v) (hv0 : v ≠ 0)
    (hw : HasWinding P.psi γ₁ 0) : ¬ HomotopicClosed P.psi γ₀ γ₁ :=
  fun h => hv0 (h.hasWinding_eq P hv hw)

end

end Work.TorusCover
