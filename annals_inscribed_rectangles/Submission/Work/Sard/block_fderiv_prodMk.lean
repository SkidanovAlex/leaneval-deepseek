import Mathlib

namespace Work.Sard

/-- Linear-algebra core: for a continuous linear map `D : G × C →L[ℝ] W`, the "block matrix"
map `(g, c) ↦ (g, D (g, c))` is surjective iff the second block `D ∘ inr` is surjective.
Indeed `D (x, c) = D (x, 0) + D (0, c)`, and adding the constant `D (x, 0)` does not change
surjectivity of `c ↦ D (x, c)`. -/
lemma block_aux {G C W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : G × C →L[ℝ] W) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ G C).prod D) ↔
      Function.Surjective (D.comp (ContinuousLinearMap.inr ℝ G C)) := by
  constructor
  · intro hL y
    obtain ⟨v, hv⟩ := hL (0, y)
    rw [ContinuousLinearMap.prod_apply] at hv
    have hv1 : v.1 = 0 := congrArg Prod.fst hv
    have hv2 : D v = y := congrArg Prod.snd hv
    refine ⟨v.2, ?_⟩
    have h0 : ((0 : G), v.2) = v := by rw [← hv1]
    show D (0, v.2) = y
    rw [h0, hv2]
  · intro hB
    rintro ⟨x1, x2⟩
    obtain ⟨w, hw⟩ := hB (x2 - D (x1, 0))
    have hw' : D (0, w) = x2 - D (x1, 0) := by
      have h := hw
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at h
      exact h
    refine ⟨(x1, w), ?_⟩
    have hD : D (x1, w) = x2 := by
      have hsplit : ((x1, w) : G × C) = (x1, 0) + (0, w) := by ext <;> simp
      rw [hsplit, map_add, hw']
      abel
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext rfl hD

theorem block_fderiv_prodMk {G C W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : G × C → W) (p : G × C) (hg : DifferentiableAt ℝ g p) :
    Function.Surjective (fderiv ℝ (fun z : G × C => (z.1, g z)) p) ↔
      Function.Surjective (fderiv ℝ (fun c : C => g (p.1, c)) p.2) := by
  have hL : fderiv ℝ (fun z : G × C => (z.1, g z)) p
      = (ContinuousLinearMap.fst ℝ G C).prod (fderiv ℝ g p) := by
    rw [DifferentiableAt.fderiv_prodMk (𝕜 := ℝ) (f₁ := (Prod.fst : G × C → G))
        differentiableAt_fst hg, fderiv_fst]
  have hB : fderiv ℝ (fun c : C => g (p.1, c)) p.2
      = (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ G C) := by
    have hg' : HasFDerivAt g (fderiv ℝ g p) ((p.1, p.2) : G × C) := by
      rw [Prod.mk.eta]; exact hg.hasFDerivAt
    exact (hg'.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  rw [hL, hB]
  exact block_aux (fderiv ℝ g p)

end Work.Sard
