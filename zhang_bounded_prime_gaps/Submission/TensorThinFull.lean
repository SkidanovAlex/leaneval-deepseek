import Submission.TensorThin

set_option maxHeartbeats 2000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The thin tensor data, exposing the full-sum bound

`Submission/TensorThin.exists_tensorData_thin` hides the *full-sum* bound
`Σ_j |c j| ∏_i |Gt j i (t i)| ≤ M` (it returns only the coarse `∃ B` and the marginal bound
`≤ M`).  The full-sum bound is exactly what is needed to bound the `J₂`-part *without* a
marginal bound: for `T ⊆ univ`,

  `|tenP G c i T t| = |∫_{x>0} Σ_{j∈T} c j ∏_l G j l (extendAt i x t_l) dx| ≤ M·(R + 12kη)`,

because the full tensor sum is bounded by `M` and vanishes once `x > R + 12kη` (its
`i`-th components have support radius `≤ R + 12kη`).

This module re-derives `exists_tensorData_thin` with the full-sum bound and the vanishing
`β j i < u → Gt j i u = 0` exposed.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **The thin tensor data with the full-sum bound exposed.** -/
theorem exists_tensorData_thin_full {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    (hk : 1 ≤ k) {η δ cc M : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h1 : R + 24 * (k : ℝ) * η ≤ 1) (hM : ∀ t : Fin k → ℝ, |F t| ≤ M) :
    ∃ (ψ : ℝ → ℝ) (J : ℕ) (Gt : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ)
      (β : Fin J → Fin k → ℝ),
      ψ 0 = 1 ∧ (∀ u : ℝ, 0 ≤ u → ψ u = 1) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ (∀ u : ℝ, u ≤ -(12 * η) → ψ u = 0) ∧
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (Gt j i)) ∧
      (∀ j i, HasCompactSupport (Gt j i)) ∧
      (∀ j i, 0 ≤ β j i) ∧
      (∀ j i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j i u, 0 ≤ u → Gt j i u ≠ 0 → β j i - 6 * η < u ∧ u < β j i) ∧
      (∀ j i u, β j i < u → Gt j i u = 0) ∧
      (∀ t : Fin k → ℝ, ∑ j, |c j| * ∏ i, |Gt j i (t i)| ≤ M) ∧
      |tpAlpha c (fun j i => anti ψ (Gt j) i) - IFuncOrth k F| < δ ∧
      (∀ i₀ : Fin k, |(∫ t : ({l : Fin k // l ≠ i₀} → ℝ),
          (tenP Gt c i₀ Finset.univ t) ^ 2 * margInd k i₀ cc t) - JFunc k i₀ cc F|
        ≤ δ / 2) := by
  classical
  obtain ⟨ψ, hψsm, hψ0', hψ1', hψ01⟩ :=
    Commons.Analysis.Calculus.exists_contDiff_step (-(12 * η)) 0 (by linarith)
  have hψ0 : ψ 0 = 1 := hψ1' 0 le_rfl
  have hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1 := fun u hu => hψ1' u hu
  obtain ⟨J, β, Gt, c, hGtsm, hGtcs, hGtvan, hβnn, hβind, hβsum, hthin, hBdata, hJnear,
      hαnear, hβnear, _hBmargdata⟩ :=
    exists_tensorData_near hFc hFcs hR0 hR hψ0 hψ1 hη hδ hM
  obtain ⟨Gtf, Bg, el, CF, hGtf_eq, hBg, hel, hCF0, hCF, hGcoord, happrox, hfullM, hmargM,
    hbound⟩ := hJnear
  refine ⟨ψ, J, Gt, c, β, hψ0, hψ1, hψsm, hψ0', hGtsm, hGtcs, hβnn, hβind, hβsum, hthin,
    hGtvan, hfullM, hαnear, ?_⟩
  have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
  have hRB : R ≤ Bg := by rw [hBg]; nlinarith [hη, Nat.cast_nonneg (α := ℝ) k]
  have hF0 : ∀ s : Fin k → ℝ, F s ≠ 0 → ∀ i, 0 ≤ s i := fun s hs => (hR s hs).1
  have hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨hnn, hle⟩ := hR s hne
    obtain ⟨i, hi⟩ := hs
    have : s i ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
    linarith
  have hGcoord' : ∀ s : Fin k → ℝ,
      (∃ i, Bg < s i) → (∑ j : Fin J, c j * ∏ l, Gt j l (s l)) = 0 := by
    intro s hs
    rw [← hGtf_eq]
    exact hGcoord s hs
  have happrox' : ∀ s : Fin k → ℝ, |(∑ j : Fin J, c j * ∏ l, Gt j l (s l)) - F s| ≤ el := by
    intro s
    rw [← hGtf_eq]
    exact happrox s
  intro i₀
  refine le_trans ?_ hbound
  refine margTensor_near_JFunc Gt (fun j i => (hGtsm j i).continuous) hGtcs
    (fun j i => ((hGtsm j i).continuous).integrable_of_hasCompactSupport (hGtcs j i))
    c i₀ cc hFc hCF0 hCF hBg0 hRB hel hFcoord hGcoord' happrox' hF0

end Commons.NumberTheory.MaynardSieve
