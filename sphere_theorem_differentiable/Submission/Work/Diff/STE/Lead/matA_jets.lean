import Mathlib
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set Metric Filter

namespace Work.Diff.STE.Lead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The weight `matA D i = ψ i · √(dens i)` is globally `C^∞`.**

Inside the topological support of the cut-off `χ i` the chart parameter `flatToE (x₀ i) z` lies in
the chart target (`B3Data.hχtsup`), so both factors are smooth there: `ψ i` is the product of the
smooth `χ i` with `ζ i ∘ pt i` (`B3Data.psi_contDiff`) and `√(dens i)` is smooth because `dens i`
is positive and smooth on the chart target (`Work.Diff.STE.B3.densGood`, i.e. `DensGood`, together
with `Real.contDiffAt_sqrt`).  Off the topological support, `ψ i` — hence `matA D i` — vanishes on
a whole neighbourhood.  No metric fact beyond the positivity of the chart Gram determinant is
used, and in particular the smoothness is global, not merely on the `2σ`-ball. -/
theorem matA_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContDiff ℝ (⊤ : ℕ∞) (matA (I := I) (M := M) D i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (D.χ i)
  · have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.hχtsup i z hz
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi i) z := (D.psi_contDiff i).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Real.sqrt (D.dens i z)) z :=
      D.sqrt_dens_contDiffAt i (Work.Diff.STE.B3.densGood D i) hzt
    exact h1.mul h2
  · have hz' : ∀ᶠ y in 𝓝 z, y ∉ tsupport (D.χ i) :=
      (isClosed_tsupport (D.χ i)).isOpen_compl.mem_nhds hz
    have h0 : matA (I := I) (M := M) D i =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hz'] with y hy
      simp only [matA, Work.Diff.STE.B3Data.psi,
        image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0

/-- `pdR q (pdR p f) z` is the second iterated derivative of `f` at `z` evaluated on the tuple
`(∂_q, ∂_p) = (![single q 1, single p 1])`.

This is the chain rule hidden in `DifferentiableAt.iteratedFDeriv_succ_apply_left'` at `n = 1`,
applied to the function `y ↦ fderiv ℝ f y (single p 1) = pdR p f y`: the `∂_q`-derivative of
`∂_p f` is the second derivative of `f` in the pair `(∂_q, ∂_p)`. -/
theorem pdR_pdR_eq_iteratedFDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (h : ContDiff ℝ (⊤ : ℕ∞) f)
    (p q : Fin n) (z : Fin n → ℝ) :
    pdR q (pdR p f) z =
      iteratedFDeriv ℝ 2 f z (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z :=
    (((h.iteratedFDeriv_right (i := 1) (m := (1 : WithTop ℕ∞)) (by simp)).differentiable
      (by norm_num)).differentiableAt)
  have hk : iteratedFDeriv ℝ 2 f z (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) =
      (fderiv ℝ (fun y => (iteratedFDeriv ℝ 1 f y)
        (Fin.tail (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)))) z)
        ((![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)) 0) := by
    simpa using hd.iteratedFDeriv_succ_apply_left'
      (m := (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ)))
  rw [hk]
  rw [show (fun y => (iteratedFDeriv ℝ 1 f y)
        (Fin.tail (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin n → ℝ))))
      = fun y => fderiv ℝ f y (Pi.single p 1) from by
    funext y
    rw [iteratedFDeriv_one_apply]
    rfl]
  rfl

/-- The second derivative tuple `![single q 1, single p 1]` has multilinear norm `1`. -/
theorem norm_prod_tuple {n : ℕ} (p q : Fin n) :
    ∏ i : Fin 2, ‖(![Pi.single q (1 : ℝ), Pi.single p (1 : ℝ)] :
      Fin 2 → (Fin n → ℝ)) i‖ = 1 := by
  rw [Fin.prod_univ_two]
  simp [Pi.norm_single]

/-- Uniform bounds for the weight `matA D i = ψ i · √(dens i)` and its first two derivatives on
the closed `σ i`-ball, with a single constant `K` for all charts `i` and all points `z` with
`‖z‖ ≤ D.σ i`.  (`D.R i h a b z = matA D i z * D.mat i h a b z`.)

Route.
* The open ball `U := Metric.ball 0 (2 * D.σ i)` contains the closed ball
  `Metric.closedBall 0 (D.σ i)` (use `D.hσ i`), and `matA D i` is `C^∞` on `U`: for `z ∈ U` one has
  `‖z‖ ≤ 2 * D.σ i`, so `flatToE (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target` (`D.htarget`), hence
  `ContDiffAt ℝ ⊤ (fun z => Real.sqrt (D.dens i z)) z` (from `D.DensGood i`, which is proved
  unconditionally by `Work.Diff.STE.B3.densGood`, using `Real.contDiffAt_sqrt`) and
  `ContDiffAt ℝ ⊤ (D.psi i) z` (`Work.Diff.STE.B3Data.psi_contDiff`), so their product is
  `ContDiffAt`; conclude `ContDiffOn ℝ ⊤ (matA D i) U` with `IsOpen.contDiffOn_iff`.
* `Work.Diff.STE.flat.compact_iteratedFDeriv_bound (matA D i) (isOpen_ball) hcd isCompact_closedBall
  (subset) 2` gives `K i` with `‖iteratedFDeriv ℝ j (matA D i) z‖ ≤ K i` for `z` in the closed
  `σ`-ball and all `j ≤ 2`; take the maximum over the finite type `ι₀` (`Finset.univ.sup'`, or the
  constant `0` when `ι₀` is empty).
* `j = 0` gives `|matA D i z| ≤ K` (`norm_iteratedFDeriv_zero`); for `j = 1` and `j = 2` use
  `pdR p f z = fderiv ℝ f z (Pi.single p 1)`,
  `iteratedFDeriv_succ_apply_left` (at `n = 0`, together with
  `continuousMultilinearCurryFin0`) and `DifferentiableAt.iteratedFDeriv_succ_apply_left'`
  (at `n = 1`) to identify `pdR q (pdR p f) z` with `iteratedFDeriv ℝ 2 f z m` for a suitable tuple
  `m : Fin 2 → (Fin (Module.finrank ℝ E) → ℝ)`, then bound with
  `ContinuousMultilinearMap.le_opNorm` and `Pi.norm_single`. -/
theorem matA_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
      |Work.Diff.STE.Lead.matA (I := I) (M := M) D i z| ≤ K ∧
      (∀ p : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.pdR p (Work.Diff.STE.Lead.matA (I := I) (M := M) D i) z| ≤ K) ∧
      (∀ p q : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.pdR q
          (Work.Diff.STE.pdR p (Work.Diff.STE.Lead.matA (I := I) (M := M) D i)) z| ≤ K) := by
  classical
  -- One bound per chart, from the global `C^∞`-regularity of the weight.
  have hper : ∀ i : ι₀, ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ i →
        |matA (I := I) (M := M) D i z| ≤ Ki ∧
        (∀ p : Fin (Module.finrank ℝ E),
          |Work.Diff.STE.pdR p (matA (I := I) (M := M) D i) z| ≤ Ki) ∧
        (∀ p q : Fin (Module.finrank ℝ E),
          |Work.Diff.STE.pdR q
            (Work.Diff.STE.pdR p (matA (I := I) (M := M) D i)) z| ≤ Ki) := by
    intro i
    set f := matA (I := I) (M := M) D i with hf
    have hcd : ContDiff ℝ (⊤ : ℕ∞) f := matA_contDiff D i
    obtain ⟨Ki, hKi0, hKi⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound
      f isOpen_univ hcd.contDiffOn
      (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) (subset_univ _) 2
    refine ⟨Ki, hKi0, ?_⟩
    intro z hz
    have hzmem : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz
    have b0 := hKi z hzmem 0 (by norm_num)
    have b1 := hKi z hzmem 1 (by norm_num)
    have b2 := hKi z hzmem 2 (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · -- the value itself: level `0` of the tower
      simpa [Real.norm_eq_abs] using b0
    · -- first derivatives: level `1` of the tower
      intro p
      have hle := ContinuousLinearMap.le_opNorm (fderiv ℝ f z) (Pi.single p 1)
      have hsingle : ‖(Pi.single p (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)‖ = 1 := by
        rw [Pi.norm_single]; norm_num
      have hone : ‖iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f z‖ := norm_iteratedFDeriv_one f
      calc |Work.Diff.STE.pdR p f z|
          = ‖(fderiv ℝ f z) (Pi.single p (1 : ℝ))‖ := by
            rw [Work.Diff.STE.pdR]
            exact (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ f z‖ * ‖(Pi.single p (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)‖ := hle
        _ = ‖fderiv ℝ f z‖ := by rw [hsingle, mul_one]
        _ = ‖iteratedFDeriv ℝ 1 f z‖ := hone.symm
        _ ≤ Ki := b1
    · -- second derivatives: level `2` of the tower
      intro p q
      have hkey := pdR_pdR_eq_iteratedFDeriv f hcd p q z
      have hkey2 : |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z| =
          ‖(iteratedFDeriv ℝ 2 f z)
            (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin (Module.finrank ℝ E) → ℝ))‖ := by
        rw [hkey]
        exact (Real.norm_eq_abs _).symm
      rw [hkey2]
      calc ‖(iteratedFDeriv ℝ 2 f z)
            (![Pi.single q 1, Pi.single p 1] : Fin 2 → (Fin (Module.finrank ℝ E) → ℝ))‖
          ≤ ‖iteratedFDeriv ℝ 2 f z‖ * ∏ i : Fin 2,
              ‖(![Pi.single q 1, Pi.single p 1] :
                Fin 2 → (Fin (Module.finrank ℝ E) → ℝ)) i‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ 2 f z‖ := by rw [norm_prod_tuple, mul_one]
        _ ≤ Ki := b2
  choose Kf hKf0 hKf using hper
  -- Combine the finitely many chartwise constants into one (the sum; `0` when `ι₀` is empty).
  refine ⟨∑ i : ι₀, Kf i, Finset.sum_nonneg (fun i _ => hKf0 i), ?_⟩
  intro i z hz
  have hle : Kf i ≤ ∑ j : ι₀, Kf j :=
    Finset.single_le_sum (fun j _ => hKf0 j) (Finset.mem_univ i)
  obtain ⟨h1, h2, h3⟩ := hKf i z hz
  exact ⟨le_trans h1 hle, fun p => le_trans (h2 p) hle, fun p q => le_trans (h3 p q) hle⟩

end Work.Diff.STE.Lead
