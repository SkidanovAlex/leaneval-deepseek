import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear

set_option linter.unusedVariables false

noncomputable section

open Set Filter
open scoped ENNReal NNReal Topology

namespace Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- At order one, the norm of a difference of iterated derivatives agrees with the norm of the
difference of the (within) Fréchet derivatives: the two are identified by the linear isometry
`continuousMultilinearCurryFin1`. -/
lemma norm_iteratedFDerivWithin_one_sub {P : Set X} (f : X → ℂ) {x y : X}
    (hx : UniqueDiffWithinAt ℝ P x) (hy : UniqueDiffWithinAt ℝ P y) :
    ‖iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y‖
      = ‖fderivWithin ℝ f P x - fderivWithin ℝ f P y‖ := by
  have key : ∀ z : X, UniqueDiffWithinAt ℝ P z →
      continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDerivWithin ℝ 1 f P z)
        = fderivWithin ℝ f P z := by
    intro z hz
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDerivWithin_one_apply hz]
    simp
  calc ‖iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y‖
      = ‖continuousMultilinearCurryFin1 ℝ X ℂ
          (iteratedFDerivWithin ℝ 1 f P x - iteratedFDerivWithin ℝ 1 f P y)‖ :=
        (LinearIsometryEquiv.norm_map _ _).symm
    _ = ‖fderivWithin ℝ f P x - fderivWithin ℝ f P y‖ := by rw [map_sub, key x hx, key y hy]

end Work.CR.Flat

namespace Work.NN.Core

open Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Componentwise bounds -/

private lemma le_holderSeminorm_zero (α : ℝ) (f : X → ℂ) (Ω : Set X) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) ≤ holderSeminorm 0 α f Ω := by
  rw [← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub f Ω x y]
  exact le_holderSeminorm 0 α f Ω hx hy hxy

private lemma le_holderSeminorm_one (α : ℝ) (f : X → ℂ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal (‖fderivWithin ℝ f Ω x - fderivWithin ℝ f Ω y‖ / ‖x - y‖ ^ α)
      ≤ holderSeminorm 1 α f Ω := by
  rw [← Work.CR.Flat.norm_iteratedFDerivWithin_one_sub f (hΩ.uniqueDiffWithinAt hx)
    (hΩ.uniqueDiffWithinAt hy)]
  exact le_holderSeminorm 1 α f Ω hx hy hxy

private lemma le_iterDerivNorm_zero (f : X → ℂ) (Ω : Set X) {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖f x‖ ≤ iterDerivNorm 0 f Ω := by
  rw [iterDerivNorm_zero]
  exact le_iSup₂_of_le x hx le_rfl

private lemma le_iterDerivNorm_one (f : X → ℂ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω)
    {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖fderivWithin ℝ f Ω x‖ ≤ iterDerivNorm 1 f Ω := by
  rw [← norm_iteratedFDerivWithin_one f (hΩ.uniqueDiffWithinAt hx)]
  exact le_iterDerivNorm 1 f Ω hx

/-- `iterDerivNorm 0` is subadditive, with no differentiability hypothesis. -/
private lemma iterDerivNorm_zero_add_le (f g : X → ℂ) (Ω : Set X) :
    iterDerivNorm 0 (f + g) Ω ≤ iterDerivNorm 0 f Ω + iterDerivNorm 0 g Ω := by
  simp only [iterDerivNorm_zero]
  refine iSup₂_le fun x hx => ?_
  calc ENNReal.ofReal ‖(f + g) x‖
      = ENNReal.ofReal ‖f x + g x‖ := by simp
    _ ≤ ENNReal.ofReal (‖f x‖ + ‖g x‖) := ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖f x‖ + ENNReal.ofReal ‖g x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖) + (⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖) :=
        add_le_add (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)

/-- `holderSeminorm 0` is subadditive, with no differentiability hypothesis. -/
private lemma holderSeminorm_zero_add_le (α : ℝ) (f g : X → ℂ) (Ω : Set X) :
    holderSeminorm 0 α (f + g) Ω ≤ holderSeminorm 0 α f Ω + holderSeminorm 0 α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub (f + g) Ω x y]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  calc ENNReal.ofReal (‖(f + g) x - (f + g) y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hd)
        have h : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
          simp only [Pi.add_apply]; abel
        rw [h]; exact norm_add_le _ _
    _ = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
        rw [add_div]
        exact ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ holderSeminorm 0 α f Ω + holderSeminorm 0 α g Ω :=
        add_le_add (le_holderSeminorm_zero α f Ω hx hy hxy)
          (le_holderSeminorm_zero α g Ω hx hy hxy)

/-- `iterDerivNorm 1` is subadditive for functions differentiable within `Ω`. -/
private lemma iterDerivNorm_one_add_le (f g : X → ℂ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω)
    (hf : ∀ x ∈ Ω, DifferentiableWithinAt ℝ f Ω x)
    (hg : ∀ x ∈ Ω, DifferentiableWithinAt ℝ g Ω x) :
    iterDerivNorm 1 (f + g) Ω ≤ iterDerivNorm 1 f Ω + iterDerivNorm 1 g Ω := by
  refine iSup₂_le fun x hx => ?_
  have hx' : UniqueDiffWithinAt ℝ Ω x := hΩ.uniqueDiffWithinAt hx
  rw [norm_iteratedFDerivWithin_one (f + g) hx', fderivWithin_add hx' (hf x hx) (hg x hx)]
  calc ENNReal.ofReal ‖fderivWithin ℝ f Ω x + fderivWithin ℝ g Ω x‖
      ≤ ENNReal.ofReal (‖fderivWithin ℝ f Ω x‖ + ‖fderivWithin ℝ g Ω x‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖fderivWithin ℝ f Ω x‖ + ENNReal.ofReal ‖fderivWithin ℝ g Ω x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ = ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 f Ω x‖
        + ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 g Ω x‖ := by
        rw [← norm_iteratedFDerivWithin_one f hx', ← norm_iteratedFDerivWithin_one g hx']
    _ ≤ iterDerivNorm 1 f Ω + iterDerivNorm 1 g Ω :=
        add_le_add (le_iterDerivNorm 1 f Ω hx) (le_iterDerivNorm 1 g Ω hx)

/-- `holderSeminorm 1` is subadditive for functions differentiable within `Ω`. -/
private lemma holderSeminorm_one_add_le (α : ℝ) (f g : X → ℂ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω)
    (hf : ∀ x ∈ Ω, DifferentiableWithinAt ℝ f Ω x)
    (hg : ∀ x ∈ Ω, DifferentiableWithinAt ℝ g Ω x) :
    holderSeminorm 1 α (f + g) Ω ≤ holderSeminorm 1 α f Ω + holderSeminorm 1 α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hx' : UniqueDiffWithinAt ℝ Ω x := hΩ.uniqueDiffWithinAt hx
  have hy' : UniqueDiffWithinAt ℝ Ω y := hΩ.uniqueDiffWithinAt hy
  rw [Work.CR.Flat.norm_iteratedFDerivWithin_one_sub (f + g) hx' hy',
      fderivWithin_add hx' (hf x hx) (hg x hx),
      fderivWithin_add hy' (hf y hy) (hg y hy)]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  calc ENNReal.ofReal (‖fderivWithin ℝ f Ω x + fderivWithin ℝ g Ω x
          - (fderivWithin ℝ f Ω y + fderivWithin ℝ g Ω y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((‖fderivWithin ℝ f Ω x - fderivWithin ℝ f Ω y‖
          + ‖fderivWithin ℝ g Ω x - fderivWithin ℝ g Ω y‖) / ‖x - y‖ ^ α) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hd)
        have h : fderivWithin ℝ f Ω x + fderivWithin ℝ g Ω x
              - (fderivWithin ℝ f Ω y + fderivWithin ℝ g Ω y)
            = (fderivWithin ℝ f Ω x - fderivWithin ℝ f Ω y)
              + (fderivWithin ℝ g Ω x - fderivWithin ℝ g Ω y) := by abel
        rw [h]; exact norm_add_le _ _
    _ = ENNReal.ofReal (‖fderivWithin ℝ f Ω x - fderivWithin ℝ f Ω y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal (‖fderivWithin ℝ g Ω x - fderivWithin ℝ g Ω y‖ / ‖x - y‖ ^ α) := by
        rw [add_div]
        exact ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ holderSeminorm 1 α f Ω + holderSeminorm 1 α g Ω :=
        add_le_add (le_holderSeminorm_one α f Ω hΩ hx hy hxy)
          (le_holderSeminorm_one α g Ω hΩ hx hy hxy)

/-- The `C^{1,α}` norm unfolded as the sum of its four components. -/
private lemma holderNorm_one_eq (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    holderNorm 1 α f Ω = (iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω)
      + (iterDerivNorm 1 f Ω + holderSeminorm 1 α f Ω) := by
  rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_one]

/-- Subadditivity of the `C^{1,α}` norm, assuming only pointwise differentiability within `Ω`. -/
private lemma holderNorm_one_add_le (α : ℝ) (f g : X → ℂ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω)
    (hf : ∀ x ∈ Ω, DifferentiableWithinAt ℝ f Ω x)
    (hg : ∀ x ∈ Ω, DifferentiableWithinAt ℝ g Ω x) :
    holderNorm 1 α (f + g) Ω ≤ holderNorm 1 α f Ω + holderNorm 1 α g Ω := by
  rw [holderNorm_one_eq, holderNorm_one_eq, holderNorm_one_eq]
  calc (iterDerivNorm 0 (f + g) Ω + holderSeminorm 0 α (f + g) Ω)
        + (iterDerivNorm 1 (f + g) Ω + holderSeminorm 1 α (f + g) Ω)
      ≤ ((iterDerivNorm 0 f Ω + iterDerivNorm 0 g Ω) + (holderSeminorm 0 α f Ω + holderSeminorm 0 α g Ω))
        + ((iterDerivNorm 1 f Ω + iterDerivNorm 1 g Ω) + (holderSeminorm 1 α f Ω + holderSeminorm 1 α g Ω)) :=
        add_le_add (add_le_add (iterDerivNorm_zero_add_le f g Ω) (holderSeminorm_zero_add_le α f g Ω))
          (add_le_add (iterDerivNorm_one_add_le f g Ω hΩ hf hg) (holderSeminorm_one_add_le α f g Ω hΩ hf hg))
    _ = ((iterDerivNorm 0 f Ω + holderSeminorm 0 α f Ω) + (iterDerivNorm 1 f Ω + holderSeminorm 1 α f Ω))
        + ((iterDerivNorm 0 g Ω + holderSeminorm 0 α g Ω) + (iterDerivNorm 1 g Ω + holderSeminorm 1 α g Ω)) := by
        ac_rfl

/-! ## The limit theorem -/

/-- A `C^{1,α}` bound passes to a limit: if a sequence of `C^1` functions is bounded in
the `C^{1,α}` norm, converges pointwise and is Cauchy in the `C^{1,α}` norm, then the limit is
again `C^{1,α}` with the same bound, and the convergence takes place in the `C^{1,α}` norm. -/
theorem holderNorm_one_le_of_tendsto_gen {α : ℝ} {P : Set X} (hP : IsOpen P) {C : ℝ}
    (hC : 0 ≤ C) {F : ℕ → X → ℂ} {v : X → ℂ}
    (hF : ∀ m, ContDiffOn ℝ 1 (F m) P)
    (hbound : ∀ m, holderNorm 1 α (F m) P ≤ ENNReal.ofReal C)
    (hconv : ∀ z ∈ P, Filter.Tendsto (fun m => F m z) Filter.atTop (nhds (v z)))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' →
      holderNorm 1 α (F m - F m') P ≤ ENNReal.ofReal ε) :
    holderNorm 1 α v P ≤ ENNReal.ofReal C ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        holderNorm 1 α (v - F m) P ≤ ENNReal.ofReal ε := by
  have hUD : UniqueDiffOn ℝ P := hP.uniqueDiffOn
  have hFdiff : ∀ m x, x ∈ P → DifferentiableWithinAt ℝ (F m) P x := fun m x hx =>
    ((hF m).contDiffWithinAt hx).differentiableWithinAt one_ne_zero
  have hFd : ∀ m x, x ∈ P → HasFDerivAt (F m) (fderivWithin ℝ (F m) P x) x := by
    intro m x hx
    have hd : DifferentiableWithinAt ℝ (F m) P x := hFdiff m x hx
    rw [fderivWithin_of_isOpen hP hx]
    exact (hd.differentiableAt (hP.mem_nhds hx)).hasFDerivAt
  -- uniform Cauchy of the derivatives
  have hUCD : UniformCauchySeqOn (fun m (x : X) => fderivWithin ℝ (F m) P x) atTop P := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hcau (ε / 2) (by linarith)
    refine ⟨M, fun m hm m' hm' x hx => ?_⟩
    have e : fderivWithin ℝ (F m - F m') P x
        = fderivWithin ℝ (F m) P x - fderivWithin ℝ (F m') P x :=
      fderivWithin_sub (hUD.uniqueDiffWithinAt hx) (hFdiff m x hx) (hFdiff m' x hx)
    have h2 : ENNReal.ofReal ‖fderivWithin ℝ (F m - F m') P x‖ ≤ ENNReal.ofReal (ε / 2) := by
      rw [← norm_iteratedFDerivWithin_one (F m - F m') (hUD.uniqueDiffWithinAt hx)]
      exact le_trans (le_trans (le_iterDerivNorm 1 _ P hx)
        (iterDerivNorm_le_holderNorm 1 α _ P le_rfl)) (hM m m' hm hm')
    have h3 : ‖fderivWithin ℝ (F m - F m') P x‖ ≤ ε / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2
    rw [dist_eq_norm, ← e]
    linarith
  -- uniform Cauchy of the values
  have hUCV : UniformCauchySeqOn (fun m (x : X) => F m x) atTop P := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hcau (ε / 2) (by linarith)
    refine ⟨M, fun m hm m' hm' x hx => ?_⟩
    have h2 : ENNReal.ofReal ‖(F m - F m') x‖ ≤ ENNReal.ofReal (ε / 2) :=
      le_trans (norm_apply_le_holderNorm 1 α (F m - F m') P hx) (hM m m' hm hm')
    have h3 : ‖(F m - F m') x‖ ≤ ε / 2 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2
    rw [dist_eq_norm]
    simpa using lt_of_le_of_lt h3 (by linarith)
  -- the pointwise limit of the derivatives
  have hcauchyD : ∀ x, x ∈ P → CauchySeq (fun m => fderivWithin ℝ (F m) P x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hUCD) ε hε
    exact ⟨N, fun m hm m' hm' => hN m hm m' hm' x hx⟩
  have hexists : ∀ x : X, ∃ y : X →L[ℝ] ℂ,
      x ∈ P → Filter.Tendsto (fun m => fderivWithin ℝ (F m) P x) Filter.atTop (nhds y) := by
    intro x
    by_cases hx : x ∈ P
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hcauchyD x hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose L hL using hexists
  have hTL : TendstoUniformlyOn (fun m (x : X) => fderivWithin ℝ (F m) P x) L atTop P :=
    hUCD.tendstoUniformlyOn_of_tendsto hL
  have hvderiv : ∀ x, x ∈ P → HasFDerivAt v (L x) x := fun x hx =>
    hasFDerivAt_of_tendstoUniformlyOn hP hTL hFd hconv hx
  have hvfw : ∀ x, x ∈ P → fderivWithin ℝ v P x = L x := by
    intro x hx
    rw [fderivWithin_of_isOpen hP hx, (hvderiv x hx).fderiv]
  have hvdiff : ∀ x, x ∈ P → DifferentiableWithinAt ℝ v P x := fun x hx =>
    (hvderiv x hx).differentiableAt.differentiableWithinAt
  -- Part 2: convergence in the `C^{1,α}` norm
  have hpart2 : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      holderNorm 1 α (v - F m) P ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hcau (ε / 4) (by linarith)
    refine ⟨M, fun m hm => ?_⟩
    have hδ0 : 0 ≤ ε / 4 := by linarith
    have hA0 : iterDerivNorm 0 (v - F m) P ≤ ENNReal.ofReal (ε / 4) := by
      rw [iterDerivNorm_zero]
      refine iSup₂_le fun x hx => ?_
      have hnum : Filter.Tendsto (fun m' => ‖(F m' - F m) x‖) Filter.atTop
          (nhds ‖(v - F m) x‖) := by
        have h1 : Filter.Tendsto (fun m' => (F m' - F m) x) Filter.atTop
            (nhds ((v - F m) x)) := by
          have hx' := (hconv x hx).sub (tendsto_const_nhds (x := F m x))
          simpa using hx'
        exact h1.norm
      refine ENNReal.ofReal_le_ofReal (le_of_tendsto hnum ?_)
      filter_upwards [Filter.eventually_ge_atTop M] with m' hm'
      have hb : ENNReal.ofReal ‖(F m' - F m) x‖ ≤ ENNReal.ofReal (ε / 4) :=
        le_trans (norm_apply_le_holderNorm 1 α (F m' - F m) P hx) (hM m' m hm' hm)
      exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp hb
    have hB0 : holderSeminorm 0 α (v - F m) P ≤ ENNReal.ofReal (ε / 4) := by
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub (v - F m) P x y]
      have hnum : Filter.Tendsto (fun m' => ‖(F m' - F m) x - (F m' - F m) y‖) Filter.atTop
          (nhds ‖(v - F m) x - (v - F m) y‖) := by
        have h1 : Filter.Tendsto (fun m' => (F m' - F m) x - (F m' - F m) y) Filter.atTop
            (nhds ((v - F m) x - (v - F m) y)) := by
          have hx' := (hconv x hx).sub (tendsto_const_nhds (x := F m x))
          have hy' := (hconv y hy).sub (tendsto_const_nhds (x := F m y))
          simpa using hx'.sub hy'
        exact h1.norm
      have hdiv := hnum.div_const (‖x - y‖ ^ α)
      refine ENNReal.ofReal_le_ofReal (le_of_tendsto hdiv ?_)
      filter_upwards [Filter.eventually_ge_atTop M] with m' hm'
      have hb : ENNReal.ofReal (‖(F m' - F m) x - (F m' - F m) y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (ε / 4) :=
        le_trans (le_holderSeminorm_zero α (F m' - F m) P hx hy hxy)
          (le_trans (holderSeminorm_le_holderNorm 1 α _ P (Nat.zero_le 1)) (hM m' m hm' hm))
      exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp hb
    have hA1 : iterDerivNorm 1 (v - F m) P ≤ ENNReal.ofReal (ε / 4) := by
      refine iSup₂_le fun x hx => ?_
      rw [norm_iteratedFDerivWithin_one (v - F m) (hUD.uniqueDiffWithinAt hx),
        fderivWithin_sub (hUD.uniqueDiffWithinAt hx) (hvdiff x hx) (hFdiff m x hx),
        hvfw x hx]
      have hnum : Filter.Tendsto
          (fun m' => ‖fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x‖) Filter.atTop
          (nhds ‖L x - fderivWithin ℝ (F m) P x‖) := by
        have h1 : Filter.Tendsto
            (fun m' => fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x) Filter.atTop
            (nhds (L x - fderivWithin ℝ (F m) P x)) :=
          (hL x hx).sub tendsto_const_nhds
        exact h1.norm
      refine ENNReal.ofReal_le_ofReal (le_of_tendsto hnum ?_)
      filter_upwards [Filter.eventually_ge_atTop M] with m' hm'
      have hb : ENNReal.ofReal ‖fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x‖
          ≤ ENNReal.ofReal (ε / 4) := by
        rw [← fderivWithin_sub (hUD.uniqueDiffWithinAt hx) (hFdiff m' x hx) (hFdiff m x hx),
          ← norm_iteratedFDerivWithin_one (F m' - F m) (hUD.uniqueDiffWithinAt hx)]
        exact le_trans (le_trans (le_iterDerivNorm 1 _ P hx)
          (iterDerivNorm_le_holderNorm 1 α _ P le_rfl)) (hM m' m hm' hm)
      exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp hb
    have hB1 : holderSeminorm 1 α (v - F m) P ≤ ENNReal.ofReal (ε / 4) := by
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [Work.CR.Flat.norm_iteratedFDerivWithin_one_sub (v - F m)
            (hUD.uniqueDiffWithinAt hx) (hUD.uniqueDiffWithinAt hy),
        fderivWithin_sub (hUD.uniqueDiffWithinAt hx) (hvdiff x hx) (hFdiff m x hx),
        fderivWithin_sub (hUD.uniqueDiffWithinAt hy) (hvdiff y hy) (hFdiff m y hy),
        hvfw x hx, hvfw y hy]
      have hnum : Filter.Tendsto
          (fun m' => ‖(fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x)
            - (fderivWithin ℝ (F m') P y - fderivWithin ℝ (F m) P y)‖ / ‖x - y‖ ^ α)
          Filter.atTop
          (nhds (‖(L x - fderivWithin ℝ (F m) P x)
            - (L y - fderivWithin ℝ (F m) P y)‖ / ‖x - y‖ ^ α)) := by
        have h1 : Filter.Tendsto
            (fun m' => (fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x)
              - (fderivWithin ℝ (F m') P y - fderivWithin ℝ (F m) P y)) Filter.atTop
            (nhds ((L x - fderivWithin ℝ (F m) P x)
              - (L y - fderivWithin ℝ (F m) P y))) :=
          ((hL x hx).sub tendsto_const_nhds).sub ((hL y hy).sub tendsto_const_nhds)
        exact h1.norm.div_const _
      refine ENNReal.ofReal_le_ofReal (le_of_tendsto hnum ?_)
      filter_upwards [Filter.eventually_ge_atTop M] with m' hm'
      have e : (fderivWithin ℝ (F m') P x - fderivWithin ℝ (F m) P x)
            - (fderivWithin ℝ (F m') P y - fderivWithin ℝ (F m) P y)
          = fderivWithin ℝ (F m' - F m) P x - fderivWithin ℝ (F m' - F m) P y := by
        rw [fderivWithin_sub (hUD.uniqueDiffWithinAt hx) (hFdiff m' x hx) (hFdiff m x hx),
          fderivWithin_sub (hUD.uniqueDiffWithinAt hy) (hFdiff m' y hy) (hFdiff m y hy)]
      rw [e]
      have hb : ENNReal.ofReal (‖fderivWithin ℝ (F m' - F m) P x
            - fderivWithin ℝ (F m' - F m) P y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (ε / 4) :=
        le_trans (le_holderSeminorm_one α (F m' - F m) P hUD hx hy hxy)
          (le_trans (holderSeminorm_le_holderNorm 1 α _ P le_rfl) (hM m' m hm' hm))
      exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp hb
    rw [holderNorm_one_eq]
    calc (iterDerivNorm 0 (v - F m) P + holderSeminorm 0 α (v - F m) P)
          + (iterDerivNorm 1 (v - F m) P + holderSeminorm 1 α (v - F m) P)
        ≤ (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4))
          + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
          add_le_add (add_le_add hA0 hB0) (add_le_add hA1 hB1)
      _ = ENNReal.ofReal ε := by
          have h1 : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
              = ENNReal.ofReal (ε / 2) := by
            rw [← ENNReal.ofReal_add hδ0 hδ0]; congr 1; ring
          rw [h1, ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ ε / 2)
            (by linarith : (0:ℝ) ≤ ε / 2)]
          norm_num
  refine ⟨?_, hpart2⟩
  -- Part 1: the limit satisfies the same bound
  refine ENNReal.le_of_forall_pos_le_add (fun η hη _ => ?_)
  have hη' : 0 < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨M, hM⟩ := hpart2 (η : ℝ) hη'
  have hvm : holderNorm 1 α (v - F M) P ≤ ENNReal.ofReal (η : ℝ) := hM M le_rfl
  have hadd : holderNorm 1 α v P ≤ holderNorm 1 α (v - F M) P + holderNorm 1 α (F M) P := by
    have hfun : v = (v - F M) + F M := by funext z; simp
    calc holderNorm 1 α v P = holderNorm 1 α ((v - F M) + F M) P := by
          conv_lhs => rw [hfun]
      _ ≤ holderNorm 1 α (v - F M) P + holderNorm 1 α (F M) P :=
          holderNorm_one_add_le α (v - F M) (F M) P hUD
            (fun x hx => (hvdiff x hx).sub (hFdiff M x hx)) (hFdiff M)
  calc holderNorm 1 α v P
      ≤ holderNorm 1 α (v - F M) P + holderNorm 1 α (F M) P := hadd
    _ ≤ ENNReal.ofReal (η : ℝ) + ENNReal.ofReal C := add_le_add hvm (hbound M)
    _ = ENNReal.ofReal C + ↑η := by rw [ENNReal.ofReal_coe_nnreal, add_comm]

/-- **The Newlander–Nirenberg `C^{1,α}` completeness lemma.**  A sequence of `C^1` functions on
an open set that is bounded and Cauchy in the `C^{1,α}` norm and converges pointwise has a limit
that is again `C^{1,α}` with the same bound, and the convergence is in the `C^{1,α}` norm. -/
theorem holderNorm_one_le_of_tendsto {n : ℕ} {α : ℝ} {P : Set (Fin n → ℂ)} (hP : IsOpen P) {C : ℝ} (hC : 0 ≤ C) {F : ℕ → (Fin n → ℂ) → ℂ} {v : (Fin n → ℂ) → ℂ} (hF : ∀ m, ContDiffOn ℝ 1 (F m) P) (hbound : ∀ m, Work.CR.Flat.holderNorm 1 α (F m) P ≤ ENNReal.ofReal C) (hconv : ∀ z ∈ P, Filter.Tendsto (fun m => F m z) Filter.atTop (nhds (v z))) (hcau : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' → Work.CR.Flat.holderNorm 1 α (F m - F m') P ≤ ENNReal.ofReal ε) : Work.CR.Flat.holderNorm 1 α v P ≤ ENNReal.ofReal C ∧ ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Work.CR.Flat.holderNorm 1 α (v - F m) P ≤ ENNReal.ofReal ε :=
  holderNorm_one_le_of_tendsto_gen hP hC hF hbound hconv hcau

end Work.NN.Core
