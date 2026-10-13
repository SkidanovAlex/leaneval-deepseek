import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.norm_sub_le_of_step_bound
import Submission.Work.CoreResiduals.exists_holder_bound_of_lipschitzOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **The compactness step of the local-to-strip reduction.**

Let a family of functions `f y : ℝ → E` (`y` ranging over an *arbitrary* type `X`, so that the
constants below are uniform in `y`) be *locally* Lipschitz in `t` at every point of `[a,b]`, with
one neighbourhood `(t₀ - ε, t₀ + ε)` and one constant `N` per point `t₀`, the same for all `y`.
Then there are a *single* `δ > 0` and a *single* `N` such that every pair `t, t' ∈ [a,b]` at
distance `< δ` satisfies the Lipschitz bound, uniformly in `y`.

This is the classical argument: the neighbourhoods `(t₀ - ε t₀, t₀ + ε t₀)` for `t₀ ∈ [a,b]` are
an open cover of the compact interval `[a,b]`, hence have a finite subcover
(`IsCompact.elim_finite_subcover`); the Lebesgue number of that *finite* cover
(`lebesgue_number_lemma_of_metric`) gives `δ > 0` such that every ball `ball t δ` with
`t ∈ [a,b]` lies inside one member of the cover; and the constants of the finitely many members
are bounded by `max 1 (N i₁)`, the maximum of the finitely many chosen `N i`
(`Finset.exists_max_image`).  The finiteness of the cover is what makes the constant uniform —
the `N` of a single point of the infinite cover would depend on the pair `(t, t')` and would not
telescope. -/
theorem exists_step_bound_of_locallyLipschitz {X E : Type*} [NormedAddCommGroup E]
    {f : X → ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t - ε) (t + ε), ∀ t'' ∈ Set.Ioo (t - ε) (t + ε), ∀ y : X,
        ‖f y t' - f y t''‖ ≤ N * |t' - t''|) :
    ∃ (δ : ℝ) (N : ℝ), 0 < δ ∧ ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, |t - t'| < δ →
      ∀ y : X, ‖f y t - f y t'‖ ≤ N * |t - t'| := by
  classical
  -- the local data, chosen at every point of the compact interval
  have hloc' : ∀ t : Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t.1 - ε) (t.1 + ε), ∀ t'' ∈ Set.Ioo (t.1 - ε) (t.1 + ε), ∀ y : X,
        ‖f y t' - f y t''‖ ≤ N * |t' - t''| := fun t => hloc t t.2
  choose ε hε N hN using hloc'
  -- these neighbourhoods cover `[a,b]`
  have hcover : Set.Icc a b ⊆ ⋃ i : Set.Icc a b, Set.Ioo (i.1 - ε i) (i.1 + ε i) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ⟨by linarith [hε ⟨t, ht⟩], by linarith [hε ⟨t, ht⟩]⟩⟩
  -- compactness: a finite subcover
  obtain ⟨tfin, htfin⟩ := isCompact_Icc.elim_finite_subcover
    (fun i : Set.Icc a b => Set.Ioo (i.1 - ε i) (i.1 + ε i)) (fun _ => isOpen_Ioo) hcover
  set c : {i // i ∈ tfin} → Set ℝ := fun i => Set.Ioo (i.1.1 - ε i.1) (i.1.1 + ε i.1) with hc
  have hcopen : ∀ i, IsOpen (c i) := fun i => isOpen_Ioo
  have hccover : Set.Icc a b ⊆ ⋃ i, c i := by
    intro t ht
    obtain ⟨i, hit, hti⟩ := Set.mem_iUnion₂.1 (htfin ht)
    exact Set.mem_iUnion.2 ⟨⟨i, hit⟩, hti⟩
  -- the Lebesgue number of the finite cover
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := Set.Icc a b) (c := c)
    isCompact_Icc hcopen hccover
  -- the index finset is nonempty because `[a,b]` is
  have hne : tfin.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.1 (htfin ⟨le_rfl, hab⟩)
    exact ⟨i, hi⟩
  -- the largest of the finitely many constants
  obtain ⟨i₁, hit₁, hi₁max⟩ := Finset.exists_max_image tfin N hne
  refine ⟨δ, max 1 (N i₁), hδpos, fun t ht t' ht' hd y => ?_⟩
  -- `ball t δ` lies in one member of the cover, and `t'` is in that ball
  obtain ⟨i, hi⟩ := hδ t ht
  have ht_mem : t ∈ c i := hi (by rw [Metric.mem_ball]; simp [hδpos])
  have ht'_mem : t' ∈ c i := by
    refine hi ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact hd
  exact (hN i.1 t ht_mem t' ht'_mem y).trans
    (mul_le_mul_of_nonneg_right (le_trans (hi₁max i.1 i.2) (le_max_right _ _)) (abs_nonneg _))

/-- The local Lipschitzness in `t` of the slices of `∂ₜω` (on the half-window) gives the *strip*
form of the second-order time-regularity of the R2 bundle: on the compact strip `[0,S]`,
`S < T`, a finite subcover of `preWindow P.T` by the local neighbourhoods of
`Work.CoreResiduals.TimeDerivLocallyLipschitz` yields a single Lipschitz constant `N` valid for all
`t, t' ∈ Icc 0 S` and all `y`; and a Lipschitz function is `α`-Hölder of every exponent `α ≤ 1` on
a bounded interval (`h ≤ h^α` for `0 ≤ h ≤ 1`, and `h ≤ S ≤ S·h^α` for `1 ≤ h ≤ S`), so a suitable
constant witnesses `Work.CoreResiduals.TimeDerivStripHolder α (solVort P) S`.  The exponent bound
`α ≤ 1` is derived internally from `P.hα13`. -/
theorem timeDerivStripHolder_of_locallyLipschitz {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α)
    (hlip : Work.CoreResiduals.TimeDerivLocallyLipschitz
      (Work.ConstructionInstance.solVort P) P.T)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.TimeDerivStripHolder α (Work.ConstructionInstance.solVort P) S := by
  -- the exponent range `α ≤ 1` of the profile data
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [P.hα13]
  have h0S : (0 : ℝ) ≤ S := le_of_lt hS
  -- the half-window contains the strip, so the local data is available at every `t ∈ Icc 0 S`
  have hloc : ∀ t ∈ Set.Icc (0 : ℝ) S, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t - ε) (t + ε), ∀ t'' ∈ Set.Ioo (t - ε) (t + ε), ∀ y : R3,
        ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t'
          - FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t''‖
          ≤ N * |t' - t''| := by
    intro t ht
    exact hlip t ⟨by linarith [ht.1], by linarith [ht.2, hST]⟩
  -- a single step size `δ` and a single constant `K` for the strip
  obtain ⟨δ, K, hδpos, hstep⟩ := exists_step_bound_of_locallyLipschitz (a := 0) (b := S)
    (f := fun y t => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t)
    h0S hloc
  -- chaining the steps: global Lipschitzness on the strip
  have hglob : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S, ∀ y : R3,
      ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t
        - FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t'‖
        ≤ K * |t - t'| :=
    norm_sub_le_of_step_bound hδpos hstep
  -- Lipschitzness gives `α`-Hölder regularity on the bounded interval
  obtain ⟨N₁, hN₁⟩ := exists_holder_bound_of_lipschitzOn (S := S) (K := max 1 K) (α := α)
    (f := fun y t => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t)
    h0S (le_trans zero_le_one (le_max_left (1 : ℝ) K)) hα1
    (fun t ht t' ht' y => (hglob t ht t' ht' y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
  exact ⟨N₁, fun y t ht t' ht' => hN₁ y t ht t' ht'⟩

end Work.CoreResiduals
