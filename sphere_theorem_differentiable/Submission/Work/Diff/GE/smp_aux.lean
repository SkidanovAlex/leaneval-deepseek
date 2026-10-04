import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.smp_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tools for the scalar maximum principle

The scalar maximum principle (`Work.Diff.GE.scalar_max_principle`) is proved by the classical
barrier argument.  This module contains the tools it needs:

* `smpBarrier`, the barrier `v(t,x) = e^{-C₁t} u(t,x) - (max B 0 + C₂ t + ε (1+t))`;
* `nonneg_of_hasDerivWithinAt_Ico`, the one-sided sign rule at a maximum taken from the left;
* `contMDiff_slice_of_contMDiffOn`, which turns joint smoothness into smoothness of the slices;
* `exists_barrier_max`, which produces the positive maximum of the barrier on the box
  `[0,t] × M` (this is where the compactness of `M` is used).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The barrier of the scalar maximum principle:
`v(t,x) = u(t,x) * exp (-(C₁ * t)) - (M0 + C₂ * t + ε * (1 + t))`. -/
noncomputable def smpBarrier (u : ℝ → M → ℝ) (C₁ C₂ M0 ε : ℝ) : ℝ × M → ℝ :=
  fun p => u p.1 p.2 * Real.exp (-(C₁ * p.1)) - (M0 + C₂ * p.1 + ε * (1 + p.1))

/-- If `f` has a maximum at `t₀` when approached from the left along `[0, t₀)` and its one-sided
derivative at `t₀` (within `[0, t₀)`) is `D`, then `0 ≤ D`: the derivative is a limit of
nonnegative slopes. -/
theorem nonneg_of_hasDerivWithinAt_Ico {f : ℝ → ℝ} {D t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : HasDerivWithinAt f D (Ico 0 t₀) t₀) (hm : ∀ s ∈ Ico 0 t₀, f s ≤ f t₀) : 0 ≤ D := by
  have hset : Ico 0 t₀ \ {t₀} = Ico 0 t₀ := by
    ext a
    constructor
    · intro ha; exact ha.1
    · intro ha; exact ⟨ha, ne_of_lt (mem_Ico.mp ha).2⟩
  have hcl : t₀ ∈ closure (Ico 0 t₀) := by
    rw [closure_Ico (by linarith : (0 : ℝ) ≠ t₀)]
    exact ⟨le_of_lt ht₀, le_rfl⟩
  haveI : NeBot (𝓝[Ico 0 t₀ \ {t₀}] t₀) := by
    rw [hset]
    exact mem_closure_iff_nhdsWithin_neBot.mp hcl
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  have h2 : Tendsto (fun s => - slope f t₀ s) (𝓝[Ico 0 t₀ \ {t₀}] t₀) (𝓝 (-D)) := h.neg
  have h3 : ∀ᶠ s in 𝓝[Ico 0 t₀ \ {t₀}] t₀, - slope f t₀ s ≤ 0 := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro s hs
    have hs1 : s ∈ Ico 0 t₀ := hs.1
    have hslt : s < t₀ := (mem_Ico.mp hs1).2
    have h1 : (s - t₀)⁻¹ ≤ 0 := inv_nonpos.mpr (sub_nonpos.mpr hslt.le)
    have h2' : f s - f t₀ ≤ 0 := sub_nonpos.mpr (hm s hs1)
    have hsl : 0 ≤ slope f t₀ s := by
      rw [slope_def_field]
      exact mul_nonneg_of_nonpos_of_nonpos h2' h1
    exact neg_nonpos.mpr hsl
  exact neg_nonpos.mp (le_of_tendsto h2 h3)

/-- A slice of a jointly smooth function of `(t,x)` is smooth on `M`. -/
theorem contMDiff_slice_of_contMDiffOn {u : ℝ → M → ℝ} {T t : ℝ} (ht : t ∈ Ico 0 T)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ univ)) : CMDiff ∞ (u t) := by
  have h1 : ContMDiffOn I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M ↦ (t, x)) univ :=
    ContMDiffOn.prodMk contMDiffOn_const contMDiffOn_id
  have h2 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M ↦ u t x) univ :=
    hu.comp h1 (by intro y hy; simp only [mem_preimage]; exact ⟨ht, mem_univ y⟩)
  exact contMDiffOn_univ.mp h2

/-! ### Derivative bookkeeping

Because `ℝ → ℝ` carries several definitionally distinct ways of spelling its algebraic
structure, the raw outputs of `HasDerivAt.add`, `HasDerivAt.mul`, ... do not unify with the
lambdas one writes down.  The two transfer lemmas below are the cheap way around that. -/

/-- Transfer a `HasDerivAt` statement to a pointwise-equal function and an equal derivative. -/
theorem hasDerivAt_congr_fun {f g : ℝ → ℝ} {D D' x : ℝ} (h : HasDerivAt f D x) (hD : D = D')
    (hfg : ∀ a, g a = f a) : HasDerivAt g D' x := by
  rw [← hD]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

/-- Transfer a `HasDerivWithinAt` statement to a pointwise-equal function and an equal
derivative. -/
theorem hasDerivWithinAt_congr_fun {f g : ℝ → ℝ} {D D' x : ℝ} {s : Set ℝ}
    (h : HasDerivWithinAt f D s x) (hD : D = D') (hfg : ∀ a, g a = f a) :
    HasDerivWithinAt g D' s x := by
  rw [← hD]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg) (hfg x)

/-- The derivative of `a ↦ exp (-(C₁ a))`. -/
theorem hasDerivAt_exp_neg_mul (C₁ t₀ : ℝ) :
    HasDerivAt (fun a : ℝ => Real.exp (-(C₁ * a))) (-(C₁ * Real.exp (-(C₁ * t₀)))) t₀ := by
  have h2 : HasDerivAt (fun a : ℝ => -(C₁ * a)) (-C₁) t₀ := by
    refine hasDerivAt_congr_fun (hasDerivAt_const_mul (-C₁) (x := t₀)) rfl (fun a => ?_)
    simp
  have h3 := h2.exp
  have h4 : Real.exp (-(C₁ * t₀)) * (-C₁) = -(C₁ * Real.exp (-(C₁ * t₀))) := by ring
  rw [h4] at h3
  exact h3

/-- The derivative of the affine part of the barrier `a ↦ max B 0 + C₂ a + ε (1 + a)`. -/
theorem hasDerivAt_affine_barrier (B C₂ ε t₀ : ℝ) :
    HasDerivAt (fun a : ℝ => max B 0 + C₂ * a + ε * (1 + a)) (C₂ + ε) t₀ := by
  have hA : HasDerivAt (fun _ : ℝ => max B 0) 0 t₀ := hasDerivAt_const t₀ _
  have hB : HasDerivAt (fun a : ℝ => C₂ * a) C₂ t₀ := hasDerivAt_const_mul C₂ (x := t₀)
  have hC : HasDerivAt (fun a : ℝ => ε * (1 + a)) ε t₀ := by
    have h1 : HasDerivAt (fun a : ℝ => (1 : ℝ) + a) 1 t₀ := by
      refine hasDerivAt_congr_fun ((hasDerivAt_const t₀ (1 : ℝ)).add (hasDerivAt_id t₀))
        (by ring) (fun a => ?_)
      simp [Pi.add_apply]
    refine hasDerivAt_congr_fun (h1.const_mul ε) (by ring) (fun a => ?_)
    simp
  refine hasDerivAt_congr_fun ((hA.add hB).add hC) (by ring) (fun a => ?_)
  simp [Pi.add_apply]

section Box

variable [T2Space M] [CompactSpace M]

/-- If the barrier `v` is positive at `(t,x)` with `t ∈ [0,T)` and `u 0 ≤ B`, then `v` attains a
positive maximum on the box `[0,t] × M` at a point `(t₀,x₀)` with `0 < t₀ < T`; there `u t₀`
attains its maximum on `M`, which is `≥ 0`, and the slice `u t₀` is smooth.  Moreover the barrier
stays below its value at `(t₀,x₀)` along `[0,t₀) × {x₀}`, which is what the one-sided sign rule
`nonneg_of_hasDerivWithinAt_Ico` consumes. -/
theorem exists_barrier_max (u : ℝ → M → ℝ) {T t C₁ C₂ B ε : ℝ}
    (hC₂ : 0 ≤ C₂) (hε : 0 < ε) (ht : t ∈ Ico 0 T) (hinit : ∀ x, u 0 x ≤ B)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ univ))
    {x : M} (hpos : 0 < smpBarrier u C₁ C₂ (max B 0) ε (t, x)) :
    ∃ t₀ x₀, 0 < t₀ ∧ t₀ < T ∧ 0 ≤ u t₀ x₀ ∧ (∀ y, u t₀ y ≤ u t₀ x₀) ∧ CMDiff ∞ (u t₀) ∧
      (∀ s ∈ Ico 0 t₀, smpBarrier u C₁ C₂ (max B 0) ε (s, x₀)
        ≤ smpBarrier u C₁ C₂ (max B 0) ε (t₀, x₀)) := by
  have ht' : 0 ≤ t ∧ t < T := mem_Ico.mp ht
  have hM0nn : 0 ≤ max B 0 := le_max_right _ _
  have hBM0 : B ≤ max B 0 := le_max_left _ _
  set K : Set (ℝ × M) := Icc 0 t ×ˢ (univ : Set M) with hK
  have hKsub : K ⊆ Ico 0 T ×ˢ univ := by
    intro p hp
    rw [hK] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : 0 ≤ p.1 ∧ p.1 ≤ t := mem_Icc.mp hp1
    exact ⟨⟨hp1'.1, lt_of_le_of_lt hp1'.2 ht'.2⟩, mem_univ p.2⟩
  have hKcomp : IsCompact K := by rw [hK]; exact isCompact_Icc.prod isCompact_univ
  have hKne : K.Nonempty := ⟨(t, x), by rw [hK]; exact ⟨⟨ht'.1, le_rfl⟩, mem_univ x⟩⟩
  have hcontu : ContinuousOn (fun p : ℝ × M ↦ u p.1 p.2) K := (hu.mono hKsub).continuousOn
  have hcontV : ContinuousOn (fun p : ℝ × M ↦ smpBarrier u C₁ C₂ (max B 0) ε p) K := by
    simp only [smpBarrier]
    refine hcontu.mul ?_ |>.sub ?_
    · exact (Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul continuous_fst).neg.continuousOn)).mono (subset_refl K)
    · exact (((continuous_const.add (continuous_fst.const_mul C₂)).add
        (continuous_const.mul (continuous_const.add continuous_fst)))).continuousOn.mono
        (subset_refl K)
  obtain ⟨p₀, hp₀K, hmaxV⟩ := hKcomp.exists_isMaxOn hKne hcontV
  obtain ⟨t₀, x₀⟩ := p₀
  have hp₀ : t₀ ∈ Icc 0 t ∧ x₀ ∈ (univ : Set M) := by
    rw [hK] at hp₀K; exact hp₀K
  have ht₀ge : 0 ≤ t₀ := (mem_Icc.mp hp₀.1).1
  have ht₀le : t₀ ≤ t := (mem_Icc.mp hp₀.1).2
  have ht₀T : t₀ < T := lt_of_le_of_lt ht₀le ht'.2
  have hVt₀pos : 0 < smpBarrier u C₁ C₂ (max B 0) ε (t₀, x₀) :=
    lt_of_lt_of_le hpos (hmaxV (by rw [hK]; exact ⟨⟨ht'.1, le_rfl⟩, mem_univ x⟩))
  have hspatial : ∀ y : M,
      smpBarrier u C₁ C₂ (max B 0) ε (t₀, y) ≤ smpBarrier u C₁ C₂ (max B 0) ε (t₀, x₀) :=
    fun y => hmaxV (by rw [hK]; exact ⟨⟨ht₀ge, ht₀le⟩, mem_univ y⟩)
  have h0lt : smpBarrier u C₁ C₂ (max B 0) ε (0, x₀) < 0 := by
    simp only [smpBarrier, mul_zero, neg_zero, Real.exp_zero]
    have h1 := hinit x₀
    linarith [hBM0, hε]
  have ht₀pos : 0 < t₀ := by
    by_contra h
    rw [not_lt] at h
    have h0 : t₀ = 0 := le_antisymm h ht₀ge
    rw [h0] at hVt₀pos
    exact absurd hVt₀pos (not_lt.mpr h0lt.le)
  have hVexp : 0 < Real.exp (-(C₁ * t₀)) * u t₀ x₀ := by
    simp only [smpBarrier] at hVt₀pos
    have h1 : 0 ≤ C₂ * t₀ := mul_nonneg hC₂ ht₀ge
    have h2 : 0 < ε * (1 + t₀) := mul_pos hε (by linarith)
    linarith
  have hU : 0 ≤ u t₀ x₀ := by
    have := (mul_pos_iff_of_pos_left (Real.exp_pos (-(C₁ * t₀)))).mp hVexp
    linarith
  have hmaxu : ∀ y : M, u t₀ y ≤ u t₀ x₀ := by
    intro y
    have h := hspatial y
    simp only [smpBarrier] at h
    have h1 : u t₀ y * Real.exp (-(C₁ * t₀)) ≤ u t₀ x₀ * Real.exp (-(C₁ * t₀)) := by linarith
    exact (mul_le_mul_iff_of_pos_right (Real.exp_pos (-(C₁ * t₀)))).mp h1
  refine ⟨t₀, x₀, ht₀pos, ht₀T, hU, hmaxu, contMDiff_slice_of_contMDiffOn ⟨ht₀ge, ht₀T⟩ hu, ?_⟩
  intro s hs
  have hmem : (s, x₀) ∈ K := by
    rw [hK]
    refine ⟨⟨hs.1, ?_⟩, mem_univ x₀⟩
    exact le_trans hs.2.le ht₀le
  exact hmaxV hmem

end Box

end Work.Diff.GE
