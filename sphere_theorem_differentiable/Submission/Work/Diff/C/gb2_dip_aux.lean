import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliaries for the "dip" branch of `Work.Diff.C.gram_bad_case2`

This module collects the elementary (analysis-only) lemmas that the bad-index / dip branch of
`Work.Diff.C.gram_bad_case2` needs, so that the main file can be assembled without re-deriving them.

* `rgrad_eq_zero_of_eventuallyEq_const` — the gradient of a function that is locally constant at a
  point vanishes there;
* `deriv_eq_zero_of_le_const` / `deriv_eq_one_of_ge_id` — the one-sided values of `deriv ψ` at the
  two thresholds of the cutoff `ψ` (which is constant below `-1+c` and the identity above `-1+2c`);
* `exists_isLeast_of_Icc_le` / `exists_isGreatest_of_Icc_le` — the first and the last time at which a
  continuous real function on `[a,b]` is `≤ A`;
* `abs_sub_le_of_tendsto_left` — the "model comparison at a first exit time" limiting step: if the
  comparison `|g t - m t| ≤ ε t` holds on `[a,T)` and `g, m` are continuous at `T`, then it holds at
  `T` as well.
-/

namespace Work.Diff.C

open Bundle ContDiff Set
open scoped Manifold ContDiff Bundle Topology

section Rgrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **The gradient of a locally constant function vanishes.** -/
theorem rgrad_eq_zero_of_eventuallyEq_const {F : M → ℝ} {a : ℝ} {x : M}
    (h : F =ᶠ[𝓝 x] fun _ => a) : rgrad (I := I) F x = 0 := by
  have hm : mfderiv I (𝓘(ℝ, ℝ)) F x = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq h, mfderiv_const]
    ext v
    simp
  rw [rgrad, hm]
  exact map_zero _

end Rgrad

section Deriv

/-- **Left value of `deriv ψ` at a point below which `ψ` is constant.** -/
theorem deriv_eq_zero_of_le_const {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h : ∀ t : ℝ, t ≤ a → ψ t = a) : deriv ψ a = 0 := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] a] deriv ψ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h1 : ψ =ᶠ[𝓝 t] (fun _ => a) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact h s (le_of_lt hs)
    rw [h1.deriv_eq]
    exact (deriv_const t a).symm
  have htend : Filter.Tendsto (deriv ψ) (𝓝[<] a) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' hev
  have h2 : Filter.Tendsto (deriv ψ) (𝓝[<] a) (𝓝 (deriv ψ a)) :=
    hcont.continuousAt.mono_left inf_le_left
  exact tendsto_nhds_unique h2 htend

/-- **Right value of `deriv ψ` at a point above which `ψ` is the identity.** -/
theorem deriv_eq_one_of_ge_id {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h : ∀ t : ℝ, a ≤ t → ψ t = t) : deriv ψ a = 1 := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hev : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝[>] a] deriv ψ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h1 : ψ =ᶠ[𝓝 t] (fun s => s) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact h s (le_of_lt hs)
    rw [h1.deriv_eq]
    simp
  have htend : Filter.Tendsto (deriv ψ) (𝓝[>] a) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds.congr' hev
  have h2 : Filter.Tendsto (deriv ψ) (𝓝[>] a) (𝓝 (deriv ψ a)) :=
    hcont.continuousAt.mono_left inf_le_left
  exact tendsto_nhds_unique h2 htend

end Deriv

section Times

/-- **First time.**  A continuous function which is `≤ A` somewhere on `[a,b]` is `≤ A` at a first
such time. -/
theorem exists_isLeast_of_Icc_le {g : ℝ → ℝ} (hg : Continuous g) {a b A : ℝ}
    (hne : ∃ t ∈ Set.Icc a b, g t ≤ A) :
    ∃ T : ℝ, T ∈ Set.Icc a b ∧ g T ≤ A ∧ ∀ t ∈ Set.Icc a b, g t ≤ A → T ≤ t := by
  have hK : IsCompact (Set.Icc a b ∩ {t : ℝ | g t ≤ A}) :=
    isCompact_Icc.inter_right (isClosed_le hg continuous_const)
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨T, hT, hmin⟩ := hK.exists_isMinOn ⟨t₀, ht₀.1, ht₀.2⟩ continuousOn_id
  exact ⟨T, hT.1, hT.2, fun t ht hlt => hmin ⟨ht, hlt⟩⟩

/-- **Last time.**  A continuous function which is `≤ A` somewhere on `[a,b]` is `≤ A` at a last such
time. -/
theorem exists_isGreatest_of_Icc_le {g : ℝ → ℝ} (hg : Continuous g) {a b A : ℝ}
    (hne : ∃ t ∈ Set.Icc a b, g t ≤ A) :
    ∃ T : ℝ, T ∈ Set.Icc a b ∧ g T ≤ A ∧ ∀ t ∈ Set.Icc a b, g t ≤ A → t ≤ T := by
  have hK : IsCompact (Set.Icc a b ∩ {t : ℝ | g t ≤ A}) :=
    isCompact_Icc.inter_right (isClosed_le hg continuous_const)
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨T, hT, hmax⟩ := hK.exists_isMaxOn ⟨t₀, ht₀.1, ht₀.2⟩ continuousOn_id
  exact ⟨T, hT.1, hT.2, fun t ht hlt => hmax ⟨ht, hlt⟩⟩

/-- **The comparison at a first exit time.**  If `|g t - m t| ≤ ε t` for all `t ∈ [a,T)` and both
`g` and `m` are continuous at `T`, then the same inequality holds at `T`. -/
theorem abs_sub_le_of_tendsto_left {g m : ℝ → ℝ} {a T ε : ℝ} (ha : a < T)
    (hg : ContinuousAt g T) (hm : ContinuousAt m T)
    (h : ∀ t : ℝ, t ∈ Set.Ioo a T → |g t - m t| ≤ ε * t) :
    |g T - m T| ≤ ε * T := by
  have hT : Filter.Tendsto (fun t : ℝ => |g t - m t|) (𝓝[<] T) (𝓝 |g T - m T|) :=
    ((hg.sub hm).abs).mono_left inf_le_left
  have hε : Filter.Tendsto (fun t : ℝ => ε * t) (𝓝[<] T) (𝓝 (ε * T)) :=
    ((continuous_const.mul continuous_id).continuousAt).tendsto.mono_left inf_le_left
  refine le_of_tendsto_of_tendsto hT hε ?_
  have h1 : Set.Ioi a ∈ 𝓝[<] T := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ha)
  have h2 : Set.Iio T ∈ 𝓝[<] T := self_mem_nhdsWithin
  have h3 : Set.Ioo a T ∈ 𝓝[<] T := Filter.inter_mem h1 h2
  filter_upwards [h3] with t ht
  exact h t ht

end Times

end Work.Diff.C
