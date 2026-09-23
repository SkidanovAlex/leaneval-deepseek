import Mathlib
import Submission.Commons.Analysis.ContinuousMap.contDiff_compContinuousMap

namespace Commons.Analysis.ContinuousMap

open scoped _root_.ContDiff Topology
open Set Filter
open Asymptotics

/-! ### A localized uniform Taylor estimate -/

section LocalTaylor

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- **Localized uniform first-order Taylor estimate.** If `q` is differentiable on an open set
`W` with continuous derivative there, then on a compact subset `S ⊆ W` the first-order Taylor
remainder is uniformly bounded by `ε‖z‖` for small `z`. -/
theorem exists_uniform_fderiv_remainder_le_local {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {q : M → V} {W : Set M} (hW : IsOpen W) (hd : DifferentiableOn ℝ q W)
    (hc : ContinuousOn (fderiv ℝ q) W) {S : Set M} (hS : IsCompact S) (hSW : S ⊆ W) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ z : M, ‖z‖ < δ →
      ‖q (x + z) - q x - fderiv ℝ q x z‖ ≤ ε * ‖z‖ := by
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hS.exists_thickening_subset_open hW hSW
  obtain ⟨η, hη, hη'⟩ : ∃ η > 0, ∀ x ∈ S, ∀ y : M,
      dist x y < η → ‖fderiv ℝ q y - fderiv ℝ q x‖ ≤ ε / 4 := by
    have hr : {p : (M →L[ℝ] V) × (M →L[ℝ] V) | dist p.1 p.2 < ε / 4} ∈
        uniformity (M →L[ℝ] V) :=
      Metric.uniformity_basis_dist.mem_iff.2 ⟨ε / 4, by positivity, subset_rfl⟩
    have h := hS.uniformContinuousAt_of_continuousAt (fderiv ℝ q)
      (fun a ha => hc.continuousAt (hW.mem_nhds (hSW ha))) hr
    rw [Metric.mem_uniformity_dist] at h
    obtain ⟨η, hη, hηU⟩ := h
    refine ⟨η, hη, fun x hx y hxy => ?_⟩
    have hh : dist (fderiv ℝ q x) (fderiv ℝ q y) < ε / 4 := hηU hxy hx
    rw [dist_eq_norm, norm_sub_rev] at hh
    exact hh.le
  refine ⟨min η δ₁, lt_min hη hδ₁, fun x hx z hz => ?_⟩
  have hle_η : min η δ₁ ≤ η := min_le_left _ _
  have hle_δ₁ : min η δ₁ ≤ δ₁ := min_le_right _ _
  have hsub : ∀ y ∈ Metric.ball x (min η δ₁),
      HasFDerivWithinAt (fun y => q y - (fderiv ℝ q x) y)
        (fderiv ℝ q y - fderiv ℝ q x) (Metric.ball x (min η δ₁)) y := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hthick : y ∈ Metric.thickening δ₁ S := by
      rw [Metric.mem_thickening_iff]
      exact ⟨x, hx, by rw [dist_eq_norm]; exact lt_of_lt_of_le hy hle_δ₁⟩
    have hyW : y ∈ W := hδ₁' hthick
    have h1 : HasFDerivAt q (fderiv ℝ q y) y :=
      (hd.differentiableAt (hW.mem_nhds hyW)).hasFDerivAt
    exact (h1.sub (fderiv ℝ q x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ Metric.ball x (min η δ₁),
      ‖fderiv ℝ q y - fderiv ℝ q x‖ ≤ ε / 4 := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hη' x hx y (by rw [dist_eq_norm, norm_sub_rev]; exact lt_of_lt_of_le hy hle_η)
  have hmem2 : x + z ∈ Metric.ball x (min η δ₁) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hz
  have hkey := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (𝕜 := ℝ) (f := fun y => q y - (fderiv ℝ q x) y)
    (f' := fun y => fderiv ℝ q y - fderiv ℝ q x) hsub hbound (convex_ball x (min η δ₁))
    (Metric.mem_ball_self (lt_min hη hδ₁)) hmem2
  have hz' : ε / 4 * ‖(x + z) - x‖ = ε / 4 * ‖z‖ := by rw [add_sub_cancel_left]
  rw [hz'] at hkey
  have heq : q (x + z) - (fderiv ℝ q x) (x + z) - (q x - (fderiv ℝ q x) x)
      = q (x + z) - q x - fderiv ℝ q x z := by
    rw [map_add]
    abel
  rw [heq] at hkey
  calc ‖q (x + z) - q x - fderiv ℝ q x z‖
      ≤ ε / 4 * ‖z‖ := hkey
    _ ≤ ε * ‖z‖ := by nlinarith [norm_nonneg z, hε]

end LocalTaylor

/-! ### The localized composition operator -/

section Nem

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The localized Nemytskii (composition) operator: on the set of `g` whose image lies in `W` it
is `g ↦ F ∘ g`; outside it is defined arbitrarily (as `0`). -/
noncomputable def nem (W : Set M) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : M → E) : C(K, M) → C(K, E) :=
  fun g => by
    classical
    exact if h : (∀ s : K, g s ∈ W) ∧ Continuous (fun s : K => F (g s)) then
      ⟨fun s => F (g s), h.2⟩
    else 0

lemma nem_apply (W : Set M) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : M → E} {g : C(K, M)} (h : ∀ s : K, g s ∈ W)
    (hc : Continuous fun s : K => F (g s)) (s : K) : nem W F g s = F (g s) := by
  unfold nem
  rw [dif_pos ⟨h, hc⟩]
  rfl

/-- **Derivative of the localized composition operator.** If `F` is differentiable on the open
set `W` with continuous derivative there, then `g ↦ F ∘ g` is differentiable at every `g₀` whose
range lies in `W`, with derivative `h ↦ (s ↦ DF(g₀ s)(h s))`. -/
theorem hasFDerivAt_nem (W : Set M) (hW : IsOpen W) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : M → E} (hd : DifferentiableOn ℝ F W)
    (hc : ContinuousOn (fderiv ℝ F) W) (hcF : ContinuousOn F W)
    (g₀ : C(K, M)) (hg₀ : ∀ s : K, g₀ s ∈ W) :
    HasFDerivAt (nem W F)
      (clmComp (⟨fun s => fderiv ℝ F (g₀ s),
        hc.comp_continuous g₀.continuous hg₀⟩ : C(K, M →L[ℝ] E))) g₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine IsLittleO.of_bound fun c hc0 => ?_
  have hS : IsCompact (Set.range g₀) := isCompact_range g₀.continuous
  have hSW : Set.range g₀ ⊆ W := by rintro _ ⟨s, rfl⟩; exact hg₀ s
  obtain ⟨δ, hδ, hδ'⟩ := exists_uniform_fderiv_remainder_le_local hW hd hc hS hSW hc0
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hS.exists_thickening_subset_open hW hSW
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, M)) (lt_min hδ hδ₁)] with h hh
  have hnorm : ‖h‖ < min δ δ₁ := by
    rw [Metric.mem_ball, dist_zero_right] at hh; exact hh
  have hltδ : ‖h‖ < δ := lt_of_lt_of_le hnorm (min_le_left _ _)
  have hltδ₁ : ‖h‖ < δ₁ := lt_of_lt_of_le hnorm (min_le_right _ _)
  have hrange : ∀ s : K, (g₀ + h) s ∈ W := by
    intro s
    refine hδ₁' ?_
    rw [Metric.mem_thickening_iff]
    exact ⟨g₀ s, ⟨s, rfl⟩, by
      rw [ContinuousMap.add_apply, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_le_of_lt (norm_apply_le_norm_of_continuousMap h s) hltδ₁⟩
  have hkey : ∀ s : K,
      ‖((nem W F (g₀ + h) - nem W F g₀
        - clmComp (⟨fun s => fderiv ℝ F (g₀ s),
            hc.comp_continuous g₀.continuous hg₀⟩ : C(K, M →L[ℝ] E)) h)) s‖ ≤ c * ‖h‖ := by
    intro s
    have hzs : ‖h s‖ ≤ ‖h‖ := norm_apply_le_norm_of_continuousMap h s
    have hz : ‖h s‖ < δ := lt_of_le_of_lt hzs hltδ
    have hv1 : nem W F (g₀ + h) s = F ((g₀ + h) s) := by
      unfold nem
      rw [dif_pos ⟨hrange, hcF.comp_continuous (g₀ + h).continuous hrange⟩]
      rfl
    have hv2 : nem W F g₀ s = F (g₀ s) := by
      unfold nem
      rw [dif_pos ⟨hg₀, hcF.comp_continuous g₀.continuous hg₀⟩]
      rfl
    have hv3 : (clmComp (⟨fun s => fderiv ℝ F (g₀ s),
        hc.comp_continuous g₀.continuous hg₀⟩ : C(K, M →L[ℝ] E)) h) s
        = fderiv ℝ F (g₀ s) (h s) := clmComp_apply _ h s
    have hval : ((nem W F (g₀ + h) - nem W F g₀
        - clmComp (⟨fun s => fderiv ℝ F (g₀ s),
            hc.comp_continuous g₀.continuous hg₀⟩ : C(K, M →L[ℝ] E)) h)) s
        = F (g₀ s + h s) - F (g₀ s) - fderiv ℝ F (g₀ s) (h s) := by
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hv1, hv2, hv3,
        ContinuousMap.add_apply]
    rw [hval]
    calc ‖F (g₀ s + h s) - F (g₀ s) - fderiv ℝ F (g₀ s) (h s)‖ ≤ c * ‖h s‖ :=
          hδ' (g₀ s) ⟨s, rfl⟩ (h s) hz
      _ ≤ c * ‖h‖ := by gcongr
  exact (ContinuousMap.norm_le
    (f := (nem W F (g₀ + h) - nem W F g₀
      - clmComp (⟨fun s => fderiv ℝ F (g₀ s),
          hc.comp_continuous g₀.continuous hg₀⟩ : C(K, M →L[ℝ] E)) h))
    (C := c * ‖h‖) (mul_nonneg hc0.le (norm_nonneg _))).2 hkey

/-- The set of continuous maps whose image lies in `W` is open, for `W` open. -/
theorem isOpen_nem (W : Set M) (hW : IsOpen W) :
    IsOpen {g : C(K, M) | ∀ s : K, g s ∈ W} := by
  rw [Metric.isOpen_iff]
  intro g₀ hg₀
  have hSW : Set.range g₀ ⊆ W := by rintro _ ⟨s, rfl⟩; exact hg₀ s
  obtain ⟨δ, hδ, hδ'⟩ := (isCompact_range g₀.continuous).exists_thickening_subset_open hW hSW
  refine ⟨δ, hδ, fun g hg => ?_⟩
  intro s
  refine hδ' ?_
  rw [Metric.mem_thickening_iff]
  exact ⟨g₀ s, ⟨s, rfl⟩, lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist s) hg⟩

/-- Base case: if `F` is continuous on the open set `W`, then `g ↦ F ∘ g` is continuous on `U`. -/
theorem continuousOn_nem (W : Set M) (hW : IsOpen W) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : M → E} (hF : ContinuousOn F W) :
    ContinuousOn (nem W F) {g : C(K, M) | ∀ s : K, g s ∈ W} := by
  intro g₀ hg₀
  have hSW : Set.range g₀ ⊆ W := by rintro _ ⟨s, rfl⟩; exact hg₀ s
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ > 0, ∀ x y : M, dist x y < δ →
      x ∈ Set.range g₀ → dist (F x) (F y) < ε := by
    have hr : {p : E × E | dist p.1 p.2 < ε} ∈ uniformity E :=
      Metric.uniformity_basis_dist.mem_iff.2 ⟨ε, hε, subset_rfl⟩
    have h := (isCompact_range g₀.continuous).uniformContinuousAt_of_continuousAt F
      (fun a ha => hF.continuousAt (hW.mem_nhds (hSW ha))) hr
    rw [Metric.mem_uniformity_dist] at h
    obtain ⟨δ, hδ, hδU⟩ := h
    exact ⟨δ, hδ, fun x y hxy hx => hδU hxy hx⟩
  refine ⟨δ, hδ, fun g hgU hgd => ?_⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro s
  rw [nem_apply W hgU (hF.comp_continuous g.continuous hgU) s,
    nem_apply W hg₀ (hF.comp_continuous g₀.continuous hg₀) s, dist_comm]
  exact hδ' (g₀ s) (g s)
    (lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist s) (by rwa [dist_comm] at hgd)) ⟨s, rfl⟩

end Nem

/-! ### Induction on the differentiability order -/

universe u v w

section Induction

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]

set_option maxHeartbeats 2000000 in
/-- **Localized Nemytskii smoothness, finite order.** If `F` is `C^k` on the open set `W`, then
the composition operator `g ↦ F ∘ g` is `C^k` on the open set of those `g` whose range lies in
`W`. -/
theorem nem_contDiffOn_nat (k : ℕ) :
    ∀ (E : Type (max u w)) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (W : Set M) (hW : IsOpen W) (F : M → E) (hF : ContDiffOn ℝ (k : ℕ∞ω) F W),
      ContDiffOn ℝ (k : ℕ∞ω) (nem W F) {g : C(K, M) | ∀ s : K, g s ∈ W} := by
  induction k with
  | zero =>
    intro E _ _ W hW F hF
    have h0 : ((0 : ℕ) : ℕ∞ω) = 0 := by norm_num
    rw [h0, contDiffOn_zero]
    exact continuousOn_nem W hW hF.continuousOn
  | succ k ih =>
    intro E _ _ W hW F hF
    have hgoal : ((k + 1 : ℕ) : ℕ∞ω) = ((k : ℕ) : ℕ∞ω) + 1 := by norm_num
    rw [hgoal]
    have hF' : ContDiffOn ℝ (((k : ℕ) : ℕ∞ω) + 1) F W := hF
    have hU : IsOpen {g : C(K, M) | ∀ s : K, g s ∈ W} := isOpen_nem W hW
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := nem W F) hU]
    have hd : DifferentiableOn ℝ F W := hF'.differentiableOn (by simp)
    have hc' : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (fderiv ℝ F) W :=
      hF'.fderiv_of_isOpen hW le_rfl
    have hc : ContinuousOn (fderiv ℝ F) W := hc'.continuousOn
    have hcF : ContinuousOn F W := hF'.continuousOn
    refine ⟨?_, ?_, ?_⟩
    · intro g₀ hg₀
      exact (hasFDerivAt_nem W hW hd hc hcF g₀ hg₀).differentiableAt.differentiableWithinAt
    · intro hk
      exact absurd hk (by simp)
    · have hIH : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (nem W (fderiv ℝ F))
          {g : C(K, M) | ∀ s : K, g s ∈ W} := ih (M →L[ℝ] E) W hW (fderiv ℝ F) hc'
      have hfin : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω)
          (fun g : C(K, M) => compCLM (K := K) (M := M) (V := E)
            (nem W (fderiv ℝ F) g)) {g : C(K, M) | ∀ s : K, g s ∈ W} := by
        have h := ContDiffOn.continuousLinearMap_comp
          (compCLM (K := K) (M := M) (V := E)) hIH
        simpa only [Function.comp_def] using h
      refine hfin.congr fun g hg => ?_
      have h1 : fderiv ℝ (nem W F) g = clmComp (⟨fun s => fderiv ℝ F (g s),
          hc.comp_continuous g.continuous hg⟩ : C(K, M →L[ℝ] E)) :=
        (hasFDerivAt_nem W hW hd hc hcF g hg).fderiv
      have h2 : nem W (fderiv ℝ F) g = (⟨fun s => fderiv ℝ F (g s),
          hc.comp_continuous g.continuous hg⟩ : C(K, M →L[ℝ] E)) := by
        unfold nem
        rw [dif_pos ⟨hg, hc.comp_continuous g.continuous hg⟩]
      rw [h1, compCLM_apply, h2]

end Induction

/-! ### Lifting the target to a large enough universe -/

section Final

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Localized Nemytskii smoothness.** If `F` is `C^∞` on the open set `W`, then the
composition operator `g ↦ F ∘ g` is `C^∞` on the open set of those `g` whose range lies in `W`. -/
theorem nem_contDiffOn_univ {W : Set M} (hW : IsOpen W) {F : M → E}
    (hF : ContDiffOn ℝ ∞ F W) :
    ContDiffOn ℝ ∞ (nem W F) {g : C(K, M) | ∀ s : K, g s ∈ W} := by
  rw [contDiffOn_infty]
  intro k
  set Fl : M → ULift.{u, w} E := fun x => ULift.up (F x) with hFl
  have hFl' : ContDiffOn ℝ ∞ Fl W := by
    have h := ContDiffOn.continuousLinearMap_comp
      (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) hF
    rw [hFl]
    simpa only [Function.comp_def, uliftUpCLM_apply] using h
  have hFl_cont : ContinuousOn Fl W := hFl'.continuousOn
  have hnem : ContDiffOn ℝ (k : ℕ∞ω) (nem W Fl)
      {g : C(K, M) | ∀ s : K, g s ∈ W} :=
    nem_contDiffOn_nat k (ULift.{u, w} E) W hW Fl (hFl'.of_le (by exact_mod_cast le_top : ((k : ℕ) : ℕ∞ω) ≤ ∞))
  have hLd : (fun v : C(K, ULift.{u, w} E) => clmComp (K := K) (M := ULift.{u, w} E) (V := E)
        (⟨fun _ : K => (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E), continuous_const⟩ :
          C(K, ULift.{u, w} E →L[ℝ] E)) v)
      = (clmComp (K := K) (M := ULift.{u, w} E) (V := E)
        (⟨fun _ : K => (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E), continuous_const⟩ :
          C(K, ULift.{u, w} E →L[ℝ] E))) := rfl
  have hfin : ContDiffOn ℝ (k : ℕ∞ω)
      (fun g : C(K, M) => clmComp (K := K) (M := ULift.{u, w} E) (V := E)
        (⟨fun _ : K => (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E), continuous_const⟩ :
          C(K, ULift.{u, w} E →L[ℝ] E)) (nem W Fl g))
      {g : C(K, M) | ∀ s : K, g s ∈ W} := by
    have h := ContDiffOn.continuousLinearMap_comp
      (clmComp (K := K) (M := ULift.{u, w} E) (V := E)
        (⟨fun _ : K => (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E), continuous_const⟩ :
          C(K, ULift.{u, w} E →L[ℝ] E))) hnem
    simpa only [Function.comp_def] using h
  refine hfin.congr fun g _ => ?_
  ext s
  rw [clmComp_apply]
  by_cases h : ∀ s : K, g s ∈ W
  · have e1 : nem W Fl g s = Fl (g s) := by
      unfold nem
      rw [dif_pos ⟨h, hFl_cont.comp_continuous g.continuous h⟩]
      rfl
    have e2 : nem W F g s = F (g s) := by
      unfold nem
      rw [dif_pos ⟨h, hF.continuousOn.comp_continuous g.continuous h⟩]
      rfl
    rw [e1, e2, hFl]
    simp only [ContinuousMap.coe_mk, uliftDownCLM_apply]
  · have e1 : nem W Fl g = 0 := by
      unfold nem
      rw [dif_neg (fun hc => h hc.1)]
    have e2 : nem W F g = 0 := by
      unfold nem
      rw [dif_neg (fun hc => h hc.1)]
    rw [e1, e2]
    simp

end Final

open scoped _root_.ContDiff

/-- **Localized Nemytskii (composition) operator smoothness.**  If `F : M → E` is `C^∞` on an open
set `W ⊆ M`, then the composition operator `g ↦ F ∘ g` on `C(K, M)` is `C^∞` on the open set of
those `g` whose image lies in `W`. -/
theorem exists_contDiffOn_nemitskii {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set M} (hW : IsOpen W) {F : M → E} (hF : ContDiffOn ℝ ∞ F W) :
    ∃ Φ : C(K, M) → C(K, E),
      (∀ g, (∀ s : K, g s ∈ W) → ∀ s : K, Φ g s = F (g s)) ∧
      ContDiffOn ℝ ∞ Φ {g : C(K, M) | ∀ s : K, g s ∈ W} := by
  refine ⟨nem W F, fun g hg s => nem_apply W hg (hF.continuousOn.comp_continuous g.continuous hg) s,
    nem_contDiffOn_univ (K := K) (M := M) (E := E) hW hF⟩

end Commons.Analysis.ContinuousMap
