import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.ContinuousMap.contDiff_omega_compContinuousMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Commons.Analysis.ContinuousMap

open scoped Topology ContDiff
open Filter Asymptotics

/-!
# The composition (Nemytskii) operator on spaces of continuous maps

For a compact space `K` and normed spaces `M`, `E` over `ℝ`, and a `C^n` map `F : M → E`,
the operator `g ↦ F ∘ g` on `C(K, M)` is `C^n`.

The proof proceeds by induction on the order of differentiability.  The base case
(`n = 0`) reduces, via compactness of the range of `g`, to uniform continuity of `F`
there.  The inductive step computes the derivative of the operator: it is the composite
of the operator for `fderiv ℝ F` (smooth by the induction hypothesis) with the bounded
linear "currying" map `u ↦ (h ↦ (s ↦ u s (h s)))`.
-/

section Setup

variable {K M E V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The norm of the value at a point is bounded by the sup norm. -/
lemma norm_apply_le_norm_of_continuousMap {α : Type*} {F : Type*} [TopologicalSpace α]
    [CompactSpace α] [NormedAddCommGroup F] (f : C(α, F)) (x : α) : ‖f x‖ ≤ ‖f‖ := by
  have h := ContinuousMap.dist_apply_le_dist (f := f) (g := 0) x
  simpa using h

/-- The pointwise evaluation of a continuous family of continuous linear maps on a continuous
map is continuous. -/
lemma continuous_pointwise_apply {α : Type*} [TopologicalSpace α] {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (u : C(α, F →L[ℝ] G)) (h : C(α, F)) : Continuous fun s : α => u s (h s) :=
  isBoundedBilinearMap_apply.continuous.comp (u.continuous.prodMk h.continuous)

/-- The continuous linear map `h ↦ (s ↦ u s (h s))` from `C(K,M)` to `C(K,V)`, for
`u : C(K, M →L[ℝ] V)`. -/
noncomputable def clmComp (u : C(K, M →L[ℝ] V)) : C(K, M) →L[ℝ] C(K, V) :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨fun s => u s (h s), continuous_pointwise_apply u h⟩
      map_add' := by
        intro h₁ h₂
        ext s
        simp [map_add]
      map_smul' := by
        intro c h
        ext s
        simp [map_smul] }
    ‖u‖ (fun h => by
      refine (ContinuousMap.norm_le
        (f := (⟨fun s => u s (h s), continuous_pointwise_apply u h⟩ : C(K, V)))
        (C := ‖u‖ * ‖h‖) (mul_nonneg (norm_nonneg u) (norm_nonneg h))).2 fun s => ?_
      calc ‖(⟨fun s => u s (h s), continuous_pointwise_apply u h⟩ : C(K, V)) s‖
          = ‖u s (h s)‖ := rfl
        _ ≤ ‖u s‖ * ‖h s‖ := (u s).le_opNorm (h s)
        _ ≤ ‖u‖ * ‖h‖ := by
            gcongr
            · exact norm_apply_le_norm_of_continuousMap u s
            · exact norm_apply_le_norm_of_continuousMap h s)

lemma clmComp_apply (u : C(K, M →L[ℝ] V)) (h : C(K, M)) (s : K) :
    clmComp u h s = u s (h s) := rfl

lemma norm_clmComp_le (u : C(K, M →L[ℝ] V)) : ‖clmComp u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun h => ?_
  show ‖(⟨fun s => u s (h s), continuous_pointwise_apply u h⟩ : C(K, V))‖ ≤ ‖u‖ * ‖h‖
  refine (ContinuousMap.norm_le
    (f := (⟨fun s => u s (h s), continuous_pointwise_apply u h⟩ : C(K, V)))
    (C := ‖u‖ * ‖h‖) (mul_nonneg (norm_nonneg u) (norm_nonneg h))).2 fun s => ?_
  calc ‖(⟨fun s => u s (h s), continuous_pointwise_apply u h⟩ : C(K, V)) s‖
      = ‖u s (h s)‖ := rfl
    _ ≤ ‖u s‖ * ‖h s‖ := (u s).le_opNorm (h s)
    _ ≤ ‖u‖ * ‖h‖ := by
        gcongr
        · exact norm_apply_le_norm_of_continuousMap u s
        · exact norm_apply_le_norm_of_continuousMap h s

/-- The bounded linear "currying" map `u ↦ (h ↦ (s ↦ u s (h s)))`. -/
noncomputable def compCLM : C(K, M →L[ℝ] V) →L[ℝ] (C(K, M) →L[ℝ] C(K, V)) :=
  LinearMap.mkContinuous
    ({ toFun := fun u => clmComp u
       map_add' := by
         intro u₁ u₂
         apply ContinuousLinearMap.ext
         intro h
         apply ContinuousMap.ext
         intro s
         simp [clmComp_apply]
       map_smul' := by
         intro c u
         apply ContinuousLinearMap.ext
         intro h
         apply ContinuousMap.ext
         intro s
         simp [clmComp_apply] } :
      C(K, M →L[ℝ] V) →ₗ[ℝ] (C(K, M) →L[ℝ] C(K, V)))
    (1 : ℝ) (fun u : C(K, M →L[ℝ] V) => by rw [one_mul]; exact norm_clmComp_le u)

lemma compCLM_apply (u : C(K, M →L[ℝ] V)) : compCLM u = clmComp u := by
  rw [compCLM, LinearMap.mkContinuous_apply]
  rfl

end Setup

section Uniform

variable {K M V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Uniform first-order Taylor estimate on a compact set.**  If `q` is differentiable with
continuous derivative, then on a compact set `S` the first-order Taylor remainder is uniformly
bounded by `ε‖z‖`. -/
theorem exists_uniform_fderiv_remainder_le {q : M → V} (hd : Differentiable ℝ q)
    (hc : Continuous (fderiv ℝ q)) {S : Set M} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ z : M, ‖z‖ < δ →
      ‖q (x + z) - q x - fderiv ℝ q x z‖ ≤ ε * ‖z‖ := by
  obtain ⟨η, hη, hη'⟩ : ∃ η > 0, ∀ x ∈ S, ∀ y : M,
      dist x y < η → ‖fderiv ℝ q y - fderiv ℝ q x‖ ≤ ε / 4 := by
    have hr : {p : (M →L[ℝ] V) × (M →L[ℝ] V) | dist p.1 p.2 < ε / 4} ∈
        uniformity (M →L[ℝ] V) :=
      Metric.uniformity_basis_dist.mem_iff.2 ⟨ε / 4, by positivity, subset_rfl⟩
    have h := hS.uniformContinuousAt_of_continuousAt (fderiv ℝ q)
      (fun a _ => hc.continuousAt) hr
    rw [Metric.mem_uniformity_dist] at h
    obtain ⟨η, hη, hηU⟩ := h
    refine ⟨η, hη, fun x hx y hxy => ?_⟩
    have hh : dist (fderiv ℝ q x) (fderiv ℝ q y) < ε / 4 := hηU hxy hx
    rw [dist_eq_norm, norm_sub_rev] at hh
    exact hh.le
  refine ⟨η, hη, fun x hx z hz => ?_⟩
  have hsub : ∀ y ∈ Metric.ball x η, HasFDerivWithinAt (fun y => q y - (fderiv ℝ q x) y)
      (fderiv ℝ q y - fderiv ℝ q x) (Metric.ball x η) y := by
    intro y _
    have h1 : HasFDerivAt q (fderiv ℝ q y) y := (hd y).hasFDerivAt
    exact (h1.sub (fderiv ℝ q x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ Metric.ball x η, ‖fderiv ℝ q y - fderiv ℝ q x‖ ≤ ε / 4 :=
    fun y hy => hη' x hx y (by rw [dist_comm]; exact hy)
  have hmem2 : x + z ∈ Metric.ball x η := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hz
  have hkey := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (𝕜 := ℝ) (f := fun y => q y - (fderiv ℝ q x) y)
    (f' := fun y => fderiv ℝ q y - fderiv ℝ q x) hsub hbound (convex_ball x η)
    (Metric.mem_ball_self hη) hmem2
  have hz' : ε / 4 * ‖(x + z) - x‖ = ε / 4 * ‖z‖ := by rw [add_sub_cancel_left]
  rw [hz'] at hkey
  have heq : q (x + z) - (fderiv ℝ q x) (x + z) - (q x - (fderiv ℝ q x) x)
      = q (x + z) - q x - fderiv ℝ q x z := by
    rw [map_add]
    abel
  rw [heq] at hkey
  calc ‖q (x + z) - q x - fderiv ℝ q x z‖
      ≤ ε / 4 * ‖z‖ := hkey
    _ ≤ ε * ‖z‖ := by
        have : (0:ℝ) < 4 := by norm_num
        nlinarith [norm_nonneg z, hε]

end Uniform

section Deriv

variable {K M V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The derivative of the composition operator.**  The composition operator with a `C¹` map `q`
is differentiable at `g`, with derivative `h ↦ (s ↦ fderiv ℝ q (g s) (h s))`. -/
theorem hasFDerivAt_compContinuousMap {q : M → V} (hd : Differentiable ℝ q)
    (hc : Continuous (fderiv ℝ q)) (g : C(K, M)) :
    HasFDerivAt (fun g' : C(K, M) => (⟨q, hd.continuous⟩ : C(M, V)).comp g')
      (clmComp (⟨fun s => fderiv ℝ q (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] V))) g := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine IsLittleO.of_bound fun c hc0 => ?_
  obtain ⟨δ, hδ, hδ'⟩ :=
    exists_uniform_fderiv_remainder_le hd hc (isCompact_range g.continuous) hc0
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, M)) hδ] with h hh
  have hh' : ‖h‖ < δ := by
    have hmem := hh
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact hmem
  have key : ∀ s : K,
      ‖((⟨q, hd.continuous⟩ : C(M, V)).comp (g + h) - (⟨q, hd.continuous⟩ : C(M, V)).comp g
        - clmComp (⟨fun s => fderiv ℝ q (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] V)) h) s‖
        ≤ c * ‖h‖ := by
    intro s
    have hzs : ‖h s‖ ≤ ‖h‖ := norm_apply_le_norm_of_continuousMap h s
    have hz : ‖h s‖ < δ := lt_of_le_of_lt hzs hh'
    have hval : ((⟨q, hd.continuous⟩ : C(M, V)).comp (g + h)
          - (⟨q, hd.continuous⟩ : C(M, V)).comp g
          - clmComp (⟨fun s => fderiv ℝ q (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] V)) h) s
        = q (g s + h s) - q (g s) - fderiv ℝ q (g s) (h s) := by
      simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.comp_apply,
        clmComp_apply, ContinuousMap.coe_mk]
    rw [hval]
    calc ‖q (g s + h s) - q (g s) - fderiv ℝ q (g s) (h s)‖ ≤ c * ‖h s‖ :=
          hδ' (g s) ⟨s, rfl⟩ (h s) hz
      _ ≤ c * ‖h‖ := by gcongr
  exact (ContinuousMap.norm_le
    (f := ((⟨q, hd.continuous⟩ : C(M, V)).comp (g + h) - (⟨q, hd.continuous⟩ : C(M, V)).comp g
      - clmComp (⟨fun s => fderiv ℝ q (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] V)) h))
    (C := c * ‖h‖) (mul_nonneg hc0.le (norm_nonneg _))).2 key

end Deriv

universe u v w w'

section Main

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]

omit [NormedSpace ℝ M] in
/-- The composition operator with a fixed continuous map is continuous. -/
theorem continuous_compContinuousMap {V : Type*} [PseudoMetricSpace V] (F : C(M, V)) :
    Continuous (fun g : C(K, M) => F.comp g) := by
  rw [Metric.continuous_iff]
  intro g₀ ε hε
  obtain ⟨δ, hδ, hδ'⟩ :
      ∃ δ > 0, ∀ x y : M, dist x y < δ → x ∈ Set.range g₀ → dist (F x) (F y) < ε := by
    have hr : {p : V × V | dist p.1 p.2 < ε} ∈ uniformity V :=
      Metric.uniformity_basis_dist.mem_iff.2 ⟨ε, hε, subset_rfl⟩
    have h := (isCompact_range g₀.continuous).uniformContinuousAt_of_continuousAt F
      (fun a _ => F.continuous.continuousAt) hr
    rw [Metric.mem_uniformity_dist] at h
    obtain ⟨δ, hδ, hδU⟩ := h
    exact ⟨δ, hδ, fun x y hxy hx => hδU hxy hx⟩
  refine ⟨δ, hδ, fun g hg => ?_⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro s
  rw [dist_comm]
  refine hδ' (g₀ s) (g s) ?_ ⟨s, rfl⟩
  calc dist (g₀ s) (g s) ≤ dist g₀ g := ContinuousMap.dist_apply_le_dist s
    _ = dist g g₀ := dist_comm _ _
    _ < δ := hg

/-- The main induction: the composition operator with a `C^k` map is `C^k`, for `k : ℕ`.  The
universe of the target is chosen large enough for the recursive step (in which the target is
replaced by `M →L[ℝ] W`). -/
theorem contDiff_compContinuousMap_nat (k : ℕ) :
    ∀ (W : Type (max u w)) [NormedAddCommGroup W] [NormedSpace ℝ W] (F : M → W)
      (hF : ContDiff ℝ (k : ℕ∞ω) F),
      ContDiff ℝ (k : ℕ∞ω) (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, W)).comp g) := by
  induction k with
  | zero =>
    intro W _ _ F hF
    have h0 : ((0 : ℕ) : ℕ∞ω) = 0 := by norm_num
    refine (contDiff_zero.2 (continuous_compContinuousMap ⟨F, hF.continuous⟩)).of_le ?_
    exact le_of_eq h0
  | succ k ih =>
    intro W _ _ F hF
    have hgoal : ((k + 1 : ℕ) : ℕ∞ω) = ((k : ℕ) : ℕ∞ω) + 1 := by norm_num
    have hF' : ContDiff ℝ (((k : ℕ) : ℕ∞ω) + 1) F := hF.of_le (le_of_eq hgoal.symm)
    have hderiv : ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fderiv ℝ F) := hF'.fderiv_right le_rfl
    have hc : Continuous (fderiv ℝ F) := hderiv.continuous
    have hd : Differentiable ℝ F := hF'.differentiable (by simp)
    have hΨ : ContDiff ℝ ((k : ℕ) : ℕ∞ω)
        (fun g : C(K, M) =>
          (⟨fderiv ℝ F, hc⟩ : C(M, M →L[ℝ] W)).comp g) :=
      ih (M →L[ℝ] W) (fderiv ℝ F) hderiv
    have hDfun : ContDiff ℝ ((k : ℕ) : ℕ∞ω)
        (fun g : C(K, M) =>
          clmComp (⟨fun s => fderiv ℝ F (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] W))) := by
      have hCLM : ContDiff ℝ ((k : ℕ) : ℕ∞ω)
          (fun u : C(K, M →L[ℝ] W) => compCLM u) :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(K, M →L[ℝ] W))
          (F := (C(K, M) →L[ℝ] C(K, W))) (n := ((k : ℕ) : ℕ∞ω)) compCLM
      have h1 : ContDiff ℝ ((k : ℕ) : ℕ∞ω)
          (fun g : C(K, M) =>
            compCLM ((⟨fderiv ℝ F, hc⟩ : C(M, M →L[ℝ] W)).comp g)) :=
        hCLM.comp hΨ
      have h2 : (fun g : C(K, M) => compCLM ((⟨fderiv ℝ F, hc⟩ : C(M, M →L[ℝ] W)).comp g))
          = fun g : C(K, M) =>
              clmComp (⟨fun s => fderiv ℝ F (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] W)) := by
        funext g
        rw [compCLM_apply]
        have hcomp : (⟨fderiv ℝ F, hc⟩ : C(M, M →L[ℝ] W)).comp g
            = (⟨fun s => fderiv ℝ F (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] W)) := by
          ext s
          rfl
        rw [hcomp]
      rw [h2] at h1
      exact h1
    have hD : ∀ g : C(K, M),
        HasFDerivAt (fun g' : C(K, M) => (⟨F, hF.continuous⟩ : C(M, W)).comp g')
          (clmComp (⟨fun s => fderiv ℝ F (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] W))) g :=
      fun g => hasFDerivAt_compContinuousMap hd hc g
    have hmain : ContDiff ℝ (((k : ℕ) : ℕ∞ω) + 1)
        (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, W)).comp g) := by
      refine (contDiff_succ_iff_fderiv (n := ((k : ℕ) : ℕ∞ω)) (f := (fun g : C(K, M) =>
        (⟨F, hF.continuous⟩ : C(M, W)).comp g))).2 ⟨?_, ?_, ?_⟩
      · exact fun g => (hD g).differentiableAt
      · intro hk
        exact absurd hk (by simp)
      · have hfeq : fderiv ℝ (fun g' : C(K, M) => (⟨F, hF.continuous⟩ : C(M, W)).comp g')
            = fun g : C(K, M) =>
                clmComp (⟨fun s => fderiv ℝ F (g s), hc.comp g.continuous⟩ : C(K, M →L[ℝ] W)) := by
          funext g
          exact (hD g).fderiv
        rw [hfeq]
        exact hDfun
    exact hmain.of_le (le_of_eq hgoal)

end Main

section Final

open scoped Topology ContDiff

/-- `ULift.up` as a continuous linear map into a universe that contains the source universe. -/
noncomputable def uliftUpCLM (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →L[ℝ] ULift.{u, w} E :=
  LinearMap.mkContinuous
    { toFun := ULift.up
      map_add' := fun x y => ULift.ext (by simp [ULift.add_down])
      map_smul' := fun c x => ULift.ext (by simp [ULift.smul_down]) }
    1 (fun x => by
      show ‖x‖ ≤ 1 * ‖x‖
      rw [one_mul])

/-- `ULift.down` as a continuous linear map. -/
noncomputable def uliftDownCLM (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ULift.{u, w} E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := ULift.down
      map_add' := fun x y => by simp [ULift.add_down]
      map_smul' := fun c x => by simp [ULift.smul_down] }
    1 (fun x => by
      show ‖x‖ ≤ 1 * ‖x‖
      rw [one_mul])

lemma uliftUpCLM_apply (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) x = ULift.up x := rfl

lemma uliftDownCLM_apply (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ULift.{u, w} E) :
    (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E) x = ULift.down x := rfl

lemma uliftDownCLM_upCLM (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E)
      ((uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) x) = x := by
  rw [uliftUpCLM_apply, uliftDownCLM_apply, ULift.down_up]

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a `C^n` map `F` becomes `C^n` after composing with a continuous linear map `up` that has a
continuous linear left inverse `down`, then the composition operator with `F` is `C^n`.  This lets
one move to a larger universe in which the inductive proof of the main theorem applies. -/
theorem contDiff_compContinuousMap_of_lift {E' : Type w'} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {up : E →L[ℝ] E'} {down : E' →L[ℝ] E} (hup : ∀ x, down (up x) = x)
    {n : ℕ∞ω} {F : M → E} (hFc : Continuous F)
    (h : ContDiff ℝ n (fun g : C(K, M) =>
          (⟨fun x : M => up (F x), up.continuous.comp hFc⟩ : C(M, E')).comp g)) :
    ContDiff ℝ n (fun g : C(K, M) => (⟨F, hFc⟩ : C(M, E)).comp g) := by
  have hΨ : ContDiff ℝ n
      (fun u : C(K, E') => clmComp (K := K) (M := E') (V := E)
        (⟨fun _ : K => down, continuous_const⟩ : C(K, E' →L[ℝ] E)) u) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(K, E')) (F := C(K, E)) (n := n)
      (clmComp (K := K) (M := E') (V := E)
        (⟨fun _ : K => down, continuous_const⟩ : C(K, E' →L[ℝ] E)))
  have hcomp := hΨ.comp h
  convert hcomp using 1
  funext g
  ext s
  exact (hup (F (g s))).symm

/-- Auxiliary form of the main theorem, with explicit universes. -/
theorem contDiff_compContinuousMap_univ {n : ℕ∞ω} {F : M → E} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, E)).comp g) := by
  match n with
  | ω => exact contDiff_omega_compContinuousMap hF
  | (n : ℕ∞) =>
    rw [contDiff_iff_forall_nat_le]
    intro m hm
    have hmF : ContDiff ℝ ((m : ℕ) : ℕ∞ω) F := hF.of_le (by exact_mod_cast hm)
    have hFl : ContDiff ℝ ((m : ℕ) : ℕ∞ω)
        (fun x : M => (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) (F x)) :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E) (F := ULift.{u, w} E)
        (n := ((m : ℕ) : ℕ∞ω)) (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E)).comp hmF
    have hΦ' : ContDiff ℝ ((m : ℕ) : ℕ∞ω)
        (fun g : C(K, M) =>
          (⟨fun x : M => (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) (F x), hFl.continuous⟩ :
            C(M, ULift.{u, w} E)).comp g) :=
      contDiff_compContinuousMap_nat.{u, v, w} (K := K) (M := M) m (ULift.{u, w} E)
        (fun x : M => (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E) (F x)) hFl
    exact contDiff_compContinuousMap_of_lift (up := (uliftUpCLM E : E →L[ℝ] ULift.{u, w} E))
      (down := (uliftDownCLM E : ULift.{u, w} E →L[ℝ] E)) (uliftDownCLM_upCLM.{u, w} E)
      hF.continuous hΦ'

/-- **Composition with a `C^n` map is `C^n` on the Banach space `C(K,M)`.**

For a compact space `K` and a fixed `C^n` map `F : M → E` between real normed spaces, the
composition operator `g ↦ F ∘ g` on `C(K, M)` is `C^n`. -/
theorem contDiff_compContinuousMap {K M E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {F : M → E} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun g : C(K, M) => (⟨F, hF.continuous⟩ : C(M, E)).comp g) :=
  contDiff_compContinuousMap_univ hF

end Final