import Mathlib

set_option autoImplicit false

/-!
# Smoothness of the composition operator on spaces of continuous maps

For a `C^n` map `f : E → F` between normed spaces and a compact space `K`, the map
`u ↦ f ∘ u` on the Banach space `C(K, E)` of continuous maps is `C^n`.  We prove this by
induction: the derivative is pointwise application of `fderiv f`, which is again a composition
operator, followed by the (smooth) evaluation pairing of continuous maps.
-/

open scoped Topology NNReal ContDiff
open Set Function Pointwise

namespace Work.RPCore.Port.ODE

universe u

section Basic

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition with `f`, as an operator on spaces of continuous maps. -/
noncomputable def compCM (f : E → F) (hf : Continuous f) : C(K, E) → C(K, F) :=
  fun u => ⟨fun t => f (u t), hf.comp u.continuous⟩

@[simp]
lemma compCM_apply (f : E → F) (hf : Continuous f) (u : C(K, E)) (t : K) :
    compCM f hf u t = f (u t) := rfl

lemma continuous_compCM [ProperSpace E] [ProperSpace F] {f : E → F} (hf : Continuous f) :
    Continuous (compCM (K := K) f hf) := by
  rw [Metric.continuous_iff]
  intro u₀ ε hε
  have hS : IsCompact (Set.range u₀ ∪ (Set.range u₀ + Metric.closedBall (0 : E) 1)) :=
    (isCompact_range u₀.continuous).union
      ((isCompact_range u₀.continuous).add (isCompact_closedBall 0 1))
  have hunif : UniformContinuousOn f
      (Set.range u₀ ∪ (Set.range u₀ + Metric.closedBall (0 : E) 1)) :=
    hS.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨η, hηpos, hη⟩ := hunif ε hε
  refine ⟨min η 1, lt_min hηpos zero_lt_one, fun u hu => ?_⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  have hu₀ : u₀ t ∈ Set.range u₀ ∪ (Set.range u₀ + Metric.closedBall (0 : E) 1) :=
    Or.inl ⟨t, rfl⟩
  have hut : u t ∈ Set.range u₀ ∪ (Set.range u₀ + Metric.closedBall (0 : E) 1) := by
    refine Or.inr ⟨u₀ t, ⟨t, rfl⟩, u t - u₀ t, ?_, by abel⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖u t - u₀ t‖ = ‖(u - u₀) t‖ := rfl
      _ ≤ ‖u - u₀‖ := ContinuousMap.norm_coe_le_norm (u - u₀) t
      _ = dist u u₀ := by rw [dist_eq_norm]
      _ ≤ min η 1 := le_of_lt hu
      _ ≤ 1 := min_le_right _ _
  have hd : dist (u t) (u₀ t) < η := by
    have h1 : dist (u t) (u₀ t) ≤ dist u u₀ := by
      rw [dist_eq_norm, dist_eq_norm]
      exact ContinuousMap.norm_coe_le_norm (u - u₀) t
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hu (min_le_left _ _))
  exact hη (u t) hut (u₀ t) hu₀ hd

end Basic

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Uniform Taylor estimate.**  For a `C¹` map and a compact set `S`, the first order Taylor
remainder is uniformly `o(‖y - x‖)` for `x, y ∈ S`. -/
lemma norm_sub_fderiv_le_of_isCompact [ProperSpace E] {f : E → F} (hf : ContDiff ℝ 1 f)
    {S : Set E} (hS : IsCompact S) :
    ∀ ε > 0, ∃ η > 0, ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ η →
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  obtain ⟨η₀, hη₀pos, hη₀⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      ((hS.add (isCompact_closedBall (0 : E) 1)).uniformContinuousOn_of_continuous
        ((hf.continuous_fderiv (by norm_num)).continuousOn))) ε hε
  refine ⟨min (η₀ / 2) 1, lt_min_iff.mpr ⟨by linarith, zero_lt_one⟩,
    fun x hx y hy hxy => ?_⟩
  have hηpos : (0:ℝ) < min (η₀ / 2) 1 := lt_min_iff.mpr ⟨by linarith, zero_lt_one⟩
  have hηle : min (η₀ / 2) 1 ≤ 1 := min_le_right _ _
  have hηlt : min (η₀ / 2) 1 < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- every point of the ball around `x` of radius `η` lies in the compact set
  have hball : Metric.closedBall x (min (η₀ / 2) 1) ⊆ S + Metric.closedBall (0 : E) 1 := by
    intro z hz
    have hzx : ‖z - x‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact le_trans (Metric.mem_closedBall.mp hz) hηle
    refine ⟨x, hx, z - x, ?_, ?_⟩
    · rwa [Metric.mem_closedBall, dist_zero_right]
    · show x + (z - x) = z
      abel_nf
  have hbound : ∀ z ∈ Metric.closedBall x (min (η₀ / 2) 1),
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε := by
    intro z hz
    have hxT : x ∈ S + Metric.closedBall (0 : E) 1 :=
      ⟨x, hx, 0, by simp [Metric.mem_closedBall], by simp⟩
    have hzx : dist z x < η₀ := lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hηlt
    have h := hη₀ z (hball hz) x hxT hzx
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
    (f := f) (s := Metric.closedBall x (min (η₀ / 2) 1)) (f' := fun z => fderiv ℝ f z)
    (φ := fderiv ℝ f x) (C := ε)
    (fun z _ => ((hf.differentiable (by norm_num) z).hasFDerivAt).hasFDerivWithinAt)
    hbound (convex_closedBall x _) (Metric.mem_closedBall_self (le_of_lt hηpos))
    (by rw [Metric.mem_closedBall]; exact hxy)
  exact this

end Taylor

section Eval

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise evaluation pairing of continuous maps. -/
noncomputable def evalBilin : C(K, E →L[ℝ] F) × C(K, E) → C(K, F) :=
  fun p => ⟨fun t => p.1 t (p.2 t), p.1.continuous.clm_apply p.2.continuous⟩

@[simp]
lemma evalBilin_apply (g : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    evalBilin (g, u) t = g t (u t) := rfl

lemma evalBilin_bound (x : C(K, E →L[ℝ] F)) (y : C(K, E)) :
    ‖evalBilin (K := K) (x, y)‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  calc ‖evalBilin (x, y) t‖ = ‖x t (y t)‖ := rfl
    _ ≤ ‖x t‖ * ‖y t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖x‖ * ‖y‖ := by
        apply mul_le_mul
        · exact ContinuousMap.norm_coe_le_norm x t
        · exact ContinuousMap.norm_coe_le_norm y t
        · positivity
        · positivity
    _ = 1 * ‖x‖ * ‖y‖ := by rw [one_mul]

lemma isBoundedBilinearMap_evalBilin :
    IsBoundedBilinearMap ℝ (evalBilin (K := K) (E := E) (F := F)) :=
  { add_left := fun x y z => by ext t; simp
    smul_left := fun c x y => by ext t; simp
    add_right := fun x y z => by ext t; simp
    smul_right := fun c x y => by ext t; simp
    bound := ⟨1, one_pos, evalBilin_bound⟩ }

lemma contDiff_evalBilin (n : ℕ∞ω) : ContDiff ℝ n (evalBilin (K := K) (E := E) (F := F)) :=
  isBoundedBilinearMap_evalBilin.contDiff

end Eval



section Deriv

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ProperSpace E] [ProperSpace F]

/-- Pointwise evaluation *as a linear map* in the second argument. -/
noncomputable def evalLM (g : C(K, E →L[ℝ] F)) : C(K, E) →ₗ[ℝ] C(K, F) where
  toFun u := ⟨fun t => g t (u t), g.continuous.clm_apply u.continuous⟩
  map_add' a b := by ext t; simp [ContinuousLinearMap.map_add]
  map_smul' c a := by ext t; simp [ContinuousLinearMap.map_smul]

@[simp]
lemma evalLM_apply (g : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    evalLM g u t = g t (u t) := rfl

lemma norm_evalLM_le (g : C(K, E →L[ℝ] F)) (u : C(K, E)) : ‖evalLM g u‖ ≤ ‖g‖ * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  calc ‖g t (u t)‖ ≤ ‖g t‖ * ‖u t‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖g‖ * ‖u‖ := by
        apply mul_le_mul
        · exact ContinuousMap.norm_coe_le_norm g t
        · exact ContinuousMap.norm_coe_le_norm u t
        · positivity
        · positivity

/-- Evaluation of a continuous family of linear maps on a continuous map, as a bounded linear map
in the second argument. -/
noncomputable def evalCLM (g : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  (evalLM g).mkContinuous ‖g‖ (norm_evalLM_le g)

@[simp]
lemma evalCLM_apply (g : C(K, E →L[ℝ] F)) (u : C(K, E)) (t : K) :
    evalCLM g u t = g t (u t) := rfl

lemma evalCLM_eq_evalBilin (g : C(K, E →L[ℝ] F)) (u : C(K, E)) :
    evalCLM g u = evalBilin (g, u) := rfl

lemma norm_evalCLM_le (g : C(K, E →L[ℝ] F)) : ‖evalCLM g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le (f := evalLM g) (C := ‖g‖) (norm_nonneg g) (norm_evalLM_le g)

/-- `evalCLM` depends boundedly-linearly on its first argument. -/
lemma isBoundedLinearMap_evalCLM :
    IsBoundedLinearMap ℝ (fun g : C(K, E →L[ℝ] F) => evalCLM g) where
  map_add := by
    intro g₁ g₂
    refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
    simp [ContinuousLinearMap.add_apply]
  map_smul := by
    intro c g
    refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
    simp
  bound := ⟨1, one_pos, fun g => by rw [one_mul]; exact norm_evalCLM_le g⟩

lemma contDiff_evalCLMₗ (n : ℕ∞ω) :
    ContDiff ℝ n (fun g : C(K, E →L[ℝ] F) => evalCLM g) :=
  isBoundedLinearMap_evalCLM.contDiff

/-- The candidate derivative of `compCM f` at `u`. -/
noncomputable def derivCLM (f : E → F) (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    C(K, E) →L[ℝ] C(K, F) :=
  evalCLM (compCM (fderiv ℝ f) (hf.continuous_fderiv (by norm_num)) u)

lemma hasFDerivAt_compCM {f : E → F} (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    HasFDerivAt (compCM (K := K) f hf.continuous) (derivCLM f hf u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨η, hηpos, hη⟩ := norm_sub_fderiv_le_of_isCompact (f := f) hf
    ((isCompact_range u.continuous).add (isCompact_closedBall (0 : E) 1)) c hc
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) (lt_min_iff.mpr ⟨hηpos, zero_lt_one⟩)]
    with h hh
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have ht : u t + h t ∈ Set.range u + Metric.closedBall (0 : E) 1 := by
    refine ⟨u t, ⟨t, rfl⟩, h t, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖h t‖ ≤ ‖h‖ := ContinuousMap.norm_coe_le_norm h t
      _ ≤ min η 1 := le_of_lt hh
      _ ≤ 1 := min_le_right _ _
  have htu : u t ∈ Set.range u + Metric.closedBall (0 : E) 1 :=
    ⟨u t, ⟨t, rfl⟩, 0, by simp [Metric.mem_closedBall], by simp⟩
  have hd : dist (u t + h t) (u t) ≤ η := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact le_of_lt (lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm h t)
      (lt_of_lt_of_le hh (min_le_left _ _)))
  have hmain := hη (u t) htu (u t + h t) ht hd
  rw [add_sub_cancel_left] at hmain
  have hle : c * ‖h t‖ ≤ c * ‖h‖ :=
    mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm h t) (le_of_lt hc)
  calc ‖(compCM f hf.continuous (u + h) - compCM f hf.continuous u - derivCLM f hf u h) t‖
      = ‖f (u t + h t) - f (u t) - fderiv ℝ f (u t) (h t)‖ := by
        simp only [ContinuousMap.sub_apply, ContinuousMap.coe_sub, compCM_apply, derivCLM,
          evalCLM_apply, ContinuousMap.add_apply]
    _ ≤ c * ‖h t‖ := hmain
    _ ≤ c * ‖h‖ := hle

/-- Bound on the derivative of the composition operator. -/
lemma norm_derivCLM_le {f : E → F} (hf : ContDiff ℝ 1 f) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ f z‖ ≤ C) (u : C(K, E)) :
    ‖derivCLM f hf u‖ ≤ C := by
  have hg : ‖compCM (fderiv ℝ f) (hf.continuous_fderiv (by norm_num)) u‖ ≤ C := by
    rw [ContinuousMap.norm_le _ (le_trans (norm_nonneg _) (hC 0))]
    intro t
    exact hC (u t)
  exact (norm_evalCLM_le _).trans hg

end Deriv

section Induct

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Smoothness of the composition operator on spaces of continuous maps.** -/
theorem contDiff_compCM_aux (n : ℕ) {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F)
    (hfc : Continuous f) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun u : C(K, E) =>
      (⟨fun t => f (u t), hfc.comp u.continuous⟩ : C(K, F))) := by
  induction n generalizing E F f with
  | zero =>
    exact contDiff_zero.mpr ((continuous_compCM hfc).congr (fun u => rfl))
  | succ n ih =>
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
    have hf1c : Continuous f := hf1.continuous
    have hfd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (le_of_eq (Nat.cast_succ n).symm)
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 from Nat.cast_succ n]
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun u => derivCLM f hf1 u, ?_, fun u => hasFDerivAt_compCM hf1 u⟩
    have hg : ContDiff ℝ n (fun u : C(K, E) =>
        compCM (fderiv ℝ f) (hf1.continuous_fderiv (by norm_num)) u) :=
      ih (fderiv ℝ f) (hf1.continuous_fderiv (by norm_num)) hfd
    have hfun : (fun u : C(K, E) => derivCLM f hf1 u)
        = (fun g : C(K, E →L[ℝ] F) => evalCLM g) ∘ (fun u : C(K, E) =>
            compCM (fderiv ℝ f) (hf1.continuous_fderiv (by norm_num)) u) := rfl
    rw [hfun]
    exact (contDiff_evalCLMₗ n).comp hg

/-- **Smoothness of the composition operator on spaces of continuous maps.** -/
theorem contDiff_compCM (n : ℕ) {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F)
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun u : C(K, E) =>
      (⟨fun t => f (u t), hf.continuous.comp u.continuous⟩ : C(K, F))) :=
  contDiff_compCM_aux n f hf.continuous hf

end Induct

end Work.RPCore.Port.ODE
