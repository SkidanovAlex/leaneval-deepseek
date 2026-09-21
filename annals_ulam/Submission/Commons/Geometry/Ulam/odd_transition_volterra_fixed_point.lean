import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section

open Filter Set
open scoped Topology
open MeasureTheory
open scoped Interval

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def oddTransitionVolterraOp {a b : ℝ} (Q : E ≃L[ℝ] E)
    (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z : ℝ → E) (s : ℝ) : E :=
  Z s - Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s)

lemma oddTransitionVolterraOp_fixedPoint_solves {a b : ℝ} (Q : E ≃L[ℝ] E)
    (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E) (Z : ℝ → E)
    (hZ : ∀ s ∈ Set.Icc a b, oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ Z s = Z s) :
    ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s := by
  intro s hs
  have h := hZ s hs
  unfold oddTransitionVolterraOp at h
  have hsub : Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s) = 0 := by
    have h' : Z s - (Z s - Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s)) = 0 := by
      rw [h, sub_self]
    simpa using h'
  have hzero : G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s = 0 := by
    exact Q.symm.map_eq_zero_iff.mp hsub
  have h1 : G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) = Ξ s := sub_eq_zero.mp hzero
  have h2 := eq_add_of_sub_eq (a := G s (Z s)) (b := Ξ s)
    (c := (∫ σ in s..b, Θ s σ (Z σ))) h1
  simpa [add_comm] using h2

lemma oddTransitionVolterraOp_dist_le
    {a b s : ℝ} {Q : E ≃L[ℝ] E}
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Z W : ℝ → E}
    {K_G L_Θ M : ℝ} (hK_nonneg : 0 ≤ K_G) (hL_nonneg : 0 ≤ L_Θ)
    (hG : ∀ s z w, dist (z - Q.symm (G s z)) (w - Q.symm (G s w)) ≤ K_G * dist z w)
    (hΘ_lip : ∀ s σ z w, dist (Θ s σ z) (Θ s σ w) ≤ L_Θ * dist z w)
    (hΘZ_int : ∀ s, IntervalIntegrable (fun σ => Θ s σ (Z σ)) volume s b)
    (hΘW_int : ∀ s, IntervalIntegrable (fun σ => Θ s σ (W σ)) volume s b)
    (hsb : s ≤ b)
    (hZ_le : ∀ σ ∈ Set.Icc s b, dist (Z σ) (W σ) ≤ M) :
    dist (oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ Z s)
      (oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ W s) ≤
      (K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - s)) * M := by
  unfold oddTransitionVolterraOp
  have hs_mem : s ∈ Set.Icc s b := ⟨le_rfl, hsb⟩
  have hZ_s : dist (Z s) (W s) ≤ M := hZ_le s hs_mem
  have hG_bound : dist (Z s - Q.symm (G s (Z s))) (W s - Q.symm (G s (W s))) ≤ K_G * M := by
    calc
      dist (Z s - Q.symm (G s (Z s))) (W s - Q.symm (G s (W s)))
          ≤ K_G * dist (Z s) (W s) := hG s (Z s) (W s)
      _ ≤ K_G * M := by
        exact mul_le_mul_of_nonneg_left hZ_s hK_nonneg
  have hI_sub : (∫ σ in s..b, Θ s σ (Z σ)) - (∫ σ in s..b, Θ s σ (W σ)) =
      ∫ σ in s..b, (Θ s σ (Z σ) - Θ s σ (W σ)) := by
    rw [intervalIntegral.integral_sub (hΘZ_int s) (hΘW_int s)]
  have hI_norm : dist (∫ σ in s..b, Θ s σ (Z σ)) (∫ σ in s..b, Θ s σ (W σ)) ≤
      L_Θ * (b - s) * M := by
    rw [dist_eq_norm, hI_sub]
    have hnorm_int : ‖∫ σ in s..b, (Θ s σ (Z σ) - Θ s σ (W σ))‖ ≤
        (L_Θ * M) * (b - s) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := b)
        (f := fun σ => Θ s σ (Z σ) - Θ s σ (W σ)) (C := L_Θ * M) ?_
      · simpa [abs_of_nonneg (sub_nonneg.mpr hsb)] using h
      · intro σ hσ
        have hσ_mem : σ ∈ Set.Icc s b := by
          rw [Set.uIoc_of_le hsb] at hσ
          exact ⟨le_of_lt hσ.1, hσ.2⟩
        have hdist := hΘ_lip s σ (Z σ) (W σ)
        have hnorm : ‖Θ s σ (Z σ) - Θ s σ (W σ)‖ ≤ L_Θ * dist (Z σ) (W σ) := by
          simpa [dist_eq_norm] using hdist
        exact hnorm.trans (mul_le_mul_of_nonneg_left (hZ_le σ hσ_mem) hL_nonneg)
    calc
      ‖∫ σ in s..b, (Θ s σ (Z σ) - Θ s σ (W σ))‖
          ≤ (L_Θ * M) * (b - s) := hnorm_int
      _ = L_Θ * (b - s) * M := by ring
  have hQ_I : dist (Q.symm (∫ σ in s..b, Θ s σ (Z σ)))
      (Q.symm (∫ σ in s..b, Θ s σ (W σ))) ≤
      ‖(Q.symm : E →L[ℝ] E)‖ * (L_Θ * (b - s) * M) := by
    exact (Q.symm : E →L[ℝ] E).dist_le_opNorm _ _ |>.trans
      (mul_le_mul_of_nonneg_left hI_norm (norm_nonneg _))
  have hmain : dist (Z s - Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s))
      (W s - Q.symm (G s (W s) - (∫ σ in s..b, Θ s σ (W σ)) - Ξ s)) ≤
      dist (Z s - Q.symm (G s (Z s))) (W s - Q.symm (G s (W s))) +
        dist (Q.symm (∫ σ in s..b, Θ s σ (Z σ))) (Q.symm (∫ σ in s..b, Θ s σ (W σ))) := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    have hsub :
        (Z s - Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s)) -
          (W s - Q.symm (G s (W s) - (∫ σ in s..b, Θ s σ (W σ)) - Ξ s)) =
        ((Z s - Q.symm (G s (Z s))) - (W s - Q.symm (G s (W s)))) +
          (Q.symm (∫ σ in s..b, Θ s σ (Z σ)) - Q.symm (∫ σ in s..b, Θ s σ (W σ))) := by
      simp only [map_sub]
      abel
    rw [hsub]
    exact norm_add_le _ _
  calc
    dist (Z s - Q.symm (G s (Z s) - (∫ σ in s..b, Θ s σ (Z σ)) - Ξ s))
        (W s - Q.symm (G s (W s) - (∫ σ in s..b, Θ s σ (W σ)) - Ξ s))
      ≤ dist (Z s - Q.symm (G s (Z s))) (W s - Q.symm (G s (W s))) +
          dist (Q.symm (∫ σ in s..b, Θ s σ (Z σ))) (Q.symm (∫ σ in s..b, Θ s σ (W σ))) := hmain
    _ ≤ K_G * M + ‖(Q.symm : E →L[ℝ] E)‖ * (L_Θ * (b - s) * M) := by
          gcongr
    _ = (K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - s)) * M := by ring

def oddTransitionBcfExt {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E) : ℝ → E :=
  Set.IccExtend hab (fun s : Set.Icc a b => Z s)

lemma oddTransitionBcfExt_continuous {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E) :
    Continuous (oddTransitionBcfExt hab Z) := by
  dsimp [oddTransitionBcfExt]
  exact Z.continuous.Icc_extend'

lemma oddTransitionBcfExt_of_mem {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : oddTransitionBcfExt hab Z x = Z ⟨x, hx⟩ := by
  dsimp [oddTransitionBcfExt]
  exact Set.IccExtend_of_mem (h := hab) (f := fun s : Set.Icc a b => Z s) hx

lemma oddTransitionBcfExt_apply_mem {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) : oddTransitionBcfExt hab Z (s : ℝ) = Z s := by
  exact oddTransitionBcfExt_of_mem hab Z s.2

lemma oddTransitionVolterraOpIntegral_continuousOn
    {a b : ℝ} (hab : a ≤ b)
    {Θ : ℝ → ℝ → E → E} (Z : BoundedContinuousFunction (Set.Icc a b) E)
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2)) :
    ContinuousOn (fun s : ℝ => ∫ σ in s..b, Θ s σ (oddTransitionBcfExt hab Z σ)) (Set.Icc a b) := by
  let f : ℝ → ℝ → E := fun s σ => Θ s σ (oddTransitionBcfExt hab Z σ)
  have hf_cont : Continuous f.uncurry := by
    have hZ : Continuous (oddTransitionBcfExt hab Z) := oddTransitionBcfExt_continuous hab Z
    have hpair : Continuous (fun p : ℝ × ℝ => (p.1, p.2, oddTransitionBcfExt hab Z p.2)) := by
      fun_prop
    dsimp [f]
    exact hΘ_cont.comp hpair
  have hcont : Continuous (fun s : ℝ => ∫ σ in b..s, f s σ) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      (f := f) (a₀ := b) (s := fun s : ℝ => s) hf_cont continuous_id
  have hneg : Continuous (fun s : ℝ => -∫ σ in b..s, f s σ) := hcont.neg
  have h_eq : (fun s : ℝ => -∫ σ in b..s, f s σ) =
      (fun s : ℝ => ∫ σ in s..b, Θ s σ (oddTransitionBcfExt hab Z σ)) := by
    funext s
    dsimp [f]
    rw [intervalIntegral.integral_symm]
    exact neg_neg _
  rw [h_eq] at hneg
  exact hneg.continuousOn

lemma oddTransitionVolterraOp_continuousOn
    {a b : ℝ} (hab : a ≤ b)
    {Q : E ≃L[ℝ] E}
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E}
    (Z : BoundedContinuousFunction (Set.Icc a b) E)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ) :
    ContinuousOn (fun s : ℝ => oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Z) s)
      (Set.Icc a b) := by
  have hZc_sub : Continuous (fun s : Set.Icc a b => oddTransitionBcfExt hab Z (s : ℝ)) :=
    (oddTransitionBcfExt_continuous hab Z).comp continuous_subtype_val
  have hGc : Continuous (fun s : Set.Icc a b => G (s : ℝ) (oddTransitionBcfExt hab Z (s : ℝ))) :=
    hG_cont.comp (continuous_subtype_val.prodMk hZc_sub)
  have hIc : Continuous (fun s : Set.Icc a b => ∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (oddTransitionBcfExt hab Z σ)) := by
    exact continuousOn_iff_continuous_domRestrict.mp
      (oddTransitionVolterraOpIntegral_continuousOn hab (Θ := Θ) Z hΘ_cont)
  have hΞc : Continuous (fun s : Set.Icc a b => Ξ (s : ℝ)) :=
    hΞ_cont.comp continuous_subtype_val
  have hAc : Continuous (fun s : Set.Icc a b =>
      G (s : ℝ) (oddTransitionBcfExt hab Z (s : ℝ)) - (∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (oddTransitionBcfExt hab Z σ)) - Ξ (s : ℝ)) :=
    (hGc.sub hIc).sub hΞc
  have hQc : Continuous (fun s : Set.Icc a b =>
      Q.symm (G (s : ℝ) (oddTransitionBcfExt hab Z (s : ℝ)) - (∫ σ in (s : ℝ)..b, Θ (s : ℝ) σ (oddTransitionBcfExt hab Z σ)) - Ξ (s : ℝ))) :=
    (Q.symm : E →L[ℝ] E).continuous.comp hAc
  have hmain : Continuous (fun s : Set.Icc a b =>
      oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Z) (s : ℝ)) := by
    dsimp [oddTransitionVolterraOp]
    exact hZc_sub.sub hQc
  exact continuousOn_iff_continuous_domRestrict.mpr hmain

def oddTransitionVolterraOpBcf {a b : ℝ} (hab : a ≤ b)
    (Q : E ≃L[ℝ] E)
    (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ) :
    BoundedContinuousFunction (Set.Icc a b) E → BoundedContinuousFunction (Set.Icc a b) E := by
  intro Z
  let g : C(Set.Icc a b, E) :=
    { toFun := fun s => oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Z) (s : ℝ)
      continuous_toFun := by
        exact continuousOn_iff_continuous_domRestrict.mp
          (oddTransitionVolterraOp_continuousOn hab (Q := Q) (G := G) (Θ := Θ) (Ξ := Ξ) Z hG_cont hΘ_cont hΞ_cont) }
  exact BoundedContinuousFunction.mkOfCompact g

lemma oddTransitionVolterraOpBcf_apply {a b : ℝ} (hab : a ≤ b)
    (Q : E ≃L[ℝ] E)
    (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ) (Z : BoundedContinuousFunction (Set.Icc a b) E)
    (s : Set.Icc a b) :
    oddTransitionVolterraOpBcf hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont Z s =
      oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Z) (s : ℝ) := rfl

lemma oddTransitionBcf_dist_le_of_pointwise {α : Type*} [TopologicalSpace α] {β : Type*} [PseudoMetricSpace β]
    {f g : BoundedContinuousFunction α β} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, dist (f x) (g x) ≤ C) : dist f g ≤ C := by
  exact (BoundedContinuousFunction.dist_le hC).2 h

lemma oddTransitionBcf_lipschitz_of_pointwise {α : Type*} [TopologicalSpace α] {β : Type*} [PseudoMetricSpace β]
    {K : NNReal} {T : BoundedContinuousFunction α β → BoundedContinuousFunction α β}
    (hpoint : ∀ Z W : BoundedContinuousFunction α β, ∀ x : α,
      dist ((T Z) x) ((T W) x) ≤ (K : ℝ) * dist Z W) :
    LipschitzWith K T := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  apply oddTransitionBcf_dist_le_of_pointwise (mul_nonneg K.2 dist_nonneg)
  intro x
  exact hpoint Z W x

lemma oddTransitionContractingWith_of_pointwise {α : Type*} [TopologicalSpace α] {β : Type*} [MetricSpace β]
    {K : NNReal} {T : BoundedContinuousFunction α β → BoundedContinuousFunction α β}
    (hK : K < 1)
    (hpoint : ∀ Z W : BoundedContinuousFunction α β, ∀ x : α,
      dist ((T Z) x) ((T W) x) ≤ (K : ℝ) * dist Z W) :
    ContractingWith K T :=
  ⟨hK, oddTransitionBcf_lipschitz_of_pointwise hpoint⟩

theorem odd_transition_volterra_fixed_point_of_global_lipschitz
    {a b : ℝ} (hab : a ≤ b)
    (Q : E ≃L[ℝ] E)
    (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    {K_G L_Θ : ℝ} (hK_G : 0 ≤ K_G) (hL_Θ : 0 ≤ L_Θ)
    (hG_lip : ∀ s z w, dist (z - Q.symm (G s z)) (w - Q.symm (G s w)) ≤ K_G * dist z w)
    (hΘ_lip : ∀ s σ z w, dist (Θ s σ z) (Θ s σ w) ≤ L_Θ * dist z w)
    (hK_lt : K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - a) < 1) :
    ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧
      ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s := by
  let K : ℝ := K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - a)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have hQ : 0 ≤ ‖(Q.symm : E →L[ℝ] E)‖ := norm_nonneg _
    have hLen : 0 ≤ b - a := sub_nonneg.mpr hab
    have h1 : 0 ≤ ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ := mul_nonneg hQ hL_Θ
    have h2 : 0 ≤ ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - a) := mul_nonneg h1 hLen
    exact add_nonneg hK_G h2
  have hK_lt' : K < 1 := hK_lt
  let Knn : NNReal := ⟨K, hK_nonneg⟩
  have hKnn_lt : Knn < 1 := by exact_mod_cast hK_lt'
  let T : BoundedContinuousFunction (Set.Icc a b) E → BoundedContinuousFunction (Set.Icc a b) E :=
    oddTransitionVolterraOpBcf hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont
  have hpoint : ∀ Z W : BoundedContinuousFunction (Set.Icc a b) E, ∀ s : Set.Icc a b,
      dist ((T Z) s) ((T W) s) ≤ (Knn : ℝ) * dist Z W := by
    intro Z W s
    have hTZ := oddTransitionVolterraOpBcf_apply hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont Z s
    have hTW := oddTransitionVolterraOpBcf_apply hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont W s
    rw [hTZ, hTW]
    have hs : (s : ℝ) ∈ Set.Icc a b := s.2
    have hZ_le : ∀ σ ∈ Set.Icc (s : ℝ) b, dist (oddTransitionBcfExt hab Z σ) (oddTransitionBcfExt hab W σ) ≤ dist Z W := by
      intro σ hσ
      have hσ_ab : σ ∈ Set.Icc a b := ⟨le_trans hs.1 hσ.1, hσ.2⟩
      rw [oddTransitionBcfExt_of_mem hab Z hσ_ab, oddTransitionBcfExt_of_mem hab W hσ_ab]
      exact (BoundedContinuousFunction.dist_coe_le_dist (f := Z) (g := W) ⟨σ, hσ_ab⟩)
    have hΘZ_int : ∀ s : ℝ, IntervalIntegrable (fun σ => Θ s σ (oddTransitionBcfExt hab Z σ)) volume s b := by
      intro s
      exact Continuous.intervalIntegrable (by
        dsimp [oddTransitionBcfExt]
        fun_prop) s b
    have hΘW_int : ∀ s : ℝ, IntervalIntegrable (fun σ => Θ s σ (oddTransitionBcfExt hab W σ)) volume s b := by
      intro s
      exact Continuous.intervalIntegrable (by
        dsimp [oddTransitionBcfExt]
        fun_prop) s b
    have hmain := oddTransitionVolterraOp_dist_le (a := a) (b := b) (s := (s : ℝ))
      (Q := Q) (G := G) (Θ := Θ) (Ξ := Ξ) (Z := oddTransitionBcfExt hab Z) (W := oddTransitionBcfExt hab W)
      (K_G := K_G) (L_Θ := L_Θ) (M := dist Z W) hK_G hL_Θ hG_lip hΘ_lip hΘZ_int hΘW_int hs.2 hZ_le
    have hlen : b - (s : ℝ) ≤ b - a := by linarith [hs.1]
    have hcoef : K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - (s : ℝ)) ≤ K := by
      dsimp [K]
      gcongr
    calc
      dist (oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Z) (s : ℝ))
          (oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab W) (s : ℝ))
          ≤ (K_G + ‖(Q.symm : E →L[ℝ] E)‖ * L_Θ * (b - (s : ℝ))) * dist Z W := hmain
      _ ≤ K * dist Z W := by
          exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
      _ = (Knn : ℝ) * dist Z W := by rfl
  have hcontr : ContractingWith Knn T := oddTransitionContractingWith_of_pointwise hKnn_lt hpoint
  let Zcur : BoundedContinuousFunction (Set.Icc a b) E := ContractingWith.fixedPoint T hcontr
  have hfix : Function.IsFixedPt T Zcur := ContractingWith.fixedPoint_isFixedPt hcontr
  dsimp [T] at hfix
  refine ⟨oddTransitionBcfExt hab Zcur, ?_, ?_⟩
  · exact (oddTransitionBcfExt_continuous hab Zcur).continuousOn
  · intro s hs
    have hEq := oddTransitionVolterraOp_fixedPoint_solves (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Zcur) ?_
    · simpa [oddTransitionBcfExt_of_mem hab Zcur hs] using hEq s hs
    · intro t ht
      have hTZt := oddTransitionVolterraOpBcf_apply hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont Zcur ⟨t, ht⟩
      have hvolt : oddTransitionVolterraOp (a := a) (b := b) Q G Θ Ξ (oddTransitionBcfExt hab Zcur) t = oddTransitionBcfExt hab Zcur t := by
        rw [← hTZt]
        rw [oddTransitionBcfExt_of_mem hab Zcur ht]
        exact congrArg (fun f : BoundedContinuousFunction (Set.Icc a b) E => f ⟨t, ht⟩) hfix
      exact hvolt




lemma odd_transition_volterra_fixed_point {a b : ℝ} (hab : a ≤ b)
    (Q : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (G : ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (Θ : ℝ → ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (Ξ : ℝ → EuclideanSpace ℝ (Fin 4))
    (hG_cont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    {K_G L_Θ : ℝ} (hK_G : 0 ≤ K_G) (hL_Θ : 0 ≤ L_Θ)
    (hG_lip : ∀ s z w, dist (z - Q.symm (G s z)) (w - Q.symm (G s w)) ≤ K_G * dist z w)
    (hΘ_lip : ∀ s σ z w, dist (Θ s σ z) (Θ s σ w) ≤ L_Θ * dist z w)
    (hK_lt : K_G + ‖(Q.symm : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))‖ * L_Θ * (b - a) < 1) :
    ∃ Z : ℝ → EuclideanSpace ℝ (Fin 4),
      ContinuousOn Z (Set.Icc a b) ∧
      ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s := by
  exact (odd_transition_volterra_fixed_point_of_global_lipschitz (E := EuclideanSpace ℝ (Fin 4))
    (a := a) (b := b) hab Q G Θ Ξ hG_cont hΘ_cont hΞ_cont hK_G hL_Θ hG_lip hΘ_lip hK_lt)

end Commons.Geometry.Ulam