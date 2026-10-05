import Mathlib
import Submission.Work.RPCore.Port.ODE.Nemytskii
import Submission.Work.RPCore.Port.ODE.Primitive

set_option autoImplicit false

/-!
# Smooth dependence of the flow on the initial condition

The time slices of the flow of a smooth vector field with bounded value and derivative are smooth,
for uniformly small times.  The proof uses the implicit function theorem in the Banach space of
continuous paths on a small interval: the fixed point equation of the Picard operator is a `C^n`
equation whose derivative in the path variable is invertible.
-/

open scoped Topology NNReal ContDiff
open Set Function Pointwise

namespace Work.RPCore.Port.ODE

universe u

section Crux

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- A bound on the derivative gives a Lipschitz bound. -/
lemma norm_sub_le_of_norm_fderiv_le {X : E → E} {K : ℝ} (hX1 : ContDiff ℝ 1 X)
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (a b : E) : ‖X a - X b‖ ≤ K * ‖a - b‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hLip : LipschitzWith K.toNNReal X :=
    lipschitzWith_of_nnnorm_fderiv_le (hX1.differentiable (by norm_num)) (fun z => by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal K hK0]
      exact hK z)
  have h := hLip.dist_le_mul a b
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hK0] at h
  exact h

/-- The Picard operator of the ODE `γ' = X ∘ γ` on the interval `[0,δ]`. -/
noncomputable def pic (X : E → E) (hXc : Continuous X) (δ : ℝ) (hδ : 0 ≤ δ) (y : E)
    (u : C(Set.Icc 0 δ, E)) : C(Set.Icc 0 δ, E) :=
  ContinuousMap.const _ y + primCLM δ hδ (compCM X hXc u)

@[simp]
lemma pic_apply (X : E → E) (hXc : Continuous X) (δ : ℝ) (hδ : 0 ≤ δ) (y : E)
    (u : C(Set.Icc 0 δ, E)) (t : Set.Icc 0 δ) :
    pic X hXc δ hδ y u t = y + ∫ s in (0 : ℝ)..(t : ℝ), X (u (Set.projIcc 0 δ hδ s)) := by
  simp [pic, primCLM_apply, primLM_apply, compCM_apply]

/-- The Picard operator is a contraction with constant `δ * K`. -/
lemma dist_pic_le {X : E → E} {K : ℝ} (hX1 : ContDiff ℝ 1 X) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K)
    (hXc : Continuous X) {δ : ℝ} (hδ : 0 ≤ δ) (y : E) (u v : C(Set.Icc 0 δ, E)) :
    dist (pic X hXc δ hδ y u) (pic X hXc δ hδ y v) ≤ (δ * K) * dist u v := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hδ0 : 0 ≤ δ := hδ
  have hfun : pic X hXc δ hδ y u - pic X hXc δ hδ y v
      = primCLM δ hδ (compCM X hXc u - compCM X hXc v) := by
    simp only [pic, add_sub_add_left_eq_sub]
    rw [← map_sub]
  rw [dist_eq_norm, dist_eq_norm, hfun]
  have hmid : ‖compCM X hXc u - compCM X hXc v‖ ≤ K * ‖u - v‖ := by
    rw [ContinuousMap.norm_le _ (mul_nonneg hK0 (norm_nonneg _))]
    intro t
    have h1 : ‖X (u t) - X (v t)‖ ≤ K * ‖u t - v t‖ :=
      norm_sub_le_of_norm_fderiv_le hX1 hK _ _
    have h2 : ‖u t - v t‖ ≤ ‖u - v‖ := by
      rw [← ContinuousMap.sub_apply]
      exact ContinuousMap.norm_coe_le_norm (u - v) t
    calc ‖(compCM X hXc u - compCM X hXc v) t‖ = ‖X (u t) - X (v t)‖ := by
          rw [ContinuousMap.sub_apply, compCM_apply, compCM_apply]
      _ ≤ K * ‖u t - v t‖ := h1
      _ ≤ K * ‖u - v‖ := mul_le_mul_of_nonneg_left h2 hK0
  calc ‖primCLM δ hδ (compCM X hXc u - compCM X hXc v)‖
      ≤ δ * ‖compCM X hXc u - compCM X hXc v‖ := norm_primCLM_apply_le δ hδ _
    _ ≤ δ * (K * ‖u - v‖) := mul_le_mul_of_nonneg_left hmid hδ0
    _ = (δ * K) * ‖u - v‖ := by ring


/-- The constant-path map as a bounded linear map. -/
noncomputable def constCLM (δ : ℝ) : E →L[ℝ] C(Set.Icc 0 δ, E) :=
  LinearMap.mkContinuous
    { toFun := fun y => ContinuousMap.const (Set.Icc 0 δ) y
      map_add' := by intro a b; ext t; rfl
      map_smul' := by intro c a; ext t; rfl }
    1
    (fun y => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg y)]
      intro t
      exact le_rfl)

@[simp]
lemma constCLM_apply (δ : ℝ) (y : E) (t : Set.Icc 0 δ) : constCLM δ y t = y := rfl

lemma contDiff_constCLM (δ : ℝ) (n : ℕ∞ω) : ContDiff ℝ n (constCLM (E := E) δ) :=
  (constCLM (E := E) δ).contDiff (𝕜 := ℝ) (n := n)

/-- The Picard operator, as a function of `(y,u)`, is smooth. -/
lemma contDiff_pic (X : E → E) (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (δ : ℝ)
    (hδ : 0 ≤ δ) (n : ℕ) :
    ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) => pic X hX.continuous δ hδ p.1 p.2) := by
  have h1 : ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) => constCLM δ p.1) :=
    (contDiff_constCLM δ n).comp contDiff_fst
  have h2 : ContDiff ℝ n (fun p : E × C(Set.Icc 0 δ, E) =>
      primCLM δ hδ (compCM X hX.continuous p.2)) :=
    (ContinuousLinearMap.contDiff (primCLM δ hδ)).comp
      ((contDiff_compCM n X (hX.of_le (by exact_mod_cast le_top))).comp contDiff_snd)
  have hfun : (fun p : E × C(Set.Icc 0 δ, E) => pic X hX.continuous δ hδ p.1 p.2)
      = fun p => constCLM δ p.1 + primCLM δ hδ (compCM X hX.continuous p.2) := by
    funext p
    rfl
  rw [hfun]
  exact h1.add h2

/-- Derivative of the Picard operator in both variables. -/
lemma hasFDerivAt_pic (X : E → E) (hX1 : ContDiff ℝ 1 X) (hXc : Continuous X) (δ : ℝ)
    (hδ : 0 ≤ δ) (y : E) (u : C(Set.Icc 0 δ, E)) :
    HasFDerivAt (fun p : E × C(Set.Icc 0 δ, E) => pic X hXc δ hδ p.1 p.2)
      (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E) +
        (primCLM δ hδ ∘L derivCLM X hX1 u) ∘L
          ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E)) (y, u) := by
  have h1 : HasFDerivAt (fun p : E × C(Set.Icc 0 δ, E) => constCLM δ p.1)
      (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E)) (y, u) :=
    ((constCLM (E := E) δ).hasFDerivAt).comp (y, u)
      (hasFDerivAt_fst (p := (y, u)))
  have h2 : HasFDerivAt (fun p : E × C(Set.Icc 0 δ, E) =>
      primCLM δ hδ (compCM X hXc p.2))
      ((primCLM δ hδ ∘L derivCLM X hX1 u) ∘L
        ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E)) (y, u) := by
    have hCM : HasFDerivAt (compCM X hXc ∘ Prod.snd)
        (derivCLM X hX1 u ∘L ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E)) (y, u) :=
      HasFDerivAt.comp (y, u) (hasFDerivAt_compCM hX1 u) (hasFDerivAt_snd (p := (y, u)))
    have h4 : HasFDerivAt (fun v : C(Set.Icc 0 δ, E) => primCLM δ hδ v)
        (primCLM δ hδ) (compCM X hXc u) :=
      ContinuousLinearMap.hasFDerivAt (primCLM (E := E) δ hδ)
    have h3 := HasFDerivAt.comp (y, u) h4 hCM
    simpa [Function.comp_def, ContinuousLinearMap.comp_assoc] using h3
  have hfun : (fun p : E × C(Set.Icc 0 δ, E) => pic X hXc δ hδ p.1 p.2)
      = fun p => constCLM δ p.1 + primCLM δ hδ (compCM X hXc p.2) := by
    funext p
    rfl
  rw [hfun]
  exact h1.add h2

/-- Restricting a global integral curve to `[0,δ]` gives a fixed point of the Picard operator. -/
lemma isFixedPt_pic_of_curve (X : E → E) (hXc : Continuous X) {δ : ℝ} (hδ : 0 ≤ δ) {y : E}
    {γ : ℝ → E} (hγ0 : γ 0 = y) (hγ : IsIntegralCurve γ (fun _ z => X z)) :
    pic X hXc δ hδ y ⟨fun t => γ t, hγ.continuous.comp continuous_subtype_val⟩ =
      ⟨fun t => γ t, hγ.continuous.comp continuous_subtype_val⟩ := by
  ext t
  rw [pic_apply]
  change y + (∫ s in (0 : ℝ)..(t : ℝ), X (γ (Set.projIcc 0 δ hδ s))) = γ t
  have hcongr : (∫ s in (0 : ℝ)..(t : ℝ), X (γ (Set.projIcc 0 δ hδ s)))
      = ∫ s in (0 : ℝ)..(t : ℝ), X (γ s) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs' : s ∈ Set.Icc (0 : ℝ) δ := by
      rw [uIcc_of_le t.2.1] at hs
      exact ⟨hs.1, hs.2.trans t.2.2⟩
    rw [show (Set.projIcc 0 δ hδ s : ℝ) = s from congrArg Subtype.val (projIcc_of_mem hδ hs')]
  rw [hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hγ s)
      ((hXc.comp hγ.continuous).intervalIntegrable 0 (t : ℝ)),
    hγ0]
  rw [add_comm, sub_add_cancel]

/-- A fixed point of the Picard operator solves the ODE on `(0,δ)`. -/
lemma isIntegralCurveOn_of_isFixedPt (X : E → E) (hXc : Continuous X) {δ : ℝ} (hδ : 0 ≤ δ)
    {y : E} {u : C(Set.Icc 0 δ, E)} (hu : pic X hXc δ hδ y u = u) :
    IsIntegralCurveOn (fun s : ℝ => u (Set.projIcc 0 δ hδ s)) (fun _ z => X z) (Ioo 0 δ) := by
  have hu' : ∀ t : Set.Icc 0 δ, u t = y + ∫ s in (0 : ℝ)..(t : ℝ),
      X (u (Set.projIcc 0 δ hδ s)) := by
    intro t
    have h := DFunLike.congr_fun hu t
    rw [pic_apply] at h
    exact h.symm
  have hcont : Continuous fun s : ℝ => X (u (Set.projIcc 0 δ hδ s)) :=
    hXc.comp (u.continuous.comp continuous_projIcc)
  intro s hs
  have hagree : (fun r : ℝ => u (Set.projIcc 0 δ hδ r)) =ᶠ[𝓝 s]
      (fun r : ℝ => y + ∫ r' in (0 : ℝ)..r, X (u (Set.projIcc 0 δ hδ r'))) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    have hrI : r ∈ Set.Icc (0 : ℝ) δ := ⟨hr.1.le, hr.2.le⟩
    rw [show u (Set.projIcc 0 δ hδ r) = u ⟨r, hrI⟩ from by
      congr 1
      exact Subtype.ext (congrArg Subtype.val (projIcc_of_mem hδ hrI)), hu']
  have hderiv : HasDerivAt (fun r : ℝ => y + ∫ r' in (0 : ℝ)..r,
      X (u (Set.projIcc 0 δ hδ r'))) (X (u (Set.projIcc 0 δ hδ s))) s := by
    have h := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 s)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
    exact h.const_add y
  exact ((hagree.hasDerivAt_iff).mpr hderiv).hasDerivWithinAt


/-- Uniqueness of global integral curves (a local copy, to avoid a dependency cycle). -/
lemma eq_of_isIntegralCurve {X : E → E} {L : NNReal} (hL : LipschitzWith L X) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurve γ₁ (fun _ z => X z)) (h₂ : IsIntegralCurve γ₂ (fun _ z => X z))
    {t : ℝ} (h : γ₁ t = γ₂ t) : γ₁ = γ₂ :=
  ODE_solution_unique_univ (v := fun _ z => X z) (s := fun _ => univ) (K := L) (t₀ := t)
    (fun _ => hL.lipschitzOnWith) (fun s => ⟨h₁ s, mem_univ _⟩) (fun s => ⟨h₂ s, mem_univ _⟩) h

/-- The curve `s ↦ Φ s y` is an integral curve of `X`, whenever `Φ` is a flow function. -/
lemma isIntegralCurve_flow {X : E → E} {L : NNReal} (hL : LipschitzWith L X) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    (y : E) : IsIntegralCurve (fun s => Φ s y) (fun _ z => X z) := by
  set γ : ℝ → E := Classical.choose (hΦ 0 y) with hγdef
  have hγ0 : γ 0 = y := (Classical.choose_spec (hΦ 0 y)).1
  have hγint : IsIntegralCurve γ (fun _ z => X z) := (Classical.choose_spec (hΦ 0 y)).2.1
  have hmain : ∀ r : ℝ, Φ r y = γ r := by
    intro r
    obtain ⟨γr, hγr0, hγr, hγrval⟩ := hΦ r y
    have heq : γr = γ := eq_of_isIntegralCurve hL hγr hγint (by rw [hγr0, hγ0])
    rw [← hγrval, heq]
  rw [show (fun s : ℝ => Φ s y) = γ from funext hmain]
  exact hγint

lemma flow_zero {X : E → E} (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    (y : E) : Φ 0 y = y := by
  obtain ⟨γ, hγ0, -, hγval⟩ := hΦ 0 y
  rw [← hγval, hγ0]

variable {X : E → E} {K : ℝ}

/-- The Lipschitz constant of `X` associated with a bound on its derivative. -/
noncomputable def lipConst (K : ℝ) : NNReal := K.toNNReal

lemma lipschitzWith_lipConst {X : E → E} {K : ℝ} (hX1 : ContDiff ℝ 1 X)
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) : LipschitzWith (lipConst K) X := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  refine lipschitzWith_of_nnnorm_fderiv_le (hX1.differentiable (by norm_num)) (fun z => ?_)
  show ‖fderiv ℝ X z‖₊ ≤ K.toNNReal
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal K hK0]
  exact hK z

/-- **Local smoothness of the flow in the initial condition.**  For `0 ≤ t < δ` (with `δ` a fixed
small constant depending only on a bound `K` for the derivative), the map `y ↦ Φ t y` is `C^n`
near any point. -/
lemma contDiffAt_timeSlice (X : E → E) {K : ℝ} (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X)
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    (n : ℕ) (hn : 1 ≤ n) (y₀ : E) {t : ℝ} (ht0 : 0 ≤ t)
    (htδ : t < min 1 (1 / (2 * (K + 1)))) : ContDiffAt ℝ n (fun y => Φ t y) y₀ := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by exact_mod_cast le_top)
  have hXc : Continuous X := hX.continuous
  set δ : ℝ := min 1 (1 / (2 * (K + 1))) with hδdef
  have hδpos : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδle : 0 ≤ δ := hδpos.le
  have hδK : δ * K < 1 := by
    have h1 : δ ≤ 1 / (2 * (K + 1)) := by rw [hδdef]; exact min_le_right _ _
    have h2 : (0:ℝ) < 2 * (K + 1) := by positivity
    calc δ * K ≤ (1 / (2 * (K + 1))) * K := mul_le_mul_of_nonneg_right h1 hK0
      _ = K / (2 * (K + 1)) := by ring
      _ < 1 := by
          rw [div_lt_one h2]
          linarith
  have hδ' : t < δ := htδ
  -- the base point: the restriction of the global curve through `y₀`
  let u₀ : C(Set.Icc 0 δ, E) :=
    ⟨fun s => (Classical.choose (hΦ 0 y₀)) s,
      ((Classical.choose_spec (hΦ 0 y₀)).2.1).continuous.comp continuous_subtype_val⟩
  have hu₀ : pic X hXc δ hδle y₀ u₀ = u₀ :=
    isFixedPt_pic_of_curve X hXc hδle (Classical.choose_spec (hΦ 0 y₀)).1
      (Classical.choose_spec (hΦ 0 y₀)).2.1
  -- smoothness of the equation
  have hGsmooth : ContDiffAt ℝ (n : ℕ∞ω)
      (fun p : E × C(Set.Icc 0 δ, E) => p.2 - pic X hXc δ hδle p.1 p.2) (y₀, u₀) :=
    (contDiff_snd.sub (contDiff_pic X hX δ hδle n)).contDiffAt
  -- derivative and invertibility
  have hGderiv : HasFDerivAt (fun p : E × C(Set.Icc 0 δ, E) =>
      p.2 - pic X hXc δ hδle p.1 p.2)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E) -
        (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E) +
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) ∘L
            ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E))) (y₀, u₀) :=
    hasFDerivAt_snd.sub (hasFDerivAt_pic X hX1 hXc δ hδle y₀ u₀)
  have hcomp_inr : (ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E) -
        (constCLM δ ∘L ContinuousLinearMap.fst ℝ E C(Set.Icc 0 δ, E) +
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) ∘L
            ContinuousLinearMap.snd ℝ E C(Set.Icc 0 δ, E)))
        ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc 0 δ, E)
      = 1 - primCLM δ hδle ∘L derivCLM X hX1 u₀ := by
    ext v
    simp [ContinuousLinearMap.comp_apply]
  have hBlt : ‖primCLM δ hδle ∘L derivCLM X hX1 u₀‖ < 1 := by
    refine lt_of_le_of_lt ?_ hδK
    refine (norm_primCLM_comp_le δ hδle _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_derivCLM_le hX1 hK u₀) hδle
  have hInv : ContinuousLinearMap.IsInvertible (fderiv ℝ (fun p : E × C(Set.Icc 0 δ, E) =>
      p.2 - pic X hXc δ hδle p.1 p.2) (y₀, u₀) ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc 0 δ, E)) := by
    rw [hGderiv.fderiv, hcomp_inr]
    exact ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub
        (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt), by
      rw [show ((ContinuousLinearEquiv.ofUnit (Units.oneSub
          (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt) :
            C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E)))
          = ((Units.oneSub (primCLM δ hδle ∘L derivCLM X hX1 u₀) hBlt :
              (C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E))ˣ) :
              C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E)) from rfl, Units.val_oneSub]⟩
  -- the implicit function
  set ψ : E → C(Set.Icc 0 δ, E) := hGsmooth.implicitFunction
    (by intro h; rw [Nat.cast_eq_zero] at h; omega) hInv with hψdef
  have hψ0 : ψ y₀ = u₀ := hGsmooth.implicitFunction_apply_self _ _
  have hψsm : ContDiffAt ℝ (n : ℕ∞ω) ψ y₀ := hGsmooth.contDiffAt_implicitFunction _ _
  have hψeq : ∀ᶠ y in 𝓝 y₀, pic X hXc δ hδle y (ψ y) = ψ y := by
    filter_upwards [hGsmooth.eventually_apply_implicitFunction
      (by intro h; rw [Nat.cast_eq_zero] at h; omega) hInv] with y hy
    have hy' : ψ y - pic X hXc δ hδle y (ψ y)
        = u₀ - pic X hXc δ hδle y₀ u₀ := hy
    rw [hu₀, sub_self] at hy'
    exact (sub_eq_zero.mp hy').symm
  -- the two fixed points coincide, by uniqueness of the fixed point of the contraction
  have hkey : ∀ᶠ y in 𝓝 y₀, ∀ s : Set.Icc 0 δ, (ψ y) s = Φ s y := by
    filter_upwards [hψeq] with y hy
    intro s
    let uy : C(Set.Icc 0 δ, E) := ⟨fun r => Φ r y,
      (isIntegralCurve_flow (lipschitzWith_lipConst hX1 hK) Φ hΦ y).continuous.comp
        continuous_subtype_val⟩
    have huy : pic X hXc δ hδle y uy = uy :=
      isFixedPt_pic_of_curve X hXc hδle (flow_zero Φ hΦ y)
        (isIntegralCurve_flow (lipschitzWith_lipConst hX1 hK) Φ hΦ y)
    have hdist : dist (ψ y) uy ≤ (δ * K) * dist (ψ y) uy := by
      calc dist (ψ y) uy = dist (pic X hXc δ hδle y (ψ y)) (pic X hXc δ hδle y uy) := by
            rw [hy, huy]
        _ ≤ (δ * K) * dist (ψ y) uy := dist_pic_le hX1 hK hXc hδle y _ _
    have hzero : dist (ψ y) uy = 0 := by
      by_contra hne
      have hpos : 0 < dist (ψ y) uy := lt_of_le_of_ne (dist_nonneg) (Ne.symm hne)
      nlinarith [hdist, hδK]
    have heq : ψ y = uy := dist_eq_zero.mp hzero
    rw [heq]
    rfl
  -- conclusion
  have hsmooth : ContDiffAt ℝ (n : ℕ∞ω) (fun y => (ψ y) ⟨t, ht0, hδ'.le⟩) y₀ := by
    have h1 := ((ContinuousMap.evalCLM ℝ ⟨t, ht0, hδ'.le⟩).contDiff
      (n := (n : ℕ∞ω))).contDiffAt.comp y₀ hψsm
    simpa [ContinuousMap.evalCLM_apply, Function.comp_def] using h1
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hkey] with y hy
  exact (hy ⟨t, ht0, hδ'.le⟩).symm

/-- **Smooth dependence on the initial condition.**  The time slices of the flow of a smooth vector
field with bounded derivative are smooth, for uniformly small times. -/
theorem contDiff_flow_timeSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (X : E → E)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (M K : ℝ)
    (hM : ∀ z, ‖X z‖ ≤ M) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y) :
    ∃ δ > (0 : ℝ), ∀ t, |t| ≤ δ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ t) := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  set δ₀ : ℝ := min 1 (1 / (2 * (K + 1))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min zero_lt_one (by positivity)
  -- the key step, for an arbitrary such field and flow function
  have key : ∀ (Y : E → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y →
      (∀ z, ‖fderiv ℝ Y z‖ ≤ K) → ∀ (Ψ : ℝ → E → E),
      (∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => Y z) ∧ γ t = Ψ t y) →
      ∀ t : ℝ, 0 ≤ t → t < δ₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ t) := by
    intro Y hY hKY Ψ hΨ t ht0 htδ
    refine contDiff_iff_forall_nat_le.mpr (fun m _ => ?_)
    have h1 : ContDiff ℝ 1 (Ψ t) :=
      contDiff_iff_contDiffAt.mpr (fun y =>
        contDiffAt_timeSlice Y hY hKY Ψ hΨ 1 le_rfl y ht0 htδ)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      exact h1.of_le (by norm_num)
    · exact contDiff_iff_contDiffAt.mpr (fun y =>
        contDiffAt_timeSlice Y hY hKY Ψ hΨ m hmpos y ht0 htδ)
  -- the reversed field
  have hKneg : ∀ z, ‖fderiv ℝ (fun z : E => -X z) z‖ ≤ K := by
    intro z
    have h : fderiv ℝ (fun z : E => -X z) z = -fderiv ℝ X z := by
      simpa using fderiv_neg (𝕜 := ℝ) (f := X) (x := z)
    rw [h, norm_neg]
    exact hK z
  have hΦneg : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧
      IsIntegralCurve γ (fun _ z => -X z) ∧ γ t = (fun r y => Φ (-r) y) t y := by
    intro t y
    obtain ⟨γ, hγ0, hγint, hγval⟩ := hΦ (-t) y
    refine ⟨fun s => γ (-1 * s), ?_, ?_, ?_⟩
    · simpa using hγ0
    · have hfield : ((-1 : ℝ) • (fun (_ : ℝ) (z : E) => X z))
          = (fun (_ : ℝ) (z : E) => -X z) := by
        funext r z
        simp
      have hfield3 : ((-1 : ℝ) • ((fun (_ : ℝ) (z : E) => X z) ∘ (fun x : ℝ => x * -1)))
          = (fun (_ : ℝ) (z : E) => -X z) := by
        funext r z
        simp [Function.comp_def]
      have h := hγint.comp_mul (-1)
      rw [hfield3] at h
      simpa [Function.comp_def, mul_comm] using h
    · show γ (-1 * t) = Φ (-t) y
      rw [neg_one_mul]
      exact hγval
  refine ⟨δ₀ / 2, by positivity, fun t ht => ?_⟩
  rw [abs_le] at ht
  rcases le_or_gt 0 t with ht0 | ht0
  · exact key X hX hK Φ hΦ t ht0 (by linarith [ht.2])
  · have ht' : -t < δ₀ := by linarith [ht.1]
    have h := key (fun z : E => -X z) (hX.neg) hKneg (fun r y => Φ (-r) y) hΦneg (-t)
      (by linarith) ht'
    simpa [neg_neg] using h

end Crux

end Work.RPCore.Port.ODE
