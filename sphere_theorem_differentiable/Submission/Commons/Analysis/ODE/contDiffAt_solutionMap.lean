import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped ContDiff
open Set Filter Asymptotics Metric
open scoped Topology

namespace Commons.Analysis.ODE

universe u

namespace SmoothDep

abbrev K : Set ℝ := Set.Icc 0 1

lemma K_compact : IsCompact K := isCompact_Icc

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## The Nemitskii operator -/

noncomputable def nem (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) : C(K, E) → C(K, G) :=
  fun γ => ⟨fun σ => h (σ, γ σ), by
    have h1 : Continuous fun σ : K => ((σ:ℝ), γ σ) := by fun_prop
    exact hh.continuous.comp h1⟩

lemma nem_apply (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) (γ : C(K,E)) (σ : K) :
    nem G h hh γ σ = h (σ, γ σ) := rfl

noncomputable def mulLin (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (C(K, E →L[ℝ] G)) →ₗ[ℝ] (C(K, E) →ₗ[ℝ] C(K, G)) where
  toFun A :=
    { toFun := fun δ => ⟨fun σ => A σ (δ σ), by
        exact Continuous.clm_apply (𝕜 := ℝ) A.continuous δ.continuous⟩
      map_add' := by
        intro δ₁ δ₂
        ext σ
        change A σ ((δ₁ + δ₂) σ) = A σ (δ₁ σ) + A σ (δ₂ σ)
        rw [ContinuousMap.add_apply]
        exact (A σ).map_add _ _
      map_smul' := by
        intro c δ
        ext σ
        change A σ ((c • δ) σ) = c • (A σ (δ σ))
        rw [ContinuousMap.smul_apply]
        exact (A σ).map_smul _ _ }
  map_add' := by intro A B; ext δ σ; change (A σ + B σ) (δ σ) = A σ (δ σ) + B σ (δ σ); rfl
  map_smul' := by intro c A; ext δ σ; change (c • A σ) (δ σ) = c • (A σ (δ σ)); rfl

lemma mulLin_apply (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : C(K, E →L[ℝ] G)) (δ : C(K,E)) (σ : K) :
    mulLin G A δ σ = A σ (δ σ) := rfl

lemma mulLin_bound (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : C(K, E →L[ℝ] G)) (δ : C(K, E)) :
    ‖mulLin G A δ‖ ≤ ‖A‖ * ‖δ‖ := by
  exact (ContinuousMap.norm_le _ (by positivity)).mpr (fun σ => by
    calc ‖(mulLin G A δ) σ‖ = ‖A σ (δ σ)‖ := rfl
      _ ≤ ‖A σ‖ * ‖δ σ‖ := (A σ).le_opNorm (δ σ)
      _ ≤ ‖A‖ * ‖δ‖ := mul_le_mul (ContinuousMap.norm_coe_le_norm A σ)
            (ContinuousMap.norm_coe_le_norm δ σ) (norm_nonneg (δ σ)) (norm_nonneg A))

noncomputable def mulClm (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    C(K, E →L[ℝ] G) →L[ℝ] (C(K, E) →L[ℝ] C(K, G)) :=
  LinearMap.mkContinuous
    { toFun := fun A => LinearMap.mkContinuous (mulLin G A) ‖A‖ (mulLin_bound G A)
      map_add' := by
        intro A B
        ext δ σ
        simp only [LinearMap.mkContinuous_apply]
        show ((A + B) σ) (δ σ) = ((A σ) (δ σ) + (B σ) (δ σ))
        rfl
      map_smul' := by
        intro c A
        ext δ σ
        simp only [LinearMap.mkContinuous_apply]
        show ((c • A) σ) (δ σ) = c • ((A σ) (δ σ))
        rfl }
    1 (by
      intro A
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      · intro δ
        change ‖(LinearMap.mkContinuous (mulLin G A) ‖A‖ (mulLin_bound G A)) δ‖ ≤ ‖A‖ * ‖δ‖
        rw [LinearMap.mkContinuous_apply]
        exact mulLin_bound G A δ)

lemma mulClm_apply (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : C(K, E →L[ℝ] G)) (δ : C(K,E)) :
    mulClm G A δ = mulLin G A δ := by
  show (LinearMap.mkContinuous (mulLin G A) ‖A‖ (mulLin_bound G A)) δ = mulLin G A δ
  rw [LinearMap.mkContinuous_apply]

noncomputable def D2 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) : ℝ × E → (E →L[ℝ] G) :=
  fun p => fderiv ℝ (fun y => h (p.1, y)) p.2

lemma D2_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (σ : ℝ) (y : E) :
    D2 h (σ, y) = fderiv ℝ (fun y' => h (σ, y')) y := rfl

lemma fderiv_snd_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) (σ : ℝ) (y : E) :
    fderiv ℝ (fun y' => h (σ, y')) y = (fderiv ℝ h (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hf : HasFDerivAt h (fderiv ℝ h (σ, y)) (σ, y) :=
    (hh.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg : HasFDerivAt (fun y' : E => ((σ, y') : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right σ y
  exact (hf.comp y hg).fderiv

lemma D2_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) :
    D2 h = fun p : ℝ × E => (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  funext p
  obtain ⟨σ, y⟩ := p
  exact (D2_apply h σ y).trans (fderiv_snd_eq h hh σ y)

theorem D2_contDiff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (D2 h) := by
  rw [D2_eq h hh]
  have h1 : ContDiff ℝ ∞ (fderiv ℝ h) := by
    apply hh.fderiv_right (m := ∞) (n := ∞)
    simp
  have h2 : ContDiff ℝ ∞ (fun _ : ℝ × E => (ContinuousLinearMap.inr ℝ ℝ E : E →L[ℝ] (ℝ × E))) :=
    contDiff_const
  exact h1.clm_comp h2

theorem exists_pos_forall_dist_le {α : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
    {E : Type*} [NormedAddCommGroup E]
    {G : Type*} [PseudoMetricSpace G]
    (γ : α → E) (hγ : Continuous γ) (Ψ : α × E → G) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ (a : α) (y : E), dist y (γ a) ≤ r → dist (Ψ (a, y)) (Ψ (a, γ a)) ≤ ε := by
  let Z : Set (α × E) := {p | ε ≤ dist (Ψ p) (Ψ (p.1, γ p.1))}
  have hZc : IsClosed Z := isClosed_le continuous_const
    (hΨ.dist (hΨ.comp (continuous_fst.prodMk (hγ.comp continuous_fst))))
  by_cases hempty : Z = ∅
  · refine ⟨1, one_pos, fun a y _ => ?_⟩
    have h : (a, y) ∉ Z := by rw [hempty]; exact Set.notMem_empty _
    exact le_of_lt (not_le.mp h)
  · have hne : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    have hL : IsCompact (Set.range fun a : α => (a, γ a)) :=
      isCompact_range (continuous_id.prodMk hγ)
    have hLne : (Set.range fun a : α => (a, γ a)).Nonempty :=
      ⟨(Classical.arbitrary α, γ (Classical.arbitrary α)), ⟨_, rfl⟩⟩
    have hcont : Continuous fun p : α × E => infDist p Z := Metric.continuous_infDist_pt Z
    obtain ⟨p₀, hp₀L, hp₀min⟩ := hL.exists_isMinOn hLne hcont.continuousOn
    have hp₀pos : 0 < infDist p₀ Z := by
      refine (Metric.infDist_pos_iff_notMem_closure hne).mp ?_
      intro hmem
      rw [hZc.closure_eq] at hmem
      obtain ⟨a, ha⟩ := hp₀L
      have hpa : p₀ = (a, γ a) := ha.symm
      have hd : dist (Ψ p₀) (Ψ (p₀.1, γ p₀.1)) = 0 := by
        rw [hpa]; simp
      simp only [Z, mem_setOf_eq] at hmem
      rw [hd] at hmem
      linarith
    refine ⟨infDist p₀ Z / 2, half_pos hp₀pos, fun a y hy => ?_⟩
    by_contra hcon
    have hyZ : (a, y) ∈ Z := le_of_lt (not_le.mp hcon)
    have h1 : infDist p₀ Z ≤ infDist (a, γ a) Z := hp₀min (show (a, γ a) ∈ _ from ⟨a, rfl⟩)
    have h2 : infDist (a, γ a) Z ≤ dist (a, γ a) (a, y) := Metric.infDist_le_dist_of_mem hyZ
    have h3 : dist (a, γ a) (a, y) = dist (γ a) y := by rw [Prod.dist_eq]; simp
    have h4 : infDist p₀ Z ≤ dist (γ a) y := by rw [← h3]; exact h1.trans h2
    rw [dist_comm] at hy
    linarith [hy, h4, hp₀pos]

set_option maxHeartbeats 800000 in
theorem nem_hasFDerivAt (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) (γ : C(K, E)) :
    HasFDerivAt (nem G h hh) (mulClm G (nem (E →L[ℝ] G) (D2 h) (D2_contDiff h hh) γ)) γ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hr'⟩ := exists_pos_forall_dist_le (G := E →L[ℝ] G) (fun σ : K => γ σ) γ.continuous
      (fun p : K × E => D2 h (p.1, p.2))
      ((D2_contDiff h hh).continuous.comp (by fun_prop : Continuous fun p : K × E => ((p.1:ℝ), p.2)))
      (ε := ε) hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hr] with δ hδ
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro σ
  have hδ' : ‖δ‖ < r := by simpa [dist_eq_norm] using hδ
  have hcomp : (nem G h hh (γ + δ) - nem G h hh γ
      - mulClm G (nem (E →L[ℝ] G) (D2 h) (D2_contDiff h hh) γ) δ) σ
      = h (σ, γ σ + δ σ) - h (σ, γ σ) - D2 h (σ, γ σ) (δ σ) := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, nem_apply, mulClm_apply,
      mulLin_apply]
  rw [hcomp]
  have hdiff : ∀ y ∈ Metric.closedBall (γ σ) ‖δ‖, DifferentiableAt ℝ (fun y : E => h (σ, y)) y :=
    fun y hy => (hh.contDiffAt (x := ((σ:ℝ), y))).differentiableAt (by simp) |>.comp y
      (by fun_prop)
  have hbound : ∀ y ∈ Metric.closedBall (γ σ) ‖δ‖,
      ‖fderiv ℝ (fun y : E => h (σ, y)) y - D2 h (σ, γ σ)‖ ≤ ε := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hdd : dist y ((fun σ : K => γ σ) σ) ≤ r := by
      rw [dist_eq_norm]
      exact le_of_lt (lt_of_le_of_lt hy hδ')
    simpa [dist_eq_norm, D2_apply] using hr' σ y hdd
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
    (f := fun y : E => h (σ, y)) (φ := D2 h (σ, γ σ)) (C := ε)
    (s := Metric.closedBall (γ σ) ‖δ‖) hdiff hbound
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg δ))
    (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        exact ContinuousMap.norm_coe_le_norm δ σ)
  rw [show (γ σ + δ σ) - γ σ = δ σ from by abel] at hmvt
  calc ‖h (σ, γ σ + δ σ) - h (σ, γ σ) - D2 h (σ, γ σ) (δ σ)‖
      ≤ ε * ‖δ σ‖ := hmvt
    _ ≤ ε * ‖δ‖ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm δ σ) hε.le

set_option maxHeartbeats 800000 in
theorem nem_contDiff (n : ℕ) :
    ∀ (G' : Type u) [NormedAddCommGroup G'] [NormedSpace ℝ G']
      (h : ℝ × E → G') (hh : ContDiff ℝ ∞ h), ContDiff ℝ n (nem G' h hh) := by
  induction n with
  | zero =>
    intro G' _ _ h hh
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun γ =>
      (nem_hasFDerivAt G' h hh γ).continuousAt)
  | succ n ih =>
    intro G' _ _ h hh
    have hcast : (↑(n+1) : ℕ∞ω) = (↑n + 1 : ℕ∞ω) := by push_cast; ring
    rw [hcast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun γ => mulClm G' (nem (E →L[ℝ] G') (D2 h) (D2_contDiff h hh) γ), ?_,
      fun γ => nem_hasFDerivAt G' h hh γ⟩
    have hmul : ContDiff ℝ n (mulClm G' (E := E)) := ContinuousLinearMap.contDiff _
    have hih : ContDiff ℝ n (nem (E →L[ℝ] G') (D2 h) (D2_contDiff h hh)) :=
      ih (G' := E →L[ℝ] G') (h := D2 h) (hh := D2_contDiff h hh)
    exact hmul.comp hih

theorem contDiff_nemitskii (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : ℝ × E → G) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (nem G h hh) := by
  rw [contDiff_infty]
  intro n
  exact nem_contDiff (E := E) n G h hh


/-! ### integration -/

def clampK (r : ℝ) : K := ⟨min 1 (max 0 r), by
  constructor
  · exact le_min zero_le_one (le_max_left 0 r)
  · exact min_le_left 1 (max 0 r)⟩

lemma continuous_clampK : Continuous clampK := by
  apply Continuous.subtype_mk
  fun_prop

lemma clampK_coe (σ : K) : clampK (σ : ℝ) = σ := by
  ext
  simp only [clampK]
  rw [max_eq_right σ.2.1, min_eq_right σ.2.2]

lemma clampK_of_mem {r : ℝ} (hr : r ∈ K) : clampK r = ⟨r, hr⟩ := by
  ext
  simp only [clampK]
  rw [max_eq_right hr.1, min_eq_right hr.2]

lemma continuous_comp_clampK (w : C(K,E)) : Continuous fun r : ℝ => w (clampK r) :=
  w.continuous.comp continuous_clampK

noncomputable def IntLin : C(K,E) →ₗ[ℝ] C(K,E) where
  toFun w := ⟨fun σ => ∫ r in (0:ℝ)..(σ:ℝ), w (clampK r), by
    have h1 : Continuous fun b : ℝ => ∫ r in (0:ℝ)..b, w (clampK r) :=
      intervalIntegral.continuous_primitive (fun a b => (continuous_comp_clampK w).intervalIntegrable a b) 0
    exact h1.comp continuous_subtype_val⟩
  map_add' := by
    intro w₁ w₂
    ext σ
    simp only [ContinuousMap.add_apply]
    exact intervalIntegral.integral_add ((continuous_comp_clampK w₁).intervalIntegrable _ _)
      ((continuous_comp_clampK w₂).intervalIntegrable _ _)
  map_smul' := by
    intro c w
    ext σ
    simp only [ContinuousMap.smul_apply]
    exact intervalIntegral.integral_smul c (fun r => w (clampK r))

noncomputable def IntCLM : C(K,E) →L[ℝ] C(K,E) :=
  LinearMap.mkContinuous IntLin 1 (by
    intro w
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
    intro σ
    calc ‖∫ r in (0:ℝ)..(σ:ℝ), w (clampK r)‖ ≤ ‖w‖ * |(σ:ℝ) - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x hx
          exact ContinuousMap.norm_coe_le_norm w (clampK x)
      _ = ‖w‖ * (σ:ℝ) := by rw [sub_zero, abs_of_nonneg σ.2.1]
      _ ≤ ‖w‖ * 1 := by gcongr; exact σ.2.2
      _ = ‖w‖ := mul_one _)

/-! ### multiplication by a continuous function -/

noncomputable def smulBy (g : C(K,ℝ)) : C(K,E) →L[ℝ] C(K,E) :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟨fun σ => g σ • w σ, by
        exact Continuous.smul (g.continuous) (w.continuous)⟩
      map_add' := by intro w₁ w₂; ext σ; rw [ContinuousMap.add_apply]; exact smul_add _ _ _
      map_smul' := by intro c w; ext σ; rw [ContinuousMap.smul_apply]; exact smul_comm _ _ _ }
    ‖g‖ (by
      intro w
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg g) (norm_nonneg w))).mpr
      intro σ
      calc ‖g σ • w σ‖ = ‖g σ‖ * ‖w σ‖ := norm_smul _ _
        _ ≤ ‖g‖ * ‖w‖ := by
            gcongr
            · exact ContinuousMap.norm_coe_le_norm g σ
            · exact ContinuousMap.norm_coe_le_norm w σ)

/-! ### constant and pair maps -/

noncomputable def constFun (x : E) : C(K,E) := ⟨fun _ => x, continuous_const⟩
lemma constFun_apply (x : E) (σ : K) : constFun x σ = x := rfl

noncomputable def constCLM : E →L[ℝ] C(K,E) :=
  LinearMap.mkContinuous
    { toFun := constFun
      map_add' := by
        intro x y
        ext σ
        simp only [ContinuousMap.add_apply, constFun, ContinuousMap.coe_mk]
      map_smul' := by
        intro c x
        ext σ
        simp only [ContinuousMap.smul_apply, constFun, ContinuousMap.coe_mk, RingHom.id_apply] }
    1 (by
      intro x
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro σ
      change ‖constFun x σ‖ ≤ ‖x‖
      rw [constFun_apply])

noncomputable def pairFun (w : C(K,E)) : C(K, ℝ×E) :=
  ⟨fun σ => (0, w σ), continuous_const.prodMk w.continuous⟩
lemma pairFun_apply (w : C(K,E)) (σ : K) : pairFun w σ = (0, w σ) := rfl

noncomputable def pairE : C(K,E) →L[ℝ] C(K, ℝ × E) :=
  LinearMap.mkContinuous
    { toFun := pairFun
      map_add' := by
        intro w₁ w₂
        ext σ
        · simp [pairFun]
        · simp [pairFun, ContinuousMap.add_apply]
      map_smul' := by
        intro c w
        ext σ
        · simp [pairFun]
        · simp [pairFun, ContinuousMap.smul_apply] }
    1 (by
      intro w
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
      intro σ
      change ‖pairFun w σ‖ ≤ ‖w‖
      rw [pairFun_apply, Prod.norm_def]
      exact max_le (by simp) (ContinuousMap.norm_coe_le_norm w σ))

/-! ### the map (t,eta) |-> (sigma |-> (t, e^{lam sigma} eta sigma)) -/

noncomputable def expFun (lam : ℝ) : C(K, ℝ) := ⟨fun σ => Real.exp (lam * (σ:ℝ)), by fun_prop⟩
noncomputable def expFunNeg (lam : ℝ) : C(K, ℝ) := ⟨fun σ => Real.exp (-(lam * (σ:ℝ))), by fun_prop⟩

noncomputable def combFun (p : ℝ × C(K,E)) : C(K, ℝ × E) :=
  ⟨fun σ => (p.1, p.2 σ), continuous_const.prodMk p.2.continuous⟩
lemma combFun_apply (p : ℝ × C(K,E)) (σ : K) :
    combFun p σ = (p.1, p.2 σ) := rfl

noncomputable def comb (lam : ℝ) : ℝ × C(K,E) →L[ℝ] C(K, ℝ × E) :=
  LinearMap.mkContinuous
    { toFun := combFun
      map_add' := by
        intro p q
        ext σ <;> simp only [combFun_apply, ContinuousMap.add_apply, Prod.fst_add, Prod.snd_add,
          Prod.mk_add_mk]
      map_smul' := by
        intro c p
        ext σ <;> simp only [combFun_apply, ContinuousMap.smul_apply, Prod.smul_fst, Prod.smul_snd,
          Prod.smul_mk, RingHom.id_apply, smul_eq_mul] }
    1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro σ
      change ‖combFun p σ‖ ≤ ‖p‖
      rw [combFun_apply, Prod.norm_def]
      exact max_le (le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) le_rfl)
        (le_trans (ContinuousMap.norm_coe_le_norm p.2 σ) (by rw [Prod.norm_def]; exact le_max_right _ _)))

lemma comb_apply (lam : ℝ) (t : ℝ) (η : C(K,E)) (σ : K) :
    comb (E := E) lam (t, η) σ = (t, η σ) := by
  show combFun (t, η) σ = _
  rw [combFun_apply]

noncomputable def emb (lam : ℝ) : C(K,E) →L[ℝ] C(K, ℝ × E) :=
  (comb (E := E) lam).comp (ContinuousLinearMap.inr ℝ ℝ C(K,E))

lemma emb_apply (lam : ℝ) (η : C(K,E)) (σ : K) :
    emb (E := E) lam η σ = (0, η σ) := by
  simp only [emb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, comb_apply]

/-! ### h -/

noncomputable def hfun (lam : ℝ) (f : ℝ → E → E) : ℝ × (ℝ × E) → E :=
  fun p => p.2.1 • f (p.2.1 * p.1) (Real.exp (lam * p.1) • p.2.2)

lemma hfun_contDiff (lam : ℝ) {f : ℝ → E → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) : ContDiff ℝ ∞ (hfun (E := E) lam f) := by
  unfold hfun; fun_prop



/-! ### Invertibility of `1 - L` for `‖L‖ < 1` -/

theorem isInvertible_one_sub {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (L : X →L[ℝ] X) (hL : ‖L‖ < 1) : (1 - L).IsInvertible := by
  let u := Units.oneSub L hL
  have hu : (u : X →L[ℝ] X) = 1 - L := Units.val_oneSub L hL
  refine ⟨ContinuousLinearEquiv.equivOfInverse (u : X →L[ℝ] X) (↑u⁻¹) ?_ ?_, hu.symm⟩
  · intro x
    rw [← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  · intro x
    rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]

/-! ### The equation and its smoothness -/

noncomputable def Mlam (lam : ℝ) : C(K,E) →L[ℝ] C(K,E) := smulBy (expFunNeg lam)

noncomputable def Phieq (lam : ℝ) (h : ℝ × (ℝ × E) → E) (hh : ContDiff ℝ ∞ h) :
    (E × ℝ) × C(K,E) → C(K,E) :=
  fun p => Mlam lam (IntCLM (nem (E := ℝ × E) E h hh (comb lam (p.1.2, p.2))))

noncomputable def Feq (lam : ℝ) (h : ℝ × (ℝ × E) → E) (hh : ContDiff ℝ ∞ h) :
    (E × ℝ) × C(K,E) → C(K,E) :=
  fun p => p.2 - Mlam lam (constCLM p.1.1) - Phieq lam h hh p

theorem Phieq_contDiff (lam : ℝ) (h : ℝ × (ℝ × E) → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (Phieq (E := E) lam h hh) := by
  have h1 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) => (p.1.2, p.2)) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) => comb (E := E) lam (p.1.2, p.2)) :=
    ((comb (E := E) lam).contDiff.comp h1)
  have h3 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) =>
      nem (E := ℝ × E) E h hh (comb (E := E) lam (p.1.2, p.2))) :=
    (contDiff_nemitskii (E := ℝ × E) E h hh).comp h2
  have h4 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) =>
      IntCLM (nem (E := ℝ × E) E h hh (comb (E := E) lam (p.1.2, p.2)))) := by
    simpa only [Function.comp_def] using IntCLM.contDiff.comp h3
  have h5 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) =>
      Mlam lam (IntCLM (nem (E := ℝ × E) E h hh (comb (E := E) lam (p.1.2, p.2))))) := by
    simpa only [Function.comp_def] using (Mlam lam).contDiff.comp h4
  exact h5

theorem Feq_contDiff (lam : ℝ) (h : ℝ × (ℝ × E) → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (Feq (E := E) lam h hh) := by
  have h1 : ContDiff ℝ ∞ (Phieq (E := E) lam h hh) := Phieq_contDiff lam h hh
  have h2 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) => Mlam (E := E) lam (constCLM p.1.1)) := by
    fun_prop
  have h3 : ContDiff ℝ ∞ (fun p : (E × ℝ) × C(K,E) => p.2) := by fun_prop
  have h4 : ContDiff ℝ ∞ (Feq (E := E) lam h hh) := by
    rw [show Feq (E := E) lam h hh = (fun p : (E × ℝ) × C(K,E) =>
      p.2 - Mlam lam (constCLM p.1.1) - Phieq lam h hh p) from rfl]
    exact (h3.sub h2).sub h1
  exact h4



lemma smulBy_apply (g : C(K,ℝ)) (w : C(K,E)) (σ : K) : smulBy g w σ = g σ • w σ := rfl
lemma IntCLM_apply (w : C(K,E)) (σ : K) :
    IntCLM w σ = ∫ r in (0:ℝ)..(σ:ℝ), w (clampK r) := rfl
lemma Mlam_apply (lam : ℝ) (w : C(K,E)) (σ : K) :
    Mlam lam w σ = Real.exp (-(lam * (σ:ℝ))) • w σ := by
  simp only [Mlam, smulBy_apply, expFunNeg, ContinuousMap.coe_mk]
lemma constCLM_apply (x : E) (σ : K) : constCLM x σ = x := rfl
lemma expFun_apply (lam : ℝ) (σ : K) : expFun lam σ = Real.exp (lam * (σ:ℝ)) := rfl
lemma expFunNeg_apply (lam : ℝ) (σ : K) : expFunNeg lam σ = Real.exp (-(lam * (σ:ℝ))) := rfl

lemma integral_exp_mul (lam : ℝ) (hlam : lam ≠ 0) (a b : ℝ) :
    ∫ r in a..b, Real.exp (lam * r) = (Real.exp (lam * b) - Real.exp (lam * a)) / lam := by
  have hderiv : ∀ r : ℝ, HasDerivAt (fun u : ℝ => Real.exp (lam * u) / lam) (Real.exp (lam * r)) r := by
    intro r
    have h1 : HasDerivAt (fun u : ℝ => lam * u) lam r := hasDerivAt_const_mul lam
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (lam * u)) (Real.exp (lam * r) * lam) r :=
      (Real.hasDerivAt_exp (lam * r)).comp r h1
    have h4 := h3.div_const lam
    rwa [mul_div_cancel_right₀ _ hlam] at h4
  have hint : IntervalIntegrable (fun r : ℝ => Real.exp (lam * r)) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hderiv r) hint]
  ring


variable {f : ℝ → E → E} {a b : ℝ} {u : E → ℝ → E} {t₀ : ℝ}

lemma t_mul_mem_Ioo (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Ioo a b)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : t₀ * r ∈ Ioo a b := by
  have hmin : a < min 0 t₀ := lt_min ha ht₀.1
  have hmax : max 0 t₀ < b := max_lt hb ht₀.2
  have hmem : t₀ * r ∈ Icc (min 0 t₀) (max 0 t₀) := by
    rcases le_total 0 t₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact ⟨by nlinarith [hr.1, hr.2], by nlinarith [hr.1, hr.2]⟩
    · rw [min_eq_right h, max_eq_left h]
      exact ⟨by nlinarith [hr.1, hr.2], by nlinarith [hr.1, hr.2]⟩
  exact ⟨lt_of_lt_of_le hmin hmem.1, lt_of_le_of_lt hmem.2 hmax⟩

lemma hasDerivAt_gammaR (hode : ∀ x : E, ∀ t ∈ Ioo a b, HasDerivAt (u x) (f t (u x t)) t)
    (x₀ : E) {t₀ r : ℝ} (hr : t₀ * r ∈ Ioo a b) :
    HasDerivAt (fun r : ℝ => u x₀ (t₀ * r)) (t₀ • f (t₀ * r) (u x₀ (t₀ * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => t₀ * r) t₀ r := hasDerivAt_const_mul t₀
  have h2 := ((hode x₀ (t₀ * r) hr).hasFDerivAt).comp_hasDerivAt r h1
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h2

lemma gamma0_continuous (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Ioo a b)
    (hode : ∀ x : E, ∀ t ∈ Ioo a b, HasDerivAt (u x) (f t (u x t)) t) (x₀ : E) :
    Continuous fun σ : K => u x₀ (t₀ * (σ:ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  exact ((hasDerivAt_gammaR hode x₀ (t_mul_mem_Ioo ha hb ht₀ σ.2)).continuousAt).comp
    continuous_subtype_val.continuousAt

lemma gammaR_integral (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Ioo a b)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (hode : ∀ x : E, ∀ t ∈ Ioo a b, HasDerivAt (u x) (f t (u x t)) t)
    (hu0 : ∀ x : E, u x 0 = x) (x₀ : E) {σ : ℝ} (hσ : σ ∈ K) :
    ∫ r in (0:ℝ)..σ, t₀ • f (t₀ * r) (u x₀ (t₀ * r)) = u x₀ (t₀ * σ) - x₀ := by
  have hle : (0:ℝ) ≤ σ := hσ.1
  have hderiv' : ∀ r ∈ Icc (0:ℝ) σ, HasDerivAt (fun r : ℝ => u x₀ (t₀ * r))
      (t₀ • f (t₀ * r) (u x₀ (t₀ * r))) r := by
    intro r hr
    exact hasDerivAt_gammaR hode x₀ (t_mul_mem_Ioo ha hb ht₀ ⟨hr.1, le_trans hr.2 hσ.2⟩)
  have hcont : ContinuousOn (fun r : ℝ => u x₀ (t₀ * r)) (Icc 0 σ) :=
    HasDerivAt.continuousOn hderiv'
  have hint : IntervalIntegrable (fun r : ℝ => t₀ • f (t₀ * r) (u x₀ (t₀ * r))) MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    have h1 : ContinuousOn (fun r : ℝ => ((t₀ * r), u x₀ (t₀ * r))) (uIcc 0 σ) := by
      refine ContinuousOn.prodMk ?_ ?_
      · exact (continuous_const.mul continuous_id).continuousOn
      · exact hcont.mono (by rw [uIcc_of_le hle])
    exact (continuous_const.smul hf.continuous).comp_continuousOn h1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
      (fun r hr => hderiv' r ⟨le_of_lt hr.1, le_of_lt hr.2⟩) hint
  rw [h, mul_zero, hu0 x₀]

lemma D2_hfun (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) (lam t σ : ℝ) (y v : E) :
    D2 (hfun (E:=E) lam f) (σ, (t, y)) (0, v)
      = t • (D2 (fun p : ℝ × E => f p.1 p.2) (t * σ, Real.exp (lam * σ) • y))
          (Real.exp (lam * σ) • v) := by
  set f' : ℝ × E → E := fun p => f p.1 p.2 with hf'm
  set ψ : ℝ × E → ℝ × E := fun q => (q.1 * σ, Real.exp (lam * σ) • q.2) with hψm
  have hfd : HasFDerivAt f' (fderiv ℝ f' (ψ (t,y))) (ψ (t,y)) :=
    ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h1 : HasFDerivAt (fun q : ℝ × E => q.1 * σ) (σ • ContinuousLinearMap.fst ℝ ℝ E) (t,y) :=
    hasFDerivAt_fst.mul_const σ
  have h2 : HasFDerivAt (fun q : ℝ × E => Real.exp (lam * σ) • q.2)
      (Real.exp (lam * σ) • ContinuousLinearMap.snd ℝ ℝ E) (t,y) :=
    hasFDerivAt_snd.const_smul (Real.exp (lam * σ))
  have hψ : HasFDerivAt ψ ((σ • ContinuousLinearMap.fst ℝ ℝ E).prod
      (Real.exp (lam * σ) • ContinuousLinearMap.snd ℝ ℝ E)) (t,y) := h1.prodMk h2
  have hg := hfd.comp (t,y) hψ
  have hsm := (hasFDerivAt_fst (p := (t,y))).smul hg
  have heq : (fun p : ℝ × E => hfun (E:=E) lam f (σ, p)) = fun q => q.1 • (f' ∘ ψ) q := by
    funext q
    simp only [hfun, hf'm, hψm, Function.comp_apply]
  rw [D2_apply, heq]
  rw [show (fun q : ℝ × E => q.1 • (f' ∘ ψ) q) = ((Prod.fst : ℝ × E → ℝ) • (f' ∘ ψ)) from rfl,
    hsm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, hψm, Function.comp_apply, D2_apply]
  rw [fderiv_snd_eq f' hf (t * σ) (Real.exp (lam * σ) • y)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  simp


end SmoothDep

open SmoothDep

open scoped Classical in
theorem contDiffAt_solutionMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {u : E → ℝ → E} (hu0 : ∀ x : E, u x 0 = x)
    (hode : ∀ x : E, ∀ t ∈ Set.Ioo a b, HasDerivAt (u x) (f t (u x t)) t)
    (huniq : ∀ x : E, ∀ y : ℝ → E, (∀ t ∈ Set.Ioo a b, HasDerivAt y (f t (y t)) t) → y 0 = x →
      ∀ t ∈ Set.Ioo a b, y t = u x t)
    (x₀ : E) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    ContDiffAt ℝ ∞ (fun p : E × ℝ => u p.1 p.2) (x₀, t₀) := by
  classical
  have hf' : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2) := hf
  set γ₀ : C(K,E) := ⟨fun σ => u x₀ (t₀ * (σ:ℝ)), gamma0_continuous ha hb ht₀ hode x₀⟩ with hγ₀def
  have hγ₀ : ∀ σ : K, γ₀ σ = u x₀ (t₀ * (σ:ℝ)) := fun σ => rfl
  have hDccont : Continuous fun σ : K => D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ) :=
    ((D2_contDiff (fun p : ℝ × E => f p.1 p.2) hf').continuous.comp
      (by fun_prop : Continuous fun σ : K => ((t₀*(σ:ℝ)), γ₀ σ)))
  set Dc : C(K, E →L[ℝ] E) := ⟨fun σ => D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ), hDccont⟩
    with hDcdef
  set C₀ : ℝ := ‖Dc‖ with hC₀def
  have hDcbound : ∀ σ : K, ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀*(σ:ℝ), γ₀ σ)‖ ≤ C₀ :=
    fun σ => ContinuousMap.norm_coe_le_norm Dc σ
  have hC₀nn : 0 ≤ C₀ := hC₀def.symm ▸ norm_nonneg Dc
  set lam : ℝ := 1 + |t₀| * C₀ with hlamdef
  have hlam_pos : 0 < lam := by rw [hlamdef]; positivity
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam_gt : |t₀| * C₀ < lam := by rw [hlamdef]; linarith
  have hh : ContDiff ℝ ∞ (hfun lam f) := hfun_contDiff lam hf
  set η₀ : C(K,E) := Mlam lam γ₀ with hη₀def
  set u0 : E × ℝ := (x₀, t₀) with hu0def
  set p₀ : (E × ℝ) × C(K,E) := (u0, η₀) with hp₀def
  have hbase : Feq lam (hfun lam f) hh p₀ = 0 := by
    ext σ
    have h1 : (Feq lam (hfun lam f) hh p₀) σ
        = η₀ σ - Real.exp (-(lam * (σ:ℝ))) • x₀
          - Real.exp (-(lam * (σ:ℝ))) • ∫ r in (0:ℝ)..(σ:ℝ),
              (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r) := by
      simp only [Feq, Phieq, ContinuousMap.sub_apply, Mlam_apply, constCLM_apply,
        IntCLM_apply, hp₀def, hu0def]
    rw [h1]
    have hcongr : ∫ r in (0:ℝ)..(σ:ℝ),
          (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r)
        = ∫ r in (0:ℝ)..(σ:ℝ), t₀ • f (t₀ * r) (u x₀ (t₀ * r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le σ.2.1] at hr
      have hrK : r ∈ K := ⟨hr.1, le_trans hr.2 σ.2.2⟩
      show (nem (E := ℝ×E) E (hfun lam f) hh (comb lam (t₀, η₀))) (clampK r)
        = t₀ • f (t₀ * r) (u x₀ (t₀ * r))
      rw [nem_apply, comb_apply, clampK_of_mem hrK]
      simp only [hfun, Subtype.coe_mk]
      congr 1
      rw [hη₀def, Mlam_apply]
      simp only [Subtype.coe_mk]
      rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
      exact congrArg (fun z => f (t₀ * r) z) (hγ₀ ⟨r, hrK⟩)
    rw [hcongr, gammaR_integral ha hb ht₀ hf hode hu0 x₀ σ.2]
    rw [hη₀def, Mlam_apply, hγ₀ σ]
    simp only [ContinuousMap.zero_apply]
    rw [smul_sub]
    abel
  set Xc : C(K, (ℝ × E) →L[ℝ] E) := nem (E := ℝ × E) ((ℝ × E) →L[ℝ] E) (D2 (hfun lam f))
    (D2_contDiff (hfun lam f) hh) (comb lam (t₀, η₀)) with hXcdef
  set A : C(K,E) →L[ℝ] C(K,E) :=
    (Mlam lam).comp (IntCLM.comp ((mulClm (E := ℝ × E) (G := E) Xc).comp (emb lam))) with hAdef
  have hA_has : HasFDerivAt (fun η : C(K,E) => Phieq lam (hfun lam f) hh (u0, η)) A η₀ := by
    have hinr : HasFDerivAt (fun η : C(K,E) => (t₀, η)) (ContinuousLinearMap.inr ℝ ℝ C(K,E)) η₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := t₀)).prodMk (hasFDerivAt_id η₀)
    have hcomb : HasFDerivAt (fun η : C(K,E) => comb lam (t₀, η)) (emb lam) η₀ := by
      have hh1 := (comb (E := E) lam).hasFDerivAt.comp η₀ hinr
      simpa only [emb, Function.comp_def] using hh1
    have hnem : HasFDerivAt (fun ζ : C(K, ℝ×E) => nem (E := ℝ×E) E (hfun lam f) hh ζ)
        (mulClm (E := ℝ × E) (G := E) Xc) (comb lam (t₀, η₀)) :=
      nem_hasFDerivAt (E := ℝ×E) (G := E) (hfun lam f) hh (comb lam (t₀, η₀))
    have h4 := hnem.comp η₀ hcomb
    have h5 := IntCLM.hasFDerivAt.comp η₀ h4
    have h6 := (Mlam lam).hasFDerivAt.comp η₀ h5
    simpa only [A, Phieq, Function.comp_def, hu0def, hAdef, hXcdef] using h6
  have hA_pt : ∀ δ : C(K,E), ‖A δ‖ ≤ (|t₀| * C₀ / lam) * ‖δ‖ := by
    intro δ
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro σ
    have hAap : (A δ) σ = Real.exp (-(lam * (σ:ℝ))) • ∫ r in (0:ℝ)..(σ:ℝ),
        Xc (clampK r) ((emb lam δ) (clampK r)) := by
      simp only [A, hAdef, ContinuousLinearMap.comp_apply, Mlam_apply, IntCLM_apply,
        mulClm_apply, mulLin_apply]
    rw [hAap, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hint : IntervalIntegrable (fun r : ℝ => |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖)
        MeasureTheory.volume 0 (σ:ℝ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hle : ‖∫ r in (0:ℝ)..(σ:ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le σ.2.1
      · filter_upwards with r hr
        have hrK : r ∈ K := ⟨le_of_lt hr.1, le_trans hr.2 σ.2.2⟩
        have hXc : Xc (clampK r) = D2 (hfun lam f) (clampK r, (t₀, η₀ (clampK r))) := by
          simp only [Xc, hXcdef, nem_apply, comb_apply]
        rw [hXc, emb_apply, clampK_of_mem hrK]
        simp only [Subtype.coe_mk]
        rw [D2_hfun hf lam t₀ r (η₀ ⟨r, hrK⟩) (δ ⟨r, hrK⟩)]
        have hη : Real.exp (lam * r) • η₀ ⟨r, hrK⟩ = u x₀ (t₀ * r) := by
          rw [hη₀def, Mlam_apply]
          simp only [Subtype.coe_mk]
          rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
          exact hγ₀ ⟨r, hrK⟩
        rw [hη]
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.map_smul, norm_smul,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h1 : ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))‖ ≤ C₀ := by
          have hh1 := hDcbound ⟨r, hrK⟩
          rwa [hγ₀ ⟨r, hrK⟩] at hh1
        have h2 : ‖δ ⟨r, hrK⟩‖ ≤ ‖δ‖ := ContinuousMap.norm_coe_le_norm δ ⟨r, hrK⟩
        have h1' : ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖
            ≤ C₀ * ‖δ‖ := by
          calc ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖
              ≤ ‖D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))‖ * ‖δ ⟨r, hrK⟩‖ :=
                (D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r, u x₀ (t₀ * r))).le_opNorm _
            _ ≤ C₀ * ‖δ‖ := mul_le_mul h1 h2 (norm_nonneg _) hC₀nn
        have h3 : 0 ≤ Real.exp (lam * r) := le_of_lt (Real.exp_pos _)
        have h5 : 0 ≤ |t₀| := abs_nonneg t₀
        calc |t₀| * (Real.exp (lam * r) * ‖(D2 (fun p : ℝ × E => f p.1 p.2) (t₀ * r,
                u x₀ (t₀ * r))) (δ ⟨r, hrK⟩)‖)
            ≤ |t₀| * (Real.exp (lam * r) * (C₀ * ‖δ‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1' h3) h5
          _ = |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by ring
      · exact hint
    have hInt : ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖
        = |t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_exp_mul lam hlam_ne 0 (σ:ℝ)]
      rw [mul_zero, Real.exp_zero]
      ring
    have hexp : Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖)
        = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := by
      have hh1 : Real.exp (-(lam * (σ:ℝ))) * Real.exp (lam * (σ:ℝ)) = 1 := by
        rw [← Real.exp_add]
        have hh2 : -(lam * (σ:ℝ)) + lam * (σ:ℝ) = 0 := by ring
        rw [hh2, Real.exp_zero]
      calc Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖)
          = (Real.exp (-(lam * (σ:ℝ))) * (Real.exp (lam * (σ:ℝ)) - 1)) * (|t₀| * C₀ / lam * ‖δ‖) := by
            ring
        _ = (1 - Real.exp (-(lam * (σ:ℝ)))) * (|t₀| * C₀ / lam * ‖δ‖) := by
            rw [mul_sub, hh1, mul_one]
        _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := by ring
    have h10 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖
        ≤ |t₀| * C₀ / lam * ‖δ‖ := by
      have h12 : (1 - Real.exp (-(lam * (σ:ℝ)))) ≤ 1 := by
        have := Real.exp_pos (-(lam * (σ:ℝ))); linarith
      have h13 : 0 ≤ |t₀| * C₀ := mul_nonneg (abs_nonneg t₀) hC₀nn
      have h14 : 0 ≤ ‖δ‖ := norm_nonneg _
      have hh1 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam ≤ |t₀| * C₀ / lam := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hlam_pos)
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg t₀) hC₀nn) h12
      exact mul_le_mul_of_nonneg_right hh1 h14
    calc Real.exp (-(lam * (σ:ℝ))) * ‖∫ r in (0:ℝ)..(σ:ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ Real.exp (-(lam * (σ:ℝ))) * ∫ r in (0:ℝ)..(σ:ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ :=
          mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(lam * (σ:ℝ))) * (|t₀| * C₀ * (Real.exp (lam * (σ:ℝ)) - 1) / lam * ‖δ‖) := by
          rw [hInt]
      _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ:ℝ)))) / lam * ‖δ‖ := hexp
      _ ≤ |t₀| * C₀ / lam * ‖δ‖ := h10
  have hA_bound : ‖A‖ ≤ |t₀| * C₀ / lam :=
    ContinuousLinearMap.opNorm_le_bound A (by positivity) hA_pt
  have hA_lt : ‖A‖ < 1 := by
    have h1 : |t₀| * C₀ / lam < 1 := by
      rw [div_lt_one hlam_pos]; exact hlam_gt
    linarith
  have hsub : HasFDerivAt (fun η : C(K,E) => Feq lam (hfun lam f) hh (u0, η)) (1 - A) η₀ := by
    have h1 : HasFDerivAt (fun η : C(K,E) => η) (1 : C(K,E) →L[ℝ] C(K,E)) η₀ :=
      hasFDerivAt_id (𝕜 := ℝ) (x := η₀)
    have h2 : HasFDerivAt (fun _ : C(K,E) => Mlam lam (constCLM x₀)) 0 η₀ :=
      hasFDerivAt_const (𝕜 := ℝ) (c := Mlam lam (constCLM x₀)) (x := η₀)
    have h3 := (h1.sub h2).sub hA_has
    have heq : (fun η : C(K,E) => Feq lam (hfun lam f) hh (u0, η))
        = ((fun η : C(K,E) => η) - (fun _ : C(K,E) => Mlam lam (constCLM x₀))
           - (fun η : C(K,E) => Phieq lam (hfun lam f) hh (u0, η))) := by
      funext η
      simp only [Feq, Phieq, hu0def, Pi.sub_apply]
    rw [heq]
    simpa only [sub_zero] using h3
  have hFeq_at : HasFDerivAt (Feq lam (hfun lam f) hh)
      (fderiv ℝ (Feq lam (hfun lam f) hh) p₀) p₀ :=
    ((Feq_contDiff lam (hfun lam f) hh).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hinr2 : HasFDerivAt (fun η : C(K,E) => (u0, η))
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)) η₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := u0)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (x := η₀))
  have hcomp := hFeq_at.comp η₀ hinr2
  have hEq : ((fderiv ℝ (Feq lam (hfun lam f) hh) p₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)) = 1 - A := by
    rw [← hcomp.fderiv]
    exact hsub.fderiv
  have hif : ((fderiv ℝ (Feq lam (hfun lam f) hh) p₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(K,E)).IsInvertible := by
    rw [hEq]
    exact isInvertible_one_sub A hA_lt
  have hFeq_cd : ContDiffAt ℝ ∞ (Feq lam (hfun lam f) hh) p₀ :=
    (Feq_contDiff lam (hfun lam f) hh).contDiffAt
  let ψ : E × ℝ → C(K,E) := hFeq_cd.implicitFunction (by simp) hif
  have hψ_cd : ContDiffAt ℝ ∞ ψ u0 := hFeq_cd.contDiffAt_implicitFunction (by simp) hif
  have hψ0 : ψ u0 = η₀ := hFeq_cd.implicitFunction_apply_self (by simp) hif
  have hev : ∀ᶠ y in 𝓝 u0, Feq lam (hfun lam f) hh (y, ψ y) = Feq lam (hfun lam f) hh p₀ :=
    hFeq_cd.eventually_apply_implicitFunction (by simp) hif
  have key : ∀ᶠ y in 𝓝 u0, u y.1 y.2 = Real.exp lam • (ψ y) ⟨1, by norm_num⟩ := by
    have hmem : ∀ᶠ y : E × ℝ in 𝓝 u0, y.2 ∈ Ioo a b := by
      have h1 : IsOpen {y : E × ℝ | y.2 ∈ Ioo a b} := isOpen_Ioo.preimage continuous_snd
      have h2 : u0 ∈ {y : E × ℝ | y.2 ∈ Ioo a b} := by rw [hu0def]; exact ht₀
      exact h1.mem_nhds h2
    filter_upwards [hev, hmem] with y hy hyab
    rw [hbase] at hy
    set W := ψ y with hW
    have hint_eq : ∀ σ : K, W σ = Real.exp (-(lam * (σ:ℝ))) • (y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
        hfun lam f (clampK r, (y.2, W (clampK r)))) := by
      intro σ
      have h := congrArg (fun w : C(K,E) => w σ) hy
      simp only [Feq, Phieq, ContinuousMap.sub_apply, ContinuousMap.zero_apply, Mlam_apply,
        constCLM_apply, IntCLM_apply, nem_apply, comb_apply] at h
      rw [smul_add]
      have h1 : W σ - Real.exp (-(lam * (σ:ℝ))) • y.1
          = Real.exp (-(lam * (σ:ℝ))) • (∫ r in (0:ℝ)..(σ:ℝ), hfun lam f (clampK r, (y.2, W (clampK r)))) :=
        sub_eq_zero.mp h
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, add_comm]
    set GR : ℝ → E := fun r => Real.exp (lam * r) • W (clampK r) with hGRdef
    have hGReq : ∀ σ : K, GR (σ:ℝ) = y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
        hfun lam f (clampK r, (y.2, W (clampK r))) := by
      intro σ
      have h := hint_eq σ
      have h2 : Real.exp (lam * (σ:ℝ)) • W σ
          = Real.exp (lam * (σ:ℝ)) • (Real.exp (-(lam * (σ:ℝ))) • (y.1 + ∫ r in (0:ℝ)..(σ:ℝ),
              hfun lam f (clampK r, (y.2, W (clampK r))))) := by rw [h]
      rw [smul_smul] at h2
      have h3 : Real.exp (lam * (σ:ℝ)) * Real.exp (-(lam * (σ:ℝ))) = 1 := by
        rw [← Real.exp_add, show lam * (σ:ℝ) + -(lam * (σ:ℝ)) = 0 from by ring, Real.exp_zero]
      rw [h3, one_smul] at h2
      have h4 : GR (σ:ℝ) = Real.exp (lam * (σ:ℝ)) • W σ := by
        simp only [hGRdef, clampK_coe]
      rw [h4, h2]
    have hGR_cont : Continuous GR := by
      simp only [hGRdef]
      exact (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).smul
        (W.continuous.comp continuous_clampK)
    have hfun_apply : ∀ r ∈ Set.Icc (0:ℝ) 1,
        hfun lam f (clampK r, (y.2, W (clampK r))) = y.2 • f (y.2 * r) (GR r) := by
      intro r hr
      rw [clampK_of_mem hr]
      simp only [hfun, Subtype.coe_mk]
      congr 1
      rw [hGRdef]
      simp only [clampK_of_mem hr]
    have hGR_deriv : ∀ σ ∈ Ioo (0:ℝ) 1, HasDerivAt GR (y.2 • f (y.2 * σ) (GR σ)) σ := by
      intro σ hσ
      have hcont : Continuous fun r : ℝ => y.2 • f (y.2 * r) (GR r) :=
        continuous_const.smul (hf'.continuous.comp
          (by fun_prop : Continuous fun r : ℝ => (y.2 * r, GR r)))
      have h1 : GR =ᶠ[𝓝 σ] fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r) := by
        filter_upwards [isOpen_Ioo.mem_nhds hσ] with σ' hσ'
        rw [hGReq ⟨σ', ⟨le_of_lt hσ'.1, le_of_lt hσ'.2⟩⟩]
        congr 1
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hσ'.1.le] at hr
        exact hfun_apply r ⟨hr.1, hr.2.trans hσ'.2.le⟩
      have h2 : HasDerivAt (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r))
          (y.2 • f (y.2 * σ) (GR σ)) σ := by
        have h3 := intervalIntegral.integral_hasDerivAt_right
          (hcont.intervalIntegrable 0 σ)
          (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 σ))
          hcont.continuousAt
        simpa using h3.const_add y.1
      exact h2.congr_of_eventuallyEq h1
    have hGR_apply : ∀ σ : K, GR (σ:ℝ) = Real.exp (lam * (σ:ℝ)) • W σ :=
      fun σ => by simp only [hGRdef, clampK_coe]
    by_cases h0 : y.2 = 0
    · have hz : (∫ r in (0:ℝ)..(1:ℝ), hfun lam f (clampK r, (y.2, W (clampK r)))) = 0 := by
        rw [h0]
        simp [hfun]
      have hW1 : W ⟨1, by norm_num⟩ = Real.exp (-(lam * 1)) • y.1 := by
        have h := hint_eq ⟨1, by norm_num⟩
        rw [h, hz, add_zero]
      rw [h0, hu0, hW1, smul_smul]
      have hexp : Real.exp lam * Real.exp (-(lam * 1)) = 1 := by
        rw [← Real.exp_add]
        have h2 : lam + -(lam * 1) = 0 := by ring
        rw [h2, Real.exp_zero]
      rw [hexp, one_smul]
    · have hIcc_mem : Set.Icc (0:ℝ) 1 ∈ 𝓝[Set.Ici 0] 0 := by
        have h : Set.Ici (0:ℝ) ∩ Set.Iic (1:ℝ) ∈ 𝓝[Set.Ici (0:ℝ)] (0:ℝ) :=
          inter_mem_nhdsWithin _ (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
        rwa [Set.Ici_inter_Iic] at h
      have hdiff : DifferentiableOn ℝ (u y.1) (Set.Ioo a b) :=
        fun t ht => (hode y.1 t ht).differentiableAt.differentiableWithinAt (s := Set.Ioo a b)
      have hu_cont : ContinuousOn (u y.1) (Set.Ioo a b) := hdiff.continuousOn
      have hscale : ∀ r ∈ Set.Icc (0:ℝ) 1, y.2 * r ∈ Set.Ioo a b := by
        intro r hr
        rcases lt_or_gt_of_ne h0 with h | h
        · exact ⟨lt_of_lt_of_le hyab.1 (by simpa using mul_le_mul_of_nonpos_left hr.2 (le_of_lt h)),
            lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg (le_of_lt h) hr.1) hb⟩
        · exact ⟨lt_of_lt_of_le ha (mul_nonneg (le_of_lt h) hr.1),
            lt_of_le_of_lt (mul_le_of_le_one_right (le_of_lt h) hr.2) hyab.2⟩
      have hg_cont : ContinuousOn (fun r : ℝ => u y.1 (y.2 * r)) (Set.Icc (0:ℝ) 1) :=
        hu_cont.comp (continuous_const.mul continuous_id).continuousOn hscale
      have hUcont : Continuous fun t : Set.Icc (0:ℝ) 1 => u y.1 (y.2 * (t:ℝ)) :=
        hg_cont.domRestrict
      have hGcont : Continuous fun t : Set.Icc (0:ℝ) 1 => GR (t:ℝ) :=
        hGR_cont.continuousOn.domRestrict
      haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
      let Φ : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 → ℝ × E := fun q =>
        (y.2 * (q.1:ℝ), (1 - (q.2:ℝ)) • GR (q.1:ℝ) + (q.2:ℝ) • u y.1 (y.2 * (q.1:ℝ)))
      have hΦcont : Continuous Φ := by
        have hv2 : Continuous fun q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 =>
            ((q.2 : Set.Icc (0:ℝ) 1) : ℝ) := continuous_subtype_val.comp continuous_snd
        exact Continuous.prodMk
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
          (((continuous_const.sub hv2).smul (hGcont.comp continuous_fst)).add
            (hv2.smul (hUcont.comp continuous_fst)))
      have hFcont : Continuous fun q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 =>
          y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q) :=
        (continuous_const : Continuous fun _ : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 => y.2).smul
          ((D2_contDiff (fun p : ℝ × E => f p.1 p.2) hf').continuous.comp hΦcont)
      let Fc : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, E →L[ℝ] E) :=
        ⟨fun q => y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q), hFcont⟩
      let M : ℝ := ‖Fc‖
      have hMnn : 0 ≤ M := norm_nonneg Fc
      have hMbound : ∀ q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1,
          ‖y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (Φ q)‖ ≤ M :=
        fun q => ContinuousMap.norm_coe_le_norm Fc q
      have hGR_deriv' : ∀ t ∈ Set.Ico (0:ℝ) 1,
          HasDerivWithinAt GR (y.2 • f (y.2 * t) (GR t)) (Set.Ici t) t := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with h0' | hpos
        · subst h0'
          have hcont : Continuous fun r : ℝ => y.2 • f (y.2 * r) (GR r) :=
            continuous_const.smul (hf'.continuous.comp
              (by fun_prop : Continuous fun r : ℝ => (y.2 * r, GR r)))
          have h2 : HasDerivAt (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r))
              (y.2 • f (y.2 * 0) (GR 0)) 0 := by
            have h3 := intervalIntegral.integral_hasDerivAt_right
              (hcont.intervalIntegrable 0 0)
              (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 0))
              hcont.continuousAt
            simpa using h3.const_add y.1
          have h1 : GR =ᶠ[𝓝[Set.Ici 0] (0:ℝ)]
              fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r) := by
            filter_upwards [hIcc_mem] with r hr
            have hinteg : (∫ r' in (0:ℝ)..r, hfun lam f (clampK r', (y.2, W (clampK r'))))
                = ∫ r' in (0:ℝ)..r, y.2 • f (y.2 * r') (GR r') := by
              apply intervalIntegral.integral_congr
              intro r' hr'
              rw [uIcc_of_le hr.1] at hr'
              exact hfun_apply r' ⟨hr'.1, hr'.2.trans hr.2⟩
            rw [show GR r = y.1 + ∫ r' in (0:ℝ)..r,
                hfun lam f (clampK r', (y.2, W (clampK r'))) from hGReq ⟨r, hr⟩, hinteg]
          have hpt : GR 0 = (fun σ' => y.1 + ∫ r in (0:ℝ)..σ', y.2 • f (y.2 * r) (GR r)) 0 := by
            rw [show GR 0 = y.1 + ∫ r in (0:ℝ)..0,
                hfun lam f (clampK r, (y.2, W (clampK r))) from hGReq ⟨0, by norm_num⟩]
            simp
          exact (h2.hasDerivWithinAt).congr_of_eventuallyEq h1 hpt
        · exact (hGR_deriv t ⟨hpos, ht.2⟩).hasDerivWithinAt
      have hg_deriv : ∀ t ∈ Set.Ico (0:ℝ) 1,
          HasDerivWithinAt (fun r : ℝ => u y.1 (y.2 * r))
            (y.2 • f (y.2 * t) (u y.1 (y.2 * t))) (Set.Ici t) t := by
        intro t ht
        have h1 : HasDerivAt (fun r : ℝ => y.2 * r) y.2 t := by
          simpa using (hasDerivAt_id t).const_mul y.2
        have h2 : HasDerivAt (u y.1) (f (y.2 * t) (u y.1 (y.2 * t))) (y.2 * t) :=
          hode y.1 (y.2 * t) (hscale t ⟨ht.1, le_of_lt ht.2⟩)
        exact (h2.scomp t h1).hasDerivWithinAt
      have hlip : ∀ t ∈ Set.Ico (0:ℝ) 1, LipschitzOnWith ⟨M, hMnn⟩
          (fun z : E => y.2 • f (y.2 * t) z) (segment ℝ (GR t) (u y.1 (y.2 * t))) := by
        intro t ht
        refine LipschitzOnWith.of_dist_le_mul (fun z₁ hz₁ z₂ hz₂ => ?_)
        rw [dist_eq_norm, dist_eq_norm]
        have hbd : ∀ z ∈ segment ℝ (GR t) (u y.1 (y.2 * t)),
            ‖fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z‖ ≤ M := by
          intro z hz
          have hfz : HasFDerivAt (fun z' : E => f (y.2 * t) z')
              ((fderiv ℝ (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z)).comp
                (ContinuousLinearMap.inr ℝ ℝ E)) z :=
            ((hf'.differentiable (by simp) (y.2 * t, z)).hasFDerivAt.comp z
              (hasFDerivAt_prodMk_right (y.2 * t) z))
          have hfd : fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z
              = y.2 • D2 (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z) := by
            rw [show fderiv ℝ (fun z' : E => y.2 • f (y.2 * t) z') z
                = y.2 • (fderiv ℝ (fun p : ℝ × E => f p.1 p.2) (y.2 * t, z)).comp
                    (ContinuousLinearMap.inr ℝ ℝ E) from (hfz.const_smul y.2).fderiv]
            congr 1
            rw [D2_apply, fderiv_snd_eq _ hf']
          rw [hfd]
          rw [segment_eq_image] at hz
          obtain ⟨θ, hθ, hzθ⟩ := hz
          have hΦq : Φ ((⟨t, ⟨ht.1, le_of_lt ht.2⟩⟩ : Set.Icc (0:ℝ) 1),
              (⟨θ, hθ⟩ : Set.Icc (0:ℝ) 1)) = (y.2 * t, z) := by
            show (y.2 * t, (1 - θ) • GR t + θ • u y.1 (y.2 * t)) = (y.2 * t, z)
            rw [show (1 - θ) • GR t + θ • u y.1 (y.2 * t) = z from hzθ]
          have hq := hMbound ((⟨t, ⟨ht.1, le_of_lt ht.2⟩⟩ : Set.Icc (0:ℝ) 1),
            (⟨θ, hθ⟩ : Set.Icc (0:ℝ) 1))
          rw [hΦq] at hq
          exact hq
        have hdiffseg : ∀ z ∈ segment ℝ (GR t) (u y.1 (y.2 * t)),
            DifferentiableAt ℝ (fun z' : E => y.2 • f (y.2 * t) z') z := by
          intro z hz
          exact (((hf'.differentiable (by simp) (y.2 * t, z)).hasFDerivAt.comp z
            (hasFDerivAt_prodMk_right (y.2 * t) z)).differentiableAt).const_smul y.2
        have hmain : ‖y.2 • f (y.2 * t) z₂ - y.2 • f (y.2 * t) z₁‖ ≤ M * ‖z₂ - z₁‖ :=
          Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (E := E) (G := E)
            (f := fun z : E => y.2 • f (y.2 * t) z) (C := M)
            (s := segment ℝ (GR t) (u y.1 (y.2 * t)))
            hdiffseg hbd (convex_segment (𝕜 := ℝ) (E := E) (GR t) (u y.1 (y.2 * t))) hz₁ hz₂
        calc ‖y.2 • f (y.2 * t) z₁ - y.2 • f (y.2 * t) z₂‖
            = ‖y.2 • f (y.2 * t) z₂ - y.2 • f (y.2 * t) z₁‖ :=
              norm_sub_rev (y.2 • f (y.2 * t) z₁) (y.2 • f (y.2 * t) z₂)
          _ ≤ M * ‖z₂ - z₁‖ := hmain
          _ = (⟨M, hMnn⟩ : NNReal) * ‖z₁ - z₂‖ := by
              rw [norm_sub_rev z₁ z₂]
      have h0eq : GR 0 = u y.1 (y.2 * 0) := by
        rw [show GR 0 = y.1 + ∫ r in (0:ℝ)..0,
            hfun lam f (clampK r, (y.2, W (clampK r))) from hGReq ⟨0, by norm_num⟩,
          mul_zero, hu0]
        simp
      have hEqOn : Set.EqOn GR (fun r : ℝ => u y.1 (y.2 * r)) (Set.Icc (0:ℝ) 1) :=
        ODE_solution_unique_of_mem_Icc_right
          (v := fun t z => y.2 • f (y.2 * t) z)
          (s := fun t => segment ℝ (GR t) (u y.1 (y.2 * t)))
          (K := ⟨M, hMnn⟩) hlip hGR_cont.continuousOn hGR_deriv'
          (fun t ht => left_mem_segment ℝ _ _) hg_cont hg_deriv
          (fun t ht => right_mem_segment ℝ _ _) h0eq
      have hG1 : GR 1 = u y.1 (y.2 * 1) := hEqOn (by norm_num)
      have hGR1 : GR 1 = Real.exp lam • W (⟨1, by norm_num⟩ : K) := by
        have h := hGR_apply ⟨1, by norm_num⟩
        simpa using h
      rw [hGR1] at hG1
      simpa using hG1.symm
  have hcd : ContDiffAt ℝ ∞ (fun p : E × ℝ => Real.exp lam • (ψ p) ⟨1, by norm_num⟩) u0 := by
    have h1 : ContDiffAt ℝ ∞ (fun p : E × ℝ => ψ p) u0 := hψ_cd
    have h2 : ContDiffAt ℝ ∞ (fun p : E × ℝ => (ψ p) ⟨1, by norm_num⟩) u0 := by
      have heval : ContDiff ℝ ∞ (fun w : C(K,E) => w ⟨1, by norm_num⟩) := by
        have hlin : IsBoundedLinearMap ℝ (fun w : C(K,E) => w ⟨1, by norm_num⟩) :=
          ⟨⟨fun a b => rfl, fun c a => rfl⟩, ⟨1, one_pos, fun w => by
            rw [one_mul]; exact ContinuousMap.norm_coe_le_norm w ⟨1, by norm_num⟩⟩⟩
        exact hlin.contDiff
      exact heval.contDiffAt.comp u0 h1
    exact (contDiffAt_const (c := Real.exp lam)).smul h2
  have hgoal : ContDiffAt ℝ ∞ (fun p : E × ℝ => u p.1 p.2) u0 :=
    hcd.congr_of_eventuallyEq key
  simpa [hu0def] using hgoal



end Commons.Analysis.ODE