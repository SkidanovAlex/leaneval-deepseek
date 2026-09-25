import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UniformSpace.Uniformizable

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Complex

open Complex Metric
open scoped Topology NNReal ENNReal

variable {d : ℕ}

/-! ## Auxiliary facts about `Fin.cons` and polydiscs -/

private lemma mem_closedBall_cons_iff {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (u : ℂ) (v : Fin n → ℂ) :
    (Fin.cons u v : Fin (n + 1) → ℂ) ∈ closedBall c R ↔
      u ∈ closedBall (c 0) R ∧ v ∈ closedBall (Fin.tail c) R := by
  rw [mem_closedBall, dist_pi_le_iff hR, mem_closedBall, mem_closedBall, dist_pi_le_iff hR]
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, h⟩ i
    induction i using Fin.cases with
    | zero => exact h0
    | succ j => exact h j

private lemma mem_ball_cons_iff {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} (hR : 0 < R)
    (u : ℂ) (v : Fin n → ℂ) :
    (Fin.cons u v : Fin (n + 1) → ℂ) ∈ ball c R ↔
      u ∈ ball (c 0) R ∧ v ∈ ball (Fin.tail c) R := by
  rw [mem_ball, dist_pi_lt_iff hR, mem_ball, mem_ball, dist_pi_lt_iff hR]
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, h⟩ i
    induction i using Fin.cases with
    | zero => exact h0
    | succ j => exact h j

private theorem differentiable_cons_snd {n : ℕ} (v : Fin n → ℂ) :
    Differentiable ℂ (fun w : ℂ => (Fin.cons w v : Fin (n + 1) → ℂ)) := by fun_prop

private theorem differentiable_cons_fst {n : ℕ} (w : ℂ) :
    Differentiable ℂ (fun v : Fin n → ℂ => (Fin.cons w v : Fin (n + 1) → ℂ)) := by fun_prop

/-! ## The iterated Cauchy integral over a polydisc -/

/-- Nested Cauchy integral of `f` over the polydisc with centre `c` and radius `R`. -/
private noncomputable def polyCauchy :
    (d : ℕ) → ((Fin d → ℂ) → ℂ) → (Fin d → ℂ) → ℝ → (Fin d → ℂ) → ℂ
  | 0, f, _, _, z => f z
  | (n + 1), f, c, R, z =>
      (2 * Real.pi * Complex.I)⁻¹ *
        ∮ w in C(c 0, R),
          polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail z) / (w - z 0)

/-- The iterated Cauchy integral of a function holomorphic on a polydisc reproduces the
function on the open polydisc. -/
private theorem polyCauchy_eq_of_differentiableOn {d : ℕ} {f : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ}
    {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall c R)) :
    ∀ z ∈ ball c R, f z = polyCauchy d f c R z := by
  induction d with
  | zero => intro z _; rfl
  | succ n ih =>
    intro z hz
    obtain ⟨hz0, hztail⟩ :=
      (mem_ball_cons_iff hR (z 0) (Fin.tail z)).mp (by rw [Fin.cons_self_tail]; exact hz)
    -- the slice `w ↦ f (cons w (tail z))`
    have hgdiff : DifferentiableOn ℂ (fun w : ℂ => f (Fin.cons w (Fin.tail z)))
        (closedBall (c 0) R) := by
      refine hf.comp (differentiable_cons_snd (Fin.tail z)).differentiableOn ?_
      intro w hw
      exact (mem_closedBall_cons_iff hR.le w (Fin.tail z)).mpr ⟨hw, ball_subset_closedBall hztail⟩
    have hcauchy := hgdiff.circleIntegral_sub_inv_smul hz0
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hcauchy' : (∮ w in C(c 0, R), (w - z 0)⁻¹ • f (Fin.cons w (Fin.tail z)))
        = 2 * Real.pi * Complex.I * f z := by
      simpa [Fin.cons_self_tail, smul_eq_mul] using hcauchy
    have hstep1 : f z = (2 * Real.pi * Complex.I)⁻¹ *
        ∮ w in C(c 0, R), f (Fin.cons w (Fin.tail z)) / (w - z 0) := by
      calc f z = (2 * Real.pi * Complex.I)⁻¹ * ((2 * Real.pi * Complex.I) * f z) := by
              rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
        _ = (2 * Real.pi * Complex.I)⁻¹ *
              ∮ w in C(c 0, R), (w - z 0)⁻¹ • f (Fin.cons w (Fin.tail z)) := by rw [hcauchy']
        _ = (2 * Real.pi * Complex.I)⁻¹ *
              ∮ w in C(c 0, R), f (Fin.cons w (Fin.tail z)) / (w - z 0) := by
              congr 1
              exact circleIntegral.integral_congr hR.le
                (fun w _ => by rw [smul_eq_mul, div_eq_mul_inv, mul_comm])
    have hcongr : ∀ w ∈ sphere (c 0) R,
        f (Fin.cons w (Fin.tail z)) =
          polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail z) := by
      intro w hw
      have hw' : w ∈ closedBall (c 0) R := (mem_sphere.mp hw).le
      have hdiff : DifferentiableOn ℂ (fun v : Fin n → ℂ => f (Fin.cons w v))
          (closedBall (Fin.tail c) R) := by
        refine hf.comp (differentiable_cons_fst (n := n) w).differentiableOn ?_
        intro v hv
        exact (mem_closedBall_cons_iff hR.le w v).mpr ⟨hw', hv⟩
      exact ih hdiff (Fin.tail z) hztail
    rw [hstep1, polyCauchy]
    congr 1
    exact circleIntegral.integral_congr hR.le (fun w hw => by rw [hcongr w hw])


/-! ## The Cauchy coefficients of a holomorphic function on a polydisc -/

/-- Multi-index coefficients of the power series of `f` at `c`, defined recursively by the
iterated Cauchy integral. -/
private noncomputable def polyCoeff :
    (d : ℕ) → ((Fin d → ℂ) → ℂ) → (Fin d → ℂ) → ℝ → (Fin d → ℕ) → ℂ
  | 0, f, c, _, _ => f c
  | (n + 1), f, c, R, α =>
      (2 * Real.pi * Complex.I)⁻¹ *
        ∮ w in C(c 0, R),
          (w - c 0)⁻¹ ^ (α 0) * (w - c 0)⁻¹ *
            polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail α)

private lemma norm_two_pi_I_inv : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  have h1 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one,
      show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
    have h : Complex.normSq ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi) * (2 * Real.pi) :=
      Complex.normSq_ofReal _
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg ((2 * Real.pi : ℝ) : ℂ), Real.pi_pos]
  rw [norm_inv, h1]

/-- Cauchy's estimate for the multi-index coefficients. -/
private theorem norm_polyCoeff_le (d : ℕ) :
    ∀ {f : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ} {R M : ℝ}, 0 < R → 0 ≤ M →
      (∀ x ∈ closedBall c R, ‖f x‖ ≤ M) → ∀ α : Fin d → ℕ,
        ‖polyCoeff d f c R α‖ ≤ M * R⁻¹ ^ (∑ j, α j) := by
  induction d with
  | zero =>
    intro f c R M hR hM hb α
    change ‖f c‖ ≤ M * R⁻¹ ^ (∑ j : Fin 0, α j)
    simpa using hb c (mem_closedBall_self hR.le)
  | succ n ih =>
    intro f c R M hR hM hb α
    have hRne : R ≠ 0 := hR.ne'
    have hkey : ∀ w ∈ sphere (c 0) R,
        ‖polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail α)‖ ≤
          M * R⁻¹ ^ (∑ j : Fin n, α j.succ) := by
      intro w hw
      have h := ih (c := Fin.tail c) hR hM (fun v hv => hb (Fin.cons w v) ?_) (Fin.tail α)
      · simpa only [Fin.tail] using h
      · exact (mem_closedBall_cons_iff hR.le w v).mpr ⟨(mem_sphere.mp hw).le, hv⟩
    have hS0 : 0 ≤ M * R⁻¹ ^ (∑ j : Fin n, α j.succ) :=
      mul_nonneg hM (pow_nonneg (inv_nonneg.mpr hR.le) _)
    have hint : ‖∮ w in C(c 0, R), (w - c 0)⁻¹ ^ (α 0) * (w - c 0)⁻¹ *
        polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail α)‖ ≤
        2 * Real.pi * R *
          (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ))) := by
      apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
      intro w hw
      have hwR : ‖w - c 0‖ = R := by rw [← dist_eq_norm]; exact mem_sphere.mp hw
      have hnorm : ‖(w - c 0)⁻¹ ^ (α 0) * (w - c 0)⁻¹ *
          polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail α)‖
          = R⁻¹ ^ (α 0) * R⁻¹ *
            ‖polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail α)‖ := by
        rw [norm_mul, norm_mul, norm_pow, norm_inv, hwR]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (hkey w hw) (by positivity)
    rw [polyCoeff, norm_mul, norm_two_pi_I_inv]
    refine le_trans (mul_le_mul_of_nonneg_left hint (by positivity)) ?_
    rw [Fin.sum_univ_succ]
    have h2 : (2 * Real.pi)⁻¹ * (2 * Real.pi * R *
        (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ))))
        = R * (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ))) := by
      rw [show (2 * Real.pi) * R *
            (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ)))
          = (2 * Real.pi) *
            (R * (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ)))) from by ring]
      rw [inv_mul_cancel_left₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    have h3 : R * (R⁻¹ ^ (α 0) * R⁻¹ * (M * R⁻¹ ^ (∑ j : Fin n, α j.succ)))
        = M * (R⁻¹ ^ (α 0) * R⁻¹ ^ (∑ j : Fin n, α j.succ)) := by
      field_simp
    exact le_of_eq (h2.trans (h3.trans (by rw [pow_add])))

/-! ## Continuity of the coefficients in a parameter -/

/-- Continuity of the Cauchy integral in a parameter. -/
private lemma continuousOn_circleIntegral_family {X : Type*} [TopologicalSpace X] {s : Set X}
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) {H : X × ℂ → ℂ}
    (hH : ContinuousOn H (s ×ˢ closedBall c ρ)) :
    ContinuousOn (fun x : X => ∮ u in C(c, ρ), (u - c)⁻¹ ^ k * (u - c)⁻¹ * H (x, u)) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hH' : Continuous (fun p : s × ℝ => H ((p.1 : X), circleMap c ρ p.2)) :=
    hH.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_circleMap c ρ).comp continuous_snd))
      (fun p => ⟨p.1.2, sphere_subset_closedBall (circleMap_mem_sphere c hρ.le p.2)⟩)
  have hderiv' : Continuous (fun θ : ℝ => deriv (circleMap c ρ) θ) := by
    rw [funext (deriv_circleMap c ρ)]
    exact (continuous_circleMap 0 ρ).mul continuous_const
  have hd : Continuous (fun p : s × ℝ => deriv (circleMap c ρ) p.2) :=
    hderiv'.comp continuous_snd
  have hinv : Continuous (fun p : s × ℝ => (circleMap c ρ p.2 - c)⁻¹) :=
    (((continuous_circleMap c ρ).comp continuous_snd).sub continuous_const).inv₀
      (fun p => sub_ne_zero.mpr (circleMap_ne_center (c := c) (R := ρ) hρ.ne' (θ := p.2)))
  have hΦ : Continuous (Function.uncurry (fun x : s => fun θ : ℝ => deriv (circleMap c ρ) θ *
      ((circleMap c ρ θ - c)⁻¹ ^ k * (circleMap c ρ θ - c)⁻¹ *
        H ((x : X), circleMap c ρ θ)))) := by
    change Continuous (fun p : s × ℝ => deriv (circleMap c ρ) p.2 *
      ((circleMap c ρ p.2 - c)⁻¹ ^ k * (circleMap c ρ p.2 - c)⁻¹ *
        H ((p.1 : X), circleMap c ρ p.2)))
    exact hd.mul (((hinv.pow k).mul hinv).mul hH')
  have hmain := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hΦ (0 : ℝ) (2 * Real.pi)
  convert hmain using 1
  ext x
  simp only [circleIntegral, smul_eq_mul, Set.domRestrict]

/-- The coefficient function of a family varying continuously in a parameter is continuous. -/
private theorem continuousOn_polyCoeff_family (d : ℕ) :
    ∀ {X : Type*} [TopologicalSpace X] (s : Set X) (F : X × (Fin d → ℂ) → ℂ) (c : Fin d → ℂ)
      (ρ : ℝ), 0 < ρ → ContinuousOn F (s ×ˢ closedBall c ρ) →
      ∀ α : Fin d → ℕ,
        ContinuousOn (fun x : X => polyCoeff d (fun v => F (x, v)) c ρ α) s := by
  induction d with
  | zero =>
    intro X _ s F c ρ hρ hF α
    have h0 : (fun x : X => polyCoeff 0 (fun v => F (x, v)) c ρ α) = fun x => F (x, c) := by
      funext x; rfl
    rw [h0, continuousOn_iff_continuous_domRestrict]
    exact hF.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun x => ⟨x.2, mem_closedBall_self hρ.le⟩)
  | succ n ih =>
    intro X _ s F c ρ hρ hF α
    have hHinner : ContinuousOn
        (fun p : X × ℂ =>
          polyCoeff n (fun v => F (p.1, Fin.cons p.2 v)) (Fin.tail c) ρ (Fin.tail α))
        (s ×ˢ closedBall (c 0) ρ) := by
      refine ih (X := X × ℂ) (s := s ×ˢ closedBall (c 0) ρ)
        (F := fun p : (X × ℂ) × (Fin n → ℂ) => F (p.1.1, Fin.cons p.1.2 p.2))
        (c := Fin.tail c) (ρ := ρ) hρ ?_ (Fin.tail α)
      refine hF.comp (by fun_prop) ?_
      rintro ⟨⟨x, u⟩, v⟩ ⟨hxu, hv⟩
      exact ⟨hxu.1, (mem_closedBall_cons_iff hρ.le u v).mpr ⟨hxu.2, hv⟩⟩
    have houter := continuousOn_circleIntegral_family hρ (α 0) hHinner
    have hconv : (fun x : X => polyCoeff (n + 1) (fun v => F (x, v)) c ρ α)
        = fun x => (2 * Real.pi * Complex.I)⁻¹ *
            ∮ u in C(c 0, ρ), (u - c 0)⁻¹ ^ (α 0) * (u - c 0)⁻¹ *
              polyCoeff n (fun v => F (x, Fin.cons u v)) (Fin.tail c) ρ (Fin.tail α) := by
      funext x
      rw [polyCoeff]
    rw [hconv]
    exact continuousOn_const.mul houter

/-! ## Interchanging circle integrals with sums -/

/-- Interchanging a circle integral with a `HasSum` of continuous functions, given a summable
uniform bound on the circle. -/
private theorem circleIntegral_hasSum_of_summable_bound {ι : Type*} [Countable ι] {c : ℂ} {R : ℝ}
    (hR : 0 < R) (G : ι → ℂ → ℂ) (Gsum : ℂ → ℂ) (bound : ι → ℝ)
    (hG : ∀ i, ContinuousOn (G i) (sphere c R))
    (hbound : ∀ i, ∀ w ∈ sphere c R, ‖G i w‖ ≤ bound i)
    (hbsum : Summable bound)
    (hsum : ∀ w ∈ sphere c R, HasSum (fun i => G i w) (Gsum w)) :
    HasSum (fun i => ∮ w in C(c, R), G i w) (∮ w in C(c, R), Gsum w) := by
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    rw [funext (deriv_circleMap c R)]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hcont_i : ∀ i, Continuous (fun θ : ℝ => G i (circleMap c R θ)) := fun i =>
    (hG i).comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR0 θ)
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (a := 0) (b := 2 * Real.pi)
    (f := fun θ => deriv (circleMap c R) θ * Gsum (circleMap c R θ))
    (F := fun i θ => deriv (circleMap c R) θ * G i (circleMap c R θ))
    (bound := fun i _ => R * bound i)
    (fun i => ((hderiv.mul (hcont_i i))).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
        abs_of_nonneg hR0]
      exact mul_le_mul_of_nonneg_left (hbound i _ (circleMap_mem_sphere c hR0 θ)) hR0)
    (Filter.Eventually.of_forall fun θ _ => hbsum.mul_left R)
    (by
      have h : (fun t : ℝ => ∑' i, R * bound i) = fun _ => R * ∑' i, bound i := by
        funext t; rw [tsum_mul_left]
      rw [h]
      exact intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ => (hsum _ (circleMap_mem_sphere c hR0 θ)).mul_left _)
  have h1 : (fun i => ∮ w in C(c, R), G i w)
      = fun i => ∫ t in (0:ℝ)..(2 * Real.pi), deriv (circleMap c R) t * G i (circleMap c R t) := by
    funext i
    simp only [circleIntegral, smul_eq_mul]
  have h2 : (∮ w in C(c, R), Gsum w)
      = ∫ t in (0:ℝ)..(2 * Real.pi), deriv (circleMap c R) t * Gsum (circleMap c R t) := by
    simp only [circleIntegral, smul_eq_mul]
  rw [h1, h2]
  exact key

/-! ## A geometric expansion on the circle -/

private lemma hasSum_geometric_circle {c z w : ℂ} {R : ℝ} (hR : 0 < R) (hw : w ∈ sphere c R)
    (hz : z ∈ ball c R) :
    HasSum (fun k : ℕ => (z - c) ^ k * (w - c)⁻¹ ^ (k + 1)) (w - z)⁻¹ := by
  have hwc_norm : ‖w - c‖ = R := by rw [← dist_eq_norm]; exact mem_sphere.mp hw
  have hwc : w - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hwc_norm; exact hR.ne' hwc_norm.symm
  have hz_norm : ‖z - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.mp hz
  have hratio : ‖(z - c) * (w - c)⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, hwc_norm, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hz_norm
  have hgeo := (hasSum_geometric_of_norm_lt_one hratio).mul_right ((w - c)⁻¹)
  have hsummand : (fun k : ℕ => ((z - c) * (w - c)⁻¹) ^ k * (w - c)⁻¹)
      = fun k : ℕ => (z - c) ^ k * (w - c)⁻¹ ^ (k + 1) := by
    funext k
    rw [mul_pow, mul_assoc, pow_succ]
  have hlim : (1 - (z - c) * (w - c)⁻¹)⁻¹ * (w - c)⁻¹ = (w - z)⁻¹ := by
    have hwz : w - z ≠ 0 := by
      intro h
      have h0 : ‖w - z‖ = 0 := by rw [h, norm_zero]
      have h2 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        rw [show w - c = (w - z) + (z - c) from by ring]
        exact norm_add_le _ _
      rw [hwc_norm, h0, zero_add] at h2
      linarith
    have h1 : 1 - (z - c) * (w - c)⁻¹ = (w - z) * (w - c)⁻¹ := by
      field_simp
      ring
    rw [h1]
    field_simp
  rw [hsummand, hlim] at hgeo
  exact hgeo


/-! ## Multi-index summability -/

private lemma summable_prod_pow_fin {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i < 1) :
    Summable (fun β : Fin d → ℕ => ∏ i, a i ^ β i) := by
  induction d with
  | zero =>
    have h : (fun β : Fin 0 → ℕ => ∏ i : Fin 0, a i ^ β i) = fun _ => (1 : ℝ) := by
      funext β; simp
    rw [h]
    exact (hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℝ))).summable
  | succ n ih =>
    refine (Equiv.summable_iff (f := fun β : Fin (n + 1) → ℕ => ∏ i, a i ^ β i)
      (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp ?_
    have hprod : (fun β : Fin (n + 1) → ℕ => ∏ i, a i ^ β i) ∘
          (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))
        = fun p : ℕ × (Fin n → ℕ) => a 0 ^ p.1 * ∏ i : Fin n, a i.succ ^ p.2 i := by
      funext p
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
    rw [hprod]
    refine (summable_prod_of_nonneg (f := fun p : ℕ × (Fin n → ℕ) =>
      a 0 ^ p.1 * ∏ i : Fin n, a i.succ ^ p.2 i) (by
        intro p
        exact mul_nonneg (pow_nonneg (ha 0) _)
          (Finset.prod_nonneg fun i _ => pow_nonneg (ha i.succ) _))).mpr ⟨?_, ?_⟩
    · intro k
      have h := (ih (a := fun i => a i.succ) (fun i => ha i.succ) (fun i => ha1 i.succ)).mul_left
        (a 0 ^ k)
      simpa [mul_assoc] using h
    · have h2 : (fun k : ℕ => ∑' γ : Fin n → ℕ, a 0 ^ k * ∏ i : Fin n, a i.succ ^ γ i)
          = fun k : ℕ => a 0 ^ k * (∑' γ : Fin n → ℕ, ∏ i : Fin n, a i.succ ^ γ i) := by
        funext k; rw [tsum_mul_left]
      rw [h2]
      simpa [mul_comm] using (summable_geometric_of_lt_one (ha 0) (ha1 0)).mul_left
        (∑' γ : Fin n → ℕ, ∏ i : Fin n, a i.succ ^ γ i)

private lemma summable_multiIndex_prod_geom {d : ℕ} {s : Fin d → ℝ} {t K : ℝ}
    (hs : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1) (ht : 0 ≤ t) (ht1 : t < 1) (hK : 0 ≤ K) :
    Summable (fun p : (Fin d → ℕ) × ℕ => K * (∏ i, s i ^ (p.1 i)) * t ^ (p.2)) := by
  refine (summable_prod_of_nonneg (f := fun p : (Fin d → ℕ) × ℕ =>
    K * (∏ i, s i ^ (p.1 i)) * t ^ (p.2)) (by
      intro p
      exact mul_nonneg (mul_nonneg hK (Finset.prod_nonneg fun i _ => pow_nonneg (hs i) _))
        (pow_nonneg ht _))).mpr ⟨?_, ?_⟩
  · intro β
    have := (summable_geometric_of_lt_one ht ht1).mul_left (K * ∏ i, s i ^ (β i))
    simpa [mul_assoc] using this
  · have h2 : (fun β : Fin d → ℕ => ∑' k : ℕ, K * (∏ i, s i ^ (β i)) * t ^ k)
        = fun β : Fin d → ℕ => (K * ∑' k : ℕ, t ^ k) * (∏ i, s i ^ (β i)) := by
      funext β
      rw [tsum_mul_left]
      ring
    rw [h2]
    exact (summable_prod_pow_fin hs hs1).mul_left _


/-! ## The power series expansion of the Cauchy integral -/

private theorem polyCauchy_hasSum (d : ℕ) :
    ∀ {f : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ} {R : ℝ}, 0 < R →
      DifferentiableOn ℂ f (closedBall c R) → ∀ z ∈ ball c R,
        HasSum (fun α : Fin d → ℕ => polyCoeff d f c R α * ∏ j, (z j - c j) ^ (α j))
          (polyCauchy d f c R z) := by
  induction d with
  | zero =>
    intro f c R hR hf z hz
    have hzc : z = c := Subsingleton.elim z c
    rw [hzc]
    have h := hasSum_unique (fun α : Fin 0 → ℕ =>
      polyCoeff 0 f c R α * ∏ j : Fin 0, (c j - c j) ^ (α j))
    simpa [polyCoeff, polyCauchy] using h
  | succ n ih =>
    intro f c R hR hf z hz
    have hR0 : (0 : ℝ) ≤ R := hR.le
    have htpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    obtain ⟨hz0, hztail⟩ :=
      (mem_ball_cons_iff hR (z 0) (Fin.tail z)).mp (by rw [Fin.cons_self_tail]; exact hz)
    have hslice : ∀ w ∈ sphere (c 0) R,
        DifferentiableOn ℂ (fun v : Fin n → ℂ => f (Fin.cons w v)) (closedBall (Fin.tail c) R) := by
      intro w hw
      refine hf.comp (differentiable_cons_fst (n := n) w).differentiableOn ?_
      intro v hv
      exact (mem_closedBall_cons_iff hR0 w v).mpr ⟨(mem_sphere.mp hw).le, hv⟩
    have hIH : ∀ w ∈ sphere (c 0) R,
        HasSum (fun β : Fin n → ℕ =>
            polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i))
          (polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail z)) :=
      fun w hw => ih hR (hslice w hw) (Fin.tail z) hztail
    obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (f c)) (hM c (mem_closedBall_self hR0))
    have hBbound : ∀ (β : Fin n → ℕ) (w : ℂ), w ∈ sphere (c 0) R →
        ‖polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β‖ ≤ M * R⁻¹ ^ (∑ i, β i) := by
      intro β w hw
      refine norm_polyCoeff_le n hR hM0 (fun v hv => hM (Fin.cons w v) ?_) β
      exact (mem_closedBall_cons_iff hR0 w v).mpr ⟨(mem_sphere.mp hw).le, hv⟩
    have hz0lt : ‖z 0 - c 0‖ < R := by
      rw [← dist_eq_norm]; exact (dist_pi_lt_iff hR).mp hz 0
    have hztlt : ∀ i : Fin n, ‖Fin.tail z i - Fin.tail c i‖ < R := by
      intro i; rw [← dist_eq_norm]; exact (dist_pi_lt_iff hR).mp hz i.succ
    have hs0 : ∀ i : Fin n, 0 ≤ ‖Fin.tail z i - Fin.tail c i‖ / R :=
      fun i => div_nonneg (norm_nonneg _) hR0
    have hs1 : ∀ i : Fin n, ‖Fin.tail z i - Fin.tail c i‖ / R < 1 :=
      fun i => (div_lt_one hR).mpr (hztlt i)
    have ht0 : 0 ≤ ‖z 0 - c 0‖ / R := div_nonneg (norm_nonneg _) hR0
    have ht1 : ‖z 0 - c 0‖ / R < 1 := (div_lt_one hR).mpr hz0lt
    have hBcont : ∀ β : Fin n → ℕ, ContinuousOn
        (fun w => polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β)
        (sphere (c 0) R) := by
      intro β
      refine continuousOn_polyCoeff_family n (X := ℂ) (s := sphere (c 0) R)
        (F := fun p : ℂ × (Fin n → ℂ) => f (Fin.cons p.1 p.2)) (c := Fin.tail c) (ρ := R) hR ?_ β
      refine hf.continuousOn.comp (by fun_prop) ?_
      rintro ⟨w, v⟩ ⟨hw, hv⟩
      exact (mem_closedBall_cons_iff hR0 w v).mpr ⟨sphere_subset_closedBall hw, hv⟩
    have hwne : ∀ w ∈ sphere (c 0) R, w - c 0 ≠ 0 := by
      intro w hw h
      have h1 : ‖w - c 0‖ = R := by rw [← dist_eq_norm]; exact mem_sphere.mp hw
      rw [h, norm_zero] at h1
      exact hR.ne' h1.symm
    -- the pointwise norm bound
    have hnormbound : ∀ (p : (Fin n → ℕ) × ℕ) (w : ℂ), w ∈ sphere (c 0) R →
        ‖(polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
            ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1))‖
          ≤ M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ / R) ^ (p.1 i))
              * (‖z 0 - c 0‖ / R) ^ p.2 := by
      rintro ⟨β, k⟩ w hw
      show ‖(polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
            ((z 0 - c 0) ^ k * ((w - c 0)⁻¹) ^ (k + 1))‖
          ≤ M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ / R) ^ (β i))
              * (‖z 0 - c 0‖ / R) ^ k
      have hwc : ‖(w - c 0)⁻¹‖ = R⁻¹ := by
        rw [norm_inv, show ‖w - c 0‖ = R from by rw [← dist_eq_norm]; exact mem_sphere.mp hw]
      have hnorm : ‖(polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
            ((z 0 - c 0) ^ k * ((w - c 0)⁻¹) ^ (k + 1))‖
          = ‖polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β‖ *
            (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i)) *
            (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_prod, hwc]
        simp only [norm_pow]
      rw [hnorm]
      have hP : (∏ i, R⁻¹ ^ (β i)) * (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i))
          = ∏ i, (‖Fin.tail z i - Fin.tail c i‖ * R⁻¹) ^ (β i) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_pow, mul_comm R⁻¹]
      have hK : ‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1)
          = R⁻¹ * (‖z 0 - c 0‖ * R⁻¹) ^ k := by
        rw [mul_pow, pow_succ']
        ring
      have hcalc : M * R⁻¹ ^ (∑ i, β i) * (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i)) *
            (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1))
          = M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ * R⁻¹) ^ (β i))
              * (‖z 0 - c 0‖ * R⁻¹) ^ k := by
        calc M * R⁻¹ ^ (∑ i, β i) * (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i)) *
              (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1))
            = M * ((∏ i, R⁻¹ ^ (β i)) * (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i))) *
                (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1)) := by
              rw [← Finset.prod_pow_eq_pow_sum (s := Finset.univ) (f := β) (a := R⁻¹)]
              ring
          _ = M * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ * R⁻¹) ^ (β i)) *
                (R⁻¹ * (‖z 0 - c 0‖ * R⁻¹) ^ k) := by rw [hP, hK]
          _ = M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ * R⁻¹) ^ (β i)) *
                (‖z 0 - c 0‖ * R⁻¹) ^ k := by ring
      calc ‖polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β‖ *
            (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i)) *
            (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1))
          ≤ M * R⁻¹ ^ (∑ i, β i) * (∏ i, ‖Fin.tail z i - Fin.tail c i‖ ^ (β i)) *
              (‖z 0 - c 0‖ ^ k * R⁻¹ ^ (k + 1)) := by
            gcongr
            exact hBbound β w hw
        _ = M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ * R⁻¹) ^ (β i)) *
              (‖z 0 - c 0‖ * R⁻¹) ^ k := hcalc
    have hpoint : ∀ w ∈ sphere (c 0) R, HasSum
        (fun p : (Fin n → ℕ) × ℕ =>
          (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
            ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1)))
        (polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail z) * (w - z 0)⁻¹) := by
      intro w hw
      have hsig := (hIH w hw).mul_right ((w - z 0)⁻¹)
      have hfiber : ∀ β : Fin n → ℕ, HasSum
          (fun k : ℕ => (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
            ((z 0 - c 0) ^ k * ((w - c 0)⁻¹) ^ (k + 1)))
          ((polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) * (w - z 0)⁻¹) := fun β =>
        (hasSum_geometric_circle hR hw hz0).mul_left _
      have hjoint : Summable (fun q : (Σ _ : Fin n → ℕ, ℕ) =>
          (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R q.1 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (q.1 i)) *
            ((z 0 - c 0) ^ q.2 * ((w - c 0)⁻¹) ^ (q.2 + 1))) := by
        refine (Equiv.summable_iff (f := fun q : (Σ _ : Fin n → ℕ, ℕ) =>
            (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R q.1 *
                ∏ i, (Fin.tail z i - Fin.tail c i) ^ (q.1 i)) *
              ((z 0 - c 0) ^ q.2 * ((w - c 0)⁻¹) ^ (q.2 + 1)))
          (Equiv.sigmaEquivProd (Fin n → ℕ) ℕ).symm).mp ?_
        have heq : ((fun q : (Σ _ : Fin n → ℕ, ℕ) =>
              (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R q.1 *
                  ∏ i, (Fin.tail z i - Fin.tail c i) ^ (q.1 i)) *
                ((z 0 - c 0) ^ q.2 * ((w - c 0)⁻¹) ^ (q.2 + 1))) ∘
            ⇑(Equiv.sigmaEquivProd (Fin n → ℕ) ℕ).symm)
            = fun p : (Fin n → ℕ) × ℕ =>
              (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
                  ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
                ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1)) := by
          funext p
          simp only [Function.comp_apply, Equiv.sigmaEquivProd_symm_apply]
        rw [heq]
        refine Summable.of_norm_bounded (summable_multiIndex_prod_geom (s := fun i =>
          ‖Fin.tail z i - Fin.tail c i‖ / R) (t := ‖z 0 - c 0‖ / R) (K := M * R⁻¹)
          hs0 hs1 ht0 ht1 (by positivity)) ?_
        rintro ⟨β, k⟩
        exact hnormbound (β, k) w hw
      refine (Equiv.hasSum_iff (f := fun q : (Σ _ : Fin n → ℕ, ℕ) =>
          (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R q.1 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (q.1 i)) *
            ((z 0 - c 0) ^ q.2 * ((w - c 0)⁻¹) ^ (q.2 + 1)))
        (Equiv.sigmaEquivProd (Fin n → ℕ) ℕ).symm).mpr ?_
      exact hsig.sigma_of_hasSum hfiber hjoint
    -- continuity of the integrands
    have hGcont : ∀ p : (Fin n → ℕ) × ℕ, ContinuousOn (fun w : ℂ =>
        (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
            ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
          ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1))) (sphere (c 0) R) := by
      rintro ⟨β, k⟩
      refine ContinuousOn.mul (ContinuousOn.mul (hBcont β) continuousOn_const) ?_
      refine ContinuousOn.mul continuousOn_const ?_
      exact ContinuousOn.pow (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
        (fun w hw => hwne w hw)) _
    have hbsum : Summable (fun p : (Fin n → ℕ) × ℕ =>
        M * R⁻¹ * (∏ i, (‖Fin.tail z i - Fin.tail c i‖ / R) ^ (p.1 i))
          * (‖z 0 - c 0‖ / R) ^ p.2) :=
      summable_multiIndex_prod_geom hs0 hs1 ht0 ht1 (by positivity)
    have hint := circleIntegral_hasSum_of_summable_bound hR
      (fun p : (Fin n → ℕ) × ℕ => fun w : ℂ =>
        (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
            ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
          ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1)))
      (fun w : ℂ => polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R (Fin.tail z) *
        (w - z 0)⁻¹)
      (fun p : (Fin n → ℕ) × ℕ => M * R⁻¹ *
        (∏ i, (‖Fin.tail z i - Fin.tail c i‖ / R) ^ (p.1 i)) * (‖z 0 - c 0‖ / R) ^ p.2)
      hGcont hnormbound hbsum hpoint
    -- identify the integrals
    have hGint : ∀ p : (Fin n → ℕ) × ℕ,
        (∮ w in C(c 0, R), (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
            ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1)))
          = (2 * Real.pi * Complex.I) *
              (polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) * (z 0 - c 0) ^ p.2 *
                ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) := by
      rintro ⟨β, k⟩
      show (∮ w in C(c 0, R), (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
            ((z 0 - c 0) ^ k * ((w - c 0)⁻¹) ^ (k + 1)))
          = (2 * Real.pi * Complex.I) * (polyCoeff (n + 1) f c R (Fin.cons k β) *
              (z 0 - c 0) ^ k * ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i))
      have hswap : (fun w : ℂ => (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
            ((z 0 - c 0) ^ k * ((w - c 0)⁻¹) ^ (k + 1)))
          = fun w : ℂ => ((z 0 - c 0) ^ k * ∏ i, (Fin.tail z i - Fin.tail c i) ^ (β i)) *
              (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
                ((w - c 0)⁻¹) ^ (k + 1)) := by
        funext w; ring
      rw [hswap]
      rw [circleIntegral.integral_const_mul]
      rw [show (∮ w in C(c 0, R), polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β *
              ((w - c 0)⁻¹) ^ (k + 1))
          = (2 * Real.pi * Complex.I) * polyCoeff (n + 1) f c R (Fin.cons k β) from by
        rw [show polyCoeff (n + 1) f c R (Fin.cons k β) = (2 * Real.pi * Complex.I)⁻¹ *
              ∮ w in C(c 0, R), (w - c 0)⁻¹ ^ k * (w - c 0)⁻¹ *
                polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R β from by
            rw [polyCoeff]; simp]
        rw [mul_inv_cancel_left₀ htpi]
        refine circleIntegral.integral_congr hR0 (fun w hw => ?_)
        rw [pow_succ]
        ring]
      ring
    have hGsum : (∮ w in C(c 0, R), polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R
          (Fin.tail z) * (w - z 0)⁻¹) = (2 * Real.pi * Complex.I) * polyCauchy (n + 1) f c R z := by
      rw [show polyCauchy (n + 1) f c R z = (2 * Real.pi * Complex.I)⁻¹ *
            ∮ w in C(c 0, R), polyCauchy n (fun v => f (Fin.cons w v)) (Fin.tail c) R
              (Fin.tail z) / (w - z 0) from by rw [polyCauchy]]
      rw [mul_inv_cancel_left₀ htpi]
      refine circleIntegral.integral_congr hR0 (fun w hw => ?_)
      rw [div_eq_mul_inv]
    have hfun1 : (fun p : (Fin n → ℕ) × ℕ => ∮ w in C(c 0, R),
            (polyCoeff n (fun v => f (Fin.cons w v)) (Fin.tail c) R p.1 *
                ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) *
              ((z 0 - c 0) ^ p.2 * ((w - c 0)⁻¹) ^ (p.2 + 1)))
          = fun p : (Fin n → ℕ) × ℕ => (2 * Real.pi * Complex.I) *
              (polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) * (z 0 - c 0) ^ p.2 *
                ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)) := funext hGint
    rw [hfun1, hGsum] at hint
    have hint2 := hint.mul_left ((2 * Real.pi * Complex.I)⁻¹)
    have hfun2 : (fun p : (Fin n → ℕ) × ℕ => (2 * Real.pi * Complex.I)⁻¹ *
            ((2 * Real.pi * Complex.I) * (polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) *
              (z 0 - c 0) ^ p.2 * ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i))))
          = fun p : (Fin n → ℕ) × ℕ => polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) *
              (z 0 - c 0) ^ p.2 * ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i) := by
        funext p; rw [inv_mul_cancel_left₀ htpi]
    rw [hfun2] at hint2
    have hval : (2 * Real.pi * Complex.I)⁻¹ * ((2 * Real.pi * Complex.I) *
        polyCauchy (n + 1) f c R z) = polyCauchy (n + 1) f c R z :=
      inv_mul_cancel_left₀ htpi _
    rw [hval] at hint2
    have heq2 : (fun α : Fin (n + 1) → ℕ => polyCoeff (n + 1) f c R α * ∏ j, (z j - c j) ^ (α j)) ∘
          ⇑((Equiv.prodComm (Fin n → ℕ) ℕ).trans (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)))
        = fun p : (Fin n → ℕ) × ℕ => polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) *
            (z 0 - c 0) ^ p.2 * ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i) := by
      funext p
      change polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) *
            ∏ j : Fin (n + 1), (z j - c j) ^ (Fin.cons p.2 p.1 j)
          = polyCoeff (n + 1) f c R (Fin.cons p.2 p.1) * (z 0 - c 0) ^ p.2 *
              ∏ i, (Fin.tail z i - Fin.tail c i) ^ (p.1 i)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring
    have htrans : HasSum ((fun α : Fin (n + 1) → ℕ =>
          polyCoeff (n + 1) f c R α * ∏ j, (z j - c j) ^ (α j)) ∘
          ⇑((Equiv.prodComm (Fin n → ℕ) ℕ).trans (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))))
        (polyCauchy (n + 1) f c R z) := by
      rw [heq2]
      exact hint2
    exact (Equiv.hasSum_iff (f := fun α : Fin (n + 1) → ℕ =>
        polyCoeff (n + 1) f c R α * ∏ j, (z j - c j) ^ (α j))
      ((Equiv.prodComm (Fin n → ℕ) ℕ).trans (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)))).mp htrans

/-! ## The formal multilinear series of a multi-index coefficient family -/

private noncomputable instance fintypeFiber (d n : ℕ) :
    Fintype {α : Fin d → ℕ // ∑ j, α j = n} := by
  classical
  refine Fintype.ofInjective (fun α : {α : Fin d → ℕ // ∑ j, α j = n} =>
      fun j => (⟨α.1 j, by
        have h1 : α.1 j ≤ ∑ i, α.1 i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
        omega⟩ : Fin (n + 1))) ?_
  intro a b hab
  exact Subtype.ext (funext fun j => congrArg Fin.val (congr_fun hab j))

private noncomputable def monoMap {d : ℕ} (α : Fin d → ℕ) (n : ℕ) (hα : ∑ j, α j = n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => (Fin d → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun k => ContinuousLinearMap.proj
      (((finCongr hα.symm).trans (finSigmaFinEquiv (n := α)).symm) k).1)

private lemma monoMap_apply_diag {d : ℕ} (α : Fin d → ℕ) (n : ℕ) (hα : ∑ j, α j = n)
    (y : Fin d → ℂ) :
    monoMap α n hα (fun _ => y) = ∏ j, y j ^ (α j) := by
  rw [monoMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  simp only [ContinuousLinearMap.proj_apply]
  rw [Equiv.prod_comp ((finCongr hα.symm).trans (finSigmaFinEquiv (n := α)).symm)
      (fun p : (j : Fin d) × Fin (α j) => y p.1)]
  rw [Fintype.prod_sigma (f := fun p : (j : Fin d) × Fin (α j) => y p.1)]
  simp

private lemma norm_monoMap_le {d : ℕ} (α : Fin d → ℕ) (n : ℕ) (hα : ∑ j, α j = n) :
    ‖monoMap α n hα‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := monoMap α n hα) zero_le_one ?_
  intro v
  rw [monoMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  calc ‖∏ k, (ContinuousLinearMap.proj
          (((finCongr hα.symm).trans (finSigmaFinEquiv (n := α)).symm) k).1) (v k)‖
      = ∏ k, ‖(ContinuousLinearMap.proj
          (((finCongr hα.symm).trans (finSigmaFinEquiv (n := α)).symm) k).1) (v k)‖ :=
        norm_prod _ _
    _ ≤ ∏ k, ‖v k‖ := by
        apply Finset.prod_le_prod₀
        · intro k _; positivity
        · intro k _
          rw [ContinuousLinearMap.proj_apply]
          exact norm_le_pi_norm (v k) _
    _ = 1 * ∏ k, ‖v k‖ := by rw [one_mul]

private noncomputable def mkSeries {d : ℕ} (c : (Fin d → ℕ) → ℂ) :
    FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ :=
  fun n => ∑ α : {α : Fin d → ℕ // ∑ j, α j = n}, c α.1 • monoMap α.1 n α.2

private lemma mkSeries_apply {d : ℕ} (c : (Fin d → ℕ) → ℂ) (n : ℕ) (y : Fin d → ℂ) :
    mkSeries c n (fun _ => y) =
      ∑ α : {α : Fin d → ℕ // ∑ j, α j = n}, c α.1 * ∏ j, y j ^ (α.1 j) := by
  rw [mkSeries, sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [smul_apply, smul_eq_mul, monoMap_apply_diag]

private lemma norm_mkSeries_le {d : ℕ} (c : (Fin d → ℕ) → ℂ) {M R : ℝ} (hM : 0 ≤ M)
    (hR : 0 < R) (hb : ∀ α, ‖c α‖ ≤ M * R⁻¹ ^ (∑ j, α j)) (n : ℕ) :
    ‖mkSeries c n‖ ≤ M * R⁻¹ ^ n * (n + 1) ^ d := by
  have hcard : (Fintype.card {α : Fin d → ℕ // ∑ j, α j = n} : ℝ) ≤ (n + 1) ^ d := by
    have h := Fintype.card_le_of_injective (fun α : {α : Fin d → ℕ // ∑ j, α j = n} =>
        fun j => (⟨α.1 j, by
          have h1 : α.1 j ≤ ∑ i, α.1 i :=
            Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
          omega⟩ : Fin (n + 1)))
      (fun a b hab => Subtype.ext (funext fun j => congrArg Fin.val (congr_fun hab j)))
    have h2 : Fintype.card (Fin d → Fin (n + 1)) = (n + 1) ^ d := by
      simp [Fintype.card_fun]
    rw [h2] at h
    exact_mod_cast h
  have hnonneg : 0 ≤ M * R⁻¹ ^ n := mul_nonneg hM (pow_nonneg (inv_nonneg.mpr hR.le) _)
  calc ‖mkSeries c n‖
      ≤ ∑ α : {α : Fin d → ℕ // ∑ j, α j = n}, ‖c α.1 • monoMap α.1 n α.2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _α : {α : Fin d → ℕ // ∑ j, α j = n}, M * R⁻¹ ^ n := by
        refine Finset.sum_le_sum fun α _ => ?_
        calc ‖c α.1 • monoMap α.1 n α.2‖ = ‖c α.1‖ * ‖monoMap α.1 n α.2‖ := norm_smul _ _
          _ ≤ ‖c α.1‖ * 1 := mul_le_mul_of_nonneg_left (norm_monoMap_le α.1 n α.2) (norm_nonneg _)
          _ = ‖c α.1‖ := mul_one _
          _ ≤ M * R⁻¹ ^ (∑ j, α.1 j) := hb α.1
          _ = M * R⁻¹ ^ n := by rw [show (∑ j, α.1 j) = n from α.2]
    _ = (Fintype.card {α : Fin d → ℕ // ∑ j, α j = n} : ℝ) * (M * R⁻¹ ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (n + 1) ^ d * (M * R⁻¹ ^ n) := mul_le_mul_of_nonneg_right hcard hnonneg
    _ = M * R⁻¹ ^ n * (n + 1) ^ d := by ring

private lemma summable_poly_geom (d : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d * (1 / 2 : ℝ) ^ n) := by
  have hpow : ∀ n : ℕ,
      ((n : ℝ) + 1) ^ d = ∑ k ∈ Finset.range (d + 1), (n : ℝ) ^ k * (Nat.choose d k : ℝ) := by
    intro n
    have h := add_pow (n : ℝ) 1 d
    simpa using h
  have heq : (fun n : ℕ => ((n : ℝ) + 1) ^ d * (1 / 2 : ℝ) ^ n)
      = fun n : ℕ => ∑ k ∈ Finset.range (d + 1),
          (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n * (Nat.choose d k : ℝ) := by
    funext n
    rw [hpow n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq]
  refine summable_sum fun k _ => ?_
  exact (summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)).mul_right
    (Nat.choose d k : ℝ)


/-! ## Assembly -/

private noncomputable def halfR (R : ℝ) (hR : 0 < R) : ℝ≥0 := ⟨R / 2, by positivity⟩

private theorem hasFPowerSeriesOnBall_mkSeries {d : ℕ} {f : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ}
    {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall c R)) :
    HasFPowerSeriesOnBall f (mkSeries (polyCoeff d f c R)) c ((halfR R hR : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f c)) (hM c (mem_closedBall_self hR.le))
  have hb : ∀ α : Fin d → ℕ, ‖polyCoeff d f c R α‖ ≤ M * R⁻¹ ^ (∑ j, α j) :=
    fun α => norm_polyCoeff_le d hR hM0 hM α
  have hr : ((halfR R hR : ℝ≥0) : ℝ) = R / 2 := rfl
  have hrpos : 0 < halfR R hR := by
    show (0 : ℝ) < R / 2
    positivity
  refine ⟨?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_summable (p := mkSeries (polyCoeff d f c R))
      (r := halfR R hR) ?_
    have hgoal : (fun n : ℕ => ‖mkSeries (polyCoeff d f c R) n‖ * ((halfR R hR : ℝ≥0) : ℝ) ^ n)
        = fun n : ℕ => ‖mkSeries (polyCoeff d f c R) n‖ * (R / 2) ^ n := by
      funext n
      rw [hr]
    rw [hgoal]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_poly_geom d).mul_left M)
    calc ‖mkSeries (polyCoeff d f c R) n‖ * (R / 2) ^ n
        ≤ (M * R⁻¹ ^ n * (n + 1) ^ d) * (R / 2) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa using norm_mkSeries_le (polyCoeff d f c R) hM0 hR hb n
      _ = M * (((n : ℝ) + 1) ^ d * (1 / 2 : ℝ) ^ n) := by
          have hR2 : R⁻¹ * (R / 2) = (1 / 2 : ℝ) := by field_simp
          rw [show (M * R⁻¹ ^ n * (n + 1) ^ d) * (R / 2) ^ n
              = M * ((n : ℝ) + 1) ^ d * (R⁻¹ ^ n * (R / 2) ^ n) by ring,
            ← mul_pow, hR2]
          ring
  · exact ENNReal.coe_pos.mpr hrpos
  · intro y hy
    rw [Metric.eball_coe, mem_ball_zero_iff] at hy
    have hyR : ‖y‖ < R := by
      rw [hr] at hy
      linarith [hy, hR]
    have hmem : c + y ∈ ball c R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hyR
    have hHS : HasSum (fun α : Fin d → ℕ => polyCoeff d f c R α * ∏ j, (y j) ^ (α j))
        (f (c + y)) := by
      rw [polyCauchy_eq_of_differentiableOn hR hf (c + y) hmem]
      simpa only [Pi.add_apply, add_sub_cancel_left] using
        polyCauchy_hasSum d hR hf (c + y) hmem
    let e : (Fin d → ℕ) ≃ (Σ n : ℕ, {α : Fin d → ℕ // ∑ j, α j = n}) :=
      { toFun := fun α => ⟨∑ j, α j, ⟨α, rfl⟩⟩
        invFun := fun q => q.2.1
        left_inv := fun α => rfl
        right_inv := fun q => by
          obtain ⟨n, ⟨α, hα⟩⟩ := q
          cases hα
          rfl }
    have h1 : HasSum (fun q : (Σ n : ℕ, {α : Fin d → ℕ // ∑ j, α j = n}) =>
        polyCoeff d f c R q.2.1 * ∏ j, (y j) ^ (q.2.1 j)) (f (c + y)) :=
      (Equiv.hasSum_iff (f := fun q : (Σ n : ℕ, {α : Fin d → ℕ // ∑ j, α j = n}) =>
          polyCoeff d f c R q.2.1 * ∏ j, (y j) ^ (q.2.1 j)) e).mp (by
        show HasSum (fun α : Fin d → ℕ => polyCoeff d f c R α * ∏ j, (y j) ^ (α j)) (f (c + y))
        exact hHS)
    have h2 := h1.sigma (fun n => hasSum_fintype (fun α : {α : Fin d → ℕ // ∑ j, α j = n} =>
      polyCoeff d f c R α.1 * ∏ j, (y j) ^ (α.1 j)))
    have hfin : (fun n : ℕ => mkSeries (polyCoeff d f c R) n (fun _ => y))
        = fun n : ℕ => ∑ α : {α : Fin d → ℕ // ∑ j, α j = n},
            polyCoeff d f c R α.1 * ∏ j, (y j) ^ (α.1 j) := by
      funext n
      exact mkSeries_apply (polyCoeff d f c R) n y
    rw [hfin]
    exact h2

/-- **Holomorphic functions on a polydisc are analytic.** If `f : (Fin d → ℂ) → ℂ` is complex
differentiable on a closed polydisc `closedBall c R` with `R > 0`, then `f` is analytic at `c`.

This is the several-variable form of "holomorphic ⟹ analytic" (Hartogs' theorem / the
Cauchy integral formula for polydiscs). -/
theorem analyticAt_of_differentiableOn_closedBall {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    {c : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) : AnalyticAt ℂ f c :=
  (hasFPowerSeriesOnBall_mkSeries hR hf).analyticAt

end Commons.Analysis.Complex