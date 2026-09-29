import Mathlib

/-!
# Frobenius at a regular singular point of exponent `0`

The analytic core of `Work.C17.logP_local_structure`: if `P2 z = (z - s) * q z` with `q`
analytic at `s`, `q s ≠ 0`, and `P1`, `P0` analytic at `s` with `P1 s = q s` (so that the two
indicial exponents at `s` are `0, 0`), then for every `a₀` the homogeneous equation has a
solution holomorphic on a ball around `s` with `y s = a₀`.

Strategy (this file).  After the shift `t = z - s` the equation is equivalent to the first order
system `t·U₁' = U₂`, `U₂' = B·U₂ + D·(U₁ + a₀)` with `U₁ = y - a₀`, `U₂ = t·y'`, where
`B = 1 - P1/Q`, `D = -P0/Q`.  The system is solved by a Picard iteration whose operator is

`T(U) = (prim (dslope (prim G) 0), prim G)`,   `G = B·U₂ + D·(U₁ + a₀)`,

where `prim` is a primitive and `dslope` divides by `t`; the point of this shape is that the
singular factor `1/t` is absorbed by `dslope`/`prim`, and `G` is linear in `U` with small
coefficients, so `T` is a contraction on a small ball.
-/

namespace Work.C17f

open Metric Filter
open scoped Topology

noncomputable section

/-! ## A chosen primitive -/

/-- A primitive, vanishing at `0`, of a function which is holomorphic on `ball 0 R`
(and `0` if `h` is not differentiable there, which we never use). -/
def prim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : ℝ) (h : ℂ → E) : ℂ → E := by
  classical
  exact if hh : DifferentiableOn ℂ h (Metric.ball 0 R) then
    (hh.isExactOn_ball.with_val_at 0 0).choose
  else 0

lemma prim_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {R : ℝ} {h : ℂ → E} (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) :
    prim R h 0 = 0 := by
  rw [prim, dif_pos hh]
  exact (Classical.choose_spec (hh.isExactOn_ball.with_val_at 0 0)).1

lemma prim_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {R : ℝ} {h : ℂ → E} (hh : DifferentiableOn ℂ h (Metric.ball 0 R)) :
    ∀ z ∈ Metric.ball 0 R, HasDerivAt (prim R h) (h z) z := by
  intro z hz
  rw [prim, dif_pos hh]
  exact (Classical.choose_spec (hh.isExactOn_ball.with_val_at 0 0)).2 z hz

/-! ## Two mean-value estimates for primitives -/

theorem prim_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g h : ℂ → E} {s : Set ℂ} {C : ℝ} (hs : Convex ℝ s) (h0 : (0 : ℂ) ∈ s)
    (hg : ∀ z ∈ s, HasDerivAt g (h z) z) (hg0 : g 0 = 0)
    (hb : ∀ z ∈ s, ‖h z‖ ≤ C) :
    ∀ z ∈ s, ‖g z‖ ≤ ‖z‖ * C := by
  intro z hz
  have hdiff : ∀ w ∈ s, DifferentiableAt ℂ g w := fun w hw => (hg w hw).differentiableAt
  have hderiv : ∀ w ∈ s, ‖deriv g w‖ ≤ C := by
    intro w hw
    rw [(hg w hw).deriv]
    exact hb w hw
  have h1 := hs.norm_image_sub_le_of_norm_deriv_le hdiff hderiv h0 hz
  simp only [hg0, sub_zero] at h1
  calc ‖g z‖ ≤ C * ‖z‖ := h1
    _ = ‖z‖ * C := mul_comm _ _

theorem dslope_prim_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g h : ℂ → E} {s : Set ℂ} {C : ℝ} (hs : Convex ℝ s) (h0 : (0 : ℂ) ∈ s)
    (hg : ∀ z ∈ s, HasDerivAt g (h z) z) (hg0 : g 0 = 0)
    (hb : ∀ z ∈ s, ‖h z‖ ≤ C) :
    ∀ z ∈ s, ‖dslope g 0 z‖ ≤ C := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [dslope_same, (hg 0 h0).deriv]
    exact hb 0 h0
  · have hbnd := prim_norm_bound hs h0 hg hg0 hb z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [dslope_of_ne g hz0, slope_def_module, sub_zero, hg0, sub_zero, norm_smul, norm_inv]
    calc ‖z‖⁻¹ * ‖g z‖ ≤ ‖z‖⁻¹ * (‖z‖ * C) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = C := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hzpos), one_mul]

/-- Locally uniform convergence on an open ball follows from uniform convergence on every
strictly smaller closed ball. -/
theorem locally_uniform_of_closedBall {E ι : Type*} [PseudoMetricSpace E] {l : Filter ι}
    {F : ι → ℂ → E} {f : ℂ → E} {R : ℝ}
    (h : ∀ r : ℝ, r < R → TendstoUniformlyOn F f l (Metric.closedBall (0 : ℂ) r)) :
    TendstoLocallyUniformlyOn F f l (Metric.ball (0 : ℂ) R) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
  obtain ⟨r, hxr, hrR⟩ := exists_between hx
  have hxmem : x ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hxr
  refine ⟨Metric.ball 0 r, mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hxmem), ?_⟩
  have h' := h r hrR
  rw [Metric.tendstoUniformlyOn_iff] at h'
  filter_upwards [h' ε hε] with n hn y hy
  exact hn y (Metric.ball_subset_closedBall hy)

/-! ## The singular first order system `t·U' = M t·U` -/

/-- The right hand side `G = B·U₂ + D·(U₁ + a₀)` of the second equation. -/
def src (B D : ℂ → ℂ) (a₀ : ℂ) (U : (ℂ → ℂ) × (ℂ → ℂ)) : ℂ → ℂ :=
  fun t => B t * U.2 t + D t * (U.1 t + a₀)

/-- The divided primitive `t ↦ (prim g t)/t`. -/
def Jop (R : ℝ) (g : ℂ → ℂ) : ℂ → ℂ := fun t => dslope (prim R g) 0 t

/-- The Picard operator of the singular system. -/
def TopOp (B D : ℂ → ℂ) (a₀ : ℂ) (R : ℝ) (U : (ℂ → ℂ) × (ℂ → ℂ)) : (ℂ → ℂ) × (ℂ → ℂ) :=
  (prim R (Jop R (src B D a₀ U)), prim R (src B D a₀ U))

/-- `dslope` is additive in the function (for differentiable functions). -/
lemma dslope_fun_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {a : ℂ} (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) :
    dslope (fun z => f z - g z) a = fun z => dslope f a z - dslope g a z := by
  funext z
  rcases eq_or_ne z a with rfl | hz
  · rw [dslope_same, dslope_same, dslope_same]
    exact deriv_sub hf hg
  · rw [dslope_of_ne _ hz, dslope_of_ne f hz, dslope_of_ne g hz,
      slope_def_module, slope_def_module, slope_def_module]
    simp only [smul_sub]
    abel

/-- **Existence for the singular system.** If `B, D` are holomorphic on `ball 0 R` with
`‖B z‖ + ‖D z‖ ≤ K` there and `R·K ≤ 1/2`, then the system `t·U₁' = U₂`,
`U₂' = B·U₂ + D·(U₁ + a₀)` has a holomorphic solution on `ball 0 R` with `U₁ 0 = U₂ 0 = 0`. -/
theorem system_solution {B D : ℂ → ℂ} {a₀ : ℂ} {R K : ℝ} (hR : 0 < R)
    (hB : DifferentiableOn ℂ B (Metric.ball 0 R)) (hD : DifferentiableOn ℂ D (Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖D z‖ + ‖B z‖ ≤ K)
    (hKR : R * K ≤ 1 / 2) :
    ∃ U₁ U₂ : ℂ → ℂ, DifferentiableOn ℂ U₁ (Metric.ball 0 R) ∧
      DifferentiableOn ℂ U₂ (Metric.ball 0 R) ∧ U₁ 0 = 0 ∧ U₂ 0 = 0 ∧
      (∀ z ∈ Metric.ball 0 R, z * deriv U₁ z = U₂ z) ∧
      (∀ z ∈ Metric.ball 0 R, deriv U₁ z = dslope U₂ 0 z) ∧
      (∀ z ∈ Metric.ball 0 R, deriv U₂ z = B z * U₂ z + D z * (U₁ z + a₀)) := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hR.le
    have h1 : (0 : ℝ) ≤ ‖D 0‖ + ‖B 0‖ := by positivity
    linarith [hbound 0 h0]
  have hq0 : 0 ≤ R * K := mul_nonneg hR.le hK0
  set x₀ : (ℂ → ℂ) × (ℂ → ℂ) := ((fun _ => (0 : ℂ)), (fun _ => (0 : ℂ))) with hx₀
  set Uf : ℕ → (ℂ → ℂ) × (ℂ → ℂ) := fun n => (TopOp B D a₀ R)^[n] x₀ with hUf
  have hUf0 : Uf 0 = x₀ := by simp only [hUf, Function.iterate_zero_apply]
  have hUfsucc : ∀ n, Uf (n + 1) = TopOp B D a₀ R (Uf n) := by
    intro n
    simp only [hUf, Function.iterate_succ_apply']
  have hx0fst : x₀.1 = fun _ => (0 : ℂ) := rfl
  have hx0snd : x₀.2 = fun _ => (0 : ℂ) := rfl
  have hUf0val1 : ∀ z : ℂ, (Uf 0).1 z = 0 := by intro z; rw [hUf0, hx0fst]
  have hUf0val2 : ∀ z : ℂ, (Uf 0).2 z = 0 := by intro z; rw [hUf0, hx0snd]
  have hSrcdiff : ∀ U : (ℂ → ℂ) × (ℂ → ℂ), DifferentiableOn ℂ U.1 (Metric.ball 0 R) →
      DifferentiableOn ℂ U.2 (Metric.ball 0 R) →
      DifferentiableOn ℂ (src B D a₀ U) (Metric.ball 0 R) := by
    intro U h1 h2
    exact (hB.mul h2).add (hD.mul (h1.add (differentiableOn_const a₀)))
  have hPrimdiff : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) →
      DifferentiableOn ℂ (prim R g) (Metric.ball 0 R) := by
    intro g hg z hz
    exact (prim_hasDerivAt hg z hz).differentiableAt.differentiableWithinAt
  have hJdiff : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) →
      DifferentiableOn ℂ (Jop R g) (Metric.ball 0 R) := by
    intro g hg
    exact (Complex.differentiableOn_dslope (f := prim R g) (c := 0)
      (Metric.ball_mem_nhds 0 hR)).mpr (hPrimdiff g hg)
  have hTopdiff : ∀ U : (ℂ → ℂ) × (ℂ → ℂ), DifferentiableOn ℂ U.1 (Metric.ball 0 R) →
      DifferentiableOn ℂ U.2 (Metric.ball 0 R) →
      DifferentiableOn ℂ (TopOp B D a₀ R U).1 (Metric.ball 0 R) ∧
      DifferentiableOn ℂ (TopOp B D a₀ R U).2 (Metric.ball 0 R) := by
    intro U h1 h2
    have hG := hSrcdiff U h1 h2
    exact ⟨hPrimdiff _ (hJdiff _ hG), hPrimdiff _ hG⟩
  have hTopzero : ∀ U : (ℂ → ℂ) × (ℂ → ℂ), DifferentiableOn ℂ U.1 (Metric.ball 0 R) →
      DifferentiableOn ℂ U.2 (Metric.ball 0 R) →
      (TopOp B D a₀ R U).1 0 = 0 ∧ (TopOp B D a₀ R U).2 0 = 0 := by
    intro U h1 h2
    have hG := hSrcdiff U h1 h2
    exact ⟨prim_zero (hJdiff _ hG), prim_zero hG⟩
  have hUhol : ∀ n, DifferentiableOn ℂ (Uf n).1 (Metric.ball 0 R) ∧
      DifferentiableOn ℂ (Uf n).2 (Metric.ball 0 R) := by
    intro n
    induction n with
    | zero => rw [hUf0, hx0fst, hx0snd]; exact ⟨differentiableOn_const 0, differentiableOn_const 0⟩
    | succ n ih =>
      rw [hUfsucc n]
      exact hTopdiff _ ih.1 ih.2
  have hUval1 : ∀ n, (Uf n).1 0 = 0 := by
    intro n
    induction n with
    | zero => rw [hUf0, hx0fst]
    | succ n ih => rw [hUfsucc n]; exact (hTopzero _ (hUhol n).1 (hUhol n).2).1
  have hUval2 : ∀ n, (Uf n).2 0 = 0 := by
    intro n
    induction n with
    | zero => rw [hUf0, hx0snd]
    | succ n ih => rw [hUfsucc n]; exact (hTopzero _ (hUhol n).1 (hUhol n).2).2
  have hLip : ∀ (V W : (ℂ → ℂ) × (ℂ → ℂ)) (r x y : ℝ), 0 ≤ r → r < R →
      DifferentiableOn ℂ V.1 (Metric.ball 0 R) → DifferentiableOn ℂ V.2 (Metric.ball 0 R) →
      DifferentiableOn ℂ W.1 (Metric.ball 0 R) → DifferentiableOn ℂ W.2 (Metric.ball 0 R) →
      (∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖V.1 w - W.1 w‖ ≤ x) →
      (∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖V.2 w - W.2 w‖ ≤ y) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        ‖(TopOp B D a₀ R V).1 z - (TopOp B D a₀ R W).1 z‖ ≤ ‖z‖ * (K * max x y) ∧
        ‖(TopOp B D a₀ R V).2 z - (TopOp B D a₀ R W).2 z‖ ≤ ‖z‖ * (K * max x y) := by
    intro V W r x y hr hrR hV1 hV2 hW1 hW2 hx hy z hz
    have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := Metric.mem_closedBall_self hr
    have hx0 : 0 ≤ x := le_trans (norm_nonneg _) (hx 0 hzero)
    have hy0 : 0 ≤ y := le_trans (norm_nonneg _) (hy 0 hzero)
    have hM0 : 0 ≤ max x y := le_max_of_le_left hx0
    have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R := by
      intro w hw
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    have hSV := hSrcdiff V hV1 hV2
    have hSW := hSrcdiff W hW1 hW2
    have hGs : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖src B D a₀ V w - src B D a₀ W w‖ ≤ K * max x y := by
      intro w hw
      have hwR : w ∈ Metric.closedBall (0 : ℂ) R := by
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw ⊢
        linarith
      have hK := hbound w hwR
      have h1 := hx w hw
      have h2 := hy w hw
      have hVW : src B D a₀ V w - src B D a₀ W w
          = B w * (V.2 w - W.2 w) + D w * (V.1 w - W.1 w) := by
        simp only [src]; ring
      rw [hVW]
      calc ‖B w * (V.2 w - W.2 w) + D w * (V.1 w - W.1 w)‖
          ≤ ‖B w * (V.2 w - W.2 w)‖ + ‖D w * (V.1 w - W.1 w)‖ := norm_add_le _ _
        _ = ‖B w‖ * ‖V.2 w - W.2 w‖ + ‖D w‖ * ‖V.1 w - W.1 w‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖B w‖ * max x y + ‖D w‖ * max x y := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (le_trans h2 (le_max_right x y)) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (le_trans h1 (le_max_left x y)) (norm_nonneg _))
        _ = (‖B w‖ + ‖D w‖) * max x y := by ring
        _ ≤ K * max x y := by
            rw [add_comm]
            exact mul_le_mul_of_nonneg_right hK hM0
    have hprimdiff : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        HasDerivAt (fun t => prim R (src B D a₀ V) t - prim R (src B D a₀ W) t)
          (src B D a₀ V w - src B D a₀ W w) w := by
      intro w hw
      exact (prim_hasDerivAt hSV w (hsub hw)).sub (prim_hasDerivAt hSW w (hsub hw))
    have hprim0 : (fun t => prim R (src B D a₀ V) t - prim R (src B D a₀ W) t) 0 = 0 := by
      simp only [prim_zero hSV, prim_zero hSW, sub_self]
    constructor
    · have hJeq : ∀ w, Jop R (src B D a₀ V) w - Jop R (src B D a₀ W) w
          = dslope (fun t => prim R (src B D a₀ V) t - prim R (src B D a₀ W) t) 0 w := by
        intro w
        have h := congrFun (dslope_fun_sub (f := prim R (src B D a₀ V))
          (g := prim R (src B D a₀ W)) (a := 0)
          ((hPrimdiff _ hSV).differentiableAt (Metric.ball_mem_nhds 0 hR))
          ((hPrimdiff _ hSW).differentiableAt (Metric.ball_mem_nhds 0 hR))) w
        simp only [Jop]
        exact h.symm
      have hderiv1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
          HasDerivAt (fun t => prim R (Jop R (src B D a₀ V)) t
              - prim R (Jop R (src B D a₀ W)) t)
            (dslope (fun t => prim R (src B D a₀ V) t - prim R (src B D a₀ W) t) 0 w) w := by
        intro w hw
        have h1 : HasDerivAt (prim R (Jop R (src B D a₀ V))) (Jop R (src B D a₀ V) w) w :=
          prim_hasDerivAt (hJdiff _ hSV) w (hsub hw)
        have h2 : HasDerivAt (prim R (Jop R (src B D a₀ W))) (Jop R (src B D a₀ W) w) w :=
          prim_hasDerivAt (hJdiff _ hSW) w (hsub hw)
        have h3 := h1.sub h2
        rwa [hJeq w] at h3
      have hzero1 : (fun t => prim R (Jop R (src B D a₀ V)) t
          - prim R (Jop R (src B D a₀ W)) t) 0 = 0 := by
        simp only [prim_zero (hJdiff _ hSV), prim_zero (hJdiff _ hSW), sub_self]
      have hslope : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
          ‖dslope (fun t => prim R (src B D a₀ V) t - prim R (src B D a₀ W) t) 0 w‖
            ≤ K * max x y :=
        dslope_prim_norm_bound (convex_closedBall 0 r) hzero hprimdiff hprim0 hGs
      exact prim_norm_bound (convex_closedBall 0 r) hzero hderiv1 hzero1 hslope z hz
    · exact prim_norm_bound (convex_closedBall 0 r) hzero hprimdiff hprim0 hGs z hz
  have hIter : ∀ n (r : ℝ), 0 ≤ r → r < R → ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ‖(Uf (n + 1)).1 z - (Uf n).1 z‖ ≤ ((R * K) * ‖a₀‖) * (R * K) ^ n ∧
      ‖(Uf (n + 1)).2 z - (Uf n).2 z‖ ≤ ((R * K) * ‖a₀‖) * (R * K) ^ n := by
    intro n
    induction n with
    | zero =>
      intro r hr hrR z hz
      have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R := by
        intro w hw
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
        simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
        linarith
      have hsrcdiff : DifferentiableOn ℂ (src B D a₀ x₀) (Metric.ball 0 R) :=
        hSrcdiff x₀ (differentiableOn_const 0) (differentiableOn_const 0)
      have hbound' : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖(src B D a₀ x₀) w‖ ≤ K * ‖a₀‖ := by
        intro w hw
        have hwR : w ∈ Metric.closedBall (0 : ℂ) R := by
          simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw ⊢
          linarith
        have hK := hbound w hwR
        have hDw : ‖D w‖ ≤ K := by linarith [norm_nonneg (B w)]
        calc ‖(src B D a₀ x₀) w‖ = ‖D w * a₀‖ := by simp only [src, hx0fst, hx0snd]; ring_nf
          _ = ‖D w‖ * ‖a₀‖ := norm_mul _ _
          _ ≤ K * ‖a₀‖ := mul_le_mul_of_nonneg_right hDw (norm_nonneg _)
      have hprimzero : prim R (src B D a₀ x₀) 0 = 0 := prim_zero hsrcdiff
      have hd : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
          HasDerivAt (prim R (src B D a₀ x₀)) ((src B D a₀ x₀) w) w :=
        fun w hw => prim_hasDerivAt hsrcdiff w (hsub hw)
      have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
      have hTx0_1 : ‖(TopOp B D a₀ R x₀).1 z‖ ≤ ‖z‖ * (K * ‖a₀‖) :=
        prim_norm_bound (convex_closedBall 0 r) (Metric.mem_closedBall_self hr)
          (fun w hw => prim_hasDerivAt (hJdiff _ hsrcdiff) w (hsub hw))
          (prim_zero (hJdiff _ hsrcdiff))
          (dslope_prim_norm_bound (convex_closedBall 0 r) (Metric.mem_closedBall_self hr)
            hd hprimzero hbound') z hz
      have hTx0_2 : ‖(TopOp B D a₀ R x₀).2 z‖ ≤ ‖z‖ * (K * ‖a₀‖) :=
        prim_norm_bound (convex_closedBall 0 r) (Metric.mem_closedBall_self hr)
          hd hprimzero hbound' z hz
      have hx1 : x₀.1 z = 0 := by simp [hx0fst]
      have hx2 : x₀.2 z = 0 := by simp [hx0snd]
      rw [hUfsucc 0, hUf0, hx1, hx2, sub_zero, sub_zero]
      constructor
      · refine le_trans hTx0_1 ?_
        calc ‖z‖ * (K * ‖a₀‖) ≤ r * (K * ‖a₀‖) :=
              mul_le_mul_of_nonneg_right hzr (by positivity)
          _ ≤ R * (K * ‖a₀‖) := mul_le_mul_of_nonneg_right (le_of_lt hrR) (by positivity)
          _ = ((R * K) * ‖a₀‖) * (R * K) ^ 0 := by rw [pow_zero, mul_one]; ring
      · refine le_trans hTx0_2 ?_
        calc ‖z‖ * (K * ‖a₀‖) ≤ r * (K * ‖a₀‖) :=
              mul_le_mul_of_nonneg_right hzr (by positivity)
          _ ≤ R * (K * ‖a₀‖) := mul_le_mul_of_nonneg_right (le_of_lt hrR) (by positivity)
          _ = ((R * K) * ‖a₀‖) * (R * K) ^ 0 := by rw [pow_zero, mul_one]; ring
    | succ n ih =>
      intro r hr hrR z hz
      have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
      have hxy1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
          ‖(Uf (n+1)).1 w - (Uf n).1 w‖ ≤ ((R * K) * ‖a₀‖) * (R * K) ^ n :=
        fun w hw => (ih r hr hrR w hw).1
      have hxy2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
          ‖(Uf (n+1)).2 w - (Uf n).2 w‖ ≤ ((R * K) * ‖a₀‖) * (R * K) ^ n :=
        fun w hw => (ih r hr hrR w hw).2
      obtain ⟨hb1, hb2⟩ := hLip (Uf (n+1)) (Uf n) r _ _ hr hrR (hUhol (n+1)).1 (hUhol (n+1)).2
        (hUhol n).1 (hUhol n).2 hxy1 hxy2 z hz
      rw [max_self] at hb1 hb2
      have h1a : (Uf (n+1+1)).1 z = (TopOp B D a₀ R (Uf (n+1))).1 z := by rw [hUfsucc (n+1)]
      have h1b : (Uf (n+1)).1 z = (TopOp B D a₀ R (Uf n)).1 z := by rw [hUfsucc n]
      have h2a : (Uf (n+1+1)).2 z = (TopOp B D a₀ R (Uf (n+1))).2 z := by rw [hUfsucc (n+1)]
      have h2b : (Uf (n+1)).2 z = (TopOp B D a₀ R (Uf n)).2 z := by rw [hUfsucc n]
      constructor
      · rw [h1a, h1b]
        refine le_trans hb1 ?_
        calc ‖z‖ * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n))
            ≤ r * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n)) :=
              mul_le_mul_of_nonneg_right hzr (by positivity)
          _ ≤ R * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n)) :=
              mul_le_mul_of_nonneg_right (le_of_lt hrR) (by positivity)
          _ = ((R * K) * ‖a₀‖) * (R * K) ^ (n+1) := by rw [pow_succ]; ring
      · rw [h2a, h2b]
        refine le_trans hb2 ?_
        calc ‖z‖ * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n))
            ≤ r * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n)) :=
              mul_le_mul_of_nonneg_right hzr (by positivity)
          _ ≤ R * (K * (((R * K) * ‖a₀‖) * (R * K) ^ n)) :=
              mul_le_mul_of_nonneg_right (le_of_lt hrR) (by positivity)
          _ = ((R * K) * ‖a₀‖) * (R * K) ^ (n+1) := by rw [pow_succ]; ring
  have hq1 : ‖R * K‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    linarith
  have hsummable : Summable (fun n : ℕ => ((R * K) * ‖a₀‖) * (R * K) ^ n) :=
    (summable_geometric_of_norm_lt_one hq1).mul_left _
  set L₁ : ℂ → ℂ := fun z => ∑' n, ((Uf (n + 1)).1 z - (Uf n).1 z) with hL₁
  set L₂ : ℂ → ℂ := fun z => ∑' n, ((Uf (n + 1)).2 z - (Uf n).2 z) with hL₂
  have hUnif1 : ∀ r : ℝ, r < R →
      TendstoUniformlyOn (fun (N : Finset ℕ) z => ∑ n ∈ N, ((Uf (n + 1)).1 z - (Uf n).1 z))
        L₁ Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
    intro r hrR
    rw [hL₁]
    refine tendstoUniformlyOn_tsum hsummable (fun n z hz => ?_)
    by_cases hr : 0 ≤ r
    · exact (hIter n r hr hrR z hz).1
    · rw [Metric.closedBall_eq_empty.mpr (not_le.mp hr)] at hz
      exact absurd hz (Set.notMem_empty _)
  have hUnif2 : ∀ r : ℝ, r < R →
      TendstoUniformlyOn (fun (N : Finset ℕ) z => ∑ n ∈ N, ((Uf (n + 1)).2 z - (Uf n).2 z))
        L₂ Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
    intro r hrR
    rw [hL₂]
    refine tendstoUniformlyOn_tsum hsummable (fun n z hz => ?_)
    by_cases hr : 0 ≤ r
    · exact (hIter n r hr hrR z hz).2
    · rw [Metric.closedBall_eq_empty.mpr (not_le.mp hr)] at hz
      exact absurd hz (Set.notMem_empty _)
  have hConv1 : ∀ r : ℝ, r < R → TendstoUniformlyOn (fun (N : ℕ) z => (Uf N).1 z) L₁
      Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
    intro r hrR
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := (Metric.tendstoUniformlyOn_iff.mp (hUnif1 r hrR)) ε hε
    rw [Filter.eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    filter_upwards [eventually_ge_atTop (a.sup id + 1)] with N hN z hz
    have hsub : a ⊆ Finset.range N := by
      intro x hx
      simp only [Finset.mem_range]
      have h1 : x ≤ a.sup id := Finset.le_sup (f := id) hx
      omega
    have huse := ha (Finset.range N) hsub z hz
    have hsum : (∑ n ∈ Finset.range N, ((Uf (n + 1)).1 z - (Uf n).1 z)) = (Uf N).1 z := by
      rw [Finset.sum_range_sub (fun n => (Uf n).1 z), hUf0val1 z, sub_zero]
    rwa [hsum] at huse
  have hConv2 : ∀ r : ℝ, r < R → TendstoUniformlyOn (fun (N : ℕ) z => (Uf N).2 z) L₂
      Filter.atTop (Metric.closedBall (0 : ℂ) r) := by
    intro r hrR
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := (Metric.tendstoUniformlyOn_iff.mp (hUnif2 r hrR)) ε hε
    rw [Filter.eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    filter_upwards [eventually_ge_atTop (a.sup id + 1)] with N hN z hz
    have hsub : a ⊆ Finset.range N := by
      intro x hx
      simp only [Finset.mem_range]
      have h1 : x ≤ a.sup id := Finset.le_sup (f := id) hx
      omega
    have huse := ha (Finset.range N) hsub z hz
    have hsum : (∑ n ∈ Finset.range N, ((Uf (n + 1)).2 z - (Uf n).2 z)) = (Uf N).2 z := by
      rw [Finset.sum_range_sub (fun n => (Uf n).2 z), hUf0val2 z, sub_zero]
    rwa [hsum] at huse
  have hLhol1 : DifferentiableOn ℂ L₁ (Metric.ball 0 R) :=
    (locally_uniform_of_closedBall hConv1).differentiableOn
      (Eventually.of_forall fun N => (hUhol N).1) Metric.isOpen_ball
  have hLhol2 : DifferentiableOn ℂ L₂ (Metric.ball 0 R) :=
    (locally_uniform_of_closedBall hConv2).differentiableOn
      (Eventually.of_forall fun N => (hUhol N).2) Metric.isOpen_ball
  have hFixpt : ∀ z ∈ Metric.ball (0 : ℂ) R,
      L₁ z = (TopOp B D a₀ R (L₁, L₂)).1 z ∧ L₂ z = (TopOp B D a₀ R (L₁, L₂)).2 z := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    obtain ⟨r, hzr, hrR⟩ := exists_between hz
    have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt (norm_nonneg z) hzr)
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) r := by
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzr.le
    have hzr' : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzcl
    have hc1 := hConv1 r hrR
    have hc2 := hConv2 r hrR
    rw [Metric.tendstoUniformlyOn_iff] at hc1 hc2
    have key : ∀ ε > 0, dist (L₁ z) ((TopOp B D a₀ R (L₁, L₂)).1 z) ≤ ε ∧
        dist (L₂ z) ((TopOp B D a₀ R (L₁, L₂)).2 z) ≤ ε := by
      intro ε hε
      have hpos : 0 < 1 + r * K := by positivity
      set η := ε / (1 + r * K) with hη
      have hηpos : 0 < η := by positivity
      have hηeq : η * (1 + r * K) = ε := by
        rw [hη]; field_simp
      obtain ⟨N, hN⟩ := eventually_atTop.mp ((hc1 η hηpos).and (hc2 η hηpos))
      have hN1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, dist (L₁ w) ((Uf N).1 w) < η :=
        fun w hw => (hN N le_rfl).1 w hw
      have hN2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, dist (L₂ w) ((Uf N).2 w) < η :=
        fun w hw => (hN N le_rfl).2 w hw
      have hN1' : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖(Uf N).1 w - L₁ w‖ ≤ η := by
        intro w hw
        have := hN1 w hw
        rw [dist_eq_norm, norm_sub_rev] at this
        exact le_of_lt this
      have hN2' : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖(Uf N).2 w - L₂ w‖ ≤ η := by
        intro w hw
        have := hN2 w hw
        rw [dist_eq_norm, norm_sub_rev] at this
        exact le_of_lt this
      obtain ⟨hb1, hb2⟩ := hLip (Uf N) (L₁, L₂) r η η hr0 hrR (hUhol N).1 (hUhol N).2
        hLhol1 hLhol2 hN1' hN2' z hzcl
      rw [max_self] at hb1 hb2
      have hN1'' : ‖L₁ z - (Uf (N+1)).1 z‖ < η := by
        have h' := (hN (N+1) (by omega)).1 z hzcl
        rwa [dist_eq_norm] at h'
      have hN2'' : ‖L₂ z - (Uf (N+1)).2 z‖ < η := by
        have h' := (hN (N+1) (by omega)).2 z hzcl
        rwa [dist_eq_norm] at h'
      constructor
      · have htri : ‖L₁ z - (TopOp B D a₀ R (L₁, L₂)).1 z‖
            ≤ ‖L₁ z - (Uf (N+1)).1 z‖ + ‖(Uf (N+1)).1 z - (TopOp B D a₀ R (L₁,L₂)).1 z‖ := by
          have h := norm_add_le (L₁ z - (Uf (N+1)).1 z)
            ((Uf (N+1)).1 z - (TopOp B D a₀ R (L₁,L₂)).1 z)
          rwa [sub_add_sub_cancel] at h
        rw [dist_eq_norm]
        calc ‖L₁ z - (TopOp B D a₀ R (L₁, L₂)).1 z‖
            ≤ η + ‖(Uf (N+1)).1 z - (TopOp B D a₀ R (L₁,L₂)).1 z‖ :=
              le_trans htri (add_le_add (le_of_lt hN1'') le_rfl)
          _ ≤ η + r * (K * η) := by
              refine add_le_add le_rfl ?_
              have h2 : ‖(Uf (N+1)).1 z - (TopOp B D a₀ R (L₁,L₂)).1 z‖
                  ≤ ‖z‖ * (K * η) := by
                rw [hUfsucc N]
                exact hb1
              exact le_trans h2 (mul_le_mul_of_nonneg_right hzr' (by positivity))
          _ = ε := by rw [← hηeq]; ring
      · have htri : ‖L₂ z - (TopOp B D a₀ R (L₁, L₂)).2 z‖
            ≤ ‖L₂ z - (Uf (N+1)).2 z‖ + ‖(Uf (N+1)).2 z - (TopOp B D a₀ R (L₁,L₂)).2 z‖ := by
          have h := norm_add_le (L₂ z - (Uf (N+1)).2 z)
            ((Uf (N+1)).2 z - (TopOp B D a₀ R (L₁,L₂)).2 z)
          rwa [sub_add_sub_cancel] at h
        rw [dist_eq_norm]
        calc ‖L₂ z - (TopOp B D a₀ R (L₁, L₂)).2 z‖
            ≤ η + ‖(Uf (N+1)).2 z - (TopOp B D a₀ R (L₁,L₂)).2 z‖ :=
              le_trans htri (add_le_add (le_of_lt hN2'') le_rfl)
          _ ≤ η + r * (K * η) := by
              refine add_le_add le_rfl ?_
              have h2 : ‖(Uf (N+1)).2 z - (TopOp B D a₀ R (L₁,L₂)).2 z‖
                  ≤ ‖z‖ * (K * η) := by
                rw [hUfsucc N]
                exact hb2
              exact le_trans h2 (mul_le_mul_of_nonneg_right hzr' (by positivity))
          _ = ε := by rw [← hηeq]; ring
    constructor
    · apply eq_of_forall_dist_le
      intro ε hε
      exact (key ε hε).1
    · apply eq_of_forall_dist_le
      intro ε hε
      exact (key ε hε).2
  have hL1zero : L₁ 0 = 0 := by
    rw [hL₁]
    simp only [hUval1, sub_self, tsum_zero]
  have hL2zero : L₂ 0 = 0 := by
    rw [hL₂]
    simp only [hUval2, sub_self, tsum_zero]
  have hsrcL : DifferentiableOn ℂ (src B D a₀ (L₁, L₂)) (Metric.ball 0 R) :=
    hSrcdiff (L₁, L₂) hLhol1 hLhol2
  have hder2 : ∀ z ∈ Metric.ball 0 R,
      deriv L₂ z = B z * L₂ z + D z * (L₁ z + a₀) := by
    intro z hz
    have hHD : HasDerivAt (prim R (src B D a₀ (L₁, L₂))) (src B D a₀ (L₁, L₂) z) z :=
      prim_hasDerivAt hsrcL z hz
    have heq : prim R (src B D a₀ (L₁, L₂)) =ᶠ[𝓝 z] L₂ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact ((hFixpt w hw).2).symm
    have hderiv2 : deriv L₂ z = src B D a₀ (L₁, L₂) z :=
      (hHD.congr_of_eventuallyEq heq.symm).deriv
    rw [hderiv2]
    rfl
  have hder1 : ∀ z ∈ Metric.ball 0 R, z * deriv L₁ z = L₂ z := by
    intro z hz
    have hHD : HasDerivAt (prim R (Jop R (src B D a₀ (L₁, L₂))))
        (Jop R (src B D a₀ (L₁, L₂)) z) z :=
      prim_hasDerivAt (hJdiff _ hsrcL) z hz
    have heq : prim R (Jop R (src B D a₀ (L₁, L₂))) =ᶠ[𝓝 z] L₁ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact ((hFixpt w hw).1).symm
    have hderivz : deriv L₁ z = Jop R (src B D a₀ (L₁, L₂)) z :=
      (hHD.congr_of_eventuallyEq heq.symm).deriv
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [hderivz, zero_mul]
      exact hL2zero.symm
    · have hval : prim R (src B D a₀ (L₁, L₂)) z = L₂ z := (hFixpt z hz).2.symm
      have hval0 : prim R (src B D a₀ (L₁, L₂)) 0 = 0 := prim_zero hsrcL
      have hstep : deriv L₁ z = z⁻¹ * (L₂ z - 0) := by
        rw [hderivz]
        simp only [Jop]
        rw [dslope_of_ne _ hz0, slope_def_module, sub_zero, hval, hval0, sub_zero,
          smul_eq_mul]
      rw [hstep, sub_zero, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  have hder1b : ∀ z ∈ Metric.ball 0 R, deriv L₁ z = dslope L₂ 0 z := by
    intro z hz
    have hHD : HasDerivAt (prim R (Jop R (src B D a₀ (L₁, L₂))))
        (Jop R (src B D a₀ (L₁, L₂)) z) z :=
      prim_hasDerivAt (hJdiff _ hsrcL) z hz
    have heq : prim R (Jop R (src B D a₀ (L₁, L₂))) =ᶠ[𝓝 z] L₁ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact ((hFixpt w hw).1).symm
    have hderivz : deriv L₁ z = Jop R (src B D a₀ (L₁, L₂)) z :=
      (hHD.congr_of_eventuallyEq heq.symm).deriv
    rw [hderivz]
    show dslope (prim R (src B D a₀ (L₁, L₂))) 0 z = dslope L₂ 0 z
    rcases eq_or_ne z 0 with rfl | hz0
    · have h0 : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
      rw [dslope_same, dslope_same, (prim_hasDerivAt hsrcL 0 h0).deriv, hder2 0 h0]
      rfl
    · rw [dslope_of_ne _ hz0, dslope_of_ne _ hz0, slope_def_module, slope_def_module,
        sub_zero]
      congr 1
      have hval : prim R (src B D a₀ (L₁, L₂)) z = L₂ z := (hFixpt z hz).2.symm
      have hval0 : prim R (src B D a₀ (L₁, L₂)) 0 = 0 := prim_zero hsrcL
      rw [hval, hval0, hL2zero]
  exact ⟨L₁, L₂, hLhol1, hLhol2, hL1zero, hL2zero, hder1, hder1b, hder2⟩

/-! ## Shifting the equation to the singular point -/

/-- Local differentiability and nonvanishing after shifting an analytic datum to `0`. -/
theorem analytic_shift_ball' {q P1 P0 : ℂ → ℂ} {s : ℂ}
    (hq : AnalyticAt ℂ q s) (hqs : q s ≠ 0) (hP1 : AnalyticAt ℂ P1 s)
    (hP0 : AnalyticAt ℂ P0 s) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun t => q (s + t)) (Metric.ball 0 ρ) ∧
      DifferentiableOn ℂ (fun t => P1 (s + t)) (Metric.ball 0 ρ) ∧
      DifferentiableOn ℂ (fun t => P0 (s + t)) (Metric.ball 0 ρ) ∧
      (∀ t ∈ Metric.ball 0 ρ, q (s + t) ≠ 0) := by
  have hshift : ∀ f : ℂ → ℂ, AnalyticAt ℂ f s → AnalyticAt ℂ (fun t => f (s + t)) 0 := by
    intro f hf
    have h2 : AnalyticAt ℂ (fun t : ℂ => s + t) 0 :=
      (analyticAt_const (v := s)).add analyticAt_id
    have hf' : AnalyticAt ℂ f ((fun t : ℂ => s + t) 0) := by simpa using hf
    have h3 := hf'.comp h2
    exact h3
  have h1 : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ (fun u => q (s + u)) t :=
    (hshift q hq).eventually_analyticAt
  have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ (fun u => P1 (s + u)) t :=
    (hshift P1 hP1).eventually_analyticAt
  have h3 : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ (fun u => P0 (s + u)) t :=
    (hshift P0 hP0).eventually_analyticAt
  have h4 : ∀ᶠ t in 𝓝 (0 : ℂ), (fun u => q (s + u)) t ≠ 0 := by
    have h0 : (fun u : ℂ => q (s + u)) 0 ≠ 0 := by simpa using hqs
    exact (hshift q hq).continuousAt.eventually_ne h0
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp ((h1.and h2).and (h3.and h4))
  exact ⟨ρ, hρ,
    AnalyticOnNhd.differentiableOn fun t ht => (hsub ht).1.1,
    AnalyticOnNhd.differentiableOn fun t ht => (hsub ht).1.2,
    AnalyticOnNhd.differentiableOn fun t ht => (hsub ht).2.1,
    fun t ht => (hsub ht).2.2⟩

/-- Transporting a solution of the shifted equation back to the original variable. -/
theorem shift_ode' {q Q P1 P1s P0 P0s : ℂ → ℂ} {Y : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hQ : ∀ t : ℂ, Q t = q (s + t)) (hP1 : ∀ t : ℂ, P1s t = P1 (s + t))
    (hP0 : ∀ t : ℂ, P0s t = P0 (s + t))
    (hY : DifferentiableOn ℂ Y (Metric.ball 0 R))
    (hYd : DifferentiableOn ℂ (deriv Y) (Metric.ball 0 R))
    (hode : ∀ t ∈ Metric.ball 0 R,
      t * Q t * deriv (deriv Y) t + P1s t * deriv Y t + P0s t * Y t = 0)
    (ha : Y 0 = a) :
    DifferentiableOn ℂ (fun z => Y (z - s)) (Metric.ball s R) ∧
      (fun z => Y (z - s)) s = a ∧
      ∀ z ∈ Metric.ball s R,
        (z - s) * q z * deriv (deriv (fun z => Y (z - s))) z
          + P1 z * deriv (fun z => Y (z - s)) z + P0 z * (fun z => Y (z - s)) z = 0 := by
  have hmem : ∀ z ∈ Metric.ball s R, z - s ∈ Metric.ball 0 R := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    simpa using hz
  have hdiff : DifferentiableOn ℂ (fun z => Y (z - s)) (Metric.ball s R) :=
    hY.comp (differentiableOn_id.sub (differentiableOn_const s)) hmem
  have hderiv : ∀ z ∈ Metric.ball s R, deriv (fun z => Y (z - s)) z = deriv Y (z - s) := by
    intro z hz
    have h1 : DifferentiableAt ℂ Y (z - s) :=
      (hY (z - s) (hmem z hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z hz))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - s) z := by fun_prop
    rw [show deriv (fun z : ℂ => Y (z - s)) z = deriv (Y ∘ fun w : ℂ => w - s) z from rfl,
      deriv_comp z h1 h2]
    simp
  have hderiv2 : ∀ z ∈ Metric.ball s R,
      deriv (deriv (fun z => Y (z - s))) z = deriv (deriv Y) (z - s) := by
    intro z hz
    have hev : deriv (fun z => Y (z - s)) =ᶠ[𝓝 z] fun w => deriv Y (w - s) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact hderiv w hw
    rw [hev.deriv_eq]
    have h1 : DifferentiableAt ℂ (deriv Y) (z - s) :=
      (hYd (z - s) (hmem z hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z hz))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - s) z := by fun_prop
    rw [show deriv (fun w : ℂ => deriv Y (w - s)) z
        = deriv ((deriv Y) ∘ fun w : ℂ => w - s) z from rfl, deriv_comp z h1 h2]
    simp
  have hQs : ∀ z : ℂ, Q (z - s) = q z := by
    intro z; rw [hQ]; ring_nf
  have hP1s' : ∀ z : ℂ, P1s (z - s) = P1 z := by
    intro z; rw [hP1]; ring_nf
  have hP0s' : ∀ z : ℂ, P0s (z - s) = P0 z := by
    intro z; rw [hP0]; ring_nf
  refine ⟨hdiff, ?_, fun z hz => ?_⟩
  · show Y (s - s) = a
    rw [sub_self]; exact ha
  · rw [hderiv2 z hz, hderiv z hz, ← hQs z, ← hP1s' z, ← hP0s' z]
    exact hode (z - s) (hmem z hz)

theorem frobenius_double_exponent_zero {P2 P1 P0 q : ℂ → ℂ} {s : ℂ} (a₀ : ℂ)
    (hP2 : ∀ z : ℂ, P2 z = (z - s) * q z)
    (hq : AnalyticAt ℂ q s) (hqs : q s ≠ 0)
    (hP1 : AnalyticAt ℂ P1 s) (hres : P1 s = q s)
    (hP0 : AnalyticAt ℂ P0 s) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ y : ℂ → ℂ,
      DifferentiableOn ℂ y (Metric.ball s δ) ∧ y s = a₀ ∧
      ∀ z ∈ Metric.ball s δ, P2 z * deriv (deriv y) z + P1 z * deriv y z + P0 z * y z = 0 := by
  obtain ⟨ρ, hρ, hQdiff, hP1sdiff, hP0sdiff, hQne⟩ := analytic_shift_ball' hq hqs hP1 hP0
  set Q : ℂ → ℂ := fun t => q (s + t) with hQ
  set P1s : ℂ → ℂ := fun t => P1 (s + t) with hP1s
  set P0s : ℂ → ℂ := fun t => P0 (s + t) with hP0s
  have hQd : DifferentiableOn ℂ Q (Metric.ball 0 ρ) := hQdiff
  have hP1sd : DifferentiableOn ℂ P1s (Metric.ball 0 ρ) := hP1sdiff
  have hP0sd : DifferentiableOn ℂ P0s (Metric.ball 0 ρ) := hP0sdiff
  have hQ0P : Q 0 = P1s 0 := by
    simp only [hQ, hP1s]
    simpa using hres.symm
  set B : ℂ → ℂ := fun t => dslope (fun u => Q u - P1s u) 0 t / Q t with hB
  set D : ℂ → ℂ := fun t => -(P0s t) / Q t with hD
  have hBdiff : DifferentiableOn ℂ B (Metric.ball 0 ρ) := by
    rw [hB]
    exact ((Complex.differentiableOn_dslope (f := fun u => Q u - P1s u) (c := 0)
      (Metric.ball_mem_nhds 0 hρ)).mpr (hQd.sub hP1sd)).div hQd (fun z hz => hQne z hz)
  have hDdiff : DifferentiableOn ℂ D (Metric.ball 0 ρ) := by
    rw [hD]
    exact (hP0sd.neg).div hQd (fun z hz => hQne z hz)
  have hsubc : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hcont : ContinuousOn (fun z => ‖D z‖ + ‖B z‖) (Metric.closedBall 0 (ρ / 2)) :=
    ((hDdiff.continuousOn.norm).mono hsubc).add ((hBdiff.continuousOn.norm).mono hsubc)
  have hKc : IsCompact (Metric.closedBall (0 : ℂ) (ρ / 2)) := isCompact_closedBall (0 : ℂ) (ρ / 2)
  obtain ⟨K, hK⟩ := hKc.exists_bound_of_continuousOn hcont
  have hK' : ∀ z ∈ Metric.closedBall 0 (ρ / 2), ‖D z‖ + ‖B z‖ ≤ K := by
    intro z hz
    have h1 := hK z hz
    have h2 : (0 : ℝ) ≤ ‖D z‖ + ‖B z‖ := by positivity
    rwa [Real.norm_of_nonneg h2] at h1
  have hK0 : 0 ≤ K := le_trans (by positivity : (0 : ℝ) ≤ ‖D 0‖ + ‖B 0‖)
    (hK' 0 (Metric.mem_closedBall_self (by positivity)))
  set R : ℝ := min (ρ / 2) (1 / (2 * (K + 1))) with hR
  have hRpos : 0 < R := by
    rw [hR]; exact lt_min (by positivity) (by positivity)
  have hRle : R ≤ ρ / 2 := by rw [hR]; exact min_le_left _ _
  have hKR : R * K ≤ 1 / 2 := by
    have h1 : R ≤ 1 / (2 * (K + 1)) := by rw [hR]; exact min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (K + 1) := by positivity
    calc R * K ≤ (1 / (2 * (K + 1))) * K := mul_le_mul_of_nonneg_right h1 hK0
      _ = K / (2 * (K + 1)) := by ring
      _ ≤ 1 / 2 := by
          refine le_of_mul_le_mul_right ?_ h2
          have hL : K / (2 * (K + 1)) * (2 * (K + 1)) = K := by
            rw [div_mul_cancel₀ _ (ne_of_gt h2)]
          have hR : (1 / 2) * (2 * (K + 1)) = K + 1 := by ring
          rw [hL, hR]
          linarith
  have hBdiffR : DifferentiableOn ℂ B (Metric.ball 0 R) :=
    hBdiff.mono (Metric.ball_subset_ball (by linarith))
  have hDdiffR : DifferentiableOn ℂ D (Metric.ball 0 R) :=
    hDdiff.mono (Metric.ball_subset_ball (by linarith))
  have hboundR : ∀ z ∈ Metric.closedBall 0 R, ‖D z‖ + ‖B z‖ ≤ K :=
    fun z hz => hK' z (Metric.closedBall_subset_closedBall (by linarith) hz)
  obtain ⟨U₁, U₂, hU₁d, hU₂d, hU₁0, hU₂0, hrel1, hrel2, hder2⟩ :=
    system_solution (a₀ := a₀) hRpos hBdiffR hDdiffR hboundR hKR
  set Y : ℂ → ℂ := fun t => a₀ + U₁ t with hYdef
  have hYd : DifferentiableOn ℂ Y (Metric.ball 0 R) := by
    rw [hYdef]
    exact (differentiableOn_const a₀).add hU₁d
  have hY0 : Y 0 = a₀ := by simp [hYdef, hU₁0]
  have hderivY : ∀ z ∈ Metric.ball 0 R, deriv Y z = deriv U₁ z := by
    intro z hz
    rw [hYdef]
    exact (((hU₁d z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.const_add
      a₀).deriv
  have hdslopediff : DifferentiableOn ℂ (dslope U₂ 0) (Metric.ball 0 R) :=
    (Complex.differentiableOn_dslope (f := U₂) (c := 0) (Metric.ball_mem_nhds 0 hRpos)).mpr hU₂d
  have hYdd : DifferentiableOn ℂ (deriv Y) (Metric.ball 0 R) :=
    hdslopediff.congr (fun z hz => (hderivY z hz).trans (hrel2 z hz))
  have hQ0 : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hRpos
  have hode : ∀ t ∈ Metric.ball 0 R,
      t * Q t * deriv (deriv Y) t + P1s t * deriv Y t + P0s t * Y t = 0 := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · have hdY0 : deriv Y 0 = -(P0s 0) / Q 0 * a₀ := by
        rw [hderivY 0 hQ0, hrel2 0 hQ0, dslope_same, hder2 0 hQ0, hU₂0, hU₁0, hD]
        ring
      have hQ0' : Q 0 ≠ 0 := hQne 0 (Metric.mem_ball_self hρ)
      rw [hdY0, hY0, ← hQ0P]
      field_simp
      ring
    · have htmem : t ∈ Metric.ball 0 R := ht
      have htρ : t ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at htmem ⊢
        linarith [hRle]
      have hQt : Q t ≠ 0 := hQne t htρ
      have hYt : deriv Y t = U₂ t / t := by
        rw [hderivY t htmem, hrel2 t htmem, dslope_of_ne _ ht0, slope_def_module,
          smul_eq_mul, sub_zero]
        field_simp
        rw [hU₂0, sub_zero]
      have hYtt : deriv (deriv Y) t = (deriv U₂ t * t - U₂ t) / t ^ 2 := by
        have hev1 : deriv Y =ᶠ[𝓝 t] dslope U₂ 0 := by
          filter_upwards [Metric.isOpen_ball.mem_nhds htmem] with w hw
          exact (hderivY w hw).trans (hrel2 w hw)
        rw [hev1.deriv_eq]
        have hev2 : dslope U₂ 0 =ᶠ[𝓝 t] fun w => U₂ w / w := by
          filter_upwards [Metric.ball_mem_nhds t (norm_pos_iff.mpr ht0)] with w hw
          rw [Metric.mem_ball, dist_eq_norm] at hw
          have hw0 : w ≠ 0 := by
            rintro rfl
            simp at hw
          rw [dslope_of_ne _ hw0, slope_def_module, smul_eq_mul, sub_zero, hU₂0, sub_zero,
            div_eq_inv_mul]
        rw [hev2.deriv_eq]
        have hd : deriv (fun w : ℂ => U₂ w / w) t = (deriv U₂ t * t - U₂ t) / t ^ 2 := by
          rw [show (fun w : ℂ => U₂ w / w) = U₂ / id from rfl,
            deriv_div (hU₂d.differentiableAt (Metric.isOpen_ball.mem_nhds htmem))
              differentiableAt_id ht0]
          simp
        exact hd
      have hBrel : B t = ((Q t - P1s t) / t) / Q t := by
        rw [hB]
        dsimp only
        rw [dslope_of_ne _ ht0, slope_def_module, smul_eq_mul, sub_zero, hQ0P, sub_self,
          sub_zero, div_eq_mul_inv]
        ring
      have hDrel : D t = -(P0s t) / Q t := by rw [hD]
      rw [hYt, hYtt, hder2 t htmem, hBrel, hDrel, hYdef]
      field_simp
      ring
  obtain ⟨hydiff, hyeq, hyode⟩ := shift_ode' (fun t => rfl) (fun t => rfl) (fun t => rfl)
    hYd hYdd hode hY0
  refine ⟨R, hRpos, fun z => Y (z - s), hydiff, hyeq, fun z hz => ?_⟩
  have h := hyode z hz
  rw [hP2 z]
  exact h

end

end Work.C17f
