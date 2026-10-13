import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.sin_complete_Ioc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory

/-- `∫_0^{π/2} cos (c θ) dθ`, with the degenerate case `c = 0` isolated. -/
theorem integral_cos_mul_Iθ (c : ℝ) :
    ∫ θ in (0:ℝ)..(Real.pi/2), Real.cos (c * θ)
      = if c = 0 then Real.pi/2 else Real.sin (c * Real.pi/2) / c := by
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    rw [show (∫ θ in (0:ℝ)..(Real.pi/2), Real.cos (0 * θ))
        = ∫ _θ in (0:ℝ)..(Real.pi/2), (1:ℝ) from
      intervalIntegral.integral_congr (fun θ _ => by rw [zero_mul, Real.cos_zero])]
    rw [intervalIntegral.integral_const]
    simp
  · rw [if_neg hc, intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x) hc]
    rw [show c * 0 = 0 by ring, integral_cos, Real.sin_zero, sub_zero,
      show c * (Real.pi / 2) = c * Real.pi / 2 by ring]
    simp only [smul_eq_mul]
    ring

/-- Orthogonality and normalisation of the Dirichlet sine system on `Iθ = [0, π/2]`:
`∫_{Iθ} sin (2(n+1)θ) sin (2(m+1)θ) dθ = (π/4) δ_{nm}`. -/
theorem sin_sin_int (n m : ℕ) :
    ∫ θ in Work.Spaces.Iθ, Real.sin (2 * (n + 1) * θ) * Real.sin (2 * (m + 1) * θ)
      = if n = m then Real.pi / 4 else 0 := by
  rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
  set a : ℝ := 2 * ((n:ℝ)+1) with ha
  set b : ℝ := 2 * ((m:ℝ)+1) with hb
  have hpt : ∀ θ : ℝ, Real.sin (2 * (n + 1) * θ) * Real.sin (2 * (m + 1) * θ)
      = (1/2) * Real.cos ((a - b) * θ) - (1/2) * Real.cos ((a + b) * θ) := by
    intro θ
    have e1 : Real.sin (2 * (n + 1) * θ) = Real.sin (a * θ) := by rw [ha]
    have e2 : Real.sin (2 * (m + 1) * θ) = Real.sin (b * θ) := by rw [hb]
    have e3 : (a - b) * θ = a * θ - b * θ := by ring
    have e4 : (a + b) * θ = a * θ + b * θ := by ring
    rw [e1, e2, e3, e4]
    have key : Real.cos (a * θ - b * θ) - Real.cos (a * θ + b * θ)
        = 2 * (Real.sin (a * θ) * Real.sin (b * θ)) := by
      rw [Real.cos_sub, Real.cos_add]; ring
    linarith
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hi1 : IntervalIntegrable (fun θ : ℝ => (1/2:ℝ) * Real.cos ((a - b) * θ)) volume 0 (Real.pi/2) :=
    (by fun_prop : Continuous fun θ : ℝ => (1/2:ℝ) * Real.cos ((a - b) * θ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => (1/2:ℝ) * Real.cos ((a + b) * θ)) volume 0 (Real.pi/2) :=
    (by fun_prop : Continuous fun θ : ℝ => (1/2:ℝ) * Real.cos ((a + b) * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_mul_Iθ (a - b), integral_cos_mul_Iθ (a + b)]
  have hab : (0:ℝ) < a + b := by rw [ha, hb]; positivity
  have hB : Real.sin ((a + b) * Real.pi / 2) = 0 := by
    rw [Real.sin_eq_zero_iff]
    exact ⟨(n:ℤ) + (m:ℤ) + 2, by rw [ha, hb]; push_cast; ring⟩
  rw [if_neg (ne_of_gt hab), hB, zero_div, mul_zero, sub_zero]
  have hab' : a - b = 0 ↔ n = m := by
    rw [ha, hb]
    constructor
    · intro h
      have h' : ((n:ℝ)+1) = ((m:ℝ)+1) := by linarith
      have h2 : (n:ℝ) = (m:ℝ) := by linarith
      exact Nat.cast_injective h2
    · intro h; subst h; ring
  by_cases hnm : n = m
  · rw [if_pos (hab'.mpr hnm), if_pos hnm]
    ring
  · rw [if_neg (fun h => hnm (hab'.mp h))]
    rw [if_neg hnm]
    have hA : Real.sin ((a - b) * Real.pi / 2) = 0 := by
      rw [Real.sin_eq_zero_iff]
      exact ⟨(n:ℤ) - (m:ℤ), by rw [ha, hb]; push_cast; ring⟩
    rw [hA, zero_div]
    ring

/-- **Completeness of the Dirichlet sine system on `Iθ = [0, π/2]`**: a square integrable
function of which every even sine coefficient vanishes is zero a.e. -/
theorem sin_system_complete {f : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h : ∀ n : ℕ, ∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2 * (n + 1) * θ) = 0) :
    f =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] 0 := by
  have hL : (0:ℝ) < Real.pi/2 := by positivity
  have hmeas : (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2)))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl]
    exact MeasureTheory.restrict_Ioc_eq_restrict_Icc
  have hmem' : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))) := hmeas.symm ▸ hmem
  have h' : ∀ n : ℕ, 0 < n →
      ∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (n * Real.pi * θ / (Real.pi/2)) = 0 := by
    intro n hn
    have h2 := h (n - 1)
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)] at h2
    rw [show (∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (n * Real.pi * θ / (Real.pi/2)))
        = ∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (2 * (((n - 1 : ℕ) : ℝ) + 1) * θ) from by
      apply intervalIntegral.integral_congr
      intro θ _
      show f θ * Real.sin ((n:ℝ) * Real.pi * θ / (Real.pi/2))
        = f θ * Real.sin (2 * (((n - 1 : ℕ) : ℝ) + 1) * θ)
      have hsub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring
      have key : (n : ℝ) * Real.pi * θ / (Real.pi/2) = 2 * (n:ℝ) * θ := by
        field_simp
      have key2 : 2 * (((n - 1 : ℕ) : ℝ) + 1) * θ = 2 * (n:ℝ) * θ := by rw [hsub]
      rw [key, key2], h2]
  have hfin := sin_complete_Ioc hL hmem' h'
  rwa [hmeas] at hfin

theorem sin2_parseval_aesm {f : ℝ → ℝ} (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
      = (Real.pi / 4) * ∑' n : ℕ,
          ((4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2 * (n + 1) * θ)) ^ 2 := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) := rfl
  haveI hfin : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hIθ, MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmem : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfm).mpr hf
  let c : ℝ := 2 / Real.sqrt Real.pi
  have hc : c * c = 4 / Real.pi := by
    have hπ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
      rw [← sq, Real.sq_sqrt Real.pi_pos.le]
    simp only [c]
    rw [div_mul_div_comm, hπ]
    norm_num
  have hg_mem : ∀ n : ℕ, MeasureTheory.MemLp (fun θ : ℝ => c * Real.sin (2*(n+1)*θ)) 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun n =>
    MeasureTheory.MemLp.of_bound ((continuous_const.mul (Real.continuous_sin.comp (by fun_prop))).aestronglyMeasurable) |c|
      (by filter_upwards with x; rw [Real.norm_eq_abs, abs_mul]
          simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (2*((n:ℝ)+1)*x)) (abs_nonneg c))
  let e : ℕ → MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n => MeasureTheory.MemLp.toLp (fun θ : ℝ => c * Real.sin (2*(n+1)*θ)) (hg_mem n)
  have he_coe : ∀ n, ((e n : ℝ → ℝ)) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun θ => c * Real.sin (2*(n+1)*θ)) :=
    fun n => MeasureTheory.MemLp.coeFn_toLp _
  have he_orth : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro n m
    rw [MeasureTheory.L2.inner_def]
    have hpt : (fun a => inner ℝ (((e n : ℝ → ℝ)) a) (((e m : ℝ → ℝ)) a))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun a => (c * Real.sin (2*(n+1)*a)) * (c * Real.sin (2*(m+1)*a))) := by
      filter_upwards [he_coe n, he_coe m] with a h1 h2
      rw [h1, h2, Real.inner_apply]
    rw [MeasureTheory.integral_congr_ae hpt]
    have hsplit : ∫ a, (c * Real.sin (2*(n+1)*a)) * (c * Real.sin (2*(m+1)*a)) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)
        = c * c * ∫ θ in Work.Spaces.Iθ, Real.sin (2*(n+1)*θ) * Real.sin (2*(m+1)*θ) := by
      rw [show (∫ a, (c * Real.sin (2*(n+1)*a)) * (c * Real.sin (2*(m+1)*a)) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = ∫ a, c * (c * (Real.sin (2*(n+1)*a) * Real.sin (2*(m+1)*a))) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from by
            apply MeasureTheory.integral_congr_ae; filter_upwards with a; ring]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring
    rw [hsplit, sin_sin_int n m, hc]
    split_ifs with h
    · field_simp
    · ring
  have hspan : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    refine sin_system_complete (MeasureTheory.Lp.memLp y) ?_
    intro n
    have h0 : inner ℝ (e n) y = 0 := by
      rw [Submodule.mem_orthogonal] at hy
      exact hy (e n) (Submodule.subset_span ⟨n, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at h0
    have h1 : ∫ a, c * (Real.sin (2*(n+1)*a) * (y : ℝ → ℝ) a) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) = 0 := by
      rw [← h0]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [he_coe n] with a ha
      rw [ha, Real.inner_apply]
      ring
    rw [MeasureTheory.integral_const_mul] at h1
    have hc0 : c ≠ 0 := by
      simp only [c]
      positivity
    have h2 : ∫ a, Real.sin (2*(n+1)*a) * (y : ℝ → ℝ) a ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hc0
      · exact h
    rw [← h2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with a
    ring
  let x : MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hmem.toLp f
  have hx_coe : (x : ℝ → ℝ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] f := MeasureTheory.MemLp.coeFn_toLp hmem
  have hxx : inner ℝ x x = ∫ θ in Work.Spaces.Iθ, (f θ)^2 := by
    rw [MeasureTheory.L2.inner_def]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hx_coe] with a ha
    rw [ha, Real.inner_apply, sq]
  have hterm : ∀ n : ℕ, inner ℝ x (e n) * inner ℝ (e n) x
      = (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2*(n+1)*θ))^2 := by
    intro n
    have h1 : inner ℝ x (e n) = c * ∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2*(n+1)*θ) := by
      rw [MeasureTheory.L2.inner_def]
      rw [show (∫ a, inner ℝ ((x : ℝ → ℝ) a) (((e n : ℝ → ℝ)) a) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ∫ a, c * (f a * Real.sin (2*(n+1)*a)) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hx_coe, he_coe n] with a ha hb
          rw [ha, hb, Real.inner_apply]; ring]
      rw [MeasureTheory.integral_const_mul]
    have h2 : inner ℝ (e n) x = c * ∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2*(n+1)*θ) := by
      rw [real_inner_comm]; exact h1
    rw [h1, h2, ← hc]
    ring
  have key := (HilbertBasis.mkOfOrthogonalEqBot he_orth hspan).tsum_inner_mul_inner x x
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at key
  rw [← hxx, ← key]
  rw [tsum_congr hterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  field_simp

end Work.FTS.EllipticEst
