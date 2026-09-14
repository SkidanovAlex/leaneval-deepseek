import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.Analysis.Calculus.tendsto_of_tendsto_average_of_deriv_bound
import Submission.Commons.Analysis.Calculus.tendsto_inv_mul_intervalIntegral_sq_mul_second_deriv
import Submission.Commons.Analysis.Calculus.intervalIntegrable_of_continuousOn_Ioo_of_bound
import Submission.Commons.Analysis.InnerProduct.tendsto_zero_of_forall_inner_tendsto_zero
import Submission.NBody.MarchalClusterCoord
import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.MarchalClusterShapeLimit

/-!
# Ferrario--Terracini's `as:lim2`: `t^2 s_i'' -> 0`

The last ingredient of Ferrario--Terracini's asymptotics of a colliding cluster (`propo:asy`) is
that the second derivative of the normalised configuration vanishes after multiplication by `t^2`.

The proof is the Tauberian argument of the paper (`lemma:tech`): for
`phi(t) = t^2 s_i''(t)` the identity `∫_0^t phi = t^2 s_i'(t) - 2 ∫_0^t tau s_i'(tau) dtau`
together with `t s_i'(t) -> 0` (`as:lim1`) shows that the running averages of `phi` vanish, while
the a priori bounds `|t^2 s_i''| <= K1`, `|t^3 s_i'''| <= K2` show `|t phi'(t)| <= 2|phi(t)| + K2`.
The comparison lemma `Commons.Analysis.Calculus.tendsto_of_tendsto_average_of_deriv_bound` then
yields `phi -> 0`.

Because the components of the normalised configuration are `E`-valued (body positions live in `E`),
the scalar Tauberian lemma is applied to the scalar functions `t ↦ ⟪b j, s_i(t)⟫` for an
orthonormal basis `(b j)` of `E`, and the conclusion for the vector-valued `t^2 s_i''` follows
from `Commons.Analysis.InnerProduct.tendsto_zero_of_forall_inner_tendsto_zero`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open MeasureTheory intervalIntegral
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **A scalar Tauberian lemma (Ferrario--Terracini `lemma:tech`).**

If `s : ℝ → ℝ` is twice differentiable on `(0,ε)`, `t * s'(t) → 0` at `0⁺`, and both
`t ^ 2 * s''(t)` and `t ^ 3 * s'''(t)` are bounded on `(0,ε)` (and `2 t s'(t)` is bounded, which is
needed only for the integrability of the auxiliary function), then `t ^ 2 * s''(t) → 0` at `0⁺`. -/
theorem tendsto_mul_sq_deriv_deriv_of_bounds {s : ℝ → ℝ} {ε K1 K2 C1 : ℝ} (hε : 0 < ε)
    (hbdd1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, |2 * t * deriv s t| ≤ C1)
    (hs2 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt (deriv s) (deriv (deriv s) t) t)
    (hs3 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv s)) (deriv (deriv (deriv s)) t) t)
    (hlim : Filter.Tendsto (fun t : ℝ => t * deriv s t)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hK1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, |t ^ 2 * deriv (deriv s) t| ≤ K1)
    (hK2 : ∀ t ∈ Set.Ioo (0:ℝ) ε, |t ^ 3 * deriv (deriv (deriv s)) t| ≤ K2) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * deriv (deriv s) t)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  set φ : ℝ → ℝ := fun t => t ^ 2 * deriv (deriv s) t with hφ
  have hpoint : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      HasDerivAt φ (2 * t * deriv (deriv s) t + t ^ 2 * deriv (deriv (deriv s)) t) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    exact h1.mul (hs3 t ht)
  have hderivφ : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt φ (deriv φ t) t := by
    intro t ht
    exact (hpoint t ht).congr_deriv (hpoint t ht).deriv.symm
  have hD2cont : ContinuousOn (deriv (deriv s)) (Set.Ioo (0:ℝ) ε) :=
    fun x hx => (hs3 x hx).continuousAt.continuousWithinAt
  have hD1cont : ContinuousOn (deriv s) (Set.Ioo (0:ℝ) ε) :=
    fun x hx => (hs2 x hx).continuousAt.continuousWithinAt
  have hint0 : ∀ t ∈ Set.Ioo (0:ℝ) ε, IntervalIntegrable φ volume 0 t := by
    intro t ht
    have hcont : ContinuousOn φ (Set.Ioo (0:ℝ) t) := by
      have hsub : Set.Ioo (0:ℝ) t ⊆ Set.Ioo (0:ℝ) ε :=
        fun x hx => ⟨hx.1, lt_trans hx.2 ht.2⟩
      exact (continuousOn_id.pow 2).mul (hD2cont.mono hsub)
    refine Commons.Analysis.Calculus.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (C := K1) (le_of_lt ht.1) hcont ?_
    intro x hx
    exact hK1 x ⟨hx.1, lt_trans hx.2 ht.2⟩
  have hint1 : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      IntervalIntegrable (fun u : ℝ => 2 * u * deriv s u) volume 0 t := by
    intro t ht
    have hcont : ContinuousOn (fun u : ℝ => 2 * u * deriv s u) (Set.Ioo (0:ℝ) t) := by
      have hsub : Set.Ioo (0:ℝ) t ⊆ Set.Ioo (0:ℝ) ε :=
        fun x hx => ⟨hx.1, lt_trans hx.2 ht.2⟩
      exact (continuousOn_const.mul continuousOn_id).mul (hD1cont.mono hsub)
    refine Commons.Analysis.Calculus.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (C := C1) (le_of_lt ht.1) hcont ?_
    intro x hx
    exact hbdd1 x ⟨hx.1, lt_trans hx.2 ht.2⟩
  have hexpr : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      deriv φ t = 2 * t * deriv (deriv s) t + t ^ 2 * deriv (deriv (deriv s)) t :=
    fun t ht => (hpoint t ht).deriv
  -- `deriv φ` is integrable on every `[a,b]` with `0 < a ≤ b < ε`
  have hint : ∀ a b : ℝ, 0 < a → a ≤ b → b < ε → IntervalIntegrable (deriv φ) volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), x ∈ Set.Ioo a b := by
      have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo a b)), x ∈ Set.Ioo a b :=
        ae_restrict_mem measurableSet_Ioo
      rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
    refine IntegrableOn.of_bound ?_ (measurable_deriv φ).aestronglyMeasurable
      ((2 * K1 + K2) / a) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [hae] with x hx
      have hx0 : 0 < x := lt_trans ha hx.1
      have hxa : a ≤ x := le_of_lt hx.1
      have hm : x ∈ Set.Ioo (0:ℝ) ε := ⟨hx0, lt_trans hx.2 hb⟩
      rw [Real.norm_eq_abs, hexpr x hm]
      have hL1 : |x ^ 2 * deriv (deriv s) x| ≤ K1 := hK1 x hm
      have hL2 : |x ^ 3 * deriv (deriv (deriv s)) x| ≤ K2 := hK2 x hm
      have harg1 : 2 * x * deriv (deriv s) x = 2 * (x ^ 2 * deriv (deriv s) x) / x := by
        field_simp
      have harg2 : x ^ 2 * deriv (deriv (deriv s)) x =
          (x ^ 3 * deriv (deriv (deriv s)) x) / x := by
        field_simp
      have habs1 : |2 * x * deriv (deriv s) x| = 2 * |x ^ 2 * deriv (deriv s) x| / x := by
        rw [harg1, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)), abs_of_pos hx0]
      have habs2 : |x ^ 2 * deriv (deriv (deriv s)) x| =
          |x ^ 3 * deriv (deriv (deriv s)) x| / x := by
        rw [harg2, abs_div, abs_of_pos hx0]
      calc |2 * x * deriv (deriv s) x + x ^ 2 * deriv (deriv (deriv s)) x|
          ≤ |2 * x * deriv (deriv s) x| + |x ^ 2 * deriv (deriv (deriv s)) x| := abs_add_le _ _
        _ = 2 * |x ^ 2 * deriv (deriv s) x| / x
              + |x ^ 3 * deriv (deriv (deriv s)) x| / x := by rw [habs1, habs2]
        _ ≤ 2 * K1 / a + K2 / a := by
            apply add_le_add
            · rw [div_le_div_iff₀ hx0 ha]
              nlinarith [hL1, abs_nonneg (x ^ 2 * deriv (deriv s) x), hxa]
            · rw [div_le_div_iff₀ hx0 ha]
              nlinarith [hL2, abs_nonneg (x ^ 3 * deriv (deriv (deriv s)) x), hxa]
        _ = (2 * K1 + K2) / a := by ring
  have havg : Filter.Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0:ℝ)..t, φ u)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    Commons.Analysis.Calculus.tendsto_inv_mul_intervalIntegral_sq_mul_second_deriv
      (s := s) hε hs2 hint0 hint1 hlim
  obtain ⟨A, hAc, hAb⟩ : ∃ A : ℝ → ℝ, Continuous A ∧
      ∀ t ∈ Set.Ioo (0:ℝ) ε, |deriv φ t| < A (φ t) / t := by
    refine ⟨fun y => 2 * |y| + (K2 + 1), ?_, ?_⟩
    · exact (continuous_abs.const_mul 2).add continuous_const
    · intro t ht
      have ht0 : 0 < t := ht.1
      have hL2 : |t ^ 3 * deriv (deriv (deriv s)) t| ≤ K2 := hK2 t ht
      have harg1 : 2 * t * deriv (deriv s) t = 2 * (t ^ 2 * deriv (deriv s) t) / t := by
        field_simp
      have harg2 : t ^ 2 * deriv (deriv (deriv s)) t =
          (t ^ 3 * deriv (deriv (deriv s)) t) / t := by
        field_simp
      have habs1 : |2 * t * deriv (deriv s) t| = 2 * |t ^ 2 * deriv (deriv s) t| / t := by
        rw [harg1, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)), abs_of_pos ht0]
      have habs2 : |t ^ 2 * deriv (deriv (deriv s)) t| =
          |t ^ 3 * deriv (deriv (deriv s)) t| / t := by
        rw [harg2, abs_div, abs_of_pos ht0]
      have hbound : |deriv φ t| ≤ (2 * |φ t| + K2) / t := by
        have e1 : |t ^ 2 * deriv (deriv s) t| = |φ t| := by rw [hφ]
        rw [hexpr t ht]
        calc |2 * t * deriv (deriv s) t + t ^ 2 * deriv (deriv (deriv s)) t|
            ≤ |2 * t * deriv (deriv s) t| + |t ^ 2 * deriv (deriv (deriv s)) t| := abs_add_le _ _
          _ = 2 * |φ t| / t + |t ^ 3 * deriv (deriv (deriv s)) t| / t := by
              rw [habs1, habs2, e1]
          _ ≤ 2 * |φ t| / t + K2 / t := by
              exact add_le_add le_rfl (div_le_div_of_nonneg_right hL2 (le_of_lt ht0))
          _ = (2 * |φ t| + K2) / t := by ring
      have hstrict : (2 * |φ t| + K2) / t < (2 * |φ t| + (K2 + 1)) / t := by
        apply div_lt_div_of_pos_right _ ht0
        linarith
      linarith
  exact Commons.Analysis.Calculus.tendsto_of_tendsto_average_of_deriv_bound hε hderivφ hint
    hint0 havg ⟨A, hAc, hAb⟩

/-- **`as:lim2` for one coordinate.**  For every body `i` of the colliding cluster, the second
derivative of the `i`-th coordinate of the normalised configuration satisfies `t^2 s_i''(t) → 0`. -/
theorem tendsto_mul_sq_deriv_deriv_clusterShape_coord {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    ∀ i ∈ k, Tendsto (fun t : ℝ =>
        t ^ 2 • deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  classical
  intro i _
  obtain ⟨K1, _hK1nn, hK1⟩ := exists_bound_mul_sq_deriv_deriv_clusterShape
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hIn hDn hSec hUn
  obtain ⟨K2, _hK2nn, hK2⟩ := exists_bound_mul_cube_deriv_deriv_deriv_clusterShape
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hIn hDn hSec hUn
  -- shrink the interval so that the three bounds hold everywhere on `(0, ε₃)`
  obtain ⟨ε₁, hε₁pos, hε₁le, hK1ε⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₁,
        ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ≤ K1 := by
    rw [eventually_nhdsWithin_iff] at hK1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hK1
    exact ⟨min δ ε, lt_min hδpos hε, min_le_right _ _,
      fun t ht => hδ t (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_lt_of_le ht.2 (min_le_left _ _)) ht.1⟩
  obtain ⟨ε₂, hε₂pos, hε₂le, hK2ε⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ ε₁ ∧
      ∀ t ∈ Ioo (0:ℝ) ε₂,
        ‖t ^ 3 • deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t‖ ≤ K2 := by
    rw [eventually_nhdsWithin_iff] at hK2
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hK2
    exact ⟨min δ ε₁, lt_min hδpos hε₁pos, min_le_right _ _,
      fun t ht => hδ t (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_lt_of_le ht.2 (min_le_left _ _)) ht.1⟩
  have hbd3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖t • deriv (fun τ : ℝ => (clusterShape m k (x τ)) i) t‖ ≤ 1 := by
    have h := (tendsto_smul_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep
      hv hI i).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds (by simp : ‖(0 : E)‖ < 1))] with t ht
    exact le_of_lt ht
  obtain ⟨ε₃, hε₃pos, hε₃le, hK3ε⟩ : ∃ ε₃ : ℝ, 0 < ε₃ ∧ ε₃ ≤ ε₂ ∧
      ∀ t ∈ Ioo (0:ℝ) ε₃,
        ‖t • deriv (fun τ : ℝ => (clusterShape m k (x τ)) i) t‖ ≤ 1 := by
    rw [eventually_nhdsWithin_iff] at hbd3
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hbd3
    exact ⟨min δ ε₂, lt_min hδpos hε₂pos, min_le_right _ _,
      fun t ht => hδ t (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_lt_of_le ht.2 (min_le_left _ _)) ht.1⟩
  have hε₃ε : ε₃ ≤ ε := le_trans (le_trans hε₃le hε₂le) hε₁le
  have hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ) :=
    fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)
  -- local abbreviations
  set si : ℝ → E := fun τ : ℝ => (clusterShape m k (x τ)) i with hsi
  set A : ℝ → E := deriv si with hA
  set B : ℝ → E := deriv A with hB
  set Cd : ℝ → E := deriv B with hCd
  have hs1 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt si (A t) t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hx s hs
    have hcurve := hasDerivAt_clusterShape_curve (m := m) (k := k) (x := x) (hpos t ht) hev
    have hcurve' : HasDerivAt (fun s : ℝ => clusterShape m k (x s))
        (deriv (fun s : ℝ => clusterShape m k (x s)) t) t :=
      hcurve.congr_deriv hcurve.deriv.symm
    have h := hasDerivAt_apply hcurve' i
    have heq : (deriv (fun s : ℝ => clusterShape m k (x s)) t) i = A t :=
      ((deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
        hm hk2 ht hnc hx i).eq_of_nhds).symm
    exact h.congr_deriv heq
  have hs2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt A (B t) t := by
    intro t ht
    have h := hasDerivAt_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
      hm hk2 ht hnc hx hd2 hode i
    have heq : deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t = B t := by
      rw [hB, hA]
    exact h.congr_deriv heq
  have hs3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt B (Cd t) t := by
    intro t ht
    have h := hasDerivAt_deriv_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (t := t) hm hk2 ht hnc hx hd2 hd3 hode i
    have heq : deriv (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))) t = Cd t := by
      rw [hCd, hB, hA]
    exact h.congr_deriv heq
  -- coordinatewise identification of `B` and `Cd`
  have hBcoord : ∀ t ∈ Ioo (0:ℝ) ε,
      B t = (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i := by
    intro t ht
    rw [hB, hA]
    exact (deriv_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
      hm hk2 ht hnc hx hd2 hode i).eq_of_nhds
  have hCcoord : ∀ t ∈ Ioo (0:ℝ) ε,
      Cd t = (deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t) i := by
    intro t ht
    rw [hCd, hB, hA]
    exact deriv_deriv_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
      hm hk2 ht hnc hx hd2 hd3 hode i
  -- the orthonormal basis and the coordinatewise Tauberian argument
  set b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hb
  have hkey : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun t : ℝ => ⟪b j, t ^ 2 • B t⟫_ℝ) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    intro j
    set sj : ℝ → ℝ := fun τ : ℝ => ⟪b j, si τ⟫_ℝ with hsj
    have heq1 : ∀ t ∈ Ioo (0:ℝ) ε, deriv sj t = ⟪b j, A t⟫_ℝ := by
      intro t ht
      have h := HasDerivAt.inner ℝ (hasDerivAt_const t (b j)) (hs1 t ht)
      simpa only [inner_zero_left, add_zero] using h.deriv
    have heq2 : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv sj) t = ⟪b j, B t⟫_ℝ := by
      intro t ht
      have hge : deriv sj =ᶠ[𝓝 t] (fun τ : ℝ => ⟪b j, A τ⟫_ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
        exact heq1 τ hτ
      rw [hge.deriv_eq]
      have h := HasDerivAt.inner ℝ (hasDerivAt_const t (b j)) (hs2 t ht)
      simpa only [inner_zero_left, add_zero] using h.deriv
    have heq3 : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv (deriv sj)) t = ⟪b j, Cd t⟫_ℝ := by
      intro t ht
      have hge : deriv (deriv sj) =ᶠ[𝓝 t] (fun τ : ℝ => ⟪b j, B τ⟫_ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
        exact heq2 τ hτ
      rw [hge.deriv_eq]
      have h := HasDerivAt.inner ℝ (hasDerivAt_const t (b j)) (hs3 t ht)
      simpa only [inner_zero_left, add_zero] using h.deriv
    have hsj2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv sj) (deriv (deriv sj) t) t := by
      intro t ht
      have hge : deriv sj =ᶠ[𝓝 t] (fun τ : ℝ => ⟪b j, A τ⟫_ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
        exact heq1 τ hτ
      have h := HasDerivAt.inner ℝ (hasDerivAt_const t (b j)) (hs2 t ht)
      refine (h.congr_of_eventuallyEq hge).congr_deriv ?_
      simp only [inner_zero_left, add_zero]
      exact (heq2 t ht).symm
    have hsj3 : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt (deriv (deriv sj)) (deriv (deriv (deriv sj)) t) t := by
      intro t ht
      have hge : deriv (deriv sj) =ᶠ[𝓝 t] (fun τ : ℝ => ⟪b j, B τ⟫_ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
        exact heq2 τ hτ
      have h := HasDerivAt.inner ℝ (hasDerivAt_const t (b j)) (hs3 t ht)
      refine (h.congr_of_eventuallyEq hge).congr_deriv ?_
      simp only [inner_zero_left, add_zero]
      exact (heq3 t ht).symm
    have hlimj : Tendsto (fun t : ℝ => t * deriv sj t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      have h := tendsto_smul_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε)
        (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep
        hv hI i
      have hconst : Tendsto (fun _ : ℝ => b j) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (b j)) :=
        tendsto_const_nhds
      have h2 : Tendsto (fun t : ℝ => ⟪b j, t • deriv si t⟫_ℝ)
          (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (⟪b j, (0 : E)⟫_ℝ)) :=
        hconst.inner h
      simp only [inner_zero_right] at h2
      refine Filter.Tendsto.congr' ?_ h2
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      rw [heq1 t ht, inner_smul_right]
    have hbdd1 : ∀ t ∈ Ioo (0:ℝ) ε₃, |2 * t * deriv sj t| ≤ 2 := by
      intro t ht
      have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hε₃ε⟩
      have h1 : |t * deriv sj t| ≤ 1 := by
        rw [heq1 t htε, ← inner_smul_right]
        calc |⟪b j, t • A t⟫_ℝ| ≤ ‖b j‖ * ‖t • A t‖ := abs_real_inner_le_norm _ _
          _ = ‖t • A t‖ := by rw [b.orthonormal.norm_eq_one j, one_mul]
          _ ≤ 1 := hK3ε t ht
      have hmain : |2 * t * deriv sj t| = 2 * |t * deriv sj t| := by
        have hrw : (2:ℝ) * t * deriv sj t = 2 * (t * deriv sj t) := by ring
        rw [hrw, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      calc |2 * t * deriv sj t| = 2 * |t * deriv sj t| := hmain
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 2 := by norm_num
    have hK1j : ∀ t ∈ Ioo (0:ℝ) ε₃, |t ^ 2 * deriv (deriv sj) t| ≤ K1 := by
      intro t ht
      have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hε₃ε⟩
      have h1 : t ^ 2 * ⟪b j, B t⟫_ℝ = ⟪b j, t ^ 2 • B t⟫_ℝ := by
        rw [inner_smul_right]
      calc |t ^ 2 * deriv (deriv sj) t|
          = |⟪b j, t ^ 2 • B t⟫_ℝ| := by rw [heq2 t htε, h1]
        _ ≤ ‖b j‖ * ‖t ^ 2 • B t‖ := abs_real_inner_le_norm _ _
        _ = ‖t ^ 2 • B t‖ := by rw [b.orthonormal.norm_eq_one j, one_mul]
        _ = t ^ 2 * ‖B t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
        _ ≤ t ^ 2 * ‖deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ :=
            mul_le_mul_of_nonneg_left (by rw [hBcoord t htε]; exact PiLp.norm_apply_le _ _)
              (sq_nonneg t)
        _ = ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
        _ ≤ K1 := hK1ε t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans hε₃le hε₂le)⟩
    have hK2j : ∀ t ∈ Ioo (0:ℝ) ε₃, |t ^ 3 * deriv (deriv (deriv sj)) t| ≤ K2 := by
      intro t ht
      have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hε₃ε⟩
      have h1 : t ^ 3 * ⟪b j, Cd t⟫_ℝ = ⟪b j, t ^ 3 • Cd t⟫_ℝ := by
        rw [inner_smul_right]
      calc |t ^ 3 * deriv (deriv (deriv sj)) t|
          = |⟪b j, t ^ 3 • Cd t⟫_ℝ| := by rw [heq3 t htε, h1]
        _ ≤ ‖b j‖ * ‖t ^ 3 • Cd t‖ := abs_real_inner_le_norm _ _
        _ = ‖t ^ 3 • Cd t‖ := by rw [b.orthonormal.norm_eq_one j, one_mul]
        _ = t ^ 3 * ‖Cd t‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le 3)]
        _ ≤ t ^ 3 * ‖deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t‖ :=
            mul_le_mul_of_nonneg_left (by rw [hCcoord t htε]; exact PiLp.norm_apply_le _ _)
              (pow_nonneg ht.1.le 3)
        _ = ‖t ^ 3 • deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le 3)]
        _ ≤ K2 := hK2ε t ⟨ht.1, lt_of_lt_of_le ht.2 hε₃le⟩
    have hres := tendsto_mul_sq_deriv_deriv_of_bounds (s := sj) (ε := ε₃) (K1 := K1) (K2 := K2)
      (C1 := 2) hε₃pos hbdd1 (fun t ht => hsj2 t ⟨ht.1, lt_of_lt_of_le ht.2 hε₃ε⟩)
      (fun t ht => hsj3 t ⟨ht.1, lt_of_lt_of_le ht.2 hε₃ε⟩) hlimj hK1j hK2j
    refine Filter.Tendsto.congr' ?_ hres
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    show t ^ 2 * deriv (deriv sj) t = ⟪b j, t ^ 2 • B t⟫_ℝ
    rw [heq2 t ht, inner_smul_right]
  -- passage from the inner products with the basis to the vector statement
  have hall : ∀ v : E, Tendsto (fun t : ℝ => ⟪t ^ 2 • B t, v⟫_ℝ)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    intro v
    have hexp : (fun t : ℝ => ⟪t ^ 2 • B t, v⟫_ℝ)
        = fun t : ℝ => ∑ j, ⟪b j, v⟫_ℝ * ⟪b j, t ^ 2 • B t⟫_ℝ := by
      funext t
      conv_lhs => rw [← b.sum_repr' v]
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [inner_smul_right, real_inner_comm (b j) (t ^ 2 • B t)]
    rw [hexp]
    have hsum : Tendsto (fun t : ℝ => ∑ j, ⟪b j, v⟫_ℝ * ⟪b j, t ^ 2 • B t⟫_ℝ)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (∑ j, ⟪b j, v⟫_ℝ * (0:ℝ))) :=
      tendsto_finsetSum Finset.univ
        (fun j _ => (hkey j).const_mul (⟪b j, v⟫_ℝ))
    simpa using hsum
  have hfin : Tendsto (fun t : ℝ => t ^ 2 • B t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    Commons.Analysis.InnerProduct.tendsto_zero_of_forall_inner_tendsto_zero
      (f := fun t : ℝ => t ^ 2 • B t) hall
  simpa only [hB, hA] using hfin

/-- **`as:lim2`, vector form.**  `t ^ 2 · s̈ → 0` for the colliding cluster. -/
theorem tendsto_mul_sq_deriv_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun t : ℝ => clusterInertia m k (x t) / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hDn : Tendsto (fun t : ℝ => deriv (fun s : ℝ => clusterInertia m k (x s)) t
      / t ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hSec : Tendsto (fun t : ℝ => deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)))
    (hUn : Tendsto (fun t : ℝ => clusterPotential m k (x t) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ))) :
    Tendsto (fun t : ℝ => t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hterm : ∀ i : Fin N, Tendsto
      (fun t : ℝ => ‖(t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i‖ ^ 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    intro i
    have hcomp : ∀ t ∈ Ioo (0:ℝ) ε,
        (t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i
          = t ^ 2 • deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t := by
      intro t ht
      rw [show (t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i
          = t ^ 2 • (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i from rfl,
        ← (deriv_deriv_coord_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
          hm hk2 ht hnc hx hd2 hode i).eq_of_nhds]
    by_cases hi : i ∈ k
    · have hc := (tendsto_mul_sq_deriv_deriv_clusterShape_coord (m := m) (k := k) (x := x)
        (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ) hm hk2 hε hC hν hCv hκ hnc hE hW
        hx hd2 hd3 hode hsep hv hI hIn hDn hSec hUn i hi).norm.pow 2
      refine Filter.Tendsto.congr' ?_ (by simpa using hc)
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      show ‖t ^ 2 • deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t‖ ^ 2
        = ‖(t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i‖ ^ 2
      rw [← hcomp t ht]
    · have hgi : (fun τ : ℝ => (clusterShape m k (x τ)) i) = fun _ : ℝ => (0 : E) := by
        funext τ
        rw [clusterShape_apply, cmRel_apply_of_notMem hi, smul_zero]
      have hzero : ∀ t : ℝ, deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t = 0 := by
        intro t
        have h1 : deriv (fun τ : ℝ => (clusterShape m k (x τ)) i) = fun _ : ℝ => (0 : E) := by
          rw [hgi]
          ext x
          exact deriv_const x (0 : E)
        rw [h1]
        exact deriv_const t (0 : E)
      have hgoalzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)]
          (fun t : ℝ => ‖(t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i‖ ^ 2) := by
        filter_upwards [Ioo_mem_nhdsGT hε] with t ht
        show (0 : ℝ) = ‖(t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i‖ ^ 2
        rw [hcomp t ht, hzero t, smul_zero, norm_zero]
        norm_num
      exact Filter.Tendsto.congr' hgoalzero
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
  have hnorm : Tendsto (fun t : ℝ =>
      ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ^ 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    rw [show (fun t : ℝ =>
          ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ^ 2)
        = fun t : ℝ => ∑ i : Fin N,
            ‖(t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) i‖ ^ 2 by
      funext t
      rw [PiLp.norm_sq_eq_of_L2]]
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => hterm i)
    simpa using hsum
  have hsqrt : Tendsto (fun t : ℝ =>
      Real.sqrt (‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ^ 2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp hnorm
    simpa only [Function.comp_def, Real.sqrt_zero] using h2
  rw [show (fun t : ℝ => ‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖)
      = fun t : ℝ =>
          Real.sqrt (‖t ^ 2 • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t‖ ^ 2)
      from funext fun t => (Real.sqrt_sq (norm_nonneg _)).symm]
  exact hsqrt

end Submission.NBody
