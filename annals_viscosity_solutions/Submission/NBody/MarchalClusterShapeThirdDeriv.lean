import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.MarchalJoltBound
import Submission.Commons.Analysis.Calculus.abs_rpow_seven_thirds_mul_inertia_deriv_le

/-!
# The third derivative of the normalised configuration

Ferrario--Terracini's `as:lim2` (`t^2 s_i'' -> 0`) is proved by their Tauberian lemma `lemma:tech`,
which needs `t^3 s_jolt` bounded.  With `q = sqrt(I_k) s` (the centre-of-mass-relative
configuration) and `phi = sqrt(I_k)`, the third-order Leibniz rule gives

    `q_jolt = phi_jolt * s + 3 phi'' * s' + 3 phi' * s'' + phi * s_jolt`,

so `sqrt(I_k) * s_jolt = q_jolt - phi_jolt * s - 3 phi'' * s' - 3 phi' * s''` (`eq:dddotqi`).

This file proves
* `t^(7/3) * phi_jolt` bounded (from the five already available factor bounds),
* the third-order identity above, and
* `t^3 * s_jolt` bounded.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Boundedness of `t^(7/3)` times the third derivative of `phi = sqrt(I_k)`.**  The proof
decomposes `phi_jolt = I_k_jolt/(2 sqrt I_k) - 3 I_k' I_k''/(4 (sqrt I_k)^3)
+ 3 (I_k')^3/(8 (sqrt I_k)^5)` into five convergent factors and applies
`Commons.Analysis.Calculus.abs_rpow_seven_thirds_mul_inertia_deriv_le`. -/
lemma exists_bound_rpow_seven_thirds_deriv_deriv_deriv_sqrtInertia {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
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
      * t ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |t ^ ((7:ℝ)/3)
        * deriv (deriv (deriv (fun s : ℝ => Real.sqrt (clusterInertia m k (x s))))) t| ≤ C' := by
  obtain ⟨C₃, hC₃nn, hC₃⟩ := exists_bound_rpow_five_thirds_third_deriv_clusterInertia
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hSec
  have hb1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)|
        ≤ (4:ℝ)/3 * κ + 1 := by
    have h : Tendsto (fun t : ℝ => |deriv (fun s : ℝ => clusterInertia m k (x s)) t
        / t ^ ((1:ℝ)/3)|) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |(4:ℝ)/3 * κ|) := by
      simpa only [Real.norm_eq_abs] using hDn.norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show |(4:ℝ)/3 * κ| < (4:ℝ)/3 * κ + 1 by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ)/3 * κ)]
        linarith))] with t ht
    exact le_of_lt ht
  have hb2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t * t ^ ((2:ℝ)/3)|
        ≤ (4:ℝ)/9 * κ + 1 := by
    have h : Tendsto (fun t : ℝ => |deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t
        * t ^ ((2:ℝ)/3)|) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |(4:ℝ)/9 * κ|) := by
      simpa only [Real.norm_eq_abs] using hSec.norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show |(4:ℝ)/9 * κ| < (4:ℝ)/9 * κ + 1 by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ)/9 * κ)]
        linarith))] with t ht
    exact le_of_lt ht
  have hb4 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))| ≤ (Real.sqrt κ)⁻¹ + 1 := by
    have h : Tendsto (fun t : ℝ => |t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t))|)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |(Real.sqrt κ)⁻¹|) := by
      simpa only [Real.norm_eq_abs] using
        (tendsto_rpow_two_thirds_div_sqrtInertia hm hk2 hε hκ hnc hIn).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show |(Real.sqrt κ)⁻¹| < (Real.sqrt κ)⁻¹ + 1 by
        rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg κ))]
        linarith))] with t ht
    exact le_of_lt ht
  have hb5 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |(clusterInertia m k (x t) / t ^ ((4:ℝ)/3)) ^ (-((3:ℝ)/2))|
        ≤ κ ^ (-((3:ℝ)/2)) + 1 := by
    have h : Tendsto (fun t : ℝ =>
        |(clusterInertia m k (x t) / t ^ ((4:ℝ)/3)) ^ (-((3:ℝ)/2))|)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |κ ^ (-((3:ℝ)/2))|) := by
      simpa only [Real.norm_eq_abs] using
        (hIn.rpow_const (p := -((3:ℝ)/2)) (Or.inl (ne_of_gt hκ))).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show |κ ^ (-((3:ℝ)/2))| < κ ^ (-((3:ℝ)/2)) + 1 by
        rw [abs_of_nonneg (Real.rpow_nonneg hκ.le _)]
        linarith))] with t ht
    exact le_of_lt ht
  have hb6 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      |(clusterInertia m k (x t) / t ^ ((4:ℝ)/3)) ^ (-((5:ℝ)/2))|
        ≤ κ ^ (-((5:ℝ)/2)) + 1 := by
    have h : Tendsto (fun t : ℝ =>
        |(clusterInertia m k (x t) / t ^ ((4:ℝ)/3)) ^ (-((5:ℝ)/2))|)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds |κ ^ (-((5:ℝ)/2))|) := by
      simpa only [Real.norm_eq_abs] using
        (hIn.rpow_const (p := -((5:ℝ)/2)) (Or.inl (ne_of_gt hκ))).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show |κ ^ (-((5:ℝ)/2))| < κ ^ (-((5:ℝ)/2)) + 1 by
        rw [abs_of_nonneg (Real.rpow_nonneg hκ.le _)]
        linarith))] with t ht
    exact le_of_lt ht
  refine ⟨C₃ * ((Real.sqrt κ)⁻¹ + 1) / 2
    + 3 / 4 * (((4:ℝ)/3 * κ + 1) * ((4:ℝ)/9 * κ + 1)
        * (κ ^ (-((3:ℝ)/2)) + 1))
    + 3 / 8 * (((4:ℝ)/3 * κ + 1) ^ 3 * (κ ^ (-((5:ℝ)/2)) + 1)), by positivity, ?_⟩
  filter_upwards [hb1, hb2, hC₃, hb4, hb5, hb6, Ioo_mem_nhdsGT hε] with t h1 h2 h3 h4 h5 h6 ht
  have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
  rw [(hasDerivAt_deriv_deriv_clusterSqrtInertia_curve (m := m) (k := k) (x := x) (ε := ε)
    (t := t) ht (fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)) hx hd2 hd3).deriv]
  exact Commons.Analysis.Calculus.abs_rpow_seven_thirds_mul_inertia_deriv_le
    (D1 := deriv (fun s : ℝ => clusterInertia m k (x s)) t)
    (D2 := deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) t)
    (D3 := deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t)
    (I := clusterInertia m k (x t)) (t := t)
    (b1 := (4:ℝ)/3 * κ + 1) (b2 := (4:ℝ)/9 * κ + 1) (b3 := C₃)
    (b4 := (Real.sqrt κ)⁻¹ + 1) (b5 := κ ^ (-((3:ℝ)/2)) + 1)
    (b6 := κ ^ (-((5:ℝ)/2)) + 1)
    ht.1 hIpos (by positivity) (by positivity) hC₃nn (by positivity) (by positivity) (by positivity)
    h1 h2 h3 h4 h5 h6


/-- **The third derivative of the centre-of-mass-relative configuration.** -/
lemma deriv_deriv_deriv_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hd3 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) :
    deriv (deriv (deriv (fun s : ℝ => cmRel m k (x s)))) t
      = cmRel m k (deriv (deriv (deriv x)) t) := by
  have hEq : deriv (deriv (fun s : ℝ => cmRel m k (x s)))
      =ᶠ[𝓝 t] (fun u => cmRel m k (∇_[m] (U m) (x u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact deriv_deriv_cmRel (m := m) (k := k) (x := x) (ε := ε) (t := u) hu hx hd2 hode
  have hgrad : HasDerivAt (fun u => ∇_[m] (U m) (x u)) (deriv (deriv (deriv x)) t) t := by
    have heq2 : (fun u => ∇_[m] (U m) (x u)) =ᶠ[𝓝 t] deriv (deriv x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      rw [← hode u hu, iteratedDeriv_two_eq_deriv_deriv x u]
    exact (hd3 t ht).congr_of_eventuallyEq heq2
  rw [Filter.EventuallyEq.deriv_eq hEq]
  exact (hasDerivAt_cmRel m k hgrad).deriv

/-- **The derivative of `s''`** (the normalised configuration's second derivative), i.e. the third
derivative of the normalised configuration.  This is the differentiated form of the second-order
identity `sqrt(I_k) * s'' = q'' - phi'' * s - 2 phi' * s'`. -/
theorem hasDerivAt_deriv_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hd3 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) :
    HasDerivAt (deriv (deriv (fun s : ℝ => clusterShape m k (x s))))
      ((Real.sqrt (clusterInertia m k (x t)))⁻¹ • ((cmRel m k (deriv (deriv (deriv x)) t)) - ((deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t) • (deriv (fun s : ℝ => clusterShape m k (x s)) t) + (deriv (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))) t) • (clusterShape m k (x t))) - ((2 * (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)) • (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) + (2 * (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)) • (deriv (fun s : ℝ => clusterShape m k (x s)) t))) + (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) / (Real.sqrt (clusterInertia m k (x t))) ^ 2) • ((cmRel m k (∇_[m] (U m) (x t)) - (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t) • (clusterShape m k (x t)) - (2 * (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)) • (deriv (fun s : ℝ => clusterShape m k (x s)) t)))) t := by
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  have hΦne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hpos t ht))
  have hP1 : HasDerivAt (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))
      (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t) t := by
    have h := hasDerivAt_clusterSqrtInertia_curve (m := m) (k := k) (x := x) (hpos t ht) hev
    exact h.congr_deriv h.deriv.symm
  have hP2 : HasDerivAt (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))
      (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t) t := by
    have h := hasDerivAt_deriv_clusterSqrtInertia_curve (m := m) (k := k) (x := x) (ε := ε)
      (t := t) ht hpos hx hd2
    exact h.congr_deriv h.deriv.symm
  have hP3 : HasDerivAt (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))))
      (deriv (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))) t) t := by
    have h := hasDerivAt_deriv_deriv_clusterSqrtInertia_curve (m := m) (k := k) (x := x)
      (ε := ε) (t := t) ht hpos hx hd2 hd3
    exact h.congr_deriv h.deriv.symm
  have hS1 : HasDerivAt (fun s : ℝ => clusterShape m k (x s))
      (deriv (fun s : ℝ => clusterShape m k (x s)) t) t := by
    have h := hasDerivAt_clusterShape_curve (m := m) (k := k) (x := x) (hpos t ht) hev
    exact h.congr_deriv h.deriv.symm
  have hS2 : HasDerivAt (deriv (fun s : ℝ => clusterShape m k (x s)))
      (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) t := by
    have h := hasDerivAt_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t)
      ht hpos hx hd2 hode
    exact h.congr_deriv h.deriv.symm
  have hQ : HasDerivAt (fun u => cmRel m k (∇_[m] (U m) (x u)))
      (cmRel m k (deriv (deriv (deriv x)) t)) t := by
    have hgrad : HasDerivAt (fun u => ∇_[m] (U m) (x u)) (deriv (deriv (deriv x)) t) t := by
      have heq2 : (fun u => ∇_[m] (U m) (x u)) =ᶠ[𝓝 t] deriv (deriv x) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
        rw [← hode u hu, iteratedDeriv_two_eq_deriv_deriv x u]
      exact (hd3 t ht).congr_of_eventuallyEq heq2
    exact hasDerivAt_cmRel m k hgrad
  -- the second-order identity, pointwise on a neighbourhood of `t`
  have hId2 : (fun u => Real.sqrt (clusterInertia m k (x u))
        • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) u)
      =ᶠ[𝓝 t] (fun u => cmRel m k (∇_[m] (U m) (x u))
        - deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) u
            • clusterShape m k (x u)
        - (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) u)
            • deriv (fun s : ℝ => clusterShape m k (x s)) u) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact sqrtInertia_smul_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (t := u) hu hpos hx hd2 hode
  set num : ℝ → EN E N := (fun u => cmRel m k (∇_[m] (U m) (x u))
      - deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) u
          • clusterShape m k (x u)
      - (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) u)
          • deriv (fun s : ℝ => clusterShape m k (x s)) u) with hnum
  set Rfun : ℝ → EN E N :=
    (fun u => (Real.sqrt (clusterInertia m k (x u)))⁻¹ • num u) with hR
  have hs2 : deriv (deriv (fun s : ℝ => clusterShape m k (x s))) =ᶠ[𝓝 t] Rfun := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    have h := sqrtInertia_smul_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (t := u) hu hpos hx hd2 hode
    have hΦu : Real.sqrt (clusterInertia m k (x u)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hpos u hu))
    rw [hR, hnum]
    have h1 : (Real.sqrt (clusterInertia m k (x u)))⁻¹
        • (Real.sqrt (clusterInertia m k (x u))
            • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) u)
        = (Real.sqrt (clusterInertia m k (x u)))⁻¹
          • (cmRel m k (∇_[m] (U m) (x u))
            - deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) u
                • clusterShape m k (x u)
            - (2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) u)
                • deriv (fun s : ℝ => clusterShape m k (x s)) u) := by rw [h]
    rwa [smul_smul, inv_mul_cancel₀ hΦu, one_smul] at h1
  have hnumd : HasDerivAt num
      (cmRel m k (deriv (deriv (deriv x)) t)
        - (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
              • deriv (fun s : ℝ => clusterShape m k (x s)) t
            + deriv (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))) t
              • clusterShape m k (x t))
        - ((2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
              • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
            + (2 * deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
              • deriv (fun s : ℝ => clusterShape m k (x s)) t)) t := by
    rw [hnum]
    exact (hQ.sub (hP3.smul hS1)).sub ((hP2.const_mul 2).smul hS2)
  have hRd : HasDerivAt Rfun
      ((Real.sqrt (clusterInertia m k (x t)))⁻¹
          • (cmRel m k (deriv (deriv (deriv x)) t)
            - (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t
                  • deriv (fun s : ℝ => clusterShape m k (x s)) t
                + deriv (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))) t
                  • clusterShape m k (x t))
            - ((2 * deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
                  • deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t
                + (2 * deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t)
                  • deriv (fun s : ℝ => clusterShape m k (x s)) t))
        + (-(deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t)
            / (Real.sqrt (clusterInertia m k (x t))) ^ 2) • num t) t := by
    rw [hR]
    exact (hP1.inv hΦne).smul hnumd
  exact hRd.congr_of_eventuallyEq hs2


/-- **Boundedness of `t^3` times the third derivative of the normalised configuration.**  From
`sqrt(I_k) * s_jolt = q_jolt - phi_jolt * s - 3 phi'' * s' - 3 phi' * s''` and the estimates
`t^(7/3) |q_jolt|`, `t^(7/3) |phi_jolt|`, `t^(4/3) |phi''|`, `t^(1/3) |phi'|`,
`t^2 |s''|`, `t |s'|`, `|s|` all bounded, together with `sqrt(I_k) ~ t^(2/3)`. -/
theorem exists_bound_mul_cube_deriv_deriv_deriv_clusterShape {m : Fin N → ℝ}
    {k : Finset (Fin N)} {x : ℝ → EN E N} {ε C ν Cv κ : ℝ}
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
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖t ^ 3 • deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t‖ ≤ C' := by
  obtain ⟨C1, hC1nn, hC1⟩ := exists_bound_rpow_seven_thirds_cmRel_third_deriv
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hSec
  obtain ⟨C2, hC2nn, hC2⟩ := exists_bound_rpow_seven_thirds_deriv_deriv_deriv_sqrtInertia
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hIn hDn hSec
  obtain ⟨C3, hC3nn, hC3⟩ := exists_bound_rpow_four_thirds_deriv_deriv_sqrtInertia
    (m := m) (k := k) (x := x) (ε := ε) (κ := κ) hm hk2 hε hκ hnc hx hd2 hIn hDn hSec
  obtain ⟨C4, hC4nn, hC4⟩ := exists_bound_rpow_third_deriv_sqrtInertia
    (m := m) (k := k) (x := x) (ε := ε) (κ := κ) hm hk2 hε hκ hnc hx hIn hDn
  obtain ⟨K1, hK1nn, hK1⟩ := exists_bound_mul_sq_deriv_deriv_clusterShape
    (m := m) (k := k) (x := x) (ε := ε) (C := C) (ν := ν) (Cv := Cv) (κ := κ)
    hm hk2 hε hC hν hCv hκ hnc hE hW hx hd2 hd3 hode hsep hv hI hIn hDn hSec hUn
  obtain ⟨c, hcpos, hcmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ k, c ≤ m i := by
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < k.card)
    obtain ⟨i1, hi1, hle⟩ := Finset.exists_min_image k m ⟨i0, hi0⟩
    exact ⟨m i1, hm i1, fun i hi => hle i hi⟩
  have hK0 : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)) ≤ (Real.sqrt κ)⁻¹ + 1 := by
    have h := tendsto_rpow_two_thirds_div_sqrtInertia (m := m) (k := k) (x := x)
      (ε := ε) (κ := κ) hm hk2 hε hκ hnc hIn
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds
      (show (Real.sqrt κ)⁻¹ < (Real.sqrt κ)⁻¹ + 1 by linarith))] with t ht
    exact le_of_lt ht
  have hts : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ≤ 1 := by
    have h := (tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI).norm
    filter_upwards [h.eventually (isOpen_Iio.mem_nhds (by simp : ‖(0 : EN E N)‖ < 1))]
      with t ht
    exact le_of_lt ht
  have hss : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      ‖clusterShape m k (x t)‖ ≤ Real.sqrt (1 / c) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have hIp : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
    have h2 := norm_clusterShape_sq_le (m := m) (k := k) (x := x t) hcpos hcmin hIp
    calc ‖clusterShape m k (x t)‖ = Real.sqrt (‖clusterShape m k (x t)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt h2
  refine ⟨((Real.sqrt κ)⁻¹ + 1) * (C1 + C2 * Real.sqrt (1 / c) + 3 * C3 + 2 * C4 * K1)
      + ((Real.sqrt κ)⁻¹ + 1) * (C4 * K1), by positivity, ?_⟩
  filter_upwards [hC1, hC2, hC3, hC4, hK1, hK0, hts, hss, Ioo_mem_nhdsGT hε]
    with t h1 h2 h3 h4 hk1 hk0 hts1 hss1 ht
  have ht0 : 0 < t := ht.1
  have hIpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
  have hΦpos : 0 < Real.sqrt (clusterInertia m k (x t)) := Real.sqrt_pos.mpr hIpos
  have hΦne : Real.sqrt (clusterInertia m k (x t)) ≠ 0 := ne_of_gt hΦpos
  set PH : ℝ := Real.sqrt (clusterInertia m k (x t)) with hPH
  set PH1 : ℝ := deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))) t with hPH1
  set PH2 : ℝ := deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ)))) t with hPH2
  set PH3 : ℝ :=
    deriv (deriv (deriv (fun υ : ℝ => Real.sqrt (clusterInertia m k (x υ))))) t with hPH3
  set S1 : EN E N := deriv (fun s : ℝ => clusterShape m k (x s)) t with hS1
  set S2 : EN E N := deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t with hS2
  set ST : EN E N := clusterShape m k (x t) with hST
  set Q3 : EN E N := cmRel m k (deriv (deriv (deriv x)) t) with hQ3
  set NUM' : EN E N := Q3 - (PH2 • S1 + PH3 • ST) - ((2 * PH1) • S2 + (2 * PH2) • S1) with hNUM'
  set NUMT : EN E N := cmRel m k (∇_[m] (U m) (x t)) - PH2 • ST - (2 * PH1) • S1 with hNUMT
  have h1' : t ^ ((7:ℝ)/3) * ‖Q3‖ ≤ C1 := by simpa only [hQ3] using h1
  have h2' : t ^ ((7:ℝ)/3) * |PH3| ≤ C2 := by
    have h := h2
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at h
    simpa only [hPH3] using h
  have h3' : t ^ ((4:ℝ)/3) * |PH2| ≤ C3 := by
    have h := h3
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at h
    simpa only [hPH2] using h
  have h4' : t ^ ((1:ℝ)/3) * |PH1| ≤ C4 := by
    have h := h4
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at h
    simpa only [hPH1] using h
  have hk1' : ‖t ^ 2 • S2‖ ≤ K1 := by simpa only [hS2] using hk1
  have hts1' : ‖t • S1‖ ≤ 1 := by simpa only [hS1] using hts1
  have hss1' : ‖ST‖ ≤ Real.sqrt (1 / c) := by simpa only [hST] using hss1
  have hNUMTeq : NUMT = PH • S2 := by
    rw [hNUMT, hPH, hS2, hPH2, hPH1, hST, hS1]
    exact (sqrtInertia_smul_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (t := t) ht (fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)) hx hd2 hode).symm
  have hs3 : deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t
      = PH⁻¹ • NUM' + (-(PH1) / PH ^ 2) • NUMT := by
    rw [hNUM', hNUMT, hPH, hPH1, hPH2, hPH3, hS1, hS2, hST, hQ3]
    exact (hasDerivAt_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t) ht
      (fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)) hx hd2 hd3 hode).deriv
  rw [hs3]
  -- bound the two pieces separately
  have hNUMbound : t ^ ((7:ℝ)/3) * ‖NUM'‖ ≤ C1 + C2 * Real.sqrt (1 / c) + 3 * C3 + 2 * C4 * K1 := by
    rw [hNUM']
    have htri : ‖Q3 - (PH2 • S1 + PH3 • ST) - ((2 * PH1) • S2 + (2 * PH2) • S1)‖
        ≤ ‖Q3‖ + (‖PH2 • S1‖ + ‖PH3 • ST‖) + (‖(2 * PH1) • S2‖ + ‖(2 * PH2) • S1‖) := by
      have hA := norm_sub_le (Q3 - (PH2 • S1 + PH3 • ST)) ((2 * PH1) • S2 + (2 * PH2) • S1)
      have hB := norm_sub_le Q3 (PH2 • S1 + PH3 • ST)
      have hC := norm_add_le (PH2 • S1) (PH3 • ST)
      have hD := norm_add_le ((2 * PH1) • S2) ((2 * PH2) • S1)
      linarith
    have hmul := mul_le_mul_of_nonneg_left htri (Real.rpow_nonneg ht0.le ((7:ℝ)/3))
    have e1 : t ^ ((7:ℝ)/3) * ‖PH2 • S1‖ ≤ C3 := by
      rw [norm_smul, Real.norm_eq_abs]
      have h7 : t ^ ((7:ℝ)/3) = t ^ ((4:ℝ)/3) * t := by
        have h := Real.rpow_add ht0 ((4:ℝ)/3) (1:ℝ)
        rw [show ((4:ℝ)/3) + 1 = (7:ℝ)/3 by norm_num, Real.rpow_one] at h
        exact h
      have hts2 : t * ‖S1‖ = ‖t • S1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      have hmain : t ^ ((7:ℝ)/3) * (|PH2| * ‖S1‖)
          = (t ^ ((4:ℝ)/3) * |PH2|) * ‖t • S1‖ := by
        rw [h7, ← hts2]; ring
      rw [hmain]
      calc (t ^ ((4:ℝ)/3) * |PH2|) * ‖t • S1‖ ≤ C3 * 1 :=
            mul_le_mul h3' hts1' (norm_nonneg _) hC3nn
        _ = C3 := by ring
    have e2 : t ^ ((7:ℝ)/3) * ‖PH3 • ST‖ ≤ C2 * Real.sqrt (1 / c) := by
      rw [norm_smul, Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul h2' hss1' (norm_nonneg _) hC2nn
    have e3 : t ^ ((7:ℝ)/3) * ‖(2 * PH1) • S2‖ ≤ 2 * C4 * K1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have h7 : t ^ ((7:ℝ)/3) = t ^ ((1:ℝ)/3) * t ^ 2 := by
        have h := Real.rpow_add ht0 ((1:ℝ)/3) (2:ℝ)
        rw [show ((1:ℝ)/3) + 2 = (7:ℝ)/3 by norm_num] at h
        rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
        exact h
      rw [h7]
      have e : t ^ ((1:ℝ)/3) * t ^ 2 * (|2 * PH1| * ‖S2‖)
          = (t ^ ((1:ℝ)/3) * |PH1|) * (2 * ‖t ^ 2 • S2‖) := by
        rw [show (2:ℝ) * ‖t ^ 2 • S2‖ = 2 * (t ^ 2 * ‖S2‖) by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]]
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        ring
      rw [e]
      have h2'' : (2:ℝ) * ‖t ^ 2 • S2‖ ≤ 2 * K1 :=
        mul_le_mul_of_nonneg_left hk1' (by norm_num)
      calc (t ^ ((1:ℝ)/3) * |PH1|) * (2 * ‖t ^ 2 • S2‖) ≤ C4 * (2 * K1) :=
            mul_le_mul h4' h2'' (by positivity) hC4nn
        _ = 2 * C4 * K1 := by ring
    have e4 : t ^ ((7:ℝ)/3) * ‖(2 * PH2) • S1‖ ≤ 2 * C3 := by
      rw [norm_smul, Real.norm_eq_abs]
      have h7 : t ^ ((7:ℝ)/3) = t ^ ((4:ℝ)/3) * t := by
        have h := Real.rpow_add ht0 ((4:ℝ)/3) (1:ℝ)
        rw [show ((4:ℝ)/3) + 1 = (7:ℝ)/3 by norm_num, Real.rpow_one] at h
        exact h
      have e : t ^ ((7:ℝ)/3) * (|2 * PH2| * ‖S1‖)
          = (t ^ ((4:ℝ)/3) * |PH2|) * (2 * ‖t • S1‖) := by
        have hts2 : t * ‖S1‖ = ‖t • S1‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.le]
        rw [h7, ← hts2]
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        ring
      rw [e]
      have h2'' : (2:ℝ) * ‖t • S1‖ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hts1' (by norm_num)
      calc (t ^ ((4:ℝ)/3) * |PH2|) * (2 * ‖t • S1‖) ≤ C3 * (2 * 1) :=
            mul_le_mul h3' h2'' (by positivity) hC3nn
        _ = 2 * C3 := by ring
    calc t ^ ((7:ℝ)/3) * ‖Q3 - (PH2 • S1 + PH3 • ST) - ((2 * PH1) • S2 + (2 * PH2) • S1)‖
        ≤ t ^ ((7:ℝ)/3) * (‖Q3‖ + (‖PH2 • S1‖ + ‖PH3 • ST‖)
            + (‖(2 * PH1) • S2‖ + ‖(2 * PH2) • S1‖)) := hmul
      _ = t ^ ((7:ℝ)/3) * ‖Q3‖ + (t ^ ((7:ℝ)/3) * ‖PH2 • S1‖ + t ^ ((7:ℝ)/3) * ‖PH3 • ST‖)
            + (t ^ ((7:ℝ)/3) * ‖(2 * PH1) • S2‖ + t ^ ((7:ℝ)/3) * ‖(2 * PH2) • S1‖) := by ring
      _ ≤ C1 + (C3 + C2 * Real.sqrt (1 / c)) + (2 * C4 * K1 + 2 * C3) :=
          add_le_add (add_le_add h1' (add_le_add e1 e2)) (add_le_add e3 e4)
      _ = C1 + C2 * Real.sqrt (1 / c) + 3 * C3 + 2 * C4 * K1 := by ring
  have hAt : ‖t ^ 3 • (PH⁻¹ • NUM')‖
      ≤ ((Real.sqrt κ)⁻¹ + 1) * (C1 + C2 * Real.sqrt (1 / c) + 3 * C3 + 2 * C4 * K1) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 3),
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have e : t ^ 3 * ((Real.sqrt (clusterInertia m k (x t)))⁻¹ * ‖NUM'‖)
        = (t ^ ((2:ℝ)/3) / Real.sqrt (clusterInertia m k (x t)))
            * (t ^ ((7:ℝ)/3) * ‖NUM'‖) := by
      rw [div_eq_mul_inv]
      have h7 : t ^ ((7:ℝ)/3) * t ^ ((2:ℝ)/3) = t ^ 3 := by
        rw [← Real.rpow_add ht0]; norm_num
      rw [← h7]
      ring
    rw [e]
    exact mul_le_mul hk0 hNUMbound (by positivity) (by positivity)
  have hBt : ‖t ^ 3 • ((-(PH1) / PH ^ 2) • NUMT)‖
      ≤ ((Real.sqrt κ)⁻¹ + 1) * (C4 * K1) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 3), hNUMTeq, norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg hΦpos.le]
    have e : t ^ 3 * (|-(PH1) / PH ^ 2| * (PH * ‖S2‖))
        = (t ^ ((2:ℝ)/3) / PH) * ((t ^ ((1:ℝ)/3) * |PH1|) * ‖t ^ 2 • S2‖) := by
      have hPHne : PH ≠ 0 := by rw [hPH]; exact hΦne
      have h7a : t ^ ((7:ℝ)/3) = t ^ ((1:ℝ)/3) * t ^ 2 := by
        have h := Real.rpow_add ht0 ((1:ℝ)/3) (2:ℝ)
        rw [show ((1:ℝ)/3) + 2 = (7:ℝ)/3 by norm_num] at h
        rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
        exact h
      have habs : |-(PH1) / PH ^ 2| = |PH1| / PH ^ 2 := by
        rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ PH ^ 2)]
      have hnorm : ‖t ^ 2 • S2‖ = t ^ 2 * ‖S2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
      rw [habs, hnorm]
      have h3s : t ^ 3 = t ^ ((2:ℝ)/3) * t ^ ((7:ℝ)/3) := by
        rw [← Real.rpow_natCast t 3, ← Real.rpow_add ht0]
        norm_num
      rw [h3s, h7a]
      field_simp
    rw [e]
    have h4'' : t ^ ((1:ℝ)/3) * |PH1| ≤ C4 := h4'
    have hK0' : t ^ ((2:ℝ)/3) / PH ≤ (Real.sqrt κ)⁻¹ + 1 := by rw [hPH]; exact hk0
    exact mul_le_mul hK0' (mul_le_mul h4'' hk1' (norm_nonneg _) hC4nn)
      (by positivity) (by positivity)
  have hsplit : t ^ 3 • (PH⁻¹ • NUM' + (-(PH1) / PH ^ 2) • NUMT)
      = t ^ 3 • (PH⁻¹ • NUM') + t ^ 3 • ((-(PH1) / PH ^ 2) • NUMT) := by rw [smul_add]
  refine le_trans (le_of_eq (congrArg Norm.norm hsplit)) ?_
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add hAt hBt

end Submission.NBody
