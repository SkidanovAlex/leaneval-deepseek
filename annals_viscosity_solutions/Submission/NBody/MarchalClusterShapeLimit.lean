import Submission.NBody.MarchalClusterShapeIdentity

/-!
# Ferrario–Terracini `as:lim1`: `t · ṡ_i → 0`

For an isolated cluster collapsing at `t = 0`, the normalised configuration
`s = I_k^{-1/2}(x - x_{cm,k})` satisfies `t ṡ_i → 0` as `t → 0⁺`.  This is the first of the two
asymptotic statements of Ferrario–Terracini (`as:lim1`); the proof uses the identity

    `I_k · R_k(ṡ) = R_k(ẋ) - (İ_k)²/(4 I_k)`

together with the asymptotics `I_k ~ κ t^{4/3}`, `İ_k ~ (4/3) κ t^{1/3}`,
`R_k(ẋ) ~ (4/9) κ t^{-2/3}`.

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

/-- **`as:lim1`, weighted form.**  The mass-weighted squared norm of `t ṡ` tends to `0`. -/
theorem tendsto_mul_sq_clusterKineticSq_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto (fun t : ℝ =>
      clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) * t ^ 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  classical
  obtain ⟨κ, hκpos, hJn, hDn, _hSec, _hU, hRn⟩ :=
    clusterPotential_asymptotic_of_isolated (m := m) (k := k) (x := x) (ε := ε) (C := C)
      (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have hF : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhdsWithin (0:ℝ) (Ioi 0) := le_rfl
  obtain ⟨i0, hi0⟩ : k.Nonempty := Finset.card_pos.mp (by omega)
  -- the identity holds on `(0, ε)`
  have hid : ∀ t ∈ Ioo (0:ℝ) ε,
      clusterInertia m k (x t)
          * clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
        = clusterRelKinetic m k (deriv x t)
          - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
              / (4 * clusterInertia m k (x t)) := by
    intro t ht
    refine clusterInertia_mul_clusterKineticSq_deriv_shape
      (clusterInertia_pos hm hk2 (hnc t ht)) ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hx s hs
  -- `(İ_k²/(4 I_k)) t^{2/3} → (4/9) κ`
  have hratio : Tendsto
      (fun t : ℝ => (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
        / (4 * clusterInertia m k (x t)) * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)) := by
    have hnum : Tendsto
        (fun t : ℝ => (deriv (fun s : ℝ => clusterInertia m k (x s)) t / t ^ ((1:ℝ)/3)) ^ 2)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (((4:ℝ)/3 * κ) ^ 2)) := hDn.pow 2
    have hden : Tendsto (fun t : ℝ => 4 * (clusterInertia m k (x t) / t ^ ((4:ℝ)/3)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (4 * κ)) := hJn.const_mul 4
    have hdenne : (4:ℝ) * κ ≠ 0 := by positivity
    have hquot := hnum.div hden hdenne
    have hval : ((4:ℝ)/3 * κ) ^ 2 / (4 * κ) = (4:ℝ)/9 * κ := by
      field_simp
      ring
    rw [hval] at hquot
    refine Filter.Tendsto.congr' ?_ hquot
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have ht0 : 0 < t := ht.1
    have hJpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
    simp only [Pi.div_apply]
    have h13sq : (t ^ ((1:ℝ)/3)) ^ 2 = t ^ ((2:ℝ)/3) := by
      rw [← Real.rpow_natCast (t ^ ((1:ℝ)/3)) 2, ← Real.rpow_mul ht0.le]
      norm_num
    have h43 : t ^ ((4:ℝ)/3) = t ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) := by
      rw [← Real.rpow_add ht0]
      norm_num
    rw [div_pow, h13sq, h43]
    field_simp
  -- `I_k R_k t^{2/3} → 0`
  have hJK : Tendsto
      (fun t : ℝ => clusterInertia m k (x t)
        * clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
        * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hsub := hRn.sub hratio
    rw [sub_self] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    rw [hid t ht]
    ring
  -- `K_k(t) t² → 0`
  have hKsq : Tendsto (fun t : ℝ =>
      clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) * t ^ 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hquot := hJK.div hJn (ne_of_gt hκpos)
    rw [zero_div] at hquot
    refine Filter.Tendsto.congr' ?_ hquot
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have ht0 : 0 < t := ht.1
    have hJpos : 0 < clusterInertia m k (x t) := clusterInertia_pos hm hk2 (hnc t ht)
    simp only [Pi.div_apply, Pi.mul_apply, Pi.inv_apply]
    have hsplit : t ^ ((2:ℝ)/3) * t ^ ((4:ℝ)/3) = t ^ 2 := by
      rw [← Real.rpow_add ht0]
      norm_num
    rw [div_eq_mul_inv, inv_div]
    field_simp
    rw [mul_assoc, hsplit]
  exact hKsq

/-- Outside the cluster the derivative of the normalised configuration vanishes. -/
lemma deriv_clusterShape_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t : ℝ} (hJpos : 0 < clusterInertia m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) {i : Fin N} (hi : i ∉ k) :
    (deriv (fun s : ℝ => clusterShape m k (x s)) t) i = 0 := by
  have hcurve := hasDerivAt_clusterShape_curve hJpos hx
  have hda := hasDerivAt_apply hcurve i
  have hc : (fun s : ℝ => (clusterShape m k (x s)) i) = fun _ : ℝ => (0 : E) := by
    funext s; rw [clusterShape_apply, cmRel_apply_of_notMem hi, smul_zero]
  rw [hc] at hda
  have h2 := hda.deriv
  rw [deriv_const] at h2
  rw [hcurve.deriv]
  exact h2.symm

/-- **Ferrario–Terracini `as:lim1`.**  Each coordinate `(t ṡ)_i` of a body of the collapsing
cluster tends to `0`. -/
theorem tendsto_mul_deriv_clusterShape_apply {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    {i : Fin N} (hi : i ∈ k) :
    Tendsto (fun t : ℝ => t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  have hK := tendsto_mul_sq_clusterKineticSq_deriv_clusterShape (m := m) (k := k) (x := x)
    (ε := ε) (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  have hmipos : 0 < m i := hm i
  have hle : ∀ t ∈ Ioo (0:ℝ) ε,
      ‖t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖
        ≤ Real.sqrt (clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
            * t ^ 2 / m i) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hsingle : m i * ‖(deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖ ^ 2
        ≤ clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) := by
      rw [clusterKineticSq]
      exact Finset.single_le_sum
        (f := fun j : Fin N =>
          m j * ‖(deriv (fun s : ℝ => clusterShape m k (x s)) t) j‖ ^ 2)
        (fun j _ => mul_nonneg (hm j).le (sq_nonneg _)) hi
    have hKnn : 0 ≤ clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) :=
      clusterKineticSq_nonneg (fun j => (hm j).le) k _
    have hsq : ‖t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖ ^ 2
        ≤ clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) * t ^ 2 / m i := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
      rw [le_div_iff₀ hmipos]
      nlinarith [hsingle, sq_nonneg t, hKnn]
    calc ‖t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖
        = Real.sqrt (‖t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
            * t ^ 2 / m i) := Real.sqrt_le_sqrt hsq
  refine squeeze_zero_norm'
    (a := fun t : ℝ => Real.sqrt
      (clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t) * t ^ 2 / m i)) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    exact hle t ht
  · have h1 : Tendsto
        (fun t : ℝ => clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
          * t ^ 2 / m i) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (0 / m i)) :=
      hK.div_const (m i)
    rw [zero_div] at h1
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
    simpa only [Function.comp_def, Real.sqrt_zero] using h2

/-- **Ferrario–Terracini `as:lim1`, vector form.**  `t · ṡ → 0`. -/
theorem tendsto_mul_deriv_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
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
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto (fun t : ℝ => t • deriv (fun s : ℝ => clusterShape m k (x s)) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto
      (fun t : ℝ => ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ^ 2)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    rw [show (fun t : ℝ => ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ^ 2)
        = fun t : ℝ =>
            ∑ i : Fin N, ‖(t • deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖ ^ 2 by
      funext t; rw [PiLp.norm_sq_eq_of_L2]]
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => by
      by_cases hi : i ∈ k
      · have hcoord := tendsto_mul_deriv_clusterShape_apply (m := m) (k := k) (x := x)
          (ε := ε) (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode
          hsep hv hI hi
        simpa using (hcoord.norm.pow 2)
      · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (0:ℝ)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
        filter_upwards [Ioo_mem_nhdsGT hε] with t ht
        have hJpos := clusterInertia_pos hm hk2 (hnc t ht)
        have hz := deriv_clusterShape_apply_of_notMem hJpos (by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
          exact hx s hs) hi
        simp [hz])
    simpa using hsum
  have hsqrt : Tendsto
      (fun t : ℝ => Real.sqrt (‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ^ 2))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero] using h2
  rw [show (fun t : ℝ => ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖)
      = fun t : ℝ => Real.sqrt (‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ ^ 2)
      from funext fun t => (Real.sqrt_sq (norm_nonneg _)).symm]
  exact hsqrt

end Submission.NBody
