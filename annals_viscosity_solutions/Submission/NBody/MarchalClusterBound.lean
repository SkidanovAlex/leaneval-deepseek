import Submission.NBody.MarchalClusterAsymptotic

/-!
# The analysis hypotheses of the Sundman machinery, for a colliding cluster

`clusterInertia_asymptotic` proves `I_k(x(t)) = κ t^{4/3} + o(t^{4/3})` from two *boundedness*
hypotheses on the cluster: the centre-of-mass-relative energy `E_k^{rel}` and the interaction work
`crossWork_k` are bounded.  This module discharges them, under the geometric hypotheses which
express that `k` is an *isolated colliding cluster* at `t = 0`:

* `x` solves Newton's equations on `(0, ε)` and is collision free there;
* the pairs which are not internal to `k` stay separated: `ν ≤ ‖xᵢ(t) - xⱼ(t)‖`;
* the bodies outside `k` have bounded velocities;
* the bodies of `k` collapse: `I_k(x(t)) → 0`.

The key identity is the global one: writing `U = U_k + U_{rest}` (internal pairs and the rest) and
`K = K_k + K_{rest}` (kinetic energies), conservation of the total energy `H = K - U` gives

    `E_k = H - (K_{rest} - U_{rest})`,

and each term on the right is bounded: `K_{rest}` by the velocity bound, `U_{rest}` by the
separation.  Finally the centre of mass of the cluster has bounded acceleration (the internal
forces cancel), hence a finite limit velocity at `t = 0`, which bounds the last term relating
`E_k^{rel}` to `E_k`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Splitting the potential -/

/-- The potential of the pairs not both internal to `k`. -/
noncomputable def clusterPotentialRest (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : ℝ :=
  ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
    m p.1 * m p.2 * (r x p.1 p.2)⁻¹

/-- `U = U_k + U_{rest}`. -/
theorem U_eq_clusterPotential_add_rest (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    U m x = clusterPotential m k x + clusterPotentialRest m k x := by
  rw [U_eq_pairFinset, clusterPotential, clusterPotentialRest]
  exact (Finset.sum_filter_add_sum_filter_not (pairFinset N)
    (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k)
    (fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹)).symm

/-- The separation hypothesis: every pair of bodies which is not internal to `k` is at distance at
least `ν`. -/
def ClusterSeparated (k : Finset (Fin N)) (x : EN E N) (ν : ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬ (i ∈ k ∧ j ∈ k) → ν ≤ r x i j

/-- **The weak (one-sided) separation hypothesis.**  Every pair with one body in `k` and the other
outside is separated by `ν`. -/
def ClusterSeparatedWeak (k : Finset (Fin N)) (x : EN E N) (ν : ℝ) : Prop :=
  ∀ i ∈ k, ∀ j ∉ k, ν ≤ r x i j

lemma ClusterSeparated.mono {k : Finset (Fin N)} {x : EN E N} {ν ν' : ℝ}
    (h : ClusterSeparated k x ν') (hle : ν ≤ ν') : ClusterSeparated k x ν :=
  fun i j hij hk => le_trans hle (h i j hij hk)

/-- The two-sided separation implies the one-sided one. -/
lemma ClusterSeparated.weak {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (h : ClusterSeparated k x ν) : ClusterSeparatedWeak k x ν :=
  fun i hi j hj => h i j (fun hij => hj (hij ▸ hi)) (fun hc => hj hc.2)

lemma clusterPotentialRest_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (x : EN E N) : 0 ≤ clusterPotentialRest m k x := by
  rw [clusterPotentialRest]
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (inv_nonneg.mpr dist_nonneg)

/-- The interaction potential of the rest of the bodies is bounded by its value at separation
`ν`. -/
lemma clusterPotentialRest_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hsep : ClusterSeparated k x ν) :
    clusterPotentialRest m k x
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2) / ν := by
  rw [clusterPotentialRest, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).2
  have hlt : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact ne_of_lt this
  have hdist : ν ≤ r x p.1 p.2 := hsep p.1 p.2 hlt hp'
  have hpos : 0 < r x p.1 p.2 := lt_of_lt_of_le hν hdist
  have hinv : (r x p.1 p.2)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hpos hν).mpr hdist
  have hmm : 0 ≤ m p.1 * m p.2 := mul_nonneg (hm p.1) (hm p.2)
  calc m p.1 * m p.2 * (r x p.1 p.2)⁻¹ ≤ m p.1 * m p.2 * ν⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hmm
    _ = m p.1 * m p.2 / ν := by rw [div_eq_mul_inv]

/-! ## Splitting the kinetic energy -/

/-- Twice the kinetic energy of the bodies outside `k`. -/
noncomputable def outsideKineticSq (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) : ℝ :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin N => i ∉ k)), m i * ‖v i‖ ^ 2

private lemma sum_ite_mem_eq' {N : ℕ} {M : Type*} [AddCommMonoid M] (k : Finset (Fin N))
    (f : Fin N → M) : (∑ i : Fin N, if i ∈ k then f i else 0) = ∑ i ∈ k, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

private lemma sum_ite_notMem_eq {N : ℕ} {M : Type*} [AddCommMonoid M] (k : Finset (Fin N))
    (f : Fin N → M) :
    (∑ i : Fin N, if i ∉ k then f i else 0)
      = ∑ i ∈ (Finset.univ.filter (fun i : Fin N => i ∉ k)), f i := by
  rw [Finset.sum_filter]

/-- The kinetic energy splits over `k` and its complement. -/
lemma kinetic_eq_clusterKinetic_add_outside (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) :
    kinetic m v = clusterKineticSq m k v / 2 + outsideKineticSq m k v / 2 := by
  have hsplit : (∑ i : Fin N, m i * ‖v i‖ ^ 2)
      = (∑ i : Fin N, if i ∈ k then m i * ‖v i‖ ^ 2 else 0)
        + (∑ i : Fin N, if i ∉ k then m i * ‖v i‖ ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ k <;> simp [hi]
  rw [kinetic, clusterKineticSq, outsideKineticSq, hsplit, sum_ite_mem_eq', sum_ite_notMem_eq]
  ring

/-- The kinetic energy of the complement, bounded by the velocity bound. -/
lemma outsideKineticSq_le {m : Fin N → ℝ} {k : Finset (Fin N)} {v : EN E N} {Cv : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hCv : 0 ≤ Cv) (hv : ∀ j ∉ k, ‖v j‖ ≤ Cv) :
    outsideKineticSq m k v ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 := by
  rw [outsideKineticSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := (Finset.mem_filter.mp hj).2
  have h1 : ‖v j‖ ^ 2 ≤ Cv ^ 2 := by
    exact sq_le_sq' (by linarith [norm_nonneg (v j), hv j hj']) (hv j hj')
  exact mul_le_mul_of_nonneg_left h1 (hm j)

end Submission.NBody

namespace Submission.NBody

/-! ## Conservation of energy, locally -/

/-- **Conservation of energy, local form.**  Along any collision-free local solution of Newton's
equations, the total energy has derivative zero. -/
theorem energy_hasDerivAt_zero_of_local {m : Fin N → ℝ} (hm : ∀ i, m i ≠ 0)
    {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : WithoutCollisions (x t)) :
    HasDerivAt (energy m x) 0 t := by
  have hdy := hx.self_of_nhds
  have hkin : HasDerivAt (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv x s i‖ ^ 2)
      ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv x t i) (iteratedDeriv 2 x t i)))) t :=
    HasDerivAt.const_mul (𝔸 := ℝ) (1 / 2) (hasDerivAt_kinetic_sum m hd2)
  have hpot : HasDerivAt (fun s : ℝ => U m (x s)) ((fderiv ℝ (U m) (x t)) (deriv x t)) t := by
    have hU_at : HasFDerivAt (U m) (fderiv ℝ (U m) (x t)) (x t) :=
      (hasFDerivAt_U m (x t) hnc).differentiableAt.hasFDerivAt
    simpa [Function.comp_def] using hU_at.comp_hasDerivAt t hdy
  have hE : HasDerivAt (energy m x)
      ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv x t i) (iteratedDeriv 2 x t i))) -
        (fderiv ℝ (U m) (x t)) (deriv x t)) t := by
    have hE' := hkin.sub hpot
    rw [show (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv x s i‖ ^ 2) - (fun s : ℝ => U m (x s))
        = energy m x by
      funext s
      simp [energy, Pi.sub_apply]] at hE'
    exact hE'
  have hkey : (fderiv ℝ (U m) (x t)) (deriv x t) =
      ∑ i, m i * inner ℝ (iteratedDeriv 2 x t i) (deriv x t i) := by
    rw [← inner_gradient_eq_fderiv (x t) (deriv x t)]
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [gradient_eq_smul_weightedGrad m hm (x t) i, ← hode]
    rw [inner_smul_left]
    simp
  rw [hkey] at hE
  have hzero : (1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv x t i) (iteratedDeriv 2 x t i))) -
      (∑ i, m i * inner ℝ (iteratedDeriv 2 x t i) (deriv x t i)) = 0 := by
    rw [Finset.mul_sum, sub_eq_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
    ring
  rwa [hzero] at hE

/-- **Energy is constant on an interval of a collision-free local solution.** -/
theorem energy_eq_of_mem_Ioo {m : Fin N → ℝ} (hm : ∀ i, m i ≠ 0) {x : ℝ → EN E N} {ε : ℝ}
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    {s t : ℝ} (hs : s ∈ Ioo (0:ℝ) ε) (ht : t ∈ Ioo (0:ℝ) ε) :
    energy m x s = energy m x t := by
  have hderiv : ∀ z ∈ Ioo (0:ℝ) ε, HasDerivAt (energy m x) 0 z := by
    intro z hz
    refine energy_hasDerivAt_zero_of_local hm ?_ (hd2 z hz) (hode z hz) (hnc z hz)
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
    exact hx w hw
  have hdiff : DifferentiableOn ℝ (energy m x) (Ioo (0:ℝ) ε) := fun z hz =>
    (hderiv z hz).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ z ∈ Ioo (0:ℝ) ε, fderivWithin ℝ (energy m x) (Ioo (0:ℝ) ε) z = 0 := by
    intro z hz
    have hd := hderiv z hz
    have hf : fderiv ℝ (energy m x) z = 0 := by simpa using hd.hasFDerivAt.fderiv
    rw [fderivWithin_of_isOpen isOpen_Ioo hz, hf]
  exact Convex.is_const_of_fderivWithin_eq_zero (convex_Ioo (0:ℝ) ε) hdiff hfderiv hs ht

/-! ## The energy of a cluster in terms of the energy of the motion -/

/-- The energy of a cluster is the total energy minus the energy of the rest of the bodies. -/
lemma clusterEnergy_eq_kinetic_sub_rest (m : Fin N → ℝ) (k : Finset (Fin N)) (x v : EN E N) :
    clusterEnergy m k x v
      = kinetic m v - U m x - (outsideKineticSq m k v / 2 - clusterPotentialRest m k x) := by
  rw [clusterEnergy, kinetic_eq_clusterKinetic_add_outside, U_eq_clusterPotential_add_rest]
  ring

/-- The energy of a cluster along a motion is the total energy minus the energy of the rest. -/
lemma clusterEnergy_eq_energy_sub_rest (m : Fin N → ℝ) (k : Finset (Fin N))
    (x : ℝ → EN E N) (t : ℝ) :
    clusterEnergy m k (x t) (deriv x t)
      = energy m x t
        - (outsideKineticSq m k (deriv x t) / 2 - clusterPotentialRest m k (x t)) := by
  have hkin : kinetic m (deriv x t) = (1 / 2) * ∑ i, m i * ‖deriv x t i‖ ^ 2 := rfl
  rw [clusterEnergy_eq_kinetic_sub_rest, energy, hkin]

end Submission.NBody

namespace Submission.NBody

/-! ## The work of the interaction forces is bounded -/

/-- Each term of the interaction work is bounded by the mass product times the separation
constant, once the centre-of-mass-relative configuration is bounded and the bodies are separated. -/
lemma abs_crossWork_term {m : Fin N → ℝ} {x d : EN E N} {ν R : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hR : 0 ≤ R) {i j : Fin N} (hij : i ≠ j)
    (hsep : ν ≤ ‖x i - x j‖) (hd : ‖d i - d j‖ ≤ 2 * R) :
    |m i * m j * (-((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (d i - d j))|
      ≤ m i * m j * (2 * R) * (ν⁻¹) ^ 2 := by
  have hmm : 0 ≤ m i * m j := mul_nonneg (hm i) (hm j)
  have hnorm : 0 < ‖x i - x j‖ := lt_of_lt_of_le hν hsep
  have hinner : |inner ℝ (x i - x j) (d i - d j)| ≤ ‖x i - x j‖ * ‖d i - d j‖ :=
    abs_real_inner_le_norm _ _
  have h1 : 0 ≤ (‖x i - x j‖ ^ 3)⁻¹ := by positivity
  have habs : |m i * m j * (-((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (d i - d j))|
      = m i * m j * ((‖x i - x j‖ ^ 3)⁻¹ * |inner ℝ (x i - x j) (d i - d j)|) := by
    rw [abs_mul, abs_of_nonneg hmm, abs_mul, abs_neg, abs_of_nonneg h1]
  rw [habs]
  have hstep1 : m i * m j * ((‖x i - x j‖ ^ 3)⁻¹ * |inner ℝ (x i - x j) (d i - d j)|)
      ≤ m i * m j * ((‖x i - x j‖ ^ 3)⁻¹ * (‖x i - x j‖ * (2 * R))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h1) hmm
    exact le_trans hinner (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  refine hstep1.trans ?_
  have hpow : (‖x i - x j‖ ^ 3)⁻¹ * ‖x i - x j‖ = (‖x i - x j‖ ^ 2)⁻¹ := by
    rw [inv_mul_eq_div, pow_succ]
    field_simp
  have hle : (‖x i - x j‖ ^ 2)⁻¹ ≤ (ν⁻¹) ^ 2 := by
    have h2 : (‖x i - x j‖)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hnorm hν).mpr hsep
    have h3 : ((‖x i - x j‖)⁻¹) ^ 2 ≤ (ν⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rwa [inv_pow] at h3
  have hrew : m i * m j * ((‖x i - x j‖ ^ 3)⁻¹ * (‖x i - x j‖ * (2 * R)))
      = m i * m j * (2 * R) * ((‖x i - x j‖ ^ 2)⁻¹) := by
    rw [← hpow]; ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **The interaction work is bounded.** -/
theorem abs_crossWork_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν R : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hR : 0 ≤ R) (hsep : ClusterSeparated k x ν)
    (hd : ∀ p : Fin N, ‖(cmRel m k x) p‖ ≤ R) :
    |crossWork m k x (cmRel m k x)|
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2 * (2 * R)) * (ν⁻¹) ^ 2 := by
  rw [crossWork]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).2
  have hlt : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact ne_of_lt this
  have hsep' : ν ≤ ‖x p.1 - x p.2‖ := by
    have := hsep p.1 p.2 hlt hp'
    rwa [r_eq_norm_sub] at this
  have hd' : ‖(cmRel m k x) p.1 - (cmRel m k x) p.2‖ ≤ 2 * R := by
    calc ‖(cmRel m k x) p.1 - (cmRel m k x) p.2‖
        ≤ ‖(cmRel m k x) p.1‖ + ‖(cmRel m k x) p.2‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hd p.1) (hd p.2)
      _ = 2 * R := by ring
  have := abs_crossWork_term hm hν hR hlt hsep' hd'
  calc |m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
        ((cmRel m k x) p.1 - (cmRel m k x) p.2))|
      ≤ m p.1 * m p.2 * (2 * R) * (ν⁻¹) ^ 2 := this
    _ = m p.1 * m p.2 * (2 * R) * (ν⁻¹) ^ 2 := rfl

/-- The centre-of-mass-relative configuration of a cluster is bounded by the square root of the
moment of inertia. -/
lemma norm_sub_clusterCM_le_sqrt {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {κ : ℝ}
    (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ) {i : Fin N} (hi : i ∈ k) :
    ‖x i - clusterCM m k x‖ ≤ Real.sqrt (clusterInertia m k x / κ) := by
  have hI : clusterInertia m k x = ∑ j ∈ k, m j * ‖x j - clusterCM m k x‖ ^ 2 := rfl
  have hle : m i * ‖x i - clusterCM m k x‖ ^ 2 ≤ clusterInertia m k x := by
    rw [hI]
    exact Finset.single_le_sum (f := fun j : Fin N => m j * ‖x j - clusterCM m k x‖ ^ 2)
      (fun j _ => mul_nonneg (le_trans hκpos.le (hκ j)) (sq_nonneg _)) hi
  have h2 : ‖x i - clusterCM m k x‖ ^ 2 ≤ clusterInertia m k x / κ := by
    rw [le_div_iff₀ hκpos]
    calc ‖x i - clusterCM m k x‖ ^ 2 * κ ≤ ‖x i - clusterCM m k x‖ ^ 2 * m i :=
          mul_le_mul_of_nonneg_left (hκ i) (sq_nonneg _)
      _ = m i * ‖x i - clusterCM m k x‖ ^ 2 := by ring
      _ ≤ clusterInertia m k x := hle
  calc ‖x i - clusterCM m k x‖ = Real.sqrt (‖x i - clusterCM m k x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (clusterInertia m k x / κ) := Real.sqrt_le_sqrt h2

end Submission.NBody

namespace Submission.NBody

/-! ## The velocity of the centre of mass of a colliding cluster -/

/-- **The centre of mass of a colliding cluster has a bounded velocity.**  Its acceleration is the
mean of the accelerations of the bodies of the cluster, which is bounded by `A`; the mean value
inequality then bounds the velocity on `(0, ε)` by its value at `ε/4` plus `A ε/4`. -/
theorem exists_bound_clusterCM_deriv {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hacc : ∀ t ∈ Ioo (0:ℝ) ε, ‖clusterCM m k (iteratedDeriv 2 x t)‖ ≤ A) :
    ∀ t ∈ Ioo (0:ℝ) (ε / 4),
      ‖clusterCM m k (deriv x t)‖ ≤ A * (ε / 4) + ‖clusterCM m k (deriv x (ε / 4))‖ := by
  set g : ℝ → E := fun t => clusterCM m k (deriv x t) with hg
  have hquarter : ε / 4 ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
  have hderiv : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt g (clusterCM m k (iteratedDeriv 2 x t)) t :=
    fun t ht => hasDerivAt_clusterCM m k (hd2 t ht)
  intro t ht
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := g) (f' := fun s => clusterCM m k (iteratedDeriv 2 x s)) (C := A) (a := t) (b := ε/4)
    (fun s hs => (hderiv s ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hquarter.2⟩).hasDerivWithinAt)
    (fun s hs => hacc s ⟨lt_of_lt_of_le ht.1 hs.1, lt_trans hs.2 hquarter.2⟩)
  have h1 := hseg (ε/4) ⟨le_of_lt ht.2, le_rfl⟩
  simp only [hg] at h1 ⊢
  have h2 : A * (ε / 4 - t) ≤ A * (ε / 4) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) hA
  have h3 : ‖clusterCM m k (deriv x t)‖
      ≤ ‖clusterCM m k (deriv x t) - clusterCM m k (deriv x (ε / 4))‖
        + ‖clusterCM m k (deriv x (ε / 4))‖ := by
    have := norm_add_le (clusterCM m k (deriv x t) - clusterCM m k (deriv x (ε / 4)))
      (clusterCM m k (deriv x (ε / 4)))
    rw [sub_add_cancel] at this
    exact this
  rw [norm_sub_rev] at h3
  linarith [norm_nonneg (clusterCM m k (deriv x (ε / 4)))]

end Submission.NBody

namespace Submission.NBody

/-! ## The two boundedness hypotheses of `clusterInertia_asymptotic` -/

/-- **The relative energy and the interaction work of an isolated colliding cluster are bounded.**

The total energy `H` is conserved; `U = U_k + U_rest` and `K = K_k + K_rest` split the potential and
the kinetic energy, whence `E_k = H - (K_rest - U_rest)`.  The velocity bound controls `K_rest`, the
separation controls `U_rest`, and the centre-of-mass velocity bound controls the difference between
`E_k` and the relative energy `E_k^{rel}`.  The interaction work is controlled by the separation and
by `I_k → 0` (each body of the cluster approaches its centre of mass). -/
theorem exists_clusterRelEnergy_crossWork_bound {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν Cv Ccm : ℝ}
    (hm : ∀ i, 0 < m i) (hε : 0 < ε) (hk : k.Nonempty)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hν : 0 < ν) (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparated k (x t) ν)
    (hCv : 0 ≤ Cv) (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k, ‖deriv x t j‖ ≤ Cv)
    (hCcm : 0 ≤ Ccm) (hcm : ∀ t ∈ Ioo (0:ℝ) ε, ‖clusterCM m k (deriv x t)‖ ≤ Ccm)
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0)) :
    ∃ ε' C : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ 0 < C ∧ ∀ t ∈ Ioo (0:ℝ) ε',
      |clusterRelEnergy m k (x t) (deriv x t)| ≤ C ∧
      |crossWork m k (x t) (cmRel m k (x t))| ≤ C := by
  classical
  -- a positive lower bound for the masses
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, hi₀⟩ := hk
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i₀, Finset.mem_univ i₀⟩
    exact ⟨m i₁, hm i₁, fun i => hi₁ i (Finset.mem_univ i)⟩
  -- shrink the interval so that `I_k ≤ κ`
  have hIv : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), clusterInertia m k (x t) < κ :=
    hI.eventually (isOpen_Iio.mem_nhds hκpos)
  rw [eventually_nhdsWithin_iff] at hIv
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hIv
  obtain ⟨ε₁, hε₁pos, hε₁le, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧
      ∀ t ∈ Ioo (0:ℝ) ε₁, clusterInertia m k (x t) ≤ κ := by
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun t ht => ?_⟩
    have hball : t ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact lt_of_lt_of_le ht.2 (min_le_left _ _)
    exact le_of_lt (hδ t hball ht.1)
  have hmem : ∀ t ∈ Ioo (0:ℝ) ε₁, t ∈ Ioo (0:ℝ) ε := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hε₁le⟩
  -- the bounds
  set C1 : ℝ := |energy m x (ε / 2)| with hC1
  set C2 : ℝ := (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 / 2 with hC2
  set C3 : ℝ := (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      m p.1 * m p.2) / ν with hC3
  set C4 : ℝ := clusterMass m k * Ccm ^ 2 / 2 with hC4
  set C5 : ℝ := (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      m p.1 * m p.2 * 2) * (ν⁻¹) ^ 2 with hC5
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (sq_nonneg _)) (by norm_num)
  have hC3nn : 0 ≤ C3 := by
    rw [hC3]
    exact div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) hν.le
  have hC4nn : 0 ≤ C4 := by
    rw [hC4]
    exact div_nonneg (mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _))
      (by norm_num)
  have hC5nn : 0 ≤ C5 := by
    rw [hC5]
    exact mul_nonneg (Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (by norm_num)) (sq_nonneg _)
  refine ⟨ε₁, max 1 (C1 + C2 + C3 + C4 + C5), hε₁pos, hε₁le, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro t ht
  have htε := hmem t ht
  -- the energy of the cluster
  have hEr : |clusterEnergy m k (x t) (deriv x t)| ≤ C1 + C2 + C3 := by
    rw [clusterEnergy_eq_energy_sub_rest,
      energy_eq_of_mem_Ioo (fun i => ne_of_gt (hm i)) hx hd2 hode hnc htε
        (show ε / 2 ∈ Ioo (0:ℝ) ε from ⟨by linarith, by linarith⟩)]
    have hK : outsideKineticSq m k (deriv x t) / 2 ≤ C2 := by
      rw [hC2]
      linarith [outsideKineticSq_le (m := m) (k := k) (v := deriv x t) (Cv := Cv)
        (fun i => (hm i).le) hCv (fun j hj => hv t htε j hj)]
    have hU : clusterPotentialRest m k (x t) ≤ C3 := by
      rw [hC3]
      exact clusterPotentialRest_le (fun i => (hm i).le) hν (hsep t htε)
    have hKnn : 0 ≤ outsideKineticSq m k (deriv x t) / 2 := by
      rw [outsideKineticSq]
      exact div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hm j).le (sq_nonneg _)) (by norm_num)
    have hUnn : 0 ≤ clusterPotentialRest m k (x t) :=
      clusterPotentialRest_nonneg (fun i => (hm i).le) k (x t)
    have h1 : energy m x (ε/2) ≤ C1 := by rw [hC1]; exact le_abs_self _
    have h2 : -C1 ≤ energy m x (ε/2) := by rw [hC1]; exact neg_abs_le _
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
  -- the relative energy
  have hErel : |clusterRelEnergy m k (x t) (deriv x t)| ≤ C1 + C2 + C3 + C4 := by
    have hdiff : clusterRelEnergy m k (x t) (deriv x t)
        = clusterEnergy m k (x t) (deriv x t)
          - clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2 := by
      have := clusterEnergy_eq_relEnergy_add (k := k) hm hk (x t) (deriv x t)
      linarith
    have hcmsq : clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2 ≤ C4 := by
      rw [hC4]
      have h1 : ‖clusterCM m k (deriv x t)‖ ^ 2 ≤ Ccm ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hcm t htε) 2
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1 (clusterMass_nonneg (fun i => (hm i).le) k)) (by norm_num)
    have hcmsq_nn : 0 ≤ clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2 :=
      div_nonneg (mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _))
        (by norm_num)
    rw [hdiff]
    calc |clusterEnergy m k (x t) (deriv x t)
          - clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2|
        ≤ |clusterEnergy m k (x t) (deriv x t)|
          + |clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2| := abs_sub _ _
      _ = |clusterEnergy m k (x t) (deriv x t)|
          + clusterMass m k * ‖clusterCM m k (deriv x t)‖ ^ 2 / 2 := by
            rw [abs_of_nonneg hcmsq_nn]
      _ ≤ (C1 + C2 + C3) + C4 := add_le_add hEr hcmsq
  -- the interaction work
  have hW : |crossWork m k (x t) (cmRel m k (x t))| ≤ C5 := by
    have hd : ∀ p : Fin N, ‖(cmRel m k (x t)) p‖ ≤ 1 := by
      intro p
      by_cases hp : p ∈ k
      · rw [cmRel_apply_of_mem hp]
        refine le_trans (norm_sub_clusterCM_le_sqrt hκ hκpos hp) ?_
        exact Real.sqrt_le_one.mpr ((div_le_one hκpos).mpr (hε₁ t ht))
      · rw [cmRel_apply_of_notMem hp, norm_zero]
        norm_num
    have h := abs_crossWork_le (m := m) (k := k) (x := x t) (ν := ν) (R := 1)
      (fun i => (hm i).le) hν (by norm_num : (0:ℝ) ≤ 1) (hsep t htε) hd
    rw [hC5]
    simpa using h
  have hC1nn : 0 ≤ C1 := by rw [hC1]; exact abs_nonneg _
  exact ⟨le_trans hErel (le_trans (le_add_of_nonneg_right hC5nn) (le_max_right _ _)),
    le_trans hW (le_trans (le_add_of_nonneg_left (by linarith [hC1nn, hC2nn, hC3nn, hC4nn]))
      (le_max_right _ _))⟩

end Submission.NBody
