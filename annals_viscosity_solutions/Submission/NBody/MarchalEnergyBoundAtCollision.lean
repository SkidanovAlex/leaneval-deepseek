import Submission.NBody.MarchalKineticBoundAtCollision
import Submission.NBody.MarchalOutsideVelocity
import Submission.NBody.EnergyAe
import Submission.NBody.EnergyLevel

/-!
# The relative-energy bound of a colliding cluster, from the a.e. energy identity

Ferrario--Terracini's `lemma:bounded_energy` (and its `eq:Ei`/`est_E`) gives the boundedness of the
cluster energy `E^{rel}_k` near a collision.  The present file obtains it from the *global* a.e.
energy identity of `Submission.NBody.EnergyAe.ae_energy_eq_of_minimizer` — which needs neither
collision freeness nor differentiability:

  `energy m γ t = h` almost everywhere for an `h`-minimiser of finite action,

combined with the fact that the total energy is constant on every collision-free interval (the
minimiser is `C²` there).  The (purely algebraic) decomposition
`E^{rel}_k = energy - K^{rest} + U^{rest} - K^{cm,k}` then reduces the boundedness of `E^{rel}_k` to
that of the SLOW kinetic energies (`K^{rest}`, `K^{cm,k}`) and of `U^{rest}` — all of which are
controlled by the separation of the cluster from the outside.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The energy of an `h`-minimiser is `h` on a collision-free interval.**  The a.e. identity of
`ae_energy_eq_of_minimizer` upgrades to a pointwise one because the energy is constant on every
collision-free interval. -/
theorem energy_eq_level_of_minimizer {m : Fin N → ℝ} {h : ℝ} {x : ℝ → EN E N} {ε : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hε : 0 < ε)
    (hac : AbsolutelyContinuousOnInterval x 0 ε)
    (hmin : IsHMinimizer m h x 0 ε) (hfin : actionPot m h (x 0) (x ε) < ⊤)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t)) :
    ∀ t ∈ Ioo (0:ℝ) ε, energy m x t = h := by
  classical
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  -- the energy is constant on the interval
  have hconst : ∀ s ∈ Ioo (0:ℝ) ε, ∀ t ∈ Ioo (0:ℝ) ε, energy m x s = energy m x t :=
    fun s hs t ht => energy_eq_of_mem_Ioo hmne hx hd2 hode hnc hs ht
  -- and equals `h` almost everywhere
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0:ℝ) ε)), energy m x t = h :=
    ae_energy_eq_of_minimizer hm hh.le hε hac hmin hfin
  intro t ht
  by_contra hne
  -- then the whole interval consists of such points
  have hsub : Ioo (0:ℝ) ε ⊆ {s : ℝ | energy m x s ≠ h} ∩ Ioo (0:ℝ) ε := by
    intro s hs
    exact ⟨fun hcon => hne ((hconst s hs t ht).symm.trans hcon), hs⟩
  have hZ : volume ({s : ℝ | energy m x s ≠ h} ∩ Ioo (0:ℝ) ε) = 0 := by
    have h := MeasureTheory.ae_iff.mp hae
    simpa [Set.ofPred_and] using h
  have hpos : 0 < volume (Ioo (0:ℝ) ε) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hz : volume (Ioo (0:ℝ) ε) = 0 := measure_mono_null hsub hZ
  rw [hz] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **The relative-energy bound of a colliding cluster** (`lemma:bounded_energy`, quantitative form).
Let `γ` be an `h`-minimiser on `[a,b]` with a collision time `t₀ ∈ (a,b)`, and let `k` be a cluster
whose complement is separated from it by `ν` on the collision-free side `(t₀, t₀+ε)`.  Then the
relative energy of `k` is bounded on `(t₀, t₀+ε/4)`. -/
theorem exists_relEnergy_bound_at_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε ν : ℝ} {k : Finset (Fin N)}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε < b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hkne : k.Nonempty)
    (hsep : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparated k (γ t) ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (t₀ + ε / 4),
      |clusterRelEnergy m k (γ t) (deriv γ t)| ≤ C := by
  classical
  set x : ℝ → EN E N := fun u => γ (t₀ + u) with hxdef
  -- the strip
  have hsub : uIcc t₀ (t₀ + ε) ⊆ uIcc a b := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc ht₀.1.le hεb.le
  have hac' : AbsolutelyContinuousOnInterval γ t₀ (t₀ + ε) := hac.mono hsub
  -- the shifted curve is absolutely continuous
  have hacx : AbsolutelyContinuousOnInterval x 0 ε := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := t₀) (b := t₀ + ε) (c := 1) (d := t₀) (by norm_num) hac'
    have h2 : (fun t : ℝ => γ (1 * t + t₀)) = x := by
      funext t; rw [hxdef]; ring_nf
    rw [h2] at h
    simpa using h
  -- the shifted curve is a minimiser
  have hminx : IsHMinimizer m h x 0 ε := by
    have hsub' : IsHMinimizer m h γ t₀ (t₀ + ε) :=
      IsHMinimizer.sub hac hmin (IsHMinimizer.actionOn_lt_top hmin (hfin (γ a) (γ b)))
        ht₀.1 (by linarith) hεb
    have h1 : actionOn m h x 0 ε = actionOn m h γ t₀ (t₀ + ε) := by
      have h := actionOn_comp_add_const' (m := m) (h := h) (γ := γ) (c := t₀) (d := t₀ + ε)
      have h2 : (fun t : ℝ => γ (t + t₀)) = x := by
        funext t; rw [hxdef]; ring_nf
      rw [← h2]
      simpa using h
    have hx0 : x 0 = γ t₀ := by rw [hxdef]; ring_nf
    have hxε : x ε = γ (t₀ + ε) := by rw [hxdef]
    show actionOn m h x 0 ε = actionPot m h (x 0) (x ε)
    rw [hx0, hxε, h1]
    exact hsub'
  have hfinx : actionPot m h (x 0) (x ε) < ⊤ := hfin (x 0) (x ε)
  -- the Newton data on the strip
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := Ioo t₀ (t₀ + ε)) (fun t ht => ⟨ht₀.1.trans ht.1, ht.2.trans hεb⟩) (fun t ht => hnc t ht)
  have hmem : ∀ u ∈ Ioo (0:ℝ) ε, t₀ + u ∈ Ioo t₀ (t₀ + ε) :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hxγ : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt γ (deriv γ (t₀ + u)) (t₀ + u) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).1.self_of_nhds
  have hd2γ : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv γ) (iteratedDeriv 2 γ (t₀ + u)) (t₀ + u) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).2.1
  have hodeγ : ∀ u ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 γ (t₀ + u) = ∇_[m] (U m) (γ (t₀ + u)) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).2.2
  have hncx : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u) := fun u hu => hnc (t₀ + u) (hmem u hu)
  have hx' : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => γ (t₀ + s)) (deriv γ (t₀ + u)) u :=
      (hxγ u hu).comp_const_add t₀ u
    have h2 : deriv x u = deriv γ (t₀ + u) := deriv_shiftCurve_eq t₀ u
    rw [h2]
    exact h1
  have hd2' : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => deriv γ (t₀ + s)) (iteratedDeriv 2 γ (t₀ + u)) u :=
      (hd2γ u hu).comp_const_add t₀ u
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2]
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact h1
  have hd2'' : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) u) u := fun u hu =>
    (hd2' u hu).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x u)
  have hode' : ∀ u ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x u = ∇_[m] (U m) (x u) := fun u hu => by
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact hodeγ u hu
  have hode'' : ∀ u ∈ Ioo (0:ℝ) ε, deriv (deriv x) u = ∇_[m] (U m) (x u) := fun u hu =>
    (iteratedDeriv_two_eq_deriv_deriv x u).symm.trans (hode' u hu)
  -- the energy identity
  have hEid : ∀ u ∈ Ioo (0:ℝ) ε, energy m x u = h :=
    energy_eq_level_of_minimizer hm hh hε hacx hminx hfinx hx' hd2' hode' hncx
  -- the separation on the strip
  have hsepx : ∀ u ∈ Ioo (0:ℝ) ε, ClusterSeparated k (x u) ν := fun u hu => hsep (t₀ + u) (hmem u hu)
  -- the three bounds
  obtain ⟨Cv, hCv0, hCv⟩ := exists_bound_deriv_outside (m := m) (k := k) (ε := ε) (ν := ν)
    hm hε hν hsepx hncx hode' hd2'
  have hA0 : 0 ≤ (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2) :=
    mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
      (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le) (sq_nonneg _))
  have hacc : ∀ u ∈ Ioo (0:ℝ) ε,
      ‖clusterCM m k (iteratedDeriv 2 x u)‖
        ≤ (clusterMass m k)⁻¹
          * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
              * (ν⁻¹) ^ 2) := by
    intro u hu
    rw [hode' u hu]
    exact norm_clusterCM_weightedGrad_le (m := m) (k := k) (x := x u) (ν := ν)
      hm hν (hsepx u hu).weak (hncx u hu)
  have hCcm := exists_bound_clusterCM_deriv (m := m) (k := k) (x := x) (ε := ε)
    (A := _) hε hA0 hd2' hacc
  -- the constant
  refine ⟨|h| + (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 / 2
      + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2) / ν
      + clusterMass m k
        * (((clusterMass m k)⁻¹
            * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
                * (ν⁻¹) ^ 2)) * (ε / 4)
          + ‖clusterCM m k (deriv x (ε / 4))‖) ^ 2 / 2, ?_, ?_⟩
  · have h1 : 0 ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 / 2 :=
      div_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (sq_nonneg _)) (by norm_num)
    have h2 : 0 ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2) / ν :=
      div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) hν.le
    have h3 : 0 ≤ clusterMass m k
        * (((clusterMass m k)⁻¹
            * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
                * (ν⁻¹) ^ 2)) * (ε / 4)
          + ‖clusterCM m k (deriv x (ε / 4))‖) ^ 2 / 2 :=
      div_nonneg (mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)) (by norm_num)
    linarith [abs_nonneg h]
  · intro t ht
    -- the point `t` in the strip
    have htmem : t - t₀ ∈ Ioo (0:ℝ) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htmem4 : t - t₀ ∈ Ioo (0:ℝ) (ε / 4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hEt : energy m x (t - t₀) = h := hEid (t - t₀) htmem
    have hxt : x (t - t₀) = γ t := by simp [hxdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hderivt : deriv x (t - t₀) = deriv γ t := by
      rw [deriv_shiftCurve_eq]
      congr 1
      ring
    -- the decomposition
    have hcl : clusterEnergy m k (γ t) (deriv γ t)
        = energy m γ t - (outsideKineticSq m k (deriv γ t) / 2 - clusterPotentialRest m k (γ t)) :=
      clusterEnergy_eq_energy_sub_rest m k γ t
    have hrel := clusterEnergy_eq_relEnergy_add (k := k) hm hkne (γ t) (deriv γ t)
    have hkey : clusterRelEnergy m k (γ t) (deriv γ t)
        = (energy m γ t - (outsideKineticSq m k (deriv γ t) / 2 - clusterPotentialRest m k (γ t)))
          - clusterMass m k * ‖clusterCM m k (deriv γ t)‖ ^ 2 / 2 := by
      rw [← hcl]
      linarith [hrel]
    -- the bounds
    have hK : outsideKineticSq m k (deriv γ t) / 2
        ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 / 2 := by
      rw [outsideKineticSq]
      rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
      calc ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j * ‖deriv γ t j‖ ^ 2
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j * Cv ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hvj : ‖deriv γ t j‖ ≤ Cv := by
              have := hCv (t - t₀) htmem j (Finset.mem_filter.mp hj).2
              rwa [hderivt] at this
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hvj 2) (hm j).le
        _ = (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * Cv ^ 2 :=
            (Finset.sum_mul _ _ _).symm
    have hU : clusterPotentialRest m k (γ t)
        ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) / ν :=
      clusterPotentialRest_le (fun i => (hm i).le) hν
        (hsep t ⟨ht.1, by linarith [ht.2]⟩)
    have hC : clusterMass m k * ‖clusterCM m k (deriv γ t)‖ ^ 2 / 2
        ≤ clusterMass m k
          * (((clusterMass m k)⁻¹
              * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
                  * (ν⁻¹) ^ 2)) * (ε / 4)
            + ‖clusterCM m k (deriv x (ε / 4))‖) ^ 2 / 2 := by
      have h1 : ‖clusterCM m k (deriv γ t)‖ = ‖clusterCM m k (deriv x (t - t₀))‖ := by
        rw [hderivt]
      rw [h1]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hCcm (t - t₀) htmem4) 2)
          (clusterMass_nonneg (fun i => (hm i).le) k)) (by norm_num)
    have henergy : energy m γ t = h := by
      have h1 : energy m γ t = energy m x (t - t₀) := by
        rw [show energy m x (t - t₀) = (1/2) * ∑ i, m i * ‖deriv x (t - t₀) i‖ ^ 2 - U m (x (t - t₀)) from rfl]
        rw [hxt, hderivt]
        rfl
      rw [h1, hEt]
    have hKnn : 0 ≤ outsideKineticSq m k (deriv γ t) / 2 :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hm j).le (sq_nonneg _)) (by norm_num)
    have hUnn : 0 ≤ clusterPotentialRest m k (γ t) :=
      clusterPotentialRest_nonneg (fun i => (hm i).le) k (γ t)
    have hCnn : 0 ≤ clusterMass m k * ‖clusterCM m k (deriv γ t)‖ ^ 2 / 2 :=
      div_nonneg (mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)) (by norm_num)
    rw [hkey, henergy]
    rw [abs_le]
    constructor <;>
      linarith [abs_nonneg h, neg_abs_le h, le_abs_self h, hK, hU, hC, hKnn, hUnn, hCnn]

end Submission.NBody

