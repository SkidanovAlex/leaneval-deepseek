import Submission.NBody.MarchalSundmanApply

/-!
# The centre-of-mass-relative energy of a cluster

The Lagrange–Jacobi identity of `MarchalSundman` reads

    `Ï_k = 4 E_k + 2 U_k + 2·crossWork_k − 2 m_k‖v_{cm,k}‖²`,

where `E_k = (1/2)∑_{i∈k} mᵢ‖vᵢ‖² − U_k` uses the *full* kinetic energy of the cluster.  For the
Sundman analysis one wants the identity without the centre-of-mass motion, which is what the
*relative* energy below does: with

    `E_k^{rel} = (1/2)∑_{i∈k} mᵢ‖vᵢ − v_{cm,k}‖² − U_k`

one has the clean identity

    `Ï_k = 4 E_k^{rel} + 2 U_k + 2·crossWork_k`,

and, since `‖vᵢ − v_{cm,k}‖ ≤ ‖vᵢ‖`, the two Ostrogradsky-type inequalities take the form

* `(İ_k)² ≤ 4 I_k Ï_k + 16 C I_k`   from `|E_k^{rel}| ≤ C` and `|crossWork_k| ≤ C`;
* `c/√(I_k) ≤ Ï_k + 6 C`            from `E_k^{rel} ≥ −C`, `crossWork_k ≥ −C`, `U_k ≥ c/√(I_k)`.

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

/-- Twice the centre-of-mass-relative kinetic energy of a cluster. -/
noncomputable def clusterRelKinetic (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) : ℝ :=
  clusterKineticSq m k (cmRel m k v)

/-- The centre-of-mass-relative energy of a cluster. -/
noncomputable def clusterRelEnergy (m : Fin N → ℝ) (k : Finset (Fin N)) (x v : EN E N) : ℝ :=
  clusterRelKinetic m k v / 2 - clusterPotential m k x

/-- The energy of a cluster is its relative energy plus half the kinetic energy of its centre of
mass. -/
lemma clusterEnergy_eq_relEnergy_add {m : Fin N → ℝ} {k : Finset (Fin N)} (hm : ∀ i, 0 < m i)
    (hk : k.Nonempty) (x v : EN E N) :
    clusterEnergy m k x v
      = clusterRelEnergy m k x v + clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2 := by
  unfold clusterEnergy clusterRelEnergy clusterRelKinetic
  rw [clusterKineticSq_cmRel k v hm hk]
  ring

/-- **The Lagrange–Jacobi identity for a cluster, in centre-of-mass-relative form.** -/
theorem iteratedDeriv_two_clusterInertia_rel {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {t : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hnc : WithoutCollisions (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t)) :
    iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
      = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
  rw [iteratedDeriv_two_clusterInertia_energy hm hk hnc hx hd2 hode]
  unfold clusterEnergy clusterRelEnergy clusterRelKinetic
  rw [clusterKineticSq_cmRel k (deriv x t) hm hk]
  ring

/-- **Ostrogradsky's inequality for a cluster, in centre-of-mass-relative form.**  Bounding the
relative energy and the interaction work by `C` gives

    `(İ_k)² ≤ 4 I_k Ï_k + 16 C I_k`. -/
theorem clusterInertia_deriv_sq_le_rel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t C : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hE : |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : WithoutCollisions (x t)) :
    (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
      ≤ 4 * clusterInertia m k (x t)
          * iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t
        + 16 * C * clusterInertia m k (x t) := by
  have hEnn : -C ≤ clusterRelEnergy m k (x t) (deriv x t) := (abs_le.mp hE).1
  have hWnn : -C ≤ crossWork m k (x t) (cmRel m k (x t)) := (abs_le.mp hW).1
  have hderiv : deriv (fun s : ℝ => clusterInertia m k (x s)) t
      = 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t)) :=
    (deriv_clusterInertia_eq m k hx).self_of_nhds
  have hLJ := iteratedDeriv_two_clusterInertia_rel hm hk hnc hx hd2 hode
  have hCS : (massInner m (cmRel m k (x t)) (cmRel m k (deriv x t))) ^ 2
      ≤ clusterInertia m k (x t) * clusterRelKinetic m k (deriv x t) :=
    ostrogradsky (fun i => (hm i).le) k (x t) (deriv x t)
  have hfac : 0 ≤ clusterInertia m k (x t) := clusterInertia_nonneg (fun i => (hm i).le) k (x t)
  have hstep1 : (2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv x t))) ^ 2
      ≤ 4 * clusterInertia m k (x t) * clusterRelKinetic m k (deriv x t) := by
    nlinarith [hCS, hfac]
  have hK : clusterRelKinetic m k (deriv x t)
      = 2 * (clusterRelKinetic m k (deriv x t) / 2 - clusterPotential m k (x t))
        + 2 * clusterPotential m k (x t) := by ring
  rw [hderiv, hLJ]
  simp only [clusterRelEnergy] at hEnn ⊢
  nlinarith [hstep1, hEnn, hWnn, hfac, hK]

/-- **The lower bound on `Ï_k` in centre-of-mass-relative form.**  Bounding the relative energy and
the interaction work below by `−C` and using `U_k ≥ ck/√(I_k)` gives

    `ck/√(I_k) ≤ Ï_k + 6 C`. -/
theorem clusterInertia_second_deriv_ge_rel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {t C ck : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hE : -C ≤ clusterRelEnergy m k (x t) (deriv x t))
    (hW : -C ≤ crossWork m k (x t) (cmRel m k (x t)))
    (hU : ck / Real.sqrt (clusterInertia m k (x t)) ≤ clusterPotential m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s)
    (hd2 : HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hode : iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hnc : WithoutCollisions (x t)) :
    ck / Real.sqrt (clusterInertia m k (x t))
      ≤ iteratedDeriv 2 (fun s : ℝ => clusterInertia m k (x s)) t + 6 * C := by
  have hLJ := iteratedDeriv_two_clusterInertia_rel hm hk hnc hx hd2 hode
  have hU0 : 0 ≤ clusterPotential m k (x t) := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (le_of_lt (hm p.1)) (le_of_lt (hm p.2)))
        (inv_nonneg.mpr dist_nonneg)
  rw [hLJ]
  simp only [clusterRelEnergy] at hE ⊢
  linarith

/-- The relative energy is bounded by the full energy plus half a bound on the centre-of-mass
kinetic energy. -/
lemma abs_clusterRelEnergy_le {m : Fin N → ℝ} {k : Finset (Fin N)} (hm : ∀ i, 0 < m i)
    (hk : k.Nonempty) (x v : EN E N) :
    |clusterRelEnergy m k x v|
      ≤ |clusterEnergy m k x v| + clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2 := by
  have h := clusterEnergy_eq_relEnergy_add hm hk x v
  have hnn : 0 ≤ clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2 := by
    have := clusterMass_nonneg (fun i => (hm i).le) k
    positivity
  have : clusterRelEnergy m k x v
      = clusterEnergy m k x v - clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2 := by linarith
  rw [this]
  calc |clusterEnergy m k x v - clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2|
      ≤ |clusterEnergy m k x v| + |clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2| := abs_sub _ _
    _ = |clusterEnergy m k x v| + clusterMass m k * ‖clusterCM m k v‖ ^ 2 / 2 := by
        rw [abs_of_nonneg hnn]

end Submission.NBody
