import Submission.NBody.MarchalClusterPlumbing
import Submission.NBody.MarchalSundmanGeneral
import Submission.NBody.MarchalSperner

/-!
# The sum of the moments of inertia of a family of clusters

At an interior collision time `t₀` of a solution of the Newtonian `N`-body problem there may be
**several** collision classes `C₁, …, C_r` collapsing simultaneously.  The single-cluster Sundman
theory (`MarchalClusterAsymptotic`) does not apply to any one of them directly, because the bodies
of the other classes have unbounded velocities; following Ferrario–Terracini one works instead with
the *sum*

    `f(t) = ∑_{l} I_{C_l}(x(t))`

of the moments of inertia of all the colliding clusters.  The Lagrange–Jacobi identity is additive
over the clusters, so `f` obeys

    `f̈ = 4 ∑_l E^{rel}_{C_l} + 2 ∑_l U_{C_l} + 2 ∑_l W_{C_l}`,

and the whole Sundman analysis (the Ostrogradsky inequality, the lower bound on `f̈`, the
monotonicity of `f'`, the third-derivative estimate and the Tauberian lemma) can be run for `f`.

This module contains the definition and the *calculus*: the first and second derivatives of
`t ↦ multiInertia m ks (x t)`, and the Lagrange–Jacobi identity for `f`.

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

/-- The sum of the moments of inertia of a finite family of clusters. -/
noncomputable def multiInertia (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : ℝ :=
  ∑ k ∈ ks, clusterInertia m k x

lemma multiInertia_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : 0 ≤ multiInertia m ks x :=
  Finset.sum_nonneg fun k _ => clusterInertia_nonneg hm k x

/-- The sum of the centre-of-mass-relative energies of a family of clusters. -/
noncomputable def multiRelEnergy (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (x v : EN E N) : ℝ :=
  ∑ k ∈ ks, clusterRelEnergy m k x v

/-- The sum of the internal potentials of a family of clusters. -/
noncomputable def multiPotential (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : ℝ :=
  ∑ k ∈ ks, clusterPotential m k x

/-- The sum of the internal potentials of a family of clusters is non-negative. -/
lemma multiPotential_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : 0 ≤ multiPotential m ks x :=
  Finset.sum_nonneg fun k _ => by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (inv_nonneg.mpr dist_nonneg)

/-- The sum of the interaction works of a family of clusters. -/
noncomputable def multiCrossWork (m : Fin N → ℝ) (ks : Finset (Finset (Fin N)))
    (x : EN E N) : ℝ :=
  ∑ k ∈ ks, crossWork m k x (cmRel m k x)

/-- `HasDerivAt` of a finite sum of functions, in the `∑ i, A i x` form. -/
lemma hasDerivAt_sum_apply {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) (A' : ι → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (A i) (A' i) t) :
    HasDerivAt (fun r : ℝ => ∑ i ∈ s, A i r) (∑ i ∈ s, A' i) t := by
  have hsum := HasDerivAt.sum h
  have heq : (fun r : ℝ => ∑ i ∈ s, A i r) =ᶠ[𝓝 t] (∑ i ∈ s, A i) :=
    Filter.Eventually.of_forall fun r => by simp only [Finset.sum_apply]
  exact hsum.congr_of_eventuallyEq heq

/-- **First derivative of the sum of the moments of inertia.** -/
lemma hasDerivAt_multiInertia_curve {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    HasDerivAt (fun s : ℝ => multiInertia m ks (x s))
      (deriv (fun s : ℝ => multiInertia m ks (x s)) t) t := by
  have h := hasDerivAt_sum_apply ks (fun k (s : ℝ) => clusterInertia m k (x s))
    (fun k => deriv (fun s : ℝ => clusterInertia m k (x s)) t) t
    (fun k _ => hasDerivAt_clusterInertia_curve (k := k) hx)
  have hd : deriv (fun s : ℝ => multiInertia m ks (x s)) t
      = ∑ k ∈ ks, deriv (fun s : ℝ => clusterInertia m k (x s)) t := h.deriv
  rw [hd]
  exact h

/-- **Second derivative of the sum of the moments of inertia.** -/
lemma hasDerivAt_deriv_multiInertia_curve {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t : ℝ} (htm : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s) :
    HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (x s)))
      (deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t) t := by
  have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact hx s hs
  -- the derivative of `f` near `t` is the sum of the derivatives of the clusters
  have hderiv : deriv (fun s : ℝ => multiInertia m ks (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    have hsum := hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (t := s) (x := x)
        (by filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr; exact hx r hr))
    exact hsum.deriv
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t :=
    hasDerivAt_sum_apply ks (fun k (s : ℝ) => deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (fun k => deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := t)
        (by filter_upwards [isOpen_Ioo.mem_nhds htm] with r hr; exact hx r hr)
        (hd2 t htm))
  have h1 : HasDerivAt (deriv (fun s : ℝ => multiInertia m ks (x s)))
      (∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t :=
    hsum2.congr_of_eventuallyEq hderiv
  have h2 : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv]
    exact hsum2.deriv
  rw [h2]
  exact h1

/-- **The Lagrange–Jacobi identity for a family of clusters.** -/
theorem iteratedDeriv_two_multiInertia {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (htm : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s)) :
    iteratedDeriv 2 (fun s : ℝ => multiInertia m ks (x s)) t
      = 4 * multiRelEnergy m ks (x t) (deriv x t)
        + 2 * multiPotential m ks (x t) + 2 * multiCrossWork m ks (x t) := by
  have hxev : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    exact hx s hs
  have hd2' : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s :=
    fun s hs => (hd2 s hs).congr_deriv (iteratedDeriv_two_eq_deriv_deriv x s)
  -- the derivative of `f` near `t`
  have hderiv : deriv (fun s : ℝ => multiInertia m ks (x s)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with s hs
    have hsum := hasDerivAt_sum_apply ks (fun k (r : ℝ) => clusterInertia m k (x r))
      (fun k => deriv (fun r : ℝ => clusterInertia m k (x r)) s) s
      (fun k _ => hasDerivAt_clusterInertia_curve (k := k) (t := s) (x := x)
        (by filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr; exact hx r hr))
    exact hsum.deriv
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ ks, deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t :=
    hasDerivAt_sum_apply ks (fun k (s : ℝ) => deriv (fun r : ℝ => clusterInertia m k (x r)) s)
      (fun k => deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t) t
      (fun k _ => hasDerivAt_deriv_clusterInertia_curve (k := k) (t := t)
        (by filter_upwards [isOpen_Ioo.mem_nhds htm] with r hr; exact hx r hr)
        (hd2' t htm))
  have hval : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = ∑ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t := by
    rw [Filter.EventuallyEq.deriv_eq hderiv]
    exact hsum2.deriv
  have hcluster : ∀ k ∈ ks, deriv (deriv (fun r : ℝ => clusterInertia m k (x r))) t
      = 4 * clusterRelEnergy m k (x t) (deriv x t) + 2 * clusterPotential m k (x t)
        + 2 * crossWork m k (x t) (cmRel m k (x t)) := by
    intro k hk
    exact deriv_deriv_clusterInertia_curve_eq hm (hne k hk) (hnc t htm) hxev
      (hd2 t htm) (hode t htm)
  rw [iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => multiInertia m ks (x s)) t, hval]
  rw [Finset.sum_congr rfl hcluster]
  simp only [multiRelEnergy, multiPotential, multiCrossWork]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-- **The second derivative of the sum of the moments of inertia**, in the Lagrange–Jacobi form. -/
theorem deriv_deriv_multiInertia_curve_eq {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε t : ℝ} (hm : ∀ i, 0 < m i) (hne : ∀ k ∈ ks, k.Nonempty)
    (htm : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s)) :
    deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = 4 * multiRelEnergy m ks (x t) (deriv x t)
        + 2 * multiPotential m ks (x t) + 2 * multiCrossWork m ks (x t) := by
  rw [← iteratedDeriv_two_eq_deriv_deriv (fun s : ℝ => multiInertia m ks (x s)) t]
  exact iteratedDeriv_two_multiInertia (m := m) (ks := ks) (x := x) (ε := ε) (t := t)
    hm hne htm hnc hx hd2 hode

end Submission.NBody
