import Submission.NBody.MarchalClusterShapeThirdDeriv
import Submission.NBody.MarchalClusterShapeSecondDeriv

/-!
# Componentwise derivatives of the normalised configuration

The normalised configuration `s = clusterShape m k (x ·)` takes values in `EN E N`, so its
components are **`E`-valued**: `(clusterShape m k (x t)) i : E`.  For the scalar Tauberian
argument of `as:lim2` one needs the derivatives of these components, and their identification with
the components of the derivative of the whole configuration.

This file collects those identifications (all of them are `=ᶠ` statements at a point `t ∈ (0,ε)`,
plus the derived `HasDerivAt` facts).

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

/-- **The derivative of a component** of the normalised configuration is the component of the
derivative. -/
lemma deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε t : ℝ}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ τ ∈ Ioo (0:ℝ) ε, WithoutCollisions (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ) (i : Fin N) :
    deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)
      =ᶠ[𝓝 t] (fun τ : ℝ => (deriv (fun s : ℝ => clusterShape m k (x s)) τ) i) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  have hevτ : ∀ᶠ s in 𝓝 τ, HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    exact hx s hs
  have h := hasDerivAt_clusterShape_curve (m := m) (k := k) (x := x)
    (clusterInertia_pos hm hk2 (hnc τ hτ)) hevτ
  have h' : HasDerivAt (fun s : ℝ => clusterShape m k (x s))
      (deriv (fun s : ℝ => clusterShape m k (x s)) τ) τ := h.congr_deriv h.deriv.symm
  exact (hasDerivAt_apply h' i).deriv

/-- **The second derivative of a component** is the component of the second derivative of the
normalised configuration. -/
lemma deriv_deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ τ ∈ Ioo (0:ℝ) ε, WithoutCollisions (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) (i : Fin N) :
    deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))
      =ᶠ[𝓝 t]
        (fun τ : ℝ => (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) τ) i) := by
  have h1 : deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))
      =ᶠ[𝓝 t] deriv (fun τ : ℝ => (deriv (fun s : ℝ => clusterShape m k (x s)) τ) i) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact (deriv_coord_clusterShape hm hk2 hτ hnc hx i).deriv_eq
  have h2 : deriv (fun τ : ℝ => (deriv (fun s : ℝ => clusterShape m k (x s)) τ) i)
      =ᶠ[𝓝 t] (fun τ : ℝ => (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) τ) i) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have h := hasDerivAt_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := τ) hτ
      (fun υ hυ => clusterInertia_pos hm hk2 (hnc υ hυ)) hx hd2 hode
    exact (hasDerivAt_apply (h.congr_deriv h.deriv.symm) i).deriv
  exact h1.trans h2

/-- **The second derivative of a component is differentiable.** -/
lemma hasDerivAt_deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ τ ∈ Ioo (0:ℝ) ε, WithoutCollisions (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) (i : Fin N) :
    HasDerivAt (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))
      (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)) t) t := by
  have h := (hasDerivAt_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t) ht
    (fun υ hυ => clusterInertia_pos hm hk2 (hnc υ hυ)) hx hd2 hode)
  have hcurve : HasDerivAt (deriv (fun s : ℝ => clusterShape m k (x s)))
      (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) t) t :=
    h.congr_deriv h.deriv.symm
  have hcoord := (hasDerivAt_apply hcurve i).congr_of_eventuallyEq
    (deriv_coord_clusterShape hm hk2 ht hnc hx i)
  exact hcoord.congr_deriv ((deriv_deriv_coord_clusterShape hm hk2 ht hnc hx hd2 hode i).self_of_nhds).symm

/-- **The third derivative of a component is the component of the third derivative.** -/
lemma deriv_deriv_deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ τ ∈ Ioo (0:ℝ) ε, WithoutCollisions (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hd3 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) (i : Fin N) :
    deriv (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))) t
      = (deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t) i := by
  have h1 : deriv (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))) t
      = deriv (fun τ : ℝ => (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) τ) i) t :=
    (deriv_deriv_coord_clusterShape hm hk2 ht hnc hx hd2 hode i).deriv_eq
  have h2 : deriv (fun τ : ℝ => (deriv (deriv (fun s : ℝ => clusterShape m k (x s))) τ) i) t
      = (deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t) i := by
    have h := hasDerivAt_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t) ht
      (fun υ hυ => clusterInertia_pos hm hk2 (hnc υ hυ)) hx hd2 hd3 hode
    exact (hasDerivAt_apply (h.congr_deriv h.deriv.symm) i).deriv
  rw [h1, h2]

/-- **The third derivative of a component is differentiable.** -/
lemma hasDerivAt_deriv_deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card)
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hnc : ∀ τ ∈ Ioo (0:ℝ) ε, WithoutCollisions (x τ))
    (hx : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x τ) τ)
    (hd2 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x τ) τ)
    (hd3 : ∀ τ ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) τ) τ)
    (hode : ∀ τ ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x τ = ∇_[m] (U m) (x τ)) (i : Fin N) :
    HasDerivAt (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i)))
      (deriv (deriv (deriv (fun τ : ℝ => (clusterShape m k (x τ)) i))) t) t := by
  have h := hasDerivAt_deriv_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (t := t) ht
    (fun υ hυ => clusterInertia_pos hm hk2 (hnc υ hυ)) hx hd2 hd3 hode
  have hcurve : HasDerivAt (deriv (deriv (fun s : ℝ => clusterShape m k (x s))))
      (deriv (deriv (deriv (fun s : ℝ => clusterShape m k (x s)))) t) t :=
    h.congr_deriv h.deriv.symm
  have hcoord := (hasDerivAt_apply hcurve i).congr_of_eventuallyEq
    (deriv_deriv_coord_clusterShape hm hk2 ht hnc hx hd2 hode i)
  exact hcoord.congr_deriv
    ((deriv_deriv_deriv_coord_clusterShape hm hk2 ht hnc hx hd2 hd3 hode i).symm)

/-- **The derivative of a component of the normalised configuration, weighted by `t`, tends to
`0`** (the componentwise form of `as:lim1`). -/
theorem tendsto_smul_deriv_coord_clusterShape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C)
    (hν : 0 < ν) (hCv : 0 ≤ Cv)
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
    (i : Fin N) :
    Tendsto (fun t : ℝ => t • deriv (fun τ : ℝ => (clusterShape m k (x τ)) i) t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto
      (fun t : ℝ => ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε)
      (C := C) (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep
      hv hI).norm
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have he : deriv (fun τ : ℝ => (clusterShape m k (x τ)) i) t
      = (deriv (fun s : ℝ => clusterShape m k (x s)) t) i :=
    (deriv_coord_clusterShape hm hk2 ht hnc hx i).self_of_nhds
  rw [he]
  calc ‖t • (deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖
      = t * ‖(deriv (fun s : ℝ => clusterShape m k (x s)) t) i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
    _ ≤ t * ‖deriv (fun s : ℝ => clusterShape m k (x s)) t‖ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) ht.1.le
    _ = ‖t • deriv (fun s : ℝ => clusterShape m k (x s)) t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]

end Submission.NBody
