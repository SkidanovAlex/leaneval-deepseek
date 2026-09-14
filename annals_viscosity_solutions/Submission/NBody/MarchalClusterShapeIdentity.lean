import Submission.NBody.MarchalClusterShape

/-!
# The normalised-configuration identity

The counterpart of the Lagrange–Jacobi identity for the *normalised* configuration `s = I_k^{-1/2}q`:

    `I_k · R_k(ṡ) = R_k(ẋ) - (İ_k)²/(4 I_k)`.

Together with the Jacobi–Lagrange identity `Ï_k = R_k(ẋ) + 2E_k^{rel} + 2W_k` this is what turns
the asymptotics of `I_k`, `İ_k`, `Ï_k` into the statement `t · ṡ_i → 0` of Ferrario–Terracini.

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

/-- The mass inner product of two centre-of-mass-relative configurations as a sum of the
centre-of-mass-relative coordinates. -/
lemma massInner_cmRel_sum (m : Fin N → ℝ) (k : Finset (Fin N)) (X V : EN E N) :
    massInner m (cmRel m k X) (cmRel m k V)
      = ∑ i ∈ k, m i * ⟪(cmRel m k X) i, (cmRel m k V) i⟫_ℝ := by
  rw [massInner_cmRel_eq]
  exact Finset.sum_congr rfl fun i hi => by
    rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hi]

/-- Expansion of the mass-weighted squared norm of `a • v + b • w`. -/
lemma clusterKineticSq_smul_add (m : Fin N → ℝ) (k : Finset (Fin N)) (a b : ℝ) (v w : EN E N) :
    clusterKineticSq m k (a • v + b • w)
      = a ^ 2 * clusterKineticSq m k v
        + 2 * a * b * (∑ i ∈ k, m i * ⟪v i, w i⟫_ℝ)
        + b ^ 2 * clusterKineticSq m k w := by
  have hpt : ∀ i : Fin N, m i * ‖(a • v + b • w) i‖ ^ 2
      = a ^ 2 * (m i * ‖v i‖ ^ 2) + 2 * a * b * (m i * ⟪v i, w i⟫_ℝ)
        + b ^ 2 * (m i * ‖w i‖ ^ 2) := by
    intro i
    have h1 : (a • v + b • w) i = a • v i + b • w i := by simp
    rw [h1, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [clusterKineticSq, clusterKineticSq, clusterKineticSq, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hpt i

/-- **The normalised-configuration identity.**  The mass-weighted squared norm of the velocity of
the normalised configuration `s = I_k^{-1/2}q` is, times `I_k`, the relative kinetic energy minus
`(İ_k)²/(4 I_k)`. -/
theorem clusterInertia_mul_clusterKineticSq_deriv_shape {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {t : ℝ} (hJpos : 0 < clusterInertia m k (x t))
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s) :
    clusterInertia m k (x t)
        * clusterKineticSq m k (deriv (fun s : ℝ => clusterShape m k (x s)) t)
      = clusterRelKinetic m k (deriv x t)
        - (deriv (fun s : ℝ => clusterInertia m k (x s)) t) ^ 2
            / (4 * clusterInertia m k (x t)) := by
  set J := clusterInertia m k (x t) with hJdef
  set J' := deriv (fun s : ℝ => clusterInertia m k (x s)) t with hJ'def
  set r := Real.sqrt J with hrdef
  have hrpos : 0 < r := by rw [hrdef, hJdef]; exact Real.sqrt_pos.mpr hJpos
  have hsqr : r ^ 2 = J := by rw [hrdef, hJdef]; exact Real.sq_sqrt hJpos.le
  have hder : deriv (fun s : ℝ => clusterShape m k (x s)) t
      = r⁻¹ • cmRel m k (deriv x t) + (-(J' / (2 * r ^ 3))) • cmRel m k (x t) := by
    exact (hasDerivAt_clusterShape_curve hJpos hx).deriv
  have hKx : clusterKineticSq m k (cmRel m k (x t)) = J := by
    show (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖ ^ 2) = J
    rw [hJdef]
    exact sum_cmRel_sq m k (x t)
  have hcross : ∑ i ∈ k, m i * ⟪(cmRel m k (deriv x t)) i, (cmRel m k (x t)) i⟫_ℝ = J' / 2 := by
    rw [hJ'def, deriv_clusterInertia_curve (m := m) (k := k) hx,
      ← massInner_cmRel_sum m k (deriv x t) (x t), massInner_comm]
    ring
  rw [hder, clusterKineticSq_smul_add,
    show clusterKineticSq m k (cmRel m k (deriv x t)) = clusterRelKinetic m k (deriv x t) from rfl,
    hcross, hKx, ← hsqr]
  field_simp
  ring

end Submission.NBody
