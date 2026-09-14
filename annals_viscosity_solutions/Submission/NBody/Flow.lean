import ChallengeDeps
import Submission.NBody.Jacobi
import Mathlib

/-!
# The flow layer: the collision-free domain is open

First stone of the flow layer.  Newton's vector field `∇ₘ (U m)` is only meaningful (and only
locally Lipschitz) away from collisions, so the first structural fact is that the collision-free
configurations form an **open** subset of configuration space; on it the pairwise kernels are
continuous (indeed smooth), which is what the Picard–Lindelöf theory will consume.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open InnerProductSpace
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Collision-freeness is an open condition: `{x | WithoutCollisions x}` is open in
configuration space. -/
lemma isOpen_setOf_withoutCollisions : IsOpen {x : EN E N | WithoutCollisions x} := by
  have hset : {x : EN E N | WithoutCollisions x}
      = ⋂ p : {p : Fin N × Fin N // p.1 ≠ p.2}, {x : EN E N | x p.1.1 ≠ x p.1.2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun hx p => (r_ne_zero_iff x p.1.1 p.1.2).mp (hx p.1.1 p.1.2 p.2),
           fun hx i j hij => (r_ne_zero_iff x i j).mpr (hx ⟨(i, j), hij⟩)⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun p => ?_
  have hcont : Continuous (fun x : EN E N => x p.1.1 - x p.1.2) := by
    have h : (fun x : EN E N => x p.1.1 - x p.1.2) = ⇑(pairMap p.1.1 p.1.2) := by
      funext x
      rw [pairMap_apply]
    rw [h]
    exact (pairMap p.1.1 p.1.2).continuous
  have heq : {x : EN E N | x p.1.1 ≠ x p.1.2}
      = (fun x : EN E N => x p.1.1 - x p.1.2) ⁻¹' {0}ᶜ := by
    ext x
    simp [sub_eq_zero]
  rw [heq]
  exact isOpen_compl_singleton.preimage hcont

/-- The radial kernel `z ↦ ‖z‖⁻¹` is continuous away from the origin. -/
lemma continuousOn_inv_norm_of_ne :
    ContinuousOn (fun z : E => ‖z‖⁻¹) {z : E | z ≠ 0} :=
  continuous_norm.continuousOn.inv₀ (fun z hz => norm_ne_zero_iff.mpr hz)

/-- The pairwise kernel `x ↦ (r x i j)⁻¹` is continuous off the diagonal. -/
lemma continuousOn_inv_r (i j : Fin N) :
    ContinuousOn (fun y : EN E N => (r y i j)⁻¹) {x | x i ≠ x j} := by
  have h1 : ContinuousOn (fun y : EN E N => ‖pairMap i j y‖⁻¹) {x | x i ≠ x j} := by
    refine ContinuousOn.comp (g := fun z : E => ‖z‖⁻¹) continuousOn_inv_norm_of_ne (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_setOf_eq]
    refine sub_ne_zero.mpr ?_
    simpa [pairMap_apply] using hx
  refine h1.congr ?_
  intro x _
  show (r x i j)⁻¹ = ‖pairMap i j x‖⁻¹
  rw [r_eq_norm_sub, pairMap_apply]


/-- **The potential is smooth on the collision-free domain.**  Each pairwise term is `Cⁿ` off
its diagonal, and `U m` is the finite sum over the ordered pairs `i < j`. -/
lemma contDiffOn_U (m : Fin N → ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (U m) {x : EN E N | WithoutCollisions x} := by
  have hsum : ContDiffOn ℝ n (fun y : EN E N => ∑ p ∈ pairFinset N,
      m p.1 * m p.2 * (r y p.1 p.2)⁻¹) {x : EN E N | WithoutCollisions x} := by
    refine ContDiffOn.sum (s := pairFinset N) ?_
    intro p hp
    have hpne : p.1 ≠ p.2 := ne_of_lt (by simpa [pairFinset] using hp)
    have hker : ContDiffOn ℝ n (fun y : EN E N => (r y p.1 p.2)⁻¹)
        {x : EN E N | WithoutCollisions x} := by
      have hbase : ContDiffOn ℝ n (fun y : EN E N => ‖y p.1 - y p.2‖⁻¹)
          {x : EN E N | WithoutCollisions x} :=
        (contDiffOn_pair_inv_norm p.1 p.2).mono (fun x hx => by
          simp only [Set.mem_setOf_eq]
          exact (r_ne_zero_iff x p.1 p.2).mp (hx p.1 p.2 hpne))
      refine hbase.congr ?_
      intro x _
      rw [r_eq_norm_sub]
    simpa [smul_eq_mul] using ContDiffOn.const_smul (𝕜 := ℝ) (m p.1 * m p.2) hker
  refine hsum.congr ?_
  intro x _
  exact U_eq_pairFinset m x

/-- **The gradient field is continuous on the collision-free domain.**  The potential is `C¹`
there, so its Fréchet derivative is continuous, and the gradient is it transported by the
Riesz isometry. -/
lemma continuousOn_gradient_U (m : Fin N → ℝ) :
    ContinuousOn (fun x : EN E N => gradient (U m) x) {x : EN E N | WithoutCollisions x} := by
  have hs := isOpen_setOf_withoutCollisions (E := E) (N := N)
  have hU : ContDiffOn ℝ 1 (U m) {x : EN E N | WithoutCollisions x} := contDiffOn_U m
  have hf : ContinuousOn (fun x : EN E N => fderiv ℝ (U m) x) {x : EN E N | WithoutCollisions x} :=
    fun x hx => ((hU.contDiffAt (hs.mem_nhds hx)).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hcomp : ContinuousOn (fun x : EN E N => (toDual ℝ (EN E N)).symm (fderiv ℝ (U m) x))
      {x : EN E N | WithoutCollisions x} :=
    ((toDual ℝ (EN E N)).symm.continuous).comp_continuousOn hf
  refine hcomp.congr ?_
  intro x _
  rfl


/-- **The force field is `C¹` on the collision-free domain** — the regularity consumed by the
Picard–Lindelöf theorem to produce local solutions of Newton's equations. -/
lemma contDiffOn_gradient_U (m : Fin N → ℝ) :
    ContDiffOn ℝ 1 (fun x : EN E N => gradient (U m) x) {x : EN E N | WithoutCollisions x} := by
  have hs := isOpen_setOf_withoutCollisions (E := E) (N := N)
  have hU2 : ContDiffOn ℝ 2 (U m) {x : EN E N | WithoutCollisions x} := contDiffOn_U m
  have hfd : ContDiffOn ℝ 1 (fderivWithin ℝ (U m) {x : EN E N | WithoutCollisions x})
      {x : EN E N | WithoutCollisions x} :=
    hU2.fderivWithin hs.uniqueDiffOn (by norm_num)
  have hfd' : ContDiffOn ℝ 1 (fderiv ℝ (U m)) {x : EN E N | WithoutCollisions x} := by
    refine hfd.congr ?_
    intro x hx
    rw [fderivWithin_of_isOpen hs hx]
  have hcomp : ContDiffOn ℝ 1 (fun x : EN E N => (toDual ℝ (EN E N)).symm (fderiv ℝ (U m) x))
      {x : EN E N | WithoutCollisions x} :=
    ((toDual ℝ (EN E N)).symm.contDiff).comp_contDiffOn hfd'
  refine hcomp.congr ?_
  intro x _
  rfl


/-- The force field is `C¹` at a collision-free configuration. -/
lemma contDiffAt_gradient_U (m : Fin N → ℝ) (x₀ : EN E N) (hx₀ : WithoutCollisions x₀) :
    ContDiffAt ℝ 1 (fun x : EN E N => gradient (U m) x) x₀ :=
  (contDiffOn_gradient_U m).contDiffAt
    ((isOpen_setOf_withoutCollisions (E := E) (N := N)).mem_nhds hx₀)

end Submission.NBody
