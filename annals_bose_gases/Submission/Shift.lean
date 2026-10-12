import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.KineticChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Translation isometry of the gradient (kinetic) energy

The bracket argument localises a state into cells and then compares the
localised piece with the Neumann ground state of the *standard* box `[0,L]³`.
A piece supported in a translated box `w + box N L` must first be shifted back
to the standard box; this module proves that this shift is an isometry for the
gradient (kinetic) energy:

  * `fderiv_shift` — the derivative of the shifted function is the derivative
    of the original at the shifted point (translation has derivative `1`);
  * `gradSq_shift` — the whole-space gradient energy is invariant under
    translation (`∫ |∇(f∘(·+w))|² = ∫ |∇f|²`);
  * `support_shift` — shifting back a function supported in `w + box N L`
    yields a function supported in `box N L` (so the shifted piece is
    admissible on the standard box);
  * `kinBox_shift` — the box kinetic energy of the shifted function equals the
    gradient energy of the original over its (shifted) box — the isometry
    used to evaluate a piece's energy against `eNeu` on the standard box.

Throughout `w : X N` is a common shift applied to every particle coordinate
(every particle of a cell-piece is shifted by the same vector).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The common translation of every particle by the shift `w`. -/
noncomputable def shiftAll (N : ℕ) (w : X N) (x : X N) : X N :=
  x + w

/-- The translation is measure-preserving for the volume. -/
lemma measurePreserving_shiftAll (N : ℕ) (w : X N) :
    MeasurePreserving (shiftAll N w) volume volume := by
  unfold shiftAll
  simpa [add_comm] using (measurePreserving_add_left volume w)

/-- The derivative of a shifted function is the derivative at the shifted
point (translation has derivative the identity). -/
lemma fderiv_shiftAll {N : ℕ} (w : X N) {f : X N → ℝ} (hf : ContDiff ℝ 1 f)
    (x v : X N) :
    fderiv ℝ (fun z : X N => f (z + w)) x v = fderiv ℝ f (x + w) v := by
  let T : X N → X N := fun z => z + w
  have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ (X N)) x := by
    have hd : DifferentiableAt ℝ (fun z : X N => z + w) x :=
      differentiableAt_id.add (differentiableAt_const w)
    have hTf : fderiv ℝ (fun z : X N => z + w) x = ContinuousLinearMap.id ℝ (X N) := by
      simpa using (fderiv_id ℝ (X N))
    dsimp [T]
    simpa [hTf] using hd.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f (x + w)) (x + w) := by
    exact (hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (x + w)).hasFDerivAt
  have hcomp := hf'.comp x hT
  have hfderiv : fderiv ℝ (fun z : X N => f (z + w)) x = fderiv ℝ f (x + w) := by
    dsimp [T] at hcomp
    simpa [Function.comp_def] using hcomp.fderiv
  calc
    fderiv ℝ (fun z : X N => f (z + w)) x v = (fderiv ℝ f (x + w)) v := by rw [hfderiv]

/-- The whole-space gradient energy is invariant under translation. -/
lemma gradSq_shift {N : ℕ} (w : X N) {f : X N → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => f (z + w)) x (kcDir N i k)) ^ 2) =
      (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2) := by
  have hfderivcont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  let H : X N → ℝ := fun y => ∑ i : Fin N, ∑ k : Fin 3,
    (fderiv ℝ f y (kcDir N i k)) ^ 2
  have hHcont : Continuous H := by
    dsimp [H]
    -- each term continuous: (fun y => fderiv f y (kcDir N i k)) is continuous
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro k hk
    have hterm : Continuous (fun y : X N => fderiv ℝ f y (kcDir N i k)) := by
      have h1 : Continuous (fun L : X N →L[ℝ] ℝ => L (kcDir N i k)) := by fun_prop
      exact h1.comp hfderivcont
    exact hterm.pow 2
  have hpoint : (fun x : X N =>
      ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => f (z + w)) x (kcDir N i k)) ^ 2) =
      fun x : X N => H (x + w) := by
    funext x
    dsimp [H]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [fderiv_shiftAll (w := w) (hf := hf) x (kcDir N i k)]
  have hφ : AEMeasurable (shiftAll N w) := by
    exact (continuous_id.add continuous_const : Continuous (shiftAll N w)).aemeasurable
  have hHm : AEStronglyMeasurable H (Measure.map (shiftAll N w) volume) := by
    rw [(measurePreserving_shiftAll N w).map_eq]
    exact hHcont.aestronglyMeasurable
  calc
    (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => f (z + w)) x (kcDir N i k)) ^ 2)
        = ∫ x : X N, H (x + w) := by rw [hpoint]
    _ = ∫ y : X N, H y ∂(Measure.map (shiftAll N w) volume) := by
          unfold shiftAll
          exact (integral_map (φ := shiftAll N w) hφ (f := H) hHm).symm
    _ = ∫ y : X N, H y := by
          rw [(measurePreserving_shiftAll N w).map_eq]
    _ = ∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2 := by
          rfl

/-- The translated function of a function supported in the shifted box
`w + box N L` is supported in `box N L`. -/
lemma support_shiftAll {N : ℕ} {L : ℝ} (w : X N) {f : X N → ℝ}
    (hsup : Function.support f ⊆ {x : X N | x - w ∈ box N L}) :
    Function.support (fun z : X N => f (z + w)) ⊆ box N L := by
  intro z hz
  have hmem : z + w ∈ Function.support f := by
    exact hz
  have hsub := hsup hmem
  simpa using hsub

/-- **Box kinetic isometry**: for `f` supported in the shifted box
`w + box N L` with `w` a common particle shift, the box kinetic energy of the
shifted function `f ∘ (·+w)` on the standard box equals the whole-space
gradient energy of `f` (equivalently: its gradient energy over the shifted
box). -/
lemma kinBox_shift {N : ℕ} {L : ℝ} (w : X N) {f : X N → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hsup : Function.support f ⊆ {x : X N | x - w ∈ box N L}) :
    (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => f (z + w)) x (kcDir N i k)) ^ 2) =
      (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2) := by
  let u : X N → ℝ := fun z => f (z + w)
  let G : X N → ℝ := fun x => ∑ i : Fin N, ∑ k : Fin 3,
    (fderiv ℝ u x (kcDir N i k)) ^ 2
  have hsup_u : Function.support u ⊆ box N L := by
    dsimp [u]
    exact support_shiftAll (w := w) hsup
  have hGzero : ∀ x : X N, x ∉ box N L → G x = 0 := by
    intro x hx
    have hu0 : u =ᶠ[𝓝 x] 0 := by
      have hcmem : (box N L)ᶜ ∈ 𝓝 x := (box_closed L).isOpen_compl.mem_nhds hx
      filter_upwards [hcmem] with y hy
      by_contra hz
      exact hy (hsup_u hz)
    have hderiv : fderiv ℝ u x = 0 := by
      have hd0 : HasFDerivAt u (0 : X N →L[ℝ] ℝ) x := by
        exact (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hu0
      exact hd0.fderiv
    dsimp [G]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro k hk
    rw [hderiv]
    simp
  calc
    (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X N => f (z + w)) x (kcDir N i k)) ^ 2)
        = ∫ x in box N L, G x := by
          rfl
    _ = ∫ x : X N, G x :=
          setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (f := G) hGzero
    _ = ∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2 := by
          dsimp [G, u]
          exact gradSq_shift (w := w) (hf := hf)

end BoseGases

end Submission
