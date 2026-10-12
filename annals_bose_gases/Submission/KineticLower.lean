import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.KineticChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 1 — a positive kinetic lower bound on the ground-state energy.

The corpus so far only has `boxEnergy_nonneg` (E ≥ 0).  This module proves the
first quantitative lower bound: for `N` bosons in a Dirichlet box of side `L`
with a nonnegative `L¹` potential, the ground-state energy is at least the
kinetic energy of `N` free bosons in the box,

    E(N,L) ≥ c · N / L²        (c := 6; the sharp constant would be 3π²).

Proof route (all ingredients are in the corpus or elementary):

1. PER-PARTICLE KINETIC IDENTITY.  For a smooth function `f : X N → ℝ` with
   compact support and any direction `u`, integration by parts gives
   `∫ f·(−D²_u f) = ∫ (D_u f)²` (the corpus proves the ≥ 0 half as
   `BoxEnergy.wholeSpace_dir2_nonneg`; extract the *equality* from its proof:
   the calc block around `hgoal` proves exactly
       ∫ x, f x * (-(fderiv ℝ (fun z => fderiv ℝ f z u) x u)) = ∫ x, (fderiv ℝ f x u) ^ 2
   using `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).  With
   `Bridge.partialLaplacian_eq_sum_secondDir`, `Δ[i] f = Σ_k D²_{coordDir N i k} f`,
   so for `Ψ : CInfty0Box N L` (whose box integral equals its whole-space
   integral, cf. `setIntegral_eq_integral_of_forall_compl_eq_zero` + the
   vanishing outside the box interior),
       ∫_{box} Ψ·(−Δ[i]Ψ) = Σ_k ∫ (∂_{ik}Ψ)²        (per-particle, whole space).

2. ONE-DIMENSIONAL POINCARÉ (crude constant).  If `f : ℝ → ℝ` is C¹ and
   vanishes for `x ≤ 0` and `x ≥ L`, then, by `f(x) = ∫₀ˣ f′` and
   Cauchy–Schwarz,
       ‖f‖² ≤ (L²/2)‖f′‖²   i.e.  (2/L²)·∫ f² ≤ ∫ (f′)² .
   (Integrals over ℝ; `intervalIntegral` / `MeasureTheory` FTC lemmas:
   `intervalIntegral.integral_deriv_eq_sub`, `intervalIntegral.integral_of_le`,
   Fubini for the multi-variable lift.)

3. LIFT TO SEVERAL VARIABLES.  For `Ψ : X N → ℝ` (compactly supported, smooth,
   vanishing when any coordinate is outside `(0,L)`), fixing all coordinates
   but `x_{i,k}` and applying step 2 in that single real variable, then
   integrating over the remaining coordinates (Fubini/Tonelli; the corpus has
   slice/Fubini machinery in `Submission/Potential.lean`,
   `Submission/SubaddVol.lean`, `Submission/Superadd.lean`):
       ∫ (∂_{ik}Ψ)² ≥ (2/L²)·∫ Ψ²     (whole-space integrals)
   hence for each particle `i`, with `Δ[i]` over the three coordinates,
       ∫_{box} Ψ·(−Δ[i]Ψ) ≥ (6/L²)·∫_{box} Ψ² .

4. ASSEMBLY.  Under `0 ≤ v` the interaction energy is nonnegative and
   (`Potential.energy_decomposition_admissible`) the numerator splits:
       ⟪Ψ, 𝓗 N v Ψ⟫_[N,L] = kineticEnergy N L Ψ + interactionEnergy N L v Ψ
   with `kineticEnergy = Σ_i ∫_{box} Ψ·(−Δ[i]Ψ) ≥ (6N/L²)·⟪Ψ,Ψ⟫_[N,L]`, so every
   admissible quotient is ≥ `6N/L²`, hence `boxEnergy N L v ≥ 6N/L²` (infimum
   of a family all ≥ the bound, via the `le_csInf`-style lemma the corpus
   already uses, or `ciInf` lemmas).

This file must be completed with a full proof.  The theorem to prove is
`boxEnergy_kinetic_lower` below.  You may add any helper lemmas/definitions you
need.  Keep everything inside `namespace Submission.BoseGases`.  Do not add
imports beyond those present.  Only the permitted axioms may appear.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases
open Filter Metric MeasureTheory Laplacian
open scoped NNReal ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- ⟪Ψ,Ψ⟫ equals the box integral of Ψ². -/
lemma boxInt_sq_eq {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) :
    ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L] = ∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2 := by
  apply setIntegral_congr_fun (box_measurable N L)
  intro x hx
  ring

/-- The box integral of the square of an admissible state is positive. -/
lemma boxInt_sq_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    0 < ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L] := by
  rw [boxInt_sq_eq]
  let f : X N → ℝ := fun x => ((Ψ : X N → ℝ) x) ^ 2
  have hnonneg : 0 ≤ᵐ[volume.restrict (box N L)] f := ae_of_all _ (fun x => sq_nonneg _)
  have hcontf : Continuous f := by
    dsimp [f]
    exact (psi_contDiff Ψ).continuous.pow 2
  have hfi : IntegrableOn f (box N L) volume := by
    dsimp [f]
    rcases exists_bound_psi_sq hL Ψ with ⟨M, hM0, hM⟩
    have hb : ∀ᵐ (x : X N) ∂(volume.restrict (box N L)), ‖((Ψ : X N → ℝ) x) ^ 2‖ ≤ M :=
      ae_of_all _ (fun x => by
        rw [show ‖((Ψ : X N → ℝ) x) ^ 2‖ = ((Ψ : X N → ℝ) x) ^ 2 by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((Ψ : X N → ℝ) x))]]
        exact hM x)
    have hconst : Integrable (fun _ : X N => M) (volume.restrict (box N L)) :=
      (integrableOn_const (s := box N L) (C := M)
        (hs := ne_of_lt (IsCompact.measure_lt_top (box_compact hL)))).integrable
    exact Integrable.mono' hconst hcontf.aestronglyMeasurable hb
  have hne : ∃ x0 : X N, (Ψ : X N → ℝ) x0 ≠ 0 := by
    by_contra h
    apply Ψ.nezero
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  rcases hne with ⟨x0, hx0⟩
  let S : Set (X N) := {x | (Ψ : X N → ℝ) x ≠ 0}
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_ne.preimage (psi_contDiff Ψ).continuous
  have hx0S : x0 ∈ S := hx0
  rcases (Metric.isOpen_iff.mp hSopen x0 hx0S) with ⟨ε, hε, hball⟩
  have hμball : 0 < (volume : Measure (X N)) (Metric.ball x0 ε) := Metric.measure_ball_pos volume x0 hε
  have hsub : Metric.ball x0 ε ⊆ S ∩ box N L := by
    intro y hy
    constructor
    · exact hball hy
    · have hyS : y ∈ S := hball hy
      have hysupp : y ∈ Function.support (Ψ : X N → ℝ) := by exact hyS
      have hyt : y ∈ tsupport (Ψ : X N → ℝ) := subset_tsupport (Ψ : X N → ℝ) hysupp
      exact interior_subset (Ψ.support hyt)
  have hSbox : S ∩ box N L ⊆ Function.support f ∩ box N L := by
    intro y hy
    constructor
    · dsimp [f]; exact pow_ne_zero 2 hy.1
    · exact hy.2
  have hpos : 0 < (volume : Measure (X N)) (Function.support f ∩ box N L) := by
    exact lt_of_lt_of_le hμball (measure_mono (hsub.trans hSbox))
  have hres := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume) (s := box N L) hnonneg hfi).2 hpos
  simpa [f, pow_two] using hres

/-- State-wise kinetic lower bound on the Rayleigh quotient. -/
lemma kinetic_quot_bound {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (Ψ : CInfty0Box N L) :
    (6 : ℝ) * (N : ℝ) / L ^ 2 ≤
      ⟪(Ψ : X N → ℝ), _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] /
        ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := by
  let c : ℝ := (6 : ℝ) * (N : ℝ) / L ^ 2
  let a : ℝ := ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L]
  have ha0 : 0 ≤ a := by
    unfold a
    exact integral_nonneg (fun x => mul_self_nonneg _)
  have hapos : 0 < a := boxInt_sq_pos hL Ψ
  have hkin : c * a ≤ kineticEnergy N L Ψ := by
    have hsum : (∑ i : Fin N, (6 / L ^ 2) * a) = c * a := by
      unfold c
      rw [Finset.sum_const]
      rw [Finset.card_fin]
      simp [nsmul_eq_mul]
      ring
    calc
      c * a = ∑ i : Fin N, (6 / L ^ 2) * a := by rw [← hsum]
      _ ≤ ∑ i : Fin N, (∫ x in box N L, (Ψ : X N → ℝ) x * (-(Δ[i] (Ψ : X N → ℝ) x))) := by
        exact Finset.sum_le_sum (fun i hi => boxInt_kinetic_term_lower hL Ψ i)
      _ = kineticEnergy N L Ψ := by
        unfold kineticEnergy
        rfl
  have hnum : (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) =
      kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
    exact energy_decomposition_admissible N hL hv1 Ψ
  have hia : 0 ≤ interactionEnergy N L v Ψ := interactionEnergy_nonneg hv Ψ
  have hca_num : c * a ≤
      (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) := by
    rw [hnum]
    exact le_trans hkin (le_add_of_nonneg_right hia)
  have hden : ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 = a := by
    unfold a
    rw [Real.sq_sqrt ha0]
  have hc : c ≤
      (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) / a := by
    exact (le_div_iff₀ hapos).2 hca_num
  calc
    (6 : ℝ) * (N : ℝ) / L ^ 2 = c := rfl
    _ ≤ (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := by simpa [hden] using hc
    _ = ⟪(Ψ : X N → ℝ), _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] /
        ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := rfl

/-- The ground-state energy of `N` bosons with a nonnegative `L¹` potential in
a Dirichlet box of side `L` is at least the free kinetic lower bound:
`E(N,L) ≥ 6N/L²`. -/
lemma boxEnergy_kinetic_lower {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) :
    (6 : ℝ) * (N : ℝ) / L ^ 2 ≤ boxEnergy N L v := by
  haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hL
  have hquot : ∀ Ψ : CInfty0Box N L,
      (6 : ℝ) * (N : ℝ) / L ^ 2 ≤
        ⟪(Ψ : X N → ℝ), _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] /
          ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := by
    intro Ψ
    exact kinetic_quot_bound hL hv hv1 Ψ
  unfold boxEnergy
  exact le_ciInf hquot

end BoseGases

end Submission
