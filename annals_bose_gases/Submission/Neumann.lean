import Mathlib
import ChallengeDeps
import Submission.KineticLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# R1 — the Neumann box-energy family (first file: foundations)

Neumann bracketing is the classical tool for the *lower* leg of the
thermodynamic limit (Layer 2 / Ingredient 1 of `Submission.Excess`): the
Dirichlet ground-state energy of a box is bounded below by sums of *Neumann*
ground-state energies of cells, and the Neumann energies satisfy an exact
volume subadditivity (product states glue without a Dirichlet wall).

This file lays the foundations:

  * `CNeu N L` — the Neumann trial space: functions smooth on the whole
    configuration space (no vanishing at the boundary of `box N L`), nonzero,
    with positive `L²`-norm on the box;
  * `kinNeu N L Φ` — the *gradient* kinetic form `∫_{box} Σ_{i,k}(∂_{ik}Φ)²`
    (this is the honest Neumann kinetic energy; for functions that vanish on
    the boundary it agrees with the operator form `∫ Φ·(−ΔΦ)` by integration by
    parts, cf. `kinNeu_emb_eq` below);
  * `intNeu` — the pair-interaction form (same integrand as
    `BoxEnergy.interactionEnergy`);
  * `eNeu N L v` — the Neumann ground-state energy density quotient;
  * `embNeu` — every Dirichlet state is a Neumann state;
  * **`eNeu_le_boxEnergy`** — Dirichlet ≥ Neumann on the same box
    (`boxEnergy N L v ≥ eNeu N L v`), the fundamental bracketing inequality.

The `sq_pos` field keeps zero-norm states out of the infimum.  The global
smoothness (rather than `ContDiffOn` on the box) makes directional derivatives
and all box integrals immediately well-defined.

Note: `kcDir N i k` (from `KineticChild`) is the unit vector of particle `i`
in coordinate direction `k`; `fderiv ℝ Φ x (kcDir N i k)` is the directional
derivative `∂_{ik}Φ(x)`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- Neumann trial states in the box of side `L`: smooth functions on the whole
configuration space (in particular no vanishing at the boundary of the box),
nonzero, with positive box norm. -/
structure CNeu (N : ℕ) (L : ℝ) where
  toFun : X N → ℝ
  /-- Smooth on the whole space. -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- Not the zero function. -/
  nezero : toFun ≠ 0
  /-- Positive `L²`-norm on the box. -/
  sq_pos : 0 < ∫ x in box N L, (toFun x) ^ 2

instance (N : ℕ) (L : ℝ) : CoeFun (CNeu N L) (fun _ ↦ X N → ℝ) where
  coe Φ := Φ.toFun

/-- Neumann kinetic energy of a state (the gradient form on the box). -/
noncomputable def kinNeu (N : ℕ) (L : ℝ) (Φ : CNeu N L) : ℝ :=
  ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
    (fderiv ℝ (Φ : X N → ℝ) x (kcDir N i k)) ^ 2

/-- Neumann interaction energy of a state (same integrand as the Dirichlet
`interactionEnergy`). -/
noncomputable def intNeu (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Φ : CNeu N L) : ℝ :=
  ∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2 *
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), v (x p.1 - x p.2))

/-- The Neumann ground-state energy of `N` particles in a box of side `L`. -/
noncomputable def eNeu (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  ⨅ Φ : CNeu N L, (kinNeu N L Φ + intNeu N L v Φ) /
    (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2)

/-- Embedding of Dirichlet trial states into the Neumann trial space. -/
noncomputable def embNeu {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) : CNeu N L where
  toFun := Ψ
  contDiff := psi_contDiff Ψ
  nezero := Ψ.nezero
  sq_pos := by
    have hp := boxInt_sq_pos hL Ψ
    have heq := boxInt_sq_eq Ψ
    rwa [heq] at hp

/-- The Neumann kinetic energy is nonnegative. -/
lemma kinNeu_nonneg {N : ℕ} {L : ℝ} (Φ : CNeu N L) : 0 ≤ kinNeu N L Φ := by
  unfold kinNeu
  apply integral_nonneg
  intro x
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun k hk => sq_nonneg _))

/-- The Neumann interaction energy is nonnegative for `v ≥ 0`. -/
lemma intNeu_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (Φ : CNeu N L) :
    0 ≤ intNeu N L v Φ := by
  unfold intNeu
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (s := (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)))
      (f := fun p : Fin N × Fin N => v (x p.1 - x p.2)) (fun p hp => hv (x p.1 - x p.2)))

/-- The Neumann Rayleigh quotient of every admissible state is nonnegative
(for `v ≥ 0`). -/
lemma eNeu_quot_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (Φ : CNeu N L) :
    0 ≤ (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2) := by
  have hnum : 0 ≤ kinNeu N L Φ + intNeu N L v Φ := by
    exact add_nonneg (kinNeu_nonneg Φ) (intNeu_nonneg hv Φ)
  have hden : 0 < ∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2 := Φ.sq_pos
  exact div_nonneg hnum (le_of_lt hden)

/-- The Neumann quotient values are bounded below by `0` (for `v ≥ 0`). -/
lemma eNeu_quot_bddBelow {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) :
    BddBelow (Set.range (fun Φ : CNeu N L =>
      (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2))) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨Φ, rfl⟩
  exact eNeu_quot_nonneg hv Φ

/-! ## Integration by parts machinery for the kinetic-energy identity

The Neumann kinetic form `∫_{box} Σ (∂Ψ)²` equals the operator form
`Σ ∫ Ψ·(−Δ[i]Ψ)` for every Dirichlet state `Ψ`: the state (and all of its
derivatives) vanish in a neighbourhood of the boundary, so every box integral
below is really a whole-space integral, and on the whole space integration by
parts turns `∫ Ψ·(−D²_uΨ)` into `∫ (D_uΨ)²`. -/

/-- The directional derivative of a Dirichlet state vanishes outside the box. -/
lemma dirDeriv_zero_of_not_mem_box {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) {x : X N}
    (hx : x ∉ box N L) (u : X N) : fderiv ℝ (Ψ : X N → ℝ) x u = 0 := by
  have hx' : x ∉ tsupport (Ψ : X N → ℝ) := by
    intro h
    have hb : x ∈ box N L := interior_subset (Ψ.support h)
    exact hx hb
  have heq : (Ψ : X N → ℝ) =ᶠ[𝓝 x] (fun _ : X N => (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq).mp hx'
  have hfd : fderiv ℝ (Ψ : X N → ℝ) x = 0 := by
    calc
      fderiv ℝ (Ψ : X N → ℝ) x = fderiv ℝ (fun _ : X N => (0 : ℝ)) x := heq.fderiv_eq
      _ = 0 := by simp
  simp [hfd]

/-- The box integral of a squared directional derivative equals the whole-space
integral (the derivative vanishes off the box). -/
lemma fderivSq_box_eq_ws {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (u : X N) :
    (∫ x in box N L, ((fderiv ℝ (Ψ : X N → ℝ) x u) ^ 2)) = ∫ x, ((fderiv ℝ (Ψ : X N → ℝ) x u) ^ 2) := by
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (μ := volume) (by
    intro x hx
    have hz := dirDeriv_zero_of_not_mem_box Ψ hx u
    simp [hz])

/-- A squared directional derivative of a Dirichlet state is integrable on the box. -/
lemma integrableOn_fderivSq {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (u : X N) :
    IntegrableOn (fun x : X N => ((fderiv ℝ (Ψ : X N → ℝ) x u) ^ 2)) (box N L) volume := by
  let g : X N → ℝ := fun x => fderiv ℝ (Ψ : X N → ℝ) x u
  have hg_cd : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact firstDir_contDiff (psi_contDiff Ψ) u
  have hg_c : Continuous g := hg_cd.continuous
  have hts : tsupport g ⊆ tsupport (Ψ : X N → ℝ) := by
    simpa [g] using (tsupport_firstDir_subset (f := (Ψ : X N → ℝ)) u)
  have hcs_g : HasCompactSupport g := by
    exact IsCompact.of_isClosed_subset (hasCompactSupport_Ψ hL Ψ) (isClosed_tsupport g) hts
  have hcont : Continuous (fun x => (g x) ^ 2) := hg_c.pow 2
  have hsub : Function.support (fun x : X N => (g x) ^ 2) ⊆ tsupport g := by
    intro x hx
    have hgx : g x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact subset_tsupport g hgx
  have hcs : HasCompactSupport (fun x => (g x) ^ 2) := by
    refine IsCompact.of_isClosed_subset hcs_g (isClosed_tsupport (fun x => (g x) ^ 2)) ?_
    exact closure_minimal hsub (isClosed_tsupport g)
  have hint : Integrable (fun x => (g x) ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport hcont hcs
  -- integrable on the whole space implies integrable on any set
  change IntegrableOn (fun x : X N => (g x) ^ 2) (box N L) volume
  exact hint.integrableOn

/-- Whole-space per-particle identity in terms of the `kcDir` coordinate directions:
`∫ Ψ·(−Δ[i]Ψ) = ∑ₖ ∫ (∂_{ik}Ψ)²`. -/
lemma kineticWhole_dir_eq {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (i : Fin N) :
    (∫ x : X N, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) =
      ∑ k : Fin 3, ∫ x : X N, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) := by
  have hbr := kc_partialLaplacian_eq i (f := (Ψ : X N → ℝ)) (psi_contDiff_two Ψ)
  have hpoint : (fun x : X N =>
      (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
      = fun x : X N => ∑ k : Fin 3,
          (Ψ : X N → ℝ) x * (-(fderiv ℝ
            (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (kcDir N i k)) x)
              (kcDir N i k)) := by
    funext x
    have hbrx : partialLaplacian i (Ψ : X N → ℝ) x =
        ∑ k : Fin 3, (fderiv ℝ (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z
          (kcDir N i k)) x) (kcDir N i k) := by
      simpa using congrFun hbr x
    rw [hbrx]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hpoint]
  rw [integral_finsetSum (s := Finset.univ) (μ := volume)
    (f := fun (k : Fin 3) (x : X N) => (Ψ : X N → ℝ) x * (-(fderiv ℝ
      (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (kcDir N i k)) x)
        (kcDir N i k)))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hb2 := kc_ws_dir2_eq (f := (Ψ : X N → ℝ)) (u := kcDir N i k)
      (psi_contDiff Ψ) (hasCompactSupport_Ψ hL Ψ)
    exact hb2
  · intro k hk
    have hS_cd : ContDiff ℝ ∞ (fun x : X N => (fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (kcDir N i k)) x)
          (kcDir N i k)) :=
      secondDir_contDiff_u (psi_contDiff Ψ) (kcDir N i k)
    have hcont : Continuous (fun x : X N => (Ψ : X N → ℝ) x * (-(fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (kcDir N i k)) x)
          (kcDir N i k))) :=
      (psi_contDiff Ψ).continuous.mul hS_cd.continuous.neg
    have hcs : HasCompactSupport (fun x : X N => (Ψ : X N → ℝ) x * (-(fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (kcDir N i k)) x)
          (kcDir N i k))) :=
      (hasCompactSupport_Ψ hL Ψ).mul_right
    exact Continuous.integrable_of_hasCompactSupport hcont hcs

/-- Per-particle box identity: `∫_{box} Ψ·(−Δ[i]Ψ) = ∑ₖ ∫_{box} (∂_{ik}Ψ)²`. -/
lemma boxDir_kinetic_eq_sum {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (i : Fin N) :
    (∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) =
      ∑ k : Fin 3, ∫ x in box N L, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) := by
  calc
    (∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
        = ∫ x : X N, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)) := by
          exact setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (μ := volume) (by
            intro x hx
            have hz : (Ψ : X N → ℝ) x = 0 := psi_eq_zero_of_not_mem_interior Ψ (by
              intro hxi; exact hx (interior_subset hxi))
            simp [hz])
    _ = ∑ k : Fin 3, ∫ x : X N, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) :=
          kineticWhole_dir_eq hL Ψ i
    _ = ∑ k : Fin 3, ∫ x in box N L, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (fderivSq_box_eq_ws hL Ψ (kcDir N i k)).symm

/-- The Neumann kinetic energy of an embedded state expands to the double sum of
the box integrals of the squared directional derivatives. -/
lemma kinNeu_emb_expand {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    kinNeu N L (embNeu hL Ψ) =
      ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N L, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) := by
  unfold kinNeu
  have hterm : ∀ i : Fin N, ∀ k : Fin 3,
      IntegrableOn (fun x : X N => (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2)
        (box N L) volume := by
    intro i k
    simpa [embNeu] using integrableOn_fderivSq hL Ψ (kcDir N i k)
  calc
    (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2)
        = ∑ i : Fin N, ∫ x in box N L, (∑ k : Fin 3,
            (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2) := by
          rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
            (f := fun (i : Fin N) x => ∑ k : Fin 3,
              (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2)]
          · intro i hi
            -- per-i integrability: finite sum of box-integrable terms
            simpa [embNeu] using (integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
              (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) (by
                intro k hk
                exact integrableOn_fderivSq hL Ψ (kcDir N i k)))
    _ = ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N L,
          (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
            (f := fun (k : Fin 3) x => (fderiv ℝ ((embNeu hL Ψ : CNeu N L) : X N → ℝ) x (kcDir N i k)) ^ 2)]
          · intro k hk
            exact hterm i k
    _ = ∑ i : Fin N, ∑ k : Fin 3, ∫ x in box N L, ((fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) := by
          simp [embNeu]

/-- For a Dirichlet state, the gradient-form kinetic energy on the box equals
the operator-form kinetic energy (integration by parts; the state vanishes in
a neighbourhood of the boundary of the box). -/
lemma kinNeu_emb_eq {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    kinNeu N L (embNeu hL Ψ) = kineticEnergy N L Ψ := by
  rw [kinNeu_emb_expand hL Ψ]
  unfold kineticEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact (boxDir_kinetic_eq_sum hL Ψ i).symm

/-- For a Dirichlet state, the Neumann interaction energy equals the Dirichlet
one (same integrand). -/
lemma intNeu_emb_eq {N : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (hL : 0 < L) (Ψ : CInfty0Box N L) :
    intNeu N L v (embNeu hL Ψ) = interactionEnergy N L v Ψ := by
  unfold intNeu interactionEnergy embNeu
  rfl

/-- The Dirichlet quotient of an admissible state equals the Neumann quotient
of its embedding. -/
lemma quotient_eq_emb {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : MemLp v 1)
    (Ψ : CInfty0Box N L) :
    ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 =
      (kinNeu N L (embNeu hL Ψ) + intNeu N L v (embNeu hL Ψ)) /
        (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2) := by
  have hdec := energy_decomposition_admissible N hL hv Ψ
  have hkin := kinNeu_emb_eq hL Ψ
  have hint := intNeu_emb_eq v hL Ψ
  have hnorm : ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 = (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2) := by
    have hpos : 0 ≤ ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L] := le_of_lt (boxInt_sq_pos hL Ψ)
    calc
      ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 = (√ ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L]) ^ 2 := rfl
      _ = ⟪(Ψ : X N → ℝ), (Ψ : X N → ℝ)⟫_[N,L] := Real.sq_sqrt hpos
      _ = ∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2 := boxInt_sq_eq Ψ
  calc
    ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2
        = (∫ x in box N L, (Ψ : X N → ℝ) x * 𝓗 N v (Ψ : X N → ℝ) x) / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := rfl
    _ = (kineticEnergy N L Ψ + interactionEnergy N L v Ψ) / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := by
          rw [hdec]
    _ = (kineticEnergy N L Ψ + interactionEnergy N L v Ψ) / (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2) := by
          rw [hnorm]
    _ = (kinNeu N L (embNeu hL Ψ) + intNeu N L v (embNeu hL Ψ)) /
          (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2) := by
          rw [hkin, hint]

/-- **Dirichlet ≥ Neumann on the same box** (the fundamental bracketing
inequality): every Dirichlet quotient is the Neumann quotient of the embedded
state, hence the infimum over the larger Neumann space is no larger. -/
theorem eNeu_le_boxEnergy {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) : eNeu N L v ≤ boxEnergy N L v := by
  let qN : CNeu N L → ℝ := fun Φ =>
    (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2)
  let qD : CInfty0Box N L → ℝ := fun Ψ =>
    ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2
  have hbdd : BddBelow (Set.range qN) := by
    simpa [qN] using eNeu_quot_bddBelow (N := N) (L := L) (v := v) hv
  have hmono : ∀ Ψ : CInfty0Box N L, ∃ Φ : CNeu N L, qN Φ ≤ qD Ψ := by
    intro Ψ
    refine ⟨embNeu hL Ψ, ?_⟩
    dsimp [qN, qD]
    simpa [embNeu] using le_of_eq (quotient_eq_emb hL hv1 Ψ).symm
  have hcineq : (⨅ Φ : CNeu N L, qN Φ) ≤ ⨅ Ψ : CInfty0Box N L, qD Ψ := by
    haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hL
    exact le_ciInf fun Ψ => by
      obtain ⟨Φ, hΦ⟩ := hmono Ψ
      exact (ciInf_le hbdd Φ).trans hΦ
  unfold eNeu boxEnergy
  simpa [qN, qD] using hcineq

end BoseGases

end Submission
