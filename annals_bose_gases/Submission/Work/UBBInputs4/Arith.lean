import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs4.ExtClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs4.Arith` — the Route-H arithmetic at the extended class

Round 2 (`Submission/Work/UBBInputs2/`) ran FS's Route H at the Dirichlet class
`CInfty0Box`.  This file re-runs the *quantitative* part of that chain at the extended
(Neumann) class of `Work.UBBInputs4.ExtClass`, so that FS §7's localised state — which
does not live in `CInfty0Box` — is an admissible state.

The chain is

    SpectralInputNeu  --BoxShapeNeu_of_spectralNeu (the dichotomy)-->  UBBNeu
    UBBNeu  --UBB_of_UBBNeu (eNeu ≤ boxEnergy)-->  UBB  --(delivered)-->  hpres

with `SpectralInputNeu` the per-state statement "a low state has shifted energy density
at least `Λ`", in exactly the shape of `Work.UBB.SpectralInputH` but with `RaylNeu` in
place of `Rayl` and `eNeu` in place of `boxEnergy`.

The one structural input is `Submission.BoseGases.eNeu_le_boxEnergy` (Dirichlet ≥ Neumann
on the same box, proved in the corpus from `quotient_eq_emb`): the Neumann infimum is over
the *larger* class, so a lower bound for it gives FS's box theorem for the Dirichlet class
— exactly the direction `theorem_1_2` needs (FS's own box Hamiltonian is the Neumann one).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The box-level statements at the extended class -/

/-- **The box shape at the Neumann class**: the uniform dilute box bound with `boxEnergy`
replaced by the Neumann energy `eNeu`. -/
def BoxShapeNeu (v : ℝ³ → ℝ) (A C ε₀ η₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * A ^ 3 ≤ ε₀ →
    lhyRhs A C (1 / 2 + η₀) (dens N L) ≤ eNeu N L v / L ^ 3

/-- **`UBBNeu`**: the Neumann analogue of `Work.UBB.UBB`.  By
`UBB_of_UBBNeu` it *implies* the delivered `UBB` (which is the Dirichlet statement
consumed by `Submission.UBBtoGc`). -/
def UBBNeu (v : ℝ³ → ℝ) (η₀ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ BoxShapeNeu v (a v) C ε₀ η₀

/-- **The per-state spectral input at the extended class** (FS `eq:ToProve`): a *low*
state of the extended class has shifted energy density at least `Λ`.  This is
`Work.UBB.SpectralInputH` with `RaylNeu` in place of `Rayl`. -/
def SpectralInputNeu (v : ℝ³ → ℝ) (J ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CNeu N L,
        RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
            ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L)
          ≤ RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2

/-! ## 2. The dictionary between the two forms of the low-state condition -/

/-- **FS `eq:aprioriPsi` in its two equivalent forms at the extended class**: the
`H_Λ`-form `LowStateNeu` (unnormalised, with the `L³`-multiple) and the density form. -/
theorem lowStateNeu_iff_density {v : ℝ³ → ℝ} {N : ℕ} {L J : ℝ} (hL : 0 < L)
    (Φ : CNeu N L) :
    LowStateNeu v N L J Φ ↔
      RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
        ≤ Theta (a v) J (dens N L) := by
  have h3 : (0 : ℝ) < L ^ 3 := by positivity
  set b : ℝ := 8 * π * (a v) * (dens N L) ^ 2 with hb
  have hlow : LowStateNeu v N L J Φ ↔
      RaylNeu N L v Φ - b * L ^ 3 ≤ Theta (a v) J (dens N L) * L ^ 3 := by
    rw [LowStateNeu, hb]
  rw [hlow]
  constructor
  · intro h
    have h1 : RaylNeu N L v Φ ≤ Theta (a v) J (dens N L) * L ^ 3 + b * L ^ 3 := by linarith
    have h2 : RaylNeu N L v Φ ≤ (Theta (a v) J (dens N L) + b) * L ^ 3 := by
      rw [add_mul]; exact h1
    have h3' : RaylNeu N L v Φ / L ^ 3 ≤ Theta (a v) J (dens N L) + b :=
      (div_le_iff₀ h3).mpr h2
    linarith
  · intro h
    have h1 : RaylNeu N L v Φ / L ^ 3 ≤ Theta (a v) J (dens N L) + b := by linarith
    have h2 : RaylNeu N L v Φ ≤ (Theta (a v) J (dens N L) + b) * L ^ 3 :=
      (div_le_iff₀ h3).mp h1
    have h3' : RaylNeu N L v Φ ≤ Theta (a v) J (dens N L) * L ^ 3 + b * L ^ 3 := by
      rwa [add_mul] at h2
    linarith

/-! ## 3. The dichotomy at the extended class -/

/-- `eNeu` is the infimum of `RaylNeu` over the extended class (definitional, recorded in
the form the arithmetic consumes). -/
theorem eNeu_eq_ciInf_RaylNeu {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} :
    eNeu N L v = ⨅ Φ : CNeu N L, RaylNeu N L v Φ := rfl

/-- **The dichotomy at the extended class**: if every *low* extended state satisfies the
shifted bound `Λ`, then so does the Neumann box energy density.  (FS's "if such a state
does not exist, then there is nothing to prove".) -/
theorem boxShapeNeu_of_spectralNeu {v : ℝ³ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v)
    {J C ε₀ η₀ : ℝ} (hC : 0 ≤ C) (hJ : lhyC ≤ J)
    (hspec : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CNeu N L,
        RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
            ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L)
          ≤ RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2) :
    BoxShapeNeu v (a v) C ε₀ η₀ := by
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hρ : 0 ≤ dens N L := dens_nonneg N hLpos.le
  haveI : Nonempty (CNeu N L) := nonempty_CNeu N hLpos
  have hbdd : BddBelow (Set.range (fun Φ : CNeu N L => RaylNeu N L v Φ)) :=
    ⟨0, fun y hy => by rcases hy with ⟨Φ, rfl⟩; exact RaylNeu_nonneg hv Φ⟩
  have hci : (⨅ Φ : CNeu N L, RaylNeu N L v Φ / L ^ 3) = eNeu N L v / L ^ 3 := by
    rw [eNeu_eq_ciInf_RaylNeu]
    exact (ciInf_div_const hbdd (pow_pos hLpos 3)).symm
  have hfor : ∀ Φ : CNeu N L,
      lhyRhs (a v) C (1 / 2 + η₀) (dens N L) ≤ RaylNeu N L v Φ / L ^ 3 := by
    intro Φ
    have hth := theta_ge_lambda (A := a v) (K := C) (J := J) (η₀ := η₀)
      (ρ := dens N L) ha hρ hC hJ
    rw [← lhyRhs_eq_shift]
    by_cases hlow : RaylNeu N L v Φ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
        ≤ Theta (a v) J (dens N L)
    · have := hspec L hL N hN Φ hlow
      linarith
    · push_neg at hlow
      linarith
  calc lhyRhs (a v) C (1 / 2 + η₀) (dens N L)
      ≤ ⨅ Φ : CNeu N L, RaylNeu N L v Φ / L ^ 3 := le_ciInf hfor
    _ = eNeu N L v / L ^ 3 := hci

/-- **The primary assembly at the extended class**: `UBBNeu` from the per-state spectral
input alone. -/
theorem UBBNeu_of_spectralNeu {v : ℝ³ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) {J ε₀ η₀ : ℝ}
    (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J) (hspec : SpectralInputNeu v J ε₀ η₀) :
    UBBNeu v η₀ := by
  rcases hspec with ⟨C, hC, hspec⟩
  exact ⟨ε₀, hε₀, C, hC, boxShapeNeu_of_spectralNeu hv ha hC hJ hspec⟩

/-! ## 4. Back to the delivered Dirichlet statement -/

/-- **`UBBNeu` implies the delivered `UBB`**: the Dirichlet box energy dominates the
Neumann one on the same box (`Submission.BoseGases.eNeu_le_boxEnergy`, itself proved from
`quotient_eq_emb`), so a lower bound for the Neumann energy is a lower bound for the
Dirichlet one. -/
theorem UBB_of_UBBNeu {v : ℝ³ → ℝ} {η₀ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (h : UBBNeu v η₀) : UBB v η₀ := by
  rcases h with ⟨ε₀, hε₀, C, hC, hshape⟩
  refine ⟨ε₀, hε₀, C, hC, fun L hL N hN => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hle := eNeu_le_boxEnergy (N := N) (L := L) (v := v) hLpos hv hv1
  have hdiv : eNeu N L v / L ^ 3 ≤ boxEnergy N L v / L ^ 3 :=
    div_le_div_of_nonneg_right hle (by positivity)
  linarith [hshape L hL N hN]

/-- **The paper's `hpres` from `UBBNeu`** — through the delivered grand-canonical
interface `Work.UBB.Consumer.hpres_of_UBB`, so nothing downstream of `UBB` changes. -/
theorem hpres_of_UBBNeu {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {η₀ η K : ℝ} (hav : 0 < a v) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2)
    (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K) (h : UBBNeu v η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK (UBB_of_UBBNeu hv hv1 h)

/-- **The paper's `hpres` from `SpectralInputNeu`** — the single per-state statement. -/
theorem hpres_of_spectralNeu {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {J ε₀ η₀ η K : ℝ} (hav : 0 < a v) (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hspec : SpectralInputNeu v J ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBNeu hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBBNeu_of_spectralNeu hv hav.le hε₀ hJ hspec)

/-! ## 5. The window API -/

/-- The covariant window is monotone in the window function (given nonnegativity). -/
theorem windowNeu_mono {W W' : ℕ → ℝ → ℝ} {N : ℕ} {L : ℝ} {Φ : CNeu N L}
    (h : ∀ N L, W N L ≤ W' N L) (hww : WindowNeu W N L Φ) :
    WindowNeu W' N L Φ := by
  rw [WindowNeu] at hww ⊢
  have hsq := aboxSq_nonneg Φ
  calc cnPlus L (Φ : X N → ℝ) ≤ W N L * aboxSq N L Φ := hww
    _ ≤ W' N L * aboxSq N L Φ := mul_le_mul_of_nonneg_right (h N L) hsq

/-- The covariant window is invariant under scaling of the state. -/
theorem windowNeu_scale {W : ℕ → ℝ → ℝ} {N : ℕ} {L : ℝ} {Φ : CNeu N L}
    (h : WindowNeu W N L Φ) (c : ℝ) (hc : c ≠ 0) :
    WindowNeu W N L (neuScale Φ c hc) := by
  rw [WindowNeu] at h ⊢
  have hsq : aboxSq N L (neuScale Φ c hc) = c ^ 2 * aboxSq N L Φ := by
    rw [aboxSq_def, aboxSq_def, neuScale_coe]
    rw [show (∫ x in abox N L, (c * (Φ : X N → ℝ) x) ^ 2)
        = ∫ x in abox N L, c ^ 2 * ((Φ : X N → ℝ) x) ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [integral_const_mul]
  have hcn : cnPlus L ((neuScale Φ c hc : CNeu N L) : X N → ℝ)
      = c ^ 2 * cnPlus L (Φ : X N → ℝ) := by
    rw [cnPlus, cnPlus, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpt : ∀ x : X N,
        (aQ L i ((neuScale Φ c hc : CNeu N L) : X N → ℝ) x) ^ 2
          = c ^ 2 * (aQ L i (Φ : X N → ℝ) x) ^ 2 := by
      intro x
      have hlin : aP L i (fun x : X N => c * (Φ : X N → ℝ) x) x
          = c * aP L i (Φ : X N → ℝ) x := by
        unfold aP
        rw [show (∫ y in acube L, c * (Φ : X N → ℝ) (Function.update x i y))
            = c * ∫ y in acube L, (Φ : X N → ℝ) (Function.update x i y) by
          rw [integral_const_mul]]
        ring
      simp only [neuScale_coe, aQ, hlin]
      ring
    calc (∫ x in abox N L,
            (aQ L i ((neuScale Φ c hc : CNeu N L) : X N → ℝ) x) ^ 2)
        = ∫ x in abox N L, c ^ 2 * (aQ L i (Φ : X N → ℝ) x) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x
      _ = c ^ 2 * ∫ x in abox N L, (aQ L i (Φ : X N → ℝ) x) ^ 2 := by
          rw [integral_const_mul]
  rw [hcn, hsq]
  nlinarith [h, sq_nonneg c]

end Work.UBBInputs4
