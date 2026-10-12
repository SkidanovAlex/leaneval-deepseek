import ChallengeDeps
import Submission.Work.UBB.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBB.Hamiltonian` — the primary assembly (Hamiltonian carrier)

`Defs.SpectralInputH` is FS's `eq:ToProve` stated directly for the canonical box
Rayleigh quotient `Rayl N L v Ψ` (`= ⟪Ψ,𝓗Ψ⟫/‖Ψ‖²`).  This module proves that it
*alone* (plus the arithmetic `J ≥ lhyC` and `0 ≤ a v`) implies
`BoxShape v (a v) C ε₀ η₀` and hence `UBB` — **with no word/kernel dictionary
and no `WordBridge`**.  This is the primary route of the area; the word-based
machinery (`SpectralInput`, `AprioriNPlus`, `BogoliubovLow`, `WordBridge`) is
the *decomposition* of the same input into the sibling chapters' language
(see `README.md` §5).

The only order-theoretic input is the standard infimum/division arithmetic over
`Rayl`, whose boundedness comes from `v ≥ 0`
(`Submission.BoxMonotone.rayleigh_quot_nonneg`).
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false
set_option linter.dupNamespace false

namespace Work.UBB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-- `Rayl` is the Rayleigh quotient of `𝓗`, in the exact shape of `boxEnergy`'s
body. -/
theorem boxEnergy_eq_ciInf_Rayl (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) :
    boxEnergy N L v = ⨅ Ψ : CInfty0Box N L, Rayl N L v Ψ := rfl

/-- `Rayl` is nonnegative for `v ≥ 0` (from
`Submission.BoxMonotone.rayleigh_quot_nonneg`). -/
theorem Rayl_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box N L) : 0 ≤ Rayl N L v Ψ := by
  simpa [Rayl, pow_two, mul_comm, mul_left_comm, mul_assoc] using
    rayleigh_quot_nonneg hL hv Ψ

/-- Dividing an infimum of reals by a positive constant (the `ℝ`-instance of
`ciInf_div`, which Mathlib states for `Group`s only). -/
theorem ciInf_div_const {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hbdd : BddBelow (Set.range f))
    {c : ℝ} (hc : 0 < c) : (⨅ i, f i) / c = ⨅ i, f i / c := by
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun i => ?_
    exact div_le_div_of_nonneg_right (ciInf_le hbdd i) hc.le
  · have hbdd' : BddBelow (Set.range (fun i => f i / c)) := by
      rcases hbdd with ⟨m, hm⟩
      exact ⟨m / c, fun y hy => by
        rcases hy with ⟨i, rfl⟩
        exact div_le_div_of_nonneg_right (hm (Set.mem_range_self i)) hc.le⟩
    have h1 : ∀ i, (⨅ i, f i / c) * c ≤ f i := by
      intro i
      have h2 := ciInf_le hbdd' i
      have h3 := mul_le_mul_of_nonneg_right h2 hc.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h3
    exact (le_div_iff₀ hc).mpr (le_ciInf h1)

/-- **The dichotomy at the box level**: if every *low* state satisfies the
shifted bound `Λ`, then so does the canonical box energy density. -/
theorem boxShape_of_spectralH {v : ℝ³ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v)
    {J C ε₀ η₀ : ℝ} (hC : 0 ≤ C) (hJ : lhyC ≤ J)
    (hspec : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L,
        Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
            ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L)
          ≤ Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2) :
    BoxShape v (a v) C ε₀ η₀ := by
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hρ : 0 ≤ dens N L := dens_nonneg N hLpos.le
  haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hLpos
  have hbdd : BddBelow (Set.range (fun Ψ : CInfty0Box N L => Rayl N L v Ψ)) :=
    ⟨0, fun y hy => by rcases hy with ⟨Ψ, rfl⟩; exact Rayl_nonneg hLpos hv Ψ⟩
  have hci : (⨅ Ψ : CInfty0Box N L, Rayl N L v Ψ / L ^ 3)
      = boxEnergy N L v / L ^ 3 := by
    rw [boxEnergy_eq_ciInf_Rayl]
    exact (ciInf_div_const hbdd (pow_pos hLpos 3)).symm
  have hfor : ∀ Ψ : CInfty0Box N L,
      lhyRhs (a v) C (1 / 2 + η₀) (dens N L) ≤ Rayl N L v Ψ / L ^ 3 := by
    intro Ψ
    have hth := theta_ge_lambda (A := a v) (K := C) (J := J) (η₀ := η₀)
      (ρ := dens N L) ha hρ hC hJ
    rw [← lhyRhs_eq_shift]
    by_cases hlow : Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
        ≤ Theta (a v) J (dens N L)
    · have := hspec L hL N hN Ψ hlow
      linarith
    · push_neg at hlow
      linarith
  calc lhyRhs (a v) C (1 / 2 + η₀) (dens N L)
      ≤ ⨅ Ψ : CInfty0Box N L, Rayl N L v Ψ / L ^ 3 := le_ciInf hfor
    _ = boxEnergy N L v / L ^ 3 := hci

/-- **The primary assembly**: `UBB` from the Hamiltonian-carrier spectral input
alone. -/
theorem UBB_of_spectralH {v : ℝ³ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) {J ε₀ η₀ : ℝ}
    (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J) (hspec : SpectralInputH v J ε₀ η₀) :
    UBB v η₀ := by
  rcases hspec with ⟨C, hC, hspec⟩
  exact ⟨ε₀, hε₀, C, hC, boxShape_of_spectralH hv ha hC hJ hspec⟩

end Work.UBB
