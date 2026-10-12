import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBB.Arith` — the parameter arithmetic of the UBB assembly

All statements here are PROVED (`sorry`-free, axiom-clean).  They are the pure
arithmetic/bookkeeping that the assembly needs; the *analytic* content lives in
the named inputs of `Defs.lean`/`Assembly.lean`.

Contents:

* `lhyRhs_eq_shift` — **the dictionary**: the corpus's canonical LHY right-hand
  side is FS's shifted (chemical-potential) right-hand side plus the exact
  shift `8πAρ²`.  This is what makes "FS `thm:LHY-Box`" and "corpus UBB" the
  *same* statement (`boxShape_iff_fsShape`).
* `theta_ge_lambda` — the a-priori threshold dominates the target as soon as
  `J ≥ c = 128/(15√π)`; this is the arithmetic behind FS's "if such a state
  does not exist, then there is nothing to prove" and pins the admissible
  choice of the FS parameter `J` (`0 < J ≤ K_B³`, `J ≥ c`).
* the `dens` bookkeeping and the `lhyRhs` domination wrapper.
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

/-! ## 1. The dictionary -/

/-- **The shift identity** (pure algebra): the corpus's canonical LHY
right-hand side at density `ρ` equals FS's shifted right-hand side `Λ` plus the
exact chemical-potential shift `8πAρ²`:

`lhyRhs A K (1/2+η₀) ρ = Λ A K η₀ ρ + 8πAρ²`,

`Λ A K η₀ ρ = −4πρ²A(1 − c√(ρA³) + K(ρA³)^{1/2+η₀})`, `c = 128/(15√π)`.

This is FS's passage `thm:LHY-Box` ⟹ `thm:LHY-Background` (`eq:BackgroundH`:
`H_{μ,N} = H_N − 8πaμN`) read as an identity of the two right-hand sides. -/
theorem lhyRhs_eq_shift (A K η₀ ρ : ℝ) :
    Lambda A K η₀ ρ + 8 * π * A * ρ ^ 2 = lhyRhs A K (1 / 2 + η₀) ρ := by
  unfold Lambda lhyC lhyRhs
  ring

/-- **The dictionary for the box theorem**: the corpus (canonical, unshifted)
shape `BoxShape` and FS's shifted shape `FSShape` are the SAME statement.  So
"UBB" and "FS `thm:LHY-Box` with `μ := N/L³`" are interchangeable, and a proof
of either is a proof of the other. -/
theorem boxShape_iff_fsShape {v : ℝ³ → ℝ} {A C ε₀ η₀ : ℝ} :
    BoxShape v A C ε₀ η₀ ↔ FSShape v A C ε₀ η₀ := by
  constructor
  · intro h L hL N hN
    have h1 := h L hL N hN
    rw [← lhyRhs_eq_shift] at h1
    linarith
  · intro h L hL N hN
    have h1 := h L hL N hN
    rw [← lhyRhs_eq_shift]
    linarith

/-! ## 2. The threshold/target comparison -/

/-- **The a-priori threshold dominates the target** as soon as `J ≥ c`:

`Λ A K η₀ ρ ≤ Θ A J ρ`  whenever  `0 ≤ A`, `0 ≤ ρ`, `0 ≤ K`, `c ≤ J`.

The difference is `4πρ²A((c−J)√(ρA³) − K(ρA³)^{1/2+η₀}) ≤ 0`.  Consequence:
a state whose shifted energy density is *above* the a-priori threshold
automatically satisfies the box lower bound; only the *low* states need the
spectral analysis.  This is FS's "if such a state does not exist, then there is
nothing to prove". -/
theorem theta_ge_lambda {A K J η₀ ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hK : 0 ≤ K) (hJ : lhyC ≤ J) :
    Lambda A K η₀ ρ ≤ Theta A J ρ := by
  have hpre : 0 ≤ 4 * π * ρ ^ 2 * A := by positivity
  have hsq : 0 ≤ √(ρ * A ^ 3) := Real.sqrt_nonneg _
  have hpow : 0 ≤ (ρ * A ^ 3) ^ (1 / 2 + η₀) := Real.rpow_nonneg (by positivity) _
  have hb : (lhyC - J) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ (1 / 2 + η₀) ≤ 0 := by
    have h1 : (lhyC - J) * √(ρ * A ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hsq
    have h2 : 0 ≤ K * (ρ * A ^ 3) ^ (1 / 2 + η₀) := mul_nonneg hK hpow
    linarith
  have hkey : Lambda A K η₀ ρ - Theta A J ρ
      = 4 * π * ρ ^ 2 * A * ((lhyC - J) * √(ρ * A ^ 3)
          - K * (ρ * A ^ 3) ^ (1 / 2 + η₀)) := by
    unfold Lambda Theta
    ring
  have : Lambda A K η₀ ρ - Theta A J ρ ≤ 0 := by
    rw [hkey]
    exact mul_nonpos_of_nonneg_of_nonpos hpre hb
  linarith

/-- `lhyC` is positive (needed to choose `J`). -/
theorem lhyC_pos : 0 < lhyC := by
  unfold lhyC
  positivity

/-! ## 3. `dens` bookkeeping -/

theorem dens_nonneg (N : ℕ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ dens N L := by
  unfold dens
  positivity

theorem dens_pos {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L) : 0 < dens N L := by
  unfold dens
  have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

theorem dens_mul (N : ℕ) {L : ℝ} (_hL : L ≠ 0) (A : ℝ) :
    dens N L * A ^ 3 = (N : ℝ) * A ^ 3 / L ^ 3 := by
  unfold dens
  ring

/-- The threshold written out at the box density `ρ = N/L³`. -/
theorem theta_dens (A J : ℝ) (N : ℕ) (L : ℝ) :
    Theta A J (dens N L)
      = - (4 * π * dens N L ^ 2 * A * (1 - J * √(dens N L * A ^ 3))) := rfl

/-- The target written out at the box density `ρ = N/L³`. -/
theorem lambda_dens (A K η₀ : ℝ) (N : ℕ) (L : ℝ) :
    Lambda A K η₀ (dens N L)
      = - (4 * π * dens N L ^ 2 * A
            * (1 - lhyC * √(dens N L * A ^ 3) + K * (dens N L * A ^ 3) ^ (1 / 2 + η₀))) :=
  rfl

/-! ## 4. The dilute window kills the small boxes

The `∀L ≥ 1` quantifier of `UBB` is *not* a strengthening to worry about: if
`ε₀` is chosen small in terms of the scattering length `A = a v` and the box side
(it suffices that `ε₀ ≤ (A/R)^{4}`-ish, see `README.md` §6), then a box of side
`L < A/ε₀^{1/3}` can only carry `N = 0` particles inside the dilute window — and
`N = 0` is trivial.  This is the arithmetic behind the corpus/FS regime
conditions (`R ≤ L·chiR0`, `1 ≤ μ L³`, `R ≤ K_B^{1/2}(μ a³)^{1/4}(μa)^{-1/2}`
of `Work.SmallBoxDLBound`), all of which then hold automatically on the dilute
window with `L` large. -/

/-- **The dilute window forces `N = 0` on small boxes**: for `0 < L`, if
`dens N L · A³ ≤ ε₀` and `ε₀ · L³ < A³` (i.e. `L < A/ε₀^{1/3}`) then `N = 0`. -/
theorem dilute_forces_N_zero {N : ℕ} {L A ε₀ : ℝ} (hA : 0 < A) (hL : 0 < L)
    (h : dens N L * A ^ 3 ≤ ε₀) (hε : ε₀ * L ^ 3 < A ^ 3) : N = 0 := by
  have hL3 : 0 < L ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hL3.le
  have hrew : dens N L * A ^ 3 * L ^ 3 = (N : ℝ) * A ^ 3 := by
    unfold dens
    field_simp
  rw [hrew] at hmul
  have hlt : (N : ℝ) * A ^ 3 < A ^ 3 := lt_of_le_of_lt hmul hε
  have hA3 : 0 < A ^ 3 := by positivity
  have hN1 : (N : ℝ) < 1 := by nlinarith
  by_contra hN
  have hNpos : 1 ≤ N := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hN)
  have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  linarith

/-! ## 5. The `lhyRhs` domination wrapper (consumer shape)

`Submission.UniformBox.lhyRhs_le_of_domination` proves the same fact with the
`η`-parametrised target exponent; we re-export it in the `η₀/η` normalisation
used by `Submission.UBBtoGc`. -/

/-- Decreasing the error coefficient (in the sense of the domination
`C·t^(η₀−η) ≤ K`) and increasing the error exponent from `1/2+η` to `1/2+η₀`
lowers `lhyRhs`. -/
theorem lhyRhs_le_of_domination {A C K : ℝ} {η₀ η ρ : ℝ} (hA : 0 ≤ A)
    (hu : 0 < ρ * A ^ 3) (hdom : C * (ρ * A ^ 3) ^ (η₀ - η) ≤ K) :
    lhyRhs A K (1 / 2 + η) ρ ≤ lhyRhs A C (1 / 2 + η₀) ρ := by
  have hu0 : 0 ≤ ρ * A ^ 3 := le_of_lt hu
  have hCK : C * (ρ * A ^ 3) ^ (1 / 2 + η₀) ≤ K * (ρ * A ^ 3) ^ (1 / 2 + η) := by
    calc
      C * (ρ * A ^ 3) ^ (1 / 2 + η₀)
          = C * ((ρ * A ^ 3) ^ (1 / 2 + η) * (ρ * A ^ 3) ^ (η₀ - η)) := by
            rw [show 1 / 2 + η₀ = (1 / 2 + η) + (η₀ - η) by ring]
            rw [Real.rpow_add hu]
      _ = (C * (ρ * A ^ 3) ^ (η₀ - η)) * (ρ * A ^ 3) ^ (1 / 2 + η) := by ring
      _ ≤ K * (ρ * A ^ 3) ^ (1 / 2 + η) :=
            mul_le_mul_of_nonneg_right hdom (Real.rpow_nonneg hu0 (1 / 2 + η))
  have hinner : 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ (1 / 2 + η)
      ≤ 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - C * (ρ * A ^ 3) ^ (1 / 2 + η₀) := by
    linarith
  have hpre : 0 ≤ 4 * π * ρ ^ 2 * A := by positivity
  calc
    lhyRhs A K (1 / 2 + η) ρ
        = 4 * π * ρ ^ 2 * A *
            (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ (1 / 2 + η)) := by
          rw [lhyRhs]
    _ ≤ 4 * π * ρ ^ 2 * A *
            (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - C * (ρ * A ^ 3) ^ (1 / 2 + η₀)) := by
          exact mul_le_mul_of_nonneg_left hinner hpre
    _ = lhyRhs A C (1 / 2 + η₀) ρ := by rw [lhyRhs]

end Work.UBB
