import Mathlib
import Submission.Work.LinnikAreas.Setup

/-!
# Splitting the family zero-density input (Area 2)

`Work.LinnikAreas.FamilyZeroDensityHyp` (Heath-Brown's (1.4)) is the only deep input of Area 2.
This module isolates the *irreducible* part of it.

The trivial, σ-blind family count of the workspace (`FamilyZeroCountNonPrincipal` +
`PrincipalZeroCount`) gives, log-free, `Σ_χ N(σ,T,χ) ≤ C_ε (qT)^{1+ε}`.  Consequently
Heath-Brown's estimate with exponent `(12/5+ε)(1-σ)` is *automatic* as soon as
`(12/5+ε)(1-σ) ≥ 1+ε`, i.e. `1-σ ≥ (1+ε)/(12/5+ε)`.  The genuinely new information is therefore
confined to the near-line range

`(12/5+ε)(1-σ) < 1+ε`  (thus `1-σ < 5/12 + O(ε)`),

which is what `FamilyZeroDensityNearLine` states.  The main theorem of this file,
`familyZeroDensityHyp_of_trivial_and_nearLine`, shows that the two pieces reassemble into
`FamilyZeroDensityHyp`; `area2.lean` then derives `Area2` from `FamilyZeroDensityNearLine`.

This is a genuine *split*: the near-line range is what the paper imports (Jutila's log-free bound
together with Huxley's estimate), while the complementary range is a theorem about the workspace's
own σ-blind zero counts.
-/

open DirichletCharacter
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The trivial, σ-blind family zero count, in the log-free shape `(qT)^{1+ε}`.**

For every `ε > 0` there is `C > 0` such that for all `q ≥ 2`, all `σ ∈ [0,1]` and all `T ≥ 1` the
total number of zeros (with multiplicity) of the completed `L`-functions of *all* the characters
mod `q` (the principal one included) in the rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is at most
`C (qT)^{1+ε}`.  The point is that this is *log-free*: the σ-blind count
`≪ q (T+2) log(q(T+2))` is converted into a power of `qT` by absorbing the logarithm. -/
def TrivialFamilyCountForm : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T) ≤ C * ((q : ℝ) * T) ^ (1 + ε)

/-- **The near-line core.**  Heath-Brown's (1.4) restricted to the range
`(12/5+ε)(1-σ) < 1+ε`, where the σ-blind count does not suffice.  This is the irreducible
imported input of Area 2 (a log-free family zero-density estimate for Dirichlet characters,
Jutila's log-free bound combined with Huxley's result). -/
def FamilyZeroDensityNearLine : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ((12 : ℝ) / 5 + ε) * (1 - σ) < 1 + ε →
        (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ))

/-- **Reassembly.**  The trivial count plus the near-line core is exactly `FamilyZeroDensityHyp`:
the hypothesis splits the `(σ,T)`-range into the part where the exponent `(12/5+ε)(1-σ)` is at
least `1+ε` (handled by the σ-blind count) and its complement (the core). -/
theorem familyZeroDensityHyp_of_trivial_and_nearLine
    (htriv : TrivialFamilyCountForm) (hnear : FamilyZeroDensityNearLine) :
    FamilyZeroDensityHyp := by
  intro ε hε
  obtain ⟨C₁, hC₁pos, hC₁⟩ := htriv ε hε
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hnear ε hε
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro q hq _inst σ T hσ0 hσ1 hT
  have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hrpownn : 0 ≤ ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ)) :=
    Real.rpow_nonneg (by linarith) _
  by_cases hcase : ((12 : ℝ) / 5 + ε) * (1 - σ) < 1 + ε
  · refine le_trans (hC₂ q hq σ T hσ0 hσ1 hT hcase) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hrpownn
  · have hle : 1 + ε ≤ ((12 : ℝ) / 5 + ε) * (1 - σ) := not_lt.mp hcase
    refine le_trans (hC₁ q hq σ T hσ0 hσ1 hT) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase hle) (le_of_lt hC₁pos)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hrpownn


/-! ## The canonical refinement of the near-line core: Jutila's and Huxley's halves

Heath-Brown's (1.4) is, in his own words, "a combination of a log-free bound of Jutila [21]
with a result of Huxley [17]".  Correspondingly the near-line core splits into

* `FamilyZeroDensityJutila` — the log-free bound `Σ_χ N(σ,T,χ) ≪_ε (qT)^{(2+ε)(1-σ)}` on
  `σ ≥ 4/5` (Jutila's log-free zero-density theorem, in the family form);
* `FamilyZeroDensityHuxley` — Huxley's `12/5` bound on `σ ≤ 4/5` (equivalently, by the
  functional-equation symmetry `β ↔ 1-β`, on `σ ≥ 1/2`);  no logarithm of `qT` is allowed,
  since the near-line shells `λ = (1-σ)𝓛 ≲ 1` of the far mass cannot absorb one.

Both are restricted to the family `Σ_χ` and are therefore *strictly weaker* than the full
`FamilyZeroDensityHyp`.  `familyZeroDensityNearLine_of_jutila_huxley` reassembles them into the
core. -/

/-- **Jutila's log-free bound**, `σ ≥ 4/5` (family form, exponent `2+ε`, no logarithm). -/
def FamilyZeroDensityJutila : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))

/-- **Huxley's bound**, `σ ≤ 4/5` (family form, exponent `12/5+ε`, no logarithm). -/
def FamilyZeroDensityHuxley : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ (4 : ℝ) / 5 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ))

/-- **Reassembly of the near-line core from Jutila's and Huxley's halves.** -/
theorem familyZeroDensityNearLine_of_jutila_huxley
    (hj : FamilyZeroDensityJutila) (hh : FamilyZeroDensityHuxley) :
    FamilyZeroDensityNearLine := by
  intro ε hε
  obtain ⟨Cj, hCjpos, hCj⟩ := hj ε hε
  obtain ⟨Ch, hChpos, hCh⟩ := hh ε hε
  refine ⟨max Cj Ch, lt_max_of_lt_left hCjpos, ?_⟩
  intro q hq _inst σ T hσ0 hσ1 hT hcase
  have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hrpownn : 0 ≤ ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ)) :=
    Real.rpow_nonneg (by linarith) _
  rcases le_total ((4 : ℝ) / 5) σ with hσ | hσ
  · refine le_trans (hCj q hq σ T hσ hσ1 hT) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase
        (by nlinarith : (2 + ε) * (1 - σ) ≤ ((12 : ℝ) / 5 + ε) * (1 - σ)))
      (le_of_lt hCjpos)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left Cj Ch) hrpownn
  · refine le_trans (hCh q hq σ T hσ0 hσ hT) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right Cj Ch) hrpownn


/-! ## Remarks on how the near-line core is expected to be discharged

**(a) Jutila + Huxley.**  Splitting the core at `σ = 4/5` (as `familyZeroDensityNearLine_of_jutila_huxley`
does) matches the paper's attribution of (1.4) and gives two *named* classical theorems:

* Jutila's log-free bound covers `σ ≥ 4/5`, i.e. `λ = (1-σ)𝓛 ≤ 𝓛/5`;
* Huxley's `12/5` bound covers `σ ≤ 4/5`, i.e. `λ ≥ 𝓛/5`.

**(b) Why the shell decomposition cannot be split at `λ ≈ A log log q`.**  A natural hope (recorded in
`ROUTE_LEAD.md` §3.1) is to use a *log-free* estimate only on the very low shells `λ ≤ A log log q`
(where HB §11's zero detector applies, with `λ₀ = (1/3) log log log q`) and to allow logarithms
beyond, absorbing them by the kernel decay `e^{-(4.9-c)λ}`.  This needs the log factor to be killed,
i.e. `λ ≳ (B/(4.9-c)) log log q` for the logarithmic power `B` of the estimate in question.  The
gap `(1/3) log log log q ≪ λ ≪ A log log q` is therefore *not* covered by either piece: at those
shells the log-free estimate is out of range and the logarithmic power is not yet absorbed, so the
corresponding terms of the far mass still carry a factor `(log q)^B`, which is fatal since the box
radius `R = R(ε)` is fixed.  Consequently the paper's own combination of Jutila and Huxley —
log-free, hence valid *uniformly* in `λ` — is what is really used, and `FamilyZeroDensityNearLine`
cannot be weakened to "log-free only for `λ ≤ A log log q`".

**(c) A sufficient rewrite of the far-bound argument.**  In the other direction, the shell
decomposition of `FarBoundOfDensity` *can* be reorganised shell-by-shell with the split of (a):
the shells `λ ≥ 𝓛/5` may then use an estimate *with* a logarithmic power `(log qT)^B` and
`c < 4.9`, because there `e^{-4.9λ}(qT)^{cλ/𝓛} ≤ q^{-(4.9-c)/5}` kills `(log q)^B`, while the
shells `λ ≤ 𝓛/5` use Jutila's log-free bound.  That would replace `FamilyZeroDensityNearLine` by
the pair (Jutila log-free on `σ ≥ 4/5`) + (Montgomery's large-sieve density theorem on
`σ ≤ 4/5`, where a logarithmic power is harmless), both of which are *named, textbook* results.
This rewrite is pure assembly work on the shell decomposition; it is not part of the irreducible
input.

**It has since been carried out** (`Submission/Work/LinnikAreas/FarBoundOfJutilaMontgomery` for
the definitions and the cell bound, `Submission/Work/LinnikAreas/FarBoundJM` for the assembly):
`FarBoundHyp_of_jutila_and_montgomery : FamilyZeroDensityJutila → FamilyZeroDensityMontgomery
→ FarBoundHyp` and `area2_of_jutila_montgomery`, where `FamilyZeroDensityMontgomery` is the
`σ ≤ 4/5` estimate with a logarithmic power allowed (`FamilyZeroDensityHuxley` implies it, by
`FamilyZeroDensityMontgomery_of_huxley`), and the use of the latter may even be restricted to
`σ ∈ [7/12, 4/5]` (`FamilyZeroDensityMontgomeryMid` plus
`FamilyZeroDensityMontgomery_of_trivial_and_mid`).  So the irreducible log-free requirement is
now confined to `σ ≥ 4/5`, exactly where the paper's attribution puts Jutila's bound.
-/

end Work.LinnikAreas
