import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

/-!
# `Setup` — notation and easy facts for Area 2 (the HB §13 reduction)

This module holds the definitions used by `Submission.Work.LinnikAreas.area2` and by the
lemmas delegated for it.  Everything here is proved; nothing depends on Area 2 itself.

Mathematical context (Heath-Brown 1992, §13).  With `L = 11/2`, `K = 3/10`, `a = L - 2K = 4.9`,
`𝓛 = log q` and the tent weight `h = tentWeight L K`, the class prime sum is

`PS = Σ_{p ≡ a (mod q)} (log p / p) · h(log p / 𝓛)`,

and Heath-Brown's Lemmas 13.1–13.2 give

`𝓛⁻¹ PS = K²/φ(q) - φ(q)⁻¹ Σ_{χ ≠ 1} χ̄(a) Σ_ρ Hk(L,K,(1-ρ)𝓛) + O(1/(φ(q)𝓛))`,

where the inner sum runs over the non-trivial zeros `ρ` of `L(s,χ*)` (`χ*` the primitive
character inducing `χ`), **provided** the sum is restricted to the box
`InBox q R ρ` (`λ(ρ) ≤ R` and `|Im ρ|·𝓛 ≤ R`) — the zeros outside the box are the "far" zeros,
whose total mass is bounded by the far bound `farZeroBound` (`Submission.Work.LinnikAreas.farZeroBound`).

* `farSum q L K R χ` is the mass of the far zeros of `χ`, i.e. the complement of the box.
* `boxSum`/`InBox`/`Hk`/`zeroMult` come from `Submission.Work.LinnikContract.Defs`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- The **far part** of the zero sum for `χ`: the total mass (with multiplicity) of the zeros of
`Λ(χ*,·)` lying outside Heath-Brown's box `InBox q R`, weighted by the kernel `Hk L K`. -/
def farSum (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ, if InBox q R ρ then 0
    else (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * ((Real.log (q : ℝ) : ℝ) : ℂ))‖

lemma farSum_nonneg (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) :
    0 ≤ farSum q L K R χ := by
  refine tsum_nonneg (fun ρ => ?_)
  split
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)


/-- **Number of zeros in a rectangle.** `zeroCountIn χ σ T` is the number of zeros `ρ` of
`Λ(χ*,·)` (counted with multiplicity) with `σ ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T`.  Since `Λ(χ*,·)` is
entire with finitely many zeros in any bounded region, this is a finite sum (`finsum`). -/
def zeroCountIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℝ :=
  ∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T then (zeroMult χ ρ : ℝ) else 0

open scoped BigOperators in
/-- A **family zero-density estimate** for the Dirichlet characters mod `q`, uniform in `q`:
for every `ε > 0` the number of zeros of the whole family in the rectangle
`σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is `≪_ε (qT)^{(12/5+ε)(1-σ)}` (Jutila's log-free bound combined with
Huxley's estimate; Heath-Brown's (1.4), which is **log-free** — no power of `log qT` is
allowed, since the near-line region of the far-zero sum cannot absorb such a factor).
This is the only deep input of Area 2 that is not supplied by the certificates of Areas 3–5,
and it is Burgess-free (only convexity and the large sieve enter). -/
def FamilyZeroDensityHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ σ T : ℝ,
    0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ))

/-- **Heath-Brown's Lemma 13.2 (far zeros).**  For every `ε > 0` there is `R = R(ε)` such that,
for all sufficiently large `q`, the total mass of the zeros **outside** the box `InBox q R`
(over all non-principal characters mod `q`) is at most `ε`.  With `λ(ρ) = (1-Re ρ) log q` and
`Hk` Heath-Brown's kernel, the box is `λ(ρ) ≤ R`, `|Im ρ| log q ≤ R`. -/
def FarBoundHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
    ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ ≤ ε


/-- **Heath-Brown's Lemma 13.1, uniform in `q` (the class-sum explicit formula, restricted to
the box).**  With `L = 11/2`, `K = 3/10` and `𝓛 = log q`, the tent-weighted prime sum over the
class `a mod q` equals `𝓛·(K²/φ(q) − φ(q)⁻¹Σ_{χ≠1} χ̄(a)·(box sum of zeros))` up to

* `C/(φ(q)·𝓛)` — the (uniform) error of the explicit formula, and
* `φ(q)⁻¹ Σ_{χ≠1} farSum` — the mass of the zeros *outside* the box,
* `C·q^{-(L-2K)/2}/𝓛` — the prime-power tail.

This is the box-restricted form of `tentMellin_bridge_scale` + `tentMellin_principal`: the
Dedekind-sum identity is summed over `χ` with the orthogonality relation
`1_{n ≡ a} = φ(q)⁻¹ Σ_χ χ̄(a)χ(n)`, and the zeros lie at scale `log q`.  In particular the
error constant `C` is **absolute** (independent of `q` and of `a`). -/
def ClassIdentityHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ R : ℝ, 0 < R → ∀ a : ℕ, a.Coprime q →
    ∀ X : ℕ, (q : ℝ) ^ (11/2 : ℝ) ≤ (X : ℝ) →
      ‖((Real.log (q : ℝ) : ℂ))⁻¹ *
          (∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
            ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10) (Real.log (p : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
        - (((3/10 : ℝ) ^ 2 / (q.totient : ℝ) : ℝ) : ℂ)
        + ((q.totient : ℂ))⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ) (χ (a : ZMod q)) * boxSum q (11/2) (3/10) R χ‖
      ≤ C / ((q.totient : ℝ) * Real.log (q : ℝ))
        + (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ
        + C * (q : ℝ) ^ (-(49/10 : ℝ) / 2) / Real.log (q : ℝ)


end Work.LinnikAreas
