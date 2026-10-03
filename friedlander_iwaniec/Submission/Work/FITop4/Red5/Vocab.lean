/-
# `Submission.Work.FITop4.Red5.Vocab` — the round-5 vocabulary

Round 4 (`Defs4`/`Areas4`) isolated the `§§4–5.2` reduction as the hypothesis `AreaReduce`.  Round 5
*proves* the reduction.  The one place where the round-4 parameters are too tight is the paper's §4
sentence "the contribution of terms with `m ⩽ ϑxN^{-1}` is absorbed by the bound (4.17)": as
`Red5/BformAtilSmall_le` shows, that region can be absorbed *elementarily*, but only into an error
of size `(ϑx)^{3/4}(log x)^{65536}`, i.e. `x^{3/4}(log x)^{-3A/4+65536}` where `ϑ = (log x)^{-A}`.
The frozen target of the chain is `Ã(x)(log x)^{4-Astar}` with `Astar = 2^26+4`, which requires
`3A/4 - 65536 ≥ Astar - 4`, i.e.

  `A ≥ (4/3)(Astar + 65536) ≈ 8.95·10^7`.

So round 5 runs the *pieces* (and hence the seven areas, which are stated for an arbitrary `Params`)
at the larger saving exponent `Asave`, while the *conclusion* is the frozen exponent `4 - Astar`.

Two further items belong to the round-5 contract:

* the round-5 *target* is the `Π`-restricted `Prop41StatementPiBig`: the seven areas' coefficient
  `IsBetaCoeff` pins `β` to the support (5.8) `(z, Π) = 1`, so the `§§4–5.2` reduction produces a
  bound for `Work.FITop.BformPi x N C Pz`, the form (4.3) of the paper.  (An earlier draft bundled
  the removal `BformAtil ≤ BformPi + err` into an eighth area; that *pointwise* statement is FALSE
  — e.g. `N = 1`, `C = 1` gives `BformPi = 0` while `BformAtil ≍ x^{3/4}` — and the companion's
  Theorem 3 is an *integrated* statement over the `N`-window and the truncation level.  That
  chapter belongs to the consumer `FIChain`; see `PI_REMOVAL_ROUTE.md`.)
* the wider `B`-range `BmaxBig η = b(η) + 2^31` (the paper's `B` must dominate the internal
  `(9.12)` condition `B ≥ 15.5·Asave + b(η) + O(1)`, which `b(η) + 2^30` does not).
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Aseq_tau_sq_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic

set_option autoImplicit false

namespace Work.FITop4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The internal saving exponent of the round-5 reduction**: `A = 10^8`, comfortably above the
threshold `(4/3)(Astar + 65536) ≈ 8.95·10^7` forced by the elementary absorption of the small-`m`
region (`Red5.BformAtilSmall_le`), and comfortably below the value
`2^31/15.5 ≈ 1.38·10^8` at which the `B`-range becomes uncomfortably large. -/
def Asave : ℝ := 100000000

lemma Asave_pos : 0 < Asave := by unfold Asave; norm_num

lemma Astar_le_Asave : Astar ≤ Asave := by unfold Astar Asave; norm_num

/-- The `A'` of (10.12) at the round-5 internal exponent. -/
def AsaveP : ℝ := Aprime Asave

/-- `θ = (log x)^{-A'}` at the round-5 internal exponent. -/
abbrev thetaSave (x : ℕ) : ℝ := thetaOf x Asave

/-- `ϑ = (log x)^{-A}` at the round-5 internal exponent. -/
abbrev varthetaSave (x : ℕ) : ℝ := varthetaOf x Asave

/-- `τ = (log x)^{2A+2^{20}}` (the (10.11) choice) at the round-5 internal exponent. -/
abbrev tauSave (x : ℕ) : ℝ := tauOf x Asave

/-- **The range constant of the round-5 target.**  The paper's numerics needs
`B ⩾ 15.5A + b(η) + O(1)` (the (9.12) condition at the (10.11) choice of `τ`); with `A = Asave`
this is `≈ 1.55·10^9 + b(η)`, so `BmaxBig η = b(η) + 2^31` suffices. -/
def BmaxBig (η : ℝ) : ℝ := bFun η + (2 : ℝ) ^ (31 : ℕ)

lemma Bmax_le_BmaxBig (η : ℝ) : Bmax η ≤ BmaxBig η := by
  unfold Bmax BmaxBig
  have : (0 : ℝ) < (2 : ℝ) ^ (30 : ℕ) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (31 : ℕ) := by positivity
  linarith [le_of_lt h2]

/-- **The round-5 target**: `Prop41Statement4` with the wider `B`-range `BmaxBig`.  (The exponent
`4 - Astar` of the frozen statement is unchanged.) -/
def Prop41StatementBig : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ B ≤ BmaxBig η ∧ 0 < K ∧
    ∀ x : ℕ, x₀ ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      ∀ C : ℝ, 1 ≤ C → C ≤ (N : ℝ) ^ (1 - η) →
      ∀ Pz : ℕ, 2 ≤ Pz →
        (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
        Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
        BformAtil x N C ≤ K * AcountAtil x * (Real.log (x : ℝ)) ^ (4 - Astar)

/-- The round-4 target implies the round-5 one (a wider `B`-range is a weaker statement). -/
theorem Prop41StatementBig_of_Four (h : Prop41Statement4) : Prop41StatementBig := by
  intro η hη0 hη1
  obtain ⟨B, K, x₀, hB0, hBle, hK, hbound⟩ := h η hη0 hη1
  exact ⟨B, K, x₀, hB0, le_trans hBle (Bmax_le_BmaxBig η), hK, hbound⟩

/-- The `Π`-condition `(n, Π) = 1` of (4.21)/(5.8) as a named proposition (so that the
`if`-conditions of the reduction are decidable by typeclass search). -/
def PiCond (Pz n : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n

instance (Pz n : ℕ) : Decidable (PiCond Pz n) := Classical.dec _

/-- The `τ`-condition `τ(n) ≤ τ` of (4.9)/(5.9) as a named proposition. -/
def TauCond (τ : ℝ) (n : ℕ) : Prop := (((n.divisors.card : ℕ)) : ℝ) ≤ τ

instance (τ : ℝ) (n : ℕ) : Decidable (TauCond τ n) := Classical.dec _

/-- **The `τ`-truncated `Π`-restricted sieve form** (the paper's (4.9)): `BformPi` with the
additional restriction `τ(n) ≤ τ` on the inner variable (the support condition (5.9) that
`IsBetaCoeff` carries). -/
def BformPiTau (x N Pz : ℕ) (C τ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
      then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
        * Work.FITop.atilFIa (m * n) else 0)|

/-- **The round-5 target, in the `Π`-restricted form.**  Identical to `Prop41StatementBig` — the
same `η`-range, the same `N`-range (in particular the same `BmaxBig η` in the upper bound), the same
`C`- and `Pz`-ranges (`Pz` is already quantified in the hypothesis list, so it is *not* an extra
parameter) — except that the bilinear form in the conclusion is the `Π`-restricted
`Work.FITop.BformPi x N C Pz`, i.e. the form (4.3) of the paper with the condition `(n, Π) = 1`.

This is the form the `§§4–5.2` reduction produces: the seven areas' coefficient class `IsBetaCoeff`
has the support condition (5.8) `(z, Π) = 1` built in, so the pieces bound the `Π`-restricted form;
the passage from `BformPi` back to the frozen, `Π`-free `BformAtil` is the companion paper's
Theorem 3 (`ASP` §10) and belongs to the consumer `FIChain` (see `PI_REMOVAL_ROUTE.md`). -/
def Prop41StatementPiBig : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ B ≤ BmaxBig η ∧ 0 < K ∧
    ∀ x : ℕ, x₀ ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      ∀ C : ℝ, 1 ≤ C → C ≤ (N : ℝ) ^ (1 - η) →
      ∀ Pz : ℕ, 2 ≤ Pz →
        (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
        Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
        Work.FITop.BformPi x N C Pz ≤ K * AcountAtil x * (Real.log (x : ℝ)) ^ (4 - Astar)

end

end Work.FITop4
