import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Evar_le_trivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The vocabulary of FI §13 ("enlarging moduli")

The paper's (13.1) splits each class sum of the local variance `Work.FIPlan.Evar R S d α`
according to whether a fixed prime `p` divides `r` or not:

* `EvarA R S d p α` is the `p ∤ r` part `E_p(d)`,
* `EvarB R S d p α` is the `p ∣ r` part `E'_p(d)`,
* `L2p R S p α` is the `L²`-mass on the pairs with `p ∣ r`.

The structural facts used by the §13 argument are

* `Evar_le_two_EvarA_add_EvarB`  (13.1): `E(d) ≤ 2(E_p(d) + E'_p(d))`;
* `EvarA_le_p_sq_Evar_mul`       (13.3): `E_p(d) ≤ p² E(d p²)` (class refinement, using
  `(dp²/r) = (d/r)` for `p ∤ r`);
* `sum_EvarB_le`                        : `Σ_{d ∼ D} E'_p(d) ≪ (D + τ_max (RS)/p)·L2p`
  (the trivial estimate of the paper, via the divisor count of `r s' − r' s`).
-/


/-
## The `P > 1` case of FI §13, for the assembler

The intended proof of the "case `P > 1`" half of FI Proposition 13.1, with
`P := p13P D R S = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}` and `N := ⌈P⌉₊`, `W := {p prime : N < p ≤ 2N}`:

1. (`P13_EvarA_le`, (13.1)) for every prime `p ∈ W` and every `d ∈ (D, 2D]`:
   `Evar R S d α ≤ 2 (EvarA R S d p α + EvarB R S d p α) ≤ 2 p² Evar R S (d p²) α + 2 EvarB R S d p α`.
2. Averaging (1) over `p ∈ W` (Mertens: `Σ_{p∈W} 1 ≫ P/log(4P)` primes, `P13_prime_count`) turns
   `Vvar R S D α` into `(8P²/|W|) Σ_p U p + (2/|W|) Σ_p V p`, where
   `U p = Σ_{d ∈ (D,2D]} Evar R S (d p²) α` and `V p = Σ_{d ∈ (D,2D]} EvarB R S d p α`.
3. The `U`-sum: each modulus `e = d p²` (`p` prime in `W`, `d ∈ (D,2D]`) is hit at most
   `log e / log 4 + 1` times (a prime with `p² ∣ e` contributes two to the exponent of `e`), so
   `p13_enlarged_sum_le` gives `Σ_p U p ≤ (log(8e₁)/log 4 + 2) Σ_{e ∈ (e₁,8e₁]} Evar R S e α`
   with `e₁ = D N²`, and the window splits into `V(e₁) + V(2e₁) + V(4e₁)`; applying Proposition
   12.1 (`h121`) and the numerical comparison `hns`
   (`P · T12(D',ε/8) ≪ T13(D,ε)(RS)^{ε/2}` for `D' ∈ [DP²/2, 16DP²]`) gives the `U`-part
   `≪ (P log(4P)/cp) · log(8e₁) · T13 · Ener`, the extra `log(8e₁) ≪ (RS)^{ε/8}` coming from the
   last clause of `haf` (`8e₁ ≤ 32 (RS)^{3/4}`).
4. The `V`-sum: `P13_EvarB_sum` gives `V p ≤ (D + B(4RS/p + 4)) L2p R S p α` with
   `B = Kt (8RS)^{ε/4}`, and `P13_sum_L2p` with `P13_prime_divisor_count` gives
   `Σ_{p∈W} L2p R S p α ≤ Kpd (RS)^{ε/8} p14L2 R S α`; hence the `V`-part is
   `≪ (log(4P)/(cpP)) (D + B(4RS/N + 4)) (RS)^{ε/8} L2`, and the three terms are bounded by
   `T13(D,ε)` using `haf` (`D/P ≤ T13`, `1/P ≤ T13`, `(RS)/P² = D(R+S)^{1/4}(RS)^{1/4} ≤ T13`).
5. Bookkeeping: every auxiliary factor is absorbed with the `haf`/`log` bounds
   `log(4P) ≤ Kaf (RS)^{ε/8}`, `log x ≤ Kaf (RS)^{ε/8}` for `1 ≤ x ≤ 32(RS)^{3/4}` (so
   `log(8 e₁)/log 4 + 2 ≤ Kaf' (RS)^{ε/8}`, since `e₁ ≤ 4D P² ≤ 4(RS)^{3/4}`), and
   `(RS)^{ε/2} ≤ (RS)^ε`, `(RS)^{7ε/8} ≤ (RS)^ε` (as `RS ≥ 1`).
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `‖z + w‖² ≤ 2(‖z‖² + ‖w‖²)` for complex numbers. -/
lemma normSq_add_le (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have h2 : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (‖z‖ + ‖w‖) ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  linarith

/-- The class sum of the local variance of FI (11.7), restricted to the `r` selected by `sel`:
`Σ_{r ≤ 2R, (r,d)=1, sel r} Σ_{s ≤ 2S, s ≡ r a (d)} α r s (r|d')`. -/
def EvarClsSum (R S d : ℕ) (α : ℕ → ℕ → ℂ) (sel : ℕ → Prop) [DecidablePred sel] (a : ℕ) : ℂ :=
  ∑ r ∈ Finset.Icc 1 (2 * R),
    if Nat.Coprime r d ∧ sel r then
      ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)),
        α r s * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ)
    else 0

/-- The `p ∤ r` part `E_p(d)` of the local variance (FI (13.1)). -/
def EvarA (R S d p : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ a ∈ Finset.range d,
    Complex.normSq (EvarClsSum R S d α (fun r => ¬ p ∣ r) a)

/-- The `p ∣ r` part `E'_p(d)` of the local variance (FI (13.1)). -/
def EvarB (R S d p : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ a ∈ Finset.range d,
    Complex.normSq (EvarClsSum R S d α (fun r => p ∣ r) a)

/-- The `L²`-mass of `α` on the pairs with `p ∣ r`: `Σ_{p ∣ r ≤ 2R} Σ_{s ≤ 2S} ‖α r s‖²`. -/
def L2p (R S p : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 (2 * R)).filter (fun r => p ∣ r),
    ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)

lemma EvarClsSum_split (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (a : ℕ) :
    EvarClsSum R S d α (fun _ => True) a
      = EvarClsSum R S d α (fun r => ¬ p ∣ r) a + EvarClsSum R S d α (fun r => p ∣ r) a := by
  unfold EvarClsSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hC : Nat.Coprime r d
  · by_cases hp : p ∣ r
    · rw [if_pos ⟨hC, trivial⟩, if_neg (by tauto), if_pos ⟨hC, hp⟩]; ring
    · rw [if_pos ⟨hC, trivial⟩, if_pos ⟨hC, hp⟩, if_neg (by tauto)]; ring
  · rw [if_neg (by tauto : ¬ (Nat.Coprime r d ∧ True)),
        if_neg (by tauto : ¬ (Nat.Coprime r d ∧ ¬ p ∣ r)),
        if_neg (by tauto : ¬ (Nat.Coprime r d ∧ p ∣ r))]; ring

/-- `Evar` is the sum of the `sel = True` class sums. -/
lemma Evar_eq_sum_clsSum_true (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d, Complex.normSq (EvarClsSum R S d α (fun _ => True) a) := by
  rw [Work.FIPlan.Evar]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  unfold EvarClsSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hC : Nat.Coprime r d
  · rw [if_pos hC, if_pos ⟨hC, trivial⟩]
  · rw [if_neg hC, if_neg (by tauto)]

/-- **FI (13.1)**: `E(d) ≤ 2(E_p(d) + E'_p(d))`. -/
lemma Evar_le_two_EvarA_add_EvarB (R S d p : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α ≤ 2 * (EvarA R S d p α + EvarB R S d p α) := by
  rw [Evar_eq_sum_clsSum_true]
  calc ∑ a ∈ Finset.range d, Complex.normSq (EvarClsSum R S d α (fun _ => True) a)
      = ∑ a ∈ Finset.range d, Complex.normSq (EvarClsSum R S d α (fun r => ¬ p ∣ r) a
            + EvarClsSum R S d α (fun r => p ∣ r) a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [EvarClsSum_split]
    _ ≤ ∑ a ∈ Finset.range d, 2 * (Complex.normSq (EvarClsSum R S d α (fun r => ¬ p ∣ r) a)
            + Complex.normSq (EvarClsSum R S d α (fun r => p ∣ r) a)) :=
        Finset.sum_le_sum (fun a _ => normSq_add_le _ _)
    _ = 2 * (EvarA R S d p α + EvarB R S d p α) := by
        rw [EvarA, EvarB, ← Finset.mul_sum]
        congr 2
        rw [Finset.sum_add_distrib]

end

end Work.FIArea4
