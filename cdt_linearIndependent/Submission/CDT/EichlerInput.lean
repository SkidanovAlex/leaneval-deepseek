import Mathlib
import Submission.CDT.ZagierHBC
import Submission.CDT.L2chi3Real
import Submission.CDT.L2chi3Corollary

/-!
# Node (2) of `mainA` — the Γ₀(6)/Eichler-integral input, stated precisely

This module pins down — as standalone, `#check`-able statements — the
missing *modular* input of node (2) of the dismantled proof of CDT Theorem
`mainA` (see the "proof of mainA, dismantled" section of
`Submission.CDT.TheoremA_leaf`): the upgrade of the recurrences for the
companion series `H_B`, `H_C` (`Submission.CDT.ZagierHBC`) to

* **integrality** `[1,2,…,n]²·bₙ, [1,2,…,n]²·cₙ ∈ ℤ`
  (`defabc` item 2 of the paper), i.e. the sequences have denominator type
  `[1..n]²` — with the notation `bₙ := HB_coeff n`, `cₙ := HC_coeff n`;
* **overconvergence** of the difference series
  `H_B − (L(2,χ₋₃)/2)·H_A` and `H_C − (ζ(2)/4)·H_A` to radius `1`
  (`defabc` item 3), i.e. their coefficient sequences `eichlerDiffB`,
  `eichlerDiffC` grow slower than every `(1/r)ⁿ`, `r < 1`
  (`OverconvergesUnit`).

These facts come in the paper from the weight-zero modular symmetry of the
Γ₀(6) Eichler integrals `A(B − L/2)`, `A(C − ζ(4)/4)` (the
`WeilHeckeLemma`/Eichler-integral input of `defabc`; see also the
integral representations `(Cintegral)`/`(Aintegral)` of the paper), and are
*not* consequences of the recurrences alone — they are exactly the content
of node (2).  They are therefore declared as *hypotheses* (definitional
`Prop`s `EichlerInputB`, `EichlerInputC`), with no `axiom` and no `sorry`:
a future modular-forms development (or an integral-representation proof in
the spirit of the Beukers chapter) discharges them, and nothing downstream
needs to change.

**Proved here (the upgrade mechanism — what node (2)'s input supplies to
node (defG))**: `OverconvergesUnit` is closed under pointwise addition and
scalar multiplication (`OverconvergesUnit_add`, `OverconvergesUnit_smul`),
the coefficient identity
`zagierH_coeff_seq_eq_diff` — under the absurd `ℚ`-dependence
`a + b·L/2 + c·ζ/4 = 0` the `H = aH_A + bH_B + cH_C` coefficients equal the
`b,c`-combination of the two difference sequences — and the flagship
derived theorem

```lean
theorem functionsH_overconverges (a b c : ℚ)
    (hrel : (a:ℝ) + (b:ℝ)·(L2chi3Real/2) + (c:ℝ)·(zeta2Real/4) = 0)
    (hB : OverconvergesUnit eichlerDiffB) (hC : OverconvergesUnit eichlerDiffC) :
    OverconvergesUnit (fun n => (ZagierH_coeff_seq a b c n : ℝ))
```

which is Proposition `functionsH`'s overconvergence half for the
`H(x)` entering the symmetrization `G = Sym⁺H` of the `mainA` proof.
The **integrality half for the combination** is supplied here as
`functionsH_denomtype_int` (given the node-(2) integrality of `H_B` and
`H_C`, every *integer* combination `H = a·H_A + b·H_B + c·H_C` has
denominator type `[1..n]²` — rational combinations reduce to this by
clearing the common denominator), using `HasDenomTypeSq_HA` (`H_A`'s
coefficients are the integers `HA_coeffZ`).  (The `lcmRange` predicate is
the formal `[1,2,…,n]`; `HasDenomTypeSq f` says `[1..n]²·fₙ ∈ ℤ` — sanity:
`4·b₂ = 4·(23/4) = 23`, `36·b₃ = 36·(145/4) = 1305`,
`36·c₃ = 36·(343/9) = 1372`, matching `defabc`'s displayed values.)
-/

namespace Submission.CDT

noncomputable section

open scoped BigOperators

/-- `[1,2,…,n]`, the lcm of `1..n` (empty lcm is `1`) -/
def lcmRange : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmRange n) (n + 1)

/-- `[1,2,…,n]` is positive -/
lemma lcmRange_pos (n : ℕ) : 0 < lcmRange n := by
  induction n with
  | zero => simp [lcmRange]
  | succ n ih => simp [lcmRange, Nat.lcm_pos ih]

/-- `f : ℕ → ℚ` has **denominator type `[1..n]²`**: for every `n`,
`[1,2,…,n]²·fₙ` is an integer (paper `defabc` item 2). -/
def HasDenomTypeSq (f : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, ((lcmRange n : ℚ) ^ 2) * f n = (z : ℚ)

/-- the power series `Σₙ fₙ·xⁿ` (real coefficients) **overconverges to
radius ≥ 1**: for every `r < 1` the coefficients grow at most like
`C·(1/r)ⁿ` (paper `defabc` item 3: radius of convergence `1`). -/
def OverconvergesUnit (f : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |f n| ≤ C / r ^ n

/-- `OverconvergesUnit` is closed under pointwise addition -/
lemma OverconvergesUnit_add {f g : ℕ → ℝ} (hf : OverconvergesUnit f)
    (hg : OverconvergesUnit g) : OverconvergesUnit (fun n => f n + g n) := by
  intro r hr0 hr1
  rcases hf r hr0 hr1 with ⟨Cf, hCf0, hfb⟩
  rcases hg r hr0 hr1 with ⟨Cg, hCg0, hgb⟩
  refine ⟨Cf + Cg, add_pos hCf0 hCg0, ?_⟩
  intro n
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le (f n) (g n)
    _ ≤ Cf / r ^ n + Cg / r ^ n := add_le_add (hfb n) (hgb n)
    _ = (Cf + Cg) / r ^ n := by rw [← add_div]

/-- `OverconvergesUnit` is closed under scalar multiplication -/
lemma OverconvergesUnit_smul (t : ℝ) {f : ℕ → ℝ} (hf : OverconvergesUnit f) :
    OverconvergesUnit (fun n => t * f n) := by
  intro r hr0 hr1
  rcases hf r hr0 hr1 with ⟨C, hC0, hfb⟩
  refine ⟨|t| * C + 1, add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg t) (le_of_lt hC0)) zero_lt_one, ?_⟩
  intro n
  calc
    |t * f n| = |t| * |f n| := abs_mul t (f n)
    _ ≤ |t| * (C / r ^ n) := mul_le_mul_of_nonneg_left (hfb n) (abs_nonneg t)
    _ = (|t| * C) / r ^ n := by rw [← mul_div_assoc]
    _ ≤ (|t| * C + 1) / r ^ n := by
          exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt hr0) n)

/-- the coefficients of `H_B(x) − (L(2,χ₋₃)/2)·H_A(x)` (real) -/
def eichlerDiffB (n : ℕ) : ℝ := (HB_coeff n : ℝ) - (L2chi3Real / 2) * (HA_coeff n : ℝ)

/-- the coefficients of `H_C(x) − (ζ(2)/4)·H_A(x)` (real) -/
def eichlerDiffC (n : ℕ) : ℝ := (HC_coeff n : ℝ) - (zeta2Real / 4) * (HA_coeff n : ℝ)

/-- **Node-(2) input (B)**: the Eichler-integral facts for `H_B` —
integrality `[1..n]²·bₙ ∈ ℤ` and overconvergence of `H_B − (L/2)H_A` to
radius `1`.  Proven in the paper by the Γ₀(6) modular/Eichler construction
(`defabc`); not derivable from the recurrences. -/
def EichlerInputB : Prop := HasDenomTypeSq HB_coeff ∧ OverconvergesUnit eichlerDiffB

/-- **Node-(2) input (C)**: the Eichler-integral facts for `H_C` —
integrality `[1..n]²·cₙ ∈ ℤ` and overconvergence of `H_C − (ζ(2)/4)H_A` to
radius `1`. -/
def EichlerInputC : Prop := HasDenomTypeSq HC_coeff ∧ OverconvergesUnit eichlerDiffC

/-- **the upgrade identity**: under the absurd `ℚ`-dependence
`a + b·L/2 + c·ζ/4 = 0`, the `n`-th coefficient of
`H = aH_A + bH_B + cH_C` (as a real number) equals
`b·(bₙ − (L/2)aₙ) + c·(cₙ − (ζ/4)aₙ)` — the `b,c`-combination of the two
overconvergent difference sequences (paper `defH`). -/
lemma zagierH_coeff_seq_eq_diff (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (L2chi3Real / 2) + (c : ℝ) * (zeta2Real / 4) = 0) (n : ℕ) :
    (ZagierH_coeff_seq a b c n : ℝ) = (b : ℝ) * eichlerDiffB n + (c : ℝ) * eichlerDiffC n := by
  have hrel' : (a : ℝ) = -(b : ℝ) * (L2chi3Real / 2) - (c : ℝ) * (zeta2Real / 4) := by
    linarith
  unfold ZagierH_coeff_seq eichlerDiffB eichlerDiffC
  push_cast
  rw [hrel']
  ring

/-- **Proposition `functionsH`, overconvergence half**: with the absurd
`ℚ`-dependence and the node-(2) inputs for `B` and `C`, the series
`H = aH_A + bH_B + cH_C` (the `H(x)` whose symmetrization `G = Sym⁺H` is
the `mainA` function) overconverges to radius `1`. -/
theorem functionsH_overconverges (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (L2chi3Real / 2) + (c : ℝ) * (zeta2Real / 4) = 0)
    (hB : OverconvergesUnit eichlerDiffB) (hC : OverconvergesUnit eichlerDiffC) :
    OverconvergesUnit (fun n => (ZagierH_coeff_seq a b c n : ℝ)) := by
  have hfunext : (fun n : ℕ => (ZagierH_coeff_seq a b c n : ℝ))
      = fun n : ℕ => (b : ℝ) * eichlerDiffB n + (c : ℝ) * eichlerDiffC n := by
    funext n
    exact zagierH_coeff_seq_eq_diff a b c hrel n
  rw [hfunext]
  exact OverconvergesUnit_add (OverconvergesUnit_smul (b : ℝ) hB)
    (OverconvergesUnit_smul (c : ℝ) hC)

/-! ## The modular conjunct of `EichlerInputB`/`EichlerInputC`: `[1..n]²`-integrality

`EichlerInputB = HasDenomTypeSq HB_coeff ∧ OverconvergesUnit eichlerDiffB`;
the overconvergence conjunct is supplied by the `(Cintegral)` module
(`Submission.CDT.L2chi3Cintegral.overconvergesB_of_cintegral`).  The
remaining — modular — conjunct is isolated here under the names
`ModularIntegralityB`/`ModularIntegralityC` (the paper's `defabc` item 2:
`[1,2,…,n]²·bₙ, [1,2,…,n]²·cₙ ∈ ℤ`).  Its proof in the paper comes from
identifying `H_B`, `H_C` with the coefficients of Γ₀(6) Eichler integrals
(weight-zero modular symmetry; the `WeilHeckeLemma` input), and is *not*
derivable from the recurrences alone.  Also proved here: the
`HasDenomTypeSq`-closure under addition/negation/integer scaling (so the
integrality assembles across linear combinations once it holds for the
atomic sequences), the `lcmRange` divisibility chain, and the **ground
checks** `HB_denomType_initial`/`HC_denomType_initial` — the exact
statement holds at the boundary with explicit integer witnesses
(`[1..1]²b₁ = 1`, `[1..2]²b₂ = 23`, `[1..3]²b₃ = 1305`,
`[1..4]²b₄ = 35937`; `[1..2]²c₂ = 24`, `[1..3]²c₃ = 1372`,
`[1..4]²c₄ = 37824`), matching the `defabc` display — and the
continuation through `n = 8` (`HB_denomType_six/seven/eight`,
`HC_denomType_six/seven/eight`, witnesses `49459563`, `18801291105`,
`594772199703` for `B`; `52065312`, `19791871920`, `626109046272` for
`C`; `lcmRange` values `60, 420, 840`).
-/

/-- **the modular conjunct of `EichlerInputB`**: `[1..n]²·bₙ ∈ ℤ` for all
`n` (paper `defabc` item 2, `H_B` half; Γ₀(6) Eichler-integral input). -/
def ModularIntegralityB : Prop := HasDenomTypeSq HB_coeff

/-- **the modular conjunct of `EichlerInputC`**: `[1..n]²·cₙ ∈ ℤ` for all
`n` (paper `defabc` item 2, `H_C` half).  The complementary
overconvergence conjunct of `EichlerInputC` is proved unconditionally in
`Submission.CDT.AintegralUntransformed` (`overconvergesC_proved`), so
`eichlerInputC_of_modular : ModularIntegralityC → EichlerInputC` needs only
this integrality — mirroring `eichlerInputB_of_modular`. -/
def ModularIntegralityC : Prop := HasDenomTypeSq HC_coeff

/-- `EichlerInputB` = modular integrality ∧ overconvergence (definitional
decomposition; the second conjunct is supplied by the `(Cintegral)` route). -/
lemma eichlerInputB_iff_parts :
    EichlerInputB ↔ ModularIntegralityB ∧ OverconvergesUnit eichlerDiffB := by
  rfl

/-- `lcmRange n ∣ lcmRange (n+1)` (the lcm chain is divisibility-growing) -/
lemma lcmRange_dvd_succ (n : ℕ) : lcmRange n ∣ lcmRange (n + 1) := by
  change lcmRange n ∣ Nat.lcm (lcmRange n) (n + 1)
  exact Nat.dvd_lcm_left (lcmRange n) (n + 1)

/-- `lcmRange m ∣ lcmRange n` for `m ≤ n` -/
lemma lcmRange_dvd_of_le {m n : ℕ} (h : m ≤ n) : lcmRange m ∣ lcmRange n := by
  induction h with
  | refl => rfl
  | step h' ih => exact dvd_trans ih (lcmRange_dvd_succ _)

/-- denominator type `[1..n]²` is closed under pointwise addition -/
lemma HasDenomTypeSq_add {f g : ℕ → ℚ} (hf : HasDenomTypeSq f) (hg : HasDenomTypeSq g) :
    HasDenomTypeSq (fun n => f n + g n) := by
  intro n
  rcases hf n with ⟨zf, hzf⟩
  rcases hg n with ⟨zg, hzg⟩
  refine ⟨zf + zg, ?_⟩
  calc
    ((lcmRange n : ℚ) ^ 2) * (f n + g n)
        = ((lcmRange n : ℚ) ^ 2) * f n + ((lcmRange n : ℚ) ^ 2) * g n := by ring
    _ = (zf : ℚ) + (zg : ℚ) := by rw [hzf, hzg]
    _ = ((zf + zg : ℤ) : ℚ) := by rw [Int.cast_add]

/-- denominator type `[1..n]²` is closed under negation -/
lemma HasDenomTypeSq_neg {f : ℕ → ℚ} (hf : HasDenomTypeSq f) :
    HasDenomTypeSq (fun n => -f n) := by
  intro n
  rcases hf n with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    ((lcmRange n : ℚ) ^ 2) * (-f n) = -(((lcmRange n : ℚ) ^ 2) * f n) := by ring
    _ = -(z : ℚ) := by rw [hz]
    _ = ((-z : ℤ) : ℚ) := by rw [Int.cast_neg]

/-- denominator type `[1..n]²` is closed under integer scaling -/
lemma HasDenomTypeSq_int_mul {f : ℕ → ℚ} (k : ℤ) (hf : HasDenomTypeSq f) :
    HasDenomTypeSq (fun n => (k : ℚ) * f n) := by
  intro n
  rcases hf n with ⟨z, hz⟩
  refine ⟨k * z, ?_⟩
  calc
    ((lcmRange n : ℚ) ^ 2) * ((k : ℚ) * f n) = (k : ℚ) * (((lcmRange n : ℚ) ^ 2) * f n) := by ring
    _ = (k : ℚ) * (z : ℚ) := by rw [hz]
    _ = ((k * z : ℤ) : ℚ) := by rw [Int.cast_mul]

/-- `H_A` has denominator type `[1..n]²` **for free** — its coefficients
`aₙ = Σₖ C(n,k)²·C(2k,k)` are integers (`HA_coeffZ`), so
`[1..n]²·aₙ ∈ ℤ` with the integer witness `[1..n]²·HA_coeffZ n`. -/
lemma HasDenomTypeSq_HA : HasDenomTypeSq HA_coeff := by
  intro n
  refine ⟨((lcmRange n : ℤ) ^ 2) * HA_coeffZ n, ?_⟩
  calc
    ((lcmRange n : ℚ) ^ 2) * HA_coeff n
        = ((lcmRange n : ℚ) ^ 2) * (HA_coeffZ n : ℚ) := by rw [HA_coeff_eq_cast]
    _ = ((((lcmRange n : ℤ) ^ 2) * HA_coeffZ n : ℤ) : ℚ) := by
          push_cast
          ring

/-- **denominator-type of an integer linear combination** (the
`functionsH`-combination with integer `a, b, c`): given the node-(2)
integrality for `H_B` and `H_C` (and the trivially-integer `H_A`), every
`H = a·H_A + b·H_B + c·H_C` with `a, b, c ∈ ℤ` has denominator type
`[1..n]²`.  Rational combinations reduce to this by clearing the common
denominator (the paper's `defH` uses the cleared combination). -/
lemma functionsH_denomtype_int (a b c : ℤ) (hB : ModularIntegralityB)
    (hC : ModularIntegralityC) :
    HasDenomTypeSq (fun n : ℕ => ZagierH_coeff_seq (a : ℚ) (b : ℚ) (c : ℚ) n) := by
  change HasDenomTypeSq
    (fun n : ℕ => (a : ℚ) * HA_coeff n + (b : ℚ) * HB_coeff n + (c : ℚ) * HC_coeff n)
  exact HasDenomTypeSq_add
    (HasDenomTypeSq_add (HasDenomTypeSq_int_mul a HasDenomTypeSq_HA)
      (HasDenomTypeSq_int_mul b hB))
    (HasDenomTypeSq_int_mul c hC)

/-- ground check of `ModularIntegralityB` at the boundary: the exact
statement holds for `n ≤ 4` with explicit witnesses (`1, 23, 1305,
35937`), matching the `defabc` display. -/
lemma HB_denomType_initial (n : ℕ) (hn : n ≤ 4) :
    ∃ z : ℤ, ((lcmRange n : ℚ) ^ 2) * HB_coeff n = (z : ℚ) := by
  interval_cases n
  · exact ⟨0, by norm_num [lcmRange, HB_coeff_zero]⟩
  · exact ⟨1, by norm_num [lcmRange, HB_coeff_one]⟩
  · exact ⟨23, by norm_num [lcmRange, HB_coeff_two]⟩
  · exact ⟨1305, by norm_num [lcmRange, HB_coeff_three]⟩
  · exact ⟨35937, by norm_num [lcmRange, HB_coeff_four]⟩

/-- ground check of `ModularIntegralityC` at the boundary: the exact
statement holds for `n ≤ 4` with explicit witnesses (`24, 1372, 37824`). -/
lemma HC_denomType_initial (n : ℕ) (hn : n ≤ 4) :
    ∃ z : ℤ, ((lcmRange n : ℚ) ^ 2) * HC_coeff n = (z : ℚ) := by
  interval_cases n
  · exact ⟨0, by norm_num [lcmRange, HC_coeff_zero]⟩
  · exact ⟨1, by norm_num [lcmRange, HC_coeff_one]⟩
  · exact ⟨24, by norm_num [lcmRange, HC_coeff_two]⟩
  · exact ⟨1372, by norm_num [lcmRange, HC_coeff_three]⟩
  · exact ⟨37824, by norm_num [lcmRange, HC_coeff_four]⟩

/-- `[1,2,3,4,5] = 60` -/
lemma lcmRange_five : lcmRange 5 = 60 := by native_decide

/-- `[1,2,3,4,5,6] = 60` -/
lemma lcmRange_six : lcmRange 6 = 60 := by native_decide

/-- `[1,2,3,4,5,6,7] = 420` -/
lemma lcmRange_seven : lcmRange 7 = 420 := by native_decide

/-- `[1,2,3,4,5,6,7,8] = 840` -/
lemma lcmRange_eight : lcmRange 8 = 840 := by native_decide

/-- **the `n = 5` obligation of `ModularIntegralityB`**: `[1..5]²·b₅ ∈ ℤ`
with explicit witness `6543531 = 3³·29·61·137`
(`b₅ = 727059/400`, `[1..5]² = 3600`, `3600·b₅ = 6543531`).  The witness's
factorization — large primes `29, 61, 137` with no divisibility pattern in
the earlier witnesses `1, 23, 1305, 35937` — shows the `[1..n]²`-integrality
is genuinely hidden arithmetic (not readable off a naive pattern of `zₙ`),
consistent with `ModularIntegralityB` being modular/Eichler-integral input. -/
lemma HB_denomType_five :
    ∃ z : ℤ, ((lcmRange 5 : ℚ) ^ 2) * HB_coeff 5 = (z : ℚ) := by
  refine ⟨6543531, ?_⟩
  norm_num [lcmRange_five, HB_coeff_five]

/-- ground check at `n = 6`: `[1..6]²·b₆ = 49459563` -/
lemma HB_denomType_six :
    ∃ z : ℤ, ((lcmRange 6 : ℚ) ^ 2) * HB_coeff 6 = (z : ℚ) := by
  refine ⟨49459563, ?_⟩
  norm_num [lcmRange_six, HB_coeff_six]

/-- ground check at `n = 7`: `[1..7]²·b₇ = 18801291105` -/
lemma HB_denomType_seven :
    ∃ z : ℤ, ((lcmRange 7 : ℚ) ^ 2) * HB_coeff 7 = (z : ℚ) := by
  refine ⟨18801291105, ?_⟩
  norm_num [lcmRange_seven, HB_coeff_seven]

/-- ground check at `n = 8`: `[1..8]²·b₈ = 594772199703` -/
lemma HB_denomType_eight :
    ∃ z : ℤ, ((lcmRange 8 : ℚ) ^ 2) * HB_coeff 8 = (z : ℚ) := by
  refine ⟨594772199703, ?_⟩
  norm_num [lcmRange_eight, HB_coeff_eight]

/-- ground check at `n = 6`: `[1..6]²·c₆ = 52065312` -/
lemma HC_denomType_six :
    ∃ z : ℤ, ((lcmRange 6 : ℚ) ^ 2) * HC_coeff 6 = (z : ℚ) := by
  refine ⟨52065312, ?_⟩
  norm_num [lcmRange_six, HC_coeff_six]

/-- ground check at `n = 7`: `[1..7]²·c₇ = 19791871920` -/
lemma HC_denomType_seven :
    ∃ z : ℤ, ((lcmRange 7 : ℚ) ^ 2) * HC_coeff 7 = (z : ℚ) := by
  refine ⟨19791871920, ?_⟩
  norm_num [lcmRange_seven, HC_coeff_seven]

/-- ground check at `n = 8`: `[1..8]²·c₈ = 626109046272` -/
lemma HC_denomType_eight :
    ∃ z : ℤ, ((lcmRange 8 : ℚ) ^ 2) * HC_coeff 8 = (z : ℚ) := by
  refine ⟨626109046272, ?_⟩
  norm_num [lcmRange_eight, HC_coeff_eight]

end

end Submission.CDT
