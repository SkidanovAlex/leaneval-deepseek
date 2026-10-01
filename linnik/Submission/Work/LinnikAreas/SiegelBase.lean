import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec
import Submission.Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le

/-!
# AREA 6 (the Siegel case of Linnik's theorem): the vocabulary

This module holds **only definitions and statements** (no proofs of the deep inputs): the weighted
class sums of HB §13, the zero sums and counting functions of the Deuring--Heilbronn analysis, and
the `Prop`s in which the inputs of AREA 6 are recorded.

It is separated from `Submission.Work.LinnikAreas.area6` (which contains the proofs) so that
lemmas *proved elsewhere* can be stated over this vocabulary without importing `area6` -- the
file holding the frozen target `Work.LinnikAreas.area6` -- and hence without an import cycle.
`area6.lean` imports this module, so every name below is also visible to any file importing
`area6`.

## Setting (HB92 §13, §14)

`L = 11/2`, `K = 3/10`, `a₀ = L - 2K = 49/10`, `𝓛 = log q`, `f = tentWeight L K`,
`λ(ρ) = (1 - Re ρ)·𝓛`, and `χ₁` is a real character mod `q` with the exceptional real zero
`β₁ = 1 - λ₁/𝓛`, `λ₁ = lamOf q β₁`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.unusedVariables false

namespace Siegel

open Work.LinnikContract

/-! ## 1. The weighted class sums and the prime extraction -/

/-- HB's tent weight `f`, supported on `(L - 2K, L]` (the `L`-window of §13). -/
noncomputable def tent (L K x : ℝ) : ℝ := Commons.NumberTheory.Linnik.tentWeight L K x

/-- `⌊q^L⌋`: the upper limit of the class sum. -/
def classLimit (q : ℕ) (L : ℝ) : ℕ := ⌊(q : ℝ) ^ L⌋₊

/-- **The weighted von Mangoldt class sum of HB §13**:
`Σ_{n ≡ a (mod q), n ≤ q^L} Λ(n)/n · f(log n / log q)`. -/
noncomputable def vmClassSum (q : ℕ) [NeZero q] (L K : ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 (classLimit q L)).filter (fun n => n ≡ a [MOD q]),
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) * tent L K (Real.log n / Real.log q)

/-- The non-prime part of `vmClassSum`. -/
noncomputable def nonPrimeClassSum (q : ℕ) [NeZero q] (L K : ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.Icc 1 (classLimit q L)).filter (fun n => n ≡ a [MOD q])).filter
      (fun n => ¬ n.Prime),
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) * tent L K (Real.log n / Real.log q)

/-- The prime part of `vmClassSum`. -/
noncomputable def primeClassSum (q : ℕ) [NeZero q] (L K : ℝ) (a : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.Icc 1 (classLimit q L)).filter (fun n => n ≡ a [MOD q])).filter
      (fun n => n.Prime),
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) * tent L K (Real.log n / Real.log q)


/-! ## 2. The API of `SiegelZero` -/

/-- A Siegel zero needs a non-principal character of level `q`, so `q ≥ 2`. -/
theorem two_le_level {q : ℕ} [NeZero q] {lamS : ℝ} (h : SiegelZero q lamS) : 2 ≤ q := by
  obtain ⟨χ, hχ1, -, -⟩ := h
  by_contra hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : q = 1 := by omega
  exact hχ1 (DirichletCharacter.level_one' χ hq1)

/-- `χ` is real (quadratic) in a Siegel zero, hence so is its primitive character. -/
theorem primitive_sq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  refine (DirichletCharacter.changeLevel_eq_one_iff χ.conductor_dvd_level).mp ?_
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]

/-- A non-principal `χ` has non-principal primitive character. -/
theorem primitive_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h1
  refine h ?_
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- `zeroMult` unfolds to: the completed L-function of the primitive character vanishes. -/
theorem completedLFunction_eq_zero_of_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {β : ℝ} (hz : zeroMult χ (β : ℂ) ≠ 0) :
    @completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter (β : ℂ) = 0 :=
  apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa only [zeroMult] using hz)

/-- The exceptional zero lies in the critical strip, so `0 < β < 1`. -/
theorem re_mem_Ioo {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {β : ℝ} (hχ : χ ≠ 1)
    (hβ1 : β < 1) (hz : zeroMult χ (β : ℂ) ≠ 0) : 0 < β :=
  (@Commons.NumberTheory.Linnik.completedL_zero_strip χ.conductor ⟨χ.conductor_ne_zero⟩
    χ.primitiveCharacter (primitive_ne_one hχ)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (β : ℂ)
    (completedLFunction_eq_zero_of_zeroMult χ hz)).1

/-- `λ₁ = (1 - β)·log q > 0` for the exceptional zero. -/
theorem lamOf_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {β : ℝ} (hχ : χ ≠ 1)
    (hβ1 : β < 1) (hz : zeroMult χ (β : ℂ) ≠ 0) : 0 < lamOf q (β : ℂ) := by
  have hq2 : 2 ≤ q := by
    by_contra h
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hq1 : q = 1 := by omega
    exact hχ (DirichletCharacter.level_one' χ hq1)
  have hβ0 : 0 < β := re_mem_Ioo hχ hβ1 hz
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  rw [lamOf, Complex.ofReal_re]
  exact mul_pos (by linarith) hlog

/-- **Siegel's theorem, in the shape used by AREA 6.**  There is an absolute constant `C > 0` such
that the `λ`-value `λ₁ = lamOf q β` of a Siegel zero of a real character of level `q` satisfies
`λ₁ ≥ C·log q/√q`.  (This is the only use of the *ineffective* Siegel bound: it makes the
polynomial error terms of the class-sum expansion -- which are `≪ q^{-1}` -- negligible against
the main term, which is of size `λ₁`.)

Proved from `LFunction_realZero_siegel_uniform` (Siegel's theorem, ε = 1/2) applied to the
primitive character, `χ.conductor ≤ q`, and `√(conductor) ≤ √q`. -/
theorem lamOf_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ (χ : DirichletCharacter ℂ q) (β : ℝ),
      χ ≠ 1 → χ ^ 2 = 1 → β < 1 → zeroMult χ (β : ℂ) ≠ 0 →
      C * Real.log q / Real.sqrt q ≤ lamOf q (β : ℂ) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform (1/2) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro q _ hq2 χ β hχ hsq hβ1 hz
  have hβ0 : 0 < β := re_mem_Ioo hχ hβ1 hz
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne : χ.primitiveCharacter ≠ 1 := primitive_ne_one hχ
  have hsq' : χ.primitiveCharacter * χ.primitiveCharacter = 1 := by
    have h2 := primitive_sq_one hsq
    rwa [pow_two] at h2
  have hzL : LFunction χ.primitiveCharacter (β : ℂ) = 0 := by
    rw [@DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.conductor
      ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter (β : ℂ)
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hβ0))),
      completedLFunction_eq_zero_of_zeroMult χ hz, zero_div]
  have hSie := hC χ.conductor χ.primitiveCharacter hprim hne hsq' β hβ0 hβ1 hzL
  have hcondnonneg : (0 : ℝ) ≤ (χ.conductor : ℝ) := Nat.cast_nonneg _
  have hcond_le : (χ.conductor : ℝ) ≤ (q : ℝ) :=
    by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hcond_pos : 0 < (χ.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hsqrt_le : Real.sqrt (χ.conductor : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hcond_le
  have h1 : (1 : ℝ) / Real.sqrt (q : ℝ) ≤ (χ.conductor : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hcondnonneg, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hcond_pos) hsqrt_le
  have h2 : C * (1 / Real.sqrt (q : ℝ)) * Real.log q ≤ (1 - β) * Real.log q :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCpos.le) hlogq.le)
      (mul_le_mul_of_nonneg_right hSie hlogq.le)
  have h3 : C * (1 / Real.sqrt (q : ℝ)) * Real.log q = C * Real.log q / Real.sqrt (q : ℝ) := by
    ring
  have hgoal : C * Real.log q / Real.sqrt (q : ℝ) ≤ lamOf q (β : ℂ) := by
    rw [lamOf, Complex.ofReal_re]
    rw [h3] at h2
    linarith [h2]
  exact hgoal


/-! ## 3. The zero sums and the counting function -/

/-- The signed box sum over *all* characters (including the principal one, whose completed
L-function is the completed `ζ`, so that its "zeros" are the zeros of `ζ` up to the finitely many
Euler factors of `q`): `Σ_χ Re(χ̄(a)·boxSum q L K R χ)`.  This is the quantity that must be
bounded away from `K²` in order to conclude that the class `a mod q` contains a prime `≤ q^L`. -/
noncomputable def signedBoxSumAll (q : ℕ) [NeZero q] (L K R : ℝ) (a : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ((starRingEnd ℂ) (χ a) * boxSum q L K R χ).re

/-- The same sum restricted to the non-principal characters (the form in which `Area2` of the
contract is stated). -/
noncomputable def signedBoxSum (q : ℕ) [NeZero q] (L K R : ℝ) (a : ℕ) : ℝ :=
  ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
    ((starRingEnd ℂ) (χ a) * boxSum q L K R χ).re

/-- **`N(t)`**: the multiplicity-weighted number of zeros, over all characters mod `q` (the
principal one included, so that the `ζ`-zeros are counted), lying in the working region
`λ(ρ) ≤ t`, `|Im ρ| ≤ 1`. -/
noncomputable def zeroCountAll (q : ℕ) [NeZero q] (t : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1
      then (zeroMult χ ρ : ℝ) else 0

open scoped Classical in
/-- **`N(t)` with the exceptional character removed**: the multiplicity-weighted number of zeros of
the completed `L`-functions of the characters mod `q` other than `χ₁` (the principal one included,
so that the `ζ`-zeros are counted) lying in the working region `λ(ρ) ≤ t`, `|Im ρ| ≤ 1`.
This is the counting function of the *Deuring--Heilbronn* zero-density estimate (the `λ₁`-saving
form), the exceptional zero itself being removed from the count. -/
noncomputable def zeroCountExcl {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase χ₁,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1
      then (zeroMult χ ρ : ℝ) else 0

open scoped Classical in
/-- `N(t,T)` with the exceptional character removed: the multiplicity-weighted number of zeros of
the completed `L`-functions of the characters mod `q` other than `χ₁` (the principal one included)
with `λ(ρ) ≤ t` and `|Im ρ|·log q ≤ T` (HB's box in the height direction).  This is the counting
function of the *log-free* zero-density estimate in the form needed for the **far** zeros. -/
noncomputable def zeroCountExclHeight {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (t T : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase χ₁,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| * Real.log q ≤ T
      then (zeroMult χ ρ : ℝ) else 0

/-- The sum of `|Hk L K ((1-ρ)𝓛)|` over the zeros *outside* the box `InBox q R` (all characters,
with multiplicity): the quantity that the class-sum expansion leaves over when only the box is
kept.  Since the complement of the box is unbounded, this sum is a `∑'` (infinite series) and not
a `∑ᶠ`: the kernel decays like `4/‖(1-ρ)𝓛‖²`, a quadratic decay against a linear growth in the
number of zeros, so the dyadic layers converge geometrically (see
`Submission.Work.LinnikAreas.siegelFarSummable`); the terms are non-negative, so the value is the
honest one whenever the series converges, and every estimate below *proves* a bound for it. -/
noncomputable def farZeroSum (q : ℕ) [NeZero q] (L K R : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑' ρ : ℂ, if InBox q R ρ then 0
      else (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * Real.log q)‖

/-- The "rest" of the zero sum: `Σ` over *all* pairs `(χ,ρ)`, `(χ,ρ) ≠ (χ₁,β₁)`, of
`mult·‖Hk L K ((1-ρ)𝓛)‖`, all heights included.  It is the sum that the assembly has to control:
the exceptional pair being excluded, every term of this sum is repelled by `β₁`. -/
noncomputable def restZeroSum {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (L K : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑' ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * Real.log q)‖
      else 0

/-- The part of `restZeroSum` with `|Im ρ| ≤ 1` (the working region of HB §13, where the
Deuring--Heilbronn repulsion is available). -/
noncomputable def restLowZeroSum {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (L K : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑' ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * Real.log q)‖
      else 0

/-- The part of `restZeroSum` with `1 < |Im ρ|`: here the kernel decay `‖Hk‖ ≤ 4e^{-a₀λ}/‖(1-ρ)𝓛‖²`
is what makes the series converge, and the counting input `PairDensityHeightInput` (with its
`T`-exponent `c' < 2`) is what makes the total `o(λ₁)`. -/
noncomputable def restHighZeroSum {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (L K : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑' ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * Real.log q)‖
      else 0

/-- The sum of `|Hk L K ((1-ρ)𝓛)|` over the zeros *inside* the box, the exceptional character
excluded (with multiplicity). -/
noncomputable def boxZeroSum {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (L K R : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase χ₁,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ InBox q R ρ
      then (zeroMult χ ρ : ℝ) * ‖Hk L K ((1 - ρ) * Real.log q)‖
      else 0


/-! ## 4. The counting functions of the Deuring--Heilbronn analysis (pair forms)

All counts below are **multiplicity weighted** (`Σ (zeroMult χ ρ : ℝ)`) and count the pairs
`(χ, ρ)` of a character `χ` mod `q` (the principal one included, so that the `ζ`-zeros are
counted) and a zero `ρ` of `L(s,χ*)`.  The only pair removed from every count is the
**exceptional pair** `(χ₁, β₁)`: the Deuring--Heilbronn density estimate improves the count of all
zeros *except* the exceptional one by a factor `λ₁` (it is the repulsion of `β₁` that produces the
improvement), and it is essential to keep `χ₁`'s *other* zeros in the count: they too are pushed
away by the repulsion, but a bound that only controls the characters `χ ≠ χ₁` cannot see this. -/

open scoped Classical in
/-- Multiplicity-weighted number of pairs `(χ,ρ)`, `(χ,ρ) ≠ (χ₁,β₁)`, with `zeroMult χ ρ ≠ 0`,
`λ(ρ) ≤ t` and `|Im ρ| ≤ 1`. -/
noncomputable def pairCount {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (t : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (zeroMult χ ρ : ℝ) else 0

open scoped Classical in
/-- Multiplicity-weighted number of pairs `(χ,ρ)`, `(χ,ρ) ≠ (χ₁,β₁)`, with `zeroMult χ ρ ≠ 0`,
`λ(ρ) ≤ t` and `|Im ρ|·𝓛 ≤ T` (the height-normalised box of HB §13). -/
noncomputable def pairCountHeight {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (t T : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q,
    ∑ᶠ ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| * Real.log q ≤ T
        ∧ ¬(χ = χ₁ ∧ ρ = β₁)
      then (zeroMult χ ρ : ℝ) else 0

/-! ## 5. The inputs of AREA 6, as `Prop`s

The five statements below are the complete input list of `Submission.Work.LinnikAreas.area6`.
`SimpleInput` (Landau's simplicity of the exceptional zero), `RepulsionInput` (Deuring--Heilbronn
repulsion) and `ExpansionInput` (HB §13 = the contract's AREA 2) are proved elsewhere in this
workspace.  The two counting estimates `PairDensityInput` and `PairDensityHeightInput` are the
Deuring--Heilbronn *log-free density estimate with the `λ₁` factor* (Principle 3 of HB92 §1
refined by the repulsion; Bombieri, *Le grand crible*, Theorem 14; Jutila 1977).  They are the
irreducible deep input of AREA 6 -- exactly as Heath-Brown (1992) says, and the reason he replaces
the `λ₁ → 0` end of §14 by [HB90]. -/

/-- **(S1) Deuring--Heilbronn repulsion, pair form.**  The exceptional real zero `β₁` of the real
character `χ₁` repels *every other zero of every `L(s,χ)`, `χ` arbitrary mod `q`, principal
included*: `λ(ρ) ≥ c·log(1/λ₁)`.  The exclusion is that of the **pair** `(χ₁,β₁)`, not merely of
the point `β₁`: no other character may vanish at `β₁` either, which is the classical "at most one
exceptional zero" statement (Landau's two-real-zeros repulsion `λ₁λ₂ ≫ 1`), a consequence of the
same Deuring--Heilbronn positivity argument.  This is Principle 2 of HB92 §1 (Graham: any
`c₂ < 3/2` in the region `σ ≥ 1 - c₂log(δ⁻¹)/(𝓛(2+|t|))`, i.e. `c = c₂/3` for `|t| ≤ 1`), and the
crucial point for AREA 6 is that it holds **down to `λ₁ → 0`** (unlike HB Theorem 4, whose bound
is capped at `(1/3)logloglog q`). -/
def RepulsionInput : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ lamOf q ρ

/-- **(S2) `λ₁`-saving log-free zero-count in the working region `|Im ρ| ≤ 1`.**  The number
(multiplicity weighted) of zeros of the completed `L`-functions of *all* characters of level `q`
(principal included), other than the exceptional pair `(χ₁,β₁)`, with `λ(ρ) ≤ t`, is
`≤ C·λ₁·e^{ct}` with `c < 49/10 = L - 2K`.

This is the log-free Deuring--Heilbronn density estimate
`Σ_χ N*(σ, T, χ) ≤ Cλ₁(qT)^{c(1-σ)}` at `T = 1` with the exceptional zero removed; the exponent
condition `c < L - 2K` is exactly what makes the weight `e^{-(L-2K)λ}` of the class-sum expansion
beat the count, and the `λ₁` factor together with the repulsion `λ(ρ) ≥ c_r log(1/λ₁)` is what
produces the power saving `λ₁^{1+δ}`, `δ = c_r(a₀ - c) > 0`, that the assembly needs. -/
def PairDensityInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, c < 49 / 10 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      pairCount χ₁ (β₁ : ℂ) t ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t)

/-- **(S2') `λ₁`-saving log-free zero-count in the full height range.**  The number (multiplicity
weighted) of zeros of the completed `L`-functions of *all* characters of level `q` (principal
included), other than the exceptional pair `(χ₁,β₁)`, with `λ(ρ) ≤ t` and `|Im ρ|·𝓛 ≤ T`, is
`≤ C·λ₁·e^{ct}·T^{c'}` with `c < 49/10 = L - 2K` and `c' < 2`.

This is the same Deuring--Heilbronn density estimate in both variables,
`Σ_χ N*(σ,T,χ) ≤ Cλ₁(qT)^{c(1-σ)}` with the `T`-exponent `c' < 2` of Jutila--Huxley
(`q^{3(1-σ)}T^{3/2}`, HB (1.4)).  The condition `c' < 2` is what makes the kernel decay
`‖Hk‖ ≤ 4e^{-(L-2K)λ}/‖(1-ρ)𝓛‖²` summable in the height: the far-zero mass is then
`≤ C·λ₁·(const)·𝓛^{c'-2} = o(λ₁)` for `q → ∞` -- a *constant* multiple of `λ₁`, which is what the
assembly needs (HB's far-zero bound `O(R^{-2})` -- Lemma 13.2 -- is *not* a multiple of `λ₁` and
is the reason HB92 §14 needs [HB90] for tiny `λ₁`). -/
def PairDensityHeightInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, c < 49 / 10 ∧ ∃ c' : ℝ, c' < 2 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
      pairCountHeight χ₁ (β₁ : ℂ) t T
        ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t) * T ^ c'


/-- **(S2'') The `λ₁`-saving log-free Deuring--Heilbronn density estimate in the *coupled* form.**
There is a threshold `q₀` such that for every real character `χ₁` mod `q ≥ q₀` carrying an
exceptional real zero `β₁` (`λ₁ ≤ 1/2`), the multiplicity-weighted number of zero-pairs other than
the exceptional pair `(χ₁,β₁)` with `λ(ρ) ≤ t` and `|Im ρ|·𝓛 ≤ T` is at most
`C·λ₁·(q·T/𝓛)^{c·t/𝓛}`:

`pairCountHeight χ₁ β₁ t T ≤ C·λ₁·(q·T/𝓛)^{c·t/𝓛}`,  `c < 49/10`.

This is the classical *coupled* form `Σ_χ N*(σ,T,χ) ≤ C·λ₁·(qT)^{c(1-σ)}` (`1 - σ = t/𝓛`) of
Bombieri, *Le grand crible*, Thm. 14, and Jutila (1977) -- the form in which the height `T` and the
modulus `q` enter only through their *product*, which is what the literature states and what
`ROUTE_LEAD.md` §3.1 route (ii) prescribes.  It is weaker than the split-exponent form
`PairDensityHeightInput` for `c·t/𝓛 > c'` and stronger for `c·t/𝓛 < c'`; in particular the
classical `(12/5)`-exponent estimate with the `λ₁` factor implies it for every `c ≥ 12/5`, and it
is what the high-zero assembly `Siegel.siegelRestHighCoupled` consumes. -/
def DHLogFreeHeightCoupled (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
      pairCountHeight χ₁ (β₁ : ℂ) t T
        ≤ C * lamOf q (β₁ : ℂ) * (((q : ℝ) * T / Real.log q) ^ (c * t / Real.log q))

/-! ### Compatibility: the first-generation counting `Prop`s

The two `Prop`s below are the counting estimates in the form in which they were first *requested*
from the fleet (`zeroCountExcl`/`zeroCountExclHeight`, i.e. counting only the characters
`χ ≠ χ₁`).  They are kept only so that the files that were written against them
(`siegelFarDensity.lean`) keep compiling; the *pair* form above (`pairCount`,
`pairCountHeight`) is what the assembly of AREA 6 uses, because `χ₁`'s own zeros other than `β₁`
must also be counted.  Kept statements are exact copies of the originals. -/

/-- **(S2-old)** `λ₁`-saving count of the zeros of the characters `≠ χ₁` with `λ ≤ t`, `|Im| ≤ 1`
(kept for compatibility; superseded by `PairDensityInput`). -/
def DensityInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, c < 49 / 10 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      zeroCountExcl (q := q) χ₁ t ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t)

/-- **(S2'-old)** the same in the height direction, for the characters `≠ χ₁` (kept for
compatibility; superseded by `PairDensityHeightInput`). -/
def FarDensityInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, c < 49 / 10 ∧ ∃ c' : ℝ, c' < 2 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
      zeroCountExclHeight (q := q) χ₁ t T
        ≤ C * lamOf q (β₁ : ℂ) * Real.exp (c * t) * T ^ c'

/-- **(S3) Simplicity of the exceptional zero** (Landau; Principle 1 of HB92 §1, effective for
`λ₁ ≤ 1/100`).  Needed because the exceptional zero enters the class sum with its multiplicity;
proved in this workspace as `Work.LinnikAreas.siegelZeroSimple`. -/
def SimpleInput : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 100 → zeroMult χ₁ (β₁ : ℂ) = 1

/-- **(S4) The class-sum expansion of HB §13.1--13.2, in the Siegel-case normalisation.**
With `L = 11/2`, `K = 3/10` (`a₀ = L - 2K = 49/10`) and `f` the tent weight supported on
`(L-2K, L]`, the weighted *prime* class sum satisfies, for the box radius `R`,
`|𝓛⁻¹ Σ_{p ≡ a (q)} (log p)/p·f(log p/𝓛) - φ(q)⁻¹(K² - Σ_χ Re(χ̄(a)·boxSum q L K R χ))| ≤ q⁻² + φ(q)⁻¹·F`,
where `F = farZeroSum q L K R` is the (multiplicity-weighted, all characters) sum of
`|Hk L K ((1-ρ)𝓛)|` over the zeros *outside* the box.  The sum over `χ` runs over *all*
characters, so the principal one contributes the `ζ`-zeros: this is what makes the error
`O(q⁻²)` (a PNT-type error `O(1/φ(q))` would be too big when `λ₁ → 0`).  The pole of the
principal `L`-function produces the main term `K²`; `q⁻²` dominates every remaining contribution
(the prime powers `p^k, k ≥ 2`, the `p | q` terms, the imprimitivity corrections), and the far
zeros are *kept* in `F` (they are estimated in the assembly from the `λ₁`-saving density
estimates).  This is the content of the contract's AREA 2, and it holds uniformly in the box
radius `R` (`q₀` depending on `R`). -/
def ExpansionInput (R : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (a : ℕ), a.Coprime q →
    |(Real.log q)⁻¹ * primeClassSum q (11 / 2) (3 / 10) a
        - (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - signedBoxSumAll q (11 / 2) (3 / 10) R a)|
      ≤ 1 / (q : ℝ) ^ 2 + (q.totient : ℝ)⁻¹ * farZeroSum q (11 / 2) (3 / 10) R

/-- **(S5) The Siegel-case zero-sum bound**: for every `q ≥ q₀` carrying a Siegel zero with
`λ₁ ≤ lamS`, the box sum and the far-zero sum together are at most `K²(1 - a₀λ₁/2)`.

This is HB92 §13--§14 re-run for `λ₁ → 0`, i.e. without the `(1/3)logloglog q` cap of HB Theorem 4
and with a far-zero bound that is a multiple of `λ₁` (the `λ₁`-saving density estimates).  Its
proof (`Submission.Work.LinnikAreas.area6`) uses:

* the repulsion `RepulsionInput`: with `Λ = c_r log(1/λ₁) > R`, the box contains *only* the
  exceptional zero, so the box sum is the single term
  `Re(χ̄₁(a)·Hk(L,K,λ₁)) ≤ Hk(L,K,λ₁) = K²e^{-a₀λ₁}(1-Kλ₁)² ≤ K²(1 - a₀λ₁/2)`;
* the working-region count `PairDensityInput` together with the repulsion: the zeros with
  `|Im ρ| ≤ 1` outside the box are counted by `N(t) ≤ Cλ₁e^{ct}` and carry the weight
  `e^{-a₀λ}`, giving `≤ C'λ₁^{1+δ}`, `δ = c_r(a₀-c) > 0`;
* the height count `PairDensityHeightInput`: the zeros with `|Im ρ|𝓛 > 𝓛` carry the weight
  `‖Hk‖ ≤ 4e^{-a₀λ}/‖(1-ρ)𝓛‖²`, giving `≤ C''λ₁𝓛^{c'-2} = o(λ₁)`;
* `SimpleInput` (multiplicity one of `β₁`) and the arithmetic
  `C x^{1+δ} < K²(1 - e^{-a₀x})` (`siegel_numeric_close`). -/
def BoxSumBound (R : ℝ) : Prop :=
  ∃ lamS : ℝ, 0 < lamS ∧ lamS ≤ 1 / 100 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ lamS → ∀ a : ℕ, a.Coprime q →
      signedBoxSumAll q (11 / 2) (3 / 10) R a + farZeroSum q (11 / 2) (3 / 10) R
        ≤ (3 / 10 : ℝ) ^ 2 * (1 - (49 / 10) * lamOf q (β₁ : ℂ) / 2)


/-! ## 6. The elementary estimates for the kernel

Everything below is proved from `‖1 - e^{-w}‖ ≤ ‖w‖` (`Re w ≥ 0`),
`Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le`, and `‖e^{w}‖ = e^{Re w}`. -/

/-- `‖1 - e^{-Kz}‖ ≤ K‖z‖` for `Re z ≥ 0`. -/
private lemma norm_one_sub_exp_neg_mul_le {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖1 - Complex.exp (-(K : ℂ) * z)‖ ≤ K * ‖z‖ := by
  have hKz : 0 ≤ ((K : ℂ) * z).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hK.le hz
  have h1 : ‖1 - Complex.exp (-((K : ℂ) * z))‖ ≤ ‖(K : ℂ) * z‖ :=
    Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le ((K : ℂ) * z) hKz
  have h3 : ‖(K : ℂ) * z‖ = K * ‖z‖ := by
    rw [norm_mul]
    have h : ‖(K : ℂ)‖ = |K| := RCLike.norm_ofReal K
    rw [h, abs_of_pos hK]
  have hw : Complex.exp (-((K : ℂ) * z)) = Complex.exp (-(K : ℂ) * z) := by rw [neg_mul]
  rw [hw, h3] at h1
  exact h1

/-- **`‖F₂(z)‖ ≤ K²`** for `Re z ≥ 0`, `K > 0`. -/
theorem F2_norm_le_K2 {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) : ‖F2 K z‖ ≤ K ^ 2 := by
  rcases eq_or_ne z 0 with h | h
  · subst h
    have hz0 : Complex.exp (-(K : ℂ) * 0) = 1 := by
      rw [mul_zero, Complex.exp_zero]
    rw [F2, hz0, sub_self, zero_div]
    have h2 : ‖((0 : ℂ) ^ 2)‖ = 0 := by simp
    rw [h2]
    exact sq_nonneg K
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr h
    have h1 := norm_one_sub_exp_neg_mul_le hK hz
    rw [F2, norm_pow, norm_div]
    have h2 : ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ ≤ K := by
      rw [div_le_iff₀ hzn]
      linarith
    have h3 : 0 ≤ ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ := by positivity
    nlinarith [h2, h3, hK]

/-- **`‖F₂(z)‖ ≤ 4/‖z‖²`** for `Re z ≥ 0`, `K > 0`, `z ≠ 0`. -/
theorem F2_norm_le_invSq {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) (hzn : z ≠ 0) :
    ‖F2 K z‖ ≤ 4 / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzn
  have hnorm : ‖Complex.exp (-(K : ℂ) * z)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    have h1 : (-(K : ℂ) * z).re = -(K * z.re) := by
      rw [neg_mul]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] <;> ring
    rw [h1]
    nlinarith [hz, hK]
  have hN : ‖1 - Complex.exp (-(K : ℂ) * z)‖ ≤ 2 := by
    have h1 : ‖1 - Complex.exp (-(K : ℂ) * z)‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(K : ℂ) * z)‖ := norm_sub_le _ _
    rw [norm_one] at h1
    linarith
  rw [F2, norm_pow, norm_div]
  have h2 : ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ ≤ 2 / ‖z‖ := by
    rw [div_le_div_iff_of_pos_right hzpos]
    exact hN
  have h3 : 0 ≤ ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ := by positivity
  calc (‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖) ^ 2
      ≤ (2 / ‖z‖) ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ = 4 / ‖z‖ ^ 2 := by rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]

/-- **`‖Hk L K z‖ ≤ K²e^{-(L-2K)Re z}`** for `Re z ≥ 0`. -/
theorem Hk_norm_le_K2 {L K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Hk L K z‖ ≤ K ^ 2 * Real.exp (-(L - 2 * K) * z.re) := by
  have h1 := F2_norm_le_K2 (K := K) hK hz
  have hexp : 0 ≤ Real.exp (-(L - 2 * K) * z.re) := Real.exp_nonneg _
  rw [Hk, norm_mul, Complex.norm_exp]
  have hre : (-(((L - 2 * K : ℝ)) : ℂ) * z).re = -(L - 2 * K) * z.re := by
    rw [neg_mul]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] <;> ring
  rw [hre]
  calc Real.exp (-(L - 2 * K) * z.re) * ‖F2 K z‖
      ≤ Real.exp (-(L - 2 * K) * z.re) * K ^ 2 := mul_le_mul_of_nonneg_left h1 hexp
    _ = K ^ 2 * Real.exp (-(L - 2 * K) * z.re) := by ring

/-- **`‖Hk L K z‖ ≤ 4e^{-(L-2K)Re z}/‖z‖²`** for `Re z ≥ 0`, `z ≠ 0`. -/
theorem Hk_norm_le_invSq {L K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) (hzn : z ≠ 0) :
    ‖Hk L K z‖ ≤ 4 * Real.exp (-(L - 2 * K) * z.re) / ‖z‖ ^ 2 := by
  have h1 := F2_norm_le_invSq (K := K) hK hz hzn
  have hexp : 0 ≤ Real.exp (-(L - 2 * K) * z.re) := Real.exp_nonneg _
  rw [Hk, norm_mul, Complex.norm_exp]
  have hre : (-(((L - 2 * K : ℝ)) : ℂ) * z).re = -(L - 2 * K) * z.re := by
    rw [neg_mul]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] <;> ring
  rw [hre]
  calc Real.exp (-(L - 2 * K) * z.re) * ‖F2 K z‖
      ≤ Real.exp (-(L - 2 * K) * z.re) * (4 / ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hexp
    _ = 4 * Real.exp (-(L - 2 * K) * z.re) / ‖z‖ ^ 2 := by ring

/-- `Re ((1-ρ)𝓛) = λ(ρ)`. -/
lemma re_one_sub_mul_log {q : ℕ} (ρ : ℂ) : ((1 - ρ) * (Real.log q : ℂ)).re = lamOf q ρ := by
  rw [lamOf, Complex.mul_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    mul_zero]
  ring

/-- The kernel bound in the form used by the assembly: on a zero `ρ` with `Re ρ < 1` and
`1 < q`, `‖Hk L K ((1-ρ)𝓛)‖ ≤ K²e^{-(L-2K)λ(ρ)}`. -/
theorem Hk_norm_le_exp_lamOf {q : ℕ} [NeZero q] {L K : ℝ} (hK : 0 < K) (hq : 1 < q) {ρ : ℂ}
    (hρ : ρ.re < 1) :
    ‖Hk L K ((1 - ρ) * (Real.log q : ℂ))‖ ≤ K ^ 2 * Real.exp (-(L - 2 * K) * lamOf q ρ) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hre : 0 ≤ ((1 - ρ) * (Real.log q : ℂ)).re := by
    rw [re_one_sub_mul_log]
    exact mul_nonneg (by linarith) hlog.le
  have h1 := Hk_norm_le_K2 (L := L) (K := K) hK hre
  rwa [re_one_sub_mul_log] at h1

/-- The kernel bound in the form used for the far zeros: on a zero `ρ` with `Re ρ < 1` and
`1 < q`, `‖Hk L K ((1-ρ)𝓛)‖ ≤ 4e^{-(L-2K)λ(ρ)}/‖(1-ρ)𝓛‖²`. -/
theorem Hk_norm_le_invSq_lamOf {q : ℕ} [NeZero q] {L K : ℝ} (hK : 0 < K) (hq : 1 < q) {ρ : ℂ}
    (hρ : ρ.re < 1) :
    ‖Hk L K ((1 - ρ) * (Real.log q : ℂ))‖
      ≤ 4 * Real.exp (-(L - 2 * K) * lamOf q ρ) / ‖(1 - ρ) * (Real.log q : ℂ)‖ ^ 2 := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hre : 0 ≤ ((1 - ρ) * (Real.log q : ℂ)).re := by
    rw [re_one_sub_mul_log]
    exact mul_nonneg (by linarith) hlog.le
  have hne : (1 - ρ) * (Real.log q : ℂ) ≠ 0 := by
    intro h
    have h2 : ((1 - ρ) * (Real.log q : ℂ)).re = 0 := by rw [h]; simp
    rw [re_one_sub_mul_log] at h2
    have h3 : 0 < lamOf q ρ := by
      rw [lamOf]; exact mul_pos (by linarith) hlog
    linarith
  have h1 := Hk_norm_le_invSq (L := L) (K := K) hK hre hne
  rwa [re_one_sub_mul_log] at h1

end Siegel

end

end Work.LinnikAreas
