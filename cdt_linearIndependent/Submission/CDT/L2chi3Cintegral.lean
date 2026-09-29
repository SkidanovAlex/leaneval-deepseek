import Mathlib
import Submission.CDT.ZagierHBC
import Submission.CDT.L2chi3Real
import Submission.CDT.EichlerInput
import Submission.Commons.Analysis.Real.cubeKernel_le
import Submission.Commons.Analysis.Integral.squareInverseKernelDoubleIntegral

/-!
# The `(Cintegral)` representation of `L(2,χ₋₃)·H_A − 2·H_B` — first integral lemma of the analytic route to node (2)

The paper (Remark after Proposition `functionsH`, display
`(Cintegral)`) represents the overconvergent difference series on the
`H_B`-side as a double integral over the unit square:

```lean
L(2,χ₋₃)·H_A(x) − 2·H_B(x) = Σₙ xⁿ · Jₙ,
Jₙ := ∫₀¹∫₀¹  9ⁿ·sⁿ·tⁿ·(1−s³)ⁿ·(1−t³)ⁿ / (1+st+s²t²)^(2n+1)  ds dt,
```

and notes that the kernel maximum `max_{[0,1]²} |9st(1−s³)(1−t³)/
(1+st+s²t²)²| = 1` (attained at `s = t = 1/2`) bounds every `Jₙ` by `1`,
"which gives a transparent proof that the functions `H(x)` … overconverge
beyond the singularity at `x = 1/9` to the entire unit disc".  This module
pins down that representation and its overconvergence consequence:

* `cintegralKernel` / `cintegralJ` — the summand and the `n`-th double
  integral (real, iterated interval integrals over `[0,1]`);
* `CintegralIdentityAt n : Prop` and `CintegralIdentity : Prop` — the
  coefficient identity `L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` at a single degree `n`,
  resp. for every `n`.  The **`n ≤ 23` instances are PROVED** (see the
  `Status` bullets and the per-degree modules `CintegralOne`–`CintegralTwentyThree`):
  `CintegralIdentity_zero` (`J₀ = ∫∫ dsdt/(1+st+s²t²) = L(2,χ₋₃)` via
  `cintegralJ_zero_unfold` + `squareInverseKernelDoubleIntegral`
  (commons, L61) + `squareSum_eq_L2chi3` — the square-period identity
  adjacent to the period work in `L2chi3Real`/`L2chi3Real_integral`), and
  — module `Submission.CDT.CintegralOne`, whose two displayed theorems are
  `cintegralJ_one_eq_sum_W` (`J₁ = Σₘ W(m)`) and `cintegral_identity_one`
  (`CintegralIdentityOne`, i.e. `3·L(2,χ₋₃) − 2 = J₁`), with the first
  instances assembled as `cintegral_identity_le_one` (every `n ≤ 1`).
  The remaining cases are the Beukers-style evaluations of the double
  integral for `n ≥ 24`; the whole tail is *reduced to one parametric
  statement* by `Submission.CDT.CintegralGeneral`
  (`cintegralJ_eq_sum_W_gen` + `CintegralIdentity_of_genW_sum`, and
  `CintegralAssembled.CintegralIdentity_of_recurrence`) — see the
  "How the tail is being closed" block below;
* `cintegralKernel_le_one : Prop` — the pointwise kernel bound
  `9st(1−s³)(1−t³) ≤ (1+st+s²t²)²` on `[0,1]²` (a two-variable
  polynomial inequality; numerically verified, `(1/2,1/2)` is the only
  equality);
* `cintegralJ_bound` — `|Jₙ| ≤ 1` for all `n` — is **PROVED**
  (`cintegralJ_bound'`): the pointwise kernel bound
  (`cintegralKernel_nonneg`, `cintegralKernel_le_one'`, hence
  `cintegralKernel_abs_le_one`, all from the commons `cubeKernel_le`)
  plus the Mathlib interval-integral norm estimate
  `norm_integral_le_of_norm_le_const` applied at the inner level
  (`inner_cintegralJ_abs`) and the outer level;
* **`overconvergesB_of_cintegral`** (PROVED here): `CintegralIdentity` +
  `cintegralJ_bound` imply `OverconvergesUnit eichlerDiffB` — discharging
  the *overconvergence conjunct* of `EichlerInputB` (`EichlerInput`) for
  the `H_B`-side of node (2) of `mainA`'s proof, contingent only on the
  Beukers evaluation `CintegralIdentity`.

**Status of the `n = 1` case (`CintegralIdentityOne`: `3·L(2,χ₋₃) − 2 =
J₁`).**  **PROVED in full** (module `Submission.CDT.CintegralOne`); the two
displayed theorems there are `cintegralJ_one_eq_sum_W`
(`J₁ = Σₘ W(m)`) and `cintegral_identity_one : CintegralIdentityOne`.
Mathematically: expand the kernel by the binomial series
`(1−u³)^{-3} = Σₘ C(m+2,2)u^{3m}` (`u = st`) so that
`kernel₁(s,t) = Σₘ Aₘ(s,t)` with
`Aₘ(s,t) = 9·((m+1)(m+2)/2)·(st)^{3m+1}·(1−st)³·(1−s³)(1−t³) ≥ 0`;
two 1D Bochner interchanges (`integral_tsum_interval`, in `t` for a.e. `s`,
then in `s` — absolute summability of the inner norms from the binomial
series, of the outer ones from `sum_cintegralOne_core`) reduce `J₁` to
`Σₘ ∫∫Aₘ`; expanding `(1−st)³ = Σᵢ₌₀³(−1)ⁱC(3,i)(st)ⁱ` and using the
monomial integrals `∫₀¹ x^q(1−x³)dx = 3/((q+1)(q+4))` gives the rational
closed form `∫∫Aₘ = W(m)`, and the commons identity
`Commons.Analysis.Summation.sum_cintegralOne_core`
(`Σₘ W(m) = 3·Σₖ(1/(3k+1)² − 1/(3k+2)²) − 2`) together with
`squareSum_eq_L2chi3` closes `CintegralIdentityOne` via
`CintegralIdentityOne_eq`.

**Status (all three `Prop`s of this module are now PROVED, with no `axiom`
and no `sorry`).**  `cintegralKernel_le_one` comes from the commons
`cubeKernel_le` (fleet L57); `cintegralJ_bound` is `cintegralJ_bound'`
(the kernel bound plus `norm_integral_le_of_norm_le_const` at both levels);
and `CintegralIdentity` is **proved for all `n`** as `CintegralIdentity_proved`
(`CintegralAssembled`) from the parametric divergence certificate
`Commons.Analysis.Integral.cintegral_recurrence_parametric` (fleet L130)
via the reduction `CintegralIdentity_of_recurrence`.  Consequently the
analytic (overconvergence) conjunct of `EichlerInputB` is *unconditional*:
`overconvergesB_proved : OverconvergesUnit eichlerDiffB`, and
`EichlerInputB` follows from its modular (`[1..n]²`-integrality) conjunct
alone (`eichlerInputB_of_modular`).  The ζ-side analogue (the paper's
`(Aintegral)` display) is stated in module `Submission.CDT.Aintegral` and is
**PROVED for all `n`** in module `Submission.CDT.AintegralAssembled`
(`AintegralIdentity_proved`), whence the transformed ζ-side overconvergence
`overconvergesCtr_proved`.
-/

namespace Submission.CDT

noncomputable section

/-- the `(Cintegral)` summand kernel `9ⁿsⁿtⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}` -/
def cintegralKernel (n : ℕ) (s t : ℝ) : ℝ :=
  (9 : ℝ) ^ n * s ^ n * t ^ n * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n
    / (1 + s * t + s ^ 2 * t ^ 2) ^ (2 * n + 1)

/-- the `n`-th `(Cintegral)` double integral `Jₙ = ∫₀¹∫₀¹ kernel ds dt` -/
def cintegralJ (n : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, cintegralKernel n s t

/-- **`(Cintegral)`, coefficient form at a single degree `n`**:
`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ`. -/
def CintegralIdentityAt (n : ℕ) : Prop :=
  L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ) = cintegralJ n

/-- **`(Cintegral)`, coefficient form**: for every `n`,
`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ`.  **PROVED for all `n`** —
`CintegralIdentity_proved` (`CintegralAssembled`), from the parametric
divergence certificate `Commons.Analysis.Integral.cintegral_recurrence_parametric`
via `CintegralIdentity_of_recurrence`.  (Independently, the instances at
`n ≤ 35` are proved directly, see
`CintegralIdentity_zero` here, the modules `Submission.CDT.CintegralOne` —
`CintegralTwentyThree`, assembled as `cintegral_identity_le_twentyThree` in
`Submission.CDT.CintegralAssembled`), and the whole tail is *reduced to a
single parametric statement* by `Submission.CDT.CintegralGeneral`
(`cintegralJ_eq_sum_W_gen`, `CintegralIdentity_of_genW_sum`) and by
`CintegralIdentity_of_recurrence`; the `n ≥ 28` instances remain). -/
def CintegralIdentity : Prop :=
  ∀ n : ℕ, CintegralIdentityAt n

/-- `CintegralIdentity` is the conjunction of its single-degree instances -/
lemma CintegralIdentity_iff_at : CintegralIdentity ↔ ∀ n : ℕ, CintegralIdentityAt n := by
  rfl

/-- the **missing tail of `CintegralIdentity`**: the instances at degrees
`n ≥ 2` (the instances at `n ≤ 31` are PROVED — `CintegralIdentity_zero`
and modules `Submission.CDT.CintegralOne`–`CintegralTwentySeven`, assembled as
`cintegral_identity_le_thirtyOne` (`CintegralAssembled`); hence
`CintegralIdentity ↔ CintegralIdentityTail` once the adjoined `n ≤ 31`
instances are used, see `CintegralOne.cintegralIdentity_iff_tail`). -/
def CintegralIdentityTail : Prop := ∀ n : ℕ, 2 ≤ n → CintegralIdentityAt n

/-!
**How the tail is being closed.**  The known instances
(`J₀ = L`, `J₁ = 3L − 2`, `J₂ = 15L − 23/2`, `J₃ = 93L − 145/2`,
`J₄ = 639L − 3993/8`, `J₅ = 4653L − 727059/200`,
`J₆ = 35169L − 5495507/200`, `J₇ = 272835L − 417806469/1960`,
`J₈ = 2157759L − 66085799967/39200`, `J₉ = 17319837L − 530455590781/39200`,
`J₁₀ = 140668065L − 4308248502993/39200`,
`J₁₁ = 1153462995L − 4274588067098379/4743200`,
`J₁₂ = 9533639025L − 1413218448827853/189728`,
`J₁₃ = 79326566595L − 49681644752988856791/801600800`,
`J₁₄ = 663835030335L − 415754993154999572883/801600800`,
`J₁₅ = 5582724468093L − 699283848231726007461/160320160`,
`J₁₆ = 47152425626559L − 2147724879365145978567/58298240`,
`J₁₇ = 399769750195965L − 11577240673264126122251355/37066020992`,
… and (NEW) the instances at `n = 18, …, 27` in modules
`CintegralEighteen`–`CintegralTwentySeven`) satisfy — and numerical checks
confirm — the **Zagier 3-term recurrence**
`(n+1)²·J_{n+1} = (10n²+10n+3)·Jₙ − 9n²·J_{n−1}`, i.e. exactly the
recurrence of the `HA` coefficients (`HA_coeff_recurrence`, commons
`zagierC_recurrence`) and of the `HB` coefficients
(`HB_coeff_recurrence`).  Since `L·aₙ − 2·bₙ` satisfies that same
recurrence (it is linear in `aₙ`, `bₙ`, both of which do), the whole
`CintegralIdentity` follows by induction on `n` from the two base
instances `n = 0, 1` — **provided** the parametric identity
`(n+1)²·J_{n+1} = (10n²+10n+3)·Jₙ − 9n²·J_{n−1}` (`∀ n ≥ 1`) is proved
(see `CintegralAssembled.CintegralIdentity_of_recurrence`).

**What is now PROVED parametrically** (module `Submission.CDT.CintegralGeneral`):
the general-`n` **Beukers expansion** of the period integral,

`cintegralJ_eq_sum_W_gen : ∀ n, cintegralJ n = Σ'ₘ genW n m`, with
`genW n m = 9ⁿ·C(m+2n,2n)·Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)·(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²`

(together with the summability `genW_summable` and the reduction
`CintegralIdentity_of_genW_sum`).  So the *entire* remaining content of the
analytic-B route is the single parametric `m`-sum evaluation

`∀ n, Σ'ₘ genW n m = L(2,χ₋₃)·aₙ − 2·bₙ`   (equivalently, the recurrence above),

of which the commons creative-telescoping identities
`sum_cintegral<N>_core` provide one degree at a time (they are combined with
`cintegralJ_eq_sum_W_gen` by the *light* per-degree modules
`CintegralTwo`–`CintegralTwentySeven`, generated by
`Scratch/cintegral_generator/mklight_all.py` — a ~90-line module per degree;
the earlier ~800-line analytic template is archived in
`Scratch/archive_heavy/`).
-/


/-!
**The recurrence has an explicit divergence certificate — `(Cintegral)` is
PROVED.**  The parametric Zagier recurrence
`(n+1)²·J_{n+1} = (10n²+10n+3)·Jₙ − 9n²·J_{n−1}` is proved in the commons
(`Commons.Analysis.Integral.cintegral_recurrence_parametric`, fleet L130) by
an explicit *divergence certificate* for the integrand family
`Kₙ = 9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}`: with

* `W = st(1−s³)(1−t³)`, `R = 1+st+s²t²`, `P(n,s,t) = P₀(s,t) + n·P₁(s,t)`
  (explicit degree-8 polynomials),
* `Aₙ = 9ⁿ·W^{n−1}·P(n,s,t)/R^{2n+2}`, `Bₙ = 9ⁿ·W^{n−1}·P(n,t,s)/R^{2n+2}`

one has the *pointwise* identity `∂_sAₙ + ∂_tBₙ = (n+1)²K_{n+1} − (10n²+10n+3)Kₙ + 9n²K_{n−1}`,
and `Aₙ` (resp. `Bₙ`) vanishes on `s = 0,1` (resp. `t = 0,1`), so integrating
over the square gives the recurrence for every `n ≥ 1`.  Through
`CintegralIdentity_of_recurrence` (`CintegralAssembled`) this *closes the whole
`(Cintegral)` identity*: `CintegralIdentity_proved : CintegralIdentity` (=
`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` for all `n`), and hence the `H_B`-side
overconvergence of node (2), `overconvergesB_proved :
OverconvergesUnit eichlerDiffB` — the analytic half of `EichlerInputB` is now
unconditional (`eichlerInputB_of_modular`).

*Historical note (a false alarm, recorded so that nobody repeats it).*  A
plausible "no certificate" argument was explored first and is *wrong*: in the
coordinates `(s,u)`, `u = st`, exactness of `Eₙ dsdt` is equivalent to
`F = ∂_sÃ + ∂_uB̃` for `F = Eₙ(s,u/s)/s`, so the residue
`c₁(s) := Res_{u=ω}F(s,u)` (`1+u+u² = (u−ω)(u−ω²)`) must be the `s`-derivative
of a rational function.  For `n = 0` one computes
`c₁(s) = −(2ω+1)(100s¹² − 109s⁹ − 262s³ + 280)/(3s⁷)` (verified against a
contour-integral evaluation of the residue, 50 digits).  The polynomial
`100x⁴ − 109x³ − 262x + 280` (in `x = s³`) is squarefree — but its roots are
**zeros of the numerator**, not poles: `c₁` has a single pole, at `s = 0`, of
order `7`, so `c₁ = ∂_s b₁` is perfectly possible (and is exactly what the
certificate supplies).  The wrong reading ("simple poles with nonzero
residues") produced a spurious obstruction.
-/

/-- **kernel maximum**: `9st(1−s³)(1−t³) ≤ (1+st+s²t²)²` on `[0,1]²`
(equality exactly at `s = t = 1/2`).  PROVED via the commons lemma
`Commons.Analysis.Real.cubeKernel_le` (fleet L57): the pointwise bound
behind `cintegralJ_bound`. -/
lemma cintegralKernel_le_one (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    9 * s * t * (1 - s ^ 3) * (1 - t ^ 3) ≤ (1 + s * t + s ^ 2 * t ^ 2) ^ 2 := by
  exact Commons.Analysis.Real.cubeKernel_le hs0 hs1 ht0 ht1

/-- **the double integrals are bounded**: `|Jₙ| ≤ 1` for every `n`
(provable target: kernel bound + `|∫∫f| ≤ ∫∫|f| ≤ ∫∫1 = 1`). -/
def cintegralJ_bound : Prop :=
  ∀ n : ℕ, |cintegralJ n| ≤ 1

/-- the bridge: `(Cintegral)` + the kernel/integral bounds imply the
`H_B`-overconvergence of node (2): `OverconvergesUnit eichlerDiffB`
(= radius-≥1 overconvergence of `H_B − (L(2,χ₋₃)/2)·H_A`), which is the
overconvergence conjunct of `EichlerInputB`. -/
theorem overconvergesB_of_cintegral (hId : CintegralIdentity) (hBd : cintegralJ_bound) :
    OverconvergesUnit eichlerDiffB := by
  unfold OverconvergesUnit
  intro r hr0 hr1
  refine ⟨1, zero_lt_one, ?_⟩
  intro n
  -- eichlerDiffB n = bₙ − (L/2)aₙ = −(L·aₙ − 2·bₙ)/2 = −Jₙ/2
  have hdiff : eichlerDiffB n = -(cintegralJ n) / 2 := by
    unfold eichlerDiffB
    have hring : (HB_coeff n : ℝ) - (L2chi3Real / 2) * (HA_coeff n : ℝ)
        = -((L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ))) / 2 := by
      ring
    rw [hId n] at hring
    exact hring
  calc
    |eichlerDiffB n| = |-(cintegralJ n) / 2| := by rw [hdiff]
    _ = |cintegralJ n| / 2 := by
          simp [abs_div, abs_neg]
    _ ≤ 1 / 2 := by
          exact div_le_div_of_nonneg_right (hBd n) (by norm_num)
    _ ≤ 1 := by norm_num
    _ ≤ 1 / r ^ n := by
          have hden : 0 < r ^ n := pow_pos hr0 n
          rw [one_le_div hden]
          exact pow_le_one₀ (le_of_lt hr0) (le_of_lt hr1)

/-- **node (2), `H_B`-half assembled**: `EichlerInputB` splits into its
modular conjunct (`ModularIntegralityB`: `[1..n]²·bₙ ∈ ℤ`, to be supplied
by the Γ₀(6)/Eichler-integral theory) and its analytic conjunct
(supplied here by the `(Cintegral)` targets via
`overconvergesB_of_cintegral`). -/
theorem eichlerInputB_of_modular_and_cintegral (hMod : ModularIntegralityB)
    (hId : CintegralIdentity) (hBd : cintegralJ_bound) : EichlerInputB := by
  constructor
  · exact hMod
  · exact overconvergesB_of_cintegral hId hBd

end

/-! ## `cintegralJ_bound`: kernel bound + interval-integral norm estimate

`cintegralJ_bound` (`|Jₙ| ≤ 1`) now follows from (a) the pointwise kernel
bounds `0 ≤ k ≤ 1` on `[0,1]²` (from the commons `cubeKernel_le`) and
(b) the Mathlib interval-integral norm estimate
`intervalIntegral.norm_integral_le_of_norm_le_const` (no integrability
hypotheses needed — boundedness of the integrand bounds the integral).
-/

/-- `1 + s·t + s²·t² > 0` for all reals (the kernel denominator) -/
lemma cintegral_den_pos (s t : ℝ) : 0 < 1 + s * t + s ^ 2 * t ^ 2 := by
  have hsq : 0 ≤ (s * t + 1 / 2) ^ 2 := sq_nonneg (s * t + 1 / 2)
  nlinarith

/-- kernel numerator `9·s·t·(1−s³)·(1−t³) ≥ 0` on `[0,1]²` -/
lemma cintegral_num_nonneg {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ 9 * s * t * (1 - s ^ 3) * (1 - t ^ 3) := by
  have h1s : 0 ≤ 1 - s ^ 3 := by
    have hsp : s ^ 3 ≤ 1 := pow_le_one₀ hs0 hs1
    linarith
  have h1t : 0 ≤ 1 - t ^ 3 := by
    have htp : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
    linarith
  have h9s : 0 ≤ 9 * s := mul_nonneg (by norm_num) hs0
  have h9st : 0 ≤ (9 * s) * t := mul_nonneg h9s ht0
  have h1 : 0 ≤ ((9 * s) * t) * (1 - s ^ 3) := mul_nonneg h9st h1s
  exact mul_nonneg h1 h1t

/-- `k = Nⁿ / d^{2n+1}` with `N = 9st(1−s³)(1−t³)`, `d = 1+st+s²t²` -/
lemma cintegralKernel_eq_pow (n : ℕ) (s t : ℝ) :
    cintegralKernel n s t =
      (9 * s * t * (1 - s ^ 3) * (1 - t ^ 3)) ^ n
        / (1 + s * t + s ^ 2 * t ^ 2) ^ (2 * n + 1) := by
  unfold cintegralKernel
  have hnp : (9 * s * t * (1 - s ^ 3) * (1 - t ^ 3)) ^ n
      = (9 : ℝ) ^ n * s ^ n * t ^ n * (1 - s ^ 3) ^ n * (1 - t ^ 3) ^ n := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow]
  rw [← hnp]

/-- the kernel is nonnegative on `[0,1]²` -/
lemma cintegralKernel_nonneg (n : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ cintegralKernel n s t := by
  rw [cintegralKernel_eq_pow]
  exact div_nonneg (pow_nonneg (cintegral_num_nonneg hs0 hs1 ht0 ht1) n)
    (le_of_lt (pow_pos (cintegral_den_pos s t) (2 * n + 1)))

/-- the kernel is bounded by `1` on `[0,1]²` -/
lemma cintegralKernel_le_one' (n : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : cintegralKernel n s t ≤ 1 := by
  let N : ℝ := 9 * s * t * (1 - s ^ 3) * (1 - t ^ 3)
  let d : ℝ := 1 + s * t + s ^ 2 * t ^ 2
  have hnum : N ≤ d ^ 2 := by
    dsimp [N, d]
    exact Commons.Analysis.Real.cubeKernel_le hs0 hs1 ht0 ht1
  have hN0 : 0 ≤ N := by
    dsimp [N]
    exact cintegral_num_nonneg hs0 hs1 ht0 ht1
  have hd0 : 0 < d := by
    dsimp [d]
    exact cintegral_den_pos s t
  have hd1 : 1 ≤ d := by
    dsimp [d]
    have hst : 0 ≤ s * t := mul_nonneg hs0 ht0
    nlinarith [sq_nonneg (s * t)]
  have hNpow : N ^ n ≤ (d ^ 2) ^ n := pow_le_pow_left₀ hN0 hnum n
  have hd2n : (d ^ 2) ^ n = d ^ (2 * n) := (pow_mul d 2 n).symm
  have hk : cintegralKernel n s t = N ^ n / d ^ (2 * n + 1) := by
    dsimp [N, d]
    exact cintegralKernel_eq_pow n s t
  calc
    cintegralKernel n s t = N ^ n / d ^ (2 * n + 1) := hk
    _ ≤ d ^ (2 * n) / d ^ (2 * n + 1) := by
          rw [hd2n] at hNpow
          exact div_le_div_of_nonneg_right hNpow (le_of_lt (pow_pos hd0 (2 * n + 1)))
    _ = 1 / d := by
          have hsucc : 2 * n + 1 = Nat.succ (2 * n) := by omega
          rw [hsucc, pow_succ]
          field_simp [ne_of_gt hd0]
    _ ≤ 1 := by
          exact (div_le_one hd0).2 hd1


/-- the kernel has absolute value ≤ 1 on `[0,1]²` -/
lemma cintegralKernel_abs_le_one (n : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |cintegralKernel n s t| ≤ 1 := by
  rw [abs_of_nonneg (cintegralKernel_nonneg n hs0 hs1 ht0 ht1)]
  exact cintegralKernel_le_one' n hs0 hs1 ht0 ht1

/-- for `s ∈ [0,1]` the inner integral is bounded by 1 -/
lemma inner_cintegralJ_abs (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(∫ t in (0 : ℝ)..1, cintegralKernel n s t)| ≤ 1 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 1) (f := fun t : ℝ => cintegralKernel n s t) (by
        intro x hx
        have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        rcases Set.mem_Ioc.mp hx' with ⟨hx0, hx1⟩
        exact cintegralKernel_abs_le_one n hs0 hs1 (le_of_lt hx0) hx1)
  simpa using hb

/-- **`cintegralJ_bound` is proved**: the double integrals are bounded by
`1` (kernel ≤ 1 pointwise on `[0,1]²` + `norm_integral_le_of_norm_le_const`
at each of the two levels).  Together with `CintegralIdentity` this
discharges the overconvergence conjunct of `EichlerInputB`
(`overconvergesB_of_cintegral`). -/
theorem cintegralJ_bound' : cintegralJ_bound := by
  unfold cintegralJ_bound
  intro n
  unfold cintegralJ
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 1)
      (f := fun s : ℝ => (∫ t in (0 : ℝ)..1, cintegralKernel n s t)) (by
        intro s hs
        have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
        rcases Set.mem_Ioc.mp hs' with ⟨hs0, hs1⟩
        simpa using (inner_cintegralJ_abs n (le_of_lt hs0) hs1))
  simpa using hb


/-- `J₀ = ∫₀¹∫₀¹ ds dt / (1+st+s²t²)` (the `n = 0` kernel is
`1/(1+st+s²t²)`) -/
lemma cintegralJ_zero_unfold :
    cintegralJ 0 = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      (1 : ℝ) / (1 + s * t + s ^ 2 * t ^ 2) := by
  rw [show cintegralJ 0 = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      cintegralKernel 0 s t by rfl]
  apply intervalIntegral.integral_congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  unfold cintegralKernel
  simp


/-- the paired-square tsum equals `L(2,χ₋₃)` (assembly of
`pairSum_eq_sq` and `L2chi3Real_eq_pair_tsum`) -/
lemma squareSum_eq_L2chi3 :
    (∑' k : ℕ,
        ((1 : ℝ) / (((3 * k + 1 : ℕ) : ℝ) ^ 2)
          - (1 : ℝ) / (((3 * k + 2 : ℕ) : ℝ) ^ 2))) = L2chi3Real := by
  rw [L2chi3Real_eq_pair_tsum]
  congr 1
  funext k
  exact (pairSum_eq_sq k).symm


/-- **`(Cintegral)` case `n = 0`**: `J₀ = L(2,χ₋₃)` (the double square
integral of `1/(1+st+s²t²)` equals the paired square series — commons
`squareInverseKernelDoubleIntegral` (fleet L61) — which equals
`L2chi3Real` by `squareSum_eq_L2chi3`). -/
lemma cintegralJ_zero_eq : cintegralJ 0 = L2chi3Real := by
  rw [cintegralJ_zero_unfold]
  rw [Commons.Analysis.Integral.squareInverseKernelDoubleIntegral]
  exact squareSum_eq_L2chi3

/-- **first instance of `CintegralIdentity` (the `n = 0` case)**:
`L(2,χ₋₃)·a₀ − 2·b₀ = J₀`, i.e. `L(2,χ₋₃) = J₀`. -/
theorem CintegralIdentity_zero :
    L2chi3Real * (HA_coeff 0 : ℝ) - 2 * (HB_coeff 0 : ℝ) = cintegralJ 0 := by
  rw [cintegralJ_zero_eq]
  simp [HA_coeff_zero, HB_coeff_zero]


/-- `J₁ = ∫₀¹∫₀¹ ds dt · 9st(1−s³)(1−t³)/(1+st+s²t²)³` — the explicit
`n = 1` double integral (the `(Cintegral)` summand for `n = 1`). -/
lemma cintegralJ_one_unfold :
    cintegralJ 1 = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      (9 : ℝ) * s * t * (1 - s ^ 3) * (1 - t ^ 3)
        / (1 + s * t + s ^ 2 * t ^ 2) ^ 3 := by
  rw [show cintegralJ 1 = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      cintegralKernel 1 s t by rfl]
  apply intervalIntegral.integral_congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  unfold cintegralKernel
  simp

/-- the deep `(Cintegral)` instance for `n = 1`:
`L(2,χ₋₃)·a₁ − 2·b₁ = J₁` (a₀ = 1-type coefficient values make this
`3·L(2,χ₋₃) − 2 = J₁`; numerically `J₁ = 3L − 2 = 0.3439072386894589…`).
 This is the first genuine Beukers double-integral evaluation (the
`n = 0` case closed via the geometric-square evaluation; the general `n`
summands need the Apéry/creative-telescoping evaluation of the double
integral against the paired `L`-series). -/
def CintegralIdentityOne : Prop :=
  L2chi3Real * (HA_coeff 1 : ℝ) - 2 * (HB_coeff 1 : ℝ) = cintegralJ 1

/-- `CintegralIdentityOne` is literally `3·L(2,χ₋₃) − 2 = J₁` -/
lemma CintegralIdentityOne_eq : CintegralIdentityOne ↔ (3 : ℝ) * L2chi3Real - 2 = cintegralJ 1 := by
  unfold CintegralIdentityOne
  simp only [HA_coeff_one, HB_coeff_one]
  constructor
  · intro h
    ring_nf at h ⊢
    exact h
  · intro h
    ring_nf at h ⊢
    exact h

end Submission.CDT

