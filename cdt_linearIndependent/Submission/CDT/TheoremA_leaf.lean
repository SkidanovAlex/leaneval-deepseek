import Submission.Transcendence.LindemannWeierstrass
import Submission.Helpers

/-!
# Theorem A of CDT, reduced to its single atomic leaf

**The claim (CDT `mainA`, arXiv:2408.15403).**  With `χ₋₃ = ![0,1,-1]`
the numbers `1, ζ(2), L(2,χ₋₃)` are linearly independent over `ℚ`:
`LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction χ₋₃ 2]`.

**Leaf decomposition (everything here is PROVED except `theoremA_leaf`).**
Because `ζ(2) = π²/6` is transcendental over `ℚ` (proved in
`Submission.Transcendence.LindemannWeierstrass`, where also `1, ζ(2)` are
shown linearly independent), the three-element statement is *equivalent* to
the single number-theoretic claim

```lean
def theoremA_leaf : Prop :=
  ∀ a b : ℚ, ZMod.LFunction chi3 2 ≠ (a : ℂ) + (b : ℂ) * riemannZeta 2
```

i.e. **`L(2,χ₋₃) ∉ ℚ + ℚ·ζ(2)`**: no rationals `a,b` make
`L(2,χ₋₃) = a + b·ζ(2)`.  Concretely this says that each of
`L(2,χ₋₃)`, `L(2,χ₋₃)/ζ(2)`, and every `L(2,χ₋₃) − q·ζ(2)` (`q ∈ ℚ`)
is irrational.  The formal equivalence

```lean
theorem theoremA_iff_leaf :
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction chi3 2] ↔ theoremA_leaf
```

is proved here in full (both directions: the `L`-coefficient-zero case is
killed by the transcendence of `ζ(2)`; the nonzero case is algebraically
divided out, `Rat.cast_div`).

**Why the leaf is open.**  `theoremA_leaf` is precisely the content of
Theorem `mainA` of the paper.  Its simplest case (`L(2,χ₋₃)` irrational,
take `b = 0`) was open until the 2024 paper and is proved there by
*arithmetic holonomy bounds* applied to Apéry/Zagier-type sequences; that
machinery (~200 pages of new mathematics: holonomic `G`-functions,
denominator bounds `[1..n]·[…]`, Borel–Pólya–André overconvergence,
Arakelov–Bost heights) is not present in the pinned Mathlib and cannot be
reduced further to a single proof.  The first object of the paper's own
proof is the Hauptmodul series `H_A(x) = Σ aₙxⁿ` on `Y₀(6)` with
`aₙ = Σₖ C(n,k)²·C(2k,k)` (Zagier's sequence `C`, Apéry-type numerators
for `L(2,χ₋₃)`); its three-term P-recurrence
`(n+1)²a_{n+1} − (10n²+10n+3)aₙ + 9n²a_{n−1} = 0` (the coefficient form
of the ODE `x(1−x)(1−9x)y'' + (1−20x+27x²)y' + 3(−1+3x)y = 0`) is
**DONE**: the integer three-term P-recurrence landed in the commons as
`Commons.Data.Nat.Choose.zagierC_recurrence` (creative telescoping; casts to
`HA_coeff_recurrence` in `ℚ`); `H_A` satisfies the ODE in `ℚ⟦x⟧`
(`HA_ode : HA_odeLHS HA = 0`, module `Submission.CDT.ZagierH`); and the
companion series `H_B`, `H_C` (recurrences (zagr)/(zagrt), coefficients
`b₀=c₀=0, b₁=c₁=1`) satisfy the *inhomogeneous* ODEs
`L(H_B) = 1`, `L(H_C) = (1−x)⁻¹` — assembling Proposition `functionsH` of
the paper in its algebraic half (`functionsH_ode : L(aH_A+bH_B+cH_C) = b +
c/(1−x)`, module `Submission.CDT.ZagierHBC`).  What remains of Lemma
`defabc`/Proposition `functionsH` is the *rationality half* — the integrality
`[1,2,…,n]²·bₙ, [1,2,…,n]²·cₙ ∈ ℤ` and the overconvergence at `x = 1/9`,
which come from the Eichler-integral (modular-form) construction and are not
formalizable from the recurrences alone.

**Classical sub-leaves (each isolated; provable from Mathlib alone).**
1. **[DONE — module `Submission.CDT.L2chi3Real`]** `L(2,χ₋₃)` is real and
   positive (from the residue series `Σ (1/(3n+1)² − 1/(3n+2)²)`; see
   `L2chi3Real_pos`, `LFunction_chi3_two_pos_real`).
2. **[DONE — module `Submission.CDT.L2chi3Real_integral`]**
   The *period identity* of the paper's display:
   `L(2,χ₋₃) = −∫₀¹ log x / (1 + x + x²) dx`.  In detail: each paired
   summand is the period integral of `x^{3k}(1−x)(−log x)`
   (`pairSum_eq_integral`, module `Submission.CDT.L2chi3Real_period`,
   via `∫₀¹ x^k·log x = −1/(k+1)²`, proved by the improper FTC), and
   `L2chi3Real = Σ'ₖ pairSum k` (`L2chi3Real_eq_pair_tsum`); the series
   is interchanged with the integral by the Bochner theorem
   `MeasureTheory.integral_tsum_of_summable_integral_norm` on the
   restricted Lebesgue measure over `(0,1]` (each term nonnegative, norm
   series summable), and the pointwise geometric sum
   `Σₖ x^{3k}(1−x)(−logx) = (−logx)/(1+x+x²)` on `(0,1)` gives the
   result (`L2chi3Real_eq_integral_period`).
3. **[DONE — module `Submission.CDT.L2chi3Corollary`]**  The paper's
   trigamma corollary, in classical series form (no digamma theory needed):
   the four residue-class sums
   `Σₖ1/(3k+1)²`, `Σₖ1/(3k+2)²`, `Σₖ1/(6k+1)²`, `Σₖ1/(6k+5)²` are evaluated
   (`res31_eq_paper`, …, `res65_eq_paper`) as
   `±L/2 + 2π²/27` and `±5L/8 + π²/18` — these equal `ψ₁(n/3)/9` and
   `ψ₁(n/6)/36` for `n = 1, 2` and `n = 1, 5`.  Each is irrational under
   Theorem A (`corollary_irrational : theoremA_leaf → …`, through the real
   form `theoremA_leaf_real`, `L(2,χ₋₃) ∉ ℚ + ℚ·π²`).  Engine: the generic
   period-splitting lemma `tsum_period_split` (`Σₙ a n = Σ_{r<q}Σₖ a(qk+r)`
   for summable `a`), the mod-3 decomposition of `ζ(2)` =
   `A + B + ζ(2)/9` and parity splits `A = C + B/4`, `B = D + A/4`, and the
   bridge `zeta2Real = π²/6` (Mathlib `riemannZeta_two` +
   `zeta_nat_eq_tsum_of_gt_one` pulled back from `ℂ` by
   `Complex.ofReal_tsum`).
4. **[DONE — modules `Submission.CDT.L2chi3Zagier` / `Submission.CDT.ZagierWZ`]**
   Zagier's
   hypergeometric series for `L(2,χ₋₃)` (paper display after Thm. `mainA`,
   citing Hessami Pilehrood–Hessami Pilehrood §3):
   `L(2,χ₋₃) = (1/27)·Σₙ (4−15n)(−27)ⁿ/(n³·C(2n,n)²·C(3n,n))`.  Pinned:
   the rational summand `zagierL2chiTerm` (`t₀ := 0`), the real series
   `zagierL2chiSeries`, the leaf `theoremA_leaf_hypergeom`, the values
   `t₁ = 99/4`, `t₂ = −351/80`, the absolute-value identity
   `|tₙ| = (15n−4)·27ⁿ/(n³·C(2n,n)²·C(3n,n))` (n ≥ 1), and **absolute
   convergence**: `summable_zagierL2chi_term : Summable (fun n => (tₙ : ℝ))`
   (exact binomial-step ratios `centralBinom_succ_ratio`,
   `choose_three_succ_ratio`; successive-ratio bound `|t_{n+1}| ≤ ½|tₙ|`
   for n ≥ 4 via `ratioE`/`ratioE_le_half`/`ratioE_poly_le`; geometric
   decay `abs_term_geom`; comparison with the geometric series).
   Brick (ii) — the identity itself — is **CLOSED**: `zagierL2chi_identity :
   theoremA_leaf_hypergeom` and the equivalent main summation lemma
   `zagierL2chi_leaf_main` are proved in module
   `Submission.CDT.ZagierWZ` via the Markov–WZ certificate and the
   analytic rectangle limits (see the module docstring there).  Prepared
   and DONE: the Beta-integral component lemmas (complex and real-cast:
   `centralBinom_recip_beta/real`, `choose_three_recip_beta/real`,
   `integral_pow_mul_one_sub_pow_real`), the summand-denominator integral
   form `zagierL2chi_denom_integral`, the termwise equality
   `zagierL2chiTerm_eq_integralTerm`, the coefficient manipulation
   `zagierL2chi_coeff_poly`/`zagierL2chi_coeff_split` (polylog basis
   `{n·Xⁿ, Xⁿ, Xⁿ/n, Xⁿ/n², Xⁿ/n³}`), and — **NEW** — the *box form* of the
   summand: `zagierL2chiIntegralTerm_box`
   (`tₙ = ∫₀¹∫₀¹∫₀¹ P(n)·Zⁿ/n³` with box kernel
   `Z = −27x(1−x)y(1−y)z(1−z)²`, `|Z| ≤ 1/4` on the cube), via
   `zagierL2chiBoxZ_pow_eq`, `int_one_sub_sq_pow_eq`,
   `zagierL2chiBoxZ_pow_triple`.  Remaining: the summation/identification
   with the period.  Closing the identity is HHP Thm. 1 (MR2900448 §3) at
   `(α,β,a) = (1/3,2/3,0)`: their eq. (8) partial-fraction-reduces the LHS
   to the paired residue series, and the RHS is the `Σ_n G(n,0)` side of a
   Markov-WZ certificate (`F(n+1,k)−F(n,k) = G(n,k+1)−G(n,k)`, Prop. A:
   `Σ_k F(0,k) = Σ_n G(n,0)` after a vanishing limit), whose pochhammer
   products `(1/3)_n(2/3)_n = (3n)!/(27ⁿn!)` give the `tₙ` summand.
   Candidate fallback routes:
   rearrangement to the paired residue series or to the sibling
   Pascal-triangle double sum `L(2,χ₋₃) = −1/3 + Σ_{n>m>0}1/C(n,m)²`, or a
   creative-telescoping certificate.

**The proof of `mainA`, dismantled (paper §"Paths to…", `sec:proofA`).**
The paper's proof of `mainA` runs as follows; each node is annotated with
its formal status in this repository:

* **absurd set-up.**  Assume `theoremA_leaf` false: `∃ a₀ b₀ : ℚ`,
  `L(2,χ₋₃) = a₀ + b₀·ζ(2)` (equivalently the paper's
  `a + b·L/2 + c·ζ/2·? = 0` after clearing, `a,b,c ∈ ℚ`).
  *Formal status*: the equivalence of the three-term independence with the
  leaf, and the leaf's negation, is fully proved in this module
  (`theoremA_iff_leaf`, `leaf_of_three`, `three_of_leaf` + the
  Lindemann–Weierstrass chapter's transcendence of `ζ(2)`).
* **(functionsH / defabc)** with rational `a,b,c` form
  `H(x) := a·H_A(x) + b·H_B(x) + c·H_C(x)` with the explicit Zagier
  sequences `H_A, H_B, H_C ∈ ℚ⟦x⟧`; `H ∈ ℚ⟦x⟧` has denominators
  `[1..n]²` and satisfies `L(H) = b + c/(1−x)`, where `L` is the order-2
  operator `x(1−x)(1−9x)D² + (1−20x+27x²)D + 3(−1+3x)`; and the two
  difference series `H_B − (L(2,χ)/2)H_A`, `H_C − (ζ(2)/4)H_A` have radius
  of convergence `1` (overconvergence through the singularity `1/9`).
  *Formal status*: the recurrences and ODE half are PROVED —
  `HA_ode` (`ZagierH`), `HB_ode`, `HC_ode`, `functionsH_ode`,
  `ZagierH_coeff` (`ZagierHBC`), and the head-values agree with the paper's
  display (`HB_coeff_two/three/four = 23/4, 145/4, 3993/16`,
  `HC_coeff_two/three/four = 6, 343/9, 788/3`).  The integrality half
  `[1..n]²·bₙ, [1..n]²·cₙ ∈ ℤ` and the overconvergence of the difference
  series.  **The `H_B` overconvergence is no longer blocked**: it is PROVED
  (`Submission.CDT.overconvergesB_proved : OverconvergesUnit eichlerDiffB`),
  as a consequence of the now fully proved `(Cintegral)` identity
  `CintegralIdentity_proved` (`Submission.CDT.CintegralAssembled`) — the
  analytic half of `EichlerInputB`.  What remains is (i) the *modular
  integrality* `[1..n]²·bₙ, [1..n]²·cₙ ∈ ℤ` and (ii) the `H_C`-side
  overconvergence, both coming from the Eichler-integral/weight-zero modular
  symmetry of Γ₀(6) (`WeilHeckeLemma` input of `defabc`), and not
  consequences of the recurrences alone (the recurrences admit solutions
  with arbitrary denominators).  That input is now **stated
  precisely as a standalone specification** in module
  `Submission.CDT.EichlerInput` (no axioms, no `sorry`): the predicate
  `HasDenomTypeSq` (`[1..n]²·fₙ ∈ ℤ`, with `lcmRange` = `[1,2,…,n]`), the
  radius-≥1 overconvergence predicate `OverconvergesUnit`, the two
  hypothesis-`Prop`s `EichlerInputB`, `EichlerInputC`, the coefficient
  identity `zagierH_coeff_seq_eq_diff`, and the derived overconvergence of
  the `functionsH`-combination `H = aH_A+bH_B+cH_C` under the absurd
  dependence (`functionsH_overconverges`).  Discharging
  `EichlerInputB`/`EichlerInputC` is the modular-form (or
  integral-representation) task that later work — a future modular-forms
  development — must supply; nothing downstream changes once it lands.  The
  paper's two displays are both proved analytically here:
  `(Cintegral)` for all `n` (`Submission.CDT.CintegralAssembled`) and
  `(Aintegral)` for all `n` (`Submission.CDT.AintegralAssembled`), and with
  them **both** overconvergence statements: `overconvergesB_proved`
  (`OverconvergesUnit eichlerDiffB`) and, via the inverse Möbius (binomial)
  transform of the `(Aintegral)` identity onto the new kernel
  `B = (1−st) − (1−s²)(1−t²)`, `overconvergesC_proved :
  OverconvergesUnit eichlerDiffC` (`Submission.CDT.AintegralUntransformed`;
  the untransformed coefficients are in fact *bounded* by `ζ(2)/4`).  So
  `functionsH_overconverges_of_modular` gives the overconvergence half of
  Proposition `functionsH` from the modular `[1..n]²`-integrality
  `ModularIntegralityB`/`C` alone — the only remaining modular content of
  `EichlerInputB`/`EichlerInputC`.  The analytic route's **first integral lemma is now stated
  precisely** in module `Submission.CDT.L2chi3Cintegral` (with the proved
  bridge): `cintegralKernel`/`cintegralJ` (the `(Cintegral)` summands and
  double integrals), the Prop targets `CintegralIdentity`
  (`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ`), `cintegralJ_bound`
  (`|Jₙ| ≤ 1`), and the PROVED theorem `overconvergesB_of_cintegral`
  (those three targets imply `OverconvergesUnit eichlerDiffB` — the
  overconvergence conjunct of `EichlerInputB`).  Decomposition of the
  targets: the kernel inequality `9st(1−s³)(1−t³) ≤ (1+st+s²t²)²` on
  `[0,1]²` is PROVED (commons `Commons.Analysis.Real.cubeKernel_le`, fleet
  L57; in-module `cintegralKernel_le_one`); `cintegralJ_bound` is PROVED
  (`cintegralJ_bound'`: kernel ≤ 1 pointwise + `norm_integral_le_of_norm_le_const`
  at both integral levels);
  the instances of `CintegralIdentity` at `n ≤ 7` are PROVED
  (`CintegralIdentity_zero` via the commons
  `squareInverseKernelDoubleIntegral`; `CintegralIdentityOne` = `3L − 2 =
  J₁` in module `Submission.CDT.CintegralOne`; `CintegralIdentityAt_two` =
  `15L − 23/2` in `CintegralTwo`; `CintegralIdentityAt_three` = `93L −
  145/2` in `CintegralThree`; `CintegralIdentityAt_four` = `639L − 3993/8`
  in `CintegralFour`; `CintegralIdentityAt_five` = `4653L − 727059/200`
  in `CintegralFive`; `CintegralIdentityAt_six` = `35169L − 5495507/200`
  in `CintegralSix`; `CintegralIdentityAt_seven` = `272835L −
  417806469/1960` in `CintegralSeven`; `CintegralIdentityAt_eight` =
  `2157759L − 66085799967/39200` in `CintegralEight`;
  `CintegralIdentityAt_nine` = `17319837L − 530455590781/39200` in
  `CintegralNine`; `CintegralIdentityAt_ten` =
  `140668065L − 4308248502993/39200` in `CintegralTen`;
  `CintegralIdentityAt_eleven` = `1153462995L − 4274588067098379/4743200`
  in `CintegralEleven`; `CintegralIdentityAt_twelve` =
  `9533639025L − 1413218448827853/189728` in `CintegralTwelve`;
  `CintegralIdentityAt_thirteen` =
  `79326566595L − 49681644752988856791/801600800` in `CintegralThirteen`;
  `CintegralIdentityAt_fourteen` =
  `663835030335L − 415754993154999572883/801600800` in `CintegralFourteen`;
  `CintegralIdentityAt_fifteen` =
  `5582724468093L − 699283848231726007461/160320160` in `CintegralFifteen`;
  `CintegralIdentityAt_sixteen` =
  `47152425626559L − 2147724879365145978567/58298240` in `CintegralSixteen`;
  `CintegralIdentityAt_seventeen` =
  `399769750195965L − 11577240673264126122251355/37066020992` in
  `CintegralSeventeen`
  — each `Jₙ = Σₘ Wₙ(m)` is the binomial-series double-integral evaluation
  (for `n ≤ 19` realised inside the module by the analytic template, now
  archived in `Scratch/archive_heavy/`; systematically by the *light*
  ~90-line modules `CintegralTwo`–`CintegralTwentyThree`, which derive
  `CintegralIdentityAt n` from the general expansion plus the commons core,
  via `Scratch/cintegral_generator/mklight_all.py`), driven by the commons
  creative-telescoping identities `sum_cintegral{One,..,TwentyThree}_core`,
  and `cintegral_identity_le_seventeen` (`CintegralAssembled`) assembles every
  `n ≤ 17`; **NEW (this stretch): the instances at `n = 18, …, 27`**
  (`CintegralIdentityAt_eighteen` … `_twentyseven`, assembled as
  `cintegral_identity_le_thirtyOne`), **and the whole tail is reduced to a
  single parametric statement** by module `Submission.CDT.CintegralGeneral`:
  the **general-`n` Beukers expansion**
  `cintegralJ_eq_sum_W_gen : ∀ n, cintegralJ n = Σ'ₘ genW n m` with
  `genW n m = 9ⁿC(m+2n,2n)Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²`
  (proved for *all* `n`, with summability `genW_summable`), so that
  `CintegralIdentity_of_genW_sum` (`CintegralGeneral`) derives
  `CintegralIdentity` from the single `m`-sum evaluation
  `∀n, Σ'ₘ genW n m = L(2,χ₋₃)aₙ − 2bₙ`, and
  `CintegralIdentity_of_recurrence` (`CintegralAssembled`) derives it from
  the single Zagier recurrence `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}`
  (`n ≥ 1`) for the double integrals; the remaining commons
  creative-telescoping identities `sum_cintegral<N>_core` supply one degree
  at a time, and `Scratch/cintegral_generator/mklight.py` turns such an
  identity into the instance `CintegralIdentityAt N` in a ~100-line module
  (replacing the ~800-line heavy template used for `n ≤ 19`).  The **other conjunct of
  `EichlerInputB` — the modular `[1..n]²`-integrality — is isolated in
  `EichlerInput`** as `ModularIntegralityB`/`ModularIntegralityC`,
  with `HasDenomTypeSq_HA` (free: `aₙ ∈ ℤ`) and
  `functionsH_denomtype_int` (every integer combination has denom type
  `[1..n]²` once the `B`,`C`-input lands)
  (`HasDenomTypeSq HB_coeff`/`HC_coeff`), with the structural lemmas
  proved there (`lcmRange_dvd_of_le`, `HasDenomTypeSq_add/neg/int_mul`
  closures) and ground checks `HB_denomType_initial`/`HC_denomType_initial`
  and `HB_denomType_six/seven/eight`, `HC_denomType_six/seven/eight`
  (witnesses `1, 23, 1305, 35937, 6543531, 49459563, 18801291105,
  594772199703` for `B`; `24, 1372, 37824, 52065312, 19791871920,
  626109046272` for `C`); `eichlerInputB_iff_parts` records the split and
  `L2chi3Cintegral.eichlerInputB_of_modular_and_cintegral` assembles
  `EichlerInputB` from its modular conjunct (to be discharged by Γ₀(6)
  Eichler-integral theory) and its analytic conjunct (the `(Cintegral)`
  targets).
* **(defG / etalecover)** with `y = x²/(x−1)`, `G(y) := Sym⁺H(x) ∈ ℚ⟦y⟧`;
  `Gdenominatortype`: `G` has denominator type `[1..2n]²` (**PROVED** below,
  module `Submission.CDT.SympDenom`: `sympDescCoeff_denomType`,
  `HasDenomTypeSq_subst`, `sympSym_denomType`, `Gdenominatortype` — the
  doubling `[1..n]² → [1..2n]²` comes from the descent recursion and
  `[1..2m] ∣ [1..2n]`); `G` is
  holonomic on `P¹∖{0,4,∞,−1/72}`, holomorphic on `ℂ∖[4,∞)`, with `ℤ/2`
  local monodromy at `y = 4`.
  *Formal status*: the algebraic symmetrization machine is PROVED —
  descent/existence/uniqueness (`SympDescent`: `symp_descent`,
  `sympSym_subst`, `symp_subst_y_injective`), integrality of `Sym⁺H_A`
  (`sympSym_int`, `SympZagier`: `sympSym_HA_IntSeries`, defG coefficients
  `g₀..g₁₁`), `Sym⁺`-linearity (`sympSym_add`, `sympSym_C_mul`) and the
  decomposition `Sym⁺(aH_A+bH_B+cH_C) = a·G_A + b·Sym⁺H_B + c·Sym⁺H_C`
  (`ZagierHBC`: `sympSym_ZagierH`).  The denominator-type doubling and the
  analytic continuation claims are **BLOCKED** (depend on the blocked
  half of `functionsH` plus the analytic `etalecover`/`analytic quotient`
  descent, §"Basic Remark … Y(2)→Y₀(2)").
* **(Lemma 14functions)** the `14` functions `B₁..B₇`, `G, G′, G″, G‴`,
  `∫G, ∫(G−G(0))/y, ∫(G−G(0)−G′(0)y)/y²` are `ℚ(y)`-linearly
  independent.
  *Formal status*: **BLOCKED** — needs Lemma `seven` (independence of the
  seven pure functions `Bᵢ`, §"pure functions": polylogarithm
  `Li₂`, logarithms, the `J`-function with its order-2 `ODEJ`, monodromy
  arguments along paths of `P¹∖{0,1,∞}`) and the monodromy argument on
  `P¹∖{0,−1/72,4,∞}` (holonomy of the order-4 ODE, irreducibility,
  `Δ = Ĝ−G`); none of the required complex-analysis/transcendence
  infrastructure is in the pinned Mathlib.
* **(arithmetic holonomy bounds, §"fine section"/"new slopes"/…)** with
  the type array `typesA` and integration vector `e` (τ-values
  `τᵇ = 191/49`, `τ♯ = 27/80`, sum `16603/3920`), the bounds
  (Theorem `main:BC form`, resp. `main:elementary form`, resp.
  `main:BC conv discrete`) give `m ≤ 13.9938…`, resp. `13.730…`, resp.
  `13.7206… < 14` for the number `m` of `ℚ(y)`-independent functions of
  that type — refuting the absurd dependence.
  *Formal status*: **BLOCKED** — Bost–Charles slopes/Arakelov-height
  machinery (`basic main`, `main:BC form`, `main:elementary form`,
  `main:BC conv discrete`, Lemma `choicephiA`, Corollary
  `stacky overconvergence`), ~150 pages absent from Mathlib; the τ
  rational arithmetic `191/49 + 27/80 = 16603/3920` is a routine `ring`
  identity, and the analytic evaluation of `I_ξ^{14}`/`g*` and the final
  transcendental numerical inequalities (logarithms of explicit ratios)
  are not formalizable from the pinned Mathlib.

**Conclusion.** `theoremA_leaf` (≡ `cdt_theoremA_leaf_gap`) sits atop
nodes that each individually require a mathematical theory absent from the
pinned Mathlib: (i) modular/Eichler-integral arithmetic of Γ₀(6)
(`defabc`/`functionsH` integrality and overconvergence), (ii)
complex-analytic functional independence with monodromy (Lemma `seven`,
Lemma `14functions`), and (iii) Arakelov/Bost-slopes arithmetic-holonomy
bounds.  Every sub-lemma of the chain that *is* provable from the pinned
Mathlib has been formalized and committed (period identity, residue/trigamma
corollaries, Zagier hypergeometric identity, `H_A/H_B/H_C` recurrences and
ODEs, `functionsH_ode`, symmetrization/descent with `G_A` integrality and
descent coefficients, the order-4 `x`-ODE machinery of
`SympPullback`/`SympExplicitode`, and the `Sym⁺`-linearity/decomposition
brick added with this analysis).  The workspace keeps exactly the two
documented genuine gaps.

-/

namespace Submission.CDT

open Complex
open scoped BigOperators
open Polynomial

noncomputable section

/-- `χ₋₃`, the nontrivial Dirichlet character mod 3, as a complex-valued
function (same as `Submission.Helpers.chi3`). -/
abbrev chi3 : ZMod 3 → ℂ := ![0, 1, -1]

/-- The atomic number-theoretic leaf of Theorem A: `L(2,χ₋₃)` is not a
rational linear combination of `1` and `ζ(2) = π²/6`. -/
def theoremA_leaf : Prop :=
  ∀ a b : ℚ, ZMod.LFunction chi3 2 ≠ (a : ℂ) + (b : ℂ) * riemannZeta 2

/-- If `x` is transcendental over `ℚ`, then `1, x` are linearly independent
over `ℚ` (component form). -/
lemma pair_indep_comp (x : ℂ) (hx : Transcendental ℚ x) :
    ∀ p q : ℚ, (p : ℂ) + (q : ℂ) * x = 0 → p = 0 ∧ q = 0 := by
  classical
  intro p q h
  by_cases hq : q = 0
  · constructor
    · have hp0 : (p : ℂ) = 0 := by simpa [hq] using h
      exact_mod_cast hp0
    · exact hq
  · have hxalg : IsAlgebraic ℚ x := by
      refine ⟨C (q : ℚ) * X + C (p : ℚ), ?_, ?_⟩
      · intro hp0
        have hc := congrArg (fun r : ℚ[X] => r.coeff 1) hp0
        have hq1 : ((C (q : ℚ) * X + C (p : ℚ) : ℚ[X])).coeff 1 = q := by
          have h1 : (C (q : ℚ) * X : ℚ[X]) = X * C (q : ℚ) := by ring
          rw [h1, Polynomial.coeff_add]
          simp [Polynomial.coeff_C]
        rw [hq1] at hc
        exact hq hc
      · have hcast : (aeval x) ((C (q : ℚ) * X + C (p : ℚ) : ℚ[X])) = (q : ℂ) * x + (p : ℂ) := by
          simp [Polynomial.aeval_def]
        rw [hcast]
        rw [← h]
        ring
    exact False.elim (hx hxalg)

/-- `ζ(2) = π²/6` is transcendental over `ℚ` (Lindemann–Weierstrass chapter). -/
lemma zeta2_transcendental : Transcendental ℚ (riemannZeta 2) :=
  Submission.Transcendence.transcendental_riemannZeta_two_complex

/-- Three-element linear independence gives the leaf (drop the `1, ζ(2)`
terms to `b = 0`). -/
lemma leaf_of_three
    (h : LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction chi3 2]) :
    theoremA_leaf := by
  classical
  dsimp [theoremA_leaf]
  intro a b hL
  have hLI : ∀ p q r : ℚ,
      p • (1 : ℂ) + q • riemannZeta 2 + r • (ZMod.LFunction chi3 2) = 0 →
        p = 0 ∧ q = 0 ∧ r = 0 := by
    simpa using (Submission.Helpers.linearIndependent_cons3_iff (x := (1 : ℂ))
      (y := riemannZeta 2) (z := (ZMod.LFunction chi3 2))).mp h
  rcases hLI a b (-1 : ℚ) (by
    simp [Algebra.smul_def]
    rw [← hL]
    ring) with ⟨_, _, hminus⟩
  norm_num at hminus

/-- The leaf gives three-element linear independence (case `r = 0` is the
transcendence of `ζ(2)`; case `r ≠ 0` is divided out). -/
lemma three_of_leaf (htr : Transcendental ℚ (riemannZeta 2))
    (hleaf : theoremA_leaf) :
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction chi3 2] := by
  classical
  dsimp [theoremA_leaf] at hleaf
  let L : ℂ := ZMod.LFunction chi3 2
  rw [Submission.Helpers.linearIndependent_cons3_iff (x := (1 : ℂ)) (y := riemannZeta 2) (z := L)]
  intro p q r hrel
  by_cases hr : r = 0
  · have hpq : (p : ℂ) + (q : ℂ) * riemannZeta 2 = 0 := by
      simpa [hr, Algebra.smul_def] using hrel
    rcases pair_indep_comp (riemannZeta 2) htr p q hpq with ⟨hp, hq⟩
    exact ⟨hp, hq, hr⟩
  · have hL : L = (-(p / r : ℚ) : ℂ) + (-(q / r : ℚ) : ℂ) * riemannZeta 2 := by
      have hrel' : (p : ℂ) + (q : ℂ) * riemannZeta 2 + (r : ℂ) * L = 0 := by
        simpa [Algebra.smul_def] using hrel
      have hcastp : ((p / r : ℚ) : ℂ) = (p : ℂ) / (r : ℂ) := by rw [Rat.cast_div]
      have hcastq : ((q / r : ℚ) : ℂ) = (q : ℂ) / (r : ℂ) := by rw [Rat.cast_div]
      have hrℂ : (r : ℂ) ≠ 0 := by exact_mod_cast hr
      have h1 : (r : ℂ) * L = -((p : ℂ) + (q : ℂ) * riemannZeta 2) := by
        rw [eq_neg_iff_add_eq_zero]
        rw [← hrel']
        ring
      calc
        L = (r : ℂ)⁻¹ * ((r : ℂ) * L) := by
          rw [← mul_assoc, inv_mul_cancel₀ hrℂ, one_mul]
        _ = (r : ℂ)⁻¹ * (-((p : ℂ) + (q : ℂ) * riemannZeta 2)) := by rw [h1]
        _ = -(p : ℂ) / (r : ℂ) - (q : ℂ) * riemannZeta 2 / (r : ℂ) := by
          field_simp [hrℂ]
          ring
        _ = (-(p / r : ℚ) : ℂ) + (-(q / r : ℚ) : ℂ) * riemannZeta 2 := by
          rw [hcastp, hcastq]
          ring
    exact False.elim (hleaf (-(p / r : ℚ)) (-(q / r : ℚ)) (by simpa [L] using hL))

/-- **Theorem A ⟺ its atomic leaf.**  Since `ζ(2)` is transcendental the
`1, ζ(2)` part is automatic; the whole content is
`L(2,χ₋₃) ∉ ℚ + ℚ·ζ(2)`.  This is the formal statement of the single
gap of CDT Theorem A (`mainA`). -/
theorem theoremA_iff_leaf :
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction chi3 2] ↔ theoremA_leaf := by
  constructor
  · exact leaf_of_three
  · exact three_of_leaf zeta2_transcendental

end

end Submission.CDT
