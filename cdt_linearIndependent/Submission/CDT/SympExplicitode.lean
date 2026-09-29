import Mathlib
import Submission.CDT.SympZagier
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range
import Submission.Commons.RingTheory.PowerSeries.iterate_derivative_coeff
import Submission.Commons.RingTheory.PowerSeries.iterate_derivative_coeff_fact

/-!
# The order-4 ODE (explicitode) for `G_A(y) = Sym⁺H_A` — target and first coefficient block

This module pins down the **paper's eq. (explicitode)** of CDT
arXiv:2408.15403 (§"The symmetrization of H(x)"): the symmetrized
Hauptmodul series `G_A = Sym⁺H_A` (`Submission.CDT.SympZagier`, whose
descent coefficients `g₀ = 2, g₁ = −27, g₂ = 1014, g₃ = −49536` were
verified there against the paper's defG display) satisfies an order-4
linear ODE with polynomial coefficients

```lean
def GA_odeLHS := c0·G_A + c1·G_A′ + c2·G_A″ + c3·G_A‴ + c4·G_A⁗
--  target: GA_odeLHS = 0   (paper eq. (explicitode))
```

where the multipliers are the *expanded* polynomials (verified against the
paper's factored display `c0 = −18(3+126y−712y²+360y³)`, `c1 = 2(−2−2761y
+…+20736y⁶)`, `c2 = 2y(−34−6353y+…+72576y⁶)`,
`c3 = 2(−4+y)y²(10+204y−…+41472y⁵)`,
`c4 = (−4+y)²y³(1+72y)(−1+118y−122y²+144y³)`).  Here the ODE variable is
the formal variable `X` of `ℚ⟦X⟧`, which plays the paper's role of `y`
(the *paper's* `y = x²/(x−1)` is our `sympY`, the descent coordinate).

**Verified here (coefficient block)** — the coefficient equations of
degrees `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10` of the ODE identity vanish
exactly:

```lean
GA_odeLHS_coeff_zero : PowerSeries.coeff 0 GA_odeLHS = 0   -- needs g₀,g₁
GA_odeLHS_coeff_one  : PowerSeries.coeff 1 GA_odeLHS = 0   -- needs g₀..g₂
GA_odeLHS_coeff_two  : PowerSeries.coeff 2 GA_odeLHS = 0   -- needs g₀..g₃
GA_odeLHS_coeff_three: PowerSeries.coeff 3 GA_odeLHS = 0   -- needs g₄
GA_odeLHS_coeff_four : PowerSeries.coeff 4 GA_odeLHS = 0   -- needs g₅
GA_odeLHS_coeff_five : PowerSeries.coeff 5 GA_odeLHS = 0   -- needs g₆
GA_odeLHS_coeff_six  : PowerSeries.coeff 6 GA_odeLHS = 0   -- needs g₇
GA_odeLHS_coeff_seven: PowerSeries.coeff 7 GA_odeLHS = 0   -- needs g₈
GA_odeLHS_coeff_eight: PowerSeries.coeff 8 GA_odeLHS = 0   -- needs g₉
GA_odeLHS_coeff_nine : PowerSeries.coeff 9 GA_odeLHS = 0   -- needs g₁₀
GA_odeLHS_coeff_ten  : PowerSeries.coeff 10 GA_odeLHS = 0  -- needs g₁₁
GA_odeLHS_coeff_eleven : PowerSeries.coeff 11 GA_odeLHS = 0 -- needs g₁₂
```

Each proof expands the operator coefficient via the range form of
`coeff_mul` (`coeff_mul_range`, = the commons lemma
`Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range`), evaluates the
multiplier coefficients (`coeff_c0Y_…`) and the derivative coefficients
(`[yᵏ]G_A^(i) = (k+i)!/k!·g_{k+i}`, the facts `GA_d1_coeff_…`) and closes
by numeral arithmetic.  Degrees `3..11` use the descent values
`g₄ = 2699568`, `g₅ = −156368412`, `g₆ = 9417572124`,
`g₇ = −582777991998`, `g₈ = 36790168266504`, `g₉ = −2358331843506732`,
`g₁₀ = 153015687754620984`, `g₁₁ = −10026092063682326736`,
`g₁₂ = 662302233027566488692` computed in `SympZagier`
(`sympSym_HA_coeff_four/five/six/seven/eight/nine/ten/eleven/twelve`); the
multipliers `c₃`, `c₄` vanish to order `2`, `3`, so degrees `0–2` need
only `g₀..g₃`.

**The full identity** `GA_odeLHS = 0` is **PROVED** in
`Submission.CDT.SympExplicitodeFinal` (`Submission.CDT.GA_odeLHS_eq_zero`),
via the push-forward route (b) below: the bridge identity
`Submission.CDT.cleared_pullback` of `Submission.CDT.SympExplicitodeBridge`
plus the two second-order ODEs of the branches `H_A` and `H_A∘σ` and their
ODE chains.  The two routes sketched when this module was written were
(a) *coefficient route*: a creative-telescoping-style certificate that the
descent sequence `gₙ` satisfies the P-recurrence induced by the order-4
operator (from the `a`-recurrence of `H_A` through the descent recursion),
or
(b) *push-forward route*: `G_A∘y = H_A + H_A∘φ`, both summands killed by
order-2 `x`-ODEs (`HA_ode` for `H_A`, its pullback under `φ` for `H_A∘φ`),
so the symmetrized series satisfies an order-4 `x`-ODE whose image under
`x ↦ y = x²/(x−1)` is (explicitode).

The generic coefficient machinery for both routes is now permanent commons
content: `Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range` (range
form of `coeff_mul`), `…iterate_derivative_coeff` and
`…iterate_derivative_coeff_fact` (`[yᵏ]((d/dy)ⁱG) = (k+i)!/k!·g_{k+i}`
over `ℚ`).

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section
open PowerSeries
namespace Submission.CDT

/-! ## The paper's order-4 ODE (explicitode) for `G_A(y) = Sym⁺H_A` — first coefficient equations

Target (paper eq. (explicitode), arXiv:2408.15403 §"The symmetrization of
H(x)"): with `G_A := Sym⁺H_A` (module `SympZagier`),

```lean
c0·G_A + c1·G_A′ + c2·G_A″ + c3·G_A‴ + c4·G_A⁗ = 0    (in ℚ[[y]])
c0 = -18(3+126y-712y²+360y³)
c1 = 2(-2-2761y+141632y²-280328y³+176412y⁴-95616y⁵+20736y⁶)
c2 = 2y(-34-6353y+690355y²-1065613y³+867876y⁴-438336y⁵+72576y⁶)
c3 = 2(-4+y)y²(10+204y-118195y²+146946y³-142848y⁴+41472y⁵)
c4 = (-4+y)²y³(1+72y)(-1+118y-122y²+144y³)
```

The `cᵢ` are the *expanded* polynomials (verified against the paper's
factored display by direct expansion) and the ODE variable is the formal
variable `X` of `ℚ⟦X⟧` (which plays the paper's role of `y`; recall the
*paper's* `y = x²/(x−1)` is our `sympY`).

**Verified here (first coefficient block)**: the coefficient equations of
degrees `0, 1, 2` of the ODE identity vanish exactly — using the descent
coefficients `g₀ = 2, g₁ = −27, g₂ = 1014, g₃ = −49536` of the defG
display and the derivative rule `[yᵏ]G^(i) = (k+i)!/k!·g_{k+i}`.  These
are the first three equations that only involve the already-verified
coefficients of `G_A`.  The full identity needs the descent/recurrence
structure of all `gₙ` (or the x-world push-forward of `HA_ode` through
`x ↦ y = x²/(x−1)`) and is left as the next layer.
-/

/-- `c₀(y) = −18(3+126y−712y²+360y³)` (expanded) -/
def c0Y : PowerSeries ℚ := PowerSeries.mk (fun n =>
  if n = 0 then (-54 : ℚ) else if n = 1 then -2268 else if n = 2 then 12816
  else if n = 3 then -6480 else 0)

/-- `c₁(y) = 2(−2−2761y+141632y²−280328y³+176412y⁴−95616y⁵+20736y⁶)` -/
def c1Y : PowerSeries ℚ := PowerSeries.mk (fun n =>
  if n = 0 then (-4 : ℚ) else if n = 1 then -5522 else if n = 2 then 283264
  else if n = 3 then -560656 else if n = 4 then 352824 else if n = 5 then -191232
  else if n = 6 then 41472 else 0)

/-- `c₂(y) = 2y(−34−6353y+690355y²−1065613y³+867876y⁴−438336y⁵+72576y⁶)` -/
def c2Y : PowerSeries ℚ := PowerSeries.mk (fun n =>
  if n = 0 then 0 else if n = 1 then (-68 : ℚ) else if n = 2 then -12706
  else if n = 3 then 1380710 else if n = 4 then -2131226 else if n = 5 then 1735752
  else if n = 6 then -876672 else if n = 7 then 145152 else 0)

/-- `c₃(y) = 2(−4+y)y²(10+204y−118195y²+146946y³−142848y⁴+41472y⁵)` -/
def c3Y : PowerSeries ℚ := PowerSeries.mk (fun n =>
  if n = 0 then 0 else if n = 1 then 0 else if n = 2 then (-80 : ℚ)
  else if n = 3 then -1612 else if n = 4 then 945968 else if n = 5 then -1411958
  else if n = 6 then 1436676 else if n = 7 then -617472 else if n = 8 then 82944 else 0)

/-- `c₄(y) = (−4+y)²y³(1+72y)(−1+118y−122y²+144y³)` -/
def c4Y : PowerSeries ℚ := PowerSeries.mk (fun n =>
  if n = 0 then 0 else if n = 1 then 0 else if n = 2 then 0 else if n = 3 then (-16 : ℚ)
  else if n = 4 then 744 else if n = 5 then 133615 else if n = 6 then -205186
  else if n = 7 then 243382 else if n = 8 then -91584 else if n = 9 then 10368 else 0)

/-- `G_A = Sym⁺H_A`, the symmetrized Hauptmodul series -/
def GA : PowerSeries ℚ := sympSym HA

/-- first four derivatives of `G_A` (needed by the order-4 operator) -/
def GAd1 : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) GA
def GAd2 : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) GAd1
def GAd3 : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) GAd2
def GAd4 : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) GAd3

/-- the order-4 operator `L = Σᵢ cᵢ·(d/dy)ⁱ` applied to `G_A` (the LHS of
eq. (explicitode)) -/
def GA_odeLHS : PowerSeries ℚ := c0Y * GA + c1Y * GAd1 + c2Y * GAd2 + c3Y * GAd3 + c4Y * GAd4

-- sanity: c₀..c₄ agree with the paper's factored forms at low degree is
-- checked through the coefficient equations below.

/-- coefficient of the defG display: `g₀ = 2` -/
lemma GA_coeff_zero : PowerSeries.coeff 0 GA = 2 := sympSym_HA_coeff_zero
/-- `g₁ = −27` -/
lemma GA_coeff_one : PowerSeries.coeff 1 GA = -27 := sympSym_HA_coeff_one
/-- `g₂ = 1014` -/
lemma GA_coeff_two : PowerSeries.coeff 2 GA = 1014 := sympSym_HA_coeff_two
/-- `g₃ = −49536` -/
lemma GA_coeff_three : PowerSeries.coeff 3 GA = -49536 := sympSym_HA_coeff_three

/-- `[y⁰]G_A′ = g₁ = −27` -/
lemma GA_d1_coeff_zero : PowerSeries.coeff 0 GAd1 = -27 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_one]
  norm_num

/-- `[y¹]G_A′ = 2g₂ = 2028` -/
lemma GA_d1_coeff_one : PowerSeries.coeff 1 GAd1 = 2028 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_two]
  norm_num

/-- `[y²]G_A′ = 3g₃ = −148608` -/
lemma GA_d1_coeff_two : PowerSeries.coeff 2 GAd1 = -148608 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_three]
  norm_num

/-- `[y⁰]G_A″ = 2g₂ = 2028` -/
lemma GA_d2_coeff_zero : PowerSeries.coeff 0 GAd2 = 2028 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_one]
  norm_num

/-- `[y¹]G_A″ = 6g₃ = −297216` -/
lemma GA_d2_coeff_one : PowerSeries.coeff 1 GAd2 = -297216 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_two]
  norm_num

/-- `[y⁰]G_A‴ = 6g₃ = −297216` -/
lemma GA_d3_coeff_zero : PowerSeries.coeff 0 GAd3 = -297216 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_one]
  norm_num

-- coefficient of a product: `[yⁿ](c·f) = Σ_{i≤n} [yⁱ]c·[yⁿ⁻ⁱ]f`
-- (the commons lemma `Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range`)
lemma coeff_mul_range (c f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (c * f) = ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i c * PowerSeries.coeff (n - i) f :=
  Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range ℚ c f n

-- coefficient facts for the multiplier polynomials at the needed degrees
lemma coeff_c0Y_zero : PowerSeries.coeff 0 c0Y = -54 := by
  norm_num [c0Y]
lemma coeff_c0Y_one : PowerSeries.coeff 1 c0Y = -2268 := by
  norm_num [c0Y]
lemma coeff_c0Y_two : PowerSeries.coeff 2 c0Y = 12816 := by
  norm_num [c0Y]
lemma coeff_c1Y_zero : PowerSeries.coeff 0 c1Y = -4 := by
  norm_num [c1Y]
lemma coeff_c1Y_one : PowerSeries.coeff 1 c1Y = -5522 := by
  norm_num [c1Y]
lemma coeff_c1Y_two : PowerSeries.coeff 2 c1Y = 283264 := by
  norm_num [c1Y]
lemma coeff_c2Y_zero : PowerSeries.coeff 0 c2Y = 0 := by
  norm_num [c2Y]
lemma coeff_c2Y_one : PowerSeries.coeff 1 c2Y = -68 := by
  norm_num [c2Y]
lemma coeff_c2Y_two : PowerSeries.coeff 2 c2Y = -12706 := by
  norm_num [c2Y]
lemma coeff_c3Y_zero : PowerSeries.coeff 0 c3Y = 0 := by
  norm_num [c3Y]
lemma coeff_c3Y_one : PowerSeries.coeff 1 c3Y = 0 := by
  norm_num [c3Y]
lemma coeff_c3Y_two : PowerSeries.coeff 2 c3Y = -80 := by
  norm_num [c3Y]
lemma coeff_c4Y_zero : PowerSeries.coeff 0 c4Y = 0 := by
  norm_num [c4Y]
lemma coeff_c4Y_one : PowerSeries.coeff 1 c4Y = 0 := by
  norm_num [c4Y]
lemma coeff_c4Y_two : PowerSeries.coeff 2 c4Y = 0 := by
  norm_num [c4Y]

/-- **first explicitode coefficient equation**: `[y⁰](L G_A) = 0` -/
lemma GA_odeLHS_coeff_zero : PowerSeries.coeff 0 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add]
  rw [map_add]
  rw [map_add]
  rw [map_add]
  rw [coeff_mul_range c0Y GA 0, coeff_mul_range c1Y GAd1 0, coeff_mul_range c2Y GAd2 0,
      coeff_mul_range c3Y GAd3 0, coeff_mul_range c4Y GAd4 0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero]
  rw [coeff_c0Y_zero]
  rw [coeff_c1Y_zero]
  rw [coeff_c2Y_zero]
  rw [coeff_c3Y_zero]
  rw [coeff_c4Y_zero]
  rw [GA_coeff_zero]
  rw [GA_d1_coeff_zero]
  rw [GA_d2_coeff_zero]
  rw [GA_d3_coeff_zero]
  norm_num

/-- **second explicitode coefficient equation**: `[y¹](L G_A) = 0` -/
lemma GA_odeLHS_coeff_one : PowerSeries.coeff 1 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 1, coeff_mul_range c1Y GAd1 1, coeff_mul_range c2Y GAd2 1,
      coeff_mul_range c3Y GAd3 1, coeff_mul_range c4Y GAd4 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c1Y_zero, coeff_c1Y_one,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c3Y_zero, coeff_c3Y_one,
      coeff_c4Y_zero, coeff_c4Y_one]
  rw [GA_coeff_zero, GA_coeff_one, GA_d1_coeff_zero, GA_d1_coeff_one, GA_d2_coeff_zero]
  norm_num

/-- **third explicitode coefficient equation**: `[y²](L G_A) = 0` -/
lemma GA_odeLHS_coeff_two : PowerSeries.coeff 2 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 2, coeff_mul_range c1Y GAd1 2, coeff_mul_range c2Y GAd2 2,
      coeff_mul_range c3Y GAd3 2, coeff_mul_range c4Y GAd4 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d3_coeff_zero]
  norm_num
lemma GA_coeff_four : PowerSeries.coeff 4 GA = 2699568 := sympSym_HA_coeff_four
/-- `g₅ = −156368412` -/
lemma GA_coeff_five : PowerSeries.coeff 5 GA = -156368412 := sympSym_HA_coeff_five

/-- `[y³]G_A′ = 4g₄ = 10798272` -/
lemma GA_d1_coeff_three : PowerSeries.coeff 3 GAd1 = 10798272 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_four]
  norm_num

/-- `[y⁴]G_A′ = 5g₅ = −781842060` -/
lemma GA_d1_coeff_four : PowerSeries.coeff 4 GAd1 = -781842060 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_five]
  norm_num

/-- `[y²]G_A″ = 12g₄ = 32394816` -/
lemma GA_d2_coeff_two : PowerSeries.coeff 2 GAd2 = 32394816 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_three]
  norm_num

/-- `[y³]G_A″ = 20g₅ = −3127368240` -/
lemma GA_d2_coeff_three : PowerSeries.coeff 3 GAd2 = -3127368240 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_four]
  norm_num

/-- `[y¹]G_A‴ = 24g₄ = 64789632` -/
lemma GA_d3_coeff_one : PowerSeries.coeff 1 GAd3 = 64789632 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_two]
  norm_num

/-- `[y²]G_A‴ = 60g₅ = −9382104720` -/
lemma GA_d3_coeff_two : PowerSeries.coeff 2 GAd3 = -9382104720 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_three]
  norm_num

/-- `[y⁰]G_A⁗ = 24g₄ = 64789632` -/
lemma GA_d4_coeff_zero : PowerSeries.coeff 0 GAd4 = 64789632 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_one]
  norm_num

/-- `[y¹]G_A⁗ = 120g₅ = −18764209440` -/
lemma GA_d4_coeff_one : PowerSeries.coeff 1 GAd4 = -18764209440 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_two]
  norm_num

/-- multiplier coefficients at degrees 3, 4 -/
lemma coeff_c0Y_three : PowerSeries.coeff 3 c0Y = -6480 := by norm_num [c0Y]
lemma coeff_c0Y_four : PowerSeries.coeff 4 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_three : PowerSeries.coeff 3 c1Y = -560656 := by norm_num [c1Y]
lemma coeff_c1Y_four : PowerSeries.coeff 4 c1Y = 352824 := by norm_num [c1Y]
lemma coeff_c2Y_three : PowerSeries.coeff 3 c2Y = 1380710 := by norm_num [c2Y]
lemma coeff_c2Y_four : PowerSeries.coeff 4 c2Y = -2131226 := by norm_num [c2Y]
lemma coeff_c3Y_three : PowerSeries.coeff 3 c3Y = -1612 := by norm_num [c3Y]
lemma coeff_c3Y_four : PowerSeries.coeff 4 c3Y = 945968 := by norm_num [c3Y]
lemma coeff_c4Y_three : PowerSeries.coeff 3 c4Y = -16 := by norm_num [c4Y]
lemma coeff_c4Y_four : PowerSeries.coeff 4 c4Y = 744 := by norm_num [c4Y]

/-- **fourth explicitode coefficient equation**: `[y³](L G_A) = 0` -/
lemma GA_odeLHS_coeff_three : PowerSeries.coeff 3 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 3, coeff_mul_range c1Y GAd1 3, coeff_mul_range c2Y GAd2 3,
      coeff_mul_range c3Y GAd3 3, coeff_mul_range c4Y GAd4 3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two,
      GA_d3_coeff_zero, GA_d3_coeff_one,
      GA_d4_coeff_zero]
  norm_num

/-- **fifth explicitode coefficient equation**: `[y⁴](L G_A) = 0` -/
lemma GA_odeLHS_coeff_four : PowerSeries.coeff 4 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 4, coeff_mul_range c1Y GAd1 4, coeff_mul_range c2Y GAd2 4,
      coeff_mul_range c3Y GAd3 4, coeff_mul_range c4Y GAd4 4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two,
      GA_d4_coeff_zero, GA_d4_coeff_one]
  norm_num
lemma GA_coeff_six : PowerSeries.coeff 6 GA = 9417572124 := sympSym_HA_coeff_six

/-- `[y⁵]G_A′ = 6g₆ = 56505432744` -/
lemma GA_d1_coeff_five : PowerSeries.coeff 5 GAd1 = 56505432744 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_six]
  norm_num

/-- `[y⁴]G_A″ = 30g₆ = 282527163720` -/
lemma GA_d2_coeff_four : PowerSeries.coeff 4 GAd2 = 282527163720 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_five]
  norm_num

/-- `[y³]G_A‴ = 120g₆ = 1130108654880` -/
lemma GA_d3_coeff_three : PowerSeries.coeff 3 GAd3 = 1130108654880 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_four]
  norm_num

/-- `[y²]G_A⁗ = 360g₆ = 3390325964640` -/
lemma GA_d4_coeff_two : PowerSeries.coeff 2 GAd4 = 3390325964640 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_three]
  norm_num

/-- multiplier coefficients at degree 5 -/
lemma coeff_c0Y_five : PowerSeries.coeff 5 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_five : PowerSeries.coeff 5 c1Y = -191232 := by norm_num [c1Y]
lemma coeff_c2Y_five : PowerSeries.coeff 5 c2Y = 1735752 := by norm_num [c2Y]
lemma coeff_c3Y_five : PowerSeries.coeff 5 c3Y = -1411958 := by norm_num [c3Y]
lemma coeff_c4Y_five : PowerSeries.coeff 5 c4Y = 133615 := by norm_num [c4Y]

/-- **sixth explicitode coefficient equation**: `[y⁵](L G_A) = 0` -/
lemma GA_odeLHS_coeff_five : PowerSeries.coeff 5 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 5, coeff_mul_range c1Y GAd1 5, coeff_mul_range c2Y GAd2 5,
      coeff_mul_range c3Y GAd3 5, coeff_mul_range c4Y GAd4 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two]
  norm_num
lemma GA_coeff_seven : PowerSeries.coeff 7 GA = -582777991998 := sympSym_HA_coeff_seven

/-- `[y⁶]G_A′ = 7g₇ = −4079445943986` -/
lemma GA_d1_coeff_six : PowerSeries.coeff 6 GAd1 = -4079445943986 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_seven]
  norm_num

/-- `[y⁵]G_A″ = 42g₇ = −24476675663916` -/
lemma GA_d2_coeff_five : PowerSeries.coeff 5 GAd2 = -24476675663916 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_six]
  norm_num

/-- `[y⁴]G_A‴ = 210g₇ = −122383378319580` -/
lemma GA_d3_coeff_four : PowerSeries.coeff 4 GAd3 = -122383378319580 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_five]
  norm_num

/-- `[y³]G_A⁗ = 840g₇ = −489533513278320` -/
lemma GA_d4_coeff_three : PowerSeries.coeff 3 GAd4 = -489533513278320 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_four]
  norm_num

/-- multiplier coefficients at degree 6 -/
lemma coeff_c0Y_six : PowerSeries.coeff 6 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_six : PowerSeries.coeff 6 c1Y = 41472 := by norm_num [c1Y]
lemma coeff_c2Y_six : PowerSeries.coeff 6 c2Y = -876672 := by norm_num [c2Y]
lemma coeff_c3Y_six : PowerSeries.coeff 6 c3Y = 1436676 := by norm_num [c3Y]
lemma coeff_c4Y_six : PowerSeries.coeff 6 c4Y = -205186 := by norm_num [c4Y]

/-- **seventh explicitode coefficient equation**: `[y⁶](L G_A) = 0` -/
lemma GA_odeLHS_coeff_six : PowerSeries.coeff 6 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 6, coeff_mul_range c1Y GAd1 6, coeff_mul_range c2Y GAd2 6,
      coeff_mul_range c3Y GAd3 6, coeff_mul_range c4Y GAd4 6]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three]
  norm_num
lemma GA_coeff_eight : PowerSeries.coeff 8 GA = 36790168266504 := sympSym_HA_coeff_eight

/-- `[y⁷]G_A′ = 8g₈ = 294321346132032` -/
lemma GA_d1_coeff_seven : PowerSeries.coeff 7 GAd1 = 294321346132032 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_eight]
  norm_num

/-- `[y⁶]G_A″ = 56g₈ = 2060249422924224` -/
lemma GA_d2_coeff_six : PowerSeries.coeff 6 GAd2 = 2060249422924224 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_seven]
  norm_num

/-- `[y⁵]G_A‴ = 336g₈ = 12361496537545344` -/
lemma GA_d3_coeff_five : PowerSeries.coeff 5 GAd3 = 12361496537545344 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_six]
  norm_num

/-- `[y⁴]G_A⁗ = 1680g₈ = 61807482687726720` -/
lemma GA_d4_coeff_four : PowerSeries.coeff 4 GAd4 = 61807482687726720 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_five]
  norm_num

/-- multiplier coefficients at degree 7 -/
lemma coeff_c0Y_seven : PowerSeries.coeff 7 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_seven : PowerSeries.coeff 7 c1Y = 0 := by norm_num [c1Y]
lemma coeff_c2Y_seven : PowerSeries.coeff 7 c2Y = 145152 := by norm_num [c2Y]
lemma coeff_c3Y_seven : PowerSeries.coeff 7 c3Y = -617472 := by norm_num [c3Y]
lemma coeff_c4Y_seven : PowerSeries.coeff 7 c4Y = 243382 := by norm_num [c4Y]

/-- **eighth explicitode coefficient equation**: `[y⁷](L G_A) = 0` -/
lemma GA_odeLHS_coeff_seven : PowerSeries.coeff 7 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 7, coeff_mul_range c1Y GAd1 7, coeff_mul_range c2Y GAd2 7,
      coeff_mul_range c3Y GAd3 7, coeff_mul_range c4Y GAd4 7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six, coeff_c0Y_seven,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six, coeff_c1Y_seven,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six, coeff_c2Y_seven,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six, coeff_c3Y_seven,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six, coeff_c4Y_seven]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six, GA_coeff_seven,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six, GA_d1_coeff_seven,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five, GA_d2_coeff_six,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four, GA_d3_coeff_five,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three, GA_d4_coeff_four]
  norm_num
lemma GA_coeff_nine : PowerSeries.coeff 9 GA = -2358331843506732 := sympSym_HA_coeff_nine

/-- `[y⁸]G_A′ = 9g₉ = −21224986591560588` -/
lemma GA_d1_coeff_eight : PowerSeries.coeff 8 GAd1 = -21224986591560588 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_nine]
  norm_num

/-- `[y⁷]G_A″ = 72g₉ = −169799892732484704` -/
lemma GA_d2_coeff_seven : PowerSeries.coeff 7 GAd2 = -169799892732484704 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_eight]
  norm_num

/-- `[y⁶]G_A‴ = 504g₉ = −1188599249127392928` -/
lemma GA_d3_coeff_six : PowerSeries.coeff 6 GAd3 = -1188599249127392928 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_seven]
  norm_num

/-- `[y⁵]G_A⁗ = 3024g₉ = −7131595494764357568` -/
lemma GA_d4_coeff_five : PowerSeries.coeff 5 GAd4 = -7131595494764357568 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_six]
  norm_num

/-- multiplier coefficients at degree 8 -/
lemma coeff_c0Y_eight : PowerSeries.coeff 8 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_eight : PowerSeries.coeff 8 c1Y = 0 := by norm_num [c1Y]
lemma coeff_c2Y_eight : PowerSeries.coeff 8 c2Y = 0 := by norm_num [c2Y]
lemma coeff_c3Y_eight : PowerSeries.coeff 8 c3Y = 82944 := by norm_num [c3Y]
lemma coeff_c4Y_eight : PowerSeries.coeff 8 c4Y = -91584 := by norm_num [c4Y]

/-- **ninth explicitode coefficient equation**: `[y⁸](L G_A) = 0` -/
lemma GA_odeLHS_coeff_eight : PowerSeries.coeff 8 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 8, coeff_mul_range c1Y GAd1 8, coeff_mul_range c2Y GAd2 8,
      coeff_mul_range c3Y GAd3 8, coeff_mul_range c4Y GAd4 8]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six, coeff_c0Y_seven, coeff_c0Y_eight,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six, coeff_c1Y_seven, coeff_c1Y_eight,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six, coeff_c2Y_seven, coeff_c2Y_eight,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six, coeff_c3Y_seven, coeff_c3Y_eight,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six, coeff_c4Y_seven, coeff_c4Y_eight]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six, GA_coeff_seven, GA_coeff_eight,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six, GA_d1_coeff_seven, GA_d1_coeff_eight,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five, GA_d2_coeff_six, GA_d2_coeff_seven,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four, GA_d3_coeff_five, GA_d3_coeff_six,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three, GA_d4_coeff_four, GA_d4_coeff_five]
  norm_num
lemma GA_coeff_ten : PowerSeries.coeff 10 GA = 153015687754620984 := sympSym_HA_coeff_ten

/-- `[y⁹]G_A′ = 10g₁₀ = 1530156877546209840` -/
lemma GA_d1_coeff_nine : PowerSeries.coeff 9 GAd1 = 1530156877546209840 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_ten]
  norm_num

/-- `[y⁸]G_A″ = 90g₁₀ = 13771411897915888560` -/
lemma GA_d2_coeff_eight : PowerSeries.coeff 8 GAd2 = 13771411897915888560 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_nine]
  norm_num

/-- `[y⁷]G_A‴ = 720g₁₀ = 110171295183327108480` -/
lemma GA_d3_coeff_seven : PowerSeries.coeff 7 GAd3 = 110171295183327108480 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_eight]
  norm_num

/-- `[y⁶]G_A⁗ = 5040g₁₀ = 771199066283289759360` -/
lemma GA_d4_coeff_six : PowerSeries.coeff 6 GAd4 = 771199066283289759360 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_seven]
  norm_num

/-- multiplier coefficients at degree 9 -/
lemma coeff_c0Y_nine : PowerSeries.coeff 9 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_nine : PowerSeries.coeff 9 c1Y = 0 := by norm_num [c1Y]
lemma coeff_c2Y_nine : PowerSeries.coeff 9 c2Y = 0 := by norm_num [c2Y]
lemma coeff_c3Y_nine : PowerSeries.coeff 9 c3Y = 0 := by norm_num [c3Y]
lemma coeff_c4Y_nine : PowerSeries.coeff 9 c4Y = 10368 := by norm_num [c4Y]

/-- **tenth explicitode coefficient equation**: `[y⁹](L G_A) = 0` -/
lemma GA_odeLHS_coeff_nine : PowerSeries.coeff 9 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 9, coeff_mul_range c1Y GAd1 9, coeff_mul_range c2Y GAd2 9,
      coeff_mul_range c3Y GAd3 9, coeff_mul_range c4Y GAd4 9]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six, coeff_c0Y_seven, coeff_c0Y_eight, coeff_c0Y_nine,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six, coeff_c1Y_seven, coeff_c1Y_eight, coeff_c1Y_nine,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six, coeff_c2Y_seven, coeff_c2Y_eight, coeff_c2Y_nine,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six, coeff_c3Y_seven, coeff_c3Y_eight, coeff_c3Y_nine,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six, coeff_c4Y_seven, coeff_c4Y_eight, coeff_c4Y_nine]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six, GA_coeff_seven, GA_coeff_eight, GA_coeff_nine,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six, GA_d1_coeff_seven, GA_d1_coeff_eight, GA_d1_coeff_nine,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five, GA_d2_coeff_six, GA_d2_coeff_seven, GA_d2_coeff_eight,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four, GA_d3_coeff_five, GA_d3_coeff_six, GA_d3_coeff_seven,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three, GA_d4_coeff_four, GA_d4_coeff_five, GA_d4_coeff_six]
  norm_num
lemma GA_coeff_eleven : PowerSeries.coeff 11 GA = -10026092063682326736 := sympSym_HA_coeff_eleven

/-- `[y¹⁰]G_A′ = 11g₁₁ = −110287012700505594096` -/
lemma GA_d1_coeff_ten : PowerSeries.coeff 10 GAd1 = -110287012700505594096 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_eleven]
  norm_num

/-- `[y⁹]G_A″ = 110g₁₁ = −1102870127005055940960` -/
lemma GA_d2_coeff_nine : PowerSeries.coeff 9 GAd2 = -1102870127005055940960 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_ten]
  norm_num

/-- `[y⁸]G_A‴ = 990g₁₁ = −9925831143045503468640` -/
lemma GA_d3_coeff_eight : PowerSeries.coeff 8 GAd3 = -9925831143045503468640 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_nine]
  norm_num

/-- `[y⁷]G_A⁗ = 7920g₁₁ = −79406649144364027749120` -/
lemma GA_d4_coeff_seven : PowerSeries.coeff 7 GAd4 = -79406649144364027749120 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_eight]
  norm_num

/-- multiplier coefficients at degree 10 (all zero: deg cᵢ ≤ 9) -/
lemma coeff_c0Y_ten : PowerSeries.coeff 10 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_ten : PowerSeries.coeff 10 c1Y = 0 := by norm_num [c1Y]
lemma coeff_c2Y_ten : PowerSeries.coeff 10 c2Y = 0 := by norm_num [c2Y]
lemma coeff_c3Y_ten : PowerSeries.coeff 10 c3Y = 0 := by norm_num [c3Y]
lemma coeff_c4Y_ten : PowerSeries.coeff 10 c4Y = 0 := by norm_num [c4Y]

/-- **eleventh explicitode coefficient equation**: `[y¹⁰](L G_A) = 0` -/
lemma GA_odeLHS_coeff_ten : PowerSeries.coeff 10 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 10, coeff_mul_range c1Y GAd1 10, coeff_mul_range c2Y GAd2 10,
      coeff_mul_range c3Y GAd3 10, coeff_mul_range c4Y GAd4 10]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  rw [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six, coeff_c0Y_seven, coeff_c0Y_eight, coeff_c0Y_nine, coeff_c0Y_ten,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six, coeff_c1Y_seven, coeff_c1Y_eight, coeff_c1Y_nine, coeff_c1Y_ten,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six, coeff_c2Y_seven, coeff_c2Y_eight, coeff_c2Y_nine, coeff_c2Y_ten,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six, coeff_c3Y_seven, coeff_c3Y_eight, coeff_c3Y_nine, coeff_c3Y_ten,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six, coeff_c4Y_seven, coeff_c4Y_eight, coeff_c4Y_nine, coeff_c4Y_ten]
  rw [GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six, GA_coeff_seven, GA_coeff_eight, GA_coeff_nine, GA_coeff_ten,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six, GA_d1_coeff_seven, GA_d1_coeff_eight, GA_d1_coeff_nine, GA_d1_coeff_ten,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five, GA_d2_coeff_six, GA_d2_coeff_seven, GA_d2_coeff_eight, GA_d2_coeff_nine,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four, GA_d3_coeff_five, GA_d3_coeff_six, GA_d3_coeff_seven, GA_d3_coeff_eight,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three, GA_d4_coeff_four, GA_d4_coeff_five, GA_d4_coeff_six, GA_d4_coeff_seven]
  norm_num

lemma GA_coeff_twelve : PowerSeries.coeff 12 GA = 662302233027566488692 := sympSym_HA_coeff_twelve

/-- `[y¹¹]G_A′ = 12g₁₂ = 7947626796330797864304` -/
lemma GA_d1_coeff_eleven : PowerSeries.coeff 11 GAd1 = 7947626796330797864304 := by
  rw [GAd1]
  rw [coeff_derivative]
  rw [GA_coeff_twelve]
  norm_num

/-- `[y¹⁰]G_A″ = 132g₁₂ = 87423894759638776507344` -/
lemma GA_d2_coeff_ten : PowerSeries.coeff 10 GAd2 = 87423894759638776507344 := by
  rw [GAd2]
  rw [coeff_derivative]
  rw [GA_d1_coeff_eleven]
  norm_num

/-- `[y⁹]G_A‴ = 1320g₁₂ = 874238947596387765073440` -/
lemma GA_d3_coeff_nine : PowerSeries.coeff 9 GAd3 = 874238947596387765073440 := by
  rw [GAd3]
  rw [coeff_derivative]
  rw [GA_d2_coeff_ten]
  norm_num

/-- `[y⁸]G_A⁗ = 11880g₁₂ = 7868150528367489885660960` -/
lemma GA_d4_coeff_eight : PowerSeries.coeff 8 GAd4 = 7868150528367489885660960 := by
  rw [GAd4]
  rw [coeff_derivative]
  rw [GA_d3_coeff_nine]
  norm_num

/-- multiplier coefficients at degree 11 (all zero: deg cᵢ ≤ 9) -/
lemma coeff_c0Y_eleven : PowerSeries.coeff 11 c0Y = 0 := by norm_num [c0Y]
lemma coeff_c1Y_eleven : PowerSeries.coeff 11 c1Y = 0 := by norm_num [c1Y]
lemma coeff_c2Y_eleven : PowerSeries.coeff 11 c2Y = 0 := by norm_num [c2Y]
lemma coeff_c3Y_eleven : PowerSeries.coeff 11 c3Y = 0 := by norm_num [c3Y]
lemma coeff_c4Y_eleven : PowerSeries.coeff 11 c4Y = 0 := by norm_num [c4Y]

/-- **twelfth explicitode coefficient equation**: `[y¹¹](L G_A) = 0` -/
lemma GA_odeLHS_coeff_eleven : PowerSeries.coeff 11 GA_odeLHS = 0 := by
  rw [GA_odeLHS]
  rw [map_add, map_add, map_add, map_add]
  rw [coeff_mul_range c0Y GA 11, coeff_mul_range c1Y GAd1 11, coeff_mul_range c2Y GAd2 11,
      coeff_mul_range c3Y GAd3 11, coeff_mul_range c4Y GAd4 11]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero, Nat.succ_sub_one]
  norm_num [coeff_c0Y_zero, coeff_c0Y_one, coeff_c0Y_two, coeff_c0Y_three, coeff_c0Y_four, coeff_c0Y_five, coeff_c0Y_six, coeff_c0Y_seven, coeff_c0Y_eight, coeff_c0Y_nine, coeff_c0Y_ten, coeff_c0Y_eleven,
      coeff_c1Y_zero, coeff_c1Y_one, coeff_c1Y_two, coeff_c1Y_three, coeff_c1Y_four, coeff_c1Y_five, coeff_c1Y_six, coeff_c1Y_seven, coeff_c1Y_eight, coeff_c1Y_nine, coeff_c1Y_ten, coeff_c1Y_eleven,
      coeff_c2Y_zero, coeff_c2Y_one, coeff_c2Y_two, coeff_c2Y_three, coeff_c2Y_four, coeff_c2Y_five, coeff_c2Y_six, coeff_c2Y_seven, coeff_c2Y_eight, coeff_c2Y_nine, coeff_c2Y_ten, coeff_c2Y_eleven,
      coeff_c3Y_zero, coeff_c3Y_one, coeff_c3Y_two, coeff_c3Y_three, coeff_c3Y_four, coeff_c3Y_five, coeff_c3Y_six, coeff_c3Y_seven, coeff_c3Y_eight, coeff_c3Y_nine, coeff_c3Y_ten, coeff_c3Y_eleven,
      coeff_c4Y_zero, coeff_c4Y_one, coeff_c4Y_two, coeff_c4Y_three, coeff_c4Y_four, coeff_c4Y_five, coeff_c4Y_six, coeff_c4Y_seven, coeff_c4Y_eight, coeff_c4Y_nine, coeff_c4Y_ten, coeff_c4Y_eleven,
      GA_coeff_zero, GA_coeff_one, GA_coeff_two, GA_coeff_three, GA_coeff_four, GA_coeff_five, GA_coeff_six, GA_coeff_seven, GA_coeff_eight, GA_coeff_nine, GA_coeff_ten, GA_coeff_eleven, GA_coeff_twelve,
      GA_d1_coeff_zero, GA_d1_coeff_one, GA_d1_coeff_two, GA_d1_coeff_three, GA_d1_coeff_four, GA_d1_coeff_five, GA_d1_coeff_six, GA_d1_coeff_seven, GA_d1_coeff_eight, GA_d1_coeff_nine, GA_d1_coeff_ten, GA_d1_coeff_eleven,
      GA_d2_coeff_zero, GA_d2_coeff_one, GA_d2_coeff_two, GA_d2_coeff_three, GA_d2_coeff_four, GA_d2_coeff_five, GA_d2_coeff_six, GA_d2_coeff_seven, GA_d2_coeff_eight, GA_d2_coeff_nine, GA_d2_coeff_ten,
      GA_d3_coeff_zero, GA_d3_coeff_one, GA_d3_coeff_two, GA_d3_coeff_three, GA_d3_coeff_four, GA_d3_coeff_five, GA_d3_coeff_six, GA_d3_coeff_seven, GA_d3_coeff_eight, GA_d3_coeff_nine,
      GA_d4_coeff_zero, GA_d4_coeff_one, GA_d4_coeff_two, GA_d4_coeff_three, GA_d4_coeff_four, GA_d4_coeff_five, GA_d4_coeff_six, GA_d4_coeff_seven, GA_d4_coeff_eight]
end Submission.CDT
