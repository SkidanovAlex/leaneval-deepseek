/-
# `HBLemma8_1_q` — the requested statement is HB's Lemma 8.1 *without the rectangle (6.1)*

## What is requested

`Work.ZeroFreeTables.HBLemma8_1` (`Submission/Work/ZeroFreeTables/HB8Defs.lean`) asserts: for every
`ε > 0` there is `q₀` such that for every `q ≥ q₀`, real `χ₁` (`χ₁ ^ 2 = 1`) with a real exceptional
zero `ρ₁` (`IsMin1WideAt 10`, `λ₁ = lamOf q ρ₁ ≤ 1/5`) and every *other* zero `ρ₀` of `χ₁` in the
working region `IsZ` (`|Im ρ₀| ≤ 1`) which is `λ`-minimal among those zeros and satisfies
`λ₀ = lamOf q ρ₀ ≥ 4 * exp 1`,

  `(2 - ε) * log (1/λ₁) ≤ λ₀`.

## Why this is not what the paper proves

HB's Lemma 8.1 is stated "under the conditions of Lemma 6.3".  In §6 (p. 26, (6.1)) the zero `ρ₀`
is *by definition* a zero of `L(s,χ₁)` in the rectangle

  `R = {s : 1 - log log 𝓛/(3𝓛) ≤ σ ≤ 1, |t| ≤ 𝓛}`,  `𝓛 = log q`,

namely one with maximal `β` among the zeros of `χ₁` other than `ρ₁` in `R`.  Hence for the `ρ₀` of
Lemma 8.1:

* `λ₀ ≤ (1/3) log log log q = lamMax q`   (the *cap*), and
* `β₀` is maximal among *all* zeros of `L(s,χ₁)` other than `ρ₁` of height `|t| ≤ 𝓛` (a *wide*
  maximality, not merely among the zeros with `|Im| ≤ 1`).

HB states explicitly at the end of §8 (p. 48) that this restriction is essential:
*"the estimates of this section have not been proved for extremely small values of `λ₁`, since we
are only concerned with zeros `ρ₀`, `ρ₂` in the rectangle (6.1)"*.  His `λ₁`-uniform conclusions are
**capped**: Theorem 4 (p. 4) states that for a real non-principal `χ` with an exceptional zero
`1 - λ₁/log q`, `λ₁ ≤ 0.348`, the function `ζ(s)L(s,χ)` has *no* other zero in
`σ ≥ 1 - min{(11/12 - ε)log(1/λ₁), (1/3) log log log q}/log q`, i.e. `λ₀ ≥ min{(11/12 - ε)
log(1/λ₁), lamMax q}` — the cap `lamMax q` is what makes the statement true for tiny `λ₁`.

The formal statement above has neither the cap nor the wide maximality, and no positive floor on
`λ₁`; it is therefore strictly stronger than Lemmas 6.3/8.1 of the source.  The difference is not
cosmetic: in the regime `λ₀ > lamMax q` (which the statement does *not* exclude, and which
`HB81_crux` isolates as the case in which no zero of `χ₁` other than `ρ₁` lies in `R`) the
demanded inequality is the **uncapped** same-character Deuring–Heilbronn repulsion with the
constant `2`.  Neither the paper nor this workspace has that:

* every Deuring–Heilbronn estimate *proved* here (HB §5–§8, `DhCapped/*`, `DhRepel/*`) comes from
  the smoothed explicit formula (HB Lemma 5.1), whose validity is `|Re s - 1| ≤ √(log log q)/log q`,
  so its conclusion is capped at `λ ≲ √(log log q)`; the sharpest proved same-character constants
  are `log(1/λ₁) ≤ 8λ(ρ) + log(64/3)` (`DhRepel.sameCharRepelNear`, cached `λ(ρ) ≤ lamMax q`) and an
  unspecified small `c` for the uncapped forms (`repelOwnFinal`, `sameCharRepelFar`);
* the §7/§8.2 tabulated method (`k = 2/3`) stops at `λ₀b = 11.34`, i.e. covers only
  `λ₁ ≥ 0.006`—cf. Table 2 and HB's "one sees that `λ₀ ≥ 4e` for `λ₁ ≤ 0.006`, and that (8.2) holds
  for `0.006 ≤ λ₁ ≤ 0.2`";
* the deep inputs the project records for the uncapped range (`RepelResidual`, `OwnCharRepel`,
  `dhRepelSameChar`, `dhRepelOtherChar`, `OtherCharZeroCount`, `zeroCountLambdaSaving`) are all of
  the form `∃ c > 0, c·log(1/λ₁) ≤ λ(ρ)` with an unspecified constant, so they cannot give `2`.

Moreover the uncapped form is false under the standard Siegel-zero heuristics: for a real `χ₁`
whose exceptional zero has `log(1/λ₁) ≳ (1/4) log q` (i.e. `λ₁ ≲ q^{-1/4}`, the expected size of
extreme Siegel zeros) and whose other zeros of height `|Im| ≤ 1` lie near `σ = 1/2`
(`λ₀ ≈ (1/2) log q`; then no zero of `χ₁` other than `ρ₁` lies below the cap, so
`HB81_crux`'s hypothesis holds), all hypotheses are met while
`(2 - ε) log(1/λ₁) ≈ (1 - ε/2) log q > (1/2) log q ≈ λ₀`.

## The fix (already applied to the sibling Props)

As recorded in `ENGINE_AUDIT_LEAD.md` §3.1–§3.2, the `λ₁`-uniform Props were corrected by adding a
positive floor `lamS ≤ lamOf q ρ₁`, quantified *before* `q₀` (`HBProps.HBLemma8_4`,
`HBProps.HBLemma8_8`; the same fix is prescribed for `HBTable2and3`, `HBTable7`).  With such a
floor, HB's Lemma 8.1 becomes a **two-line reduction to its capped half**, carried out below:

* if `lamMax q < λ₀` then `log(1/λ₁) ≤ log(1/lamS)` is bounded while `lamMax q → ∞`, so the
  conclusion is immediate (`above_cap_of_floor`);
* otherwise `λ₀ ≤ lamMax q`, i.e. `ρ₀` lies in HB's rectangle (6.1), which is exactly the situation
  in which §8's estimates are proved (`HB81Capped`, and the reduction
  `HBLemma8_1_with_floor_of_capped`).

For the capped half the §6 triangle has to be applied with a test function of support
`x₀ = 1/2 + λ₀⁻¹ + 2ε`, which depends on `λ₀` (a `q`-dependent quantity), while the workspace's §6
lemmas (`DhRepel.dhTrianglePtH`, `HB63_TestFn`) quantify the test function *before* `q₀`.  This is
resolvable, and the resolution is worth recording for whoever proves `HB81Capped`: a **finite**
family of fixed supports suffices — no uniformity over a continuum is needed.

* For a *fixed* support `x₀ = 1/2 + 1/X + 2εₓ` the §8.1 arithmetic gives (`hb81_logBound` below,
  proved from the workspace's `DhRepel.integral_exp_diff_le`/`integral_exp_mul_sub`)
  `log(1/λ₁) ≤ λ₀·(1/2 + 2εₓ + 1/X) + log(4X/λ₀²)`.  For `X = λ₀` this is exactly HB's chain: the
  `1/λ₀` in the support turns the prefactor `λ₀²/(4X)` into `λ₀/4 ≥ 1` (using `λ₀ ≥ 4e`) and makes
  the logarithmic term `log(4/λ₀) ≤ -1` cancel it, giving `λ₀ ≥ (2-8εₓ)log(1/λ₁)`
  (`hb81_eight_two` below).
* For a fixed `X`, that *same* estimate covers the whole **unbounded** range `λ₀ ≥ X`: the exponent
  coefficient is the constant `1/2 + 2εₓ + 1/X` and the logarithmic term is `≤ 0` as soon as
  `λ₀ ≥ X ≥ 4`; so one fixed support `X ≳ 1/ε'²` gives the constant `≥ 2-ε'` for all `λ₀ ≥ X`.
* The remaining range `λ₀ ∈ [4e, X]` is **bounded** and is covered by finitely many dyadic cells
  `[X_k, 2X_k)` with `X_k = 4e·2^k ≤ X`: on each cell, with the fixed support
  `x₀ = 1/2 + 1/X_k + 2ε`, the condition `λ₀ ≥ (2-ε')log(1/λ₁)` becomes a one-variable real
  inequality in `λ₀` (the right-hand side of the display above is increasing in `λ₀` for
  `λ₀ ≤ 2(2-ε')/c`, where `c = 1-(2-ε')(1/2+2εₓ+1/X_k) > 0`), provable by monotonicity.
* Finitely many supports mean that the (existential) thresholds delivered by
  `DhRepel.dhTrianglePtH` can simply be **maxed**: `HB81Capped` is a finite check, not a uniform
  limit.

The capped half `HB81Capped` is requested from the fleet at
`Submission/Work/ZeroFreeTables/HB81_capped`; with it, `HBLemma8_1_with_floor_of_capped` (below)
gives the corrected statement, and `above_cap_of_floor` (below) the other half of the case split.

The `§8.1` arithmetic (`hb81_logBound`, `hb81_eight_two` below) is proved here and is reusable by
any route to `HB81Capped`; the remaining input is exactly one application of the `§6` triangle
(`DhRepel.dhTrianglePtH`) per fixed support.
-/
-- NB the two stub modules `Submission.Work.ZeroFreeTables.HB81_crux` / `HB81_hasR` (imported by an
-- earlier version of this file, for the intended `crux`/`hasR` case split) are *not* imported here:
-- nothing below uses their statements (the R-case is taken as an explicit `Prop` hypothesis in
-- `HBLemma8_1_with_floor_of_capped`), and their import closure currently trips the documented
-- `Commons.NumberTheory.Linnik.pfP` clash (see `Submission/Work/LinnikAreas/ownRepelNW/
-- NOTE_pfP_import_clash.md`), which makes every module importing both unusable.  Restore them once
-- that clash is resolved and the case split is wanted.
import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.LinnikAreas.log_unbounded_nat
import Submission.Work.LinnikAreas.DhRepel.integral_exp_diff_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The triple-logarithmic cap diverges -/

/-- `lamMax q = (1/3) log log log q` is eventually above every constant. -/
theorem lamMax_eventually_ge (C : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → C ≤ lamMax q := by
  obtain ⟨q₁, h₁⟩ := Work.LinnikAreas.log_unbounded_nat (Real.exp (Real.exp (3 * C)))
  refine ⟨max q₁ 3, fun q hq => ?_⟩
  have hq₁ : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq₃ : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h₁' : Real.exp (Real.exp (3 * C)) ≤ Real.log (q : ℝ) := h₁ q hq₁
  have h₂ : Real.exp (3 * C) ≤ Real.log (Real.log (q : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp (3 * C))) h₁'
    rwa [Real.log_exp] at h
  have h₃ : 3 * C ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h := Real.log_le_log (Real.exp_pos (3 * C)) h₂
    rwa [Real.log_exp] at h
  rw [lamMax]
  linarith

/-! ## With a `lam₁`-floor, the range beyond the cap is trivial -/

/-- **The part of HB's Lemma 8.1 beyond the cap, with a floor on `λ₁`.**

If `lamS ≤ λ₁` and `lamMax q < λ₀` then the requested inequality holds with no further input:
`log(1/λ₁) ≤ log(1/lamS)` is bounded, while `lamMax q = (1/3) log log log q` diverges.  This is the
range the source's Lemma 8.1 explicitly does not cover (end of §8), and the range in which the
uncapped statement is false. -/
theorem above_cap_of_floor (ε lamS : ℝ) (hε : 0 < ε) (hS : 0 < lamS) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsZ χ₁ ρ₀ → IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → ρ₀ ≠ ρ₁ →
      (∀ u : ℂ, IsZ χ₁ u → u ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q u) →
      lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ lamOf q ρ₀ →
      lamMax q < lamOf q ρ₀ →
      (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q ρ₀ := by
  obtain ⟨q₀, hq₀⟩ := lamMax_eventually_ge (2 * Real.log (1 / lamS))
  refine ⟨q₀, fun q hq _inst χ₁ ρ₁ ρ₀ _hZ _hw _hsq _him _hne _hmin hfloor _h15 h4e hcap => ?_⟩
  have hlam1pos : 0 < lamOf q ρ₁ := lt_of_lt_of_le hS hfloor
  have hlognn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
    apply Real.log_nonneg
    rw [one_div, one_le_inv₀ hlam1pos]
    linarith
  have hcap' : 2 * Real.log (1 / lamS) ≤ lamMax q := hq₀ q hq
  have h0 : (0 : ℝ) ≤ lamOf q ρ₀ := by linarith [h4e, Real.exp_pos 1]
  rcases le_or_gt 2 ε with hε2 | hε2
  · have hle : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlognn
    linarith
  · have h2e : 0 < 2 - ε := by linarith
    have hmono : Real.log (1 / lamOf q ρ₁) ≤ Real.log (1 / lamS) := by
      apply Real.log_le_log (by positivity)
      rw [one_div, one_div, inv_le_inv₀ hlam1pos hS]
      exact hfloor
    rcases le_or_gt lamS 1 with hS1 | hS1
    · have hSnn : 0 ≤ Real.log (1 / lamS) := by
        apply Real.log_nonneg
        rw [one_div, one_le_inv₀ hS]
        exact hS1
      calc (2 - ε) * Real.log (1 / lamOf q ρ₁)
          ≤ (2 - ε) * Real.log (1 / lamS) := mul_le_mul_of_nonneg_left hmono h2e.le
        _ ≤ 2 * Real.log (1 / lamS) :=
            mul_le_mul_of_nonneg_right (by linarith : 2 - ε ≤ 2) hSnn
        _ ≤ lamMax q := hcap'
        _ ≤ lamOf q ρ₀ := hcap.le
    · have hSinv : 1 / lamS < 1 := by
        rw [div_lt_one hS]; linarith
      have hSneg : Real.log (1 / lamS) < 0 := Real.log_neg (by positivity) hSinv
      have hle : (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ 0 := by
        nlinarith [hmono, h2e, hSneg]
      linarith

/-! ## The capped half of HB's Lemma 8.1, and the reduction to it -/

/-- **HB's Lemma 8.1 for zeros of the rectangle (6.1)** (the capped half).

Same statement as `Work.ZeroFreeTables.HBLemma8_1` except that `ρ₀` is required to satisfy HB's
rectangle condition `λ₀ ≤ lamMax q` (i.e. `ρ₀ ∈ R`, (6.1)), and that the maximality of `ρ₀` is
taken over the box `|Im| ≤ 2` (what HB's §6 numbering supplies: `ρ₀` has maximal `β` among the
zeros of `χ₁` other than `ρ₁` of height `|t| ≤ 𝓛`, and the §6 triangle only ever looks at the
window `|1 + iγ₀ - ρ| ≤ δ` with `δ < 1`).  This is the statement HB proves in §8.1 (his
`(8.1)` → `(8.2)`), and the only part of the requested `Prop` that the source supports. -/
def HB81Capped : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
    (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 2 → u ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q u) →
    lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ lamOf q ρ₀ → lamOf q ρ₀ ≤ lamMax q →
    (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q ρ₀

/-- **The corrected form of HB's Lemma 8.1**: with a positive floor on `λ₁` (and `ρ₀` maximisation
over `|Im| ≤ 2`, as the §6 numbering gives), the statement follows from its capped half alone. -/
theorem HBLemma8_1_with_floor_of_capped (h : HB81Capped) :
    ∀ ε : ℝ, 0 < ε → ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
      (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 2 → u ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q u) →
      lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ lamOf q ρ₀ →
      (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q ρ₀ := by
  intro ε hε lamS hS
  obtain ⟨q₁, h₁⟩ := h ε hε
  obtain ⟨q₂, h₂⟩ := above_cap_of_floor ε lamS hε hS
  refine ⟨max q₁ q₂, fun q hq _inst χ₁ ρ₁ ρ₀ hw hsq him hZ hne hmax hfloor h15 h4e => ?_⟩
  by_cases hcap : lamOf q ρ₀ ≤ lamMax q
  · exact h₁ q (le_trans (le_max_left _ _) hq) χ₁ ρ₁ ρ₀ hw hsq him hZ hne hmax h15 h4e hcap
  · refine h₂ q (le_trans (le_max_right _ _) hq) χ₁ ρ₁ ρ₀ hZ hw hsq him hne ?_ hfloor h15 h4e
      (not_le.mp hcap)
    intro u hu hune
    exact hmax u hu.2.1 (le_trans hu.2.2 (by norm_num)) hune


/-! ## The `§8.1` arithmetic of HB's Lemma 8.1 (the second half of `HB81Capped`)

Everything here is *conditional on the `§6` inequality* (the only hard input of `HB81Capped`) and
is what converts it into the repulsion `λ₀ ≥ (2-ε)log(1/λ₁)`.  The integral estimate it uses is
already proved in the workspace (`DhRepel.integral_exp_diff_le`, importing only Mathlib). -/

/-- **HB's `(8.1) ⇒ log(1/λ₁) ≤ x₀λ₀ + log(4X/λ₀²)`.**

From the `§6` triangle inequality (HB `(8.1)`) with the triangle of support
`x₀ = 1/2 + 1/X + 2εₓ` and the `§6` slack `C = 1/4 + εc ≥ 1/4 + εₓ`,

  `2F(-λ₀) - 2F(λ₁-λ₀) - F(0) + f(0)·C ≥ 0`,

this bounds `log(1/λ₁)`.  The proof is HB's: `F(-λ₀) - F(λ₁-λ₀) ≤ λ₁·x₀e^{x₀λ₀}/λ₀²`
(`DhRepel.integral_exp_diff_le`), so `λ₁ ≥ λ₀²(x₀/2 - C)/(2e^{x₀λ₀}) ≥ λ₀²/(4Xe^{x₀λ₀})`, since
`x₀/2 - C = 1/(2X) + εₓ - εc ≥ 1/(2X)`. -/
theorem hb81_logBound {x₀ X lam₀ lam₁ C εx εc : ℝ} (hX : 0 < X) (hlam₀ : 0 < lam₀)
    (hlam₁ : 0 < lam₁) (hεx : 0 ≤ εx)
    (hx : x₀ = 1 / 2 + 1 / X + 2 * εx) (hC : C = 1 / 4 + εc) (hcε : εc ≤ εx)
    (h6 : 0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp (lam₀ * t) * (x₀ - t))
        - 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((lam₀ - lam₁) * t) * (x₀ - t))
        - x₀ ^ 2 / 2 + C * x₀) :
    Real.log (1 / lam₁) ≤ x₀ * lam₀ + Real.log (4 * X / lam₀ ^ 2) := by
  have hx₀ : 0 < x₀ := by
    rw [hx]
    have h1 : 0 < 1 / X := by positivity
    linarith
  have hx₀' : 0 ≤ x₀ := hx₀.le
  -- combine the two integrals
  have hsplit : (∫ t in (0:ℝ)..x₀, Real.exp (lam₀ * t) * (x₀ - t))
      - (∫ t in (0:ℝ)..x₀, Real.exp ((lam₀ - lam₁) * t) * (x₀ - t))
      = ∫ t in (0:ℝ)..x₀,
          (Real.exp (lam₀ * t) - Real.exp ((lam₀ - lam₁) * t)) * (x₀ - t) := by
    rw [← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr (fun t _ => by ring)
    · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (lam₀ * t) * (x₀ - t))).intervalIntegrable _ _
    · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp ((lam₀ - lam₁) * t) * (x₀ - t))).intervalIntegrable _ _
  -- HB's estimate for `F(-lam₀) - F(lam₁-lam₀)`
  have hbnd : (∫ t in (0:ℝ)..x₀, (Real.exp (lam₀ * t) - Real.exp ((lam₀ - lam₁) * t)) * (x₀ - t))
      ≤ lam₁ * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2 :=
    Work.LinnikAreas.DhRepel.integral_exp_diff_le lam₀ lam₁ x₀ hlam₀ hlam₁.le hx₀'
  -- the `§6` inequality, rewritten with the combined integral
  have h6' : x₀ * (x₀ / 2 - C) ≤ 2 * (∫ t in (0:ℝ)..x₀,
      (Real.exp (lam₀ * t) - Real.exp ((lam₀ - lam₁) * t)) * (x₀ - t)) := by
    linarith [h6, hsplit]
  -- `x₀/2 - C = 1/(2X) + εx - εc ≥ 1/(2X)`
  have hgain : 1 / (2 * X) ≤ x₀ / 2 - C := by
    rw [hx, hC]; ring_nf; linarith
  have hkey : x₀ * (1 / (2 * X)) ≤ 2 * (lam₁ * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2) := by
    refine le_trans (mul_le_mul_of_nonneg_left hgain hx₀') ?_
    linarith [h6', hbnd]
  -- solve for `lam₁`
  have hpos : 0 < 2 * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2 := by positivity
  have h3 : x₀ / (2 * X) ≤ lam₁ * (2 * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2) := by
    have e1 : x₀ * (1 / (2 * X)) = x₀ / (2 * X) := by ring
    have e2 : 2 * (lam₁ * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2)
        = lam₁ * (2 * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2) := by ring
    rw [e1, e2] at hkey
    exact hkey
  have h6'' : x₀ / (2 * X) / (2 * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2) ≤ lam₁ :=
    (div_le_iff₀ hpos).mpr h3
  have h7eq : x₀ / (2 * X) / (2 * (x₀ * Real.exp (lam₀ * x₀)) / lam₀ ^ 2)
      = lam₀ ^ 2 / (4 * X * Real.exp (lam₀ * x₀)) := by
    field_simp
    ring
  have h8 : lam₀ ^ 2 / (4 * X * Real.exp (lam₀ * x₀)) ≤ lam₁ := by
    rw [← h7eq]; exact h6''
  have h8pos : 0 < lam₀ ^ 2 / (4 * X * Real.exp (lam₀ * x₀)) := by positivity
  have h9 : 1 / lam₁ ≤ 4 * X * Real.exp (lam₀ * x₀) / lam₀ ^ 2 := by
    have h := one_div_le_one_div_of_le h8pos h8
    simpa [one_div_div] using h
  refine le_trans (Real.log_le_log (by positivity) h9) ?_
  have hlog : Real.log (4 * X * Real.exp (lam₀ * x₀) / lam₀ ^ 2)
      = Real.log (4 * X / lam₀ ^ 2) + lam₀ * x₀ := by
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
        Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hX.ne']
    ring
  rw [hlog]
  exact le_of_eq (by ring)

/-- **HB's `(8.2)`**: with the `λ₀`-dependent support `x₀ = 1/2 + λ₀⁻¹ + 2εₓ` (HB's choice), the
`§6` triangle inequality gives `(2 - 8εₓ)·log(1/λ₁) ≤ λ₀`, the repulsion of HB's Lemma 8.1 with the
constant `2` (renaming `εₓ = ε/8` recovers `(2-ε)`).  The `λ₀⁻¹` in the support is what makes the
prefactor `λ₀²/(4X) = λ₀/4 ≥ 1` (using `λ₀ ≥ 4e`) cancels the logarithmic term `log(4/λ₀) ≤ -1`. -/
theorem hb81_eight_two {x₀ lam₀ lam₁ C εx εc : ℝ} (hlam₀ : 4 * Real.exp 1 ≤ lam₀)
    (hlam₁ : 0 < lam₁) (hεx : 0 ≤ εx) (hεx' : 8 * εx ≤ 1)
    (hx : x₀ = 1 / 2 + 1 / lam₀ + 2 * εx) (hC : C = 1 / 4 + εc) (hcε : εc ≤ εx)
    (h6 : 0 ≤ 2 * (∫ t in (0:ℝ)..x₀, Real.exp (lam₀ * t) * (x₀ - t))
        - 2 * (∫ t in (0:ℝ)..x₀, Real.exp ((lam₀ - lam₁) * t) * (x₀ - t))
        - x₀ ^ 2 / 2 + C * x₀) :
    (2 - 8 * εx) * Real.log (1 / lam₁) ≤ lam₀ := by
  have hlam₀pos : 0 < lam₀ := by linarith [Real.exp_pos 1]
  have hbound := hb81_logBound (X := lam₀) hlam₀pos hlam₀pos hlam₁ hεx hx hC hcε h6
  -- `x₀·λ₀ = λ₀/2 + 1 + 2εₓλ₀` and `log(4λ₀/λ₀²) = log(4/λ₀) ≤ -1`
  have hxlam : x₀ * lam₀ = lam₀ / 2 + 1 + 2 * εx * lam₀ := by
    rw [hx]; field_simp
  have hlogeq : 4 * lam₀ / lam₀ ^ 2 = 4 / lam₀ := by
    field_simp
  rw [hlogeq] at hbound
  have hlog1 : Real.log (4 / lam₀) ≤ -1 := by
    have h4e : 4 / lam₀ ≤ Real.exp (-1) := by
      rw [Real.exp_neg, div_le_iff₀ hlam₀pos, mul_comm, ← div_eq_mul_inv,
        le_div_iff₀ (Real.exp_pos 1)]
      exact hlam₀
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 4 / lam₀) h4e
    rwa [Real.log_exp] at h
  have hL : Real.log (1 / lam₁) ≤ lam₀ * (1 / 2 + 2 * εx) := by
    linarith [hbound, hxlam, hlog1]
  rcases le_or_gt lam₁ 1 with hle | hgt
  · have hLnn : 0 ≤ Real.log (1 / lam₁) := by
      apply Real.log_nonneg
      rw [one_div, one_le_inv₀ hlam₁]; exact hle
    have hden : 0 < 1 / 2 + 2 * εx := by linarith
    have hconst : (2 - 8 * εx) ≤ 1 / (1 / 2 + 2 * εx) := by
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg εx]
    calc (2 - 8 * εx) * Real.log (1 / lam₁)
        ≤ (1 / (1 / 2 + 2 * εx)) * Real.log (1 / lam₁) :=
          mul_le_mul_of_nonneg_right hconst hLnn
      _ ≤ (1 / (1 / 2 + 2 * εx)) * (lam₀ * (1 / 2 + 2 * εx)) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = lam₀ := by field_simp
  · have hLneg : Real.log (1 / lam₁) < 0 := by
      refine Real.log_neg (by positivity) ?_
      rw [one_div]
      exact inv_lt_one_of_one_lt₀ hgt
    have : (2 - 8 * εx) * Real.log (1 / lam₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hLneg.le
    linarith

/-! ## The statement

The floored statement `Work.ZeroFreeTables.HBLemma8_1` itself is *not* proved here: it is proved at
`Submission/Work/ZeroFreeTables/HBLemma8_1_witness.lean`
(`Work.ZeroFreeTables.HBLemma8_1_witness`), via the witness/triangle route of
`NOTE_HBLemma8_1_route.md`.  This module keeps the capped half and the two reductions below it.
-/

end Work.ZeroFreeTables
