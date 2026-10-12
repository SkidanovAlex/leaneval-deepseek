import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Conv.hresPairIntPrime_abs_le
import Submission.Work.BoseFixB3.Conv.hresPairInt_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.q3om_sub_q3conv_le`

The **assembly** of the `q3omWord`-vs-`q3convWord` comparison of FS §7
(`lem:Convolution`'s use in `eq:pq'pp-sf` → `eq:ReduceQ3`,
`Papers/fournais_solovej/final_v2.tex` ll. 1518–1545).

Both words are ordered-pair sums (`Conv.Q3omPairDefs`):

  `q3omWord fc κ ℓ w₁ ω Φ = 2 Σ_{i≠j} omPairInt fc κ ℓ w₁ ω i j Φ`,
  `q3convWord fc κ ℓ I Φ = I ℓ⁻³ Σ_{i,j} hresPairInt' fc κ ℓ i j Φ`,

and the hypothesis `hper` of the statement is *exactly* the per-pair output of
`lem:Convolution`

  `omPairIntχ fc κ ℓ (convKernel ℓ v h) i j Φ ≤ ℓ⁻³ (I · hresPairInt fc κ ℓ i j Φ + ρmax χM ∫Φ²)`

once the localised kernel `w₁At(x,y)·ω(x−y) = χ_ℓ(x)·(W₁ω)(x−y)·χ_ℓ(y)` is unfolded
(§1 below).  The hypothesis `|hRes| ≤ B` bounds *every* residual pairing by `B ∫Φ²`,

  `|hresPairInt fc κ ℓ i j Φ| ≤ B ∫Φ²`,   `|hresPairInt' fc κ ℓ i j Φ| ≤ B ∫Φ²`,

so the two words differ only through (i) the `n(n−1)` pairs of `q3omWord` versus the
`n²` pairs of `q3convWord` and (ii) the replacement of `P_jP_iΦ` by `P_jΦ` — FS's
identity `eq:3Qto4Q`.  Three crude `B ∫Φ²` per ordered pair (two for the `i ≠ j` pairs
and one for the `i = j` pairs) would give `3|I|ℓ⁻³B n²∫Φ²`; the slack constant `4` of
the statement absorbs it, and the second term `2ρmaxχMℓ⁻³ n²∫Φ²` comes from the
`lem:Convolution` error on the `n(n−1) ≤ n²` pairs of `q3omWord`.

The work is split as

* §1 the localised kernel identity (`w1At`/`omAt` versus `chiScale`/`convKernel`);
* §2 the pure-arithmetic comparison of the two pair sums
  (`q3om_sub_q3conv_sum_le`), a self-contained statement about two arbitrary pair
  families `om`, `aw`, `aw'` of reals;
* §2b the vanishing-momentum split of the two words into ordered-pair sums;
* §3 the assembly of the target.

All auxiliary lemmas are `private`: this module is imported by `Conv.b3ConvRoot_holds`,
which carries its own (differently proved) versions of the pair-sum identities and of
the localised-kernel identity, so this file must not add global names to the namespace
beyond the target itself.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The localised kernel of `q3omWord` in the form produced by `lem:Convolution` -/

/-- FS's localised `ω`-kernel: `w_{1,0}(x,y)·ω(x−y) = χ_ℓ(x)·(W₁ω)(x−y)·χ_ℓ(y)`,
with `W₁ = wScaled ℓ (g₀ v h)` and `ω = Classical.choose h`. -/
private lemma w1At_mul_omAt (μ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w1At μ (a v) v h x y * omAt h x y
      = chiScale (ellAt μ (a v)) x * convKernel (ellAt μ (a v)) v h (x - y)
          * chiScale (ellAt μ (a v)) y := by
  simp only [w1At, ellAt, omAt, omC, wLoc, wScaled, chiU, chiScale, convKernel, sub_zero]
  ring

/-- The ordered-pair integral of `q3omWord` does not see whether its kernel is written as
`w₁At·ω` or in FS's localised form `χ_ℓ·(W₁ω)·χ_ℓ` (`omPairIntχ`); this is the identity
that lets the `lem:Convolution` per-pair bound `hper` of the target be applied to
`omPairInt`. -/
private lemma omPairInt_eq_omPairIntχ {n : ℕ} {κ : ℝ} {fc : LowCut}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ}
    {Φ : X n → ℝ} (i j : Fin n) :
    omPairInt fc κ (ellAt μ (a v)) (w1At μ (a v) v h) (omAt h) i j Φ
      = omPairIntχ fc κ (ellAt μ (a v)) (convKernel (ellAt μ (a v)) v h) i j Φ := by
  unfold omPairInt omPairIntχ
  apply integral_congr_ae
  filter_upwards with x
  have hk := w1At_mul_omAt μ v h (x i) (x j)
  calc highSlot fc κ (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * aP (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * w1At μ (a v) v h (x i) (x j) * omAt h (x i) (x j)
      = highSlot fc κ (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * aP (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * (w1At μ (a v) v h (x i) (x j) * omAt h (x i) (x j)) := by ring
    _ = highSlot fc κ (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * aP (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
        * (chiScale (ellAt μ (a v)) (x i) * convKernel (ellAt μ (a v)) v h (x i - x j)
            * chiScale (ellAt μ (a v)) (x j)) := by
        rw [hk]

/-! ## 2. The arithmetic comparison of the two pair sums -/

/-- **The pure-arithmetic core of the comparison.**  Given

* a per-pair `lem:Convolution` bound `om i j ≤ ℓ⁻³ (I·aw i j + ρmax χM S)` for `i ≠ j`,
* and per-pair residual bounds `|aw i j| ≤ B S`, `|aw' i j| ≤ B S` for *all* pairs,

the two pair sums differ by at most `(4|I|ℓ⁻³B + 2ℓ⁻³ρmax χM) · n²S`.

Indeed the `n(n−1)` pairs of the first sum give `2ℓ⁻³(I Σ_{i≠j} aw + ρmax χM n(n−1) S)`
and the `n²` pairs of the second `ℓ⁻³ I Σ_{i,j} aw'`; the residual differences
contribute at most `2|I|ℓ⁻³ Bn²S + |I|ℓ⁻³ Bn²S = 3|I|ℓ⁻³Bn²S ≤ 4|I|ℓ⁻³Bn²S`. -/
private theorem q3om_sub_q3conv_sum_le {n : ℕ} {ℓ I B ρmax χM S : ℝ} (hℓ : 0 < ℓ)
    (hB0 : 0 ≤ B) (hρmax0 : 0 ≤ ρmax) (hχM0 : 0 ≤ χM) (hS0 : 0 ≤ S)
    {om aw aw' : Fin n → Fin n → ℝ}
    (hper : ∀ i j : Fin n, i ≠ j → om i j ≤ (ℓ ^ 3)⁻¹ * (I * aw i j + ρmax * χM * S))
    (haw : ∀ i j : Fin n, |aw i j| ≤ B * S)
    (haw' : ∀ i j : Fin n, |aw' i j| ≤ B * S) :
    2 * (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then om i j else 0))
      - I * ℓ ^ (-(3 : ℤ)) * (∑ i : Fin n, ∑ j : Fin n, aw' i j)
      ≤ (4 * |I| * ℓ ^ (-(3 : ℤ)) * B + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM)
          * ((n : ℝ) ^ 2 * S) := by
  have hP : (ℓ ^ 3)⁻¹ = ℓ ^ (-(3 : ℤ)) := by rw [zpow_neg]; norm_num
  have hP0 : 0 ≤ ℓ ^ (-(3 : ℤ)) := zpow_nonneg hℓ.le _
  set Tm : ℝ := ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then om i j else 0) with hTmdef
  set Tw : ℝ := ∑ i : Fin n, ∑ j : Fin n, aw' i j with hTwdef
  set Sw : ℝ := ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then aw i j else 0) with hSwdef
  set W : ℝ := (n : ℝ) ^ 2 * S with hWdef
  have hW0 : 0 ≤ W := by rw [hWdef]; exact mul_nonneg (sq_nonneg _) hS0
  -- (1) the per-pair bound, with the `lem:Convolution` error split off
  have hpt : ∀ i j : Fin n, (if i ≠ j then om i j else 0)
      ≤ (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0)
          + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S) := by
    intro i j
    by_cases hij : i ≠ j
    · rw [if_pos hij, if_pos hij]
      calc om i j ≤ (ℓ ^ 3)⁻¹ * (I * aw i j + ρmax * χM * S) := hper i j hij
        _ = ℓ ^ (-(3 : ℤ)) * (I * aw i j) + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S) := by
              rw [← hP]; ring
    · rw [if_neg hij, if_neg hij]
      have h : 0 ≤ ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S) :=
        mul_nonneg hP0 (mul_nonneg (mul_nonneg hρmax0 hχM0) hS0)
      linarith
  -- (2) the inner sums factor out the prefactor
  have hfac : ∀ i : Fin n, (∑ j : Fin n, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
      = ℓ ^ (-(3 : ℤ)) * (I * (∑ j : Fin n, (if i ≠ j then aw i j else 0))) := by
    intro i
    have h2 : ∀ j : Fin n, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0)
        = ℓ ^ (-(3 : ℤ)) * (I * (if i ≠ j then aw i j else 0)) := by
      intro j
      by_cases hij : i ≠ j
      · rw [if_pos hij, if_pos hij]
      · rw [if_neg hij, if_neg hij]; ring
    calc (∑ j : Fin n, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
        = ∑ j : Fin n, ℓ ^ (-(3 : ℤ)) * (I * (if i ≠ j then aw i j else 0)) :=
          Finset.sum_congr rfl (fun j _ => h2 j)
      _ = ℓ ^ (-(3 : ℤ)) * (∑ j : Fin n, I * (if i ≠ j then aw i j else 0)) := by
          rw [← Finset.mul_sum]
      _ = ℓ ^ (-(3 : ℤ)) * (I * (∑ j : Fin n, (if i ≠ j then aw i j else 0))) := by
          rw [← Finset.mul_sum]
  -- (3) the summed pair bound
  have hTm : Tm ≤ ℓ ^ (-(3 : ℤ)) * (I * Sw) + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W) := by
    rw [hTmdef, hSwdef]
    have hstep : (∑ i, ∑ j, (if i ≠ j then om i j else 0))
        ≤ (∑ i, ∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
            + (n : ℝ) ^ 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) := by
      have hinner : ∀ i : Fin n, (∑ j : Fin n,
            ((if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0)
              + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)))
          = (∑ j : Fin n, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
              + (n : ℝ) * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) := by
        intro i
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      calc (∑ i, ∑ j, (if i ≠ j then om i j else 0))
          ≤ ∑ i, ∑ j, ((if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0)
              + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
        _ = ∑ i, ((∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
              + (n : ℝ) * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S))) :=
            Finset.sum_congr rfl (fun i _ => hinner i)
        _ = (∑ i, ∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
              + (n : ℝ) ^ 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
    have hconv : (∑ i, ∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
        = ℓ ^ (-(3 : ℤ)) * (I * (∑ i, ∑ j, (if i ≠ j then aw i j else 0))) := by
      calc (∑ i, ∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
          = ∑ i, ℓ ^ (-(3 : ℤ)) * (I * (∑ j, (if i ≠ j then aw i j else 0))) :=
            Finset.sum_congr rfl (fun i _ => hfac i)
        _ = ℓ ^ (-(3 : ℤ)) * (I * (∑ i, ∑ j, (if i ≠ j then aw i j else 0))) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc (∑ i, ∑ j, (if i ≠ j then om i j else 0))
        ≤ (∑ i, ∑ j, (if i ≠ j then ℓ ^ (-(3 : ℤ)) * (I * aw i j) else 0))
            + (n : ℝ) ^ 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) := hstep
      _ = ℓ ^ (-(3 : ℤ)) * (I * (∑ i, ∑ j, (if i ≠ j then aw i j else 0)))
            + (n : ℝ) ^ 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * S)) := by rw [hconv]
      _ = ℓ ^ (-(3 : ℤ)) * (I * Sw) + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W) := by
          rw [← hSwdef, hWdef]; ring
  -- (4) `|Sw| ≤ B W`
  have hSw : |Sw| ≤ B * W := by
    rw [hSwdef, hWdef]
    have h1 : |∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then aw i j else 0)|
        ≤ ∑ i : Fin n, ∑ j : Fin n, |(if i ≠ j then aw i j else 0)| := by
      calc |∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then aw i j else 0)|
          ≤ ∑ i : Fin n, |∑ j : Fin n, (if i ≠ j then aw i j else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, |(if i ≠ j then aw i j else 0)| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    calc |∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then aw i j else 0)|
        ≤ ∑ i : Fin n, ∑ j : Fin n, |(if i ≠ j then aw i j else 0)| := h1
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (B * S) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          by_cases hij : i ≠ j
          · rw [if_pos hij]; exact haw i j
          · rw [if_neg hij]; simp only [abs_zero]; exact mul_nonneg hB0 hS0
      _ = B * ((n : ℝ) ^ 2 * S) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  -- (5) `|Tw| ≤ B W`
  have hTw : |Tw| ≤ B * W := by
    rw [hTwdef, hWdef]
    have h1 : |∑ i : Fin n, ∑ j : Fin n, aw' i j| ≤ ∑ i : Fin n, ∑ j : Fin n, |aw' i j| := by
      calc |∑ i : Fin n, ∑ j : Fin n, aw' i j| ≤ ∑ i : Fin n, |∑ j : Fin n, aw' i j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, |aw' i j| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    calc |∑ i : Fin n, ∑ j : Fin n, aw' i j| ≤ ∑ i : Fin n, ∑ j : Fin n, |aw' i j| := h1
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (B * S) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => haw' i j))
      _ = B * ((n : ℝ) ^ 2 * S) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  -- (6) the residual comparison
  have hkey : 2 * (I * Sw) - I * Tw ≤ 4 * |I| * B * W := by
    have h1 : |2 * (I * Sw) - I * Tw| ≤ 2 * |I| * |Sw| + |I| * |Tw| := by
      calc |2 * (I * Sw) - I * Tw| ≤ |2 * (I * Sw)| + |I * Tw| := abs_sub _ _
        _ = 2 * |I| * |Sw| + |I| * |Tw| := by
            simp only [abs_mul]
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            ring
    have h2 : 2 * |I| * |Sw| + |I| * |Tw| ≤ 2 * |I| * (B * W) + |I| * (B * W) := by
      have h3 : 2 * |I| * |Sw| ≤ 2 * |I| * (B * W) :=
        mul_le_mul_of_nonneg_left hSw (by positivity)
      have h4 : |I| * |Tw| ≤ |I| * (B * W) := mul_le_mul_of_nonneg_left hTw (abs_nonneg I)
      linarith
    have habs : 2 * (I * Sw) - I * Tw ≤ 2 * |I| * (B * W) + |I| * (B * W) :=
      le_trans (le_abs_self _) (le_trans h1 h2)
    have hnn : 0 ≤ |I| * (B * W) := mul_nonneg (abs_nonneg I) (mul_nonneg hB0 hW0)
    nlinarith [habs, hnn]
  -- (7) assemble
  have hfinal : 2 * Tm - I * ℓ ^ (-(3 : ℤ)) * Tw
      ≤ (4 * |I| * ℓ ^ (-(3 : ℤ)) * B + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM) * W := by
    have hB' : 2 * (ℓ ^ (-(3 : ℤ)) * (I * Sw) + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W))
        - I * ℓ ^ (-(3 : ℤ)) * Tw
        = ℓ ^ (-(3 : ℤ)) * (2 * (I * Sw) - I * Tw)
            + 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W)) := by
      ring
    have hC : ℓ ^ (-(3 : ℤ)) * (2 * (I * Sw) - I * Tw) ≤ ℓ ^ (-(3 : ℤ)) * (4 * |I| * B * W) :=
      mul_le_mul_of_nonneg_left hkey hP0
    calc 2 * Tm - I * ℓ ^ (-(3 : ℤ)) * Tw
        ≤ 2 * (ℓ ^ (-(3 : ℤ)) * (I * Sw) + ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W))
            - I * ℓ ^ (-(3 : ℤ)) * Tw := by linarith [hTm]
      _ = ℓ ^ (-(3 : ℤ)) * (2 * (I * Sw) - I * Tw)
            + 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W)) := hB'
      _ ≤ ℓ ^ (-(3 : ℤ)) * (4 * |I| * B * W) + 2 * (ℓ ^ (-(3 : ℤ)) * (ρmax * χM * W)) := by
          linarith [hC]
      _ = (4 * |I| * ℓ ^ (-(3 : ℤ)) * B + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM) * W := by ring
  rw [hTmdef, hTwdef] at hfinal
  rw [hWdef] at hfinal
  exact hfinal

/-! ## 2b. The two words as ordered-pair sums -/

/-- `q3omWord` is `2 Σ_{i≠j}` of its ordered-pair integrals. -/
private theorem q3omWord_eq_pairSum_local {fc : LowCut} {κ ℓ : ℝ}
    {w1 ω : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ}
    {Φ : X n → ℝ} :
    q3omWord fc κ ℓ w1 ω Φ
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          (if i ≠ j then omPairInt fc κ ℓ w1 ω i j Φ else 0) := by
  unfold q3omWord omPairInt
  congr 1
  rw [pairSet, Finset.sum_filter, Fintype.sum_prod_type]

/-- `q3convWord` is `I ℓ⁻³ Σ_{i,j}` of the `hRes`-pairings, by the fibre collapse
`Eps.highSlot_chiSq_aP_eq`. -/
private theorem q3convWord_eq_pairSum_local {fc : LowCut} {κ ℓ I : ℝ} {n : ℕ}
    {Φ : X n → ℝ} (hℓ : 0 < ℓ) (hΦ : Continuous Φ) :
    q3convWord fc κ ℓ I Φ
      = I * ℓ ^ (-(3 : ℤ)) * ∑ i : Fin n, ∑ j : Fin n, hresPairInt' fc κ ℓ i j Φ := by
  unfold q3convWord
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hresPairInt']
  apply integral_congr_ae
  filter_upwards with x
  rw [Eps.highSlot_chiSq_aP_eq hℓ hΦ x]

/-! ## 3. The target -/

theorem q3om_sub_q3conv_le {n : ℕ} {κ : ℝ} {fc : Work.BoseBoxFix.LowCut}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ I B ρmax χM : ℝ}
    (hℓ : 0 < Work.BoseFixB3.ellAt μ (BoseGases.a v)) (hB0 : 0 ≤ B)
    (hρmax0 : 0 ≤ ρmax) (hχM0 : 0 ≤ χM)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hI : I = ∫ y, Submission.BoseGases.wScaled (Work.BoseFixB3.ellAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h) y
        * Classical.choose h y)
    (hresb : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixB3.Eps.hRes fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) z| ≤ B)
    (hper : ∀ i j : Fin n, i ≠ j →
      (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
          Work.BoseFixB3.highSlot fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) j
              (Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i Φ) x
            * Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) j
                (Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i Φ) x
            * (Submission.BoseGases.chiScale (Work.BoseFixB3.ellAt μ (BoseGases.a v)) (x i)
                * (Submission.BoseGases.wScaled (Work.BoseFixB3.ellAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h) (x i - x j)
                    * Classical.choose h (x i - x j))
                * Submission.BoseGases.chiScale (Work.BoseFixB3.ellAt μ (BoseGases.a v)) (x j)))
        ≤ ((Work.BoseFixB3.ellAt μ (BoseGases.a v)) ^ 3)⁻¹ *
            (I * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
                  Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i Φ x
                    * (Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) j
                          (Submission.BoseGases.aP (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i Φ) x
                        * Work.BoseFixB3.Eps.hRes fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) (x j)))
              + ρmax * χM * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
                  (Φ x) ^ 2))) :
    Work.BoseFixB3.q3omWord fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v))
        (Work.BoseFixB3.w1At μ (BoseGases.a v) v h) (Work.BoseFixB3.omAt h) (Φ : Submission.BoseGases.X n → ℝ)
      - Work.BoseFixB3.q3convWord fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) I (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (4 * |I| * ((Work.BoseFixB3.ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ))) * B
          + 2 * ((Work.BoseFixB3.ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ))) * ρmax * χM)
        * ((n : ℝ) ^ 2 * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
            (Φ x) ^ 2)) := by
  have hS0 : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
      (Φ x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  -- `hper` is the `lem:Convolution` bound for the localised kernel `omPairIntχ`;
  -- `omPairInt_eq_omPairIntχ` rewrites the `q3omWord` pair integral into that form.
  have hper' : ∀ i j : Fin n, i ≠ j →
      omPairInt fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v))
          (Work.BoseFixB3.w1At μ (BoseGases.a v) v h) (Work.BoseFixB3.omAt h) i j Φ
        ≤ ((Work.BoseFixB3.ellAt μ (BoseGases.a v)) ^ 3)⁻¹ *
            (I * hresPairInt fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i j Φ
              + ρmax * χM * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
                  (Φ x) ^ 2)) := by
    intro i j hij
    rw [omPairInt_eq_omPairIntχ (fc := fc) (κ := κ) (v := v) (h := h) (μ := μ) (Φ := Φ) i j]
    exact hper i j hij
  -- the residual pairings are bounded by `B ∫Φ²` (`hresb`)
  have hres : ∀ i j : Fin n,
      |hresPairInt fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i j Φ|
        ≤ B * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
            (Φ x) ^ 2) :=
    fun i j => hresPairInt_abs_le hℓ hB0 hΦ hresb i j
  have hres' : ∀ i j : Fin n,
      |hresPairInt' fc κ (Work.BoseFixB3.ellAt μ (BoseGases.a v)) i j Φ|
        ≤ B * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB3.ellAt μ (BoseGases.a v)),
            (Φ x) ^ 2) :=
    fun i j => hresPairIntPrime_abs_le hℓ hB0 hΦ hresb i j
  -- split both words into ordered-pair sums
  have hom := q3omWord_eq_pairSum_local (fc := fc) (κ := κ)
    (ℓ := Work.BoseFixB3.ellAt μ (BoseGases.a v))
    (w1 := Work.BoseFixB3.w1At μ (BoseGases.a v) v h) (ω := Work.BoseFixB3.omAt h)
    (n := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
  have hconv := q3convWord_eq_pairSum_local (fc := fc) (κ := κ)
    (ℓ := Work.BoseFixB3.ellAt μ (BoseGases.a v))
    (I := I) (n := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hΦ
  rw [hom, hconv]
  exact q3om_sub_q3conv_sum_le hℓ hB0 hρmax0 hχM0 hS0 hper' hres hres'

end Work.BoseFixB3.Conv
