/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymLin
import Submission.Vinogradov.SymFromAsym
import Submission.Commons.Analysis.Asymptotics.linear_le_mul_two_rpow
import Submission.Vinogradov.DecLinLift

/-!
# STEP 4 of GLYZ §4: the lower bound `η ≤ Cb + A_l(b)`

GLYZ (4.4): for every `l ∈ {1,…,k−1}` and every `b ∈ [0,1]` with `b ≤ l/(k−l+1)`,
`η ≤ C·b + A_l(b)` with `C = ((k−l+1)/l)·(p_l/p_k) + (p_k−p_l)/p_k`.

The proof uses Lemma 2.1 (bilinear reduction, `LinearFromBilinear.decLin_of_bilinDec`) and
Lemma 3.4 (`SymFromAsym.symDec_of_asymDec`, our sharpening of GLYZ Lemma 3.6's first step):
for every level `N'`, the asymmetric bilinear statement at the canonical pair
`(⌊ρbN'⌋, ⌊bN'⌋)` gives the symmetric one at the same scale, with the explicit constant
`symDecConst`; that constant is dominated by `K₀·K·2^{N'(bC+A)}`, where `K` is the constant of the
asymmetric statement and `K₀` depends only on `k, l, b, uncConst`.

This module contains the *constant bookkeeping* of that step:
* `symConstBase` — the real number `U₀ = (uncConst^{p_k−2}·8^{k(k+1)})^{1/p_k}`;
* `asymConst₁_le_ofReal`, `asymConst₂_le_ofReal` — the two factors of `symDecConst` as `ofReal`s;
* `symDecConst_le_ofReal` — the real-valued form of `symDecConst`;
* `symDecConst_le_exp` — its consumer form, with the exponent `N'(bC+A)`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Submission.Vinogradov

/-! ## 1. The base constant of the symmetric bilinear bound -/

/-- The base constant `U₀ = (uncConst^{p_l−1}·uncConst^{p_k−p_l−1}·8^{k(k+1)})^{1/p_k}` of
GLYZ Lemma 3.4 (a real number depending only on `k`, `l` and the uncertainty constant). -/
noncomputable def symConstBase (k l : ℕ) (hk : 1 ≤ k) : ℝ :=
  ((((uncConst k hk).toReal) ^ (plExp l - 1)
      * (((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1))
      * (((8 : ℝ) ^ (k * (k + 1) / 2)) ^ 2))) ^ (1 / pkExp k)

lemma symConstBase_nonneg (k l : ℕ) (hk : 1 ≤ k) : 0 ≤ symConstBase k l hk :=
  Real.rpow_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (by positivity)) _

/-! ## 2. The two factors of `symDecConst` -/

/-- `asymConst₁`, as an explicit `ofReal`. -/
lemma asymConst₁_le_ofReal {k l m : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hm : 2 ≤ m) :
    asymConst₁ k l m hk
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
          * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2))) := by
  have hpl1 : 0 ≤ plExp l - 1 := by
    have h : (1 : ℝ) ≤ plExp l := by
      rw [plExp]
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    linarith
  have hUnc : ENNReal.ofReal ((uncConst k hk).toReal) = uncConst k hk :=
    ENNReal.ofReal_toReal (uncConst_ne_top k hk)
  have hA : (((2 ^ (m - 2) : ℕ) : ℝ≥0∞)) ^ (plExp l - 1)
      = ENNReal.ofReal ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))) := by
    rw [show (((2 ^ (m - 2) : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((2 : ℝ) ^ ((m - 2 : ℕ) : ℝ)) from by
      rw [Nat.cast_pow, Nat.cast_ofNat]; simp]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by norm_num) _) hpl1,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hB : (uncConst k hk) ^ (plExp l - 1)
      ≤ ENNReal.ofReal (((uncConst k hk).toReal) ^ (plExp l - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpl1, hUnc]
  have hX1 : 0 ≤ (2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1)) :=
    Real.rpow_nonneg (by norm_num) _
  have hX2 : 0 ≤ ((uncConst k hk).toReal) ^ (plExp l - 1) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hX3 : 0 ≤ ((8 : ℝ) ^ (k * (k + 1) / 2)) := by positivity
  rw [asymConst₁]
  calc (((2 ^ (m - 2) : ℕ) : ℝ≥0∞) ^ (plExp l - 1) * (uncConst k hk) ^ (plExp l - 1))
        * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1)))
            * ENNReal.ofReal (((uncConst k hk).toReal) ^ (plExp l - 1)))
          * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)) := by
        exact mul_le_mul' (by rw [hA]; exact mul_le_mul' le_rfl hB) le_rfl
    _ = ENNReal.ofReal ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
          * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2))) := by
        rw [← ENNReal.ofReal_mul hX1, ← ENNReal.ofReal_mul (mul_nonneg hX1 hX2)]


/-- `asymConst₂`, as an explicit `ofReal`. -/
lemma asymConst₂_le_ofReal {k l m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm' : 2 ≤ m') :
    asymConst₂ k l m' hk
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
          * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
          * ((8 : ℝ) ^ (k * (k + 1) / 2))) := by
  have hrs1 : 0 ≤ pkExp k - plExp l - 1 := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    have hlk' : (l : ℝ) ≤ (k : ℝ) - 1 := cast_le_sub_one hk hlk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [h1]; nlinarith
  have hUnc : ENNReal.ofReal ((uncConst k hk).toReal) = uncConst k hk :=
    ENNReal.ofReal_toReal (uncConst_ne_top k hk)
  have hA : (((2 ^ (m' - 2) : ℕ) : ℝ≥0∞)) ^ (pkExp k - plExp l - 1)
      = ENNReal.ofReal ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))) := by
    rw [show (((2 ^ (m' - 2) : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal ((2 : ℝ) ^ ((m' - 2 : ℕ) : ℝ)) from by
      rw [Nat.cast_pow, Nat.cast_ofNat]; simp]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by norm_num) _) hrs1,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hB : (uncConst k hk) ^ (pkExp k - plExp l - 1)
      ≤ ENNReal.ofReal (((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hrs1, hUnc]
  have hX1 : 0 ≤ (2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1)) :=
    Real.rpow_nonneg (by norm_num) _
  have hX2 : 0 ≤ ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [asymConst₂]
  calc (((2 ^ (m' - 2) : ℕ) : ℝ≥0∞) ^ (pkExp k - plExp l - 1)
          * (uncConst k hk) ^ (pkExp k - plExp l - 1))
        * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1)))
            * ENNReal.ofReal (((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)))
          * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)) := by
        exact mul_le_mul' (by rw [hA]; exact mul_le_mul' le_rfl hB) le_rfl
    _ = ENNReal.ofReal ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
          * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
          * ((8 : ℝ) ^ (k * (k + 1) / 2))) := by
        rw [← ENNReal.ofReal_mul hX1, ← ENNReal.ofReal_mul (mul_nonneg hX1 hX2)]


/-- **The real-valued form of GLYZ Lemma 3.4's constant** (`SymFromAsym.symDecConst`): the
symmetric bilinear constant at level `N` produced by the asymmetric statement at the levels `m,m'`
with an `ofReal` constant `c` is bounded by `ofReal (U₀·c·2^{E/p_k})` with
`E = (m−2)(p_l−1) + (m'−2)(p_k−p_l−1)` and `U₀ = symConstBase k l hk`. -/
lemma symDecConst_le_ofReal {k l m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm : 2 ≤ m) (hm' : 2 ≤ m') {c : ℝ} (hc : 0 ≤ c) :
    symDecConst k l m m' hk (ENNReal.ofReal c)
      ≤ ENNReal.ofReal (symConstBase k l hk * c
          * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
              + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)) := by
  have hP : 0 < pkExp k := pkExp_pos hk
  have hPne : pkExp k ≠ 0 := ne_of_gt hP
  have hUc0 : 0 ≤ (uncConst k hk).toReal := ENNReal.toReal_nonneg
  have h8 : 0 ≤ (8 : ℝ) ^ (k * (k + 1) / 2) := by positivity
  have hpl1 : 0 ≤ plExp l - 1 := by
    have h : (1 : ℝ) ≤ plExp l := by
      rw [plExp]
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    linarith
  have hrs1 : 0 ≤ pkExp k - plExp l - 1 := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    have hlk' : (l : ℝ) ≤ (k : ℝ) - 1 := cast_le_sub_one hk hlk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [h1]; nlinarith
  have hA₁ := asymConst₁_le_ofReal (l := l) hk hl hm
  have hA₂ := asymConst₂_le_ofReal (l := l) hk hl hlk hm'
  have hcP : (ENNReal.ofReal c) ^ (pkExp k) = ENNReal.ofReal (c ^ pkExp k) :=
    ENNReal.ofReal_rpow_of_nonneg hc (pkExp_nonneg k)
  have hX1 : 0 ≤ (2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
      * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hUc0 _)) h8
  have hX2 : 0 ≤ (2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
      * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hUc0 _)) h8
  have hprod : asymConst₁ k l m hk * asymConst₂ k l m' hk * (ENNReal.ofReal c) ^ (pkExp k)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k)) := by
    rw [hcP]
    calc asymConst₁ k l m hk * asymConst₂ k l m' hk * ENNReal.ofReal (c ^ pkExp k)
        ≤ (ENNReal.ofReal ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
              * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
            * ENNReal.ofReal ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
              * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
              * ((8 : ℝ) ^ (k * (k + 1) / 2))))
          * ENNReal.ofReal (c ^ pkExp k) :=
          mul_le_mul' (mul_le_mul' hA₁ hA₂) le_rfl
      _ = ENNReal.ofReal (((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k)) := by
        rw [← ENNReal.ofReal_mul hX1, ← ENNReal.ofReal_mul (mul_nonneg hX1 hX2)]
  -- the real identity: the `p_k`-th power of the claimed bound is the product above
  have hE : 0 ≤ (((m - 2 : ℕ) : ℝ) * (plExp l - 1)
      + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k := by
    apply div_nonneg _ hP.le
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hpl1) (mul_nonneg (Nat.cast_nonneg _) hrs1)
  have hbase : 0 ≤ symConstBase k l hk := symConstBase_nonneg k l hk
  have hd : 0 ≤ (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
      + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k) :=
    Real.rpow_nonneg (by norm_num) _
  have hW : symConstBase k l hk ^ (pkExp k)
      = ((uncConst k hk).toReal) ^ (plExp l - 1) * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
        * (((8 : ℝ) ^ (k * (k + 1) / 2)) ^ 2) := by
    rw [symConstBase, ← Real.rpow_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hUc0 _)
      (Real.rpow_nonneg hUc0 _)) (by positivity)) (1 / pkExp k) (pkExp k),
      one_div_mul_cancel hPne, Real.rpow_one]
  have hD : ((2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
        + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)) ^ (pkExp k)
      = (2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
        * (2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      div_mul_cancel₀ _ hPne,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have htarget : (symConstBase k l hk * c * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
        + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)) ^ (pkExp k)
      = ((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k) := by
    rw [Real.mul_rpow (mul_nonneg hbase hc) hd, Real.mul_rpow hbase hc, hW, hD]
    ring
  have hZ : (((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k)) ^ (1 / pkExp k)
      = symConstBase k l hk * c * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
          + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k) := by
    have htarget0 : 0 ≤ symConstBase k l hk * c
        * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
            + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k) :=
      mul_nonneg (mul_nonneg hbase hc) hd
    rw [← htarget, ← Real.rpow_mul htarget0 (pkExp k) (1 / pkExp k),
      mul_one_div_cancel hPne, Real.rpow_one]
  calc symDecConst k l m m' hk (ENNReal.ofReal c)
      = (asymConst₁ k l m hk * asymConst₂ k l m' hk * (ENNReal.ofReal c) ^ (pkExp k))
          ^ (1 / pkExp k) := rfl
    _ ≤ (ENNReal.ofReal (((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k))) ^ (1 / pkExp k) :=
        ENNReal.rpow_le_rpow hprod (by positivity)
    _ = ENNReal.ofReal ((((2 : ℝ) ^ (((m - 2 : ℕ) : ℝ) * (plExp l - 1))
            * ((uncConst k hk).toReal) ^ (plExp l - 1) * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ((2 : ℝ) ^ (((m' - 2 : ℕ) : ℝ) * (pkExp k - plExp l - 1))
            * ((uncConst k hk).toReal) ^ (pkExp k - plExp l - 1)
            * ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * c ^ (pkExp k)) ^ (1 / pkExp k)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ = ENNReal.ofReal (symConstBase k l hk * c * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
          + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)) := by rw [hZ]

/-! ## 3. The crude (trivial) bilinear constants

For the finitely many levels below the threshold of the asymmetric hypothesis we use the trivial
bound `asymDec_crude`, which is valid at *every* level and gives an explicit constant. -/

/-- The trivial (crude) bilinear constant at level `N`. -/
noncomputable def asymCrudeConst (k : ℕ) (hk : 1 ≤ k) (N : ℕ) : ℝ :=
  ((((uncConst k hk) ^ 2).toReal) * (2 : ℝ) ^ ((N : ℝ) * pkExp k / 2)) ^ (1 / pkExp k)

lemma asymCrudeConst_nonneg (k : ℕ) (hk : 1 ≤ k) (N : ℕ) : 0 ≤ asymCrudeConst k hk N :=
  Real.rpow_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by norm_num) _)) _

lemma asymCrudeConst_mono (k : ℕ) (hk : 1 ≤ k) {N N' : ℕ} (h : N ≤ N') :
    asymCrudeConst k hk N ≤ asymCrudeConst k hk N' := by
  have hP : 0 < pkExp k := pkExp_pos hk
  rw [asymCrudeConst, asymCrudeConst]
  refine Real.rpow_le_rpow
    (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by norm_num) _)) ?_
    (by positivity : (0 : ℝ) ≤ 1 / pkExp k)
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have h' : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [h', hP])

/-- **The trivial bound in `AsymDec` form.**  `asymDec_crude` gives the asymmetric bilinear
inequality at *every* level with the explicit constant `asymCrudeConst k hk N`. -/
lemma asymDec_crude_ofReal {k l N : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hN : 2 ≤ N) :
    AsymDec k hk l N 2 2 (ENNReal.ofReal (asymCrudeConst k hk N)) := by
  have hP : 0 < pkExp k := pkExp_pos hk
  have hPne : pkExp k ≠ 0 := ne_of_gt hP
  have h2ne : ((uncConst k hk) ^ 2) ≠ ⊤ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top (uncConst_ne_top k hk) (uncConst_ne_top k hk)
  have hc0 : 0 ≤ (((uncConst k hk) ^ 2).toReal) := ENNReal.toReal_nonneg
  have hexp0 : 0 ≤ (N : ℝ) * pkExp k / 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) hP.le) (by norm_num)
  have hw : 0 ≤ (((uncConst k hk) ^ 2).toReal) * (2 : ℝ) ^ ((N : ℝ) * pkExp k / 2) :=
    mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)
  have hCcP : (ENNReal.ofReal (asymCrudeConst k hk N)) ^ (pkExp k)
      = ENNReal.ofReal ((((uncConst k hk) ^ 2).toReal) * (2 : ℝ) ^ ((N : ℝ) * pkExp k / 2)) := by
    rw [asymCrudeConst]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (x := ((((uncConst k hk) ^ 2).toReal) * (2 : ℝ) ^ ((N : ℝ) * pkExp k / 2)) ^ (1 / pkExp k))
      (Real.rpow_nonneg hw _) hP.le]
    rw [← Real.rpow_mul hw (1 / pkExp k) (pkExp k), one_div_mul_cancel hPne, Real.rpow_one]
  have hmid : (2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2) * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2)
      = ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) * pkExp k / 2)) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _
      (div_nonneg (mul_nonneg (Nat.cast_nonneg N) (plExp_nonneg l)) (by norm_num))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg N) (pkExp_sub_plExp_nonneg (by omega))) (by norm_num))]
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hexp0,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
    congr 1
    ring
  have hunc : (uncConst k hk) ^ 2
      = ENNReal.ofReal (((uncConst k hk) ^ 2).toReal) := (ENNReal.ofReal_toReal h2ne).symm
  intro q q' hsep f hf
  refine (asymDec_crude hk hlk le_rfl le_rfl hN hN q q' f hf).trans ?_
  rw [hCcP, hmid]
  conv_lhs => rw [hunc, ← ENNReal.ofReal_mul hc0]

/-- `2 ≤ lvlOf c N` from the explicit threshold `⌈2/c⌉ + 1 ≤ N`. -/
lemma two_le_lvlOf_of_le {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : ⌈2 / c⌉₊ + 1 ≤ N) :
    2 ≤ lvlOf c N := by
  refine two_le_lvlOf ?_
  have h1 : 2 / c ≤ (⌈2 / c⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈2 / c⌉₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
  calc (2 : ℝ) = (2 / c) * c := by rw [div_mul_cancel₀ _ hc.ne']
    _ ≤ (N : ℝ) * c := mul_le_mul_of_nonneg_right (by linarith) hc.le
    _ = c * (N : ℝ) := by ring

/-- **The crude symmetric/bilinear bound at every level.** -/
lemma bilinDec_crude {k l N : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hN : 2 ≤ N) :
    BilinDec k (2 ^ (N - 2)) (ENNReal.ofReal (symConstBase k l hk * asymCrudeConst k hk N)) := by
  have hSym := symDec_of_asymDec (k := k) (l := l) (N := N) (m := 2) (m' := 2)
    hk hl hlk le_rfl (by omega) le_rfl (by omega)
    (asymDec_crude_ofReal hk hl hlk hN)
  have hle := symDecConst_le_ofReal (k := k) (l := l) (m := 2) (m' := 2)
    (c := asymCrudeConst k hk N) hk hl hlk le_rfl le_rfl (asymCrudeConst_nonneg k hk N)
  have hzero : ((2 - 2 : ℕ) : ℝ) * (plExp l - 1)
      + (((2 - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1) = 0 := by norm_num
  have h2 : (symDecConst k l 2 2 hk (ENNReal.ofReal (asymCrudeConst k hk N)))
      ≤ ENNReal.ofReal (symConstBase k l hk * asymCrudeConst k hk N) := by
    refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hzero, zero_div, Real.rpow_zero, mul_one]
  exact bilinDec_of_symDec hN (symDec_mono h2 hSym)

/-! ## 4. The exponent `C` of GLYZ (4.4) -/

/-- The coefficient `C` of GLYZ (4.4): `η ≤ C·b + A_l(b)` with
`C = ((k−l+1)/l)(p_l/p_k) + (p_k−p_l)/p_k`. -/
noncomputable def bilinCoef (k l : ℕ) : ℝ :=
  asymRatio k l * (plExp l / pkExp k) + (pkExp k - plExp l) / pkExp k

/-- `1 − linCoef k l b = b · bilinCoef k l`: the coefficient of GLYZ (4.5) is the complement of
the one of (4.4). -/
lemma one_sub_linCoef {k l : ℕ} (hk : 1 ≤ k) (b : ℝ) :
    1 - linCoef k l b = b * bilinCoef k l := by
  have hP : pkExp k ≠ 0 := ne_of_gt (pkExp_pos hk)
  rw [linCoef, bilinCoef]
  field_simp
  ring

/-- **The consumer form of the constant bound**: the symmetric bilinear constant produced at level
`N'` out of the asymmetric statement with constant `K·2^{N'A}` at level ratios `(ρb, b)` is
dominated by `ofReal (U₀·K·2^{N'(bC+A)})`. -/
lemma symDecConst_le_exp {k l m m' N' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm : 2 ≤ m) (hm' : 2 ≤ m') {b K A : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hmN : (m : ℝ) ≤ asymRatio k l * b * (N' : ℝ) + 1)
    (hm'N : (m' : ℝ) ≤ b * (N' : ℝ) + 1) :
    symDecConst k l m m' hk (ENNReal.ofReal (K * (2 : ℝ) ^ ((N' : ℝ) * A)))
      ≤ ENNReal.ofReal (symConstBase k l hk * K
          * (2 : ℝ) ^ ((N' : ℝ) * (b * bilinCoef k l + A))) := by
  have hP : 0 < pkExp k := pkExp_pos hk
  have hPne : pkExp k ≠ 0 := ne_of_gt hP
  have hUc0 : 0 ≤ (uncConst k hk).toReal := ENNReal.toReal_nonneg
  have hbase : 0 ≤ symConstBase k l hk := symConstBase_nonneg k l hk
  have hk2 : 2 ≤ k := by
    have h1 : 1 ≤ k - 1 := le_trans hl hlk
    omega
  have hP2 : 0 ≤ pkExp k - 2 := by
    rw [pkExp]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith
  have hpl1 : 0 ≤ plExp l - 1 := by
    have h : (1 : ℝ) ≤ plExp l := by
      rw [plExp]
      have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    linarith
  have hrs1 : 0 ≤ pkExp k - plExp l - 1 := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    have hlk' : (l : ℝ) ≤ (k : ℝ) - 1 := cast_le_sub_one hk hlk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [h1]; nlinarith
  have hρ0 : 0 ≤ asymRatio k l := by
    rw [asymRatio]
    split
    · positivity
    · have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
      have hlk' : (l : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast le_trans hlk (Nat.sub_le k 1)
      apply div_nonneg _ hl0.le
      linarith
  have hN'0 : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg N'
  have hbN : 0 ≤ b * (N' : ℝ) := mul_nonneg hb hN'0
  have hρbN : 0 ≤ asymRatio k l * b * (N' : ℝ) := mul_nonneg (mul_nonneg hρ0 hb) hN'0
  -- the two level estimates, converted to real inequalities on `m − 2`, `m' − 2`
  have hm2 : (((m - 2 : ℕ) : ℝ)) ≤ asymRatio k l * b * (N' : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    push_cast
    linarith
  have hm'2 : (((m' - 2 : ℕ) : ℝ)) ≤ b * (N' : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
    rw [Nat.cast_sub (by omega : 2 ≤ m')]
    push_cast
    linarith
  -- the exponent bound `E ≤ N'·b·p_k·C`
  have hE : (((m - 2 : ℕ) : ℝ) * (plExp l - 1)
        + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1))
      ≤ (N' : ℝ) * (b * bilinCoef k l) * pkExp k := by
    have h1 : (((m - 2 : ℕ) : ℝ) * (plExp l - 1)
          + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1))
        ≤ (asymRatio k l * b * (N' : ℝ) - 1) * (plExp l - 1)
          + (b * (N' : ℝ) - 1) * (pkExp k - plExp l - 1) := by
      refine add_le_add (mul_le_mul_of_nonneg_right hm2 hpl1)
        (mul_le_mul_of_nonneg_right hm'2 hrs1)
    have h2 : (asymRatio k l * b * (N' : ℝ)) * (plExp l - 1)
          + (b * (N' : ℝ)) * (pkExp k - plExp l - 1)
        = (N' : ℝ) * (b * bilinCoef k l) * pkExp k
          - (N' : ℝ) * b * (asymRatio k l + 1) := by
      rw [bilinCoef]; field_simp; ring
    have h3 : 0 ≤ (N' : ℝ) * b * (asymRatio k l + 1) :=
      mul_nonneg (mul_nonneg hN'0 hb) (by linarith)
    nlinarith [h1, h2, h3, hP2, hpl1, hrs1]
  have hEdiv : (((m - 2 : ℕ) : ℝ) * (plExp l - 1)
        + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k
      ≤ (N' : ℝ) * (b * bilinCoef k l) := by
    rw [div_le_iff₀ hP]
    exact hE
  have hc0 : 0 ≤ K * (2 : ℝ) ^ ((N' : ℝ) * A) :=
    mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
  have hstep := symDecConst_le_ofReal (m := m) (m' := m') (c := K * (2 : ℝ) ^ ((N' : ℝ) * A))
    hk hl hlk hm hm' hc0
  refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2A : 0 ≤ (2 : ℝ) ^ ((N' : ℝ) * A) := Real.rpow_nonneg (by norm_num) _
  have h2E : 0 ≤ (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
      + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k) :=
    Real.rpow_nonneg (by norm_num) _
  have h2NA : (0 : ℝ) < (2 : ℝ) ^ ((N' : ℝ) * A) := Real.rpow_pos_of_pos (by norm_num) _
  have hcomb : (2 : ℝ) ^ ((N' : ℝ) * A)
        * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
            + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)
      ≤ (2 : ℝ) ^ ((N' : ℝ) * (b * bilinCoef k l + A)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have h4 : (N' : ℝ) * (b * bilinCoef k l)
        = (N' : ℝ) * (b * bilinCoef k l + A) - (N' : ℝ) * A := by ring
    linarith [hEdiv, h4]
  calc symConstBase k l hk * (K * (2 : ℝ) ^ ((N' : ℝ) * A))
        * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
            + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)
      = symConstBase k l hk * K
        * ((2 : ℝ) ^ ((N' : ℝ) * A)
          * (2 : ℝ) ^ ((((m - 2 : ℕ) : ℝ) * (plExp l - 1)
              + (((m' - 2 : ℕ) : ℝ)) * (pkExp k - plExp l - 1)) / pkExp k)) := by ring
    _ ≤ symConstBase k l hk * K * (2 : ℝ) ^ ((N' : ℝ) * (b * bilinCoef k l + A)) :=
        mul_le_mul_of_nonneg_left hcomb (mul_nonneg hbase hK)

/-- `bilinCoef` is nonnegative. -/
lemma bilinCoef_nonneg {k l : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k - 1) : 0 ≤ bilinCoef k l := by
  have hP : 0 < pkExp k := pkExp_pos hk
  have hρ : 0 ≤ asymRatio k l := by
    rw [asymRatio]; split
    · positivity
    · apply div_nonneg _ (by positivity)
      have : (l : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast le_trans hlk (Nat.sub_le k 1)
      linarith
  have hpl : 0 ≤ plExp l := plExp_nonneg l
  have hrs : 0 ≤ pkExp k - plExp l := pkExp_sub_plExp_nonneg (by omega)
  rw [bilinCoef]
  positivity

/-- The level `⌊cN⌋` is at most `cN + 1`. -/
lemma lvlOf_le_mul_add_one {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    (lvlOf c N : ℝ) ≤ c * (N : ℝ) + 1 := by
  have h := Nat.floor_le (show (0 : ℝ) ≤ c * (N : ℝ) by positivity)
  simpa only [lvlOf] using le_trans h (by linarith)

set_option maxHeartbeats 16000000 in
/-- **The bilinear inequality at every dyadic scale, uniformly.**  From the asymmetric bilinear
statement at the canonical pair of every level (with constant `K·2^{NA}`) one gets the symmetric
bilinear inequality `BilinDec` at *every* dyadic scale `2^{N'-2}` with the uniform constant
`C₀·2^{N(bC+A)}` for `N' ≤ N`.  The finitely many levels below the threshold of the hypothesis are
covered by the trivial bound `asymDec_crude`. -/
theorem exists_bilinDec_bound {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hρb : asymRatio k l * b ≤ 1)
    {A K : ℝ} (hK : 0 < K) (hA : 0 ≤ A) {N₀ : ℕ}
    (hD : ∀ N, N₀ ≤ N → AsymDec k hk l N (lvlOf (asymRatio k l * b) N) (lvlOf b N)
              (ENNReal.ofReal (K * (2 : ℝ) ^ ((N : ℝ) * A)))) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N' N : ℕ, 2 ≤ N' → N' ≤ N →
      BilinDec k (2 ^ (N' - 2)) (ENNReal.ofReal (C₀
        * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)))) := by
  have hP : 0 < pkExp k := pkExp_pos hk
  have hρpos : 0 < asymRatio k l := asymRatio_pos' hk hlk
  have hρbpos : 0 < asymRatio k l * b := mul_pos hρpos hb
  have hρ0 : 0 ≤ asymRatio k l := hρpos.le
  have hβ0 : 0 ≤ bilinCoef k l := bilinCoef_nonneg hk hlk
  have hbase : 0 ≤ symConstBase k l hk := symConstBase_nonneg k l hk
  -- the threshold
  set N₁ : ℕ := max N₀ (max (⌈2 / b⌉₊ + 1) (⌈2 / (asymRatio k l * b)⌉₊ + 1)) with hN₁
  refine ⟨max 1 (max (symConstBase k l hk * K)
    (symConstBase k l hk * asymCrudeConst k hk N₁)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro N' N hN'2 hN'N
  have hN'1 : 1 ≤ N' := by omega
  have hγ0 : 0 ≤ b * bilinCoef k l + A := by positivity
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hC₀low : 0 ≤ max 1 (max (symConstBase k l hk * K)
      (symConstBase k l hk * asymCrudeConst k hk N₁)) := le_trans zero_le_one (le_max_left _ _)
  have hmono : symConstBase k l hk * K
      ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hmono' : symConstBase k l hk * asymCrudeConst k hk N₁
      ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases hsh : N₁ ≤ N'
  · -- the sharp branch
    have hsh' : max N₀ (max (⌈2 / b⌉₊ + 1) (⌈2 / (asymRatio k l * b)⌉₊ + 1)) ≤ N' := by
      rwa [hN₁] at hsh
    have hN₀N' : N₀ ≤ N' := le_trans (le_max_left _ _) hsh'
    have hthr1 : ⌈2 / b⌉₊ + 1 ≤ N' :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hsh')
    have hthr2 : ⌈2 / (asymRatio k l * b)⌉₊ + 1 ≤ N' :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hsh')
    have hm₁ : 2 ≤ lvlOf (asymRatio k l * b) N' := two_le_lvlOf_of_le hρbpos hthr2
    have hm₂ : 2 ≤ lvlOf b N' := two_le_lvlOf_of_le hb hthr1
    have hm₁N : lvlOf (asymRatio k l * b) N' ≤ N' := lvlOf_le_of_mul_le (by
      calc asymRatio k l * b * (N' : ℝ) ≤ 1 * (N' : ℝ) :=
            mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg N')
        _ = (N' : ℝ) := one_mul _)
    have hm₂N : lvlOf b N' ≤ N' := lvlOf_le_of_mul_le (by
      calc b * (N' : ℝ) ≤ 1 * (N' : ℝ) := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg N')
        _ = (N' : ℝ) := one_mul _)
    have hm₁b : ((lvlOf (asymRatio k l * b) N') : ℝ) ≤ asymRatio k l * b * (N' : ℝ) + 1 :=
      lvlOf_le_mul_add_one (by positivity) N'
    have hm₂b : ((lvlOf b N') : ℝ) ≤ b * (N' : ℝ) + 1 := lvlOf_le_mul_add_one hb.le N'
    have hSym := symDec_of_asymDec (k := k) (l := l) (N := N') (m := lvlOf (asymRatio k l * b) N')
      (m' := lvlOf b N') hk hl hlk hm₁ hm₁N hm₂ hm₂N (hD N' hN₀N')
    have hConst := symDecConst_le_exp (k := k) (l := l) (m := lvlOf (asymRatio k l * b) N')
      (m' := lvlOf b N') (N' := N') hk hl hlk hm₁ hm₂ hb.le hK.le hA hm₁b hm₂b
    have hBD := bilinDec_of_symDec hN'2 (symDec_mono hConst hSym)
    refine BilinDec_mono (ENNReal.ofReal_le_ofReal ?_) hBD
    have hN'Nr : (N' : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN'N
    have h2N : (2 : ℝ) ^ ((N' : ℝ) * (b * bilinCoef k l + A))
        ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hγ0, hN'Nr])
    calc symConstBase k l hk * K * (2 : ℝ) ^ ((N' : ℝ) * (b * bilinCoef k l + A))
        ≤ symConstBase k l hk * K * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
          mul_le_mul_of_nonneg_left h2N (mul_nonneg hbase hK.le)
      _ ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁))
            * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
          mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (by norm_num) _)
  · -- the crude branch
    have hlt : N' ≤ N₁ := le_of_lt (not_le.mp hsh)
    have hBD := bilinDec_crude hk hl hlk hN'2
    refine BilinDec_mono (ENNReal.ofReal_le_ofReal ?_) hBD
    have hmono2 : asymCrudeConst k hk N' ≤ asymCrudeConst k hk N₁ := asymCrudeConst_mono k hk hlt
    have hstep : symConstBase k l hk * asymCrudeConst k hk N'
        ≤ symConstBase k l hk * asymCrudeConst k hk N₁ :=
      mul_le_mul_of_nonneg_left hmono2 hbase
    have h2 : symConstBase k l hk * asymCrudeConst k hk N₁
        ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁)) := hmono'
    calc symConstBase k l hk * asymCrudeConst k hk N'
        ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁)) :=
          le_trans hstep h2
      _ ≤ max 1 (max (symConstBase k l hk * K) (symConstBase k l hk * asymCrudeConst k hk N₁))
            * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) := by
          nth_rewrite 1 [← mul_one (max 1 (max (symConstBase k l hk * K)
            (symConstBase k l hk * asymCrudeConst k hk N₁)))]
          exact mul_le_mul_of_nonneg_left hpow1 hC₀low


/-! ## 5. STEP 4: the linear decoupling exponent `b·C + A` -/

/-- The `ℓ²`-sum over `Icc 2 N` of a constant `ofReal c`, squared. -/
lemma sum_Icc_const_ofReal_sq_le {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (ENNReal.ofReal c) ^ (2 : ℝ))
      ≤ ENNReal.ofReal ((N : ℝ) * c ^ 2) := by
  have hterm : (ENNReal.ofReal c) ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (p := 2) hc (by norm_num), Real.rpow_two]
  rw [hterm, Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast (Finset.Icc 2 N).card,
    ← ENNReal.ofReal_mul (by positivity :
      (0 : ℝ) ≤ (((Finset.Icc 2 N).card : ℕ) : ℝ))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : (Finset.Icc 2 N).card ≤ N := by
    have h1 : (Finset.Icc 2 N).card = N + 1 - 2 := by simp
    omega
  have hcard' : (((Finset.Icc 2 N).card : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcard' (sq_nonneg c)

set_option maxHeartbeats 16000000 in
/-- **STEP 4 = GLYZ (4.4).**  From the asymmetric bilinear statements at the canonical level pair
of every level (with constant `K·2^{NA}`) the linear decoupling exponent is bounded by
`b·C + A` with `C = ((k−l+1)/l)(p_l/p_k) + (p_k−p_l)/p_k`: for every `ε > 0` there is `K' > 0`
with `DecLin k (2^N) (ofReal (K'·2^{N(bC+A+ε)}))` for every `N ≥ 1`. -/
theorem decLin_of_asymExp {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hρb : asymRatio k l * b ≤ 1)
    {A K : ℝ} (hK : 0 < K) (hA : 0 ≤ A) {N₀ : ℕ}
    (hD : ∀ N, N₀ ≤ N → AsymDec k hk l N (lvlOf (asymRatio k l * b) N) (lvlOf b N)
              (ENNReal.ofReal (K * (2 : ℝ) ^ ((N : ℝ) * A))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ N : ℕ, 1 ≤ N →
      DecLin k (2 ^ N) (ENNReal.ofReal (K'
        * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)))) := by
  obtain ⟨C₀, hC₀pos, hbil⟩ := exists_bilinDec_bound hk hl hlk hb hb1 hρb hK hA hD
  have hγ0 : 0 ≤ b * bilinCoef k l + A := by
    have := bilinCoef_nonneg hk hlk
    positivity
  obtain ⟨L, hL⟩ := Commons.Analysis.Asymptotics.linear_le_mul_two_rpow ε hε 0 1 le_rfl one_pos
  have hL' : ∀ m : ℕ, L ≤ m → (m : ℝ) ≤ (2 : ℝ) ^ (ε * (m : ℝ)) := by
    intro m hm
    have := hL m hm
    simpa using this
  obtain ⟨-, K₁, hK₁, hD₁⟩ := one_half_mem_linExpSet k hk
  set D : ℝ := Real.sqrt (6 + 16 * C₀ ^ 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  set N₂ : ℕ := max (L + 2) 2 with hN₂
  have hN₂ge2 : 2 ≤ N₂ := le_max_right _ _
  refine ⟨max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)), lt_max_of_lt_left hDpos, ?_⟩
  intro N hN1
  have hK'D : D ≤ max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)) := le_max_left _ _
  have hK'K : K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)
      ≤ max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)) := le_max_right _ _
  by_cases hN : N₂ ≤ N
  · -- the sharp branch: the bilinear reduction at level `N`
    have hN2 : 2 ≤ N := le_trans hN₂ge2 hN
    have hdec := decLin_of_bilinDec k N hk hN2
      (fun _ : ℕ => ENNReal.ofReal (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))))
      (fun n hn2 hnN => hbil (N - n + 2) N (by omega) (by omega))
    refine DecLin_mono ?_ hdec
    -- bound the sum
    have hc0 : 0 ≤ C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
      mul_nonneg hC₀pos.le (Real.rpow_nonneg (by norm_num) _)
    have hsum := sum_Icc_const_ofReal_sq_le (c := C₀
      * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) hc0 N
    have h16 : (16 : ℝ≥0∞) = ENNReal.ofReal 16 := by norm_num
    have h6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
    have hstep1 : (6 : ℝ≥0∞) + 16 * (∑ n ∈ Finset.Icc 2 N,
          (ENNReal.ofReal (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)))) ^ (2 : ℝ))
        ≤ ENNReal.ofReal (6 + 16 * ((N : ℝ) * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)) := by
      have h16le : (16 : ℝ≥0∞) * (∑ n ∈ Finset.Icc 2 N,
          (ENNReal.ofReal (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (16 * ((N : ℝ) * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)) := by
        refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
        rw [h16, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      calc (6 : ℝ≥0∞) + 16 * (∑ n ∈ Finset.Icc 2 N,
            (ENNReal.ofReal (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal 6 + ENNReal.ofReal (16 * ((N : ℝ)
              * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)) :=
            add_le_add (le_of_eq h6) h16le
        _ = ENNReal.ofReal (6 + 16 * ((N : ℝ)
              * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)) := by
            rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
    have hstep2 : (ENNReal.ofReal (6 + 16 * ((N : ℝ) * (C₀
          * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2))) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (6 + 16 * ((N : ℝ) * (C₀
          * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
          (x := 6 + 16 * ((N : ℝ) * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2))
          (p := 1 / 2) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Real.sqrt_eq_rpow]
    refine ((ENNReal.rpow_le_rpow hstep1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      (le_of_eq hstep2)).trans (ENNReal.ofReal_le_ofReal ?_)
    -- the real inequality
    have hc2 : (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2
        = C₀ ^ 2 * (2 : ℝ) ^ (2 * ((N : ℝ) * (b * bilinCoef k l + A))) := by
      rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hbigg : 6 + 16 * ((N : ℝ) * (C₀ * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)
        ≤ (6 + 16 * C₀ ^ 2) * (N : ℝ)
          * ((2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2 := by
      rw [hc2]
      nlinarith [hN1', hpow1, sq_nonneg C₀, sq_nonneg ((2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)))]
    refine (Real.sqrt_le_sqrt hbigg).trans ?_
    have hs1 : Real.sqrt ((6 + 16 * C₀ ^ 2) * (N : ℝ)
        * ((2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) ^ 2)
        = D * Real.sqrt (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (6 + 16 * C₀ ^ 2) * (N : ℝ)),
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 6 + 16 * C₀ ^ 2),
        Real.sqrt_sq (by positivity : (0 : ℝ)
          ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))),
        ← hDdef]
    rw [hs1]
    have hsqrtN : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [hN1']⟩
    have hLN : L ≤ N := by
      have h1 : L + 2 ≤ N₂ := by rw [hN₂]; exact le_max_left _ _
      omega
    have hNL : (N : ℝ) ≤ (2 : ℝ) ^ (ε * (N : ℝ)) := hL' N (by omega)
    have hε'N : (2 : ℝ) ^ (ε * (N : ℝ)) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))
        = (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    calc D * Real.sqrt (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))
        ≤ D * (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtN hDpos.le)
            (Real.rpow_nonneg (by norm_num) ((N : ℝ) * (b * bilinCoef k l + A)))
      _ ≤ D * ((2 : ℝ) ^ (ε * (N : ℝ)) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) := by
          have h2γ : (0 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A)) :=
            Real.rpow_nonneg (by norm_num) _
          have h := mul_le_mul_of_nonneg_right hNL h2γ
          calc D * (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))
              = D * ((N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) :=
                mul_assoc D (N : ℝ) _
            _ ≤ D * ((2 : ℝ) ^ (ε * (N : ℝ))
                * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A))) :=
                mul_le_mul_of_nonneg_left h hDpos.le
      _ = D * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)) := by rw [hε'N]
      _ ≤ max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2))
            * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)) :=
          mul_le_mul_of_nonneg_right hK'D
            (Real.rpow_nonneg (by norm_num) ((N : ℝ) * (b * bilinCoef k l + A + ε)))
  · -- the crude branch: the a priori bound `1/2 ∈ linExpSet`
    have hNle : N ≤ N₂ := le_of_lt (not_le.mp hN)
    have hbase := hD₁ (2 ^ N) (Nat.one_le_pow N 2 (by norm_num))
    have hbase' : DecLin k (2 ^ N) (ENNReal.ofReal (K₁ * ((2 ^ N : ℕ) : ℝ) ^ ((1 : ℝ) / 2))) := by
      have h := DecLinScale_lam_le (k := k) (M := 2 ^ N) (by positivity : 0 < 2 ^ N)
        (lam := 1) (lam' := 2) (by norm_num) (by norm_num) hbase
      exact (decLinScale_one_iff k (2 ^ N) _).mp h
    refine DecLin_mono (ENNReal.ofReal_le_ofReal ?_) hbase'
    have hcast : (((2 ^ N : ℕ) : ℝ)) = (2 : ℝ) ^ N := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show ((N : ℕ) : ℝ) * (1 / 2) = (N : ℝ) / 2 from by ring]
    have hle2 : (2 : ℝ) ^ ((N : ℝ) / 2) ≤ (2 : ℝ) ^ ((N₂ : ℝ) / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (N : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hNle
      linarith
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    calc K₁ * (2 : ℝ) ^ ((N : ℝ) / 2)
        ≤ K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hle2 hK₁.le
      _ ≤ max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)) := hK'K
      _ ≤ max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2))
            * (2 : ℝ) ^ ((N : ℝ) * (b * bilinCoef k l + A + ε)) := by
          nth_rewrite 1 [← mul_one (max D (K₁ * (2 : ℝ) ^ ((N₂ : ℝ) / 2)))]
          exact mul_le_mul_of_nonneg_left hpow1 (le_trans hDpos.le hK'D)

/-! ## 6. The conclusion: `η ≤ b·C + A_l(b)` -/

/-- **STEP 4, final form.**  For every element `A` of the exponent set of the asymmetric bilinear
decoupling at level ratios `(ρb, b)`, the linear decoupling exponent `η` is at most
`b·C + A`. -/
theorem etaLin_le_bilinCoef_add {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hρb : asymRatio k l * b ≤ 1)
    {A : ℝ} (hA : A ∈ AsymExpSet k hk l b) :
    etaLin k ≤ b * bilinCoef k l + A := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨hA0, K, hK, N₀, hD⟩ := hA
  obtain ⟨K', hK', hD'⟩ := decLin_of_asymExp hk hl hlk hb hb1 hρb hK hA0 hD hε
  have hγ0 : 0 ≤ b * bilinCoef k l + A + ε := by
    have := bilinCoef_nonneg hk hlk
    positivity
  have hcast : ∀ N : ℕ, (((2 ^ N : ℕ) : ℝ)) = (2 : ℝ) ^ ((N : ℝ)) := by
    intro N; rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hD'' : ∀ N : ℕ, 1 ≤ N → DecLin k (2 ^ N)
      (ENNReal.ofReal (K' * (((2 ^ N : ℕ) : ℝ)) ^ (b * bilinCoef k l + A + ε))) := by
    intro N hN
    refine DecLin_mono (ENNReal.ofReal_le_ofReal ?_) (hD' N hN)
    rw [hcast N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hmem : b * bilinCoef k l + A + ε ∈ linExpSet k :=
    mem_linExpSet_of_decLin_dyadic hk hK' hγ0 hD''
  have h1 := etaLin_le_of_mem hmem
  linarith

/-- **GLYZ (4.4) in its final form**: `η ≤ C·b + A_l(b)` with
`C = ((k−l+1)/l)(p_l/p_k) + (p_k−p_l)/p_k`. -/
theorem etaLin_le_bilinCoef_Aexp {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hρb : asymRatio k l * b ≤ 1) :
    etaLin k ≤ b * bilinCoef k l + Aexp k hk l b := by
  set γ : ℝ := b * bilinCoef k l with hγdef
  by_contra hcon
  push_neg at hcon
  have hcon' : γ + sInf (AsymExpSet k hk l b) < etaLin k := by
    rw [hγdef]; exact hcon
  have hδ : 0 < etaLin k - (γ + sInf (AsymExpSet k hk l b)) := by linarith
  have hlt : sInf (AsymExpSet k hk l b)
      < sInf (AsymExpSet k hk l b) + (etaLin k - (γ + sInf (AsymExpSet k hk l b))) := by
    linarith
  obtain ⟨A, hA, hAlt⟩ := (csInf_lt_iff (bddBelow_asymExpSet k hk l b)
    (asymExpSet_nonempty k hk hlk hb hb1 hρb)).mp hlt
  have h := etaLin_le_bilinCoef_add hk hl hlk hb hb1 hρb hA
  rw [← hγdef] at h
  linarith
