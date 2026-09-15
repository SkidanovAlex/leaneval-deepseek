/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.UniformChain
import Submission.Vinogradov.AsymExpZero
import Submission.Vinogradov.LvlFloor
import Submission.Vinogradov.AsymJump
import Submission.Commons.Analysis.Real.rpow_le_max_one

/-!
# GLYZ §4: the recursion of the exponent bootstrap

The recursion (4.4) of Guo–Li–Yung–Zorin-Kranich, *A short proof of `l²` decoupling for the
moment curve* (arXiv:1912.09798), expressed as a membership in the exponent set `AsymExpSet`.

For `k ≥ 2`, `1 ≤ l ≤ k−1`, a small `b > 0` and a level `N`, write
`ρ := asymRatio k l = (k−l+1)/l`, `m₁ := ⌊ρbN⌋`, `m₂ := ⌊bN⌋` and `θ := 1/(k−l+1)`.  The two
factors of the Hölder step (`HolderReduction.asymDec_of_holder`) are the asymmetric bilinear
statements at splits `k−l` (pair `(m₂,m₁)`) and `l−1` (pair `(m₁,m₂)`).  The paper supplies them
by GLYZ Lemma 3.9 from the elements `A_{k−l}(ρb)` and `A_{l−1}(b)` of the exponent set, which are
statements at the *refined* first levels `refLvl`, and by the `l = 0` brick at split `0`.

* `asymExpSet_recursion_one` handles the split `l = 1`: the second factor is the split-`0`
  statement, which is supplied directly as an `AsymExpSet k hk 0 b` element
  (`AsymExpZero.mem_asymExpSet_zero_of_linExpSet` produces such elements from the linear-decoupling
  exponent `e ∈ linExpSet k`, and no model hypothesis is consumed).
* `asymExpSet_recursion` handles the splits `l ≥ 2`, where both factors come from a model
  hypothesis (`UniformChain.asymDec_of_model_uniform` at the *fixed* enlargement
  `laneEnl k L hk hl hlk`).

The assembly of each factor is:

1. `AsymJump.asymDec_coarsen` (with `D := k+1`) moves the first slot of the factor's canonical
   statement down from `lvlOf (asymRatio k L · y) N` to the refined level `refLvl L k m'`; the
   two comparisons are `LvlFloor.floor_refLvl_le_lvlOf` and `LvlFloor.floor_lvlOf_le_refLvl_add`.
2. `UniformChain.asymDec_of_model_uniform` moves it further down to the required slot, at the price
   of `(C_model · (2^{refLvl − m})^{2εm})^{p_L/p_k}`.
3. The slack conditions `m₂ ≤ refLvl (k−l) k m₁` and `m₁ ≤ refLvl (l−1) k m₂` hold for large `N`
   by `LvlFloor.exists_lvlOf_le_refLvl` together with
   `LvlFloor.one_lt_asymRatio_mul_ratio` / `LvlFloor.asymRatio_lt_ratio`.
4. `HolderReduction.asymDec_of_holder` combines the two factors.

The constant bookkeeping (`factor_const_eq`, `factor_const_le`) collects the coarsening, model and
lane constants into a single `ofReal`, and shows that the lane loss
`(2^{refLvl − m})^{2εm·p_L/p_k}` contributes only the exponent slack
`recC k l · εm · b = 2·max(gRatio₁,gRatio₂)·εm·b`, because
`refLvl L k m' − m ≤ gRatio·b·N + O(1)`.  All floor discrepancies are `O(1/N)` in the exponent
and are absorbed by the constant `K`.

The module is imported by `ROADMAP.lean` only; it is not on the comparator chain.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Submission.Vinogradov


open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. The constants of the §4 recursion -/

/-- The upper bound on the coarse ratio `b` for which the §4 recursion is applied. -/
noncomputable def b₀ (k : ℕ) : ℝ := 1 / (4 * ((k : ℝ) + 1))

lemma b₀_pos (k : ℕ) : 0 < b₀ k := by rw [b₀]; positivity

lemma b₀_le_one (k : ℕ) : b₀ k ≤ 1 := by
  rw [b₀, div_le_one (by positivity)]
  have h : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  linarith

/-- The first-factor slack ratio `((k−(k−l)+1)/(k−l))·asymRatio k l`. -/
noncomputable def gRatio₁ (k l : ℕ) : ℝ :=
  (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * asymRatio k l

/-- The second-factor slack ratio `(k−(l−1)+1)/(l−1)`. -/
noncomputable def gRatio₂ (k l : ℕ) : ℝ :=
  ((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)

/-- The exponent slack of the §4 recursion. -/
noncomputable def recC (k l : ℕ) : ℝ := 2 * max (gRatio₁ k l) (gRatio₂ k l)

lemma one_lt_gRatio₁ {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) : 1 < gRatio₁ k l :=
  one_lt_asymRatio_mul_ratio hl hlk

lemma asymRatio_lt_gRatio₂ {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k - 1) :
    asymRatio k l < gRatio₂ k l := by
  have h := asymRatio_lt_ratio hl hlk
  simpa only [gRatio₂, mul_one] using h

lemma gRatio₁_pos {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) : 0 < gRatio₁ k l :=
  lt_trans one_pos (one_lt_gRatio₁ hl hlk)

lemma gRatio₁_le {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) : gRatio₁ k l ≤ 4 := by
  have hkl : 1 ≤ k - l := by omega
  have hlt : l ≤ k := by omega
  have h1 : ((k - l : ℕ) : ℝ) = (k:ℝ) - (l:ℝ) := Nat.cast_sub hlt
  have h2 : k - (k - l) + 1 = l + 1 := by omega
  have h2' : ((k - (k - l) + 1 : ℕ) : ℝ) = (l:ℝ) + 1 := by rw [h2]; push_cast; ring
  have hb : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have ha : (1:ℝ) ≤ (k:ℝ) - (l:ℝ) := by
    have : (1:ℝ) ≤ ((k - l : ℕ) : ℝ) := by exact_mod_cast hkl
    linarith
  rw [gRatio₁, h2', asymRatio_of_pos hl]
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
  nlinarith [ha, hb, mul_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) - 1) (by linarith : (0:ℝ) ≤ (k:ℝ) - (l:ℝ) - 1)]

lemma gRatio₂_pos {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k - 1) : 0 < gRatio₂ k l :=
  lt_trans (asymRatio_pos' (by omega) hlk) (asymRatio_lt_gRatio₂ hl hlk)

lemma gRatio₂_le {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k - 1) : gRatio₂ k l ≤ (k : ℝ) := by
  have hlt : l ≤ k := by omega
  have h1 : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ l)]; norm_num
  have h2 : k - (l - 1) + 1 = k - l + 2 := by omega
  have h2' : ((k - (l - 1) + 1 : ℕ) : ℝ) = (k:ℝ) - (l:ℝ) + 2 := by
    rw [h2, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hlt]
  have hb : (1:ℝ) ≤ (l:ℝ) - 1 := by
    have : (2:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    linarith
  rw [gRatio₂, h2', h1, div_le_iff₀ (by linarith)]
  nlinarith [Nat.cast_nonneg (α := ℝ) k, hb, hlt]

lemma asymRatio_mul_b_le_one {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) {b : ℝ}
    (hb : 0 ≤ b) (hb₁ : b ≤ b₀ k) : asymRatio k l * b ≤ 1 := by
  have hle : asymRatio k l ≤ (k:ℝ) := asymRatio_le hk hl hlk
  have hb1 : b ≤ 1 / (4 * ((k:ℝ)+1)) := hb₁
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  calc asymRatio k l * b ≤ (k:ℝ) * (1/(4*((k:ℝ)+1))) := mul_le_mul hle hb1 hb (by positivity)
    _ = (k:ℝ)/(4*((k:ℝ)+1)) := by ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith

lemma gRatio₁_mul_b_le_one {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) {b : ℝ}
    (hb : 0 ≤ b) (hb₁ : b ≤ b₀ k) : gRatio₁ k l * b ≤ 1 := by
  have hle : gRatio₁ k l ≤ 4 := gRatio₁_le hl hlk
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  calc gRatio₁ k l * b ≤ 4 * (1/(4*((k:ℝ)+1))) := mul_le_mul hle hb₁ hb (by norm_num)
    _ = 1/((k:ℝ)+1) := by
        have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
        field_simp
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith

lemma gRatio₂_mul_b_le_one {k l : ℕ} (hk : 1 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k - 1) {b : ℝ}
    (hb : 0 ≤ b) (hb₁ : b ≤ b₀ k) : gRatio₂ k l * b ≤ 1 := by
  have hle : gRatio₂ k l ≤ (k:ℝ) := gRatio₂_le hl hlk
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  calc gRatio₂ k l * b ≤ (k:ℝ) * (1/(4*((k:ℝ)+1))) := mul_le_mul hle hb₁ hb (by positivity)
    _ = (k:ℝ)/(4*((k:ℝ)+1)) := by ring
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith



/-! ## 2. The level thresholds of the recursion -/

lemma eventually_two_le_lvlOf {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ lvlOf c N := by
  refine Filter.eventually_atTop.mpr ⟨⌈2 / c⌉₊, fun N hN => ?_⟩
  have h1 : 2 / c ≤ ((⌈2 / c⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈2 / c⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h3 : 2 ≤ c * (N : ℝ) := by
    have h4 : (2 / c) * c ≤ (N : ℝ) * c := mul_le_mul_of_nonneg_right (le_trans h1 h2) hc.le
    rw [div_mul_cancel₀ _ (ne_of_gt hc)] at h4
    linarith
  exact Nat.le_floor (by exact_mod_cast h3)

lemma eventually_one_le_lvlOf {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lvlOf c N :=
  (eventually_two_le_lvlOf hc).mono fun N h => le_trans (by norm_num) h

/-- **The level gap of the first factor.** -/
lemma eventually_gap₁ {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop,
      4 ≤ 2 ^ (refLvl (k - l) k (lvlOf (asymRatio k l * b) N) - lvlOf b N) := by
  have hP1 : 1 ≤ k - l := by omega
  set c : ℝ := (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) with hc
  have hAeq : gRatio₁ k l = c * asymRatio k l := rfl
  have hδ : 0 < gRatio₁ k l - 1 := by linarith [one_lt_asymRatio_mul_ratio hl hlk]
  have hδb : 0 < (gRatio₁ k l - 1) * b := mul_pos hδ hb
  set E : ℝ := c + 1 with hE
  refine Filter.eventually_atTop.mpr ⟨⌈(E + 2) / ((gRatio₁ k l - 1) * b)⌉₊, fun N hN => ?_⟩
  have h1 : (E + 2) / ((gRatio₁ k l - 1) * b)
      ≤ ((⌈(E + 2) / ((gRatio₁ k l - 1) * b)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(E + 2) / ((gRatio₁ k l - 1) * b)⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hkey0 : E + 2 ≤ (gRatio₁ k l - 1) * (b * (N : ℝ)) := by
    have h3 : (E + 2) / ((gRatio₁ k l - 1) * b) * ((gRatio₁ k l - 1) * b)
        ≤ (N : ℝ) * ((gRatio₁ k l - 1) * b) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) hδb.le
    rw [div_mul_cancel₀ _ (ne_of_gt hδb)] at h3
    nlinarith [h3]
  have hkey : E + 2 ≤ gRatio₁ k l * (b * (N : ℝ)) - b * (N : ℝ) := by nlinarith [hkey0]
  have hm₁ : asymRatio k l * b * (N : ℝ) - 1 < ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (asymRatio k l * b * (N:ℝ))
    simp only [lvlOf]
    linarith
  have hm₂ : ((lvlOf b N : ℕ) : ℝ) ≤ b * (N : ℝ) :=
    Nat.floor_le (mul_nonneg hb.le (Nat.cast_nonneg N))
  have hM := cast_refLvl_ge (k := k) (L := k - l) hP1 (lvlOf (asymRatio k l * b) N)
  have hdiff : (lvlOf b N : ℝ) + 2
      ≤ ((refLvl (k - l) k (lvlOf (asymRatio k l * b) N) : ℕ) : ℝ) := by
    have hc0 : 0 < c := by rw [hc]; positivity
    have hstep : c * (asymRatio k l * b * (N:ℝ)) - E = gRatio₁ k l * (b * (N:ℝ)) - E := by
      rw [hAeq, hE]; ring
    have hstep2 : gRatio₁ k l * (b * (N:ℝ)) - E ≥ b * (N:ℝ) + 2 := by linarith [hkey]
    have hchain : c * ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) - 1
        > gRatio₁ k l * (b * (N:ℝ)) - E := by
      nlinarith [hm₁, hc0, hstep, hE]
    linarith [hM, hm₂, hstep2, hchain]
  have hnat : lvlOf b N + 2 ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N) := by
    exact_mod_cast hdiff
  have h2le : 2 ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N) - lvlOf b N := by omega
  have h4 : (2:ℕ) ^ 2 ≤ 2 ^ (refLvl (k - l) k (lvlOf (asymRatio k l * b) N) - lvlOf b N) :=
    Nat.pow_le_pow_right (by norm_num) h2le
  norm_num at h4
  exact h4

/-- **The level gap of the second factor.** -/
lemma eventually_gap₂ {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k - 1) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop,
      4 ≤ 2 ^ (refLvl (l - 1) k (lvlOf b N) - lvlOf (asymRatio k l * b) N) := by
  have hQ1 : 1 ≤ l - 1 := by omega
  set c : ℝ := (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) with hc
  have hAeq : gRatio₂ k l = c := rfl
  have hδ : 0 < gRatio₂ k l - asymRatio k l := by
    linarith [asymRatio_lt_ratio hl hlk]
  have hδb : 0 < (gRatio₂ k l - asymRatio k l) * b := mul_pos hδ hb
  set E : ℝ := c + 1 with hE
  refine Filter.eventually_atTop.mpr ⟨⌈(E + 2) / ((gRatio₂ k l - asymRatio k l) * b)⌉₊,
    fun N hN => ?_⟩
  have h1 : (E + 2) / ((gRatio₂ k l - asymRatio k l) * b)
      ≤ ((⌈(E + 2) / ((gRatio₂ k l - asymRatio k l) * b)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(E + 2) / ((gRatio₂ k l - asymRatio k l) * b)⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hkey0 : E + 2 ≤ (gRatio₂ k l - asymRatio k l) * (b * (N : ℝ)) := by
    have h3 : (E + 2) / ((gRatio₂ k l - asymRatio k l) * b) * ((gRatio₂ k l - asymRatio k l) * b)
        ≤ (N : ℝ) * ((gRatio₂ k l - asymRatio k l) * b) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) hδb.le
    rw [div_mul_cancel₀ _ (ne_of_gt hδb)] at h3
    nlinarith [h3]
  have hm₂ : b * (N : ℝ) - 1 < ((lvlOf b N : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (b * (N:ℝ))
    simp only [lvlOf]
    linarith
  have hm₁ : ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) ≤ asymRatio k l * b * (N : ℝ) :=
    Nat.floor_le (mul_nonneg (mul_nonneg (asymRatio_pos' (by omega) hlk).le hb.le) (Nat.cast_nonneg N))
  have hM := cast_refLvl_ge (k := k) (L := l - 1) hQ1 (lvlOf b N)
  have hdiff : (lvlOf (asymRatio k l * b) N : ℝ) + 2
      ≤ ((refLvl (l - 1) k (lvlOf b N) : ℕ) : ℝ) := by
    have hc0 : 0 < c := by rw [hc]; positivity
    have hstep : c * (b * (N:ℝ)) - E = gRatio₂ k l * (b * (N:ℝ)) - E := by
      rw [hAeq]
    have hchain : c * ((lvlOf b N : ℕ) : ℝ) - 1
        > (gRatio₂ k l - asymRatio k l) * (b * (N:ℝ)) + asymRatio k l * (b * (N:ℝ)) - E := by
      nlinarith [hm₂, hc0, hstep, hE]
    have hsplit : (gRatio₂ k l - asymRatio k l) * (b * (N:ℝ)) + asymRatio k l * (b * (N:ℝ))
        = gRatio₂ k l * (b * (N:ℝ)) := by ring
    rw [hsplit] at hchain
    have hstep2 : gRatio₂ k l * (b * (N:ℝ)) - E ≥ asymRatio k l * (b * (N:ℝ)) + 2 := by
      linarith [hkey0]
    linarith [hM, hm₁, hstep2, hchain]
  have hnat : lvlOf (asymRatio k l * b) N + 2 ≤ refLvl (l - 1) k (lvlOf b N) := by
    exact_mod_cast hdiff
  have h2le : 2 ≤ refLvl (l - 1) k (lvlOf b N) - lvlOf (asymRatio k l * b) N := by omega
  have h4 : (2:ℕ) ^ 2 ≤ 2 ^ (refLvl (l - 1) k (lvlOf b N) - lvlOf (asymRatio k l * b) N) :=
    Nat.pow_le_pow_right (by norm_num) h2le
  norm_num at h4
  exact h4

/-! ## 3. The constant bookkeeping of the recursion -/

/-- One factor of the recursion in `ofReal` form. -/
lemma factor_const_eq {K A : ℝ} (hK : 0 ≤ K) {Kc Cm : ℝ≥0∞} (hKctop : Kc ≠ ⊤)
    (hCmtop : Cm ≠ ⊤) {q r s : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) {g : ℕ} :
    (ENNReal.ofReal (K * (2:ℝ) ^ A) * Kc ^ q)
        * (Cm * ((((2 ^ g : ℕ)) : ℝ≥0∞)) ^ s) ^ r
      = ENNReal.ofReal (K * (2:ℝ) ^ A * (Kc.toReal ^ q * Cm.toReal ^ r)
          * (2:ℝ) ^ ((g:ℝ) * (s * r))) := by
  have hc1 : Kc ^ q = ENNReal.ofReal (Kc.toReal ^ q) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hKctop]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq]
  have hc2 : Cm ^ r = ENNReal.ofReal (Cm.toReal ^ r) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hCmtop]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr]
  have hc4 : (((((2 ^ g : ℕ)) : ℝ≥0∞)) ^ s) ^ r
      = ENNReal.ofReal ((2:ℝ) ^ ((g:ℝ) * (s * r))) := by
    rw [← ENNReal.ofReal_natCast (2 ^ g), ENNReal.ofReal_rpow_of_nonneg (by positivity) hs,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hr]
    congr 1
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2:ℝ) g,
        ← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hc1, ENNReal.mul_rpow_of_nonneg _ _ hr, hc2, hc4,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The exponent of one factor after raising to a power `θ ∈ [0,1]`. -/
lemma factor_const_le {K A : ℝ} (hK : 0 ≤ K) {Kc Cm : ℝ≥0∞} (hKctop : Kc ≠ ⊤)
    (hCmtop : Cm ≠ ⊤) {q r s θ : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {g : ℕ} :
    ((ENNReal.ofReal (K * (2:ℝ) ^ A) * Kc ^ q)
        * (Cm * ((((2 ^ g : ℕ)) : ℝ≥0∞)) ^ s) ^ r) ^ θ
      ≤ ENNReal.ofReal (K ^ θ * max 1 (Kc.toReal ^ q * Cm.toReal ^ r)
          * (2:ℝ) ^ (θ * (A + (g:ℝ) * (s * r)))) := by
  set D : ℝ := Kc.toReal ^ q * Cm.toReal ^ r with hD
  set X : ℝ := K * (2:ℝ) ^ A * D * (2:ℝ) ^ ((g:ℝ) * (s * r)) with hX
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  have hLHS : (ENNReal.ofReal (K * (2:ℝ) ^ A) * Kc ^ q)
      * (Cm * ((((2 ^ g : ℕ)) : ℝ≥0∞)) ^ s) ^ r = ENNReal.ofReal X :=
    factor_const_eq hK hKctop hCmtop hq hr hs
  rw [hLHS, ENNReal.ofReal_rpow_of_nonneg (x := X) hX0 hθ0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hX]
  have h1 : (K * (2:ℝ) ^ A * D * (2:ℝ) ^ ((g:ℝ) * (s * r))) ^ θ
      = K ^ θ * ((2:ℝ) ^ A) ^ θ * D ^ θ * ((2:ℝ) ^ ((g:ℝ) * (s * r))) ^ θ := by
    rw [show K * (2:ℝ) ^ A * D * (2:ℝ) ^ ((g:ℝ) * (s * r))
        = (K * (2:ℝ) ^ A * D) * (2:ℝ) ^ ((g:ℝ) * (s * r)) from by ring]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hD0,
        Real.mul_rpow hK (by positivity)]
  have h2 : ((2:ℝ) ^ A) ^ θ = (2:ℝ) ^ (A * θ) :=
    (Real.rpow_mul (x := 2) (by norm_num) A θ).symm
  have h3 : ((2:ℝ) ^ ((g:ℝ) * (s * r))) ^ θ = (2:ℝ) ^ ((g:ℝ) * (s * r) * θ) :=
    (Real.rpow_mul (x := 2) (by norm_num) _ θ).symm
  have h4 : D ^ θ ≤ max 1 D := Commons.Analysis.Real.rpow_le_max_one hθ0 hθ1 hD0
  rw [h1, h2, h3]
  calc K ^ θ * (2:ℝ) ^ (A * θ) * D ^ θ * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)
      ≤ K ^ θ * (2:ℝ) ^ (A * θ) * max 1 D * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ) := by
        have hKθ0 : 0 ≤ K ^ θ := Real.rpow_nonneg hK θ
        have hAθ0 : 0 ≤ (2:ℝ) ^ (A * θ) := by positivity
        have hXθ0 : 0 ≤ (2:ℝ) ^ ((g:ℝ) * (s * r) * θ) := by positivity
        have hmul : D ^ θ * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)
            ≤ max 1 D * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ) :=
          mul_le_mul_of_nonneg_right h4 hXθ0
        have hKX0 : 0 ≤ K ^ θ * (2:ℝ) ^ (A * θ) := mul_nonneg hKθ0 hAθ0
        calc K ^ θ * (2:ℝ) ^ (A * θ) * D ^ θ * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)
            = (K ^ θ * (2:ℝ) ^ (A * θ))
                * (D ^ θ * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)) := by ring
          _ ≤ (K ^ θ * (2:ℝ) ^ (A * θ))
                * (max 1 D * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)) :=
              mul_le_mul_of_nonneg_left hmul hKX0
          _ = K ^ θ * (2:ℝ) ^ (A * θ) * max 1 D * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ) := by ring
    _ = K ^ θ * max 1 D * ((2:ℝ) ^ (A * θ) * (2:ℝ) ^ ((g:ℝ) * (s * r) * θ)) := by ring
    _ = K ^ θ * max 1 D * (2:ℝ) ^ (A * θ + (g:ℝ) * (s * r) * θ) := by
        rw [Real.rpow_add (x := 2) (by norm_num)]
    _ = K ^ θ * max 1 D * (2:ℝ) ^ (θ * (A + (g:ℝ) * (s * r))) := by
        congr 2
        ring

/-! ## 4. The recursion -/

theorem asymExpSet_recursion {k l : ℕ} (hk : 1 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k - 1)
    {εm : ℝ} (hεm : 0 < εm)
    (hmMod₁ : ∀ (εm' : ℝ), 0 < εm' → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (k - l) M
        (laneEnl k (k - l) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm')))
    (hmMod₂ : ∀ (εm' : ℝ), 0 < εm' → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (l - 1) M
        (laneEnl k (l - 1) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm')))
    {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ b₀ k)
    {A₁ A₂ : ℝ} (hA₁ : A₁ ∈ AsymExpSet k hk (k - l) (asymRatio k l * b))
    (hA₂ : A₂ ∈ AsymExpSet k hk (l - 1) b) :
    (1 / ((k:ℝ) - (l:ℝ) + 1)) * A₁ + (((k:ℝ) - (l:ℝ)) / ((k:ℝ) - (l:ℝ) + 1)) * A₂
      + recC k l * εm * b ∈ AsymExpSet k hk l b := by
  obtain ⟨hA₁0, K₁, hK₁0, N₁, hN₁⟩ := hA₁
  obtain ⟨hA₂0, K₂, hK₂0, N₂, hN₂⟩ := hA₂
  have hP1 : 1 ≤ k - l := by omega
  have hPk : k - l ≤ k := by omega
  have hPk1 : k - l ≤ k - 1 := by omega
  have hQ1 : 1 ≤ l - 1 := by omega
  have hQk : l - 1 ≤ k := by omega
  have hQk1 : l - 1 ≤ k - 1 := by omega
  have hl1 : 1 ≤ l := by omega
  have hlk' : l ≤ k := by omega
  have hklR : (l:ℝ) ≤ (k:ℝ) := by exact_mod_cast hlk'
  have hden : 0 < (k:ℝ) - (l:ℝ) + 1 := by linarith
  obtain ⟨Kc₁, -, hKc₁top, hcoarsen₁⟩ := asymDec_coarsen hk (hl := hP1) (D := k + 1)
  obtain ⟨Kc₂, -, hKc₂top, hcoarsen₂⟩ := asymDec_coarsen hk (hl := hQ1) (D := k + 1)
  obtain ⟨a₀₁, ha₀₁, hmM₁⟩ := hmMod₁ εm hεm
  obtain ⟨a₀₂, ha₀₂, hmM₂⟩ := hmMod₂ εm hεm
  obtain ⟨Cm₁, hCm₁top, hmodel₁⟩ :=
    asymDec_of_model_uniform hk (hl := hP1) (hlk := hPk) (hlk1 := hPk1) ha₀₁ hεm hmM₁
  obtain ⟨Cm₂, hCm₂top, hmodel₂⟩ :=
    asymDec_of_model_uniform hk (hl := hQ1) (hlk := hQk) (hlk1 := hQk1) ha₀₂ hεm hmM₂
  -- the exponent parameters
  have hpk : (0:ℝ) < pkExp k := pkExp_pos hk
  have hpk0 : 0 ≤ pkExp k := hpk.le
  set θ : ℝ := 1 / ((k:ℝ) - (l:ℝ) + 1) with hθ
  set s : ℝ := 2 * εm with hs
  set q : ℝ := 1 / pkExp k with hq
  set r₁ : ℝ := plExp (k - l) / pkExp k with hr₁
  set r₂ : ℝ := plExp (l - 1) / pkExp k with hr₂
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg zero_le_one hpk0
  have hr₁0 : 0 ≤ r₁ := by rw [hr₁]; exact div_nonneg (plExp_nonneg _) hpk0
  have hr₂0 : 0 ≤ r₂ := by rw [hr₂]; exact div_nonneg (plExp_nonneg _) hpk0
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg zero_le_one hden.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hden]
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have h1θ0 : 0 ≤ 1 - θ := by linarith
  have h1θ1 : 1 - θ ≤ 1 := by linarith
  have hr₁1 : r₁ ≤ 1 := by
    rw [hr₁, div_le_one hpk, plExp, pkExp]
    have h1 : ((k - l : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast (Nat.sub_le k l)
    have h2 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    nlinarith [h1, h2]
  have hr₂1 : r₂ ≤ 1 := by
    rw [hr₂, div_le_one hpk, plExp, pkExp]
    have h1 : ((l - 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : l - 1 ≤ k)
    have h2 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    nlinarith [h1, h2]
  -- the constants
  set D₁ : ℝ := Kc₁.toReal ^ q * Cm₁.toReal ^ r₁ with hD₁
  set D₂ : ℝ := Kc₂.toReal ^ q * Cm₂.toReal ^ r₂ with hD₂
  set M₁ : ℝ := max 1 D₁ with hM₁
  set M₂ : ℝ := max 1 D₂ with hM₂
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM₂pos : 0 < M₂ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set Kfin : ℝ := (K₁ ^ θ * M₁) * (K₂ ^ (1 - θ) * M₂) with hKfin
  have hKfinpos : 0 < Kfin := by
    rw [hKfin]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hK₁0 θ) hM₁pos)
      (mul_pos (Real.rpow_pos_of_pos hK₂0 (1 - θ)) hM₂pos)
  -- the exponent
  have hAeq : θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b
      = (1 / ((k:ℝ) - (l:ℝ) + 1)) * A₁ + (((k:ℝ) - (l:ℝ)) / ((k:ℝ) - (l:ℝ) + 1)) * A₂
          + recC k l * εm * b := by
    rw [hθ]
    field_simp
    ring
  -- the level slack conditions
  have hslack₁ : b < (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * (asymRatio k l * b) := by
    have h1 := one_lt_gRatio₁ hl1 hlk
    rw [gRatio₁] at h1
    calc b = 1 * b := (one_mul b).symm
      _ < (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * asymRatio k l * b :=
          mul_lt_mul_of_pos_right h1 hb
      _ = (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * (asymRatio k l * b) := by ring
  have hslack₂ : asymRatio k l
      < (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * 1 := by
    have h1 := asymRatio_lt_ratio hl hlk
    simpa only [gRatio₂, mul_one] using h1
  obtain ⟨Nsl₁, hsl₁⟩ := exists_lvlOf_le_refLvl (k := k) (L := k - l) hk hP1 hPk (y := 1)
      (hy := one_pos) (hc0 := mul_pos (asymRatio_pos' hk hlk) hb) (hc2 := hb) hslack₁
  obtain ⟨Nsl₂, hsl₂⟩ := exists_lvlOf_le_refLvl (k := k) (L := l - 1) hk hQ1 hQk (y := b)
      (hy := hb) (hc0 := one_pos) (hc2 := asymRatio_pos' hk hlk) hslack₂
  have hev₁ : ∀ᶠ N : ℕ in atTop,
      lvlOf b N ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N) :=
    Filter.eventually_atTop.mpr ⟨Nsl₁, fun N hN => by
      simpa only [mul_one] using hsl₁ N hN⟩
  have hev₂ : ∀ᶠ N : ℕ in atTop,
      lvlOf (asymRatio k l * b) N ≤ refLvl (l - 1) k (lvlOf b N) :=
    Filter.eventually_atTop.mpr ⟨Nsl₂, fun N hN => by
      simpa only [one_mul] using hsl₂ N hN⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ lvlOf (asymRatio k l * b) N) ∧ (2 ≤ lvlOf b N) ∧
      (lvlOf b N ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N)) ∧
      (lvlOf (asymRatio k l * b) N ≤ refLvl (l - 1) k (lvlOf b N)) ∧
      (4 ≤ 2 ^ (refLvl (k - l) k (lvlOf (asymRatio k l * b) N) - lvlOf b N)) ∧
      (4 ≤ 2 ^ (refLvl (l - 1) k (lvlOf b N) - lvlOf (asymRatio k l * b) N)) := by
    filter_upwards [eventually_two_le_lvlOf (mul_pos (asymRatio_pos' hk hlk) hb),
      eventually_two_le_lvlOf hb, hev₁, hev₂,
      eventually_gap₁ hl1 hlk hb, eventually_gap₂ hl hlk hb] with N h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hrecC : recC k l = 2 * max (gRatio₁ k l) (gRatio₂ k l) := rfl
  have hrecC0 : 0 ≤ recC k l := by
    rw [hrecC]
    have h := le_trans (le_of_lt (gRatio₁_pos hl1 hlk))
      (le_max_left (gRatio₁ k l) (gRatio₂ k l))
    linarith
  have hA0 : 0 ≤ θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b := by
    have h1 : 0 ≤ θ * A₁ := mul_nonneg hθ0 hA₁0
    have h2 : 0 ≤ (1 - θ) * A₂ := mul_nonneg h1θ0 hA₂0
    have h3 : 0 ≤ recC k l * εm * b := mul_nonneg (mul_nonneg hrecC0 hεm.le) hb.le
    linarith
  rw [← hAeq]
  refine ⟨hA0, Kfin, hKfinpos, max (max N₁ N₂) N₀, fun N hNN => ?_⟩
  have hN₀' : N₀ ≤ N := le_trans (le_max_right _ _) hNN
  obtain ⟨h2m₁, h2m₂, hm₂rl₁, hm₁rl₂, h4₁, h4₂⟩ := hN₀ N hN₀'
  have N1' : N₁ ≤ N := le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ _) hNN)
  have N2' : N₂ ≤ N := le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ _) hNN)
  have hbig₁ := hN₁ N N1'
  have hbig₂ := hN₂ N N2'
  -- the (N-independent) level bounds
  have hy₁ : 0 ≤ asymRatio k l * b := (mul_pos (asymRatio_pos' hk hlk) hb).le
  have hρb1 : asymRatio k l * b ≤ 1 := asymRatio_mul_b_le_one hk hl1 hlk' hb.le hb₁
  have hb1 : b ≤ 1 := le_trans hb₁ (b₀_le_one k)
  have hasym₁ : asymRatio k (k - l) = ((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hP1, Nat.cast_add, Nat.cast_one, Nat.cast_sub hPk]
  have hasym₂ : asymRatio k (l - 1) = ((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hQ1, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : l - 1 ≤ k)]
  have hA₁b : asymRatio k (k - l) * (asymRatio k l * b) ≤ 1 := by
    have h := gRatio₁_mul_b_le_one hl1 hlk hb.le hb₁
    rw [gRatio₁, ← hasym₁, mul_assoc] at h
    exact h
  have hA₂b : asymRatio k (l - 1) * b ≤ 1 := by
    have h := gRatio₂_mul_b_le_one hk hl hlk hb.le hb₁
    rw [gRatio₂, ← hasym₂] at h
    exact h
  have hMNbig₁ : lvlOf (asymRatio k (k - l) * (asymRatio k l * b)) N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA₁b (Nat.cast_nonneg N))
  have hMNbig₂ : lvlOf (asymRatio k (l - 1) * b) N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA₂b (Nat.cast_nonneg N))
  have hm₁N : lvlOf (asymRatio k l * b) N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hρb1 (Nat.cast_nonneg N))
  have hm₂N : lvlOf b N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg N))
  have hfrl₁ : refLvl (k - l) k (lvlOf (asymRatio k l * b) N)
      ≤ lvlOf (asymRatio k (k - l) * (asymRatio k l * b)) N :=
    floor_refLvl_le_lvlOf hP1 hPk hy₁
  have hfrl₂ : refLvl (l - 1) k (lvlOf b N) ≤ lvlOf (asymRatio k (l - 1) * b) N :=
    floor_refLvl_le_lvlOf hQ1 hQk hb.le
  have hgrl₁ : lvlOf (asymRatio k (k - l) * (asymRatio k l * b)) N
      ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N) + (k + 1) :=
    floor_lvlOf_le_refLvl_add hk hP1 hPk hy₁
  have hgrl₂ : lvlOf (asymRatio k (l - 1) * b) N
      ≤ refLvl (l - 1) k (lvlOf b N) + (k + 1) :=
    floor_lvlOf_le_refLvl_add hk hQ1 hQk hb.le
  have h2rl₁ : 2 ≤ refLvl (k - l) k (lvlOf (asymRatio k l * b) N) := le_trans h2m₂ hm₂rl₁
  have h2rl₂ : 2 ≤ refLvl (l - 1) k (lvlOf b N) := le_trans h2m₁ hm₁rl₂
  have h1m₂ : 1 ≤ lvlOf b N := le_trans (by norm_num) h2m₂
  have h1m₁ : 1 ≤ lvlOf (asymRatio k l * b) N := le_trans (by norm_num) h2m₁
  -- the two factors
  have hcoars₁ := hcoarsen₁ (M := refLvl (k - l) k (lvlOf (asymRatio k l * b) N))
      (M' := lvlOf (asymRatio k (k - l) * (asymRatio k l * b)) N) (m' := lvlOf (asymRatio k l * b) N)
      h2rl₁ hfrl₁ hgrl₁ hMNbig₁ hbig₁
  have hfac₁ := hmodel₁ h2m₂ hm₂rl₁ (le_trans hfrl₁ hMNbig₁) h4₁ h1m₂ _ hcoars₁
  have hcoars₂ := hcoarsen₂ (M := refLvl (l - 1) k (lvlOf b N))
      (M' := lvlOf (asymRatio k (l - 1) * b) N) (m' := lvlOf b N)
      h2rl₂ hfrl₂ hgrl₂ hMNbig₂ hbig₂
  have hfac₂ := hmodel₂ h2m₁ hm₁rl₂ (le_trans hfrl₂ hMNbig₂) h4₂ h1m₁ _ hcoars₂
  -- Holder
  have hθeq : (1:ℝ) / ((k - l + 1 : ℕ) : ℝ) = θ := by
    rw [hθ, Nat.cast_add, Nat.cast_one, Nat.cast_sub hlk']
  have hhold := asymDec_of_holder hk hl1 (by omega : l + 1 ≤ k) h2m₁ hm₁N h2m₂ hm₂N hfac₁ hfac₂
  rw [hθeq] at hhold
  refine AsymDec_mono ?_ hhold
  -- the constant bookkeeping
  set g₁ : ℕ := refLvl (k - l) k (lvlOf (asymRatio k l * b) N) - lvlOf b N with hg₁
  set g₂ : ℕ := refLvl (l - 1) k (lvlOf b N) - lvlOf (asymRatio k l * b) N with hg₂
  have hgoal_const₁ : ((ENNReal.ofReal (K₁ * (2:ℝ) ^ ((N:ℝ) * A₁))
        * Kc₁ ^ q) * (Cm₁ * ((((2 ^ g₁ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₁) ^ θ
      ≤ ENNReal.ofReal (K₁ ^ θ * M₁ * (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))) := by
    have h := factor_const_le (K := K₁) (A := (N:ℝ) * A₁) (Kc := Kc₁) (Cm := Cm₁)
      (q := q) (r := r₁) (s := s) (θ := θ) (g := g₁) hK₁0.le hKc₁top hCm₁top hq0 hr₁0 hs0 hθ0 hθ1
    rw [hM₁, hD₁]
    exact h
  have hgoal_const₂ : ((ENNReal.ofReal (K₂ * (2:ℝ) ^ ((N:ℝ) * A₂))
        * Kc₂ ^ q) * (Cm₂ * ((((2 ^ g₂ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₂) ^ (1 - θ)
      ≤ ENNReal.ofReal (K₂ ^ (1 - θ) * M₂
          * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂)))) := by
    have h := factor_const_le (K := K₂) (A := (N:ℝ) * A₂) (Kc := Kc₂) (Cm := Cm₂)
      (q := q) (r := r₂) (s := s) (θ := 1 - θ) (g := g₂) hK₂0.le hKc₂top hCm₂top hq0 hr₂0 hs0 h1θ0 h1θ1
    rw [hM₂, hD₂]
    exact h
  -- the exponent estimate
  have hG₁ : (g₁:ℝ) ≤ gRatio₁ k l * b * (N:ℝ) := by
    have h1 : (g₁:ℝ) ≤ ((refLvl (k - l) k (lvlOf (asymRatio k l * b) N) : ℕ) : ℝ) := by
      rw [hg₁]
      exact_mod_cast Nat.sub_le _ _
    have hm₁le : ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) ≤ asymRatio k l * b * (N:ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : ((refLvl (k - l) k (lvlOf (asymRatio k l * b) N) : ℕ) : ℝ)
        ≤ (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ))
            * ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) := by
      rw [refLvl]
      calc ((((k - (k - l) + 1) * lvlOf (asymRatio k l * b) N) / (k - l) : ℕ) : ℝ)
          ≤ ((((k - (k - l) + 1) * lvlOf (asymRatio k l * b) N : ℕ)) : ℝ) / ((k - l : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ = (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ))
              * ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) := by push_cast; ring
    have hc0 : 0 ≤ ((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ) := by
      have hnum : (0:ℝ) ≤ ((k - (k - l) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hden0 : (0:ℝ) < ((k - l : ℕ) : ℝ) := by
        have : 0 < k - l := by omega
        exact_mod_cast this
      exact div_nonneg hnum hden0.le
    calc (g₁:ℝ) ≤ ((refLvl (k - l) k (lvlOf (asymRatio k l * b) N) : ℕ) : ℝ) := h1
      _ ≤ (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ))
            * ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) := h2
      _ ≤ (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * (asymRatio k l * b * (N:ℝ)) :=
          mul_le_mul_of_nonneg_left hm₁le hc0
      _ = gRatio₁ k l * b * (N:ℝ) := by rw [gRatio₁]; ring
  have hG₂ : (g₂:ℝ) ≤ gRatio₂ k l * b * (N:ℝ) := by
    have h1 : (g₂:ℝ) ≤ ((refLvl (l - 1) k (lvlOf b N) : ℕ) : ℝ) := by
      rw [hg₂]
      exact_mod_cast Nat.sub_le _ _
    have hm₂le : ((lvlOf b N : ℕ) : ℝ) ≤ b * (N:ℝ) := Nat.floor_le (by positivity)
    have h2 : ((refLvl (l - 1) k (lvlOf b N) : ℕ) : ℝ)
        ≤ (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * ((lvlOf b N : ℕ) : ℝ) := by
      rw [refLvl]
      calc ((((k - (l - 1) + 1) * lvlOf b N) / (l - 1) : ℕ) : ℝ)
          ≤ ((((k - (l - 1) + 1) * lvlOf b N : ℕ)) : ℝ) / ((l - 1 : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ = (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * ((lvlOf b N : ℕ) : ℝ) := by
            push_cast; ring
    have hc0 : 0 ≤ ((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) := by
      have hnum : (0:ℝ) ≤ ((k - (l - 1) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hden0 : (0:ℝ) < ((l - 1 : ℕ) : ℝ) := by
        have : 0 < l - 1 := by omega
        exact_mod_cast this
      exact div_nonneg hnum hden0.le
    calc (g₂:ℝ) ≤ ((refLvl (l - 1) k (lvlOf b N) : ℕ) : ℝ) := h1
      _ ≤ (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * ((lvlOf b N : ℕ) : ℝ) := h2
      _ ≤ (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * (b * (N:ℝ)) :=
          mul_le_mul_of_nonneg_left hm₂le hc0
      _ = gRatio₂ k l * b * (N:ℝ) := by rw [gRatio₂]; ring
  have hrecC : recC k l = 2 * max (gRatio₁ k l) (gRatio₂ k l) := rfl
  have hexp_le : θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁))
      + (1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂))
      ≤ (N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b) := by
    have hmax0 : 0 ≤ max (gRatio₁ k l) (gRatio₂ k l) :=
      le_trans (le_of_lt (gRatio₁_pos hl1 hlk)) (le_max_left _ _)
    have hG₁' : (g₁:ℝ) * r₁ ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by
      have hA0' : 0 ≤ gRatio₁ k l * b * (N:ℝ) :=
        mul_nonneg (mul_nonneg (gRatio₁_pos hl1 hlk).le hb.le) (Nat.cast_nonneg N)
      have h2 := mul_le_mul hG₁ hr₁1 hr₁0 hA0'
      have h3 := le_max_left (gRatio₁ k l) (gRatio₂ k l)
      have h4 : gRatio₁ k l * b * (N:ℝ) ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by
        have hbN : 0 ≤ b * (N:ℝ) := mul_nonneg hb.le (Nat.cast_nonneg N)
        calc gRatio₁ k l * b * (N:ℝ) = gRatio₁ k l * (b * (N:ℝ)) := by ring
          _ ≤ max (gRatio₁ k l) (gRatio₂ k l) * (b * (N:ℝ)) :=
              mul_le_mul_of_nonneg_right h3 hbN
          _ = max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by ring
      linarith [h2, h4]
    have hG₂' : (g₂:ℝ) * r₂ ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by
      have hA0' : 0 ≤ gRatio₂ k l * b * (N:ℝ) :=
        mul_nonneg (mul_nonneg (gRatio₂_pos hl hlk).le hb.le) (Nat.cast_nonneg N)
      have h2 := mul_le_mul hG₂ hr₂1 hr₂0 hA0'
      have h3 := le_max_right (gRatio₁ k l) (gRatio₂ k l)
      have h4 : gRatio₂ k l * b * (N:ℝ) ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by
        have hbN : 0 ≤ b * (N:ℝ) := mul_nonneg hb.le (Nat.cast_nonneg N)
        calc gRatio₂ k l * b * (N:ℝ) = gRatio₂ k l * (b * (N:ℝ)) := by ring
          _ ≤ max (gRatio₁ k l) (gRatio₂ k l) * (b * (N:ℝ)) :=
              mul_le_mul_of_nonneg_right h3 hbN
          _ = max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) := by ring
      linarith [h2, h4]
    have hkey : θ * ((g₁:ℝ) * (s * r₁)) + (1 - θ) * ((g₂:ℝ) * (s * r₂))
        ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s := by
      have hkey₁ : (g₁:ℝ) * (s * r₁) ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s := by
        have he : (g₁:ℝ) * (s * r₁) = ((g₁:ℝ) * r₁) * s := by ring
        have h2' : ((g₁:ℝ) * r₁) * s
            ≤ (max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ)) * s :=
          mul_le_mul_of_nonneg_right hG₁' hs0
        have h3' : (max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ)) * s
            = max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s := by ring
        linarith [he, h2', h3']
      have hkey₂ : (g₂:ℝ) * (s * r₂) ≤ max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s := by
        have he : (g₂:ℝ) * (s * r₂) = ((g₂:ℝ) * r₂) * s := by ring
        have h2' : ((g₂:ℝ) * r₂) * s
            ≤ (max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ)) * s :=
          mul_le_mul_of_nonneg_right hG₂' hs0
        have h3' : (max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ)) * s
            = max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s := by ring
        linarith [he, h2', h3']
      have h1 := mul_le_mul_of_nonneg_left hkey₁ hθ0
      have h2 := mul_le_mul_of_nonneg_left hkey₂ h1θ0
      linarith [h1, h2]
    have hstep : max (gRatio₁ k l) (gRatio₂ k l) * b * (N:ℝ) * s
        ≤ (N:ℝ) * recC k l * εm * b := by
      rw [hrecC, hs]
      exact le_of_eq (by ring)
    have hdist : θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁))
        + (1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂))
        = (N:ℝ) * (θ * A₁ + (1 - θ) * A₂)
          + (θ * ((g₁:ℝ) * (s * r₁)) + (1 - θ) * ((g₂:ℝ) * (s * r₂))) := by ring
    rw [hdist]
    nlinarith [hkey, hstep]
  have hcomb : ((ENNReal.ofReal (K₁ * (2:ℝ) ^ ((N:ℝ) * A₁)) * Kc₁ ^ q)
        * (Cm₁ * ((((2 ^ g₁ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₁) ^ θ
      * ((ENNReal.ofReal (K₂ * (2:ℝ) ^ ((N:ℝ) * A₂)) * Kc₂ ^ q)
        * (Cm₂ * ((((2 ^ g₂ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₂) ^ (1 - θ)
      ≤ ENNReal.ofReal (Kfin * (2:ℝ) ^ ((N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b))) := by
    refine le_trans (mul_le_mul' hgoal_const₁ hgoal_const₂) ?_
    rw [← ENNReal.ofReal_mul (by positivity), hKfin]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpw : (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
          * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂)))
        ≤ (2:ℝ) ^ ((N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b)) := by
      rw [← Real.rpow_add (x := 2) (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hexp_le
    have hpos : 0 ≤ K₁ ^ θ * M₁ * (K₂ ^ (1 - θ) * M₂) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hK₁0.le θ) hM₁pos.le)
        (mul_nonneg (Real.rpow_nonneg hK₂0.le (1 - θ)) hM₂pos.le)
    have e1 : K₁ ^ θ * M₁ * (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
          * (K₂ ^ (1 - θ) * M₂ * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂))))
        = (K₁ ^ θ * M₁ * (K₂ ^ (1 - θ) * M₂))
          * ((2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
            * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂ + (g₂:ℝ) * (s * r₂)))) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hpw hpos
  exact hcomb

/-- **The §4 recursion for `l = 1`.**  The second factor is the split-`0` statement, supplied
directly as an `AsymExpSet k hk 0 b` element (in the application it is produced by
`AsymExpZero.mem_asymExpSet_zero_of_linExpSet`); no model hypothesis is needed for it. -/
theorem asymExpSet_recursion_one {k : ℕ} (hk : 1 ≤ k) (hk2 : 1 ≤ k - 1)
    {εm : ℝ} (hεm : 0 < εm)
    (hmMod₁ : ∀ (εm' : ℝ), 0 < εm' → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (k - 1) M
        (laneEnl k (k - 1) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm')))
    {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ b₀ k)
    {A₁ A₂ : ℝ} (hA₁ : A₁ ∈ AsymExpSet k hk (k - 1) (asymRatio k 1 * b))
    (hA₂ : A₂ ∈ AsymExpSet k hk 0 b) :
    (1 / (k : ℝ)) * A₁ + (((k : ℝ) - 1) / (k : ℝ)) * A₂
      + recC k 1 * εm * b ∈ AsymExpSet k hk 1 b := by
  obtain ⟨hA₁0, K₁, hK₁0, N₁, hN₁⟩ := hA₁
  obtain ⟨hA₂0, K₂, hK₂0, N₂, hN₂⟩ := hA₂
  have hP1 : 1 ≤ k - 1 := hk2
  have hPk : k - 1 ≤ k := by omega
  have hPk1 : k - 1 ≤ k - 1 := le_rfl
  have hden : 0 < (k : ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  obtain ⟨Kc₁, -, hKc₁top, hcoarsen₁⟩ := asymDec_coarsen hk (hl := hP1) (D := k + 1)
  obtain ⟨a₀₁, ha₀₁, hmM₁⟩ := hmMod₁ εm hεm
  obtain ⟨Cm₁, hCm₁top, hmodel₁⟩ :=
    asymDec_of_model_uniform hk (hl := hP1) (hlk := hPk) (hlk1 := hPk1) ha₀₁ hεm hmM₁
  have hpk : (0:ℝ) < pkExp k := pkExp_pos hk
  have hpk0 : 0 ≤ pkExp k := hpk.le
  set θ : ℝ := 1 / (k : ℝ) with hθ
  set s : ℝ := 2 * εm with hs
  set q : ℝ := 1 / pkExp k with hq
  set r₁ : ℝ := plExp (k - 1) / pkExp k with hr₁
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg zero_le_one hpk0
  have hr₁0 : 0 ≤ r₁ := by rw [hr₁]; exact div_nonneg (plExp_nonneg _) hpk0
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg zero_le_one hden.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hden]
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have h1θ0 : 0 ≤ 1 - θ := by linarith
  have hr₁1 : r₁ ≤ 1 := by
    rw [hr₁, div_le_one hpk, plExp, pkExp]
    have h1 : ((k - 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast (Nat.sub_le k 1)
    have h2 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    nlinarith [h1, h2]
  set D₁ : ℝ := Kc₁.toReal ^ q * Cm₁.toReal ^ r₁ with hD₁
  set M₁ : ℝ := max 1 D₁ with hM₁
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set Kfin : ℝ := (K₁ ^ θ * M₁) * K₂ ^ (1 - θ) with hKfin
  have hKfinpos : 0 < Kfin := by
    rw [hKfin]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hK₁0 θ) hM₁pos)
      (Real.rpow_pos_of_pos hK₂0 (1 - θ))
  have hAeq : θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b
      = (1 / (k : ℝ)) * A₁ + (((k : ℝ) - 1) / (k : ℝ)) * A₂ + recC k 1 * εm * b := by
    rw [hθ]
    field_simp
  -- the level slack condition of the first factor
  have hslack₁ : b < (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * (asymRatio k 1 * b) := by
    have h1 := one_lt_gRatio₁ (le_refl 1) hk2
    rw [gRatio₁] at h1
    calc b = 1 * b := (one_mul b).symm
      _ < (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * asymRatio k 1 * b :=
          mul_lt_mul_of_pos_right h1 hb
      _ = (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * (asymRatio k 1 * b) := by ring
  obtain ⟨Nsl₁, hsl₁⟩ := exists_lvlOf_le_refLvl (k := k) (L := k - 1) hk hP1 hPk (y := 1)
      (hy := one_pos) (hc0 := mul_pos (asymRatio_pos' hk hk2) hb) (hc2 := hb) hslack₁
  have hev₁ : ∀ᶠ N : ℕ in atTop,
      lvlOf b N ≤ refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) :=
    Filter.eventually_atTop.mpr ⟨Nsl₁, fun N hN => by
      simpa only [mul_one] using hsl₁ N hN⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ lvlOf (asymRatio k 1 * b) N) ∧ (2 ≤ lvlOf b N) ∧
      (lvlOf b N ≤ refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N)) ∧
      (4 ≤ 2 ^ (refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) - lvlOf b N)) := by
    filter_upwards [eventually_two_le_lvlOf (mul_pos (asymRatio_pos' hk hk2) hb),
      eventually_two_le_lvlOf hb, hev₁, eventually_gap₁ (le_refl 1) hk2 hb] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hrecC : recC k 1 = 2 * max (gRatio₁ k 1) (gRatio₂ k 1) := rfl
  have hrecC0 : 0 ≤ recC k 1 := by
    rw [hrecC]
    have h := le_trans (le_of_lt (gRatio₁_pos (le_refl 1) hk2))
      (le_max_left (gRatio₁ k 1) (gRatio₂ k 1))
    linarith
  have hA0 : 0 ≤ θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b := by
    have h1 : 0 ≤ θ * A₁ := mul_nonneg hθ0 hA₁0
    have h2 : 0 ≤ (1 - θ) * A₂ := mul_nonneg h1θ0 hA₂0
    have h3 : 0 ≤ recC k 1 * εm * b := mul_nonneg (mul_nonneg hrecC0 hεm.le) hb.le
    linarith
  rw [← hAeq]
  refine ⟨hA0, Kfin, hKfinpos, max (max N₁ N₂) N₀, fun N hNN => ?_⟩
  have hN₀' : N₀ ≤ N := le_trans (le_max_right _ _) hNN
  obtain ⟨h2m₁, h2m₂, hm₂rl₁, h4₁⟩ := hN₀ N hN₀'
  have N1' : N₁ ≤ N := le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ _) hNN)
  have N2' : N₂ ≤ N := le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ _) hNN)
  have hbig₁ := hN₁ N N1'
  have hA₂conv : AsymDec k hk 0 N (lvlOf (asymRatio k 1 * b) N) (lvlOf b N)
      (ENNReal.ofReal (K₂ * (2:ℝ) ^ ((N:ℝ) * A₂))) := by
    have h := hN₂ N N2'
    have h1 : asymRatio k 0 = asymRatio k 1 := by rw [asymRatio_zero, asymRatio_one]
    rwa [h1] at h
  -- level bounds
  have hy₁ : 0 ≤ asymRatio k 1 * b := (mul_pos (asymRatio_pos' hk hk2) hb).le
  have hρb1 : asymRatio k 1 * b ≤ 1 := asymRatio_mul_b_le_one hk (le_refl 1) (by omega) hb.le hb₁
  have hb1 : b ≤ 1 := le_trans hb₁ (b₀_le_one k)
  have hasym₁ : asymRatio k (k - 1) = ((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hP1, Nat.cast_add, Nat.cast_one, Nat.cast_sub hPk]
  have hA₁b : asymRatio k (k - 1) * (asymRatio k 1 * b) ≤ 1 := by
    have h := gRatio₁_mul_b_le_one (le_refl 1) hk2 hb.le hb₁
    rw [gRatio₁, ← hasym₁, mul_assoc] at h
    exact h
  have hMNbig₁ : lvlOf (asymRatio k (k - 1) * (asymRatio k 1 * b)) N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA₁b (Nat.cast_nonneg N))
  have hm₁N : lvlOf (asymRatio k 1 * b) N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hρb1 (Nat.cast_nonneg N))
  have hm₂N : lvlOf b N ≤ N :=
    lvlOf_le_of_mul_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg N))
  have hfrl₁ : refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N)
      ≤ lvlOf (asymRatio k (k - 1) * (asymRatio k 1 * b)) N :=
    floor_refLvl_le_lvlOf hP1 hPk hy₁
  have hgrl₁ : lvlOf (asymRatio k (k - 1) * (asymRatio k 1 * b)) N
      ≤ refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) + (k + 1) :=
    floor_lvlOf_le_refLvl_add hk hP1 hPk hy₁
  have h2rl₁ : 2 ≤ refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) := le_trans h2m₂ hm₂rl₁
  have h1m₂ : 1 ≤ lvlOf b N := le_trans (by norm_num) h2m₂
  have h1m₁ : 1 ≤ lvlOf (asymRatio k 1 * b) N := le_trans (by norm_num) h2m₁
  -- factor 1
  have hcoars₁ := hcoarsen₁ (M := refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N))
      (M' := lvlOf (asymRatio k (k - 1) * (asymRatio k 1 * b)) N) (m' := lvlOf (asymRatio k 1 * b) N)
      h2rl₁ hfrl₁ hgrl₁ hMNbig₁ hbig₁
  have hfac₁ := hmodel₁ h2m₂ hm₂rl₁ (le_trans hfrl₁ hMNbig₁) h4₁ h1m₂ _ hcoars₁
  -- Holder
  have hθeq : (1:ℝ) / ((k - 1 + 1 : ℕ) : ℝ) = θ := by
    rw [hθ, Nat.sub_add_cancel hk]
  have hhold := asymDec_of_holder hk (le_refl 1) (by omega : 1 + 1 ≤ k) h2m₁ hm₁N h2m₂ hm₂N
    hfac₁ hA₂conv
  rw [hθeq] at hhold
  refine AsymDec_mono ?_ hhold
  -- constants
  set g₁ : ℕ := refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) - lvlOf b N with hg₁
  have hgoal_const₁ : ((ENNReal.ofReal (K₁ * (2:ℝ) ^ ((N:ℝ) * A₁))
        * Kc₁ ^ q) * (Cm₁ * ((((2 ^ g₁ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₁) ^ θ
      ≤ ENNReal.ofReal (K₁ ^ θ * M₁ * (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))) := by
    have h := factor_const_le (K := K₁) (A := (N:ℝ) * A₁) (Kc := Kc₁) (Cm := Cm₁)
      (q := q) (r := r₁) (s := s) (θ := θ) (g := g₁) hK₁0.le hKc₁top hCm₁top hq0 hr₁0 hs0 hθ0 hθ1
    rw [hM₁, hD₁]
    exact h
  have hgoal_const₂ : (ENNReal.ofReal (K₂ * (2:ℝ) ^ ((N:ℝ) * A₂))) ^ (1 - θ)
      ≤ ENNReal.ofReal (K₂ ^ (1 - θ) * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) h1θ0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.mul_rpow hK₂0.le (by positivity),
      (Real.rpow_mul (x := 2) (by norm_num) ((N:ℝ) * A₂) (1 - θ)).symm]
    exact le_of_eq (by ring)
  -- exponent estimate
  have hG₁ : (g₁:ℝ) ≤ gRatio₁ k 1 * b * (N:ℝ) := by
    have h1 : (g₁:ℝ) ≤ ((refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) : ℕ) : ℝ) := by
      rw [hg₁]
      exact_mod_cast Nat.sub_le _ _
    have hm₁le : ((lvlOf (asymRatio k 1 * b) N : ℕ) : ℝ) ≤ asymRatio k 1 * b * (N:ℝ) :=
      Nat.floor_le (by positivity)
    have h2 : ((refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) : ℕ) : ℝ)
        ≤ (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ))
            * ((lvlOf (asymRatio k 1 * b) N : ℕ) : ℝ) := by
      rw [refLvl]
      calc ((((k - (k - 1) + 1) * lvlOf (asymRatio k 1 * b) N) / (k - 1) : ℕ) : ℝ)
          ≤ ((((k - (k - 1) + 1) * lvlOf (asymRatio k 1 * b) N : ℕ)) : ℝ) / ((k - 1 : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ = (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ))
              * ((lvlOf (asymRatio k 1 * b) N : ℕ) : ℝ) := by push_cast; ring
    have hc0 : 0 ≤ ((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
      have hnum : (0:ℝ) ≤ ((k - (k - 1) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hden0 : (0:ℝ) < ((k - 1 : ℕ) : ℝ) := by
        have : 0 < k - 1 := by omega
        exact_mod_cast this
      exact div_nonneg hnum hden0.le
    calc (g₁:ℝ) ≤ ((refLvl (k - 1) k (lvlOf (asymRatio k 1 * b) N) : ℕ) : ℝ) := h1
      _ ≤ (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ))
            * ((lvlOf (asymRatio k 1 * b) N : ℕ) : ℝ) := h2
      _ ≤ (((k - (k - 1) + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * (asymRatio k 1 * b * (N:ℝ)) :=
          mul_le_mul_of_nonneg_left hm₁le hc0
      _ = gRatio₁ k 1 * b * (N:ℝ) := by rw [gRatio₁]; ring
  have hexp_le : θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)) + (1 - θ) * ((N:ℝ) * A₂)
      ≤ (N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b) := by
    have hG₁' : (g₁:ℝ) * r₁ ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) := by
      have hA0' : 0 ≤ gRatio₁ k 1 * b * (N:ℝ) :=
        mul_nonneg (mul_nonneg (gRatio₁_pos (le_refl 1) hk2).le hb.le) (Nat.cast_nonneg N)
      have h2 := mul_le_mul hG₁ hr₁1 hr₁0 hA0'
      have h3 := le_max_left (gRatio₁ k 1) (gRatio₂ k 1)
      have h4 : gRatio₁ k 1 * b * (N:ℝ) ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) := by
        have hbN : 0 ≤ b * (N:ℝ) := mul_nonneg hb.le (Nat.cast_nonneg N)
        calc gRatio₁ k 1 * b * (N:ℝ) = gRatio₁ k 1 * (b * (N:ℝ)) := by ring
          _ ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * (b * (N:ℝ)) :=
              mul_le_mul_of_nonneg_right h3 hbN
          _ = max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) := by ring
      linarith [h2, h4]
    have hkey₁ : (g₁:ℝ) * (s * r₁) ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s := by
      have he : (g₁:ℝ) * (s * r₁) = ((g₁:ℝ) * r₁) * s := by ring
      have h2' : ((g₁:ℝ) * r₁) * s
          ≤ (max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ)) * s :=
        mul_le_mul_of_nonneg_right hG₁' hs0
      have h3' : (max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ)) * s
          = max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s := by ring
      linarith [he, h2', h3']
    have h1 := mul_le_mul_of_nonneg_left hkey₁ hθ0
    have hstep : max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s
        ≤ (N:ℝ) * recC k 1 * εm * b := by
      rw [hrecC, hs]
      exact le_of_eq (by ring)
    have hdist : θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)) + (1 - θ) * ((N:ℝ) * A₂)
        = (N:ℝ) * (θ * A₁ + (1 - θ) * A₂) + θ * ((g₁:ℝ) * (s * r₁)) := by ring
    rw [hdist]
    have hM0 : 0 ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s :=
      mul_nonneg (mul_nonneg (mul_nonneg
        (le_trans (le_of_lt (gRatio₁_pos (le_refl 1) hk2)) (le_max_left _ _)) hb.le)
        (Nat.cast_nonneg N)) hs0
    have hθmax : θ * (max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s)
        ≤ max (gRatio₁ k 1) (gRatio₂ k 1) * b * (N:ℝ) * s := by
      nlinarith [hθ0, hθ1, hM0]
    have h2 : θ * ((g₁:ℝ) * (s * r₁)) ≤ (N:ℝ) * recC k 1 * εm * b :=
      le_trans (le_trans h1 hθmax) hstep
    have hexpand : (N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b)
        = (N:ℝ) * (θ * A₁ + (1 - θ) * A₂) + (N:ℝ) * recC k 1 * εm * b := by ring
    rw [hexpand]
    linarith [h2]
  have hcomb : ((ENNReal.ofReal (K₁ * (2:ℝ) ^ ((N:ℝ) * A₁)) * Kc₁ ^ q)
        * (Cm₁ * ((((2 ^ g₁ : ℕ)) : ℝ≥0∞)) ^ s) ^ r₁) ^ θ
      * (ENNReal.ofReal (K₂ * (2:ℝ) ^ ((N:ℝ) * A₂))) ^ (1 - θ)
      ≤ ENNReal.ofReal (Kfin * (2:ℝ) ^ ((N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b))) := by
    refine le_trans (mul_le_mul' hgoal_const₁ hgoal_const₂) ?_
    rw [← ENNReal.ofReal_mul (by positivity), hKfin]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpw : (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
          * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂))
        ≤ (2:ℝ) ^ ((N:ℝ) * (θ * A₁ + (1 - θ) * A₂ + recC k 1 * εm * b)) := by
      rw [← Real.rpow_add (x := 2) (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hexp_le
    have hpos : 0 ≤ K₁ ^ θ * M₁ * K₂ ^ (1 - θ) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hK₁0.le θ) hM₁pos.le)
        (Real.rpow_nonneg hK₂0.le (1 - θ))
    have e1 : K₁ ^ θ * M₁ * (2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
          * (K₂ ^ (1 - θ) * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂)))
        = (K₁ ^ θ * M₁ * K₂ ^ (1 - θ))
          * ((2:ℝ) ^ (θ * ((N:ℝ) * A₁ + (g₁:ℝ) * (s * r₁)))
            * (2:ℝ) ^ ((1 - θ) * ((N:ℝ) * A₂))) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hpw hpos
  exact hcomb

/-- **The first-factor slack, in level form.**  `asymRatio k (k−l)·(asymRatio k l·b) ≤ 1` for
`b ≤ b₀ k`: this is what makes the canonical first level of the `(k−l)`-factor at most `N`. -/
lemma asymRatio_mul_asymRatio_mul_le_one {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 ≤ b) (hb₁ : b ≤ b₀ k) :
    asymRatio k (k - l) * (asymRatio k l * b) ≤ 1 := by
  have hP1 : 1 ≤ k - l := by omega
  have hPk : k - l ≤ k := by omega
  have hasym₁ : asymRatio k (k - l) = ((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hP1, Nat.cast_add, Nat.cast_one, Nat.cast_sub hPk]
  have h := gRatio₁_mul_b_le_one hl hlk hb hb₁
  rw [gRatio₁, ← hasym₁, mul_assoc] at h
  exact h

/-- **The second-factor slack, in level form.**  `asymRatio k (l−1)·b ≤ 1` for `b ≤ b₀ k`. -/
lemma asymRatio_pred_mul_le_one {k l : ℕ} (hk : 1 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 ≤ b) (hb₁ : b ≤ b₀ k) : asymRatio k (l - 1) * b ≤ 1 := by
  have hQ1 : 1 ≤ l - 1 := by omega
  have hasym₂ : asymRatio k (l - 1) = ((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hQ1, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : l - 1 ≤ k)]
  have h := gRatio₂_mul_b_le_one hk hl hlk hb hb₁
  rw [gRatio₂, ← hasym₂] at h
  exact h

end Submission.Vinogradov

