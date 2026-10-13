/-
# `FTS/PhiStar/CoreAux/Fb_of_FlatW.lean` — the flat class `FlatW 7` implies the shifted class `Fb 6`

`Work.FTS.VocabO2.FlatW l f K` records, on the open quadrant `Q0 = (0,∞)×(0,π/2)`,

* `|(z+1)^k ∂_z^k f| ≤ K` for `k ≤ l`, and
* `|(z+1)^k ∂_z^k D_θ^i (∂_θ f)| ≤ K` for `k+i+1 ≤ l`.

`Work.FTS.PhiStar.Fb n K f` (see `CoreAux/Defs.lean`) is the pair `F0 n K f`,
`F0 n K (∂_θ f)`, where `F0 n K g` asks for `|(z+1)^k ∂_z^k D_θ^i g| ≤ K` for `k+i ≤ n`.

The second half of `Fb 6` is immediate from `FlatW` (`F0_six_pth_of_FlatW`).  The first half is
the substance: `FlatW` controls `D_θ^{i+1} f` only through `∂_θ f`, and the bridge back to
`D_θ^i f` is the Leibniz rule for the derivation `D_θ = sin(2·) ∂_θ`,

`D_θ^i f = D_θ^{i-1}((sin 2·)·∂_θ f) = ∑_{a<i} C(i-1,a) · D_θ^a(sin 2·) · D_θ^{i-1-a}(∂_θ f)`,

whose `z`-derivative form is `Work.FTS.PhiStar.pzIter_DthIter_leibniz`.  Every term is then a
product of a bound on an iterate of `sin 2·` (at most `A`, for angular orders `a ≤ 5`) with a
bound coming directly from `FlatW` (`k + (i-1-a) + 1 ≤ 7`), and the binomial coefficients sum to
`2^{i-1} ≤ 32`.

The constants are explicit: the binomial sum contributes `2^{i-1} ≤ 32`, and the angular factors
are bounded by `A = max 384 3840`, the order-`5` iterate coming from
`Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound` and the orders `≤ 4` from
`Work.FTS.H2.abs_DthIter_Sfun_le`.  The resulting constant is `C = 32·A + 1`.

The development is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.pzIter_DthIter_leibniz
import Submission.Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option maxHeartbeats 2000000

/-! ## The `∂_θ f`-half -/

/-- **`FlatW 7 f K` gives the flat bounds of `F0 6` for `∂_θ f`**, directly: `F0 6` needs the
angular order `k+i`, one *less* than the order `k+i+1` recorded by `FlatW 7`. -/
theorem F0_six_pth_of_FlatW {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.VocabO2.FlatW 7 f K) :
    Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f) := by
  intro k i hki z θ hz hθ hθ'
  exact (h z θ hz hθ hθ').2 k i (by omega)

/-! ## The Leibniz sum -/

/-- **The `a`-th summand of the Leibniz expansion is bounded by `C(i-1,a)·A·K`.** -/
theorem leibniz_term_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (h : Work.FTS.VocabO2.FlatW 7 f K) {i k a : ℕ} (ha : a ∈ Finset.range i) (hki : k + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      ≤ ((i - 1).choose a : ℝ) * (A * K) := by
  have hai : a ≤ i - 1 := by
    have := Finset.mem_range.mp ha
    omega
  have ha5 : a ≤ 5 := by omega
  have hX : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := hAb a ha5 z θ hθ hθ'
  have hY : |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
    (h z θ hz hθ hθ').2 k (i - 1 - a) (by omega)
  have hcoef : (0 : ℝ) ≤ ((i - 1).choose a : ℝ) := by positivity
  have hzp : (0 : ℝ) < (z + 1) ^ k := pow_pos (by linarith) k
  have h1 : |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      = ((i - 1).choose a : ℝ) *
        (|Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
          |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ|) := by
    simp only [abs_mul, abs_of_nonneg hcoef, abs_of_pos hzp]
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hX hY (abs_nonneg _) hA) hcoef

/-- **The Leibniz sum is bounded by `2^{i-1}·A·K ≤ 32·A·K`.** -/
theorem leibniz_sum_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (h : Work.FTS.VocabO2.FlatW 7 f K) {i k : ℕ} (hi : 1 ≤ i) (hki : k + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ)|
      ≤ 32 * A * K := by
  have hchoose : (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) = (2 : ℝ) ^ (i - 1) := by
    have h1 : Finset.range i = Finset.range ((i - 1) + 1) := by
      congr 1
      omega
    rw [h1]
    exact_mod_cast Nat.sum_range_choose (n := i - 1)
  have hpow : (2 : ℝ) ^ (i - 1) ≤ 32 := by
    have hi6 : i ≤ 6 := by omega
    calc (2 : ℝ) ^ (i - 1) ≤ 2 ^ 5 := by
          apply pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun a ha => leibniz_term_le hA hK hAb h ha hki hz hθ hθ')) ?_
  calc (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) * (A * K))
      = (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) * (A * K) := (Finset.sum_mul ..).symm
    _ = (2 : ℝ) ^ (i - 1) * (A * K) := by rw [hchoose]
    _ ≤ 32 * (A * K) := mul_le_mul_of_nonneg_right hpow (mul_nonneg hA hK)
    _ = 32 * A * K := by ring

/-! ## The two halves of `Fb 6` -/

/-- **A bound on the fifth iterate gives a uniform bound on the iterates of orders `≤ 5`**: the
orders `≤ 4` are covered by the explicit `Work.FTS.H2.abs_DthIter_Sfun_le`
(`|D_θ^r(sin 2·)| ≤ Asin r · sin 2θ`, `Asin r ≤ 384`), and `sin 2θ ≤ 1` on `[0,π/2]`. -/
theorem exists_bound_of_five {M : ℝ} (hM : 0 < M)
    (h5 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := by
  have hsmall : ∀ (r : ℕ), r ≤ 4 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter r Work.FTS.H2.Sfun z θ| ≤ 384 := by
    intro r hr z θ hθ hθ'
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hb := Work.FTS.H2.abs_DthIter_Sfun_le r hr z
      (θ := θ) (by simp only [Work.Spaces.Iθ]; exact ⟨hθ.le, hθ'.le⟩)
    have hA : Work.FTS.H2.Asin r ≤ 384 := by
      interval_cases r <;> norm_num [Work.FTS.H2.Asin]
    calc |Work.Spaces.DthIter r Work.FTS.H2.Sfun z θ|
        ≤ Work.FTS.H2.Asin r * Real.sin (2 * θ) := hb
      _ ≤ 384 * 1 := mul_le_mul hA hsin1 hsin0 (by norm_num)
      _ = 384 := by ring
  refine ⟨max 384 M, lt_max_of_lt_left (by norm_num), fun a ha z θ hθ hθ' => ?_⟩
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 by omega)
    with h | h | h | h | h | h <;> rw [h]
  · exact le_trans (hsmall 0 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 1 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 2 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 3 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 4 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (h5 z θ hθ hθ') (le_max_right _ _)

/-- **`FlatW 7 f K` gives `F0 6 (C·K) f`**, with the explicit constant `C = 32·A + 1` where `A`
bounds the `D_θ`-iterates of `sin 2·` up to order `5`. -/
theorem F0_six_of_FlatW {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h : Work.FTS.VocabO2.FlatW 7 f K) :
    Work.FTS.PhiStar.F0 6 ((32 * A + 1) * K) f := by
  intro k i hki z θ hz hθ hθ'
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 0 f) z θ| ≤ K := by
      simpa using (h z θ hz hθ hθ').1 k (by omega)
    calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 0 f) z θ| ≤ K := h0
      _ = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right hC1 hK
  · rw [Work.FTS.PhiStar.pzIter_DthIter_leibniz hsm hi hz ⟨hθ, hθ'⟩]
    exact le_trans (leibniz_sum_le hA hK hAb h hi hki hz hθ hθ') (by
      have h32 : (32 : ℝ) * A * K ≤ (32 * A + 1) * K := by nlinarith [mul_nonneg hA hK]
      linarith)

/-- **`FlatW 7` implies `Fb 6`** (up to a universal constant): the constant is `C = 32·A + 1`,
where `A = max 384 M` bounds the `D_θ`-iterates of `sin 2·` of orders `≤ 5`
(`Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound` supplies `M` for the order-`5` iterate and
`Work.FTS.H2.abs_DthIter_Sfun_le` the orders `≤ 4`). -/
theorem Fb_of_FlatW : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 7 f K → Work.FTS.PhiStar.Fb 6 (C * K) f := by
  obtain ⟨M, hMpos, hM⟩ := DthIter_five_Sfun_bound
  obtain ⟨A, hApos, hAb⟩ := exists_bound_of_five hMpos hM
  refine ⟨32 * A + 1, by linarith, ?_⟩
  intro K f hK hsm hflat
  have hmono : K ≤ (32 * A + 1) * K := by
    have h1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
    calc K = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right h1 hK
  exact ⟨F0_six_of_FlatW hApos.le hK hAb hsm hflat,
    (F0_six_pth_of_FlatW hflat).mono le_rfl hmono⟩

end Work.FTS.PhiStar.CoreAux
