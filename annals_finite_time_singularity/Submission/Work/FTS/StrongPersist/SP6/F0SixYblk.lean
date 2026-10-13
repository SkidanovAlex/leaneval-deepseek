/-
# `FTS/StrongPersist/SP6/F0SixYblk.lean` — the flat class of the block `D_zŶ = z ∂_zŶ`

The single object whose flat `𝒲`-bounds drive the eleven fields of `StarPkgo2` is
`Ŷ = Ycheck α Φs`; the analysis of `FTS/PhiStar/CoreAux` transfers the analytic input
`VocabO2.FlatW 7 Ŷ K` to every algebraic combination of `Ŷ` and its derivatives, and one of
those combinations is the **radial block**

`Yblk Ŷ = D_zŶ = z · ∂_zŶ`.

This file proves that the flat class `F0 6` of that block follows from `FlatW 7 Ŷ K` with a
universal constant:

`∃ C > 0,  FlatW 7 Y K  →  F0 6 (C·K) (Yblk Y)`   (`F0SixYblk`).

**The mathematics.**  On the open quadrant `Q0 = (0,∞) × (0,π/2)` the operators `D_θ` and
`D_z` commute (`DthIter_Dz_comm_smoothOpen`), so

`D_θ^i (z ∂_zY) = z · ∂_z (D_θ^i Y)`,

and then the elementary product rule `∂_z^k (z · g) = z · ∂_z^{k+1} g + k · ∂_z^k g`
(`pzIter_zpz_expand`) gives

`(z+1)^k ∂_z^k D_θ^i (Yblk Y)
   = (z/(z+1))·(z+1)^{k+1} ∂_z^{k+1} D_θ^i Y + k·(z+1)^k ∂_z^k D_θ^i Y`.

Both displayed derivatives of `D_θ^i Y` are bounded by `(32A+1)·K`, where `A` bounds the
`D_θ`-iterates of `sin 2·` of orders `≤ 5`:

* for `i = 0` they are the radial slots of `FlatW 7 Y K` (`m ≤ 7`);
* for `i ≥ 1`, `D_θ^i Y` is expanded by the Leibniz rule `D_θ^i Y = D_θ^{i-1}((sin 2·)∂_θY)`
  (`Work.FTS.PhiStar.pzIter_DthIter_leibniz`); since `k + i ≤ 6` the angular order satisfies
  `i ≤ 6`, so only the iterates `D_θ^a (sin 2·)`, `a ≤ i-1 ≤ 5`, appear, and the remaining
  slots are the flat bounds on `∂_θY` supplied by `FlatW`'s second clause.

Since `0 ≤ z/(z+1) ≤ 1` and `k ≤ 6`, the total is at most `(1 + 6)·(32A+1)·K`, so
`C = 7·(32A+1)` works; the constants are uniform because `A` is a genuine bound on the
finitely many iterates of `sin 2·` (orders `≤ 4` by `Work.FTS.H2.abs_DthIter_Sfun_le`, order
`5` by `Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The order-`7` Leibniz expansion of `D_θ^i` -/

/-- **The `a`-th summand of the Leibniz expansion of `∂_z^k D_θ^i f`, one angular order
above the range of `FlatW`.**

The angular order here is allowed to reach `i = 6` with `k + i ≤ 7`: the iterate
`D_θ^a (sin 2·)` only runs up to `a ≤ i - 1 ≤ 5` (which is why the hypothesis `i ≤ 6` is
required), and each remaining slot is one of the quantities bounded by `K` in the second
clause of `FlatW 7 f K`, i.e. by `F0 6 K (∂_θ f)`. -/
theorem leibniz_term_le7 {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hpth : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f))
    {i k a : ℕ} (ha : a ∈ Finset.range i) (hi6 : i ≤ 6) (hki : k + i ≤ 7)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      ≤ ((i - 1).choose a : ℝ) * (A * K) := by
  have halt : a < i := Finset.mem_range.mp ha
  have hai : a ≤ i - 1 := by omega
  have ha5 : a ≤ 5 := by omega
  have hX : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := hAb a ha5 z θ hθ hθ'
  have hY : |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
    hpth k (i - 1 - a) (by omega) z θ hz hθ hθ'
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

/-- **The mixed angular slot of order `k + i ≤ 7`, `i ≤ 6`, at the `∂_θ`-half constant.**

For `1 ≤ i ≤ 6`, `k + i ≤ 7` and a datum whose `∂_θ`-half lies in `F0 6 K`, the Leibniz
expansion of `D_θ^i` (`pzIter_DthIter_leibniz`) gives

`|(z+1)^k ∂_z^k D_θ^i f| ≤ 32·A·K`.

The factor `32 = 2^5` is the binomial sum `∑_{a<i} C(i-1,a) = 2^{i-1} ≤ 2^5`. -/
theorem mixed_flat_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hpth : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f))
    {i k : ℕ} (hi : 1 ≤ i) (hi6 : i ≤ 6) (hki : k + i ≤ 7)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ 32 * A * K := by
  rw [Work.FTS.PhiStar.pzIter_DthIter_leibniz (f := f) hsm hi hz ⟨hθ, hθ'⟩]
  have hchoose : (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) = (2 : ℝ) ^ (i - 1) := by
    have h1 : Finset.range i = Finset.range ((i - 1) + 1) := by
      congr 1
      omega
    rw [h1]
    exact_mod_cast Nat.sum_range_choose (n := i - 1)
  have hpow : (2 : ℝ) ^ (i - 1) ≤ 32 := by
    calc (2 : ℝ) ^ (i - 1) ≤ 2 ^ 5 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun a ha =>
    leibniz_term_le7 hA hK hAb hpth ha hi6 hki hz hθ hθ')) ?_
  calc (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) * (A * K))
      = (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) * (A * K) := (Finset.sum_mul ..).symm
    _ = (2 : ℝ) ^ (i - 1) * (A * K) := by rw [hchoose]
    _ ≤ 32 * (A * K) := mul_le_mul_of_nonneg_right hpow (mul_nonneg hA hK)
    _ = 32 * A * K := by ring

/-! ## The unified slot bound for `Y` -/

/-- **Every mixed slot `∂_z^m D_θ^i Y` with `m + i ≤ 7` and `i ≤ 6` is bounded by
`(32A+1)·K`.**

* `i = 0`: the radial slots of `FlatW 7 Y K` (`m ≤ 7`), compared with `K ≤ (32A+1)K`;
* `i ≥ 1`: the mixed bound `mixed_flat_le`, using `32·A·K ≤ (32A+1)·K`.

This is the order-`7` companion of `Work.FTS.PhiStar.CoreAux.F0_six_of_FlatW` (which stops at
order `6`, exactly because the angular Leibniz rule costs one order). -/
theorem flat_mixed_le {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hflat : Work.FTS.VocabO2.FlatW 7 Y K)
    {m i : ℕ} (hi6 : i ≤ 6) (hmi : m + i ≤ 7) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K := by
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp only [Work.Spaces.DthIter_zero]
    have hR : |(z + 1) ^ m * Work.Spaces.pzIter m Y z θ| ≤ K :=
      (hflat z θ hz hθ hθ').1 m (by omega)
    calc |(z + 1) ^ m * Work.Spaces.pzIter m Y z θ| ≤ K := hR
      _ = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right hC1 hK
  · have h1 : 1 ≤ i := Nat.succ_le_of_lt hpos
    have hmix : |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ|
        ≤ 32 * A * K :=
      mixed_flat_le hA hK hAb hsm
        (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hflat) h1 hi6 hmi hz hθ hθ'
    have h2 : 32 * A * K ≤ (32 * A + 1) * K := by
      nlinarith [mul_nonneg hA hK]
    linarith

/-! ## The target -/

/-- **`FlatW 7 Y K` implies `F0 6 (C·K) (Yblk Y)`** with the universal constant
`C = 7·(32A+1)`, where `A` bounds the `D_θ`-iterates of `sin 2·` up to order `5`.

`D_θ^i` commutes with `D_z = z∂_z` on the open quadrant, and the `k`-fold product rule
`pzIter_zpz_expand` writes

`∂_z^k D_θ^i (Yblk Y) = z·∂_z^{k+1} D_θ^i Y + k·∂_z^k D_θ^i Y`;

both slots are bounded by `(32A+1)K` (`flat_mixed_le`, the orders being `k+1+i ≤ 7` resp.
`k+i ≤ 6`), and `z/(z+1) ≤ 1`, `k ≤ 6` finish the estimate. -/
theorem F0SixYblk : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.VocabO2.FlatW 7 Y K →
    Work.FTS.PhiStar.F0 6 (C * K) (Work.FTS.PhiStar.Yblk Y) := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound
  obtain ⟨A, hApos, hAb⟩ := Work.FTS.PhiStar.CoreAux.exists_bound_of_five hMpos hM
  refine ⟨7 * (32 * A + 1), by positivity, ?_⟩
  intro K Y hK hsm hflat
  have hA0 : 0 ≤ A := hApos.le
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  -- the two families of slots of `Y` which the estimate consumes
  have hYp : Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hflat
  have hD : ∀ (m i : ℕ), i ≤ 6 → m + i ≤ 7 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i Y) z θ|
        ≤ (32 * A + 1) * K :=
    fun m i hi6 hmi z θ hz hθ hθ' => flat_mixed_le hA0 hK hAb hsm hflat hi6 hmi hz hθ hθ'
  intro k i hki z θ hz hθ hθ'
  have hk6 : k ≤ 6 := by omega
  have hi6 : i ≤ 6 := by omega
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  -- commutation and the product rule
  have hcomm := Work.FTS.PhiStar.CoreAux.DthIter_Dz_comm_smoothOpen hsm i
  have hexp := Work.FTS.PhiStar.CoreAux.pzIter_zpz_expand
    (A := Work.Spaces.DthIter i (Work.FTS.PhiStar.Yblk Y))
    (B := Work.Spaces.DthIter i Y) hcomm (hsm.DthIter i) k z θ hz hθ hθ'
  rw [hexp]
  -- the two bounded pieces
  have hb1 : |(z + 1) ^ (k + 1) * Work.Spaces.pzIter (k + 1)
      (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K :=
    hD (k + 1) i hi6 (by omega) z θ hz hθ hθ'
  have hb2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ|
      ≤ (32 * A + 1) * K := hD k i hi6 (by omega) z θ hz hθ hθ'
  have hzx : |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1)
      (Work.Spaces.DthIter i Y) z θ| ≤ (32 * A + 1) * K := by
    have hzk : (0 : ℝ) ≤ z := hz.le
    have hpowk : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
    calc |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ|
        = (z + 1) ^ k * z
            * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz1.le k), abs_of_nonneg hzk]
      _ ≤ (z + 1) ^ (k + 1)
            * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [pow_succ]
          nlinarith [hpowk]
      _ = |(z + 1) ^ (k + 1) * Work.Spaces.pzIter (k + 1)
            (Work.Spaces.DthIter i Y) z θ| := by
          rw [abs_mul, abs_of_pos (pow_pos hz1 (k + 1))]
      _ ≤ (32 * A + 1) * K := hb1
  have hky : |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k
      (Work.Spaces.DthIter i Y) z θ)| ≤ (k : ℝ) * ((32 * A + 1) * K) := by
    calc |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)|
        = (k : ℝ) * |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ| := by
          rw [show (z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)
                = (k : ℝ) * ((z + 1) ^ k
                    * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ) from by ring,
              abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ (k : ℝ) * ((32 * A + 1) * K) :=
          mul_le_mul_of_nonneg_left hb2 (Nat.cast_nonneg k)
  have hre : (z + 1) ^ k * (z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ
        + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)
      = ((z + 1) ^ k * z) * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ
        + (z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ) := by
    ring
  rw [hre]
  refine le_trans (abs_add_le _ _) ?_
  have hkR : (k : ℝ) ≤ 6 := by exact_mod_cast hk6
  have hA0K : (0 : ℝ) ≤ (32 * A + 1) * K := mul_nonneg (by linarith) hK
  have hfin : (32 * A + 1) * K + (k : ℝ) * ((32 * A + 1) * K) ≤ 7 * ((32 * A + 1) * K) := by
    have := mul_le_mul_of_nonneg_right hkR hA0K
    linarith
  calc |(z + 1) ^ k * z * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i Y) z θ|
        + |(z + 1) ^ k * ((k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i Y) z θ)|
      ≤ (32 * A + 1) * K + (k : ℝ) * ((32 * A + 1) * K) := add_le_add hzx hky
    _ ≤ 7 * ((32 * A + 1) * K) := hfin
    _ = (7 * (32 * A + 1)) * K := by ring

end Work.FTS.StrongPersist.SP6
