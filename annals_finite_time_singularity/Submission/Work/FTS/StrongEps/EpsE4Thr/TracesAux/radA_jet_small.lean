import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radA_jet_small` — the `z → 0⁺` jet bound for the radial transfer profile

The radial profile of the transfer defect is

  `radA α x z = −ampA α z · L₁₂ x (z) + (ampB α z / c α) · L₁₂(Transport x)(0)`

(`Transfer.radA`).  This file proves that, for `x` of the class `ClassC α`, `α ∈ (0,1]`, whose
angular moments satisfy `Qang x k z = O(z^{3/2})` near `0` (`k ≤ 3`) and whose `(z∂_z)`-jets of
`ampA α` decay like `z/(1+z)²` at the origin,

  `|D_z^b (radA α x) z| ≤ K·z²`  for `0 < z < 1`, `b ≤ 4`.

This is the small-`z` half of the radial trace hypotheses consumed by
`TracesAux.BdryTraces_Gam_mul_rad` (whose `hr0` needs `z·(D_z^b r·w)² → 0` at `0⁺`); with
`w = (1+z)²/z²` it follows at once from `z·K²z⁴·(1+z)⁴/z³ ≤ 16K²z → 0`.  The large-`z` half
(`≤ K/z` for `z ≥ 1`) is the sibling statement `radA_jet_big`.

## The proof

* **Expansion.**  `RadBound.radA_dzdIter_expansion_open` splits `radA` into the product
  `ampA α · L₁₂ x` and the constant multiple of `ampB α` and applies the Leibniz rule for
  `D_z = z∂_z` at order `q ≤ 4`; its two differentiability inputs come from
  `RadBound.L12f_iter_regular_open` (regularity of `L₁₂ x` on `(0,∞)`, from `SmoothOpen x` and
  `HkMem α 4 x`) and `RadBound.diffDzd_ampA_mul_L12f_open`.
* **The two factors.**  `D_z^{q−b}(L₁₂ x) = O(z^{3/2})` near the origin
  (`EpsE4Thr.DzdIter_L12f_small`, from the hypothesis `hQ`), while `D_z^b(ampA α) = O(z/(1+z)²)
  = O(z)` (`hA`); their product is `O(z^{5/2}) ⊆ O(z²)` for `z ≤ 1`.  The remaining summand is
  `D_z^q(ampB α) = O(z²/(1+z)³) = O(z²)` (`EpsE4Thr.DzdIter_ampB_bdd`) times the constant
  `L₁₂(Transport x)(0)/c α`.
* **The coefficients.**  `Σ_{b≤q} C(q,b)·K_b ≤ 6·Σ_{b≤4}K_b` for `q ≤ 4` (helper
  `sum_choose_mul_le_six`), so a single constant `6·Σ_{b≤4}K_b·D + |L₁₂(Transport x)(0)/c α|·DB
  + 1` works for all four orders.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

set_option maxHeartbeats 2000000

/-- The binomial-coefficient arithmetic of the Leibniz sum: for `q ≤ 4` and nonnegative
weights `K`, `Σ_{b≤q} C(q,b)·K b ≤ 6·(K 0 + K 1 + K 2 + K 3 + K 4)`. -/
private lemma sum_choose_mul_le_six {K : ℕ → ℝ} (hK : ∀ b, 0 ≤ K b) {q : ℕ} (hq : q ≤ 4) :
    (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * K b)
      ≤ 6 * (K 0 + K 1 + K 2 + K 3 + K 4) := by
  interval_cases q <;> norm_num [Nat.choose, Finset.sum_range_succ] <;>
    nlinarith [hK 0, hK 1, hK 2, hK 3, hK 4]

theorem radA_jet_small {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2))
    (hA : ∀ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z| ≤ K * z ^ 2 := by
  -- the jet bound of `L₁₂ x` near the origin (`O(z^{3/2})`) and of `ampB α` (`O(z²/(1+z)³)`)
  obtain ⟨D, hDnn, hDb⟩ := Work.FTS.StrongEps.EpsE4Thr.DzdIter_L12f_small hα hx hC hQ
  obtain ⟨DB, hDBnn, hDBb⟩ := Work.FTS.StrongEps.EpsE4Thr.DzdIter_ampB_bdd α
  -- the jet bounds of `ampA α`, one constant per order
  choose KA hKA using hA
  -- regularity inputs of the Leibniz expansion
  have hmem : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hx.reg 4 (by norm_num) hx.mem
  obtain ⟨_, hL12diff⟩ :=
    Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open α hα.1 hα.2 x hx.reg hmem hx.l12
  have hAdiff :=
    Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open α hα.1 hα.2 x hL12diff
  have hexp :=
    Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open α hα.1 hα.2 x hL12diff hAdiff
  have hKa : ∀ b, 0 ≤ KA b := fun b => (hKA b).1
  have hKall : (0 : ℝ) ≤ 6 * (KA 0 + KA 1 + KA 2 + KA 3 + KA 4) * D
      + |Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α| * DB + 1 := by
    have h0 := hKa 0
    have h1 := hKa 1
    have h2 := hKa 2
    have h3 := hKa 3
    have h4 := hKa 4
    positivity
  refine ⟨_, hKall, ?_⟩
  intro q hq z hz0 hz1
  rw [hexp q hq z hz0]
  -- `|D_z^b (ampA α) z| ≤ KA b·(z/(1+z)²) ≤ KA b·z` on `z > 0`
  have hA0 : ∀ b : ℕ, b ≤ 4 →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA b * z := by
    intro b hb
    have hb' := (hKA b).2 z hz0
    have hle : z / (1 + z) ^ 2 ≤ z := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [hz0.le, sq_nonneg z]
      have h2 : z * 1 ≤ z * (1 + z) ^ 2 := mul_le_mul_of_nonneg_left h1 hz0.le
      simpa using h2
    exact hb'.trans (mul_le_mul_of_nonneg_left hle (hKa b))
  -- `|D_z^m (L₁₂ x) z| ≤ D·z^{3/2}` near the origin, in the `Coercivity` vocabulary
  have hL0 : ∀ m : ℕ, m ≤ 4 →
      |Work.Elliptic.DzdIter m (Work.Coercivity.L12f x) z| ≤ D * z ^ ((3 : ℝ) / 2) := by
    intro m hm
    rw [Work.FTS.StrongEps.EpsE4Thr.L12f_eq_elliptic x]
    exact hDb m hm z hz0 hz1
  have hXnn : (0 : ℝ) ≤ D * (z * z ^ ((3 : ℝ) / 2)) :=
    mul_nonneg hDnn (mul_nonneg hz0.le (Real.rpow_nonneg hz0.le _))
  -- the per-term bound of the Leibniz sum
  have hterm : ∀ b ∈ Finset.range (q + 1),
      |(q.choose b : ℝ) * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f x) z|
        ≤ ((q.choose b : ℝ) * KA b) * (D * (z * z ^ ((3 : ℝ) / 2))) := by
    intro b hb
    have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := le_trans hbq hq
    have hqb4 : q - b ≤ 4 := by omega
    have hcb : (0 : ℝ) ≤ (q.choose b : ℝ) := Nat.cast_nonneg _
    calc |(q.choose b : ℝ) * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f x) z|
        = ((q.choose b : ℝ)
              * |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|)
            * |Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f x) z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcb]
      _ ≤ ((q.choose b : ℝ) * (KA b * z)) * (D * z ^ ((3 : ℝ) / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hA0 b hb4) hcb) (hL0 (q - b) hqb4)
            (abs_nonneg _) (mul_nonneg hcb (mul_nonneg (hKa b) hz0.le))
      _ = ((q.choose b : ℝ) * KA b) * (D * (z * z ^ ((3 : ℝ) / 2))) := by ring
  have hsum : |∑ b ∈ Finset.range (q + 1),
      (q.choose b : ℝ) * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f x) z|
      ≤ 6 * (KA 0 + KA 1 + KA 2 + KA 3 + KA 4) * (D * (z * z ^ ((3 : ℝ) / 2))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_choose_mul_le_six hKa hq) hXnn
  -- the `ampB` summand, a constant times `D_z^q (ampB α) = O(z²)`
  have hB : |Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α
        * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z|
      ≤ (|Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α| * DB)
          * z ^ 2 := by
    rw [abs_mul]
    have hb := hDBb q hq z hz0.le
    have hleB : DB * z ^ 2 / (1 + z) ^ 3 ≤ DB * z ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (1 + z) ^ 3 := by nlinarith [hz0.le, sq_nonneg z]
      have h2 : DB * z ^ 2 * 1 ≤ DB * z ^ 2 * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hDBnn (sq_nonneg z))
      simpa using h2
    calc |Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α|
          * |Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z|
        ≤ |Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α|
            * (DB * z ^ 2 / (1 + z) ^ 3) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α|
            * (DB * z ^ 2) := mul_le_mul_of_nonneg_left hleB (abs_nonneg _)
      _ = (|Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α| * DB)
            * z ^ 2 := by ring
  -- `z·z^{3/2} = z^{5/2} ≤ z²` on `0 < z < 1`
  have hstep : z * z ^ ((3 : ℝ) / 2) ≤ z ^ 2 := by
    have h1 : z ^ ((3 : ℝ) / 2) ≤ z := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hz0, Real.rpow_one]
      have h2 : z ^ ((1 : ℝ) / 2) ≤ 1 := by
        have h3 := Real.rpow_le_rpow hz0.le hz1.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rwa [Real.one_rpow] at h3
      nlinarith [hz0.le, h2]
    have h3 := mul_le_mul_of_nonneg_left h1 hz0.le
    rwa [← pow_two] at h3
  have hSD : (0 : ℝ) ≤ 6 * (KA 0 + KA 1 + KA 2 + KA 3 + KA 4) * D := by
    have h0 := hKa 0
    have h1 := hKa 1
    have h2 := hKa 2
    have h3 := hKa 3
    have h4 := hKa 4
    positivity
  have hmid : |-(∑ b ∈ Finset.range (q + 1),
        (q.choose b : ℝ) * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f x) z)
      + Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α
          * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z|
      ≤ 6 * (KA 0 + KA 1 + KA 2 + KA 3 + KA 4) * (D * (z * z ^ ((3 : ℝ) / 2)))
        + (|Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α| * DB)
            * z ^ 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    exact add_le_add hsum hB
  refine hmid.trans ?_
  have hkey := mul_le_mul_of_nonneg_left hstep hSD
  nlinarith [hkey, sq_nonneg z]

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
