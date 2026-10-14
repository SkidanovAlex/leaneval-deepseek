import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.H2.T1Q.SliceIntQ
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_jet_big =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-!
# `TracesAux.radA_jet_big` — the radial transfer profile decays like `1/z` at infinity

`radA α x z = −ampA α z·L₁₂ x(z) + (ampB α z/c α)·L₁₂(Transport x)(0)` with
`ampA α z = 2z/(c α (1+z)²)` and `ampB α z = 2z²/(1+z)³`.  Both profile coefficients are
`O(1/z)` for `z ≥ 1` (`z/(1+z)² ≤ 1/z` and `z²/(1+z)³ ≤ 1/z`), the `D_z`-jets of `ampA` obey
the hypothesis `hA`, and the `D_z`-jets of `L₁₂ x` of order `≤ 4` are bounded
(`EpsE4Thr.DzdIter_L12f_bdd`).  Hence every `D_z`-jet of `radA α x` of order `≤ 4` is `O(1/z)`
for `z ≥ 1`.

The Leibniz expansion of `D_z^q (radA α x)` is
`EpsRLX.RadBound.radA_dzdIter_expansion_open` (whose differentiability hypotheses are supplied
by `EpsRLX.RadBound.L12f_iter_regular_open` and `EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open`).
The per-term bounds `z/(1+z)² ≤ 1/z`, `z²/(1+z)³ ≤ 1/z` are proved here by cross-multiplication,
and the binomial sum is dominated by `∑_{b≤q} C(q,b) = 2^q ≤ 16` (`Nat.sum_range_choose`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

theorem radA_jet_big {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2))
    (hA : ∀ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 1 ≤ z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z| ≤ K / z := by
  have _ := hC
  have _ := hQ
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- `x` is `C^∞` on the open quadrant with `HkMem α 7`, hence with `HkMem α 4`
  have hmem4 : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hx.reg 4 (by norm_num) hx.mem
  -- the `D_z`-jets of `L₁₂ x` of order `≤ 3` are differentiable on `(0,∞)`
  have hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f x)) z :=
    (Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open α hα0 hα1 x hx.reg hmem4
      hx.l12).2
  -- and so are the jets of `ampA α · L₁₂ x`
  have hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun w : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α w
          * Work.Coercivity.L12f x w)) z :=
    Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open α hα0 hα1 x hL12diff
  -- the Leibniz expansion of the jets of `radA α x`
  have hexp := Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open
      α hα0 hα1 x hL12diff hAdiff
  -- a single constant dominating all the `ampA`-jets appearing (`b ≤ 4`)
  choose Ka hKa using hA
  have hKa0 : ∀ b : ℕ, 0 ≤ Ka b := fun b => (hKa b).1
  have hKab : ∀ (b : ℕ) (z : ℝ), 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ Ka b * (z / (1 + z) ^ 2) := fun b z hz => (hKa b).2 z hz
  set Km : ℝ := (Finset.Icc 0 4).sup' (Finset.nonempty_Icc.mpr (by norm_num)) Ka with hKm
  have hKle : ∀ b : ℕ, b ≤ 4 → Ka b ≤ Km := by
    intro b hb
    rw [hKm]
    exact Finset.le_sup' Ka (Finset.mem_Icc.mpr ⟨Nat.zero_le b, hb⟩)
  have hKm0 : 0 ≤ Km := le_trans (hKa0 0) (hKle 0 (by norm_num))
  have hKmb : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ Km * (z / (1 + z) ^ 2) := by
    intro b hb z hz
    refine (hKab b z hz).trans ?_
    exact mul_le_mul_of_nonneg_right (hKle b hb) (by positivity)
  -- the `D_z`-jets of `L₁₂ x` of order `≤ 4` are bounded
  obtain ⟨D, hD0, hDb⟩ := Work.FTS.StrongEps.EpsE4Thr.DzdIter_L12f_bdd hα hx
  have hDb' : ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter m (Work.Coercivity.L12f x) z| ≤ D := by
    intro m hm z hz
    rw [Work.FTS.StrongEps.EpsE4Thr.L12f_eq_elliptic x]
    exact hDb m hm z hz
  -- the `D_z`-jets of `ampB α` are `O(z²/(1+z)³)`
  obtain ⟨DB, hDB0, hDBb⟩ := Work.FTS.StrongEps.EpsE4Thr.DzdIter_ampB_bdd α
  have hDBb' : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
        ≤ DB * (z ^ 2 / (1 + z) ^ 3) := fun b hb z hz => by
    have h := hDBb b hb z hz
    rwa [mul_div_assoc] at h
  set T : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport x) 0 / Work.Spaces.c α with hT
  refine ⟨16 * Km * D + |T| * DB, by nlinarith [hKm0, hD0, hDB0, abs_nonneg T], ?_⟩
  intro b hb z hz1
  have hz0 : 0 < z := by linarith
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz0
  rw [hexp b hb z hzI]
  -- per-term bound in the binomial sum
  have hterm : ∀ i ∈ Finset.range (b + 1),
      |(b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
        ≤ (b.choose i : ℝ) * (Km * D) * (z / (1 + z) ^ 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hib : i ≤ 4 := by omega
    have hbi4 : b - i ≤ 4 := by omega
    have hci : (0 : ℝ) ≤ (b.choose i : ℝ) := Nat.cast_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg hci]
    have h1 := hKmb i hib z hz0
    have h2 := hDb' (b - i) hbi4 z hz0
    have h3 : |Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        * |Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
        ≤ (Km * (z / (1 + z) ^ 2)) * D :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc (b.choose i : ℝ) * |Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z|
          * |Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
        = (b.choose i : ℝ) * (|Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z|
          * |Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|) := by ring
      _ ≤ (b.choose i : ℝ) * ((Km * (z / (1 + z) ^ 2)) * D) :=
          mul_le_mul_of_nonneg_left h3 hci
      _ = (b.choose i : ℝ) * (Km * D) * (z / (1 + z) ^ 2) := by ring
  -- the whole binomial sum, bounded by `2^b ≤ 16`
  have h1 : |∑ i ∈ Finset.range (b + 1),
      (b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
      ≤ 16 * (Km * D) * (z / (1 + z) ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range (b + 1),
          |(b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
        ≤ ∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * (Km * D) * (z / (1 + z) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ b * (Km * D) * (z / (1 + z) ^ 2) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ 16 * (Km * D) * (z / (1 + z) ^ 2) := by
          have h2b : (2 : ℝ) ^ b ≤ 16 := by
            calc (2 : ℝ) ^ b ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
              _ = 16 := by norm_num
          have hzR : 0 ≤ (Km * D) * (z / (1 + z) ^ 2) :=
            mul_nonneg (mul_nonneg hKm0 hD0) (by positivity)
          have hle := mul_le_mul_of_nonneg_right h2b hzR
          calc (2 : ℝ) ^ b * (Km * D) * (z / (1 + z) ^ 2)
              = (2 : ℝ) ^ b * ((Km * D) * (z / (1 + z) ^ 2)) := by ring
            _ ≤ 16 * ((Km * D) * (z / (1 + z) ^ 2)) := hle
            _ = 16 * (Km * D) * (z / (1 + z) ^ 2) := by ring
  -- the second summand, `T · D_z^b (ampB α)`
  have h2 : |T * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
      ≤ |T| * DB * (z ^ 2 / (1 + z) ^ 3) := by
    rw [abs_mul]
    have h := hDBb' b hb z hz0.le
    calc |T| * |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
        ≤ |T| * (DB * (z ^ 2 / (1 + z) ^ 3)) := mul_le_mul_of_nonneg_left h (abs_nonneg T)
      _ = |T| * DB * (z ^ 2 / (1 + z) ^ 3) := by ring
  -- the two elementary decay estimates valid for `z ≥ 1`
  have hRz : z / (1 + z) ^ 2 ≤ 1 / z := by
    rw [div_le_div_iff₀ (by positivity) hz0]
    nlinarith
  have hTz : z ^ 2 / (1 + z) ^ 3 ≤ 1 / z := by
    rw [div_le_div_iff₀ (by positivity) hz0]
    nlinarith
  calc |-(∑ i ∈ Finset.range (b + 1),
        (b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z)
        + T * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
      ≤ |-(∑ i ∈ Finset.range (b + 1),
        (b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z)|
        + |T * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z| :=
        abs_add_le _ _
    _ = |∑ i ∈ Finset.range (b + 1),
        (b.choose i : ℝ) * Work.Elliptic.DzdIter i (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (b - i) (Work.Coercivity.L12f x) z|
        + |T * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z| :=
        by rw [abs_neg]
    _ ≤ 16 * (Km * D) * (z / (1 + z) ^ 2) + |T| * DB * (z ^ 2 / (1 + z) ^ 3) :=
        add_le_add h1 h2
    _ ≤ 16 * (Km * D) * (1 / z) + |T| * DB * (1 / z) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hRz (by nlinarith [hKm0, hD0])
        · exact mul_le_mul_of_nonneg_left hTz (by nlinarith [hDB0, abs_nonneg T])
    _ = (16 * Km * D + |T| * DB) / z := by rw [div_eq_mul_inv]; ring

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_jet_small =====
section

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
end
