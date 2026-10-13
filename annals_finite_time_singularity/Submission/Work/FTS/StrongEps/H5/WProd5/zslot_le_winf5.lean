import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.H5.WProd5.Gmaj5
import Submission.Work.FTS.StrongEps.H5.WProd5.Pointwise5
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.WProd5

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The binomial coefficients of the rows `0 ≤ n ≤ 5` are at most `16` (for `n ≤ 4` because
`n.choose k ≤ 2^n ≤ 16`, and for `n = 5` by direct evaluation: the largest entry of the fifth
row is `5.choose 2 = 10`), hence their squares are at most `256`. -/
private theorem choose_sq_le_256_five (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 5) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 16 := by
    rcases Nat.lt_or_ge n 5 with h | h
    · have h2 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
      have h3 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
      omega
    · have hn5 : n = 5 := by omega
      subst hn5
      interval_cases k <;> decide
  have h1' : ((n.choose k : ℕ) : ℝ) ≤ 16 := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_self_le_mul_self h0 h1'
  rw [sq]
  norm_num at hm ⊢
  linarith [hm]

/-- **The radial `D_z`-slots of the level-`5` `𝒲^{5,∞}`-priced product rule.**

The literal `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.zslot_le_winf`
(`Submission/Work/FTS/OpenPkg/WProdWin/zslot_le_winf.lean`): the same proof with
`i ≤ 4 → i ≤ 5`, `WlInfMem α 4 → WlInfMem α 5`, `HkIntegrand α 4 → HkIntegrand α 5`, and the
`f`-factor bound taken from `Pointwise5.dzIter_le_WlInf5` (`|D_z^b f| ≤ 100 |f|_{𝒲^{5,∞}}`,
`b ≤ 5`) instead of `Work.FTS.OpenPkg.DzIter_le_WlInf_open`.  The binomial-coefficient bound
`Work.Spaces.choose_sq_le_256` is stated for `n ≤ 4`; at level `5` one needs the trivial
extension to `n ≤ 5` (`C(5,2) = 10`, so `10² = 100 ≤ 256`), which can be proved locally. -/
theorem zslot_le_winf5 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ i : ℕ, i ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 5 f := Work.Spaces.WlInf_nonneg α 5 f hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  -- the Leibniz expansion of `D_z^i (f·g)` in the open quadrant
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f g hf hg z θ hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  -- Cauchy-Schwarz for the finite sum
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
      * (Work.Spaces.DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- the per-term bound: the `f`-factor costs `100 |f|_𝒲`, the binomial coefficient costs `16`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 5 f :=
      dzIter_le_WlInf5 hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 5 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256_five i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 5 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 6 * Work.Spaces.HkIntegrand α 5 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 5 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 5 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 6 * Work.Spaces.HkIntegrand α 5 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : i + 1 ≤ 6)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
          * (6 * (6 * Work.Spaces.HkIntegrand α 5 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : i + 1 ≤ 6)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 5 f) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
              * (6 * (6 * Work.Spaces.HkIntegrand α 5 g z θ))
            = 92160000 * ((Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongEps.H5.WProd5
