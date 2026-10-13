/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound on the mixed-slot remainder `EM`

`EM α f g` is the mixed-slot remainder of the `SpecialTransport` pairing: the sum of the
products `D_z^b D_θ^a f · D_z^{j-b} D_θ^{i-a}(∂_θ g) · D_z^j D_θ^i g · w² / sin(2θ)^γ`
with `i ≥ 1`, `i + j ≤ 4`, `a + b ≥ 1` (the `"all derivatives on g"` terms being removed).

The estimate is the paper's: the `f`-factor carries `sin(2θ)` (`abs_mixed_f_le`), which
converts `D_θ^d(∂_θ g)` into the `D_θ^{d+1} g` slot (`sigma_z_bound`), so that Cauchy–Schwarz
in the form `|A·B| ≤ (A² + B²)/2` against the squares occurring in `HkIntegrand α 4 g`
closes the estimate.  The numerical constant is very far from sharp.

The proof is assembled from three separate pieces:

* `abs_mixed_f_unif` (below): `|D_z^b D_θ^a f| ≤ 4·10^5 sin(2θ)|∂_θ f|_{𝒲^{4,∞}}` for
  `a + b ≤ 4`, obtained from the two existing barriers `abs_mixed_f_le` (`a ≥ 1`) and
  `abs_DzIter_f_le` (`a = 0`);
* `Work.FTS.H2.EMB.EM_gside` (`Submission/Work/FTS/H2/EMB/EM_gside.lean`): the `g`-side
  pairing `sin(2θ)|D_z^c D_θ^d ∂_θ g| · |D_z^j D_θ^i g| · w²/sin(2θ)^γ ≤ 187(d+1) HkIntegrand`,
  by `sigma_z_bound` followed by `gam_pair_le` on each of the `≤ d + 1` slots;
* `Work.FTS.H2.EMB.EM_term_le` (`Submission/Work/FTS/H2/EMB/EM_term_le.lean`): the bound of
  one summand of `EM`, combining the two pieces above.

What is left here, and is the actual assembly, is the summation: at most `(i+1)·(j+1)`
summands in each `(i,j)`-block, weighted by the binomial coefficients, so that each block
contributes `≤ 2^i·2^j·(4·10^5·935)|∂_θ f|_𝒲 · HkIntegrand`, and the `(i,j)`-blocks with
`i ≥ 1`, `i + j ≤ 4` give a total of `31·31·4·10^5·935 = 359414000000 ≤ 10^12`.

**Note on `π`.**  The statement below is the one that was requested, verbatim.  `π` is
Mathlib's notation for `Real.pi`, which lives in the `Real` scope; the `open scoped Real`
line is what makes the bare `π` mean `Real.pi` (without it, `π` would be auto-bound as an
extra free implicit variable, and the resulting statement is false).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STEasyBnd
import Submission.Work.FTS.H2.EMB.EM_gside
import Submission.Work.FTS.H2.EMB.EM_term_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2

set_option maxHeartbeats 4000000

/-- Every mixed derivative of `f` of total order at most `4` is bounded by
`4·10^5 · sin(2θ) · |∂_θ f|_{𝒲^{4,∞}}` on the open strip.  (`abs_mixed_f_le` for `a ≥ 1`,
`abs_DzIter_f_le` for `a = 0`.) -/
theorem abs_mixed_f_unif {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ a b : ℕ, a + b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.mixed b a f z θ|
        ≤ 400000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro a b hab z hz θ hθ
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have hb4 : b ≤ 4 := by omega
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have h1 := abs_DzIter_f_le hsm hcont hvt hWl b hb4 z hz θ hθIθ
    have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
      Work.Spaces.WlInf_nonneg α 4 _ hWl
    have h2 : |Work.Spaces.mixed b 0 f z θ| = |Work.Spaces.DzIter b f z θ| := rfl
    rw [h2]
    nlinarith [h1, mul_nonneg hS hWnn]
  · exact abs_mixed_f_le' hsm hcont hvt hα hα1 hWl a b (by omega) hab z hz θ hθ

theorem EMBound {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hg : Work.Spaces.SmoothNbhd g) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.H2.EM α f g z θ|
      ≤ 1000000000000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  set W : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.pth f) with hWdef
  set Hk : ℝ := Work.Spaces.HkIntegrand α 4 g z θ with hHkdef
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  have hWnn : 0 ≤ W := by
    rw [hWdef]; exact Work.Spaces.WlInf_nonneg α 4 _ hWl
  have hHknn : 0 ≤ Hk := by
    rw [hHkdef]; exact Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  -- the `f`-side bound
  have hf : ∀ a b : ℕ, a + b ≤ 4 →
      |Work.Spaces.mixed b a f z θ| ≤ 400000 * Real.sin (2 * θ) * W := by
    intro a b hab
    rw [hWdef]
    exact abs_mixed_f_unif hsm hcont hvt hα hα1 hWl a b hab z hz θ hθ
  -- the `g`-side pairing bound
  have hgs : ∀ c d i j : ℕ, 1 ≤ i → i + j ≤ 4 → d ≤ 3 → d + 1 + c ≤ 4 →
      Real.sin (2 * θ) * |Work.Spaces.mixed c d (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ 187 * ((d + 1 : ℕ) : ℝ) * Hk := by
    intro c d i j hi hij hd hdc
    rw [hHkdef]
    exact Work.FTS.H2.EMB.EM_gside hα hg hHk hz hθ hi hij hd hdc
  -- the per-term bound
  have hterm : ∀ i j a b : ℕ, 1 ≤ i → i + j ≤ 4 → a ≤ i → b ≤ j →
      |(if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
          else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
        (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
          * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
        ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * (400000 * 935 * W * Hk) :=
    fun i j a b hi hij ha hb => Work.FTS.H2.EMB.EM_term_le hS hWnn hHknn hf hgs hi hij ha hb
  rw [EM]
  set C : ℝ := 400000 * 935 * W * Hk with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  -- each `(i,j)`-block
  have houter : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      |(if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
              (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
                * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        else 0)| ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j * C := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _) ?_
      have hbb : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
          |(if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
              (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
                * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * C := by
        intro a ha b hb
        have hai : a ≤ i := by
          have := Finset.mem_range.mp ha; omega
        have hbj : b ≤ j := by
          have := Finset.mem_range.mp hb; omega
        rw [hCdef]
        exact hterm i j a b hc.1 hc.2 hai hbj
      refine le_trans (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hbb a ha b hb) ?_
      have hsplit : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ)) * C)
          = (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ))
            * (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) * C := by
        have h1 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ)) * C)
            = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                ((i.choose a : ℕ) : ℝ) * ((j.choose b : ℕ) : ℝ)) * C := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
        rw [h1, Finset.sum_mul_sum]
      have h2i : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) = (2 : ℝ) ^ i := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      have h2j : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      rw [hsplit, h2i, h2j]
    · rw [if_neg hc, abs_zero]
      positivity
  -- the outer double sum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ i ∈ Finset.range 5, |∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
              (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
                * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        else 0)|
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, |(if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
              else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
              (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
                * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        else 0)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (2 : ℝ) ^ i * (2 : ℝ) ^ j * C :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => houter i hi j hj
    _ = (∑ i ∈ Finset.range 5, (2 : ℝ) ^ i) * (∑ j ∈ Finset.range 5, (2 : ℝ) ^ j) * C := by
        have e2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (2 : ℝ) ^ i * (2 : ℝ) ^ j)
            = (∑ i ∈ Finset.range 5, (2 : ℝ) ^ i) * (∑ j ∈ Finset.range 5, (2 : ℝ) ^ j) :=
          (Finset.sum_mul_sum (Finset.range 5) (Finset.range 5) (fun i => (2 : ℝ) ^ i)
            (fun j => (2 : ℝ) ^ j)).symm
        rw [← e2, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ = 31 * 31 * C := by norm_num [Finset.sum_range_succ]
    _ ≤ 1000000000000 * W * Hk := by
        rw [hCdef] at *
        nlinarith [mul_nonneg hWnn hHknn]

end Work.FTS.H2
