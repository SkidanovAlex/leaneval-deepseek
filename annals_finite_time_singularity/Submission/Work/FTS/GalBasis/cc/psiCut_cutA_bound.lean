/-
# `Work.FTS.GalBasis.cc.psiCut_cutA_bound` — uniform `D_z`-jet bounds for the radial step

The radial step of the cutoff family of `Work.FTS.GalBasis.cc.CutDefs` is

  `cutA N z = 𝕋 (((N:ℝ)+1)·z − 1) · 𝕋 (2 − z/((N:ℝ)+1))`     (`𝕋 = Real.smoothTransition`),

the product of a step of mesh `1/(N+1)` at the bottom of the half-line and a step of *reciprocal*
mesh `(N+1)` at the top.  The statement proved here is that the scale-invariant operators
`D_z = z ∂_z` of the paper act on `cutA N` with bounds that are **uniform in `N`**: there is a
single constant `K` with `|D_z^j (cutA N)| ≤ K` for all `N`, all `j ≤ 4` and all `(z,θ)`.

The mechanism is the usual one for such steps.  For a function of one variable `F` we have, in the
rescaled variable `w = n z + a`,

  `z ∂_z (F (n · + a)) = (n z) F' (n z + a) = (w − a) F' (w)`,

so the operator `z ∂_z` becomes `ρ ∂_ρ` with `ρ(w) = w − a`: an operator whose coefficients are
*uniformly bounded* on the layer `w ∈ [1,2]` where `𝕋 (w − 1)` varies (and which vanishes outside
it, since `𝕋` is constant off `(0,1)`).  This is why the two factors of `cutA N` have
`N`-independent `D_z`-jets, and it is the content of the two "weighted derivative bounds"
`exists_weighted_smoothTransition_bound` below.

The `D_z`-jets of the *product* are then bounded with the Stirling expansion of the one-variable
operator `DzIterZ` (`Work.FTS.LocData.DzIterZ_eq_sum_scoef`) and the binomial (Leibniz) expansion
of `iteratedDeriv` of a product (Mathlib's `iteratedDeriv_mul`); the numerical factor is
`bell 4 ≤ 100` (`Work.Spaces.bell_le`).

## Contents

* `abs_smoothTransition_le_one`, `iteratedDeriv_smoothTransition_eq_zero_of_{lt_zero,one_lt}` —
  elementary facts about `𝕋` (bounded by `1`, and *constant* off `(0,1)`, so all its positive
  iterated derivatives vanish there);
* `exists_weighted_smoothTransition_bound c` — for every shift `c` there is `A` with
  `|(u−c)^a ∂^a 𝕋 u| ≤ A a` for all `a`, `u` (the sup over `u ∈ [0,1]`, plus the vanishing off
  `(0,1)`);
* `iteratedDeriv_comp_mul_add` — the affine chain rule
  `∂^a (F (λ · + a₀)) z = λ^a ∂^a F (λ z + a₀)`;
* `dzIterZ_pair_bound` — the `N`-independent bound for a product of two rescaled steps;
* `cutA_dzIterZ_bound` — the same for `DzIterZ j (cutA N)`;
* `psiCut_cutA_bound` — the requested statement.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.PsiCutAux
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "𝕋" => Real.smoothTransition

/-! ## 1. Elementary facts about the smooth step -/

/-- The smooth step takes its values in `[0,1]`. -/
theorem abs_smoothTransition_le_one (u : ℝ) : |𝕋 u| ≤ 1 := by
  rcases le_or_gt u 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, abs_zero]; norm_num
  rcases le_or_gt 1 u with h1 | h1
  · rw [Real.smoothTransition.one_of_one_le h1, abs_one]
  · have h0 : 0 ≤ 𝕋 u := by
      rw [← Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
      exact Real.smoothTransition.monotone (le_of_lt h)
    rw [abs_of_nonneg h0]
    calc 𝕋 u ≤ 𝕋 1 := Real.smoothTransition.monotone (le_of_lt h1)
      _ = 1 := Real.smoothTransition.one_of_one_le le_rfl

/-- `∂^a` of a constant function vanishes in positive order. -/
theorem iteratedDeriv_const_eq_zero {c : ℝ} {a : ℕ} (ha : a ≠ 0) (x : ℝ) :
    iteratedDeriv a (fun _ : ℝ => c) x = 0 := by
  rw [iteratedDeriv_const, if_neg ha]

/-- `𝕋` is (locally) constantly `0` to the left of `0`, so all its derivatives vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_lt_zero {u : ℝ} (hu : u < 0) (a : ℕ) :
    iteratedDeriv a 𝕋 u = 0 := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [iteratedDeriv_zero, Real.smoothTransition.zero_of_nonpos (le_of_lt hu)]
  · have hev : 𝕋 =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hev.iteratedDeriv_eq a,
      iteratedDeriv_const_eq_zero (Nat.pos_iff_ne_zero.mp hpos)]

/-- `𝕋` is (locally) constantly `1` to the right of `1`, so all its derivatives of positive order
vanish there. -/
theorem iteratedDeriv_smoothTransition_eq_zero_of_one_lt {u : ℝ} (hu : 1 < u) {a : ℕ}
    (ha : a ≠ 0) : iteratedDeriv a 𝕋 u = 0 := by
  have hev : 𝕋 =ᶠ[𝓝 u] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [hev.iteratedDeriv_eq a, iteratedDeriv_const_eq_zero ha]

/-! ## 2. Weighted derivative bounds for the smooth step -/

/-- **The weighted derivatives of the smooth step are bounded**, uniformly in the shift `c`.
There is `A : ℕ → ℝ` with `1 ≤ A a` and `|(u − c)^a · ∂^a 𝕋 u| ≤ A a` for all `a` and all `u`.

On `u ∈ [0,1]` this is the compactness of the (continuous) function
`u ↦ (u − c)^a ∂^a 𝕋 u`; off `[0,1]` the step is locally constant, so all the derivatives with
`a ≥ 1` vanish (`iteratedDeriv_smoothTransition_eq_zero_of_*`), while for `a = 0` the bound is
`|𝕋 u| ≤ 1` (`abs_smoothTransition_le_one`). -/
theorem exists_weighted_smoothTransition_bound (c : ℝ) :
    ∃ A : ℕ → ℝ, (∀ a : ℕ, 1 ≤ A a) ∧ ∀ (a : ℕ) (u : ℝ),
      |(u - c) ^ a * iteratedDeriv a 𝕋 u| ≤ A a := by
  have h : ∀ a : ℕ, ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |(u - c) ^ a * iteratedDeriv a 𝕋 u| ≤ C := by
    intro a
    have hcont : Continuous (fun u : ℝ => (u - c) ^ a * iteratedDeriv a 𝕋 u) :=
      ((continuous_id.sub continuous_const).pow a).mul
        ((contDiff_smoothTransition a).continuous_iteratedDeriv a (by simp))
    have hc : ContinuousOn (fun u : ℝ => (u - c) ^ a * iteratedDeriv a 𝕋 u)
        (Set.Icc (0 : ℝ) 1) := hcont.continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact ⟨C, fun u hu => by simpa only [Real.norm_eq_abs] using hC u hu⟩
  choose A hA using h
  have hApos : ∀ a : ℕ, 0 ≤ max (A a) 1 := fun a => le_trans zero_le_one (le_max_right (A a) 1)
  refine ⟨fun a => max (A a) 1, ?_, fun a u => ?_⟩
  · intro a; exact le_max_right (A a) 1
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [pow_zero, one_mul, iteratedDeriv_zero]
    exact le_trans (abs_smoothTransition_le_one u) (le_max_right (A 0) 1)
  · by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
    · exact le_trans (hA a u hu) (le_max_left (A a) 1)
    · have hane : a ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hu' : ¬(0 ≤ u ∧ u ≤ 1) := by simpa only [Set.mem_Icc] using hu
      rcases lt_or_ge u 0 with hlt | hge
      · rw [iteratedDeriv_smoothTransition_eq_zero_of_lt_zero hlt a, mul_zero, abs_zero]
        exact hApos a
      · have hgt : 1 < u := lt_of_not_ge fun h => hu' ⟨hge, h⟩
        rw [iteratedDeriv_smoothTransition_eq_zero_of_one_lt hgt hane, mul_zero, abs_zero]
        exact hApos a

/-! ## 3. The affine chain rule for `iteratedDeriv` -/

/-- **Iterated derivative of an affine substitution.**  For a smooth `F`,
`∂^a (F (λ · + a₀)) z = λ^a · ∂^a F (λ z + a₀)`: differentiating `F (λ ·)` `a` times pulls out `a`
factors of `λ` (Mathlib's `iteratedDeriv_comp_const_mul`), and the translation does not change the
iterated derivative (`iteratedDeriv_comp_add_const`). -/
theorem iteratedDeriv_comp_mul_add (F : ℝ → ℝ) (hF : ∀ m : ℕ, ContDiff ℝ m F)
    (lam a₀ : ℝ) (a : ℕ) (z : ℝ) :
    iteratedDeriv a (fun z : ℝ => F (lam * z + a₀)) z
      = lam ^ a * iteratedDeriv a F (lam * z + a₀) := by
  have hG : ContDiff ℝ (a : WithTop ℕ∞) (fun y : ℝ => F (y + a₀)) :=
    (hF a).comp (contDiff_id.add contDiff_const)
  have h1 : iteratedDeriv a (fun z : ℝ => (fun y : ℝ => F (y + a₀)) (lam * z)) z
      = lam ^ a * iteratedDeriv a (fun y : ℝ => F (y + a₀)) (lam * z) :=
    congrFun (iteratedDeriv_comp_const_mul (f := fun y : ℝ => F (y + a₀)) hG lam) z
  have h2 : iteratedDeriv a (fun y : ℝ => F (y + a₀)) (lam * z)
      = iteratedDeriv a F (lam * z + a₀) :=
    congrFun (iteratedDeriv_comp_add_const a F a₀) (lam * z)
  have hfun : (fun z : ℝ => F (lam * z + a₀))
      = (fun z : ℝ => (fun y : ℝ => F (y + a₀)) (lam * z)) := rfl
  rw [hfun, h1, h2]

/-! ## 4. The bound for a product of two rescaled steps -/

/-- **The `D_z`-jets of a product of two rescaled smooth steps are bounded**, uniformly in the
two scales `n`, `lam`.

Writing `F₁ z = 𝕋 (n z − 1)`, `F₂ z = 𝕋 (lam z + 2)`, the weighted derivative of the first factor
is `z^a ∂^a F₁ z = (n z)^a ∂^a 𝕋 (n z − 1)`, bounded by `A a` (`hAb` with `u = n z − 1`), and
that of the second is `z^b ∂^b F₂ z = (lam z)^b ∂^b 𝕋 (lam z + 2)`, bounded by `B b` (`hBb` with
`v = lam z + 2`).

The Stirling expansion `DzIterZ j = ∑_{k≤j} S(j,k) z^k ∂^k` (`DzIterZ_eq_sum_scoef`) reduces the
`D_z`-jet to the weighted *plain* derivatives `z^k ∂^k (F₁ F₂)`, which the binomial rule
(`iteratedDeriv_mul`) splits into the products `(z^a ∂^a F₁)(z^{k−a} ∂^{k−a} F₂)`; the binomial
coefficient is at most `2^k ≤ 16`, and the Stirling factor contributes `bell j ≤ 100`. -/
theorem dzIterZ_pair_bound (A B : ℕ → ℝ) (hA1 : ∀ a : ℕ, 1 ≤ A a) (hB1 : ∀ b : ℕ, 1 ≤ B b)
    (hAb : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a)
    (hBb : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n lam : ℝ) (j : ℕ), j ≤ 4 → ∀ z : ℝ,
      |Work.Coercivity.CommutZ.DzIterZ j
        (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) z| ≤ C := by
  have hAnn : ∀ a : ℕ, 0 ≤ A a := fun a => le_trans zero_le_one (hA1 a)
  have hBnn : ∀ b : ℕ, 0 ≤ B b := fun b => le_trans zero_le_one (hB1 b)
  let S : ℝ := ∑ da ∈ Finset.range 5, ∑ db ∈ Finset.range 5, 16 * A da * B db
  have hSnn : 0 ≤ S := by
    show 0 ≤ ∑ da ∈ Finset.range 5, ∑ db ∈ Finset.range 5, 16 * A da * B db
    exact Finset.sum_nonneg fun da _ => Finset.sum_nonneg fun db _ =>
      mul_nonneg (mul_nonneg (by norm_num) (hAnn da)) (hBnn db)
  have hbell4 : (0 : ℝ) ≤ ((Work.Spaces.bell 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKpos : 0 < 1 + 100 * S := by linarith
  refine ⟨1 + 100 * S, hKpos, fun n lam j hj z => ?_⟩
  have hsm1 : ∀ m : ℕ, ContDiff ℝ m (fun z : ℝ => 𝕋 (n * z + (-1))) := fun m =>
    (contDiff_smoothTransition m).comp
      (((contDiff_const : ContDiff ℝ m (fun _ : ℝ => n)).mul contDiff_id).add
        (contDiff_const : ContDiff ℝ m (fun _ : ℝ => (-1 : ℝ))))
  have hsm2 : ∀ m : ℕ, ContDiff ℝ m (fun z : ℝ => 𝕋 (lam * z + 2)) := fun m =>
    (contDiff_smoothTransition m).comp
      (((contDiff_const : ContDiff ℝ m (fun _ : ℝ => lam)).mul contDiff_id).add
        (contDiff_const : ContDiff ℝ m (fun _ : ℝ => (2 : ℝ))))
  have hchain1 : ∀ (a : ℕ) (w : ℝ), iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w
      = n ^ a * iteratedDeriv a 𝕋 (n * w + (-1)) :=
    fun a w => iteratedDeriv_comp_mul_add 𝕋 contDiff_smoothTransition n (-1) a w
  have hchain2 : ∀ (a : ℕ) (w : ℝ), iteratedDeriv a (fun z : ℝ => 𝕋 (lam * z + 2)) w
      = lam ^ a * iteratedDeriv a 𝕋 (lam * w + 2) :=
    fun a w => iteratedDeriv_comp_mul_add 𝕋 contDiff_smoothTransition lam 2 a w
  have hw1 : ∀ (a : ℕ) (w : ℝ),
      |w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w| ≤ A a := by
    intro a w
    rw [hchain1 a w]
    have hred : w ^ a * (n ^ a * iteratedDeriv a 𝕋 (n * w + (-1)))
        = (n * w + (-1) - (-1)) ^ a * iteratedDeriv a 𝕋 (n * w + (-1)) := by
      rw [← mul_assoc, ← mul_pow, show w * n = n * w + (-1) - (-1) by ring]
    rw [hred]
    exact hAb a (n * w + (-1))
  have hw2 : ∀ (a : ℕ) (w : ℝ),
      |w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (lam * z + 2)) w| ≤ B a := by
    intro a w
    rw [hchain2 a w]
    have hred : w ^ a * (lam ^ a * iteratedDeriv a 𝕋 (lam * w + 2))
        = (lam * w + 2 - 2) ^ a * iteratedDeriv a 𝕋 (lam * w + 2) := by
      rw [← mul_assoc, ← mul_pow, show w * lam = lam * w + 2 - 2 by ring]
    rw [hred]
    exact hBb a (lam * w + 2)
  have hch : ∀ (k a : ℕ), k ≤ 4 → |(((k.choose a : ℕ)) : ℝ)| ≤ 16 := by
    intro k a hk
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : k.choose a ≤ 2 ^ k := Nat.choose_le_two_pow k a
    have h2 : (2 : ℕ) ^ k ≤ 16 := by interval_cases k <;> norm_num
    exact_mod_cast le_trans h1 h2
  have hper : ∀ k : ℕ, k ≤ 4 → ∀ w : ℝ,
      |w ^ k * iteratedDeriv k (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) w| ≤ S := by
    intro k hk4 w
    have hkey : iteratedDeriv k (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) w
        = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
            * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w
            * iteratedDeriv (k - a) (fun z : ℝ => 𝕋 (lam * z + 2)) w :=
      iteratedDeriv_mul ((hsm1 k).contDiffAt) ((hsm2 k).contDiffAt)
    have hsplit : w ^ k * iteratedDeriv k
          (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) w
        = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
            * ((w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w)
              * (w ^ (k - a) * iteratedDeriv (k - a) (fun z : ℝ => 𝕋 (lam * z + 2)) w)) := by
      rw [hkey, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have hzk : w ^ a * w ^ (k - a) = w ^ k := by rw [← pow_add, Nat.add_sub_cancel' ha']
      rw [← hzk]
      ring
    calc |w ^ k * iteratedDeriv k (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) w|
        = |∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
            * ((w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w)
              * (w ^ (k - a) * iteratedDeriv (k - a) (fun z : ℝ => 𝕋 (lam * z + 2)) w))| := by
          rw [hsplit]
      _ ≤ ∑ a ∈ Finset.range (k + 1), 16 * A a * B (k - a) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a ha => ?_)
          have hXa : |w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w| ≤ A a := hw1 a w
          have hYb : |w ^ (k - a) * iteratedDeriv (k - a) (fun z : ℝ => 𝕋 (lam * z + 2)) w|
              ≤ B (k - a) := hw2 (k - a) w
          rw [abs_mul, abs_mul]
          calc |(((k.choose a : ℕ)) : ℝ)|
                * (|w ^ a * iteratedDeriv a (fun z : ℝ => 𝕋 (n * z + (-1))) w|
                  * |w ^ (k - a) * iteratedDeriv (k - a) (fun z : ℝ => 𝕋 (lam * z + 2)) w|)
              ≤ 16 * (A a * B (k - a)) :=
                mul_le_mul (hch k a hk4) (mul_le_mul hXa hYb (abs_nonneg _) (hAnn a))
                  (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                  (by norm_num : (0:ℝ) ≤ 16)
            _ = 16 * A a * B (k - a) := by ring
      _ ≤ S := by
          show (∑ a ∈ Finset.range (k + 1), 16 * A a * B (k - a))
            ≤ ∑ da ∈ Finset.range 5, ∑ db ∈ Finset.range 5, 16 * A da * B db
          have hs1 : (∑ a ∈ Finset.range (k + 1), 16 * A a * B (k - a))
              ≤ ∑ a ∈ Finset.range 5, 16 * A a * B (k - a) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro x hx
              simp only [Finset.mem_range] at hx ⊢
              omega
            · intro x _ _
              exact mul_nonneg (mul_nonneg (by norm_num) (hAnn x)) (hBnn (k - x))
          have hs2 : (∑ a ∈ Finset.range 5, 16 * A a * B (k - a))
              ≤ ∑ da ∈ Finset.range 5, ∑ db ∈ Finset.range 5, 16 * A da * B db := by
            refine Finset.sum_le_sum fun a ha => ?_
            simp only [Finset.mem_range] at ha
            refine Finset.single_le_sum
              (fun b _ => mul_nonneg (mul_nonneg (by norm_num) (hAnn a)) (hBnn b)) ?_
            simp only [Finset.mem_range]
            omega
          exact le_trans hs1 hs2
  have hTtop : ContDiff ℝ Work.Stability.smoothOrder 𝕋 := Real.smoothTransition.contDiff
  have hlin1 : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => n * z + (-1)) :=
    (((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => n)).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (-1 : ℝ))))
  have hlin2 : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => lam * z + 2) :=
    (((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => lam)).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (2 : ℝ))))
  have hsmcut : ContDiff ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) :=
    (hTtop.comp hlin1).mul (hTtop.comp hlin2)
  have hstir := congrFun (Work.FTS.LocData.DzIterZ_eq_sum_scoef
    (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) hsmcut j) z
  rw [hstir]
  have hb := Work.Spaces.abs_sum_scoef_mul_le j S
    (fun k : ℕ => z ^ k * iteratedDeriv k (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) z)
    (fun k hk => hper k (le_trans hk hj) z)
  have hbell : ((Work.Spaces.bell j : ℕ) : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le j hj
  calc |∑ k ∈ Finset.range (j + 1), ((Work.Spaces.scoef j k : ℕ) : ℝ)
        * (z ^ k * iteratedDeriv k (fun z : ℝ => 𝕋 (n * z + (-1)) * 𝕋 (lam * z + 2)) z)|
      ≤ ((Work.Spaces.bell j : ℕ) : ℝ) * S := hb
    _ ≤ 100 * S := by nlinarith [hbell, hSnn]
    _ ≤ 1 + 100 * S := by linarith

/-! ## 5. `cutA` -/

/-- `D_z`-iterates of a `θ`-independent function are the one-variable iterates `DzIterZ`. -/
theorem DzIter_mulZ_eq (j : ℕ) (m : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => m z') z θ
      = Work.Coercivity.CommutZ.DzIterZ j m z := by
  have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ j m) z) θ
  exact h

/-- **The stated bound in the one-variable form**: the `D_z`-jets of `cutA N`, up to order `4`,
are bounded uniformly in `N`. -/
theorem cutA_dzIterZ_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (N j : ℕ), j ≤ 4 → ∀ z : ℝ,
      |Work.Coercivity.CommutZ.DzIterZ j (cutA N) z| ≤ K := by
  obtain ⟨A, hA1, hAb⟩ := exists_weighted_smoothTransition_bound (-1)
  obtain ⟨B, hB1, hBb⟩ := exists_weighted_smoothTransition_bound 2
  obtain ⟨C, hCpos, hC⟩ := dzIterZ_pair_bound A B hA1 hB1 hAb hBb
  refine ⟨C, hCpos, fun N j hj z => ?_⟩
  have hfact : cutA N = fun z : ℝ =>
      𝕋 (((N : ℝ) + 1) * z + (-1)) * 𝕋 ((-(1 / ((N : ℝ) + 1))) * z + 2) := by
    funext z
    simp only [cutA]
    have h1 : ((N : ℝ) + 1) * z - 1 = ((N : ℝ) + 1) * z + (-1) := by ring
    have h2 : 2 - z / ((N : ℝ) + 1) = (-(1 / ((N : ℝ) + 1))) * z + 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
      ring
    rw [h1, h2]
  rw [hfact]
  exact hC ((N : ℝ) + 1) (-(1 / ((N : ℝ) + 1))) j hj z

/-! ## 6. The requested statement -/

/-- **The `D_z`-jets of the radial step `cutA N` are bounded, uniformly in `N`, up to order `4`.**
This is the radial half of the uniform-derivative bound of the density lemma
(`Work.FTS.GalBasis.cc.psiCut_spec`). -/
theorem psiCut_cutA_bound : ∃ K : ℝ, 0 < K ∧ ∀ (N j : ℕ), j ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.DzIter j (fun z' (_ : ℝ) => cutA N z') z θ| ≤ K := by
  obtain ⟨K, hK, hb⟩ := cutA_dzIterZ_bound
  refine ⟨K, hK, fun N j hj z θ => ?_⟩
  rw [DzIter_mulZ_eq j (cutA N) z θ]
  exact hb N j hj z

end Work.FTS.GalBasis.cc
