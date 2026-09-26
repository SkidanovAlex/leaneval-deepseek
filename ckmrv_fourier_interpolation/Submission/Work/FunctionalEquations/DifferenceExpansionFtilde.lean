import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DirichletExpansion

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# The Dirichlet expansion of the first difference of `F̃` (CKMRV Theorem 3.1)

The second difference equation (v) says that `F̃ (τ + 2) x - 2 F̃ (τ + 1) x + F̃ τ x = 0`,
so the first difference `τ ↦ F̃ (τ + 1) x - F̃ τ x` is periodic of period `1`.  By the
Poisson-summation functional equations this difference is a pure Dirichlet series with
frequencies `m ≥ 1` (the `m`-th term being `2 π i √(2m) b̃_m e^{2 π i m τ}` in the
notation of the paper, cf. (3.2)), and the coefficients are recovered by orthogonality
of the characters `e^{2 π i m t}` on `(0, 1)`.

The two ingredients used below are the generic `FtildeDiff_periodicStripBound` (a periodic function
controlled on one vertical strip of width `1` is controlled by a weight of the decay shape
needed by `DirichletExpansion`) and `FtildeDiff_dirichletExpansionIciOne` (`DirichletExpansion`
reindexed by the frequencies `m ≥ 1`).
-/

/-- The order isomorphism `ℕ ≃ {m : ℕ // 1 ≤ m}`, `k ↦ k + 1`, used to reindex a
Dirichlet series `∑_{k ≥ 0} c_k e^{2π i (k+1) τ}` by its frequencies `m = k + 1 ≥ 1`. -/
def FtildeDiff_natEquivIciOne : ℕ ≃ Set.Ici (1 : ℕ) where
  toFun k := ⟨k + 1, by simp⟩
  invFun m := m.1 - 1
  left_inv k := by simp
  right_inv m := by
    ext
    simp [Nat.sub_add_cancel m.2]

/-- **A periodic strip bound produces a weight.**  Let `h` be periodic of period `1` on the
upper half plane and bounded by `α y ^ (-β)` (with `α ≥ 0`, `β > 0`) on the strip
`-1 ≤ Re τ ≤ 0`.  Then `h` is bounded by the weight `y ↦ α y ^ (-β)`, which is of the
polynomial decay shape required by `DirichletExpansion`. -/
theorem FtildeDiff_periodicStripBound {h : ℂ → ℂ} (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 < β)
    (hper : ∀ τ : ℂ, 0 < τ.im → h (τ + 1) = h τ)
    (hstrip : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 0 → ‖h τ‖ ≤ α * τ.im ^ (-β)) :
    ∃ M : ℝ → ℝ,
      (∀ τ : ℂ, 0 < τ.im → ‖h τ‖ ≤ M τ.im) ∧
      (∃ A c : ℝ, 0 ≤ A ∧ 0 ≤ c ∧ ∀ y : ℝ, 0 < y → M y ≤ A * y ^ (-c)) ∧
      (∀ m : ℕ, Tendsto (fun y : ℝ =>
        M y * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0)) := by
  -- extend `h` to a globally `1`-periodic function
  set H : ℂ → ℂ := fun z => if 0 < z.im then h z else 0 with hH
  have Hper : Function.Periodic H 1 := by
    intro z
    rw [hH]
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [hz, hz1, if_true]
      exact hper z hz
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [hz, hz1, if_false]
  -- shift by an arbitrary integer
  have hshift : ∀ (k : ℤ) (τ : ℂ), 0 < τ.im → h (τ + k) = h τ := by
    intro k τ hτ
    have hHk : H (τ + k) = H τ := by
      have h1 := Hper.int_mul k τ
      simpa using h1
    have him : 0 < (τ + k).im := by
      simp only [Complex.add_im, Complex.intCast_im, add_zero]
      exact hτ
    have h2 : H (τ + k) = h (τ + k) := by rw [hH]; exact if_pos him
    have h3 : H τ = h τ := by rw [hH]; exact if_pos hτ
    rw [← h2, ← h3]
    exact hHk
  refine ⟨fun y => α * y ^ (-β), ?_, ?_, ?_⟩
  · intro τ hτ
    -- shift `τ` so that its real part lies in `[-1, 0]`
    set k : ℤ := -⌊τ.re⌋ - 1 with hk
    have hfl : ((⌊τ.re⌋ : ℤ) : ℝ) ≤ τ.re := Int.floor_le τ.re
    have hfl' : τ.re < ((⌊τ.re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one τ.re
    have hlow : -1 ≤ (τ + k).re := by
      simp only [Complex.add_re, Complex.intCast_re, hk]
      push_cast
      linarith
    have hup : (τ + k).re ≤ 0 := by
      simp only [Complex.add_re, Complex.intCast_re, hk]
      push_cast
      linarith
    have him : 0 < (τ + k).im := by
      simp only [Complex.add_im, Complex.intCast_im, add_zero]
      exact hτ
    calc ‖h τ‖ = ‖h (τ + k)‖ := (congrArg norm (hshift k τ hτ)).symm
      _ ≤ α * (τ + k).im ^ (-β) := hstrip (τ + k) him hlow hup
      _ = α * τ.im ^ (-β) := by rw [Complex.add_im, Complex.intCast_im, add_zero]
  · exact ⟨α, β, hα, le_of_lt hβ, fun _ _ => le_refl _⟩
  · intro m
    have hexp : ∀ y : ℝ, Real.exp (-(2 * Real.pi) * y) ^ m
        = Real.exp (-(2 * Real.pi * (m : ℝ)) * y) := by
      intro y
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h := (tendsto_rpow_neg_atTop hβ).const_mul α
      simpa using h
    · have hb : 0 < 2 * Real.pi * (m : ℝ) := by
        have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        positivity
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β)
        (2 * Real.pi * (m : ℝ)) hb
      have h4 : (fun y : ℝ => α * y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m)
          = (fun y : ℝ => α * (y ^ (-β) * Real.exp (-(2 * Real.pi * (m : ℝ)) * y))) := by
        funext y
        rw [hexp y]
        ring
      rw [h4]
      simpa using h.const_mul α

/-- **`DirichletExpansion` indexed by the positive frequencies.**  A holomorphic `1`-periodic
function on the upper half plane with a polynomial weight as in `DirichletExpansion` has an
absolutely convergent Dirichlet expansion with frequencies `m ≥ 1`,
`h τ = ∑_{m ≥ 1} c_m e^{2 π i m τ}`, and the coefficients are the contour integrals along
any horizontal line `Im = y`, `y > 0`. -/
theorem FtildeDiff_dirichletExpansionIciOne (h : ℂ → ℂ)
    (hper : ∀ τ : ℂ, 0 < τ.im → h (τ + 1) = h τ)
    (hhol : DifferentiableOn ℂ h {τ : ℂ | 0 < τ.im})
    (M : ℝ → ℝ) (hM : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ ≤ M τ.im)
    (hMbound : ∃ A β : ℝ, 0 ≤ A ∧ 0 ≤ β ∧ ∀ y : ℝ, 0 < y → M y ≤ A * y ^ (-β))
    (hMdecay : ∀ m : ℕ, Tendsto (fun y : ℝ =>
      M y * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0)) :
    ∃ c : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
        c m * dirichletTerm m.1 τ) (h τ)) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y → c m = ∫ t in (0 : ℝ)..1,
        h ((t : ℂ) + (y : ℂ) * Complex.I) * Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨c, hc1, hc2⟩ := DirichletExpansion h hper hhol M hM hMbound hMdecay
  refine ⟨fun m => c (m.1 - 1), ?_, ?_⟩
  · intro τ hτ
    have hmain := hc1 τ hτ
    have hcomp : HasSum ((fun m : Set.Ici (1 : ℕ) =>
        c (m.1 - 1) * dirichletTerm m.1 τ) ∘ FtildeDiff_natEquivIciOne) (h τ) := by
      refine hmain.congr_fun ?_
      intro k
      simp only [Function.comp_apply, FtildeDiff_natEquivIciOne, Equiv.coe_fn_mk,
        Nat.add_sub_cancel, dirichletTerm]
      push_cast
      ring_nf
    exact (Equiv.hasSum_iff FtildeDiff_natEquivIciOne).mp hcomp
  · intro m y hy
    change c (m.1 - 1) = ∫ t in (0 : ℝ)..1,
      h ((t : ℂ) + (y : ℂ) * Complex.I) * Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((t : ℂ) + (y : ℂ) * Complex.I)))
    rw [hc2 (m.1 - 1) y hy]
    have hcast : ((m.1 - 1 : ℕ) : ℂ) + 1 = (m.1 : ℂ) := by
      rw [Nat.cast_sub (R := ℂ) (m := 1) (n := m.1) m.2]
      push_cast
      ring
    rw [hcast]

/-- **Dirichlet expansion of the first difference of `F̃`** (CKMRV Theorem 3.1, cf. (3.2)).
For a solution `S` of the functional equations and any `x`, the periodic function
`τ ↦ F̃ (τ + 1) x - F̃ τ x` is a Dirichlet series with frequencies `m ≥ 1` on the upper half
plane, and its coefficients are the Fourier coefficients of the values on any horizontal
line `Im = y`, `y > 0`. -/
theorem DifferenceExpansionFtilde {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) :
    ∃ c : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          c m * Work.FE.dirichletTerm m.1 τ)
        (S.Ftilde (τ + 1) x - S.Ftilde τ x)) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        c m = ∫ t in (0 : ℝ)..1, (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
            - S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα, hβ, hunif⟩ := S.uniform_Ftilde
  -- the difference is periodic of period `1` (second difference equation)
  have hper : ∀ τ : ℂ, 0 < τ.im →
      (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) (τ + 1)
        = (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) τ := by
    intro τ hτ
    change S.Ftilde (τ + 1 + 1) x - S.Ftilde (τ + 1) x = S.Ftilde (τ + 1) x - S.Ftilde τ x
    have h2 : τ + 1 + 1 = τ + 2 := by ring
    rw [h2]
    have hr := S.recur_Ftilde τ x hτ
    linear_combination hr
  -- strip bound for the difference, from the uniform bound for `F̃`
  have hstrip : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 0 →
      ‖(fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) τ‖ ≤ (2 * α) * τ.im ^ (-β) := by
    intro τ hτ h1 h2
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    have hre1 : -1 ≤ (τ + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hre2 : (τ + 1).re ≤ 1 := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hb1 := hunif (τ + 1) x hτ1 hre1 hre2
    have hb0 := hunif τ x hτ h1 (by linarith)
    have him1 : (τ + 1).im = τ.im := by simp
    rw [him1] at hb1
    calc ‖S.Ftilde (τ + 1) x - S.Ftilde τ x‖
        ≤ ‖S.Ftilde (τ + 1) x‖ + ‖S.Ftilde τ x‖ := norm_sub_le _ _
      _ ≤ α * τ.im ^ (-β) + α * τ.im ^ (-β) := add_le_add hb1 hb0
      _ = (2 * α) * τ.im ^ (-β) := by ring
  obtain ⟨M, hM, hMbound, hMdecay⟩ :=
    FtildeDiff_periodicStripBound (2 * α) β (by linarith) hβ hper hstrip
  have hhol : DifferentiableOn ℂ
      (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) {τ : ℂ | 0 < τ.im} := by
    have hmaps : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
      intro τ hτ
      simpa using hτ
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
      (S.holomorphic_Ftilde x).comp (differentiableOn_id.add_const (1 : ℂ)) hmaps
    exact h1.sub (S.holomorphic_Ftilde x)
  obtain ⟨c, hc1, hc2⟩ := FtildeDiff_dirichletExpansionIciOne
    (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) hper hhol M hM hMbound hMdecay
  exact ⟨c, hc1, hc2⟩

end

end Work.FunctionalEquations
