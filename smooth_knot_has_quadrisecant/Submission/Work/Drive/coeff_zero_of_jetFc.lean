import Mathlib
import Submission.Work.Drive.jetDefs

/-!
# Vanishing of the Fourier combination forces trivially zero coefficients

If the complex sequence `k ↦ (α + ikβ) zᵏ + (γ + ikδ) yᵏ + (ε + ikζ) xᵏ` vanishes for the nine
consecutive integers `k = -4, …, 4`, and `z, y, x` are nonzero and pairwise distinct, then all six
real coefficients vanish.  The proof applies the difference operator `g ↦ (k ↦ g (k+1) - r g k)`
three times (which produces `A zᵏ + B yᵏ + C xᵏ` with `A = β z (z-y) (z-x)` and similar `B`, `C`)
and then differentiates twice more, eliminating the three coefficients one at a time.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The forward difference operator with shift `r`. -/
def diffOp (r : ℂ) (g : ℤ → ℂ) : ℤ → ℂ := fun k => g (k + 1) - r * g k

theorem diffOp_add (r : ℂ) (g h : ℤ → ℂ) : diffOp r (g + h) = diffOp r g + diffOp r h := by
  funext k
  simp only [diffOp, Pi.add_apply]
  ring

/-- `diffOp` applied to an affine-in-`k` exponential. -/
theorem diffOp_affine_pow_apply (c d w r : ℂ) (hw : w ≠ 0) (k : ℤ) :
    diffOp r (fun m => (c + ((m : ℤ) : ℂ) * d) * w ^ m) k
      = (((w - r) * c + w * d) + ((k : ℤ) : ℂ) * ((w - r) * d)) * w ^ k := by
  simp only [diffOp]
  rw [zpow_add_one₀ hw]
  have hk : (((k + 1 : ℤ)) : ℂ) = ((k : ℤ) : ℂ) + 1 := by push_cast; ring
  rw [hk]
  ring

/-- The function-level form of `diffOp_affine_pow_apply`. -/
theorem diffOp_affine_pow (c d w : ℂ) (hw : w ≠ 0) (r : ℂ) :
    diffOp r (fun m => (c + ((m : ℤ) : ℂ) * d) * w ^ m)
      = fun m => (((w - r) * c + w * d) + ((m : ℤ) : ℂ) * ((w - r) * d)) * w ^ m := by
  funext k
  exact diffOp_affine_pow_apply c d w r hw k

/-- Three successive differences of an affine-in-`k` exponential. -/
theorem diffOp3_family (c d w u v s : ℂ) (hw : w ≠ 0) :
    diffOp s (diffOp v (diffOp u (fun m => (c + ((m : ℤ) : ℂ) * d) * w ^ m)))
      = fun m => (((w - s) * ((w - v) * ((w - u) * c + w * d) + w * ((w - u) * d))
            + w * ((w - v) * ((w - u) * d)))
          + ((m : ℤ) : ℂ) * ((w - s) * ((w - v) * ((w - u) * d)))) * w ^ m := by
  rw [diffOp_affine_pow c d w hw u]
  rw [diffOp_affine_pow ((w - u) * c + w * d) ((w - u) * d) w hw v]
  rw [diffOp_affine_pow ((w - v) * ((w - u) * c + w * d) + w * ((w - u) * d))
        ((w - v) * ((w - u) * d)) w hw s]

/-- Differences of a sum of three exponentials. -/
theorem diffOp_sum_pow_apply (A B C a b c r : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (k : ℤ) :
    diffOp r (fun m => A * a ^ m + B * b ^ m + C * c ^ m) k
      = A * (a - r) * a ^ k + B * (b - r) * b ^ k + C * (c - r) * c ^ k := by
  simp only [diffOp]
  rw [zpow_add_one₀ ha, zpow_add_one₀ hb, zpow_add_one₀ hc]
  ring

/-- The function-level form of `diffOp_sum_pow_apply`. -/
theorem diffOp_sum_pow (A B C a b c r : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    diffOp r (fun m => A * a ^ m + B * b ^ m + C * c ^ m)
      = fun m => A * (a - r) * a ^ m + B * (b - r) * b ^ m + C * (c - r) * c ^ m := by
  funext k
  exact diffOp_sum_pow_apply A B C a b c r ha hb hc k

/-- Differences of a sum of two exponentials. -/
theorem diffOp_sum_pow_two_apply (A B a b r : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (k : ℤ) :
    diffOp r (fun m => A * a ^ m + B * b ^ m) k = A * (a - r) * a ^ k + B * (b - r) * b ^ k := by
  simp only [diffOp]
  rw [zpow_add_one₀ ha, zpow_add_one₀ hb]
  ring

theorem diffOp_eq_zero (r : ℂ) (g : ℤ → ℂ) (k : ℤ) (h1 : g (k + 1) = 0) (h0 : g k = 0) :
    diffOp r g k = 0 := by
  simp only [diffOp, h1, h0]
  ring

theorem diffOp2_eq_zero (r₁ r₂ : ℂ) (g : ℤ → ℂ) (k : ℤ) (h2 : g (k + 2) = 0)
    (h1 : g (k + 1) = 0) (h0 : g k = 0) : diffOp r₁ (diffOp r₂ g) k = 0 := by
  have h2' : g ((k + 1) + 1) = 0 := by
    rw [show (k + 1) + 1 = k + 2 from by ring]; exact h2
  simp only [diffOp, h0, h1, h2']
  ring

theorem diffOp3_eq_zero (s v u : ℂ) (g : ℤ → ℂ) (k : ℤ) (h3 : g (k + 3) = 0)
    (h2 : g (k + 2) = 0) (h1 : g (k + 1) = 0) (h0 : g k = 0) :
    diffOp s (diffOp v (diffOp u g)) k = 0 := by
  have h2' : g ((k + 1) + 1) = 0 := by
    rw [show (k + 1) + 1 = k + 2 from by ring]; exact h2
  have h3' : g (((k + 1) + 1) + 1) = 0 := by
    rw [show ((k + 1) + 1) + 1 = k + 3 from by ring]; exact h3
  simp only [diffOp, h0, h1, h2', h3']
  ring

/-- The `z`-coefficient produced by the triple difference. -/
def jetTripleA (z y x : ℂ) (β : ℝ) : ℂ := z * (z - y) * (z - x) * (Complex.I * (β : ℂ))

/-- The `y`-coefficient produced by the triple difference. -/
def jetTripleB (z y x : ℂ) (δ : ℝ) : ℂ := y * (y - z) * (y - x) * (Complex.I * (δ : ℂ))

/-- The `x`-coefficient produced by the triple difference. -/
def jetTripleC (z y x : ℂ) (ζ : ℝ) : ℂ := x * (x - z) * (x - y) * (Complex.I * (ζ : ℂ))

/-- **Vanishing of the Fourier combination.** -/
theorem coeff_zero_of_jetFc (z y x : ℂ) (hz : z ≠ 0) (hy : y ≠ 0) (hx : x ≠ 0)
    (hzy : z ≠ y) (hzx : z ≠ x) (hyx : y ≠ x) (α β γ δ ε ζ : ℝ)
    (h : ∀ k : ℤ, -4 ≤ k → k ≤ 4 → jetFc z y x α β γ δ ε ζ k = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 ∧ ε = 0 ∧ ζ = 0 := by
  set F : ℤ → ℂ := fun k => ((α : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (β : ℂ))) * z ^ k
      + ((γ : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (δ : ℂ))) * y ^ k
      + ((ε : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (ζ : ℂ))) * x ^ k with hF
  have hFapp : ∀ k, F k = ((α : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (β : ℂ))) * z ^ k
      + ((γ : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (δ : ℂ))) * y ^ k
      + ((ε : ℂ) + ((k : ℤ) : ℂ) * (Complex.I * (ζ : ℂ))) * x ^ k := by
    intro k; rw [hF]
  have hFeq : ∀ k, jetFc z y x α β γ δ ε ζ k = F k := by
    intro k
    rw [hFapp k]
    simp only [jetFc]
    ring
  have hzero : ∀ k : ℤ, -4 ≤ k → k ≤ 4 → F k = 0 := by
    intro k h1 h2
    rw [← hFeq k]
    exact h k h1 h2
  set A : ℂ := jetTripleA z y x β with hA
  set B : ℂ := jetTripleB z y x δ with hB
  set C : ℂ := jetTripleC z y x ζ with hC
  -- the triple difference of `F`
  have hkey : ∀ k : ℤ, diffOp z (diffOp y (diffOp x F)) k = A * z ^ k + B * y ^ k + C * x ^ k := by
    have hfam_z := diffOp3_family (α : ℂ) (Complex.I * (β : ℂ)) z x y z hz
    have hfam_y := diffOp3_family (γ : ℂ) (Complex.I * (δ : ℂ)) y x y z hy
    have hfam_x := diffOp3_family (ε : ℂ) (Complex.I * (ζ : ℂ)) x x y z hx
    have hFsum : F = (fun m : ℤ => ((α : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (β : ℂ))) * z ^ m)
        + (fun m : ℤ => ((γ : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (δ : ℂ))) * y ^ m)
        + (fun m : ℤ => ((ε : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (ζ : ℂ))) * x ^ m) := by
      funext m
      rw [hFapp m]
      simp only [Pi.add_apply]
    intro k
    rw [hA, hB, hC, jetTripleA, jetTripleB, jetTripleC]
    have hsum : diffOp z (diffOp y (diffOp x F))
        = diffOp z (diffOp y (diffOp x
              (fun m : ℤ => ((α : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (β : ℂ))) * z ^ m)))
          + diffOp z (diffOp y (diffOp x
              (fun m : ℤ => ((γ : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (δ : ℂ))) * y ^ m)))
          + diffOp z (diffOp y (diffOp x
              (fun m : ℤ => ((ε : ℂ) + ((m : ℤ) : ℂ) * (Complex.I * (ζ : ℂ))) * x ^ m))) := by
      rw [hFsum]
      simp only [diffOp_add]
    rw [hsum, hfam_z, hfam_y, hfam_x]
    simp only [Pi.add_apply]
    ring
  -- `A zᵏ + B yᵏ + C xᵏ` vanishes on `-4 … 1`
  have hG : ∀ k : ℤ, -4 ≤ k → k ≤ 1 → A * z ^ k + B * y ^ k + C * x ^ k = 0 := by
    intro k h1 h2
    have h0 : diffOp z (diffOp y (diffOp x F)) k = 0 :=
      diffOp3_eq_zero z y x F k (hzero (k + 3) (by omega) (by omega))
        (hzero (k + 2) (by omega) (by omega)) (hzero (k + 1) (by omega) (by omega))
        (hzero k h1 (by omega))
    rw [hkey k] at h0
    exact h0
  -- second difference of `G` and the elimination of `A`
  have hdouble : ∀ k : ℤ, diffOp y (diffOp x (fun m => A * z ^ m + B * y ^ m + C * x ^ m)) k
      = A * (z - x) * (z - y) * z ^ k := by
    have h2 := diffOp_sum_pow A B C z y x x hz hy hx
    have h3 := diffOp_sum_pow (A * (z - x)) (B * (y - x)) (C * (x - x)) z y x y hz hy hx
    intro k
    rw [h2, h3]
    ring
  have hA0 : A = 0 := by
    have h0 : diffOp y (diffOp x (fun m => A * z ^ m + B * y ^ m + C * x ^ m)) (-1) = 0 :=
      diffOp2_eq_zero y x _ (-1) (by simpa using hG 1 (by norm_num) (by norm_num))
        (by simpa using hG 0 (by norm_num) (by norm_num))
        (by simpa using hG (-1) (by norm_num) (by norm_num))
    rw [hdouble (-1), zpow_neg_one] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 (sub_ne_zero.mpr hzx)
      · exact absurd h2 (sub_ne_zero.mpr hzy)
    · exact absurd h (inv_ne_zero hz)
  -- elimination of `B` and `C`
  have hBC_vanish : ∀ k : ℤ, -4 ≤ k → k ≤ 1 → B * y ^ k + C * x ^ k = 0 := by
    intro k h1 h2
    have h0 := hG k h1 h2
    rw [hA0] at h0
    simpa using h0
  have hsingleB : ∀ k : ℤ, diffOp x (fun m => B * y ^ m + C * x ^ m) k = B * (y - x) * y ^ k := by
    intro k
    rw [diffOp_sum_pow_two_apply B C y x x hy hx k]
    ring
  have hB0 : B = 0 := by
    have h0 : diffOp x (fun m => B * y ^ m + C * x ^ m) 0 = 0 :=
      diffOp_eq_zero x _ 0 (by simpa using hBC_vanish 1 (by norm_num) (by norm_num))
        (by simpa using hBC_vanish 0 (by norm_num) (by norm_num))
    rw [hsingleB 0, zpow_zero, mul_one] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hyx)
  have hC0 : C = 0 := by
    have h0 := hG 0 (by norm_num) (by norm_num)
    rw [hA0, hB0] at h0
    simpa using h0
  -- the three coefficients of the triple difference
  have hβ : β = 0 := by
    have h1 : z * (z - y) * (z - x) * (Complex.I * (β : ℂ)) = 0 := by
      have h0 := hA0
      rw [hA, jetTripleA] at h0
      exact h0
    have h3 : z * (z - y) * (z - x) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hzy)) (sub_ne_zero.mpr hzx)
    have h2 : Complex.I * (β : ℂ) = 0 := (mul_eq_zero.mp h1).resolve_left h3
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h Complex.I_ne_zero
    · exact Complex.ofReal_eq_zero.mp h
  have hδ : δ = 0 := by
    have h1 : y * (y - z) * (y - x) * (Complex.I * (δ : ℂ)) = 0 := by
      have h0 := hB0
      rw [hB, jetTripleB] at h0
      exact h0
    have h3 : y * (y - z) * (y - x) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hy (sub_ne_zero.mpr (Ne.symm hzy))) (sub_ne_zero.mpr hyx)
    have h2 : Complex.I * (δ : ℂ) = 0 := (mul_eq_zero.mp h1).resolve_left h3
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h Complex.I_ne_zero
    · exact Complex.ofReal_eq_zero.mp h
  have hζ : ζ = 0 := by
    have h1 : x * (x - z) * (x - y) * (Complex.I * (ζ : ℂ)) = 0 := by
      have h0 := hC0
      rw [hC, jetTripleC] at h0
      exact h0
    have h3 : x * (x - z) * (x - y) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx (sub_ne_zero.mpr (Ne.symm hzx))) (sub_ne_zero.mpr (Ne.symm hyx))
    have h2 : Complex.I * (ζ : ℂ) = 0 := (mul_eq_zero.mp h1).resolve_left h3
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h Complex.I_ne_zero
    · exact Complex.ofReal_eq_zero.mp h
  -- now only `α, γ, ε` survive
  have hFβ : ∀ k : ℤ, F k = (α : ℂ) * z ^ k + (γ : ℂ) * y ^ k + (ε : ℂ) * x ^ k := by
    intro k
    rw [hFapp k, hβ, hδ, hζ]
    simp
  have hG2 : ∀ k : ℤ, -4 ≤ k → k ≤ 4 → (α : ℂ) * z ^ k + (γ : ℂ) * y ^ k + (ε : ℂ) * x ^ k = 0 := by
    intro k h1 h2
    rw [← hFβ k]
    exact hzero k h1 h2
  have hdouble2 : ∀ k : ℤ,
      diffOp y (diffOp x (fun m => (α : ℂ) * z ^ m + (γ : ℂ) * y ^ m + (ε : ℂ) * x ^ m)) k
        = (α : ℂ) * (z - x) * (z - y) * z ^ k := by
    have h2 := diffOp_sum_pow (α : ℂ) (γ : ℂ) (ε : ℂ) z y x x hz hy hx
    have h3 := diffOp_sum_pow ((α : ℂ) * (z - x)) ((γ : ℂ) * (y - x)) ((ε : ℂ) * (x - x))
      z y x y hz hy hx
    intro k
    rw [h2, h3]
    ring
  have hα : α = 0 := by
    have h0 : diffOp y (diffOp x (fun m => (α : ℂ) * z ^ m + (γ : ℂ) * y ^ m + (ε : ℂ) * x ^ m)) 0
        = 0 :=
      diffOp2_eq_zero y x _ 0 (by simpa using hG2 2 (by norm_num) (by norm_num))
        (by simpa using hG2 1 (by norm_num) (by norm_num))
        (by simpa using hG2 0 (by norm_num) (by norm_num))
    rw [hdouble2 0, zpow_zero, mul_one] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · exact Complex.ofReal_eq_zero.mp h2
      · exact absurd h2 (sub_ne_zero.mpr hzx)
    · exact absurd h (sub_ne_zero.mpr hzy)
  have hG3 : ∀ k : ℤ, -4 ≤ k → k ≤ 4 → (γ : ℂ) * y ^ k + (ε : ℂ) * x ^ k = 0 := by
    intro k h1 h2
    have h0 := hG2 k h1 h2
    rw [hα] at h0
    simpa using h0
  have hsingleG : ∀ k : ℤ, diffOp x (fun m => (γ : ℂ) * y ^ m + (ε : ℂ) * x ^ m) k
      = (γ : ℂ) * (y - x) * y ^ k := by
    intro k
    rw [diffOp_sum_pow_two_apply (γ : ℂ) (ε : ℂ) y x x hy hx k]
    ring
  have hγ : γ = 0 := by
    have h0 : diffOp x (fun m => (γ : ℂ) * y ^ m + (ε : ℂ) * x ^ m) 0 = 0 :=
      diffOp_eq_zero x _ 0 (by simpa using hG3 1 (by norm_num) (by norm_num))
        (by simpa using hG3 0 (by norm_num) (by norm_num))
    rw [hsingleG 0, zpow_zero, mul_one] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact Complex.ofReal_eq_zero.mp h
    · exact absurd h (sub_ne_zero.mpr hyx)
  have hε : ε = 0 := by
    have h0 := hG3 0 (by norm_num) (by norm_num)
    rw [hγ, zpow_zero, zpow_zero] at h0
    simpa using h0
  exact ⟨hα, hβ, hγ, hδ, hε, hζ⟩

end

end Work.Drive
