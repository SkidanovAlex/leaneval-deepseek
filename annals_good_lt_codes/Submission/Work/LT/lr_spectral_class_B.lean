import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_class_ops
import Submission.Work.LT.lr_class_ROp_swap
import Submission.Work.LT.lr_class_split
import Submission.Work.LT.lr_class_dot_bound
import Submission.Work.LT.lr_mean_sub_zero
import Submission.Work.LT.lr_var_decomp

/-!
# Spectral gap of the label-class walk on the B-edges

`classOpA A` is the walk on `Fin 2 × G` which, from `(0,g)`, jumps to `(1, A i * g)` and from
`(1,g)` to `(0, (A i)⁻¹ * g)`, each with probability `1/Δ`.  Writing a function `s` on
`Fin 2 × G` as the pair of layer functions `u g = s (0,g)`, `v g = s (1,g)`:

* the quadratic form splits as `∑ g, u g * POp A v g + ∑ g, v g * ROp A u g`
  (`lr_class_split`), where `POp A` is the normalised left-averaging walk and `ROp A` its
  transpose (`lr_class_ROp_swap`);
* so it equals `2⟨u, POp A v⟩`, and subtracting the layer means `a`, `b` (with `a + b = 0`
  because the total sum of `s` vanishes) turns it into `2⟨u₀, POp A v₀⟩ + 2ab|G|`;
* `2⟨u₀, POp A v₀⟩ ≤ μ(‖u₀‖² + ‖v₀‖²)` is `lr_class_dot_bound`, applied to the mean-zero
  `v₀` with the contraction supplied by `leftExpander A μ`;
* the correction `2ab|G| = -2a²|G|` is at most `μ·2a²|G|` because `μ ≥ 0`, and
  `‖s‖² = ‖u₀‖² + ‖v₀‖² + (a²+b²)|G|` (`lr_var_decomp`).

Hence `⟨s, classOpA A s⟩ ≤ μ‖s‖²` for mean-zero `s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-- **Spectral gap of the two-layer walk, in coordinates.** If `u`, `v : G → ℝ` satisfy
`∑ u + ∑ v = 0`, then the quadratic form `∑ g, u g * POp A v g + ∑ g, v g * ROp A u g` of the
label-class walk is at most `μ (‖u‖² + ‖v‖²)` whenever `leftExpander A μ` holds and `μ ≥ 0`. -/
theorem lr_class_form_bound (A : Fin Δ → G) (μ : ℝ) (hA : leftExpander A μ) (hμ : 0 ≤ μ)
    (hΔ : (Δ : ℝ) ≠ 0) (u v : G → ℝ) (huv : (∑ g, u g) + (∑ g, v g) = 0) :
    (∑ g, u g * POp A v g) + (∑ g, v g * ROp A u g) ≤
      μ * ((∑ g, u g ^ 2) + ∑ g, v g ^ 2) := by
  have hswap : (∑ g, v g * ROp A u g) = ∑ g, u g * POp A v g := lr_class_ROp_swap A u v
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (∑ g, u g) / (Fintype.card G : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (∑ g, v g) / (Fintype.card G : ℝ) := ⟨_, rfl⟩
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast (ne_of_gt h)
  have hu0 : ∑ g, (u g - a) = 0 := by rw [ha]; exact lr_mean_sub_zero u
  have hv0 : ∑ g, (v g - b) = 0 := by rw [hb]; exact lr_mean_sub_zero v
  have hab : a + b = 0 := by rw [ha, hb, ← add_div, huv, zero_div]
  have hA1 : a * (Fintype.card G : ℝ) = ∑ g, u g := by rw [ha, div_mul_cancel₀ _ hcard]
  have hPv0sum : ∑ g, POp A (fun g => v g - b) g = 0 := by
    rw [POp_sum A (fun g => v g - b) hΔ]; exact hv0
  have hPv : ∀ g, POp A v g = POp A (fun g => v g - b) g + b := by
    intro g
    have hv_eq : v = fun g => (v g - b) + b := by funext g; ring
    conv_lhs => rw [hv_eq]
    rw [POp_add_const A (fun g => v g - b) b hΔ]
  -- `⟨u, POp A v⟩ = ⟨u₀, POp A v₀⟩ + a b |G|` with `u₀ = u - a`, `v₀ = v - b`.
  have h1 : (∑ g, u g * POp A v g) =
      (∑ g, (u g - a) * POp A (fun g => v g - b) g) + a * b * (Fintype.card G : ℝ) := by
    have hs1 : (∑ g, u g * POp A v g) = ∑ g, u g * (POp A (fun g => v g - b) g + b) :=
      Finset.sum_congr rfl (fun g _ => by rw [hPv g])
    rw [hs1]
    have hs2 : ∀ g ∈ (Finset.univ : Finset G), u g * (POp A (fun g => v g - b) g + b)
        = u g * POp A (fun g => v g - b) g + u g * b := fun g _ => by ring
    rw [Finset.sum_congr rfl hs2, Finset.sum_add_distrib]
    have hs3 : ∀ g ∈ (Finset.univ : Finset G), u g * POp A (fun g => v g - b) g
        = (u g - a) * POp A (fun g => v g - b) g + a * POp A (fun g => v g - b) g :=
      fun g _ => by ring
    rw [Finset.sum_congr rfl hs3, Finset.sum_add_distrib, ← Finset.mul_sum, hPv0sum, mul_zero,
      add_zero]
    rw [← Finset.sum_mul]
    rw [← hA1]
    ring
  have key1 : 2 * (∑ g, (u g - a) * POp A (fun g => v g - b) g) ≤
      μ * ((∑ g, (u g - a) ^ 2) + ∑ g, (v g - b) ^ 2) :=
    lr_class_dot_bound A μ hA hμ (fun g => u g - a) (fun g => v g - b) hv0
  have hu2 : ∑ g, u g ^ 2 = (∑ g, (u g - a) ^ 2) + a ^ 2 * (Fintype.card G : ℝ) := by
    rw [ha]; exact lr_var_decomp u
  have hv2 : ∑ g, v g ^ 2 = (∑ g, (v g - b) ^ 2) + b ^ 2 * (Fintype.card G : ℝ) := by
    rw [hb]; exact lr_var_decomp v
  have hcard0 : (0 : ℝ) ≤ (Fintype.card G : ℝ) := Nat.cast_nonneg _
  have hS1 : (∑ g, u g * POp A v g) + (∑ g, v g * ROp A u g) = 2 * (∑ g, u g * POp A v g) := by
    rw [hswap]; ring
  have hb_eq : b = -a := by linarith
  have hstep : 2 * (a * b * (Fintype.card G : ℝ)) ≤ μ * (2 * (a ^ 2 * (Fintype.card G : ℝ))) := by
    have h1' : a * b * (Fintype.card G : ℝ) = -(a ^ 2 * (Fintype.card G : ℝ)) := by
      rw [hb_eq]; ring
    have h2 : (0 : ℝ) ≤ a ^ 2 * (Fintype.card G : ℝ) := mul_nonneg (sq_nonneg a) hcard0
    rw [h1']
    nlinarith [hμ, h2]
  calc (∑ g, u g * POp A v g) + (∑ g, v g * ROp A u g)
      = 2 * (∑ g, u g * POp A v g) := hS1
    _ = 2 * ((∑ g, (u g - a) * POp A (fun g => v g - b) g) + a * b * (Fintype.card G : ℝ)) := by
          rw [h1]
    _ = 2 * (∑ g, (u g - a) * POp A (fun g => v g - b) g)
          + 2 * (a * b * (Fintype.card G : ℝ)) := by ring
    _ ≤ μ * ((∑ g, (u g - a) ^ 2) + ∑ g, (v g - b) ^ 2)
          + μ * (2 * (a ^ 2 * (Fintype.card G : ℝ))) := by linarith [key1, hstep]
    _ = μ * ((∑ g, u g ^ 2) + ∑ g, v g ^ 2) := by rw [hu2, hv2, hb_eq]; ring

/-- **Spectral gap of the label-class walk of B-edges.** Identify the set of B-edges with a fixed
label `j` with `Fin 2 × G` via `(α,g) ↦` the B-edge `(α,g,j)`; the parallel move sends
`(0,g) ↦ (1, A i * g)` and `(1,g) ↦ (0, (A i)⁻¹ * g)` for a uniformly random `i`. This is
`classOpA`. For mean-zero `s` its quadratic form is at most `μ‖s‖²`, by the same argument as the
A-side, using `leftExpander A μ`. -/
theorem lr_spectral_class_B {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G) (μ : ℝ)
    (hA : leftExpander A μ) (hμ : 0 ≤ μ) :
    ∀ s : Fin 2 × G → ℝ, (∑ p, s p) = 0 →
      ∑ p, s p * classOpA A s p ≤ μ * ∑ p, s p ^ 2 := by
  intro s hs
  by_cases hΔ0 : Δ = 0
  · subst hΔ0
    have hz : ∀ p : Fin 2 × G, classOpA A s p = 0 := by
      intro p; simp [classOpA]
    calc ∑ p, s p * classOpA A s p = 0 := by simp [hz]
      _ ≤ μ * ∑ p : Fin 2 × G, s p ^ 2 := by
            have hnn : (0 : ℝ) ≤ ∑ p : Fin 2 × G, s p ^ 2 :=
              Finset.sum_nonneg (fun p _ => sq_nonneg _)
            nlinarith [hμ, hnn]
  · have hΔne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ0
    have hsplit : (∑ p : Fin 2 × G, s p) = (∑ g, s (0, g)) + (∑ g, s (1, g)) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have hsq : (∑ p : Fin 2 × G, s p ^ 2) =
        (∑ g, s (0, g) ^ 2) + (∑ g, s (1, g) ^ 2) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have huv : (∑ g, s (0, g)) + (∑ g, s (1, g)) = 0 := by rw [← hsplit]; exact hs
    rw [lr_class_split A s, hsq]
    exact lr_class_form_bound A μ hA hμ hΔne (fun g => s (0, g)) (fun g => s (1, g)) huv

end Work.LT
