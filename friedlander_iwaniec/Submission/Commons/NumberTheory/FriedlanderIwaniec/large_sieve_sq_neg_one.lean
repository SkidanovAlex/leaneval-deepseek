import Mathlib
import Submission.Commons.Analysis.ExponentialSums.large_sieve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-!
# Large sieve over the roots of `ν ^ 2 ≡ -1 (mod d)`

This file proves the large-sieve estimate of Friedlander–Iwaniec
("The polynomial X² + Y⁴ captures its primes", Lemma 3.2):

`∑_{D < d ≤ 2D} ∑_{ν² ≡ -1 (mod d)} ‖∑_{n ≤ N} a n * e(nν/d)‖² ≤ 8 (N + D) ∑ ‖a n‖²`.

The essential input is the *exceptional well-spacing* of the fractions `ν/d`:
if `(d₁,ν₁) ≠ (d₂,ν₂)` with `d₁,d₂ ∈ (D, 2D]` then the two points are at
distance `≥ 1 / max (d₁,d₂) ≥ 1/(2D)` from each other modulo `1` (`root_separation`).

The well-spacing is proved from the elementary algebraic identity
(`key_identity` below): for `dᵢ ∣ νᵢ² + 1`, writing `kᵢ = (νᵢ²+1)/dᵢ`, and
`T = k₁d₂ + k₂d₁ - 2ν₁ν₂ ∈ ℤ`, `e = ν₁d₂ - ν₂d₁`, one has
`d₁d₂ T = e² + d₁² + d₂²`.
Since `e ≠ 0` for distinct points, `T ≥ 3`, whence
`e² ≥ 3d₁d₂ - d₁² - d₂² ≥ (min d₁ d₂)²` as soon as `max d₁ d₂ ≤ 2 min d₁ d₂`
(which holds in a dyadic window).  -/

/-- The key algebraic identity.  If `Kᵢ * dᵢ = μᵢ ^ 2 + 1` then
`d₁ d₂ (K₁ d₂ + K₂ d₁ - 2 μ₁ μ₂) = (μ₁ d₂ - μ₂ d₁) ^ 2 + d₁ ^ 2 + d₂ ^ 2`. -/
lemma key_identity (d₁ d₂ K₁ K₂ μ₁ μ₂ : ℤ)
    (h₁ : K₁ * d₁ = μ₁ ^ 2 + 1) (h₂ : K₂ * d₂ = μ₂ ^ 2 + 1) :
    d₁ * d₂ * (K₁ * d₂ + K₂ * d₁ - 2 * μ₁ * μ₂)
      = (μ₁ * d₂ - μ₂ * d₁) ^ 2 + d₁ ^ 2 + d₂ ^ 2 := by
  have h : d₁ * d₂ * (K₁ * d₂ + K₂ * d₁ - 2 * μ₁ * μ₂)
      = d₂ ^ 2 * (K₁ * d₁) + d₁ ^ 2 * (K₂ * d₂) - 2 * (μ₁ * d₂) * (μ₂ * d₁) := by
    ring
  rw [h, h₁, h₂]
  ring

/-- The determinant `μ₁ d₂ - μ₂ d₁` of two solutions of `x ^ 2 ≡ -1` is large
once the moduli are comparable (`max d₁ d₂ ≤ 2 min d₁ d₂`). -/
lemma abs_det_ge_min (d₁ d₂ : ℕ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (μ₁ μ₂ : ℤ)
    (hdiv₁ : (d₁ : ℤ) ∣ μ₁ ^ 2 + 1) (hdiv₂ : (d₂ : ℤ) ∣ μ₂ ^ 2 + 1)
    (hle : max d₁ d₂ ≤ 2 * min d₁ d₂)
    (hne : μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ) ≠ 0) :
    ((min d₁ d₂ : ℕ) : ℝ) ≤ |((μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ) : ℤ) : ℝ)| := by
  obtain ⟨K₁, hK₁⟩ := hdiv₁
  obtain ⟨K₂, hK₂⟩ := hdiv₂
  have hkey := key_identity (d₁ : ℤ) (d₂ : ℤ) K₁ K₂ μ₁ μ₂
    (by linarith [hK₁]) (by linarith [hK₂])
  have hpos : (0 : ℤ) < (d₁ : ℤ) * d₂ := by
    have h1 : (0 : ℤ) < d₁ := by exact_mod_cast Nat.pos_of_ne_zero hd₁
    have h2 : (0 : ℤ) < d₂ := by exact_mod_cast Nat.pos_of_ne_zero hd₂
    positivity
  have he2 : (1 : ℤ) ≤ (μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ)) ^ 2 := by
    have habs : (1 : ℤ) ≤ |μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ)| := Int.one_le_abs hne
    nlinarith [sq_abs (μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ)), habs,
      abs_nonneg (μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ))]
  have hAM : 2 * (d₁ : ℤ) * d₂ ≤ (d₁ : ℤ) ^ 2 + d₂ ^ 2 := by
    nlinarith [sq_nonneg ((d₁ : ℤ) - d₂)]
  have hT : (3 : ℤ) ≤ K₁ * d₂ + K₂ * d₁ - 2 * μ₁ * μ₂ := by
    have hmul : (1 : ℤ) ≤ (d₁ : ℤ) * d₂ * (K₁ * d₂ + K₂ * d₁ - 2 * μ₁ * μ₂ - 2) := by
      nlinarith [hkey, he2, hAM]
    by_contra hcon
    have h2 : (d₁ : ℤ) * d₂ * (K₁ * d₂ + K₂ * d₁ - 2 * μ₁ * μ₂ - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (by omega)
    omega
  have hsq : (((min d₁ d₂ : ℕ) : ℤ)) ^ 2 ≤ (μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ)) ^ 2 := by
    have hlow : 3 * (d₁ : ℤ) * d₂ - (d₁ : ℤ) ^ 2 - d₂ ^ 2
        ≤ (μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ)) ^ 2 := by nlinarith [hkey, hT]
    rcases le_total d₁ d₂ with h | h
    · have hmin : min d₁ d₂ = d₁ := min_eq_left h
      rw [hmin]
      have h2 : d₂ ≤ 2 * d₁ := by
        have := hle; rw [hmin, max_eq_right h] at this; exact this
      have hprod : (0 : ℤ) ≤ ((d₂ : ℤ) - d₁) * (2 * (d₁ : ℤ) - d₂) :=
        mul_nonneg (by simp; omega) (by simp; omega)
      nlinarith [hlow, hprod]
    · have hmin : min d₁ d₂ = d₂ := min_eq_right h
      rw [hmin]
      have h2 : d₁ ≤ 2 * d₂ := by
        have := hle; rw [hmin, max_eq_left h] at this; exact this
      have hprod : (0 : ℤ) ≤ ((d₁ : ℤ) - d₂) * (2 * (d₂ : ℤ) - d₁) :=
        mul_nonneg (by simp; omega) (by simp; omega)
      nlinarith [hlow, hprod]
  have hsqR : (((min d₁ d₂ : ℕ) : ℝ)) ^ 2
      ≤ (((μ₁ * (d₂ : ℤ) - μ₂ * (d₁ : ℤ) : ℤ)) : ℝ) ^ 2 := by
    exact_mod_cast hsq
  have habs := (sq_le_sq.mp hsqR)
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((min d₁ d₂ : ℕ) : ℝ))] at habs

/-- **Well-spacing of the roots of `ν ^ 2 ≡ -1 (mod d)`.**  In a dyadic window
`(D, 2D]` distinct points `ν / d` are separated by at least `1 / (8 D)`. -/
lemma root_separation (D : ℕ) (hD : 1 ≤ D) (d₁ d₂ ν₁ ν₂ : ℕ)
    (hd₁ : d₁ ∈ Finset.Icc (D + 1) (2 * D)) (hd₂ : d₂ ∈ Finset.Icc (D + 1) (2 * D))
    (hν₁ : ν₁ ∈ (Finset.range d₁).filter (fun ν : ℕ => ((ν : ZMod d₁)) ^ 2 = -1))
    (hν₂ : ν₂ ∈ (Finset.range d₂).filter (fun ν : ℕ => ((ν : ZMod d₂)) ^ 2 = -1))
    (hne : ¬ (d₁ = d₂ ∧ ν₁ = ν₂)) :
    ∀ k : ℤ, (1 : ℝ) / (8 * D) ≤ |(ν₁ : ℝ) / (d₁ : ℝ) - (ν₂ : ℝ) / (d₂ : ℝ) - k| := by
  have hge₁ : D + 1 ≤ d₁ := (Finset.mem_Icc.mp hd₁).1
  have hle₁ : d₁ ≤ 2 * D := (Finset.mem_Icc.mp hd₁).2
  have hge₂ : D + 1 ≤ d₂ := (Finset.mem_Icc.mp hd₂).1
  have hle₂ : d₂ ≤ 2 * D := (Finset.mem_Icc.mp hd₂).2
  have hlt₁ : ν₁ < d₁ := Finset.mem_range.mp (Finset.mem_filter.mp hν₁).1
  have hlt₂ : ν₂ < d₂ := Finset.mem_range.mp (Finset.mem_filter.mp hν₂).1
  have hrt₁ := (Finset.mem_filter.mp hν₁).2
  have hrt₂ := (Finset.mem_filter.mp hν₂).2
  have hd₁0 : d₁ ≠ 0 := by omega
  have hd₂0 : d₂ ≠ 0 := by omega
  have hdiv₁ : d₁ ∣ ν₁ ^ 2 + 1 := by
    have h : (((ν₁ ^ 2 + 1 : ℕ)) : ZMod d₁) = 0 := by
      push_cast
      rw [hrt₁]; ring
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((ν₁ ^ 2 + 1 : ℕ) : ℤ) d₁).mp (by simpa using h)
    exact_mod_cast h2
  have hdiv₂ : d₂ ∣ ν₂ ^ 2 + 1 := by
    have h : (((ν₂ ^ 2 + 1 : ℕ)) : ZMod d₂) = 0 := by
      push_cast
      rw [hrt₂]; ring
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((ν₂ ^ 2 + 1 : ℕ) : ℤ) d₂).mp (by simpa using h)
    exact_mod_cast h2
  have hle : max d₁ d₂ ≤ 2 * min d₁ d₂ := by
    have h1 : max d₁ d₂ ≤ 2 * D := max_le hle₁ hle₂
    have h2 : D + 1 ≤ min d₁ d₂ := le_min hge₁ hge₂
    omega
  intro k
  set μ₁ : ℤ := (ν₁ : ℤ) - k * (d₁ : ℤ)
  have hdiv₁Z : (d₁ : ℤ) ∣ μ₁ ^ 2 + 1 := by
    have hbase : (d₁ : ℤ) ∣ (ν₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hdiv₁
    have hsub : (d₁ : ℤ) ∣ μ₁ - (ν₁ : ℤ) := ⟨-k, by simp only [μ₁]; ring⟩
    have hfac : μ₁ ^ 2 + 1
        = ((ν₁ : ℤ) ^ 2 + 1) + (μ₁ - (ν₁ : ℤ)) * (μ₁ + (ν₁ : ℤ)) := by ring
    rw [hfac]
    exact dvd_add hbase (dvd_mul_of_dvd_left hsub _)
  have hdiv₂Z : (d₂ : ℤ) ∣ (ν₂ : ℤ) ^ 2 + 1 := by exact_mod_cast hdiv₂
  have hne' : μ₁ * (d₂ : ℤ) - (ν₂ : ℤ) * (d₁ : ℤ) ≠ 0 := by
    intro he
    have hμν : μ₁ * (d₂ : ℤ) = (ν₂ : ℤ) * (d₁ : ℤ) := sub_eq_zero.mp he
    obtain ⟨K₁, hK₁⟩ := hdiv₁Z
    obtain ⟨K₂, hK₂⟩ := hdiv₂Z
    have hdvd₁ : (d₁ : ℤ) ∣ (d₂ : ℤ) := by
      have e1 : μ₁ * (μ₁ * (d₂ : ℤ)) - (μ₁ ^ 2 + 1) * (d₂ : ℤ) = -(d₂ : ℤ) := by ring
      rw [hμν, hK₁] at e1
      have h2 : (d₁ : ℤ) * (μ₁ * (ν₂ : ℤ) - K₁ * (d₂ : ℤ)) = -(d₂ : ℤ) := by
        rw [← e1]; ring
      exact dvd_neg.mp ⟨_, h2.symm⟩
    have hdvd₂ : (d₂ : ℤ) ∣ (d₁ : ℤ) := by
      have e1 : (ν₂ : ℤ) * ((ν₂ : ℤ) * (d₁ : ℤ)) - ((ν₂ : ℤ) ^ 2 + 1) * (d₁ : ℤ)
          = -(d₁ : ℤ) := by ring
      rw [← hμν, hK₂] at e1
      have h2 : (d₂ : ℤ) * ((ν₂ : ℤ) * μ₁ - K₂ * (d₁ : ℤ)) = -(d₁ : ℤ) := by
        rw [← e1]; ring
      exact dvd_neg.mp ⟨_, h2.symm⟩
    have heq : d₁ = d₂ := Nat.dvd_antisymm (by exact_mod_cast hdvd₁) (by exact_mod_cast hdvd₂)
    have hcast₂ : ((d₂ : ℤ)) ≠ 0 := by exact_mod_cast hd₂0
    have hμeq : μ₁ = (ν₂ : ℤ) := by
      have h := hμν
      rw [heq] at h
      exact mul_right_cancel₀ hcast₂ h
    have hk : k * (d₁ : ℤ) = (ν₁ : ℤ) - (ν₂ : ℤ) := by
      have : (ν₁ : ℤ) - k * (d₁ : ℤ) = (ν₂ : ℤ) := by simp only [← hμeq, μ₁]
      linarith
    have hbnd : |k| * (d₁ : ℤ) < (d₁ : ℤ) := by
      have h1 : |(ν₁ : ℤ) - (ν₂ : ℤ)| < (d₁ : ℤ) := by
        have h2 : ν₂ < d₁ := by omega
        rw [abs_lt]
        constructor <;> (push_cast; omega)
      rw [← hk, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (d₁ : ℤ))] at h1
      exact h1
    have hk0 : k = 0 := by
      have hd₁pos : (0 : ℤ) < (d₁ : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hd₁0
      by_contra hc
      have h1 : 1 ≤ |k| := Int.one_le_abs hc
      nlinarith
    have hνeq : ν₁ = ν₂ := by
      rw [hk0, zero_mul] at hk
      omega
    exact hne ⟨heq, hνeq⟩
  have hbound := abs_det_ge_min d₁ d₂ hd₁0 hd₂0 μ₁ (ν₂ : ℤ) hdiv₁Z hdiv₂Z hle hne'
  have hrat : (ν₁ : ℝ) / (d₁ : ℝ) - (ν₂ : ℝ) / (d₂ : ℝ) - (k : ℝ)
      = (((μ₁ * (d₂ : ℤ) - (ν₂ : ℤ) * (d₁ : ℤ) : ℤ)) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
    simp only [μ₁]; push_cast; field_simp; ring
  rw [hrat, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ))]
  refine le_trans ?_ (div_le_div_of_nonneg_right hbound (by positivity))
  have hminmax : ((min d₁ d₂ : ℕ) : ℝ) * ((max d₁ d₂ : ℕ) : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
    rw [← Nat.cast_mul, min_mul_max, Nat.cast_mul]
  rw [← hminmax]
  rw [show ((min d₁ d₂ : ℕ) : ℝ) / (((min d₁ d₂ : ℕ) : ℝ) * ((max d₁ d₂ : ℕ) : ℝ))
      = 1 / ((max d₁ d₂ : ℕ) : ℝ) by
    rw [div_mul_eq_div_div]
    rw [div_self (by positivity : (((min d₁ d₂ : ℕ) : ℝ)) ≠ 0), one_div]]
  refine one_div_le_one_div_of_le ?_ ?_
  · have h2 : D + 1 ≤ min d₁ d₂ := le_min hge₁ hge₂
    positivity
  · have hmaxle : max d₁ d₂ ≤ 8 * D := by
      have h1 : max d₁ d₂ ≤ 2 * D := max_le hle₁ hle₂
      omega
    exact_mod_cast hmaxle


theorem large_sieve_sq_neg_one (D N : ℕ) (a : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc (D+1) (2*D),
        ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
          ‖∑ n ∈ Finset.Icc 1 N,
              a n * Commons.Analysis.ExponentialSums.ch ((n:ℝ) * ((ν:ℕ):ℝ)/(d:ℝ))‖^2)
      ≤ 8 * ((N:ℝ) + (D:ℝ)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · subst hD0
    have hempty : (Finset.Icc (0 + 1) (2 * 0) : Finset ℕ) = ∅ := by decide
    rw [hempty, Finset.sum_empty]
    positivity
  · set S : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc (D + 1) (2 * D)).sigma
        (fun d => (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d)) ^ 2 = -1)) with hSdef
    let G : (Σ _ : ℕ, ℕ) → ℝ := fun x =>
      ‖∑ n ∈ Finset.Icc 1 N,
        a n * Commons.Analysis.ExponentialSums.ch
          ((n : ℝ) * (((x.2 : ℕ) : ℝ) / ((x.1 : ℕ) : ℝ)))‖ ^ 2
    have hLHS : (∑ d ∈ Finset.Icc (D+1) (2*D),
        ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
          ‖∑ n ∈ Finset.Icc 1 N,
              a n * Commons.Analysis.ExponentialSums.ch ((n:ℝ) * ((ν:ℕ):ℝ)/(d:ℝ))‖^2)
        = ∑ x ∈ S, G x := by
      rw [hSdef, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun ν _ => ?_))
      simp only [G]
      congr 1
      congr 1
      exact Finset.sum_congr rfl (fun n _ => by rw [mul_div_assoc])
    let α : ↥S → ℝ := fun x => ((x.1.2 : ℕ) : ℝ) / ((x.1.1 : ℕ) : ℝ)
    have hsep : ∀ r s : ↥S, r ≠ s → ∀ k : ℤ, (1 / (8 * D) : ℝ) ≤ |α r - α s - k| := by
      intro r s hrs k
      have hr := r.2
      have hs := s.2
      simp only [hSdef] at hr hs
      obtain ⟨hr1, hr2⟩ := Finset.mem_sigma.mp hr
      obtain ⟨hs1, hs2⟩ := Finset.mem_sigma.mp hs
      have hne : ¬ (r.1.1 = s.1.1 ∧ r.1.2 = s.1.2) := by
        rintro ⟨h1, h2⟩
        exact hrs (Subtype.ext (by
          have := Sigma.ext h1 (heq_of_eq h2)
          simpa using this))
      have h := root_separation D hD1 r.1.1 s.1.1 r.1.2 s.1.2 hr1 hs1 hr2 hs2 hne k
      simpa only [α] using h
    have hls := Commons.Analysis.ExponentialSums.large_sieve α
      (by positivity : (0 : ℝ) < 1 / (8 * D)) hsep N a
    have hGα : ∀ x : ↥S, G x.1
        = ‖∑ n ∈ Finset.Icc 1 N,
            a n * Commons.Analysis.ExponentialSums.ch ((n : ℝ) * α x)‖ ^ 2 := by
      intro x
      simp only [G, α]
    rw [hLHS]
    have hsum_eq : (∑ x ∈ S, G x)
        = ∑ r : ↥S, ‖∑ n ∈ Finset.Icc 1 N,
            a n * Commons.Analysis.ExponentialSums.ch ((n : ℝ) * α r)‖ ^ 2 :=
      (Finset.sum_coe_sort S G).symm.trans (Finset.sum_congr rfl (fun x _ => hGα x))
    rw [hsum_eq]
    refine le_trans hls ?_
    have hdelta : (1 : ℝ) / (1 / (8 * D)) = 8 * D := one_div_one_div _
    rw [hdelta]
    have hN8 : (N : ℝ) + 8 * D ≤ 8 * ((N : ℝ) + D) := by
      push_cast
      linarith
    have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by positivity
    nlinarith [hN8, hnn]

end Commons.NumberTheory.FriedlanderIwaniec
