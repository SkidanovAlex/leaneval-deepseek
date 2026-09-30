import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.SD.prime_window_card_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary and elementary lemmas for the scaling-down construction

This file isolates the objects used by the (paper-faithful) proof of `Work.BMF.scale_down`:

* `goodPairs f pol η H a b fam` — the pairs `(y,p)` with `y ∈ fam`, `p ∈ [a,b]` prime, whose
  *rescaled* phase `(1/p)_* φ_y` correlates with `f` on `[y/p, y/p + H/p]` at level `η H/p`;
* `ballPairs S x R` — the subfamily of pairs of `S` whose rescaled interval lies within `R` of the
  point `x`.

The elementary lemmas proved here are the ones the counting argument needs:

* `ball_card_le` — inside a ball of radius `3H/(2a)` there is at most one source `y` per prime `p`,
  because the source family is `500H`-separated and the ball is `≤ 4.2 H` wide in the `y`-variable;
* `window_weights` — quantitative PNT-in-windows: every window `[a, 7a/5]` with `a ≥ 10¹⁰` contains
  `≥ β' π₀(a)` primes, and its reciprocal-prime mass is `≥ β / log a`.
-/

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-- The pairs `(y,p)` with `y` a source and `p ∈ [a,b]` a prime whose rescaled phase
`(1/p)_* φ_y` correlates with `f` at level `η` on the rescaled interval of length `H/p`. -/
noncomputable def goodPairs (f : ℕ → ℂ) (pol : ℝ → ℝ[X]) (η H a b : ℝ) (fam : Finset ℝ) :
    Finset (ℝ × ℕ) :=
  (fam ×ˢ primesIn a b).filter (fun q =>
    η * (H / (q.2 : ℝ)) ≤ ‖corr f (dil (q.2 : ℝ) (pol q.1)) (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))‖)

/-- The pairs of `S` whose rescaled interval lies within `R` of the point `x`. -/
noncomputable def ballPairs (S : Finset (ℝ × ℕ)) (x R : ℝ) : Finset (ℝ × ℕ) :=
  S.filter (fun q => |q.1 / (q.2 : ℝ) - x| ≤ R)

@[simp] lemma mem_goodPairs {f : ℕ → ℂ} {pol : ℝ → ℝ[X]} {η H a b : ℝ} {fam : Finset ℝ}
    {q : ℝ × ℕ} :
    q ∈ goodPairs f pol η H a b fam ↔
      q.1 ∈ fam ∧ q.2 ∈ primesIn a b ∧
        η * (H / (q.2 : ℝ)) ≤
          ‖corr f (dil (q.2 : ℝ) (pol q.1)) (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))‖ := by
  simp [goodPairs, and_assoc]

@[simp] lemma mem_ballPairs {S : Finset (ℝ × ℕ)} {x R : ℝ} {q : ℝ × ℕ} :
    q ∈ ballPairs S x R ↔ q ∈ S ∧ |q.1 / (q.2 : ℝ) - x| ≤ R := by
  simp [ballPairs]

lemma goodPairs_mono_fam {f : ℕ → ℂ} {pol : ℝ → ℝ[X]} {η H a b : ℝ} {fam fam' : Finset ℝ}
    (h : fam ⊆ fam') : goodPairs f pol η H a b fam ⊆ goodPairs f pol η H a b fam' := by
  intro q hq
  rw [mem_goodPairs] at hq ⊢
  exact ⟨h hq.1, hq.2⟩

lemma ballPairs_mono {S T : Finset (ℝ × ℕ)} {x R : ℝ} (h : S ⊆ T) :
    ballPairs S x R ⊆ ballPairs T x R := by
  intro q hq
  rw [mem_ballPairs] at hq ⊢
  exact ⟨h hq.1, hq.2⟩

/-- In a ball of radius `3H/(2a)` around any point there is at most one source per prime:
`500H`-separated sources whose rescaled intervals both lie in the ball would be
`≤ 21H/5 < 500H` apart. -/
lemma ball_card_le {fam : Finset ℝ} {H a b x : ℝ} (hH : 0 < H) (ha : 0 < a) (hbpos : 0 < b)
    (hb : b ≤ 7 * a / 5)
    (hsep : ∀ y ∈ fam, ∀ y' ∈ fam, y ≠ y' → 500 * H ≤ |y - y'|) :
    (ballPairs (fam ×ˢ primesIn a b) x (3 * H / (2 * a))).card ≤ (primesIn a b).card := by
  set S := ballPairs (fam ×ˢ primesIn a b) x (3 * H / (2 * a)) with hS
  have hmem : ∀ q ∈ S, q ∈ fam ×ˢ primesIn a b ∧ |q.1 / (q.2 : ℝ) - x| ≤ 3 * H / (2 * a) := by
    intro q hq
    rw [hS, mem_ballPairs] at hq
    exact hq
  have hinj : Set.InjOn (fun q : ℝ × ℕ => q.2) ↑S := by
    intro q hq q' hq' hpp
    have hpp' : q.2 = q'.2 := hpp
    obtain ⟨hq1, hqx⟩ := hmem q hq
    obtain ⟨hq1', hqx'⟩ := hmem q' hq'
    have hqf : q.1 ∈ fam := (Finset.mem_product.mp hq1).1
    have hqf' : q'.1 ∈ fam := (Finset.mem_product.mp hq1').1
    have hqp : q.2 ∈ primesIn a b := (Finset.mem_product.mp hq1).2
    have hprime : Nat.Prime q.2 := (Finset.mem_filter.mp hqp).2
    have hppos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hprime.pos
    have hple : (q.2 : ℝ) ≤ 7 * a / 5 := by
      have h1 : q.2 ≤ ⌊b⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hqp).1).2
      have h3 : ((q.2 : ℕ) : ℝ) ≤ ((⌊b⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 : ((⌊b⌋₊ : ℕ) : ℝ) ≤ b := Nat.floor_le hbpos.le
      linarith
    have hdiff : |q.1 - q'.1| ≤ 3 * H * (q.2 : ℝ) / a := by
      have h1 : q.1 / (q.2 : ℝ) - q'.1 / (q.2 : ℝ) = (q.1 - q'.1) / (q.2 : ℝ) := by ring
      have h2 : |q.1 / (q.2 : ℝ) - q'.1 / (q.2 : ℝ)| ≤ 3 * H / a := by
        have hA : q'.1 / (q.2 : ℝ) = q'.1 / (q'.2 : ℝ) := by rw [hpp']
        rw [hA]
        calc |q.1 / (q.2 : ℝ) - q'.1 / (q'.2 : ℝ)|
            ≤ |q.1 / (q.2 : ℝ) - x| + |x - q'.1 / (q'.2 : ℝ)| := abs_sub_le _ _ _
          _ = |q.1 / (q.2 : ℝ) - x| + |q'.1 / (q'.2 : ℝ) - x| := by
                congr 1
                exact abs_sub_comm x _
          _ ≤ 3 * H / (2 * a) + 3 * H / (2 * a) := add_le_add hqx hqx'
          _ = 3 * H / a := by field_simp; ring
      have h6 : |(q.1 - q'.1) / (q.2 : ℝ)| * (q.2 : ℝ) = |q.1 - q'.1| := by
        rw [abs_div, abs_of_pos hppos]
        field_simp
      have h7 : |q.1 / (q.2 : ℝ) - q'.1 / (q.2 : ℝ)| * (q.2 : ℝ) = |q.1 - q'.1| := by
        rw [h1, h6]
      have h8 : |q.1 / (q.2 : ℝ) - q'.1 / (q.2 : ℝ)| * (q.2 : ℝ) ≤ (3 * H / a) * (q.2 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hppos.le
      rw [h7] at h8
      have h9 : (3 * H / a) * (q.2 : ℝ) = 3 * H * (q.2 : ℝ) / a := by ring
      linarith [h8, h9.symm.le, h9.le]
    have hlt : |q.1 - q'.1| < 500 * H := by
      have h1 : (q.2 : ℝ) / a ≤ 7 / 5 := by
        rw [div_le_iff₀ ha]; linarith
      have h2 : 3 * H * (q.2 : ℝ) / a ≤ 3 * H * (7 / 5) := by
        have h3 : 3 * H * (q.2 : ℝ) / a = 3 * H * ((q.2 : ℝ) / a) := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith [hdiff, h2, hH]
    have hxy : q.1 = q'.1 := by
      by_contra hne
      exact absurd (hsep q.1 hqf q'.1 hqf' hne) (not_le.mpr hlt)
    exact Prod.ext hxy hpp'
  calc S.card = (S.image (fun q : ℝ × ℕ => q.2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (primesIn a b).card := Finset.card_le_card (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact (Finset.mem_product.mp (hmem q hq).1).2)

/-- Quantitative PNT in windows: for `a ≥ 10¹⁰` the window `[a, 7a/5]` contains `≥ β' π₀(a)`
primes and carries reciprocal-prime mass `≥ β / log a`. -/
theorem window_weights :
    ∃ β β' A : ℝ, 0 < β ∧ 0 < β' ∧ 0 < A ∧ ∀ a : ℝ, A ≤ a →
      β / Real.log a ≤ ∑ p ∈ primesIn a (7 * a / 5), (1 : ℝ) / (p : ℝ) ∧
      β' * pi0 a ≤ ((primesIn a (7 * a / 5)).card : ℝ) := by
  obtain ⟨A₀, hA₀pos, hPNT⟩ := SD.prime_window_card_ge
  refine ⟨1 / 14, 1 / 10, max A₀ 10000000000, by norm_num, by norm_num,
    lt_max_of_lt_right (by norm_num), ?_⟩
  intro a ha
  have hA₀a : A₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha_thr : (10000000000 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hapos : (0 : ℝ) < a := by linarith
  have halog : 0 < Real.log a := Real.log_pos (by linarith)
  have hbig : 8 * a / (Real.log a) ^ 2 ≤ 2 * a / 5 := by
    have h4 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; ring
    have h3 : Real.log 8 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
    rw [h4] at h3
    have h5 : (2 : ℝ) < Real.log 10 := by linarith [Real.log_two_gt_d9]
    have h1 : Real.log ((10 : ℝ) ^ 10) ≤ Real.log a :=
      Real.log_le_log (by norm_num) (by norm_num; linarith [ha_thr])
    have h2 : Real.log ((10 : ℝ) ^ 10) = 10 * Real.log 10 := by
      rw [Real.log_pow]; push_cast; ring
    rw [h2] at h1
    have h20 : (20 : ℝ) ≤ Real.log a := by linarith
    have h20' : (20 : ℝ) ≤ (Real.log a) ^ 2 := by nlinarith [h20, halog]
    rw [div_le_iff₀ (pow_pos halog 2)]
    have h21 : (2 * a / 5) * 20 ≤ (2 * a / 5) * (Real.log a) ^ 2 :=
      mul_le_mul_of_nonneg_left h20' (by positivity)
    linarith
  have hwin := hPNT a (2 * a / 5) hA₀a (by positivity) (by linarith) hbig
  have hsub : (Finset.Ioc ⌊a⌋₊ ⌊a + 2 * a / 5⌋₊).filter Nat.Prime ⊆ primesIn a (7 * a / 5) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpr, hpprime⟩ := hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Ioc.mp hpr
    rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hpprime⟩
    · have h3 : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
        rw [Nat.ceil_le]
        push_cast
        linarith [Nat.lt_floor_add_one a]
      exact le_trans h3 hp1
    · have h2 : ⌊a + 2 * a / 5⌋₊ = ⌊7 * a / 5⌋₊ := by
        congr 1; ring
      rw [h2] at hp2
      exact hp2
  have hcard : (a / (5 * Real.log (2 * a)) : ℝ) ≤ ((primesIn a (7 * a / 5)).card : ℝ) := by
    have h1 : (((Finset.Ioc ⌊a⌋₊ ⌊a + 2 * a / 5⌋₊).filter Nat.Prime).card : ℝ) ≤
        ((primesIn a (7 * a / 5)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : (a / (5 * Real.log (2 * a)) : ℝ) = (2 * a / 5) / (2 * Real.log (2 * a)) := by ring
    rw [h2]
    linarith
  have hlogle : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) (by linarith)
  constructor
  · have hsum : ((primesIn a (7 * a / 5)).card : ℝ) / (7 * a / 5) ≤
        ∑ p ∈ primesIn a (7 * a / 5), (1 : ℝ) / (p : ℝ) := by
      have hbnd : ∀ p ∈ primesIn a (7 * a / 5), (1 : ℝ) / (7 * a / 5) ≤ (1 : ℝ) / (p : ℝ) := by
        intro p hp
        have hp2 : Nat.Prime p := (Finset.mem_filter.mp hp).2
        have hp2pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp2.pos
        have h4 : ((p : ℕ) : ℝ) ≤ ((⌊7 * a / 5⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        have h3 : ((⌊7 * a / 5⌋₊ : ℕ) : ℝ) ≤ 7 * a / 5 := Nat.floor_le (by positivity)
        exact one_div_le_one_div_of_le hp2pos (le_trans h4 h3)
      calc ((primesIn a (7 * a / 5)).card : ℝ) / (7 * a / 5)
          = ∑ _p ∈ primesIn a (7 * a / 5), (1 : ℝ) / (7 * a / 5) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum hbnd
    have hlow : (1 : ℝ) / (14 * Real.log a) ≤
        ((primesIn a (7 * a / 5)).card : ℝ) / (7 * a / 5) := by
      have h1 : a / (5 * Real.log (2 * a)) / (7 * a / 5) ≤
          ((primesIn a (7 * a / 5)).card : ℝ) / (7 * a / 5) :=
        div_le_div_of_nonneg_right hcard (by positivity)
      have h2 : a / (5 * Real.log (2 * a)) / (7 * a / 5) = 1 / (7 * Real.log (2 * a)) := by
        field_simp
      rw [h2] at h1
      have h6 : 0 < 7 * Real.log (2 * a) := by
        have h6' : 0 < Real.log (2 * a) := Real.log_pos (by linarith)
        linarith
      have h7 : 7 * Real.log (2 * a) ≤ 14 * Real.log a := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hapos)]
        linarith [hlogle, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have h5 : (1 : ℝ) / (14 * Real.log a) ≤ 1 / (7 * Real.log (2 * a)) :=
        one_div_le_one_div_of_le h6 h7
      linarith
    have hgoal : (1 : ℝ) / 14 / Real.log a = 1 / (14 * Real.log a) := by ring
    rw [hgoal]
    linarith [hsum, hlow]
  · have h1 : a / (5 * Real.log (2 * a)) ≤ ((primesIn a (7 * a / 5)).card : ℝ) := hcard
    have h4 : a / (10 * Real.log a) ≤ a / (5 * Real.log (2 * a)) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hapos)]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith [hlogle, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have h5 : a / (10 * Real.log a) = (1 / 10) * pi0 a := by rw [pi0]; ring
    rw [h5] at h4
    linarith

end Work.BMF
