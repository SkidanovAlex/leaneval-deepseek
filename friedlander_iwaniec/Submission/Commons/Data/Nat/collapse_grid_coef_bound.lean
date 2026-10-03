import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Data.Nat.card_divisors_le_const_mul_rpow

namespace Commons.Data.Nat

open scoped BigOperators

/-- Cauchy–Schwarz for the norm of a finite sum of complex numbers:
`‖∑_{i∈s} f i‖² ≤ #s · ∑_{i∈s} ‖f i‖²`. -/
private lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  linarith

/-- The number of elements `p` of `[1,K] ×ˢ [1,L]` with `p.1*p.2 = N` is at most the number
of divisors of `N`.  The map `p ↦ p.1` is injective on that set and lands in `N.divisors`. -/
private lemma filter_prod_card_le_divisors_card (K L N e : ℕ) (hN : N ≠ 0) :
    (((Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = N ∧ e ∣ p.2)).card ≤ N.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe]
    exact Nat.mem_divisors.mpr ⟨⟨p.2, hp.2.1.symm⟩, hN⟩
  · intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp.1.1).1
    have hpq' : p.1 = q.1 := hpq
    have h2 : p.2 = q.2 := by
      apply Nat.mul_left_cancel (by omega : 0 < p.1)
      rw [hp.2.1, ← hq.2.1, hpq']
    exact Prod.ext hpq' h2

/-- Collapsing the sum over `N`: for `N₀ = p.1*p.2` inside `Nr`,
`∑_{N∈Nr} [N₀ = N ∧ e ∣ p.2] · (D N · w)` equals `[e ∣ p.2] · (D N₀ · w)`. -/
private lemma sum_ite_mul_collapse (Nr : Finset ℕ) (p : ℕ × ℕ) (e : ℕ) (D : ℕ → ℝ) (w : ℝ)
    (hN0 : p.1 * p.2 ∈ Nr) :
    (∑ N ∈ Nr, if (p.1 * p.2 = N ∧ e ∣ p.2) then D N * w else 0)
      = if e ∣ p.2 then D (p.1 * p.2) * w else 0 := by
  by_cases he : e ∣ p.2
  · rw [if_pos he]
    trans ∑ N ∈ Nr, (if (p.1 * p.2 = N) then D N * w else 0)
    · apply Finset.sum_congr rfl
      intro N _
      simp only [he, and_true]
    · rw [Finset.sum_ite_eq, if_pos hN0]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro N _
    rw [if_neg]
    intro h
    exact he h.2

/-- `∑_{e∈E} [e ∣ l] · X = X · #{e ∈ E : e ∣ l}`. -/
private lemma sum_ite_dvd_eq (E : Finset ℕ) (l : ℕ) (X : ℝ) :
    (∑ e ∈ E, if e ∣ l then X else 0)
      = ((E.filter (fun e => e ∣ l)).card : ℝ) * X := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The divisors of `l` lying in `[1,M]` are divisors of `l`. -/
private lemma filter_Icc_dvd_card_le_divisors_card (M l : ℕ) (hl : l ≠ 0) :
    ((Finset.Icc 1 M).filter (fun e => e ∣ l)).card ≤ l.divisors.card := by
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he
  rw [Nat.mem_divisors]
  exact ⟨he.2, hl⟩

/-- Abstract Hilbert–Schmidt type bound underlying the collapse estimate.

`G` is a finite grid, `E` and `Nr` finite index sets, `f` a complex-valued function on `G`,
and `D` a real majorant of the cardinalities of the fibres
`{p ∈ G : p.1*p.2 = N, e ∣ p.2}`.  Then
`∑_e ∑_N ‖∑_{p∈G, p.1p.2 = N, e∣p.2} f p‖²
  ≤ ∑_{p∈G} D(p.1 p.2) · #{e ∈ E : e ∣ p.2} · ‖f p‖²`. -/
private theorem collapse_core
    (E Nr : Finset ℕ) (G : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (D : ℕ → ℝ)
    (hDcard : ∀ e N, N ∈ Nr →
      ((G.filter (fun p => p.1 * p.2 = N ∧ e ∣ p.2)).card : ℝ) ≤ D N)
    (hG : ∀ p ∈ G, p.1 * p.2 ∈ Nr) :
    (∑ e ∈ E, ∑ N ∈ Nr, ‖∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then f p else 0)‖ ^ 2)
    ≤ ∑ p ∈ G, D (p.1 * p.2) * ((E.filter (fun e => e ∣ p.2)).card : ℝ) * ‖f p‖ ^ 2 := by
  have hstep1 :
      (∑ e ∈ E, ∑ N ∈ Nr, ‖∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then f p else 0)‖ ^ 2)
      ≤ ∑ e ∈ E, ∑ N ∈ Nr,
          D N * ∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then ‖f p‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sum_le_sum
    intro N hN
    have hfilt : (∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then f p else 0))
        = ∑ p ∈ G.filter (fun p => p.1 * p.2 = N ∧ e ∣ p.2), f p := by
      rw [Finset.sum_filter]
    rw [hfilt]
    have hcs := norm_sum_sq_le_card_mul_sum_norm_sq
      (G.filter (fun p => p.1 * p.2 = N ∧ e ∣ p.2)) f
    have hfilt2 : (∑ p ∈ G.filter (fun p => p.1 * p.2 = N ∧ e ∣ p.2), ‖f p‖ ^ 2)
        = ∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then ‖f p‖ ^ 2 else 0) := by
      rw [Finset.sum_filter]
    rw [hfilt2] at hcs
    refine le_trans hcs ?_
    apply mul_le_mul_of_nonneg_right (hDcard e N hN)
    apply Finset.sum_nonneg
    intro p _
    by_cases h : (p.1 * p.2 = N ∧ e ∣ p.2)
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hreorganize :
      (∑ e ∈ E, ∑ N ∈ Nr,
          D N * ∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then ‖f p‖ ^ 2 else 0))
      = ∑ p ∈ G, D (p.1 * p.2) * ((E.filter (fun e => e ∣ p.2)).card : ℝ) * ‖f p‖ ^ 2 := by
    calc (∑ e ∈ E, ∑ N ∈ Nr,
            D N * ∑ p ∈ G, (if (p.1 * p.2 = N ∧ e ∣ p.2) then ‖f p‖ ^ 2 else 0))
        = ∑ e ∈ E, ∑ p ∈ G, ∑ N ∈ Nr,
            (if (p.1 * p.2 = N ∧ e ∣ p.2) then D N * ‖f p‖ ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          trans ∑ N ∈ Nr, ∑ p ∈ G,
              (if (p.1 * p.2 = N ∧ e ∣ p.2) then D N * ‖f p‖ ^ 2 else 0)
          · apply Finset.sum_congr rfl
            intro N _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            by_cases h : (p.1 * p.2 = N ∧ e ∣ p.2) <;> simp [h]
          · rw [Finset.sum_comm]
      _ = ∑ p ∈ G, ∑ e ∈ E, ∑ N ∈ Nr,
            (if (p.1 * p.2 = N ∧ e ∣ p.2) then D N * ‖f p‖ ^ 2 else 0) :=
          Finset.sum_comm
      _ = ∑ p ∈ G, D (p.1 * p.2) * ((E.filter (fun e => e ∣ p.2)).card : ℝ) * ‖f p‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_congr rfl
            (fun e _ => sum_ite_mul_collapse Nr p e D (‖f p‖ ^ 2) (hG p hp))]
          rw [sum_ite_dvd_eq E p.2 (D (p.1 * p.2) * ‖f p‖ ^ 2)]
          ring
  exact le_trans hstep1 (le_of_eq hreorganize)

theorem collapse_grid_coef_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K L : ℕ) (ξ : ℕ → ℕ → ℂ), 1 ≤ K → 1 ≤ L →
      (∑ e ∈ Finset.Icc 1 (K * L),
        ∑ N ∈ Finset.Icc 1 (K * L),
          ‖∑ p ∈ (Finset.Icc 1 K).product (Finset.Icc 1 L),
              (if (p.1 * p.2 = N ∧ e ∣ p.2) then ξ p.1 p.2 else 0)‖ ^ 2)
        ≤ C * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps
            * (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖ ^ 2) := by
  obtain ⟨c, hcpos, hc⟩ := card_divisors_le_const_mul_rpow eps heps
  refine ⟨c ^ 2, by positivity, ?_⟩
  intro K L ξ hK hL
  rw [Finset.product_eq_sprod]
  have hGmem : ∀ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L),
      p.1 * p.2 ∈ Finset.Icc 1 (K * L) := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_Icc] at hp1 hp2 ⊢
    exact ⟨by simpa using Nat.mul_le_mul hp1.1 hp2.1, Nat.mul_le_mul hp1.2 hp2.2⟩
  have hDcard : ∀ e N, N ∈ Finset.Icc 1 (K * L) →
      ((((Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = N ∧ e ∣ p.2)).card : ℝ)
        ≤ ((N.divisors.card : ℕ) : ℝ) := by
    intro e N hN
    have hN0 : N ≠ 0 := by have := (Finset.mem_Icc.mp hN).1; omega
    have := filter_prod_card_le_divisors_card K L N e hN0
    exact_mod_cast this
  have hcore := collapse_core (Finset.Icc 1 (K * L)) (Finset.Icc 1 (K * L))
    ((Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L)) (fun p => ξ p.1 p.2)
    (fun N => (N.divisors.card : ℝ)) hDcard hGmem
  refine le_trans hcore ?_
  have hterm : ∀ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L),
      ((p.1 * p.2).divisors.card : ℝ)
          * (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
          * ‖ξ p.1 p.2‖ ^ 2
        ≤ (c ^ 2 * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps) * ‖ξ p.1 p.2‖ ^ 2 := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_Icc] at hp1 hp2
    have hp2ne : p.2 ≠ 0 := by omega
    have hA : ((p.1 * p.2).divisors.card : ℝ) ≤ c * ((K : ℝ) * (L : ℝ)) ^ eps := by
      have h1 := hc (p.1 * p.2)
      rw [Nat.cast_mul] at h1
      refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hcpos.le)
      apply Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      · exact mul_le_mul (by exact_mod_cast hp1.2) (by exact_mod_cast hp2.2)
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact le_of_lt heps
    have hA0 : 0 ≤ ((p.1 * p.2).divisors.card : ℝ) := Nat.cast_nonneg _
    have hB : (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
        ≤ c * (L : ℝ) ^ eps := by
      have h1 : (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
          ≤ ((p.2).divisors.card : ℝ) := by
        have := filter_Icc_dvd_card_le_divisors_card (K * L) p.2 hp2ne
        exact_mod_cast this
      refine le_trans h1 (le_trans (hc p.2) (mul_le_mul_of_nonneg_left ?_ hcpos.le))
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hp2.2) (le_of_lt heps)
    have hB0 : 0 ≤ (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ) :=
      Nat.cast_nonneg _
    have hprod : ((p.1 * p.2).divisors.card : ℝ)
          * (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
        ≤ (c * ((K : ℝ) * (L : ℝ)) ^ eps) * (c * (L : ℝ) ^ eps) := by
      refine mul_le_mul hA hB hB0 ?_
      exact le_trans hA0 hA
    have hw0 : 0 ≤ ‖ξ p.1 p.2‖ ^ 2 := by positivity
    calc ((p.1 * p.2).divisors.card : ℝ)
          * (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
          * ‖ξ p.1 p.2‖ ^ 2
        ≤ ((c * ((K : ℝ) * (L : ℝ)) ^ eps) * (c * (L : ℝ) ^ eps)) * ‖ξ p.1 p.2‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hprod hw0
      _ = (c ^ 2 * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps) * ‖ξ p.1 p.2‖ ^ 2 := by
          ring
  calc (∑ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L),
          ((p.1 * p.2).divisors.card : ℝ)
            * (((Finset.Icc 1 (K * L)).filter (fun e => e ∣ p.2)).card : ℝ)
            * ‖ξ p.1 p.2‖ ^ 2)
      ≤ ∑ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L),
          (c ^ 2 * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps) * ‖ξ p.1 p.2‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (c ^ 2 * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps)
          * ∑ p ∈ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 L), ‖ξ p.1 p.2‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (c ^ 2 * ((K : ℝ) * (L : ℝ)) ^ eps * (L : ℝ) ^ eps)
          * (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖ ^ 2) := by
        rw [Finset.sum_product]

end Commons.Data.Nat