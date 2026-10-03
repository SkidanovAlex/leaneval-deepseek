import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Work.FIArea2.sum_tau_pow_div_le

namespace Work.FIArea3

open Finset

noncomputable section

/-
# The double `τ⁸`-weighted `lcm`-divisor sum of the Friedlander–Iwaniec analysis

We prove

  `∃ C > 0, ∀ K, ∑_{d ≤ K} ∑_{e ≤ K} τ(d)⁸ τ(e)⁸ τ(lcm(d,e)) / lcm(d,e) ≤ C (log K + 2)^{132096}`.

The proof is the gcd-splitting of the pair `(d,e)`: writing `g = gcd d e`, `d = g a`, `e = g b`
with `(a,b) = 1` and `lcm(d,e) = g a b`, submultiplicativity `τ(mn) ≤ τ(m)τ(n)` gives the pointwise
bound

  `τ(d)⁸τ(e)⁸ τ(lcm d e)/lcm(d,e) ≤ (τ(g)¹⁷/g)·(τ(a)⁹/a)·(τ(b)⁹/b)`,

and the pairs `(d,e) ∈ [1,K]²` correspond injectively to triples `(g,a,b) ∈ [1,K]³`, so the double
sum is bounded by `(∑_{g≤K} τ(g)¹⁷/g)·(∑_{a≤K} τ(a)⁹/a)²`; the classical bound
`∑_{n ≤ X} τ(n)^k/n ≤ C (log X + 2)^{2^k}` of `Work.FIArea2.sum_tau_pow_div_le` then gives
`(log K + 2)^{2¹⁷}·(log K + 2)^{2·2⁹} = (log K + 2)^{131072 + 1024} = (log K + 2)^{132096}`.
-/

/-- `τ(g)^{17}/g`, the weight attached to `g = gcd(d,e)` after submultiplicativity. -/
private def tauG (g : ℕ) : ℝ := ((g.divisors.card : ℝ)) ^ (17 : ℕ) / (g : ℝ)

/-- `τ(n)^{9}/n`, the weight attached to the two cofactors. -/
private def tauA (n : ℕ) : ℝ := ((n.divisors.card : ℝ)) ^ (9 : ℕ) / (n : ℝ)

/-- The parametrisation of a pair by its gcd and the two cofactors. -/
private def tauPhi (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  ((Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2), p.2 / Nat.gcd p.1 p.2)

/-- The summand of the target sum, as a function of the pair. -/
private def tauB (p : ℕ × ℕ) : ℝ :=
  (((p.1.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((p.2.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
    * ((((Nat.lcm p.1 p.2).divisors.card : ℕ) : ℝ) / ((Nat.lcm p.1 p.2 : ℕ) : ℝ))

private lemma tauG_nonneg (g : ℕ) : 0 ≤ tauG g := by
  rw [tauG]; positivity

private lemma tauA_nonneg (n : ℕ) : 0 ≤ tauA n := by
  rw [tauA]; positivity

/-- `lcm (g a) (g b) = g a b` for coprime `a,b`. -/
private lemma lcm_mul_of_coprime (g a b : ℕ) (h : Nat.Coprime a b) :
    Nat.lcm (g * a) (g * b) = g * (a * b) := by
  rw [Nat.lcm_mul_left, h.lcm_eq_mul]

/-- **Pointwise gcd-split.**  For `g,a,b ≥ 1` and `(a,b) = 1`,
`τ(ga)⁸ τ(gb)⁸ τ(lcm(ga,gb))/lcm(ga,gb) ≤ (τ(g)¹⁷/g)(τ(a)⁹/a)(τ(b)⁹/b)`. -/
private lemma tau_key (g a b : ℕ) (hg : 1 ≤ g) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : Nat.Coprime a b) :
    (((g * a).divisors.card : ℝ)) ^ (8 : ℕ) * (((g * b).divisors.card : ℝ)) ^ (8 : ℕ)
        * ((((Nat.lcm (g * a) (g * b)).divisors.card : ℕ) : ℝ)
            / ((Nat.lcm (g * a) (g * b) : ℕ) : ℝ))
      ≤ (((g.divisors.card : ℝ)) ^ (17 : ℕ) / (g : ℝ))
          * ((((a.divisors.card : ℝ)) ^ (9 : ℕ)) / (a : ℝ))
          * ((((b.divisors.card : ℝ)) ^ (9 : ℕ)) / (b : ℝ)) := by
  have hnat : (g * a).divisors.card ^ 8 * (g * b).divisors.card ^ 8 * (g * (a * b)).divisors.card
      ≤ g.divisors.card ^ 17 * a.divisors.card ^ 9 * b.divisors.card ^ 9 := by
    have h1 : (g * a).divisors.card ^ 8 ≤ g.divisors.card ^ 8 * a.divisors.card ^ 8 :=
      calc (g * a).divisors.card ^ 8
          ≤ (g.divisors.card * a.divisors.card) ^ 8 :=
            Nat.pow_le_pow_left
              (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le g a) 8
        _ = g.divisors.card ^ 8 * a.divisors.card ^ 8 := mul_pow _ _ _
    have h2 : (g * b).divisors.card ^ 8 ≤ g.divisors.card ^ 8 * b.divisors.card ^ 8 :=
      calc (g * b).divisors.card ^ 8
          ≤ (g.divisors.card * b.divisors.card) ^ 8 :=
            Nat.pow_le_pow_left
              (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le g b) 8
        _ = g.divisors.card ^ 8 * b.divisors.card ^ 8 := mul_pow _ _ _
    have h3 : (g * (a * b)).divisors.card
        ≤ g.divisors.card * (a.divisors.card * b.divisors.card) :=
      le_trans (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le g (a * b))
        (Nat.mul_le_mul_left _ (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le a b))
    calc (g * a).divisors.card ^ 8 * (g * b).divisors.card ^ 8 * (g * (a * b)).divisors.card
        ≤ (g.divisors.card ^ 8 * a.divisors.card ^ 8) * (g.divisors.card ^ 8 * b.divisors.card ^ 8)
            * (g.divisors.card * (a.divisors.card * b.divisors.card)) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = g.divisors.card ^ 17 * a.divisors.card ^ 9 * b.divisors.card ^ 9 := by ring
  have hnatR : (((g * a).divisors.card : ℝ)) ^ (8 : ℕ) * (((g * b).divisors.card : ℝ)) ^ (8 : ℕ)
      * ((g * (a * b)).divisors.card : ℝ)
      ≤ ((g.divisors.card : ℝ)) ^ (17 : ℕ) * ((a.divisors.card : ℝ)) ^ (9 : ℕ)
        * ((b.divisors.card : ℝ)) ^ (9 : ℕ) := by
    exact_mod_cast hnat
  have hL : (0 : ℝ) < ((g * (a * b) : ℕ) : ℝ) := by
    have h : 0 < g * (a * b) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    exact_mod_cast h
  have hsplit : (((g.divisors.card : ℝ)) ^ (17 : ℕ) / (g : ℝ))
        * ((((a.divisors.card : ℝ)) ^ (9 : ℕ)) / (a : ℝ))
        * ((((b.divisors.card : ℝ)) ^ (9 : ℕ)) / (b : ℝ))
      = (((g.divisors.card : ℝ)) ^ (17 : ℕ) * ((a.divisors.card : ℝ)) ^ (9 : ℕ)
          * ((b.divisors.card : ℝ)) ^ (9 : ℕ)) / ((g * (a * b) : ℕ) : ℝ) := by
    have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  rw [lcm_mul_of_coprime g a b hcop, hsplit, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnatR hL.le

/-- The map `(d,e) ↦ (gcd d e, d/gcd, e/gcd)` is injective on the box `[1,K]²`. -/
private lemma tauPhi_inj (K : ℕ) :
    Set.InjOn tauPhi ↑(Finset.Icc 1 K ×ˢ Finset.Icc 1 K) := by
  intro p _ q _ hpq
  have h1 : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2 := by
    have h := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.1) hpq
    simpa only [tauPhi] using h
  have h2 : p.1 / Nat.gcd p.1 p.2 = q.1 / Nat.gcd q.1 q.2 := by
    have h := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.2) hpq
    simpa only [tauPhi] using h
  have h3 : p.2 / Nat.gcd p.1 p.2 = q.2 / Nat.gcd q.1 q.2 := by
    have h := congrArg (fun t : (ℕ × ℕ) × ℕ => t.2) hpq
    simpa only [tauPhi] using h
  have e1 : p.1 = q.1 := by
    calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
      _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [h2, h1]
      _ = q.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left q.1 q.2)
  have e2 : p.2 = q.2 := by
    calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
      _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [h3, h1]
      _ = q.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right q.1 q.2)
  exact Prod.ext e1 e2

/-- The parametrisation lands in the box `[1,K]³`. -/
private lemma tauPhi_mem (K : ℕ) :
    ∀ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
      tauPhi p ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K := by
  intro p hp
  have hpp := Finset.mem_product.mp hp
  have hp1 : 1 ≤ p.1 ∧ p.1 ≤ K := Finset.mem_Icc.mp hpp.1
  have hp2 : 1 ≤ p.2 ∧ p.2 ≤ K := Finset.mem_Icc.mp hpp.2
  have h1pos : 0 < p.1 := by omega
  have h2pos : 0 < p.2 := by omega
  have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 h1pos
  have hg1 : 1 ≤ Nat.gcd p.1 p.2 := Nat.one_le_iff_ne_zero.mpr hgpos.ne'
  have hgle : Nat.gcd p.1 p.2 ≤ K := le_trans (Nat.gcd_le_left p.2 h1pos) hp1.2
  have ha1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 :=
    Nat.div_pos (Nat.le_of_dvd h1pos (Nat.gcd_dvd_left p.1 p.2)) hgpos
  have hale : p.1 / Nat.gcd p.1 p.2 ≤ K := le_trans (Nat.div_le_self p.1 _) hp1.2
  have hb1 : 1 ≤ p.2 / Nat.gcd p.1 p.2 :=
    Nat.div_pos (Nat.le_of_dvd h2pos (Nat.gcd_dvd_right p.1 p.2)) hgpos
  have hble : p.2 / Nat.gcd p.1 p.2 ≤ K := le_trans (Nat.div_le_self p.2 _) hp2.2
  show ((Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2), p.2 / Nat.gcd p.1 p.2)
      ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hg1, hgle⟩, Finset.mem_Icc.mpr ⟨ha1, hale⟩⟩,
      Finset.mem_Icc.mpr ⟨hb1, hble⟩⟩

/-- **Reindexing.**  An injective map from the box `[1,K]²` into the box `[1,K]³`, together with
nonnegative weights, gives the factorised bound. -/
private lemma sum_image_le_triple {φ : ℕ × ℕ → (ℕ × ℕ) × ℕ} (K : ℕ) (G A : ℕ → ℝ)
    (hG : ∀ g, 0 ≤ G g) (hA : ∀ a, 0 ≤ A a)
    (hinj : Set.InjOn φ ↑(Finset.Icc 1 K ×ˢ Finset.Icc 1 K))
    (himg : ∀ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
      φ p ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K) :
    (∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, G (φ p).1.1 * A (φ p).1.2 * A (φ p).2)
      ≤ (∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a)
          * (∑ b ∈ Finset.Icc 1 K, A b) := by
  have hstep1 : (∑ q ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K).image φ,
        G q.1.1 * A q.1.2 * A q.2)
      = ∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
          G (φ p).1.1 * A (φ p).1.2 * A (φ p).2 :=
    Finset.sum_image hinj
  rw [← hstep1]
  have hsub : (Finset.Icc 1 K ×ˢ Finset.Icc 1 K).image φ
      ⊆ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact himg p hp
  have hpair : (∑ x ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, G x.1 * A x.2)
      = (∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a) := by
    rw [Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.mul_sum]
  have hfac : (∑ q ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K,
        G q.1.1 * A q.1.2 * A q.2)
      = (∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a)
          * (∑ b ∈ Finset.Icc 1 K, A b) := by
    rw [Finset.sum_product]
    have hinner : ∀ x ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
        (∑ b ∈ Finset.Icc 1 K, G x.1 * A x.2 * A b)
          = (G x.1 * A x.2) * (∑ b ∈ Finset.Icc 1 K, A b) := by
      intro x _
      rw [Finset.mul_sum]
    calc (∑ x ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
            ∑ b ∈ Finset.Icc 1 K, G x.1 * A x.2 * A b)
        = ∑ x ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
            (G x.1 * A x.2) * (∑ b ∈ Finset.Icc 1 K, A b) :=
          Finset.sum_congr rfl hinner
      _ = (∑ x ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, G x.1 * A x.2)
            * (∑ b ∈ Finset.Icc 1 K, A b) := by rw [← Finset.sum_mul]
      _ = ((∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a))
            * (∑ b ∈ Finset.Icc 1 K, A b) := by rw [hpair]
      _ = (∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a)
            * (∑ b ∈ Finset.Icc 1 K, A b) := rfl
  calc (∑ q ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K).image φ,
        G q.1.1 * A q.1.2 * A q.2)
      ≤ ∑ q ∈ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K) ×ˢ Finset.Icc 1 K,
          G q.1.1 * A q.1.2 * A q.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun q _ _ => mul_nonneg (mul_nonneg (hG _) (hA _)) (hA _))
    _ = (∑ g ∈ Finset.Icc 1 K, G g) * (∑ a ∈ Finset.Icc 1 K, A a)
          * (∑ b ∈ Finset.Icc 1 K, A b) := hfac

theorem lcmTauDivBound :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ)))
        ≤ C * (Real.log (K : ℝ) + 2) ^ (132096 : ℕ) := by
  obtain ⟨C17, hC17pos, hC17⟩ := Work.FIArea2.sum_tau_pow_div_le 17
  obtain ⟨C9, hC9pos, hC9⟩ := Work.FIArea2.sum_tau_pow_div_le 9
  refine ⟨C17 * C9 * C9, by positivity, fun K => ?_⟩
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hzero : (∑ d ∈ Finset.Icc 1 0, ∑ e ∈ Finset.Icc 1 0,
        (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
          * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ))) = 0 := by
      simp
    rw [hzero, Nat.cast_zero, Real.log_zero]
    positivity
  · have hpoint : ∀ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K,
        tauB p ≤ tauG (tauPhi p).1.1 * tauA (tauPhi p).1.2 * tauA (tauPhi p).2 := by
      intro p hp
      have hpp := Finset.mem_product.mp hp
      have hp1 : 1 ≤ p.1 ∧ p.1 ≤ K := Finset.mem_Icc.mp hpp.1
      have hp2 : 1 ≤ p.2 ∧ p.2 ≤ K := Finset.mem_Icc.mp hpp.2
      have h1pos : 0 < p.1 := by omega
      have h2pos : 0 < p.2 := by omega
      have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 h1pos
      have hg1 : 1 ≤ Nat.gcd p.1 p.2 := Nat.one_le_iff_ne_zero.mpr hgpos.ne'
      have ha1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 :=
        Nat.div_pos (Nat.le_of_dvd h1pos (Nat.gcd_dvd_left p.1 p.2)) hgpos
      have hb1 : 1 ≤ p.2 / Nat.gcd p.1 p.2 :=
        Nat.div_pos (Nat.le_of_dvd h2pos (Nat.gcd_dvd_right p.1 p.2)) hgpos
      have hcop : Nat.Coprime (p.1 / Nat.gcd p.1 p.2) (p.2 / Nat.gcd p.1 p.2) :=
        Nat.coprime_div_gcd_div_gcd hgpos
      have hma : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
      have hmb : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
      have hkey := tau_key (Nat.gcd p.1 p.2) (p.1 / Nat.gcd p.1 p.2) (p.2 / Nat.gcd p.1 p.2)
        hg1 ha1 hb1 hcop
      simpa only [tauB, tauG, tauA, tauPhi, hma, hmb] using hkey
    have hprod : (∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, tauB p)
        ≤ (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
            * (∑ b ∈ Finset.Icc 1 K, tauA b) :=
      le_trans (Finset.sum_le_sum hpoint)
        (sum_image_le_triple K tauG tauA tauG_nonneg tauA_nonneg (tauPhi_inj K) (tauPhi_mem K))
    have hGs : (∑ g ∈ Finset.Icc 1 K, tauG g) ≤ C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17) := by
      simpa only [tauG] using hC17 K
    have hAs : (∑ a ∈ Finset.Icc 1 K, tauA a) ≤ C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9) := by
      simpa only [tauA] using hC9 K
    have hAsnn : (0 : ℝ) ≤ ∑ a ∈ Finset.Icc 1 K, tauA a :=
      Finset.sum_nonneg (fun a _ => tauA_nonneg a)
    have hLnn : (0 : ℝ) ≤ Real.log (K : ℝ) + 2 := by
      have h1 : (0 : ℝ) ≤ Real.log (K : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hKpos)
      linarith
    have h17nn : (0 : ℝ) ≤ C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17) :=
      mul_nonneg hC17pos.le (pow_nonneg hLnn _)
    have h9nn : (0 : ℝ) ≤ C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9) :=
      mul_nonneg hC9pos.le (pow_nonneg hLnn _)
    have hstep2 : (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
          * (∑ b ∈ Finset.Icc 1 K, tauA b)
        ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) := by
      have h1 : (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
          ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) :=
        calc (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
            ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17)) * (∑ a ∈ Finset.Icc 1 K, tauA a) :=
              mul_le_mul_of_nonneg_right hGs hAsnn
          _ ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
                * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) :=
              mul_le_mul_of_nonneg_left hAs h17nn
      calc (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
            * (∑ b ∈ Finset.Icc 1 K, tauA b)
          ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) * (∑ b ∈ Finset.Icc 1 K, tauA b) :=
            mul_le_mul_of_nonneg_right h1 hAsnn
        _ ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) :=
            mul_le_mul_of_nonneg_left hAs (mul_nonneg h17nn h9nn)
    have hexp : (2 : ℕ) ^ 17 + 2 ^ 9 + 2 ^ 9 = 132096 := by norm_num
    have hstep3 : (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
          * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
          * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
        = (C17 * C9 * C9) * (Real.log (K : ℝ) + 2) ^ (132096 : ℕ) := by
      calc (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
          = (C17 * C9 * C9) * ((Real.log (K : ℝ) + 2) ^ (2 ^ 17)
              * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)
              * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) := by ac_rfl
        _ = (C17 * C9 * C9) * (Real.log (K : ℝ) + 2) ^ (2 ^ 17 + 2 ^ 9 + 2 ^ 9) := by
              rw [← pow_add, ← pow_add]
        _ = (C17 * C9 * C9) * (Real.log (K : ℝ) + 2) ^ (132096 : ℕ) := by rw [hexp]
    calc (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / ((Nat.lcm d e : ℕ) : ℝ)))
        = ∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, tauB p := by
          rw [Finset.sum_product]
          rfl
      _ ≤ (∑ g ∈ Finset.Icc 1 K, tauG g) * (∑ a ∈ Finset.Icc 1 K, tauA a)
            * (∑ b ∈ Finset.Icc 1 K, tauA b) := hprod
      _ ≤ (C17 * (Real.log (K : ℝ) + 2) ^ (2 ^ 17))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
            * (C9 * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) := hstep2
      _ = (C17 * C9 * C9) * (Real.log (K : ℝ) + 2) ^ (132096 : ℕ) := hstep3

end

end Work.FIArea3
