import Mathlib.Data.Int.Star
import Submission.Commons.NumberTheory.Gcd.gcd_sum_Icc_le

open Finset

namespace Commons.NumberTheory.CharacterSum

private theorem card_le_two_mul_add_one (s : Finset ℤ) (c r : ℝ) (hr : 0 ≤ r)
    (h : ∀ δ ∈ s, |(δ : ℝ) - c| ≤ r) : (s.card : ℝ) ≤ 2 * r + 1 := by
  have hsub : s ⊆ Finset.Icc (⌈c - r⌉) (⌊c + r⌋) := by
    intro z hz
    have hz' := h z hz
    rw [abs_le] at hz'
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Int.ceil_le]; linarith [hz'.1]
    · rw [Int.le_floor]; linarith [hz'.2]
  have h0 : 0 ≤ ⌊c + r⌋ + 1 - ⌈c - r⌉ := by
    have hcl : ⌈c - r⌉ ≤ ⌊c + r⌋ + 1 := by
      rw [Int.ceil_le]; push_cast
      have := Int.lt_floor_add_one (c + r)
      linarith
    omega
  have hle : (s.card : ℤ) ≤ ⌊c + r⌋ + 1 - ⌈c - r⌉ := by
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have h0' : ((⌊c + r⌋ + 1 - ⌈c - r⌉).toNat : ℤ) = ⌊c + r⌋ + 1 - ⌈c - r⌉ :=
      Int.toNat_of_nonneg h0
    have : (s.card : ℤ) ≤ ((⌊c + r⌋ + 1 - ⌈c - r⌉).toNat : ℤ) := by exact_mod_cast hcard
    rwa [h0'] at this
  have hle' : (s.card : ℝ) ≤ ((⌊c + r⌋ : ℤ) : ℝ) + 1 - ((⌈c - r⌉ : ℤ) : ℝ) := by
    have h2 : ((⌊c + r⌋ + 1 - ⌈c - r⌉ : ℤ) : ℝ)
        = ((⌊c + r⌋ : ℤ) : ℝ) + 1 - ((⌈c - r⌉ : ℤ) : ℝ) := by push_cast; ring
    rw [← h2]; exact_mod_cast hle
  have hfl : ((⌊c + r⌋ : ℤ) : ℝ) ≤ c + r := Int.floor_le _
  have hce : c - r ≤ ((⌈c - r⌉ : ℤ) : ℝ) := Int.le_ceil _
  linarith

private theorem card_linear_eq_le_gcd (l l' : ℕ) (δ : ℤ) :
    ((Finset.range l ×ˢ Finset.range l').filter
        (fun x => (x.1 : ℤ) * (l' : ℤ) - (x.2 : ℤ) * (l : ℤ) = δ)).card
      ≤ Nat.gcd l l' := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl; simp
  rcases Nat.eq_zero_or_pos l' with hl' | hl'
  · subst hl'; simp
  have hgpos : 0 < Nat.gcd l l' := Nat.gcd_pos_of_pos_left l' hl
  have hcop : Nat.Coprime (l / Nat.gcd l l') (l' / Nat.gcd l l') :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hgm : Nat.gcd l l' * (l / Nat.gcd l l') = l := Nat.mul_div_cancel' (Nat.gcd_dvd_left l l')
  have hgm' : Nat.gcd l l' * (l' / Nat.gcd l l') = l' := Nat.mul_div_cancel' (Nat.gcd_dvd_right l l')
  have hmpos : 0 < l / Nat.gcd l l' := Nat.pos_of_mul_pos_left (by rw [hgm]; exact hl)
  have key : ((Finset.range l ×ˢ Finset.range l').filter
        (fun x => (x.1 : ℤ) * (l' : ℤ) - (x.2 : ℤ) * (l : ℤ) = δ)).card
      ≤ (Finset.range (Nat.gcd l l')).card := by
    refine Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.1 / (l / Nat.gcd l l')) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_range]
      have hx1 : x.1 < l := by
        have := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
        exact Finset.mem_range.mp this
      rw [Nat.div_lt_iff_lt_mul hmpos, hgm]
      exact hx1
    · intro x hx y hy hxy
      have hx' : (x.1 : ℤ) * (l' : ℤ) - (x.2 : ℤ) * (l : ℤ) = δ := (Finset.mem_filter.mp hx).2
      have hy' : (y.1 : ℤ) * (l' : ℤ) - (y.2 : ℤ) * (l : ℤ) = δ := (Finset.mem_filter.mp hy).2
      have hEq : ((x.1 : ℤ) - (y.1 : ℤ)) * (l' : ℤ) = ((x.2 : ℤ) - (y.2 : ℤ)) * (l : ℤ) := by
        have h1 : (x.1 : ℤ) * (l' : ℤ) - (y.1 : ℤ) * (l' : ℤ)
            = (x.2 : ℤ) * (l : ℤ) - (y.2 : ℤ) * (l : ℤ) := by linarith
        rw [sub_mul, sub_mul]; exact h1
      have hgl : (l : ℤ) = (Nat.gcd l l' : ℤ) * ((l / Nat.gcd l l' : ℕ) : ℤ) := by
        rw [← Nat.cast_mul, hgm]
      have hgl' : (l' : ℤ) = (Nat.gcd l l' : ℤ) * ((l' / Nat.gcd l l' : ℕ) : ℤ) := by
        rw [← Nat.cast_mul, hgm']
      rw [hgl, hgl'] at hEq
      have hgne : (Nat.gcd l l' : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
      have hEq3 : ((x.1 : ℤ) - (y.1 : ℤ)) * ((l' / Nat.gcd l l' : ℕ) : ℤ)
          = ((x.2 : ℤ) - (y.2 : ℤ)) * ((l / Nat.gcd l l' : ℕ) : ℤ) := by
        apply mul_left_cancel₀ hgne
        linear_combination hEq
      have hdvd : ((l / Nat.gcd l l' : ℕ) : ℤ) ∣ ((x.1 : ℤ) - (y.1 : ℤ)) := by
        have h1 : ((l / Nat.gcd l l' : ℕ) : ℤ) ∣
            ((x.1 : ℤ) - (y.1 : ℤ)) * ((l' / Nat.gcd l l' : ℕ) : ℤ) := by
          rw [hEq3]; exact dvd_mul_left _ _
        exact (hcop.isCoprime).dvd_of_dvd_mul_right h1
      have hmod : x.1 ≡ y.1 [MOD l / Nat.gcd l l'] := by
        rw [Nat.modEq_iff_dvd]
        have h := dvd_neg.mpr hdvd
        simpa using h
      have hxy1 : x.1 = y.1 := by
        simp only at hxy
        have h1 : l / Nat.gcd l l' * (x.1 / (l / Nat.gcd l l')) + x.1 % (l / Nat.gcd l l')
            = l / Nat.gcd l l' * (y.1 / (l / Nat.gcd l l')) + y.1 % (l / Nat.gcd l l') := by
          rw [hxy, hmod]
        rwa [Nat.div_add_mod x.1 (l / Nat.gcd l l'),
             Nat.div_add_mod y.1 (l / Nat.gcd l l')] at h1
      have hxy2 : x.2 = y.2 := by
        have h2 : (x.2 : ℤ) * (l : ℤ) = (y.2 : ℤ) * (l : ℤ) := by
          have h1 : (x.1 : ℤ) = (y.1 : ℤ) := by exact_mod_cast hxy1
          rw [h1] at hx'
          linarith [hx', hy']
        have h2' : x.2 * l = y.2 * l := by exact_mod_cast h2
        exact Nat.mul_right_cancel hl h2'
      exact Prod.ext hxy1 hxy2
  rwa [Finset.card_range] at key

private lemma delta_bound (P p : ℕ) (N : ℤ) (h : ℕ) (hp : 0 < p)
    {l l' : ℕ} (hl : l ∈ Finset.Icc (P + 1) (2 * P))
    (hl' : l' ∈ Finset.Icc (P + 1) (2 * P))
    {a a' : ℕ}
    (hc : |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ) - (N - (a' : ℤ) * (p : ℤ)) / (l' : ℤ)| ≤ (h : ℤ)) :
    |(((a : ℤ) * (l' : ℤ) - (a' : ℤ) * (l : ℤ) : ℤ) : ℝ)
        - (N : ℝ) / (p : ℝ) * ((l' : ℝ) - (l : ℝ))|
      ≤ 4 * (P : ℝ) ^ 2 * ((h : ℝ) + 2) / (p : ℝ) := by
  have hll : P + 1 ≤ l := (Finset.mem_Icc.mp hl).1
  have hlr : l ≤ 2 * P := (Finset.mem_Icc.mp hl).2
  have hl'l : P + 1 ≤ l' := (Finset.mem_Icc.mp hl').1
  have hl'r : l' ≤ 2 * P := (Finset.mem_Icc.mp hl').2
  have hlz0 : (0:ℤ) < (l:ℤ) := by
    have hpos : 0 < l := by omega
    exact_mod_cast hpos
  have hlz0' : (0:ℤ) < (l':ℤ) := by
    have hpos : 0 < l' := by omega
    exact_mod_cast hpos
  have hlzne : (l:ℤ) ≠ 0 := hlz0.ne'
  have hlzne' : (l':ℤ) ≠ 0 := hlz0'.ne'
  set A : ℤ := N - (a : ℤ) * (p : ℤ) with hA
  set A' : ℤ := N - (a' : ℤ) * (p : ℤ) with hA'
  set Q : ℤ := A / (l : ℤ) with hQ
  set Q' : ℤ := A' / (l' : ℤ) with hQ'
  set R : ℤ := A % (l : ℤ) with hR
  set R' : ℤ := A' % (l' : ℤ) with hR'
  have hQeq : A = (l:ℤ) * Q + R := by rw [hQ, hR]; exact (Int.mul_ediv_add_emod A (l:ℤ)).symm
  have hQ'eq : A' = (l':ℤ) * Q' + R' := by rw [hQ', hR']; exact (Int.mul_ediv_add_emod A' (l':ℤ)).symm
  have hq : |Q - Q'| ≤ (h:ℤ) := by
    simpa only [hQ, hQ', hA, hA'] using hc
  have hR0 : 0 ≤ R := by rw [hR]; exact Int.emod_nonneg _ hlzne
  have hR1 : R < (l:ℤ) := by rw [hR]; exact Int.emod_lt_of_pos _ hlz0
  have hR'0 : 0 ≤ R' := by rw [hR']; exact Int.emod_nonneg _ hlzne'
  have hR'1 : R' < (l':ℤ) := by rw [hR']; exact Int.emod_lt_of_pos _ hlz0'
  have hUint : |A * (l':ℤ) - A' * (l:ℤ)| ≤ (l:ℤ)*(l':ℤ)*((h:ℤ)+2) := by
    have hdec : A * (l':ℤ) - A' * (l:ℤ)
        = (l:ℤ)*(l':ℤ)*(Q - Q') + (R*(l':ℤ) - R'*(l:ℤ)) := by
      rw [hQeq, hQ'eq]; ring
    have hp1 : (0:ℤ) ≤ (l:ℤ)*(l':ℤ) := by positivity
    have h1 : |(l:ℤ)*(l':ℤ)*(Q - Q')| = (l:ℤ)*(l':ℤ)*|Q - Q'| := by
      rw [abs_mul, abs_mul, abs_of_pos hlz0, abs_of_pos hlz0']
    have h2 : |(l:ℤ)*(l':ℤ)*(Q - Q')| ≤ (l:ℤ)*(l':ℤ)*(h:ℤ) := by
      rw [h1]; exact mul_le_mul_of_nonneg_left hq hp1
    have h3 : |R*(l':ℤ) - R'*(l:ℤ)| ≤ 2*((l:ℤ)*(l':ℤ)) := by
      have hle : |R*(l':ℤ) - R'*(l:ℤ)| ≤ R*(l':ℤ) + R'*(l:ℤ) := by
        rw [abs_le]
        constructor
        · nlinarith [mul_nonneg hR0 (le_of_lt hlz0'), mul_nonneg hR'0 (le_of_lt hlz0)]
        · nlinarith [mul_nonneg hR0 (le_of_lt hlz0'), mul_nonneg hR'0 (le_of_lt hlz0)]
      have hRle : R ≤ (l:ℤ) := le_of_lt hR1
      have hR'le : R' ≤ (l':ℤ) := le_of_lt hR'1
      have ha : R*(l':ℤ) ≤ (l:ℤ)*(l':ℤ) := mul_le_mul_of_nonneg_right hRle (le_of_lt hlz0')
      have hb : R'*(l:ℤ) ≤ (l':ℤ)*(l:ℤ) := mul_le_mul_of_nonneg_right hR'le (le_of_lt hlz0)
      nlinarith [hle, ha, hb]
    calc |A * (l':ℤ) - A' * (l:ℤ)|
        = |(l:ℤ)*(l':ℤ)*(Q - Q') + (R*(l':ℤ) - R'*(l:ℤ))| := by rw [hdec]
      _ ≤ |(l:ℤ)*(l':ℤ)*(Q - Q')| + |R*(l':ℤ) - R'*(l:ℤ)| := abs_add_le _ _
      _ ≤ (l:ℤ)*(l':ℤ)*(h:ℤ) + 2*((l:ℤ)*(l':ℤ)) := add_le_add h2 h3
      _ = (l:ℤ)*(l':ℤ)*((h:ℤ)+2) := by ring
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmain : (p:ℝ) * ((((a:ℤ)*(l':ℤ) - (a':ℤ)*(l:ℤ) : ℤ)) : ℝ)
      = (N:ℝ)*((l':ℝ)-(l:ℝ)) - (((N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  have hUreal : |(((N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ) : ℤ) : ℝ)|
      ≤ (l:ℝ)*(l':ℝ)*((h:ℝ)+2) := by
    have hcast : |(((N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ) : ℤ) : ℝ)|
        = ((|(N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ)| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [hcast]
    have h2 : ((|(N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ)| : ℤ) : ℝ)
        ≤ (((l:ℤ)*(l':ℤ)*((h:ℤ)+2) : ℤ) : ℝ) := by
      have hU' : |(N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ)|
          ≤ (l:ℤ)*(l':ℤ)*((h:ℤ)+2) := by simpa only [hA, hA'] using hUint
      exact_mod_cast hU'
    calc ((|(N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ)| : ℤ) : ℝ)
        ≤ (((l:ℤ)*(l':ℤ)*((h:ℤ)+2) : ℤ) : ℝ) := h2
      _ = (l:ℝ)*(l':ℝ)*((h:ℝ)+2) := by push_cast; ring
  have hdelta : ((((a:ℤ)*(l':ℤ) - (a':ℤ)*(l:ℤ) : ℤ)) : ℝ)
      - (N:ℝ)/(p:ℝ)*((l':ℝ)-(l:ℝ))
      = -(((N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ) : ℤ) : ℝ) / (p:ℝ) := by
    have := hmain
    field_simp
    linarith [this]
  have hpRpos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have habsp : |(p:ℝ)| = (p:ℝ) := abs_of_pos hpRpos
  rw [hdelta, abs_div, abs_neg, habsp]
  apply div_le_div_of_nonneg_right _ (le_of_lt hpRpos)
  have hlR : (l:ℝ) ≤ 2*(P:ℝ) := by
    have h : (l:ℝ) ≤ ((2*P : ℕ):ℝ) := by exact_mod_cast hlr
    simpa using h
  have hlR' : (l':ℝ) ≤ 2*(P:ℝ) := by
    have h : (l':ℝ) ≤ ((2*P : ℕ):ℝ) := by exact_mod_cast hl'r
    simpa using h
  have hl0 : (0:ℝ) ≤ (l:ℝ) := by positivity
  have hl0' : (0:ℝ) ≤ (l':ℝ) := by positivity
  have hh2 : (0:ℝ) ≤ (h:ℝ)+2 := by positivity
  have hmul : (l:ℝ)*(l':ℝ) ≤ (2*(P:ℝ))^2 := by nlinarith [hlR, hlR', hl0, hl0']
  calc |(((N - (a:ℤ)*(p:ℤ))*(l':ℤ) - (N - (a':ℤ)*(p:ℤ))*(l:ℤ) : ℤ) : ℝ)|
      ≤ (l:ℝ)*(l':ℝ)*((h:ℝ)+2) := hUreal
    _ ≤ (2*(P:ℝ))^2*((h:ℝ)+2) := mul_le_mul_of_nonneg_right hmul hh2
    _ = 4*(P:ℝ)^2*((h:ℝ)+2) := by ring


/-- Off-diagonal collision count for floors of `(N - a*p)/l`.

For `l, l'` ranging over the interval `[P+1, 2P]` and `a < l`, `a' < l'`, the number of
quadruples with `l ≠ l'` and `|⌊(N - a p)/l⌋ - ⌊(N - a' p)/l'⌋| ≤ h` is at most
`(8 P² (h+2)/p + 4) * (4 (2P)² (log (2P) + 1))`.

Mathematical content: such a quadruple forces `|(N/p)(l'-l) - (a l' - a' l)| ≤ 4P²(h+2)/p`,
so `a l' - a' l = δ` takes at most `2·(4P²(h+2)/p) + 1` values, and for each `δ` the number
of pairs `(a,a')` with `a l' - a' l = δ` is at most `gcd l l'`; the gcd-sum over `l,l' ≤ 2P`
is `≤ 4 (2P)² (log (2P) + 1)`. -/
theorem card_floor_close_offdiag (P p : ℕ) (N : ℤ) (h : ℕ) (hp : 0 < p) (hP : 1 ≤ P) :
    (∑ l ∈ Finset.Icc (P + 1) (2 * P), ∑ a ∈ Finset.range l,
      ∑ l' ∈ Finset.Icc (P + 1) (2 * P), ∑ a' ∈ Finset.range l',
        (if l ≠ l' ∧ |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
              - (N - (a' : ℤ) * (p : ℤ)) / (l' : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0))
    ≤ (8 * (P : ℝ) ^ 2 * ((h : ℝ) + 2) / (p : ℝ) + 4)
        * (4 * (2 * P : ℝ) ^ 2 * (Real.log (2 * P : ℝ) + 1)) := by
  let F : ℕ → ℕ → ℕ → ℕ → ℝ := fun l a l' a' =>
      if l ≠ l' ∧ |(N - (a : ℤ) * (p : ℤ)) / (l : ℤ)
            - (N - (a' : ℤ) * (p : ℤ)) / (l' : ℤ)| ≤ (h : ℤ) then (1 : ℝ) else 0
  let K : ℝ := 8 * (P : ℝ) ^ 2 * ((h : ℝ) + 2) / (p : ℝ) + 4
  let r : ℝ := 4 * (P : ℝ) ^ 2 * ((h : ℝ) + 2) / (p : ℝ)
  set S : Finset ℕ := Finset.Icc (P + 1) (2 * P) with hSdef
  have hS_eq : S = Finset.Icc (P + 1) (2 * P) := hSdef
  have hKnonneg : 0 ≤ K := by
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have : (0:ℝ) ≤ 8 * (P:ℝ)^2 * ((h:ℝ)+2)/(p:ℝ) := by positivity
    simp only [K]; linarith
  have hrK : 2 * r + 1 ≤ K := by
    have hK2 : K = 2 * r + 4 := by simp only [K, r]; ring
    rw [hK2]; linarith
  have hinner : ∀ l ∈ S, ∀ l' ∈ S,
      (∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a') ≤ K * (Nat.gcd l l' : ℝ) := by
    intro l hl l' hl'
    have hlI : l ∈ Finset.Icc (P + 1) (2 * P) := hS_eq ▸ hl
    have hl'I : l' ∈ Finset.Icc (P + 1) (2 * P) := hS_eq ▸ hl'
    by_cases hll : l = l'
    · subst hll
      have hzero : (∑ a ∈ range l, ∑ a' ∈ range l, F l a l a') = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        apply Finset.sum_eq_zero
        intro a' ha'
        simp only [F]
        simp
      rw [hzero]; positivity
    · set G : Finset (ℕ × ℕ) := (Finset.range l ×ˢ Finset.range l').filter
          (fun x : ℕ × ℕ => l ≠ l' ∧
            |(N - (x.1:ℤ)*(p:ℤ))/(l:ℤ) - (N - (x.2:ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)) with hGdef
      have hsum_eq : (∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a') = (G.card : ℝ) := by
        have hprod : (∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a')
            = ∑ x ∈ (range l ×ˢ range l'), (fun y : ℕ×ℕ => F l y.1 l' y.2) x := by
          rw [Finset.sum_product]
        rw [hprod, hGdef, Finset.card_eq_sum_ones]
        push_cast
        rw [Finset.sum_filter]
      have himg : ∀ δ ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)),
          |(δ:ℝ) - (N:ℝ)/(p:ℝ)*((l':ℝ)-(l:ℝ))| ≤ r := by
        intro δ hδ
        obtain ⟨x, hxG, hxδ⟩ := Finset.mem_image.mp hδ
        rw [← hxδ]
        rw [hGdef] at hxG
        have hcond := (Finset.mem_filter.mp hxG).2
        exact delta_bound P p N h hp hlI hl'I hcond.2
      have hrle : (0:ℝ) ≤ r := by
        have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
        simp only [r]; positivity
      have himgcard : ((G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ))).card : ℝ)
          ≤ 2 * r + 1 := card_le_two_mul_add_one _ _ _ hrle himg
      have hfiber : ∀ δ ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)),
          ((G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = δ)).card : ℝ) ≤ (Nat.gcd l l' : ℝ) := by
        intro δ hδ
        have hsub : G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = δ)
            ⊆ (Finset.range l ×ˢ Finset.range l').filter
                (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = δ) := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          refine ⟨?_, hx.2⟩
          rw [hGdef] at hx
          exact (Finset.mem_filter.mp hx.1).1
        calc ((G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = δ)).card : ℝ)
            ≤ (((Finset.range l ×ˢ Finset.range l').filter
                (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = δ)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub
          _ ≤ (Nat.gcd l l' : ℝ) := by exact_mod_cast card_linear_eq_le_gcd l l' δ
      have hcard_le : (G.card : ℝ)
          ≤ ((G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ))).card : ℝ) * (Nat.gcd l l' : ℝ) := by
        have hmap : Set.MapsTo (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)) ↑G
            ↑(G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ))) :=
          fun x hx => Finset.mem_image_of_mem _ hx
        rw [Finset.card_eq_sum_card_fiberwise hmap]
        push_cast
        rw [show (∑ y ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)),
              ↑(G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = y)).card : ℝ)
            = ∑ y ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)),
              ((G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = y)).card : ℝ) from rfl]
        calc (∑ y ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)),
                ((G.filter (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ) = y)).card : ℝ))
            ≤ ∑ y ∈ G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ)), (Nat.gcd l l' : ℝ) :=
              Finset.sum_le_sum (fun y hy => hfiber y hy)
          _ = ((G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ))).card : ℝ) * (Nat.gcd l l' : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_eq]
      calc (G.card : ℝ)
          ≤ ((G.image (fun x : ℕ×ℕ => (x.1:ℤ)*(l':ℤ) - (x.2:ℤ)*(l:ℤ))).card : ℝ) * (Nat.gcd l l' : ℝ) := hcard_le
        _ ≤ (2 * r + 1) * (Nat.gcd l l' : ℝ) := mul_le_mul_of_nonneg_right himgcard (by positivity)
        _ ≤ K * (Nat.gcd l l' : ℝ) := mul_le_mul_of_nonneg_right hrK (by positivity)
  have hswap : (∑ l ∈ S, ∑ a ∈ range l, ∑ l' ∈ S, ∑ a' ∈ range l', F l a l' a')
      = (∑ l ∈ S, ∑ l' ∈ S, ∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a') := by
    apply Finset.sum_congr rfl
    intro l hl
    exact Finset.sum_comm
  have houter : (∑ l ∈ S, ∑ l' ∈ S, ∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a')
      ≤ K * (4 * (2 * P : ℝ) ^ 2 * (Real.log (2 * P : ℝ) + 1)) := by
    have step1 : (∑ l ∈ S, ∑ l' ∈ S, ∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a')
        ≤ ∑ l ∈ S, ∑ l' ∈ S, K * (Nat.gcd l l' : ℝ) := by
      apply Finset.sum_le_sum; intro l hl
      apply Finset.sum_le_sum; intro l' hl'
      exact hinner l hl l' hl'
    have step2 : (∑ l ∈ S, ∑ l' ∈ S, K * (Nat.gcd l l' : ℝ))
        = K * (∑ l ∈ S, ∑ l' ∈ S, (Nat.gcd l l' : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
    have hgcd : (∑ l ∈ S, ∑ l' ∈ S, (Nat.gcd l l' : ℝ))
        ≤ 4 * (2 * P : ℝ) ^ 2 * (Real.log (2 * P : ℝ) + 1) := by
      have h := Commons.NumberTheory.Gcd.gcd_sum_Icc_le (P+1) (2*P) (by omega) (by omega)
      rw [hSdef]
      refine le_trans h (le_of_eq ?_)
      push_cast
      ring_nf
    calc (∑ l ∈ S, ∑ l' ∈ S, ∑ a ∈ range l, ∑ a' ∈ range l', F l a l' a')
        ≤ ∑ l ∈ S, ∑ l' ∈ S, K * (Nat.gcd l l' : ℝ) := step1
      _ = K * (∑ l ∈ S, ∑ l' ∈ S, (Nat.gcd l l' : ℝ)) := step2
      _ ≤ K * (4 * (2 * P : ℝ) ^ 2 * (Real.log (2 * P : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hgcd hKnonneg
  show (∑ l ∈ S, ∑ a ∈ range l, ∑ l' ∈ S, ∑ a' ∈ range l', F l a l' a')
      ≤ K * (4 * (2 * P : ℝ) ^ 2 * (Real.log (2 * P : ℝ) + 1))
  rw [hswap]
  exact houter

end Commons.NumberTheory.CharacterSum