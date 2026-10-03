import Mathlib
import Submission.Work.FIArea4.jacobi_congruence_count

namespace Work.FIArea4.Vflip

open Finset

/-- The number of elements of an interval `Ioc lo (lo+m)` lying in one fixed residue
class modulo `k` is at most `m / k + 1`. -/
lemma card_filter_mod_Ioc_le (lo m k c : ℕ) (hk : 0 < k) :
    ((Finset.Ioc lo (lo + m)).filter (fun s => s % k = c)).card ≤ m / k + 1 := by
  set T : Finset ℕ := (Finset.Ioc lo (lo + m)).filter (fun s => s % k = c) with hT
  have hsub : ∀ s ∈ T, s ∈ Finset.Ioc lo (lo + m) := fun s hs => (Finset.mem_filter.mp hs).1
  have hmod : ∀ s ∈ T, s % k = c := fun s hs => (Finset.mem_filter.mp hs).2
  have hmem : ∀ s ∈ T, lo < s ∧ s ≤ lo + m := fun s hs => Finset.mem_Ioc.mp (hsub s hs)
  have hkdiv : ∀ a : ℕ, (a + k) / k = a / k + 1 := by
    intro a
    have := Nat.add_mul_div_left a 1 hk
    simpa using this
  have hstrict : ∀ x ∈ T, ∀ y ∈ T, x < y → (x - lo - 1) / k < (y - lo - 1) / k := by
    intro x hx y hy hxy
    obtain ⟨hx1, _⟩ := hmem x hx
    obtain ⟨hy1, _⟩ := hmem y hy
    have hme : x ≡ y [MOD k] := by
      show x % k = y % k
      rw [hmod x hx, hmod y hy]
    have hdvd : k ∣ y - x := by
      have hle : x ≤ y := le_of_lt hxy
      have hz : (k : ℤ) ∣ (y : ℤ) - (x : ℤ) := Nat.modEq_iff_dvd.mp hme
      rw [← Nat.cast_sub hle] at hz
      exact Int.natCast_dvd_natCast.mp hz
    have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
    have hkle : k ≤ y - x := Nat.le_of_dvd hpos hdvd
    have hle2 : x - lo - 1 + k ≤ y - lo - 1 := by omega
    calc (x - lo - 1) / k < (x - lo - 1 + k) / k := by rw [hkdiv]; omega
      _ ≤ (y - lo - 1) / k := Nat.div_le_div_right hle2
  have hinj : Set.InjOn (fun s => (s - lo - 1) / k) (T : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (ne_of_lt (hstrict x hx y hy h))
    · exact h
    · exact absurd hxy.symm (ne_of_lt (hstrict y hy x hx h))
  have himg : T.image (fun s => (s - lo - 1) / k) ⊆ Finset.Icc 0 (m / k) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    obtain ⟨hs1, hs2⟩ := hmem s hs
    refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
    have hle : s - lo - 1 ≤ m - 1 := by omega
    calc (s - lo - 1) / k ≤ (m - 1) / k := Nat.div_le_div_right hle
      _ ≤ m / k := Nat.div_le_div_right (by omega)
  calc T.card = (T.image (fun s => (s - lo - 1) / k)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 0 (m / k)).card := Finset.card_le_card himg
    _ = m / k + 1 := by simp [Nat.card_Icc]

/-- A finset of positive multiples of `k`, all bounded by `M`, has at most `M / k` elements. -/
lemma card_multiples_le (M k : ℕ) (hk : 0 < k) (T : Finset ℕ)
    (hT : ∀ x ∈ T, k ∣ x) (hT1 : ∀ x ∈ T, 1 ≤ x) (hT2 : ∀ x ∈ T, x ≤ M) :
    T.card ≤ M / k := by
  have hinj : Set.InjOn (fun x => x / k) (T : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    change x / k = y / k at hxy
    rw [← Nat.div_mul_cancel (hT x hx), ← Nat.div_mul_cancel (hT y hy), hxy]
  have himg : T.image (fun x => x / k) ⊆ Finset.Icc 1 (M / k) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right (hT2 x hx)⟩
    obtain ⟨t, ht⟩ := hT x hx
    have htpos : 1 ≤ t := by
      have hx1 : 1 ≤ x := hT1 x hx
      by_contra hlt
      have hlt' : t < 1 := not_le.mp hlt
      have ht0 : t = 0 := by omega
      rw [ht0, mul_zero] at ht
      omega
    rw [ht, Nat.mul_div_right t hk]
    exact htpos
  calc T.card = (T.image (fun x => x / k)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (M / k)).card := Finset.card_le_card himg
    _ = M / k := by simp [Nat.card_Icc]

/-- Elementary division estimate: `2*m/d ≤ 2*(m/d) + 1`. -/
lemma two_mul_div_le (m d : ℕ) (hd : 0 < d) : 2 * m / d ≤ 2 * (m / d) + 1 := by
  have h : 2 * m / d < 2 * (m / d) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    have h1 : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
    have h2 : m % d < d := Nat.mod_lt m hd
    nlinarith [h1, h2]
  omega

theorem count_coset_supp (R S d a : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hd : 1 ≤ d) :
    (((Finset.Ioc R (2 * R)).product (Finset.Ioc (S / 2) (5 * S / 2))).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card
      ≤ 10 * (((R * S) / d : ℕ) + min R S + 1) := by
  have hd0 : 0 < d := by omega
  set A : Finset ℕ := Finset.Ioc R (2 * R) with hA
  set B : Finset ℕ := Finset.Ioc (S / 2) (5 * S / 2) with hB
  set C : ℕ := ((A.product B).filter (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card with hC
  have hBS : 5 * S / 2 = S / 2 + 2 * S := by
    have h : 5 * S = S + 2 * (2 * S) := by ring
    rw [h, Nat.add_mul_div_left S (2 * S) (by norm_num : 0 < 2)]
  have hA2 : 2 * R = R + R := by ring
  have hcardB : B.card = 2 * S := by
    rw [hB, Nat.card_Ioc, hBS]; omega
  set q : ℕ := R * S / d with hq
  rcases le_total R S with hRS | hSR
  · -- Case R ≤ S : use the per-`r` fibre bound.
    have hcardA : A.card = R := by rw [hA, Nat.card_Ioc]; omega
    have hperr : C ≤ R * (2 * S / d + 1) := by
      rw [hC, Work.FIArea4.card_filter_product_eq_sum_fst]
      have hb : ∀ r ∈ A, (B.filter (fun s => s % d = (r * a) % d)).card ≤ 2 * S / d + 1 := by
        intro r _
        have := card_filter_mod_Ioc_le (S / 2) (2 * S) d ((r * a) % d) hd0
        rw [hB, hBS]
        exact this
      calc ∑ r ∈ A, (B.filter (fun s => s % d = (r * a) % d)).card
          ≤ ∑ _r ∈ A, (2 * S / d + 1) := Finset.sum_le_sum hb
        _ = A.card * (2 * S / d + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = R * (2 * S / d + 1) := by rw [hcardA]
    have hR2 : R * (2 * S / d) ≤ 2 * q + 1 := by
      have h1 : R * (2 * S / d) ≤ R * (2 * S) / d := Nat.mul_div_le_mul_div_assoc R (2 * S) d
      have h2 : R * (2 * S) = 2 * (R * S) := by ring
      rw [h2] at h1
      have h3 : 2 * (R * S) / d ≤ 2 * (R * S / d) + 1 := two_mul_div_le (R * S) d hd0
      rw [hq]
      exact le_trans h1 h3
    calc C ≤ R * (2 * S / d + 1) := hperr
      _ = R * (2 * S / d) + R := by ring
      _ ≤ 2 * q + 1 + R := by omega
      _ ≤ 10 * (q + R + 1) := by omega
      _ = 10 * (R * S / d + min R S + 1) := by rw [hq, min_eq_left hRS]
  · -- Case S ≤ R : use the per-`s` fibre bound with the gcd reduction.
    set g : ℕ := Nat.gcd a d with hg
    set h : ℕ := d / g with hh
    have hgd : g ∣ d := by rw [hg]; exact Nat.gcd_dvd_right a d
    have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right a hd0
    have hhpos : 0 < h := by
      rw [hh]; exact Nat.div_pos (Nat.le_of_dvd hd0 hgd) hgpos
    have hgh : g * h = d := by
      rw [hh, mul_comm]
      rw [hg]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right a d)
    have hdga : d.gcd a = g := by rw [hg]; exact Nat.gcd_comm d a
    have hmodh : d / d.gcd a = h := by rw [hdga, hh]
    set n : ℕ := (B.filter (fun s => g ∣ s)).card with hn
    have hpers : C ≤ n * (R / h + 1) := by
      rw [hC, Work.FIArea4.card_filter_product_eq_sum_snd]
      have hb : ∀ s ∈ B, (A.filter (fun r => s % d = (r * a) % d)).card ≤
          (if g ∣ s then R / h + 1 else 0) := by
        intro s _
        by_cases hgs : g ∣ s
        · rw [if_pos hgs]
          by_cases hne : (A.filter (fun r => s % d = (r * a) % d)).Nonempty
          · obtain ⟨r0, hr0⟩ := hne
            have hr0' : s % d = (r0 * a) % d := (Finset.mem_filter.mp hr0).2
            have hsub : A.filter (fun r => s % d = (r * a) % d) ⊆
                A.filter (fun r => r % h = r0 % h) := by
              intro r hr
              rw [Finset.mem_filter] at hr ⊢
              refine ⟨hr.1, ?_⟩
              have hr' : s % d = (r * a) % d := hr.2
              have hme : r * a ≡ r0 * a [MOD d] := by
                show (r * a) % d = (r0 * a) % d
                rw [← hr', ← hr0']
              have hcan := Nat.ModEq.cancel_right_div_gcd hd0 hme
              rw [hmodh] at hcan
              exact hcan
            calc (A.filter (fun r => s % d = (r * a) % d)).card
                ≤ (A.filter (fun r => r % h = r0 % h)).card := Finset.card_le_card hsub
              _ ≤ R / h + 1 := by
                  rw [hA, hA2]
                  exact card_filter_mod_Ioc_le R R h (r0 % h) hhpos
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            rw [hne]; exact Nat.zero_le _
        · rw [if_neg hgs]
          have hempty : A.filter (fun r => s % d = (r * a) % d) = ∅ := by
            rw [← Finset.not_nonempty_iff_eq_empty]
            rintro ⟨r, hr⟩
            rw [Finset.mem_filter] at hr
            have hme : r * a ≡ s [MOD d] := by
              show (r * a) % d = s % d
              rw [← hr.2]
            have hiff := Nat.ModEq.dvd_iff hme hgd
            exact hgs (hiff.mp (dvd_mul_of_dvd_right (by rw [hg]; exact Nat.gcd_dvd_left a d) r))
          rw [hempty]; exact Nat.zero_le _
      calc ∑ s ∈ B, (A.filter (fun r => s % d = (r * a) % d)).card
          ≤ ∑ s ∈ B, (if g ∣ s then R / h + 1 else 0) := Finset.sum_le_sum hb
        _ = n * (R / h + 1) := by
              rw [hn, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hn2S : n ≤ 2 * S := by
      rw [hn]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (le_of_eq hcardB)
    have hng : 2 * (n * g) ≤ 5 * S := by
      have hnle : n ≤ (5 * S / 2) / g := by
        rw [hn]
        refine card_multiples_le (5 * S / 2) g hgpos (B.filter (fun s => g ∣ s)) ?_ ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x hx
          have hxmem : x ∈ B := (Finset.mem_filter.mp hx).1
          rw [hB] at hxmem
          have := (Finset.mem_Ioc.mp hxmem).1
          omega
        · intro x hx
          have hxmem : x ∈ B := (Finset.mem_filter.mp hx).1
          rw [hB] at hxmem
          exact (Finset.mem_Ioc.mp hxmem).2
      calc 2 * (n * g) ≤ 2 * (((5 * S / 2) / g) * g) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right g hnle)
        _ ≤ 2 * (5 * S / 2) := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self (5 * S / 2) g)
        _ ≤ 5 * S := Nat.mul_div_le (5 * S) 2
    have hkey : 2 * d * (n * (R / h)) ≤ 5 * (R * S) := by
      have h2 : h * (R / h) ≤ R := by rw [mul_comm]; exact Nat.div_mul_le_self R h
      calc 2 * d * (n * (R / h)) = (2 * (n * g)) * (h * (R / h)) := by rw [← hgh]; ring
        _ ≤ (5 * S) * R := Nat.mul_le_mul hng h2
        _ = 5 * (R * S) := by ring
    have hqle : n * (R / h) ≤ 3 * q + 2 := by
      have hmod : R * S = d * q + (R * S) % d := by
        rw [hq]; exact (Nat.div_add_mod (R * S) d).symm
      have hlt : (R * S) % d < d := Nat.mod_lt (R * S) hd0
      have hkey' : d * (2 * (n * (R / h))) ≤ 5 * (R * S) := by
        have : 2 * d * (n * (R / h)) = d * (2 * (n * (R / h))) := by ring
        rw [this] at hkey; exact hkey
      have hlt2 : 5 * (R * S) < d * (5 * (q + 1)) := by nlinarith [hmod, hlt]
      have hchain : d * (2 * (n * (R / h))) < d * (5 * (q + 1)) := lt_of_le_of_lt hkey' hlt2
      have h3 : 2 * (n * (R / h)) < 5 * (q + 1) := (Nat.mul_lt_mul_left hd0).mp hchain
      omega
    calc C ≤ n * (R / h + 1) := hpers
      _ = n * (R / h) + n := by ring
      _ ≤ (3 * q + 2) + 2 * S := add_le_add hqle hn2S
      _ ≤ 10 * (q + S + 1) := by omega
      _ = 10 * (R * S / d + min R S + 1) := by rw [hq, min_eq_right hSR]

end Work.FIArea4.Vflip
