import Mathlib

namespace Work.Analysis.Primes

/-- Start of the block of three consecutive integers assigned to `p`.
For a prime `p > 3` this is `p - 2` if `p ≡ 1 (mod 6)` and `p - 3` if `p ≡ 5 (mod 6)`,
so that the block `{blkStart p, blkStart p + 1, blkStart p + 2}` is
`{p-2,p-1,p}` in the first case and `{p-3,p-2,p-1}` in the second. -/
def blkStart (p : ℕ) : ℕ := if p % 6 = 1 then p - 2 else p - 3

lemma le_blkStart (p : ℕ) : p - 3 ≤ blkStart p := by
  unfold blkStart; split_ifs <;> omega

lemma blkStart_le (p : ℕ) : blkStart p ≤ p - 2 := by
  unfold blkStart; split_ifs <;> omega

/-- Every prime `p ≥ 5` satisfies `p ≡ 1 (mod 6)` or `p ≡ 5 (mod 6)`. -/
lemma prime_mod_six (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).mpr (by omega)
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have h3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hp3' : p % 3 ≠ 0 := by intro h; exact hp3 (Nat.dvd_of_mod_eq_zero h)
  have h2 : p % 6 % 2 = 1 := by rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 6), hp2]
  have h3 : p % 6 % 3 ≠ 0 := by rw [Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6)]; exact hp3'
  have h6lt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-- The blocks assigned to two distinct primes `p < q`, both at least `5`, are ordered:
`blkStart p + 2 < blkStart q`. -/
lemma blkStart_lt (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h5 : 5 ≤ p) (hlt : p < q) :
    blkStart p + 2 < blkStart q := by
  have hp6 := prime_mod_six p hp h5
  have hq6 := prime_mod_six q hq (by omega)
  unfold blkStart
  rcases hp6 with hp6 | hp6 <;> rcases hq6 with hq6 | hq6
  · rw [if_pos hp6, if_pos hq6]; omega
  · rw [if_pos hp6, if_neg (by omega : ¬ q % 6 = 1)]; omega
  · rw [if_neg (by omega : ¬ p % 6 = 1), if_pos hq6]; omega
  · rw [if_neg (by omega : ¬ p % 6 = 1), if_neg (by omega : ¬ q % 6 = 1)]; omega

/-- For a nonincreasing nonnegative weight `g` and `6 ≤ m`, the sum of `g` over the primes
`p` with `m < p ≤ Pf` is at most a third of the sum over all integers in `[m - 2, Pf]`:
every prime `> 3` is congruent to `1` or `5` modulo `6`, and each such prime can be assigned
three distinct integers at most equal to it, in a manner that makes all the assigned sets
`{p-3,p-2,p-1}` (for `p ≡ 5 mod 6`) and `{p-2,p-1,p}` (for `p ≡ 1 mod 6`) disjoint. -/
theorem sum_primes_le_third (m Pf : ℕ) (hm : 6 ≤ m) (g : ℕ → ℝ)
    (hg0 : ∀ n, 0 ≤ g n)
    (hgm : ∀ a b : ℕ, m - 2 ≤ a → a ≤ b → b ≤ Pf → g b ≤ g a) :
    ∑ p ∈ (Finset.Icc (m + 1) Pf).filter Nat.Prime, g p
      ≤ (1 / 3) * ∑ n ∈ Finset.Icc (m - 2) Pf, g n := by
  set t : Finset ℕ := (Finset.Icc (m + 1) Pf).filter Nat.Prime with ht
  set I : Finset ℕ := Finset.Icc (m - 2) Pf with hI
  -- `φ` sends a prime `p` and an offset `j ∈ {0,1,2}` to the `j`-th integer of its block.
  let φ : ℕ × ℕ → ℕ := fun x => blkStart x.1 + x.2
  -- The blocks of distinct primes are disjoint, i.e. `φ` is injective on `t × {0,1,2}`.
  have h_inj : Set.InjOn φ (↑(t ×ˢ Finset.range 3) : Set (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ hx ⟨c, d⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx hy
    obtain ⟨hxa, hxb⟩ := hx
    obtain ⟨hya, hyb⟩ := hy
    have hpa : a.Prime := (Finset.mem_filter.mp hxa).2
    have hpc : c.Prime := (Finset.mem_filter.mp hya).2
    have ha1 : m + 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxa).1).1
    have hc1 : m + 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hya).1).1
    have hb2 : b ≤ 2 := by omega
    have hd2 : d ≤ 2 := by omega
    simp only [φ] at hxy
    have hle : a ≤ c := by
      by_contra hh
      have hh' : c < a := not_le.mp hh
      have hltc : blkStart c + 2 < blkStart a := blkStart_lt c a hpc hpa (by omega) hh'
      omega
    have hge : c ≤ a := by
      by_contra hh
      have hh' : a < c := not_le.mp hh
      have hlta : blkStart a + 2 < blkStart c := blkStart_lt a c hpa hpc (by omega) hh'
      omega
    have hac : a = c := le_antisymm hle hge
    subst hac
    have hbd : b = d := by omega
    subst hbd
    rfl
  -- `3 * ∑_{p ∈ t} g p = ∑_{x ∈ t × {0,1,2}} g x.1`
  have hA : ∑ x ∈ t ×ˢ Finset.range 3, g x.1 = 3 * ∑ p ∈ t, g p := by
    rw [Finset.sum_product]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
  -- each block term dominates the prime term, by monotonicity of `g`
  have hB : ∑ x ∈ t ×ˢ Finset.range 3, g x.1 ≤ ∑ x ∈ t ×ˢ Finset.range 3, g (φ x) := by
    apply Finset.sum_le_sum
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨hxa, hxb⟩ := hx
    have hxa1 : m + 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxa).1).1
    have hxaPf : x.1 ≤ Pf := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxa).1).2
    have hb2 : x.2 ≤ 2 := by omega
    simp only [φ]
    apply hgm
    · have := le_blkStart x.1; omega
    · have := blkStart_le x.1; omega
    · exact hxaPf
  -- pass from the sum over `t × {0,1,2}` to the sum over the (disjoint) image of `φ`
  have hC : ∑ n ∈ (t ×ˢ Finset.range 3).image φ, g n = ∑ x ∈ t ×ˢ Finset.range 3, g (φ x) :=
    Finset.sum_image (f := g) h_inj
  -- the image of `φ` lies in `[m - 2, Pf]`
  have h_sub : (t ×ˢ Finset.range 3).image φ ⊆ I := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    simp only [Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨hxa, hxb⟩ := hx
    have hxa1 : m + 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxa).1).1
    have hxaPf : x.1 ≤ Pf := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxa).1).2
    have hb2 : x.2 ≤ 2 := by omega
    simp only [hI, φ, Finset.mem_Icc]
    constructor
    · have := le_blkStart x.1; omega
    · have := blkStart_le x.1; omega
  -- extend the sum over the image to the full interval, using nonnegativity
  have hE : ∑ n ∈ (t ×ˢ Finset.range 3).image φ, g n ≤ ∑ n ∈ I, g n :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun n hn hnot => hg0 n)
  have hchain : 3 * ∑ p ∈ t, g p ≤ ∑ n ∈ I, g n := by
    calc 3 * ∑ p ∈ t, g p = ∑ x ∈ t ×ˢ Finset.range 3, g x.1 := hA.symm
      _ ≤ ∑ x ∈ t ×ˢ Finset.range 3, g (φ x) := hB
      _ = ∑ n ∈ (t ×ˢ Finset.range 3).image φ, g n := hC.symm
      _ ≤ ∑ n ∈ I, g n := hE
  have h1 : ∑ p ∈ t, g p ≤ (∑ n ∈ I, g n) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith [hchain]
  calc ∑ p ∈ t, g p ≤ (∑ n ∈ I, g n) / 3 := h1
    _ = (1 / 3) * ∑ n ∈ I, g n := by ring

end Work.Analysis.Primes
