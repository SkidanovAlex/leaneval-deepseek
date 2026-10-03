import Mathlib

namespace Work.A3.Weil

/-- Counting integers in a residue class mod `q` inside the symmetric interval `[-M, M]`.

The interval `[-M, M]` contains `2M + 1` integers, so a fixed residue class contains at most
`⌈(2M+1)/q⌉ ≤ 2M/q + 1` of them.

The proof is a clean injection: for `P` in the interval with `P % q = r`, the map
`P ↦ (P + M) / q` (Euclidean division by `q > 0`) is injective on a fixed residue class
(indeed `P + M = q * ((P+M)/q) + (P+M) % q`, and `(P+M) % q` is determined by the class),
and its image lies in `[0, 2M/q]`, an interval of `⌊2M/q⌋ + 1 ≤ 2M/q + 1` integers. -/
theorem card_emod_eq_le (M : ℕ) {q : ℤ} (hq : 1 ≤ q) (r : ℤ) :
    (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q = r)).card : ℝ)
      ≤ 2 * (M : ℝ) / (q : ℝ) + 1 := by
  have hqpos : 0 < q := by omega
  have hqne : q ≠ 0 := ne_of_gt hqpos
  set S := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q = r) with hSdef
  set K : ℤ := (2 * (M : ℤ)) / q with hKdef
  -- On a fixed residue class the map `P ↦ (P + M) / q` is injective.
  have hinj : Set.InjOn (fun P : ℤ => (P + (M : ℤ)) / q) ↑S := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_Icc] at ha hb
    have hab' : (a + (M : ℤ)) / q = (b + (M : ℤ)) / q := hab
    have hrem : (a + (M : ℤ)) % q = (b + (M : ℤ)) % q := by
      have h1 := Int.add_emod a (M : ℤ) q
      have h2 := Int.add_emod b (M : ℤ) q
      rw [h1, h2, ha.2, hb.2]
    have ha1 := Int.emod_add_mul_ediv (a + (M : ℤ)) q
    have hb1 := Int.emod_add_mul_ediv (b + (M : ℤ)) q
    have : a + (M : ℤ) = b + (M : ℤ) := by
      rw [← ha1, ← hb1, hab', hrem]
    linarith
  -- The image of `S` under that map sits in `[0, K]` with `K = 2M/q`.
  have hmaps : Set.MapsTo (fun P : ℤ => (P + (M : ℤ)) / q) ↑S ↑(Finset.Icc 0 K) := by
    intro P hP
    simp only [Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_Icc] at hP
    obtain ⟨⟨h1, h2⟩, _⟩ := hP
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by linarith) (le_of_lt hqpos)
    · rw [hKdef]
      exact Int.ediv_le_ediv hqpos (by linarith)
  have hle := Finset.card_le_card_of_injOn (fun P : ℤ => (P + (M : ℤ)) / q) hmaps hinj
  have hcard : (Finset.Icc (0 : ℤ) K).card = (K + 1).toNat := by
    rw [Int.card_Icc]; ring_nf
  have hKnn : 0 ≤ K + 1 := by
    have hK' : 0 ≤ K := by
      rw [hKdef]; exact Int.ediv_nonneg (by positivity) (le_of_lt hqpos)
    linarith
  have hcast : ((K + 1).toNat : ℝ) = (K : ℝ) + 1 := by
    have h : ((K + 1).toNat : ℤ) = K + 1 := Int.toNat_of_nonneg hKnn
    exact_mod_cast h
  have hle' : S.card ≤ (K + 1).toNat := by rw [hcard] at hle; exact hle
  have hKr : (K : ℝ) ≤ (2 * (M : ℝ)) / (q : ℝ) := by
    have hKq : K * q ≤ 2 * (M : ℤ) := by
      rw [hKdef]; exact Int.ediv_mul_le _ hqne
    have h1 : (K : ℝ) * (q : ℝ) ≤ 2 * (M : ℝ) := by
      have h2 : ((K * q : ℤ) : ℝ) ≤ ((2 * (M : ℤ) : ℤ) : ℝ) := by exact_mod_cast hKq
      push_cast at h2
      linarith
    rw [le_div_iff₀ (by exact_mod_cast hqpos)]
    linarith
  calc ((S.card : ℕ) : ℝ) ≤ (((K + 1).toNat : ℕ) : ℝ) := by exact_mod_cast hle'
    _ = (K : ℝ) + 1 := hcast
    _ ≤ 2 * (M : ℝ) / (q : ℝ) + 1 := by linarith

end Work.A3.Weil
