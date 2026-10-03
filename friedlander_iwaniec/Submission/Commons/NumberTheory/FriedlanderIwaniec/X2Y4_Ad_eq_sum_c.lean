import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star

namespace Commons.NumberTheory.FriedlanderIwaniec

private lemma rpow_quarter_pow_four (x : ℕ) :
    ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (x : ℝ) := by
  rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 4)) 4]
  rw [show (((4 : ℕ) : ℝ)) = (4 : ℝ) by norm_num]
  rw [← Real.rpow_mul (Nat.cast_nonneg x) (1 / 4) 4,
    show (1 : ℝ) / 4 * 4 = 1 by norm_num, Real.rpow_one]

private lemma pow_four_le_of_le_rpow {x N : ℕ}
    (hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4)) : N ^ 4 ≤ x := by
  have h : (N : ℝ) ^ 4 ≤ (x : ℝ) := by
    calc (N : ℝ) ^ 4 ≤ ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 :=
          pow_le_pow_left₀ (Nat.cast_nonneg N) hNle 4
      _ = (x : ℝ) := rpow_quarter_pow_four x
  have h2 : ((N ^ 4 : ℕ) : ℝ) ≤ (x : ℝ) := by push_cast; exact h
  exact_mod_cast h2

private lemma mem_Icc_iff_pow_four_le {x N : ℕ} (hx : (0 : ℝ) < (x : ℝ))
    (hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4))
    (hNlt : (x : ℝ) ^ ((1 : ℝ) / 4) < (N : ℝ) + 1) (c : ℤ) :
    c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ↔ c ^ 4 ≤ (x : ℤ) := by
  have hN4 : N ^ 4 ≤ x := pow_four_le_of_le_rpow hNle
  constructor
  · intro hc
    rw [Finset.mem_Icc] at hc
    obtain ⟨h1, h2⟩ := hc
    have habs : |c| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
    have hnat : c.natAbs ≤ N := by
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs
    have h4 : c.natAbs ^ 4 ≤ x := le_trans (Nat.pow_le_pow_left hnat 4) hN4
    have hc4 : c ^ 4 = ((c.natAbs ^ 4 : ℕ) : ℤ) := by
      rw [Nat.cast_pow]
      rw [show ((c.natAbs : ℤ)) = |c| by rw [Int.abs_eq_natAbs], ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℤ) ≤ c ^ 4)]
    rw [hc4]
    exact_mod_cast h4
  · intro hc4
    have hc4R : (c : ℝ) ^ 4 ≤ (x : ℝ) := by
      have : (((c ^ 4 : ℤ)) : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast hc4
      simpa using this
    have habs4 : (|(c : ℝ)|) ^ 4 ≤ ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
      rw [rpow_quarter_pow_four, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ 4)]
      exact hc4R
    have habs : |(c : ℝ)| ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
      (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.rpow_nonneg (le_of_lt hx) _)
        (by norm_num)).mp habs4
    have hlt : (c.natAbs : ℝ) < (N : ℝ) + 1 := by
      have h := lt_of_le_of_lt habs hNlt
      rwa [← show ((c.natAbs : ℝ)) = |(c : ℝ)| by rw [Nat.cast_natAbs, Int.cast_abs]] at h
    have hnat : c.natAbs < N + 1 := by
      have h2 : ((c.natAbs : ℕ) : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    have hnatle : c.natAbs ≤ N := by omega
    rw [Finset.mem_Icc]
    have habsZ : |c| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hnatle
    exact abs_le.mp habsZ

private lemma sub_pow_four_nonneg {x N : ℕ}
    (hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4)) {c : ℤ}
    (hc : c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) : 0 ≤ (x : ℝ) - (c : ℝ) ^ 4 := by
  have hN4 : N ^ 4 ≤ x := pow_four_le_of_le_rpow hNle
  have hN4R : (N : ℝ) ^ 4 ≤ (x : ℝ) := by
    have : ((N ^ 4 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hN4
    push_cast at this; exact this
  rw [Finset.mem_Icc] at hc
  obtain ⟨h1, h2⟩ := hc
  have habs : |c| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
  have habsR : |(c : ℝ)| ≤ (N : ℝ) := by
    have : ((|c| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by exact_mod_cast habs
    rwa [Int.cast_abs, Int.cast_natCast] at this
  have hle : (c : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) habsR 4
    rwa [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ 4)] at h
  linarith

private lemma abs_le_sqrt_iff {x : ℕ} {c : ℤ}
    (ht : 0 ≤ (x : ℝ) - (c : ℝ) ^ 4) (a : ℤ) :
    |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) ↔ a ^ 2 + c ^ 4 ≤ (x : ℤ) := by
  rw [Real.le_sqrt (abs_nonneg _) ht, sq_abs]
  constructor
  · intro h
    have : (((a ^ 2 + c ^ 4 : ℤ)) : ℝ) ≤ ((x : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : (((a ^ 2 + c ^ 4 : ℤ)) : ℝ) ≤ ((x : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

private lemma mem_Icc_of_abs_le_sqrt {x : ℕ} {c : ℤ} (a : ℤ)
    (ha : |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)) :
    a ∈ (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))
          (⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1) : Finset ℤ) := by
  rw [Finset.mem_Icc]
  have hlt : Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) <
      ((⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ : ℤ) + 1 : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
    push_cast
    linarith
  have habs : |(a : ℝ)| ≤ ((⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ : ℤ) + 1 : ℝ) :=
    le_of_lt (lt_of_le_of_lt ha hlt)
  have hab := abs_le.mp habs
  constructor
  · exact_mod_cast hab.1
  · exact_mod_cast hab.2

theorem X2Y4_Ad_eq_sum_c (x d : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) :
    (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℤ)
      = ∑ c ∈ Finset.Icc (-((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))) ((⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)),
          ((Finset.filter (fun a : ℤ =>
              |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) ∧
                ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
            (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))
              (⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))).card : ℤ) := by
  classical
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (0 : ℕ) < x := by omega
    exact_mod_cast this
  set N : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ with hN
  have hNle : (N : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hN]; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hxpos) _)
  have hNlt : (x : ℝ) ^ ((1 : ℝ) / 4) < (N : ℝ) + 1 := by
    rw [hN]; exact Nat.lt_floor_add_one _
  let B : Finset (Σ _ : ℤ, ℤ) :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).sigma (fun c =>
      Finset.filter (fun a : ℤ =>
          |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) ∧
            ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
        (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))
          (⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1)))
  let ψ : (Σ _ : ℤ, ℤ) → ℤ × ℤ := fun z => (z.2, z.1)
  have hinj : Function.Injective ψ := by
    rintro ⟨c1, a1⟩ ⟨c2, a2⟩ h
    have h' : (a1, c1) = (a2, c2) := h
    injection h' with ha hc
    rw [ha, hc]
  have hBcard : B.card = ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (Finset.filter (fun a : ℤ =>
          |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) ∧
            ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
        (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))
          (⌊Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)⌋₊ + 1))).card := by
    rw [Finset.card_sigma]
  have himage : (↑(B.image ψ) : Set (ℤ × ℤ))
      = {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)} := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_coe, Finset.mem_image] at hp
      obtain ⟨z, hz, hzp⟩ := hp
      obtain ⟨hc, ha⟩ := Finset.mem_sigma.mp hz
      have hzp' : (z.2, z.1) = p := hzp
      have h1 : z.2 = p.1 := congrArg Prod.fst hzp'
      have h2 : z.1 = p.2 := congrArg Prod.snd hzp'
      rw [Finset.mem_filter] at ha
      obtain ⟨_, habs, hdvd⟩ := ha
      have ht := sub_pow_four_nonneg hNle hc
      have heq := (abs_le_sqrt_iff ht z.2).mp habs
      rw [Set.mem_ofPred_eq, ← h1, ← h2]
      exact ⟨heq, hdvd⟩
    · intro hp
      rw [Set.mem_ofPred_eq] at hp
      obtain ⟨hle, hdvd⟩ := hp
      rw [Finset.mem_coe, Finset.mem_image]
      have hc4 : p.2 ^ 4 ≤ (x : ℤ) := by
        have : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
        linarith
      have hc : p.2 ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
        (mem_Icc_iff_pow_four_le hxpos hNle hNlt p.2).mpr hc4
      have ht := sub_pow_four_nonneg hNle hc
      have habs : |(p.1 : ℝ)| ≤ Real.sqrt ((x : ℝ) - (p.2 : ℝ) ^ 4) :=
        (abs_le_sqrt_iff ht p.1).mpr hle
      have hmem : p.1 ∈ Finset.filter (fun a : ℤ =>
          |(a : ℝ)| ≤ Real.sqrt ((x : ℝ) - (p.2 : ℝ) ^ 4) ∧
            ((d : ℤ) ∣ a ^ 2 + (p.2 : ℤ) ^ 4))
        (Finset.Icc (-(⌊Real.sqrt ((x : ℝ) - (p.2 : ℝ) ^ 4)⌋₊ + 1))
          (⌊Real.sqrt ((x : ℝ) - (p.2 : ℝ) ^ 4)⌋₊ + 1)) := by
        rw [Finset.mem_filter]
        exact ⟨mem_Icc_of_abs_le_sqrt p.1 habs, habs, hdvd⟩
      refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        exact ⟨hc, hmem⟩
      · simp only [ψ]
  have hSncard : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧
      ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard = B.card := by
    rw [← himage, Set.ncard_coe_finset, Finset.card_image_of_injective B hinj]
  have _ := hdZ
  rw [hSncard, hBcard, Nat.cast_sum]

end Commons.NumberTheory.FriedlanderIwaniec