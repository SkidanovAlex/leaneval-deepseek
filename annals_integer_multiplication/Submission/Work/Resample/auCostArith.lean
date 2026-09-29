import Mathlib

/-!
# Arithmetic assembly for the resampling cost estimate

Pure `ℕ` bookkeeping: the sum of the six terms of the resampling cost is bounded by the
single product `(K1 + 88*K2 + 2*Kc1 + 44*Kc2 + 26*K3 + 2*Kc3) * n` where
`n = (s + t*L + cop*s + 1) * (p + 1)`.

The three nontrivial ingredients are

* `keyB` : `(t+1) * ((L+1)*(2p+9)+1) ≤ 88 * n`,
* `keyE` : `(Edrop+1) * (2p+9) + 1 ≤ 44 * n`  (using `Edrop ≤ s`),
* `keyC` : `t * (L*(3p+16)+4) + t + 2 ≤ 26 * n`,

each of which follows from `n ≥ t*L*(p+1)` and elementary monotonicity estimates.
-/

namespace Work.Resample

private lemma keyB (s t L cop p : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hL : 1 ≤ L) (hp : 1 ≤ p) :
    (t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1) ≤ 88 * ((s + t * L + cop * s + 1) * (p + 1)) := by
  have h1 : t + 1 ≤ 2 * t := by omega
  have h2 : (L + 1) * (2 * p + 8 + 1) + 1 ≤ 44 * (L * (p + 1)) := by
    have hL2 : L + 1 ≤ 2 * L := by omega
    have hp2 : 2 * p + 8 + 1 ≤ 11 * (p + 1) := by omega
    have h3 : (L + 1) * (2 * p + 8 + 1) ≤ 22 * (L * (p + 1)) := by
      calc (L + 1) * (2 * p + 8 + 1) ≤ (2 * L) * (11 * (p + 1)) := Nat.mul_le_mul hL2 hp2
        _ = 22 * (L * (p + 1)) := by ring
    have hpos : 0 < (L + 1) * (2 * p + 8 + 1) := by positivity
    calc (L + 1) * (2 * p + 8 + 1) + 1
        ≤ (L + 1) * (2 * p + 8 + 1) + (L + 1) * (2 * p + 8 + 1) := by omega
      _ = 2 * ((L + 1) * (2 * p + 8 + 1)) := by ring
      _ ≤ 2 * (22 * (L * (p + 1))) := Nat.mul_le_mul_left 2 h3
      _ = 44 * (L * (p + 1)) := by ring
  have h5 : t * L ≤ s + t * L + cop * s + 1 := by omega
  calc (t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1)
      ≤ (2 * t) * (44 * (L * (p + 1))) := Nat.mul_le_mul h1 h2
    _ = 88 * (t * L * (p + 1)) := by ring
    _ ≤ 88 * ((s + t * L + cop * s + 1) * (p + 1)) :=
        Nat.mul_le_mul_left 88 (Nat.mul_le_mul_right (p + 1) h5)

private lemma keyE (s t L cop p Edrop : ℕ) (_hs : 1 ≤ s) (_ht : 1 ≤ t) (_hL : 1 ≤ L) (hp : 1 ≤ p)
    (hEdrop : Edrop ≤ s) :
    (Edrop + 1) * (2 * p + 8 + 1) + 1 ≤ 44 * ((s + t * L + cop * s + 1) * (p + 1)) := by
  have h1 : Edrop + 1 ≤ s + t * L + cop * s + 1 := by omega
  have hp2 : 2 * p + 8 + 1 ≤ 11 * (p + 1) := by omega
  have h2 : (Edrop + 1) * (2 * p + 8 + 1) ≤ 11 * ((s + t * L + cop * s + 1) * (p + 1)) := by
    calc (Edrop + 1) * (2 * p + 8 + 1) ≤ (s + t * L + cop * s + 1) * (11 * (p + 1)) :=
          Nat.mul_le_mul h1 hp2
      _ = 11 * ((s + t * L + cop * s + 1) * (p + 1)) := by ring
  have hA1 : 1 ≤ (s + t * L + cop * s + 1) * (p + 1) := by
    have hSS : 1 ≤ s + t * L + cop * s + 1 := by omega
    have := Nat.mul_le_mul hSS (show 1 ≤ p + 1 by omega)
    simpa using this
  omega

private lemma keyC (s t L cop p : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hL : 1 ≤ L) (hp : 1 ≤ p) :
    t * (L * (3 * p + 16) + 4) + t + 2 ≤ 26 * ((s + t * L + cop * s + 1) * (p + 1)) := by
  have hCeq : t * (L * (3 * p + 16) + 4) + t + 2 = t * L * (3 * p + 16) + 4 * t + t + 2 := by ring
  rw [hCeq]
  have h3p : 3 * p + 16 ≤ 16 * (p + 1) := by omega
  have h6 : t * L * (3 * p + 16) ≤ 16 * (t * L * (p + 1)) := by
    calc t * L * (3 * p + 16) ≤ (t * L) * (16 * (p + 1)) := Nat.mul_le_mul_left (t * L) h3p
      _ = 16 * (t * L * (p + 1)) := by ring
  have h5 : t * L ≤ s + t * L + cop * s + 1 := by omega
  have hLp : 2 ≤ L * (p + 1) := by
    have : 2 ≤ p + 1 := by omega
    calc 2 = 1 * 2 := by ring
      _ ≤ L * (p + 1) := Nat.mul_le_mul hL this
  have h2t : 2 * t ≤ (s + t * L + cop * s + 1) * (p + 1) := by
    have h2 : 2 * t ≤ t * L * (p + 1) := by
      calc 2 * t = t * 2 := by ring
        _ ≤ t * (L * (p + 1)) := Nat.mul_le_mul_left t hLp
        _ = t * L * (p + 1) := by ring
    exact le_trans h2 (Nat.mul_le_mul_right (p + 1) h5)
  have h1 : t * L * (3 * p + 16) ≤ 16 * ((s + t * L + cop * s + 1) * (p + 1)) :=
    le_trans h6 (Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right (p + 1) h5))
  have h2 : 4 * t + t + 2 ≤ 10 * ((s + t * L + cop * s + 1) * (p + 1)) := by omega
  omega

theorem auCostArith (K1 K2 K3 Kc1 Kc2 Kc3 s t L cop p Edrop : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hEdrop : Edrop ≤ s) :
    K1 * ((s + t * L + cop * s + 1) * (p + 1)) + K2 * (t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1)
      + 2 * Kc1 + Kc2 * ((Edrop + 1) * (2 * p + 8 + 1) + 1)
      + K3 * (t * (L * (3 * p + 16) + 4) + t + 2) + 2 * Kc3
    ≤ (K1 + 88 * K2 + 2 * Kc1 + 44 * Kc2 + 26 * K3 + 2 * Kc3) * ((s + t * L + cop * s + 1) * (p + 1)) := by
  set A := (s + t * L + cop * s + 1) * (p + 1) with hAdef
  have hB : (t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1) ≤ 88 * A := by
    rw [hAdef]; exact keyB s t L cop p hs ht hL hp
  have hE : (Edrop + 1) * (2 * p + 8 + 1) + 1 ≤ 44 * A := by
    rw [hAdef]; exact keyE s t L cop p Edrop hs ht hL hp hEdrop
  have hC : t * (L * (3 * p + 16) + 4) + t + 2 ≤ 26 * A := by
    rw [hAdef]; exact keyC s t L cop p hs ht hL hp
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have hSS : 1 ≤ s + t * L + cop * s + 1 := by omega
    have := Nat.mul_le_mul hSS (show 1 ≤ p + 1 by omega)
    simpa using this
  have h2Kc1 : 2 * Kc1 ≤ (2 * Kc1) * A := by
    simpa using Nat.mul_le_mul_left (2 * Kc1) hA1
  have h2Kc3 : 2 * Kc3 ≤ (2 * Kc3) * A := by
    simpa using Nat.mul_le_mul_left (2 * Kc3) hA1
  calc K1 * A + K2 * (t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1) + 2 * Kc1
        + Kc2 * ((Edrop + 1) * (2 * p + 8 + 1) + 1) + K3 * (t * (L * (3 * p + 16) + 4) + t + 2)
        + 2 * Kc3
      = K1 * A + K2 * ((t + 1) * ((L + 1) * (2 * p + 8 + 1) + 1)) + 2 * Kc1
        + Kc2 * ((Edrop + 1) * (2 * p + 8 + 1) + 1) + K3 * (t * (L * (3 * p + 16) + 4) + t + 2)
        + 2 * Kc3 := by ring
    _ ≤ K1 * A + K2 * (88 * A) + (2 * Kc1) * A + Kc2 * (44 * A) + K3 * (26 * A) + (2 * Kc3) * A := by
        exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl _)
          (Nat.mul_le_mul_left K2 hB)) h2Kc1) (Nat.mul_le_mul_left Kc2 hE))
          (Nat.mul_le_mul_left K3 hC)) h2Kc3
    _ = (K1 + 88 * K2 + 2 * Kc1 + 44 * Kc2 + 26 * K3 + 2 * Kc3) * A := by ring

end Work.Resample
