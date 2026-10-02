/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Outward rounding of dyadics and boxes to a fixed grid

The interval certificate of item A1 works with `Dya` values whose *representation* is not
canonical: `Dya.add` and `Dya.mul` add the exponents, so a five-level box recursion produces
endpoints of exponent in the tens of thousands even though the boxes are of size `10^{-10}`.  Every
operation on such values then costs a multiplication of two numbers with tens of thousands of bits,
and a `decide` over the whole recursion (item A3, and any future extension to the ray chain) becomes
minutes of kernel time and gigabytes of memory.

`Dya.floorK K a` and `Dya.ceilK K a` round `a` *outward* to an exact multiple of `2^-K`; the value
is unchanged up to `2^-K` and the result has exponent `≤ K`.  Applied after every step of a box
recursion (`CBox.roundOut`, `jet2IterR`), the exponents stay bounded by a small multiple of `K`, and
the arithmetic costs drop from `O(bits²)` to `O(bits)` per operation.  Soundness is immediate:
rounding outward preserves what a box contains.

## Main results

* `Dya.pow2`, `Dya.pow2_eq`;
* `Dya.floorK`, `Dya.ceilK`, `Dya.floorK_toReal_le`, `Dya.toReal_le_ceilK`;
* `CBox.roundOut`, `CBox.mem_roundOut`;
* `DJet2.roundOut`, `jet2IterR` (the rounded 2-jet recursion) — the soundness `mem_jet2R` is
  delegated.
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

namespace Dya

/-- `2^j`, computed with the kernel-primitive shift. -/
def pow2 (j : ℕ) : ℤ := ((1 : ℕ) <<< j : ℕ)

theorem pow2_eq (j : ℕ) : pow2 j = 2 ^ j := by
  unfold pow2
  rw [Nat.shiftLeft_eq]
  push_cast
  ring

theorem pow2_ne_zero (j : ℕ) : pow2 j ≠ 0 := by
  rw [pow2_eq]
  exact pow_ne_zero _ (by norm_num)

/-- Round `a` *down* to a multiple of `2^-K` (the value decreases, or stays). -/
def floorK (K : ℕ) (a : Dya) : Dya :=
  if a.exp ≤ K then a else ⟨a.num / pow2 (a.exp - K), K⟩

/-- Round `a` *up* to a multiple of `2^-K` (the value increases, or stays). -/
def ceilK (K : ℕ) (a : Dya) : Dya :=
  if a.exp ≤ K then a else ⟨-((-(a.num)) / pow2 (a.exp - K)), K⟩

private theorem pow2_cast (j : ℕ) : ((pow2 j : ℤ) : ℝ) = (2 : ℝ) ^ j := by
  rw [pow2_eq]; push_cast; ring

theorem floorK_toReal_le (K : ℕ) (a : Dya) : (floorK K a).toReal ≤ a.toReal := by
  unfold floorK
  split_ifs with h
  · exact le_refl _
  · set D : ℤ := pow2 (a.exp - K) with hDdef
    have hDne : D ≠ 0 := pow2_ne_zero (a.exp - K)
    have hDpos : (0 : ℝ) < (D : ℝ) := by
      rw [hDdef, pow2_cast]; positivity
    have hK : K ≤ a.exp := (Nat.not_le.mp h).le
    have hpow : (2 : ℝ) ^ a.exp = (2 : ℝ) ^ K * (D : ℝ) := by
      rw [hDdef, pow2_cast, ← pow_add, Nat.add_sub_cancel' hK]
    have h1 : ((a.num / D : ℤ) : ℝ) * (D : ℝ) ≤ (a.num : ℝ) := by
      have hc : ((a.num / D * D : ℤ) : ℝ) ≤ (a.num : ℝ) :=
        Int.cast_le.mpr (Int.ediv_mul_le a.num hDne)
      rwa [Int.cast_mul] at hc
    rw [Dya.toReal, Dya.toReal, hpow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (2 : ℝ) ^ K by positivity)
    linarith [h2]

theorem toReal_le_ceilK (K : ℕ) (a : Dya) : a.toReal ≤ (ceilK K a).toReal := by
  unfold ceilK
  split_ifs with h
  · exact le_refl _
  · set D : ℤ := pow2 (a.exp - K) with hDdef
    have hDne : D ≠ 0 := pow2_ne_zero (a.exp - K)
    have hDpos : (0 : ℝ) < (D : ℝ) := by
      rw [hDdef, pow2_cast]; positivity
    have hK : K ≤ a.exp := (Nat.not_le.mp h).le
    have hpow : (2 : ℝ) ^ a.exp = (2 : ℝ) ^ K * (D : ℝ) := by
      rw [hDdef, pow2_cast, ← pow_add, Nat.add_sub_cancel' hK]
    have h1 : (a.num : ℝ) ≤ -((((-a.num) / D : ℤ) : ℝ) * (D : ℝ)) := by
      have hc : (((-a.num) / D * D : ℤ) : ℝ) ≤ ((-a.num : ℤ) : ℝ) :=
        Int.cast_le.mpr (Int.ediv_mul_le (-a.num) hDne)
      rw [Int.cast_mul, Int.cast_neg] at hc
      linarith
    rw [Dya.toReal, Dya.toReal, hpow, div_le_div_iff₀ (by positivity) (by positivity)]
    dsimp only
    simp only [Int.cast_neg]
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (2 : ℝ) ^ K by positivity)
    linarith [h2]

end Dya

/-- Round every endpoint of a box outward to a multiple of `2^-K`. -/
def CBox.roundOut (K : ℕ) (B : CBox) : CBox :=
  ⟨Dya.floorK K B.rlo, Dya.ceilK K B.rhi, Dya.floorK K B.ilo, Dya.ceilK K B.ihi⟩

theorem CBox.mem_roundOut {B : CBox} {z : ℂ} {K : ℕ} (h : z ∈ B.toSet) :
    z ∈ (B.roundOut K).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(Dya.floorK_toReal_le K B.rlo).trans h1, h2.trans (Dya.toReal_le_ceilK K B.rhi),
    (Dya.floorK_toReal_le K B.ilo).trans h3, h4.trans (Dya.toReal_le_ceilK K B.ihi)⟩

/-- Round the three boxes of a 2-jet outward. -/
def DJet2.roundOut (K : ℕ) (J : DJet2) : DJet2 :=
  ⟨J.v.roundOut K, J.d1.roundOut K, J.d2.roundOut K⟩

/-- The 2-jet recursion of `(Tsq c)^[n]` with outward rounding to the grid `2^-K` after every
step: the exponents (and hence the kernel cost) stay bounded by `K`. -/
def jet2IterR (K : ℕ) (Ctyp Xz : CBox) : ℕ → DJet2
  | 0 => ⟨Xz.roundOut K, oneBox.roundOut K,
      (⟨Dya.zero, Dya.zero, Dya.zero, Dya.zero⟩ : CBox).roundOut K⟩
  | n + 1 => (jet2Step Ctyp (jet2IterR K Ctyp Xz n)).roundOut K

end

end Work.SeedCert
