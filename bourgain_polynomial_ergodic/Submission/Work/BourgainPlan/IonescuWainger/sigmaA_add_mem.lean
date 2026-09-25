import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT

/-!
# Additivity of Tao's exact-denominator sets `Σ_A` over disjoint index sets

For a finite set `S` of pairwise coprime integers `≥ 2` and `A ⊆ S`, `Q_A = ∏_{q ∈ A} q`
(`ArcDefs.lean`) and `Σ_A = sigmaA A` is Tao's set of points of the circle of *exact* denominator
`Q_A`, i.e. `a/Q_A` with `gcd(a, Q_A) = 1`.

This file proves that for **disjoint** `A, B ⊆ S`,

`Σ_A + Σ_B ⊆ Σ_{A ∪ B}`,

which is the "sumset" half of Tao's (sigma) identity in the Ionescu–Wainger major-arc system
(Tao, arXiv:2008.05066, §4).  Mathematically: if `x = a/Q_A` with `gcd(a, Q_A) = 1` and
`y = b/Q_B` with `gcd(b, Q_B) = 1`, then

`x + y = (a Q_B + b Q_A) / (Q_A Q_B) = c / Q_{A ∪ B}`,   `c = a Q_B + b Q_A`,

and `c` is coprime to `Q_A Q_B = Q_{A ∪ B}`: modulo any prime dividing `Q_A` we have
`c ≡ a Q_B` with both `a` and `Q_B` coprime to `Q_A` (the latter since `A ∩ B = ∅` and `S` is
pairwise coprime), and symmetrically for `Q_B`.  So `x + y` again has *exact* denominator
`Q_{A ∪ B}`.

Note the degenerate case `A = ∅` (so `Q_A = 1`, `Σ_A = {0}`) is not exceptional: the formula above
still holds and the coprimality `gcd(c, Q_B) = gcd(b, Q_B) = 1` survives.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- Adding points with two nonzero denominators: `a/Q + b/R = (a R + b Q)/(Q R)`. -/
private lemma arcPt_add_denom' {Q R : ℕ} (hQ : Q ≠ 0) (hR : R ≠ 0) (a b : ℤ) :
    arcPt Q a + arcPt R b = arcPt (Q * R) (a * (R : ℤ) + b * (Q : ℤ)) := by
  rw [arcPt, arcPt, arcPt, ← AddCircle.coe_add]
  congr 1
  push_cast
  field_simp

/-- **Arithmetic core.**  If `a` is coprime to `n`, `b` to `m`, and `n` to `m` (in `ℤ`), then
`a m + b n` is coprime to `n m`:
modulo `n`, the number `a m + b n` is `a m`, and both `a` and `m` are coprime to `n`; symmetrically
modulo `m`. -/
private lemma isCoprime_add_mul' {a b n m : ℤ} (ha : IsCoprime a n) (hb : IsCoprime b m)
    (hnm : IsCoprime n m) : IsCoprime (a * m + b * n) (n * m) := by
  have h1 : IsCoprime (a * m) n := ha.mul_left hnm.symm
  have h2 : IsCoprime (b * n) m := hb.mul_left hnm
  exact (h1.add_mul_right_left b).mul_right (h2.mul_add_right_left a)

/-- **The sumset identity `Σ_A + Σ_B ⊆ Σ_{A ∪ B}`** (the `Σ_·` case of Tao's (sigma),
arXiv:2008.05066, §4), for `A, B` disjoint subsets of a finite pairwise coprime set `S` of
integers `≥ 2`.  If `x = a/Q_A` and `y = b/Q_B` have exact denominators `Q_A`, `Q_B`, then
`x + y = (a Q_B + b Q_A)/(Q_A Q_B)` has exact denominator `Q_A Q_B = Q_{A ∪ B}`. -/
theorem sigmaA_add_mem {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) {x y : Circle}
    (hx : x ∈ sigmaA A) (hy : y ∈ sigmaA B) : x + y ∈ sigmaA (A ∪ B) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hAnz : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hBnz : QA B ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hB hq)
  have hQAAB : QA (A ∪ B) = QA A * QA B := QA_union hAB
  -- `Q_A` and `Q_B` are coprime: `A ∩ B = ∅` and `S` is pairwise coprime
  have hcopAB : Nat.Coprime (QA A) (QA B) := by
    rw [QA, QA]
    exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.prod_right fun q' hq' =>
      hS q (hA hq) q' (hB hq') (fun he => (Finset.disjoint_left.mp hAB hq) (he ▸ hq'))
  have haI : IsCoprime a (QA A : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using ha)
  have hbI : IsCoprime b (QA B : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hb)
  have hnmI : IsCoprime (QA A : ℤ) (QA B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopAB)
  refine ⟨a * (QA B : ℤ) + b * (QA A : ℤ), ?_, ?_⟩
  · -- the numerator `a Q_B + b Q_A` is coprime to `Q_A Q_B = Q_{A ∪ B}`
    rw [hQAAB]
    have h' := Int.isCoprime_iff_nat_coprime.mp (isCoprime_add_mul' haI hbI hnmI)
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h'
  · -- and the point is `a/Q_A + b/Q_B` put over the common denominator
    rw [hQAAB, arcPt_add_denom' hAnz hBnz]

end Work.BourgainPlan.IonescuWainger
