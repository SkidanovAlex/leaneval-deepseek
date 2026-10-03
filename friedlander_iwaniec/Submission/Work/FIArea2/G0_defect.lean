import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop3.Defs3

/-!
# The kernel `G₀` of *FI* (8.16): the frozen definition and the count (6.12)

*FI* §6 defines the arithmetic kernel of the lattice-point main term by the **count**

  (6.12)  `G₀(z₁,z₂) = |Δ|⁻¹ · #{ (γ₁,γ₂) ∈ (ℤ/|Δ|)² : γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|) }`,

where the congruence is the pair of rational congruences (6.4)/(6.5),
`γ₁²r₂ ≡ γ₂²r₁` and `γ₁²s₂ ≡ γ₂²s₁ (mod |Δ|)` (the two congruences of (6.5), with
`z₁ = r₁ + is₁`, `z₂ = r₂ + is₂`); and §8 evaluates it
(Lemma 8.4, (8.16)) as

  `G₀(z₁,z₂) = 2 Σ_{4d ∣ Δ} (φ(d)/d) ((z₂/z₁)/d)`,

where `z₂/z₁` is the **residue class** `Re(z̄₁z₂)·|z₁|^{-2} (mod |Δ|)` of (6.6) and `(·/d)` is the
Jacobi symbol extended to even `d` by (8.15) — in Mathlib that extension is exactly
`jacobiSym a d`, which *ignores the power of two* in `d` (verified here:
`jacobiSym 5 2 = 1 = jacobiSym 5 1`).

The frozen round-3/round-4 kernel `Work.FIPlan.G0` uses instead the symbol of `Re(z̄₁z₂)`
itself, i.e. it drops the factor `|z₁|^{-2}` from (6.6).  The two functions differ by the
quadratic character `(|z₁|²/d)`, which is `−1` for a positive proportion of admissible pairs.

This file records a **machine-checked witness** of the discrepancy, for a pair that satisfies
every hypothesis of Lemma 8.4 (primary, coprime, primitive, `z₁ ≡ z₂ (mod 8)`):

* `z₁ = 1 + 4i`, `z₂ = 1 + 28i`: `Δ = 24`, the count (6.12) is `120`, so `G₀ = 120/24 = 5`,
  while the frozen `G0` is `1` — five times too small (the missing factor is `(17/3) = −1`,
  since `|z₁|² = 17` and `3 ∣ Δ/4`).
  The (8.16) sum *with the reduced residue* `Re(z̄₁z₂)·|z₁|^{-2} ≡ 113·17 ≡ 1 (mod 24)`
  reproduces the count exactly (`witness1_paperG0`), confirming that (6.6) is what the frozen
  definition omits.

A second pair, `z₁ = 27 + 34i`, `z₂ = 35 + 26i` (norms `1885`, `1901`, i.e. inside an annulus of
relative width `1.0085` — the shape the polar box (5.14) prescribes — and `Δ = −488`), shows the
same discrepancy in the *opposite* direction: the count (6.12) is `24` (so `G₀ = 24/488`) while
the frozen `G0` is `2905/488 ≈ 5.95`, about `121` times too large.  This second witness is
checked numerically only (the enumeration of `(ℤ/488)²` is too heavy for the kernel), and is
*not* asserted below.
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000 in
/-- **The count (6.12)**: the number of pairs `(γ₁,γ₂)` of rational residues mod `|Δ|` with
`γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|)`, i.e. (by (6.4)/(6.5)) with both `γ₁²r₂ ≡ γ₂²r₁` and
`γ₁²s₂ ≡ γ₂²s₁ (mod |Δ|)`.  (`Δ = 0` gives an empty range, hence the value `0`.) -/
def Cnt (z1 z2 : GaussianInt) : ℕ :=
  ((Finset.range (Work.FIPlan.absDelta z1 z2) ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
    (fun p => (p.1 ^ 2 * z2.re - p.2 ^ 2 * z1.re) % Work.FIPlan.absDelta z1 z2 = 0 ∧
              (p.1 ^ 2 * z2.im - p.2 ^ 2 * z1.im) % Work.FIPlan.absDelta z1 z2 = 0)).card

/-! ## 1. The witness satisfies the hypotheses of Lemma 8.4 -/

theorem witness1_primary : Work.FIPlan.IsPrimary (⟨1, 4⟩ : GaussianInt) :=
  ⟨by decide, by decide, by decide⟩

theorem witness1_coprime : IsCoprime (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ :=
  ⟨⟨-8, 5⟩, ⟨1, -1⟩, by ext <;> simp⟩

theorem witness1_primitive : IsCoprime (⟨1, 4⟩ : GaussianInt) (star ⟨1, 4⟩) :=
  ⟨⟨0, 2⟩, ⟨1, 2⟩, by ext <;> simp [Zsqrtd.star_mk]⟩

/-- `z₂ − z₁ = 24i = 8·(3i)`: the hypothesis `z₁ ≡ z₂ (mod 8)` of Lemma 8.4. -/
theorem witness1_mod_eight : (⟨1, 28⟩ : GaussianInt) - ⟨1, 4⟩ = 8 * ⟨0, 3⟩ := by
  ext <;> simp

/-- `Δ(1+4i, 1+28i) = 24`. -/
theorem witness1_Delta : Work.FIPlan.Delta (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ = 24 := by decide

/-- `|z₁|² = 17` and `Re(z̄₁z₂) = 113`. -/
theorem witness1_data : Work.FIPlan.gnorm (⟨1, 4⟩ : GaussianInt) = 17 ∧
    (star (⟨1, 4⟩ : GaussianInt) * ⟨1, 28⟩).re = 113 := by
  refine ⟨by decide, by decide⟩

/-! ## 2. The count (6.12) and the frozen kernel at the witness -/

set_option maxRecDepth 100000 in
/-- (6.12) at the witness: `120` pairs, so `G₀ = 120/24 = 5`. -/
theorem witness1_Cnt : Cnt (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ = 120 := by decide

/-- The frozen `Work.FIPlan.G0` at the witness evaluates to `1`. -/
theorem witness1_G0 : Work.FIPlan.G0 (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ = 1 := by
  have hJ2 : jacobiSym (113 : ℤ) 2 = 1 := by norm_num
  have hJ3 : jacobiSym (113 : ℤ) 3 = -1 := by norm_num
  have hJ6 : jacobiSym (113 : ℤ) 6 = -1 := by norm_num
  have ht2 : Nat.totient 2 = 1 := by decide
  have ht3 : Nat.totient 3 = 2 := by decide
  have ht6 : Nat.totient 6 = 2 := by decide
  have hset : (Finset.Icc 1 7).filter (fun d => 4 * d ∣ 24) = ({1, 2, 3, 6} : Finset ℕ) := by decide
  rw [Work.FIPlan.G0, Work.FIPlan.absDelta, Work.FIPlan.Delta]
  simp only [Zsqrtd.star_mk]
  norm_num
  rw [hset]
  norm_num [Finset.sum_insert, ht2, ht3, ht6, hJ2, hJ3, hJ6]

/-! ## 3. The paper's (8.16), with the residue (6.6), reproduces the count -/

/-- The residue (6.6) of `z₂/z₁` is `Re(z̄₁z₂)·|z₁|^{-2} ≡ 113 · 17 ≡ 1 (mod 24)`
(here `17 · 17 ≡ 1 (mod 24)`). -/
theorem witness1_residue : ((113 : ℤ) * 17) % 24 = 1 := by norm_num

/-- **The (8.16) sum at the witness, with the residue of (6.6)**: the symbol is that of `1`, so
every term is `φ(d)/d` and the sum is `2·(1 + 1/2 + 2/3 + 2/6) = 5 = 120/24`. -/
theorem witness1_paperG0 :
    2 * (∑ d ∈ (Finset.Icc 1 7).filter (fun d => 4 * d ∣ 24),
          ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (1 : ℤ) d : ℝ))
      = (Cnt (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ : ℝ) / 24 := by
  have ht2 : Nat.totient 2 = 1 := by decide
  have ht3 : Nat.totient 3 = 2 := by decide
  have ht6 : Nat.totient 6 = 2 := by decide
  have hJ2 : jacobiSym (1 : ℤ) 2 = 1 := by norm_num
  have hJ3 : jacobiSym (1 : ℤ) 3 = 1 := by norm_num
  have hJ6 : jacobiSym (1 : ℤ) 6 = 1 := by norm_num
  have hset : (Finset.Icc 1 7).filter (fun d => 4 * d ∣ 24) = ({1, 2, 3, 6} : Finset ℕ) := by decide
  rw [witness1_Cnt, hset]
  norm_num [Finset.sum_insert, ht2, ht3, ht6, hJ2, hJ3, hJ6]

/-! ## 4. The frozen kernel is *not* the count (6.12) -/

/-- **The defect**: at the witness the frozen kernel differs from the count (6.12) by the factor
`5`.  The frozen `G0` is therefore not *FI*'s `G₀`: it omits the reduction (6.6) of `z₂/z₁`. -/
theorem witness1_G0_ne_cnt :
    (Work.FIPlan.G0 (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ : ℝ)
      ≠ (Cnt (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ : ℝ) / 24 := by
  rw [witness1_G0, witness1_Cnt]
  norm_num

/-- The same discrepancy read as a strict inequality: the frozen kernel is five times too small
at the witness. -/
theorem witness1_G0_lt_cnt :
    (Work.FIPlan.G0 (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ : ℝ)
      < (Cnt (⟨1, 4⟩ : GaussianInt) ⟨1, 28⟩ : ℝ) / 24 := by
  rw [witness1_G0, witness1_Cnt]
  norm_num

end

end Work.FIArea2
