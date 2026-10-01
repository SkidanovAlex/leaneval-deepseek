import Mathlib
import Submission.Work.LinnikBurgess.singleton_defs
import Submission.Work.LinnikBurgess.ddDefs
import Submission.Work.LinnikBurgess.castHom_ddDefectK_three
import Submission.Work.LinnikBurgess.powerSum_three_inv_eq_of_esymm_eq
import Submission.Work.LinnikBurgess.esymm_eq_of_three_powerSums

/-!
# The third power-sum defect at a doubly degenerate class is a `p`-unit

`Work.LinnikBurgess.dd_cubicUnit`: if a pair of triples `(a,b)` carries a *cubic* doubly
degenerate critical class `r'` (a DD class at which the third power-sum defect `D₃` is a
`p`-unit), then

* `5 ≤ p` (for `p = 3` the identity `x³ = x` on `ZMod 3` makes `D₃(r) ≡ D₁(r)` vanish at every
  DD class, and `p = 2` is excluded by hypothesis), and
* at *every* doubly degenerate class `r` the third power-sum defect is a `p`-unit.

## Why every DD class is cubic

Newton's identities in the field `ZMod p` show that the three congruences
`∑(r+a_l)^{-k} ≡ ∑(r+b_l)^{-k}` (`k = 1,2,3`) are equivalent to the equality of the elementary
symmetric functions `e₁, e₂, e₃` of the two triples of *inverses* `(r+a_l)^{-1}`, `(r+b_l)^{-1}`.
A doubly degenerate class supplies the cases `k = 1,2`; the case `k = 3` is exactly
`p ∣ D₃(r).val` (reduction of `D₃` modulo `p`).  The equality of the `eᵢ` of the inverse triples
inverts (via `e₁(x^{-1}) = e₂(x)/e₃(x)`, …) to the equality of the `eᵢ` of the shifted triples
`(r+a_l)`, `(r+b_l)`, and a binomial expansion turns that into the equality of the `eᵢ` of the
triples `(a_l)`, `(b_l)` themselves.  But `e₁, e₂, e₃` determine a triple up to permutation, so at
*any* other point `s` the shifted triples `(s+a_l)`, `(s+b_l)` again have equal `eᵢ`, hence the
inverse triples have equal power sums, and in particular equal third power sums: `p ∣ D₃(s).val`
for all `s` — in particular for the cubic class `r'`, a contradiction.
-/

namespace Work.LinnikBurgess

open scoped BigOperators

/-- A prime different from `2` and `3` is at least `5`. -/
private lemma prime_five_le {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  by_contra hlt
  have hlt' : p < 5 := not_le.mp hlt
  have hpge2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hp (by norm_num)

/-- In `ZMod 3` every element is its own cube, `x³ = x`. -/
private lemma zmod3_cube_self : ∀ x : ZMod 3, x ^ 3 = x := by decide

theorem dd_cubicUnit {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hcub : ∃ r' : ZMod p, Work.LinnikBurgess.IsDDCubic p e a b r')
    (hdd : Work.LinnikBurgess.IsDD p e a b r) :
    (5 ≤ p) ∧ ¬ (p : ℕ) ∣ (Work.LinnikBurgess.ddDefectK p e a b r 3).val := by
  have hdiv : p ∣ p ^ e := by simpa using pow_dvd_pow p he
  obtain ⟨hdu, hd1, hd2, hd3⟩ := hdd
  -- Step 1: `p ≠ 3`, since on `ZMod 3` the third power-sum defect reduces to the first one.
  have hpne3 : p ≠ 3 := by
    intro h3
    obtain ⟨r', hr'⟩ := hcub
    obtain ⟨hr'u, hr'1, hr'2, hr'3⟩ := hr'.1
    refine hr'.2 ((Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hdiv (ddDefectK p e a b r' 3)).mp ?_)
    subst h3
    rw [castHom_ddDefectK_three hdiv a b r' hr'u]
    simp only [zmod3_cube_self]
    exact sub_eq_zero.mpr hr'1
  -- Step 2: `p ≥ 5` from `p` odd, `p ≠ 3`.
  have hp5 : 5 ≤ p := prime_five_le Fact.out hp2 hpne3
  refine ⟨hp5, ?_⟩
  -- Step 3: `p ≥ 5` gives `2, 3 ≠ 0` in `ZMod p`.
  have h2 : (2 : ZMod p) ≠ 0 := by
    refine fun hc => ?_
    have hp2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
    have := Nat.le_of_dvd (by norm_num) hp2dvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    refine fun hc => ?_
    have hp3dvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hc
    have := Nat.le_of_dvd (by norm_num) hp3dvd
    omega
  intro hpd
  -- Reduction of `D₃(r)` modulo `p` and hence the third power-sum equality at `r`.
  have h0 : ZMod.castHom hdiv (ZMod p) (ddDefectK p e a b r 3) = 0 :=
    (Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hdiv _).mpr hpd
  rw [castHom_ddDefectK_three hdiv a b r hdu] at h0
  have H3r : (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹) ^ 3)
      = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹) ^ 3) := sub_eq_zero.mp h0
  -- The elementary symmetric functions of the triples `(a_l)` and `(b_l)` agree.
  have hsym := esymm_eq_of_three_powerSums h2 h3 (fun l => (a l : ZMod p)) (fun l => (b l : ZMod p)) r hdu
    hd1 hd2 H3r
  -- ... hence so do the third power sums of the inverses at the cubic class `r'`.
  obtain ⟨r', hr'⟩ := hcub
  obtain ⟨hr'u, hr'1, hr'2, hr'3⟩ := hr'.1
  have H3r' : (∑ l : Fin 3, ((r' + (a l : ZMod p))⁻¹) ^ 3)
      = (∑ l : Fin 3, ((r' + (b l : ZMod p))⁻¹) ^ 3) :=
    powerSum_three_inv_eq_of_esymm_eq (fun l => (a l : ZMod p)) (fun l => (b l : ZMod p)) r'
      hsym.1 hsym.2.1 hsym.2.2 hr'u
  have h0' : ZMod.castHom hdiv (ZMod p) (ddDefectK p e a b r' 3) = 0 := by
    rw [castHom_ddDefectK_three hdiv a b r' hr'u, sub_eq_zero]
    exact H3r'
  exact hr'.2 ((Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hdiv _).mp h0')

end Work.LinnikBurgess
