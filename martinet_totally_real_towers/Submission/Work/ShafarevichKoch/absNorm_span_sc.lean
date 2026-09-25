import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj

/-!
# The norm of the ideal `⟨c·d, c·√-30030⟩` in `𝓞 ℚ(√-30030)`

`𝓞 Kc = ℤ[√-30030]`, `scR = √-30030`, and `d ∣ 30030`.  In the `ℤ`-coordinates
`x + y·scR` the ideal `⟨cd, c·scR⟩` is the lattice `{(x,y) : cd ∣ x, c ∣ y}`, of index
`cd · c`; equivalently it is `(c) · ⟨d, scR⟩` and the factor `⟨d, scR⟩` has index `d`
(because `⟨d, scR⟩² = (d)`, since `30030` is squarefree).
-/

namespace Work.ShafarevichKoch

open NumberField
open scoped NumberField
open Work.ClassFieldTower

/-- `d ∣ 30030 ⟹ gcd (d²) 30030 = d`.  Indeed `30030` is squarefree, so any common divisor
`e` of `d²` and `30030` is squarefree and divides `d`. -/
private lemma gcd_mul_self_dWit (d : ℕ) (hd : d ∣ 30030) : Nat.gcd (d * d) 30030 = d := by
  have hsq : Squarefree (30030 : ℕ) := dWit_squarefree_nat
  refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right d d) hd)
  have hg2 : Nat.gcd (d * d) 30030 ∣ 30030 := Nat.gcd_dvd_right _ _
  have hsqg : Squarefree (Nat.gcd (d * d) 30030) := hsq.squarefree_of_dvd hg2
  refine (hsqg.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
  simpa [pow_two] using Nat.gcd_dvd_left (d * d) 30030

/-- `⟨d, scR⟩² = (d)` for `d ∣ 30030`.  Both inclusions are checked on generators: `d²`, `d·scR`
and `scR² = -30030` all lie in `(d)`; conversely `d` is a `ℤ`-combination of `d²` and `30030`
by Bézout, using `gcd d² 30030 = d`. -/
private lemma span_sc_pair_sq (d : ℕ) (hd : d ∣ 30030) :
    (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc)))^2 = Ideal.span ({↑d} : Set (𝓞 Kc)) := by
  have hsup : Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({↑d} : Set (𝓞 Kc)) ⊔ Ideal.span ({scR} : Set (𝓞 Kc)) := by
    rw [Ideal.span_insert]
  have hdvd : (↑d : 𝓞 Kc) ∣ (30030 : 𝓞 Kc) := by
    obtain ⟨k, hk⟩ := hd
    exact ⟨↑k, by rw [← Nat.cast_mul, ← hk]; norm_num⟩
  apply le_antisymm
  · rw [pow_two, hsup, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)
    · rw [Ideal.span_singleton_mul_span_singleton, scR_sq, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_span_singleton.mpr (dvd_neg.mpr hdvd)
  · rw [Ideal.span_singleton_le_iff_mem]
    have hbez := Nat.gcd_eq_gcd_ab (d * d) 30030
    rw [gcd_mul_self_dWit d hd] at hbez
    have hbez' : (↑d : 𝓞 Kc) = (↑(d * d) : 𝓞 Kc) * ((d * d).gcdA 30030 : 𝓞 Kc)
        + (30030 : 𝓞 Kc) * ((d * d).gcdB 30030 : 𝓞 Kc) := by
      have h := congrArg (fun z : ℤ => (z : 𝓞 Kc)) hbez
      push_cast at h
      simpa using h
    have h1 : (↑(d * d) : 𝓞 Kc) = (↑d : 𝓞 Kc) * (↑d : 𝓞 Kc) := by push_cast; ring
    have h2 : (30030 : 𝓞 Kc) = -(scR * scR) := by rw [scR_sq, neg_neg]
    have hmem1 : (↑d : 𝓞 Kc) * (↑d : 𝓞 Kc)
        ∈ (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc)))^2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl)))
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl)))
    have hmem2 : scR * scR ∈ (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc)))^2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
    have hmem : ((d * d).gcdA 30030 : 𝓞 Kc) * ((↑d : 𝓞 Kc) * (↑d : 𝓞 Kc))
        + (-((d * d).gcdB 30030 : 𝓞 Kc)) * (scR * scR)
        ∈ (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc)))^2 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem1) (Ideal.mul_mem_left _ _ hmem2)
    convert hmem using 1
    calc (↑d : 𝓞 Kc)
        = (↑(d * d) : 𝓞 Kc) * ((d * d).gcdA 30030 : 𝓞 Kc)
          + (30030 : 𝓞 Kc) * ((d * d).gcdB 30030 : 𝓞 Kc) := hbez'
      _ = ((d * d).gcdA 30030 : 𝓞 Kc) * ((↑d : 𝓞 Kc) * (↑d : 𝓞 Kc))
          + (-((d * d).gcdB 30030 : 𝓞 Kc)) * (scR * scR) := by rw [h1, h2]; ring

/-- `⟨d, scR⟩` has absolute norm `d` for `d ∣ 30030`.  Squaring and using
`⟨d, scR⟩² = (d)` gives `(absNorm ⟨d, scR⟩)² = d²`, and natural numbers are determined by
their squares. -/
private lemma absNorm_span_sc_pair (d : ℕ) (hd : d ∣ 30030) :
    Ideal.absNorm (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc))) = d := by
  have hfin : Module.finrank ℤ (𝓞 Kc) = 2 := by
    rw [NumberField.RingOfIntegers.rank Kc, finrank_eq_two]
  have hmul : Ideal.absNorm (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc)))
      * Ideal.absNorm (Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc))) = d * d := by
    rw [← map_mul Ideal.absNorm, ← pow_two, span_sc_pair_sq d hd,
      Ideal.absNorm_span_natCast, hfin]
    ring
  exact Nat.mul_self_inj.mp hmul

/-- `⟨cd, c·scR⟩ = (c)·⟨d, scR⟩`: distributing the product of the two principal-generated
ideals `(c) · (⟨d⟩ ⊔ ⟨scR⟩)`. -/
private lemma span_singleton_mul_span_sc_pair (c d : ℕ) :
    Ideal.span ({(↑c : 𝓞 Kc)} : Set (𝓞 Kc))
        * Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(↑(c * d) : 𝓞 Kc), (↑c : 𝓞 Kc) * scR} : Set (𝓞 Kc)) := by
  conv_lhs => rw [Ideal.span_insert]
  rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, ← Ideal.span_insert]

/-- `𝓞 Kc = ℤ[√-30030]` with `scR = √-30030`, and `d ∣ 30030`.  Then the index (norm) of the
ideal `⟨c*d, c·√-30030⟩` is `c*d*c`: in `𝓞 Kc = ℤ ⊕ ℤ·scR` that ideal is spanned by `(cd,0)`,
`(0,cd)`, `(-30030c,0)`, `(0,c)`, so its index is `gcd(cd, 30030c) · gcd(cd, c) = cd · c`
(using `d ∣ 30030`).  Equivalently `Ideal.absNorm` of the ideal generated by `c*d` and `c·scR`
equals `c * d * c`; note `c = 0` gives `⊥` with norm `0` on both sides. -/
theorem absNorm_span_sc (c d : ℕ) (hd : d ∣ 30030) :
    Ideal.absNorm (Ideal.span ({(↑(c * d) : NumberField.RingOfIntegers Work.ClassFieldTower.Kc),
      (↑c : NumberField.RingOfIntegers Work.ClassFieldTower.Kc) * Work.ClassFieldTower.scR}
      : Set (NumberField.RingOfIntegers Work.ClassFieldTower.Kc))) = c * d * c := by
  have hfin : Module.finrank ℤ (𝓞 Kc) = 2 := by
    rw [NumberField.RingOfIntegers.rank Kc, finrank_eq_two]
  rw [← span_singleton_mul_span_sc_pair c d, map_mul Ideal.absNorm,
    Ideal.absNorm_span_natCast, hfin, absNorm_span_sc_pair d hd]
  ring

end Work.ShafarevichKoch
