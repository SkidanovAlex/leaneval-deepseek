import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj
import Submission.Work.ShafarevichKoch.span_sc_mul_span_sc
import Submission.Work.ShafarevichKoch.span_sc_sq_eq_of_dvd

/-!
# Auxiliary ideal/class-group interface for the genus argument over `Kc = ℚ(√-30030)`

This module fixes the vocabulary in which the genus argument is phrased:

* `span_sc d` is the ideal `⟨d, √-30030⟩` of `𝓞 Kc = ℤ[√-30030]` (`√-30030 = scR`);
* `mk0Span d hd` is its class in `Cl(𝓞 Kc)`, for `d ∣ 30030`.

The key facts (proved elsewhere) are that `⟨d, scR⟩² = (d)` is principal, that
`⟨a, scR⟩ * ⟨b, scR⟩ = ⟨a*b, scR⟩` for coprime `a, b ∣ 30030` (so the classes multiply), and
that `⟨30030, scR⟩ = (scR)` is principal.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- The ideal `⟨d, √-30030⟩` of `𝓞 Kc = ℤ[√-30030]`. -/
def spanSc (d : ℕ) : Ideal (𝓞 Kc) := Ideal.span ({(↑d : 𝓞 Kc), scR} : Set (𝓞 Kc))

theorem spanSc_ne_bot (d : ℕ) (hd : d ∣ 30030) : spanSc d ≠ ⊥ := by
  intro hbot
  have hdvd : (↑d : 𝓞 Kc) ∈ (⊥ : Ideal (𝓞 Kc)) := by
    rw [← hbot]
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [Ideal.mem_bot] at hdvd
  exact (Nat.pos_of_dvd_of_pos hd (by norm_num)).ne' (Nat.cast_eq_zero.mp hdvd)

theorem spanSc_one_eq_top : spanSc 1 = ⊤ := by
  rw [spanSc, Ideal.eq_top_iff_one]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- `⟨d, √-30030⟩` as an element of the nonzero-divisor monoid. -/
def spanScUnit (d : ℕ) (hd : d ∣ 30030) : (Ideal (𝓞 Kc))⁰ :=
  ⟨spanSc d, mem_nonZeroDivisors_of_ne_zero (spanSc_ne_bot d hd)⟩

/-- The class of `⟨d, √-30030⟩` in `Cl(𝓞 Kc)`. -/
def mk0Span (d : ℕ) (hd : d ∣ 30030) : ClassGroup (𝓞 Kc) :=
  ClassGroup.mk0 (spanScUnit d hd)

/-- `⟨1, scR⟩ = ⊤` has trivial class. -/
theorem mk0Span_one : mk0Span 1 (by norm_num) = 1 := by
  refine (ClassGroup.mk0_eq_one_iff (spanScUnit 1 (by norm_num)).2).mpr ?_
  refine ⟨1, ?_⟩
  show spanSc 1 = 𝓞 Kc ∙ (1 : 𝓞 Kc)
  rw [spanSc_one_eq_top]
  exact Ideal.span_singleton_one.symm

/-- Every prime dividing `30030 = 2·3·5·7·11·13` is one of those six primes. -/
theorem prime_dvd_30030 {p : ℕ} (hp : p.Prime) (h : p ∣ 30030) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have key : ∀ {q : ℕ}, q.Prime → p ∣ q → p = q := by
    intro q hq hpq
    rcases (Nat.dvd_prime hq).mp hpq with h1 | h1
    · exact absurd h1 hp.ne_one
    · exact h1
  have hfac : (30030 : ℕ) = 2 * (3 * (5 * (7 * (11 * 13)))) := by norm_num
  rw [hfac] at h
  rcases (hp.dvd_mul).mp h with h | h
  · exact Or.inl (key (by norm_num) h)
  rcases (hp.dvd_mul).mp h with h | h
  · exact Or.inr (Or.inl (key (by norm_num) h))
  rcases (hp.dvd_mul).mp h with h | h
  · exact Or.inr (Or.inr (Or.inl (key (by norm_num) h)))
  rcases (hp.dvd_mul).mp h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key (by norm_num) h))))
  rcases (hp.dvd_mul).mp h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key (by norm_num) h)))))

/-- `30030 = 2·3·5·7·11·13` is squarefree. -/
theorem squarefree_30030 : Squarefree (30030 : ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hd
  have hxdvd : x ∣ 30030 := dvd_trans (dvd_mul_right x x) hd
  rcases prime_dvd_30030 hx hxdvd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hd

/-- Every divisor of `30030` is squarefree. -/
theorem squarefree_of_dvd_30030 {d : ℕ} (hd : d ∣ 30030) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd squarefree_30030


/-- `⟨d, √-30030⟩ ≠ ⊥` for `d ≠ 0`. -/
theorem spanSc_ne_bot' (d : ℕ) (hd : d ≠ 0) : spanSc d ≠ ⊥ := by
  intro hbot
  have hdvd : (↑d : 𝓞 Kc) ∈ (⊥ : Ideal (𝓞 Kc)) := by
    rw [← hbot]
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [Ideal.mem_bot] at hdvd
  exact hd (Nat.cast_eq_zero.mp hdvd)

/-- `⟨d, √-30030⟩` as a nonzero-divisor, for any `d ≠ 0`. -/
def spanScUnit' (d : ℕ) (hd : d ≠ 0) : (Ideal (𝓞 Kc))⁰ :=
  ⟨spanSc d, mem_nonZeroDivisors_of_ne_zero (spanSc_ne_bot' d hd)⟩


/-- `scR = √-30030` is nonzero in `𝓞 Kc`. -/
theorem scR_ne_zero : scR ≠ (0 : 𝓞 Kc) := by
  intro hz
  have h2 : ((scR : 𝓞 Kc) : Kc) = 0 := by rw [hz]; rfl
  rw [scR_coe] at h2
  have h3 := sc_sq_num
  rw [h2, mul_zero] at h3
  norm_num at h3

/-! ## Classes of the ideals `⟨d, √-30030⟩` -/

/-- The classes `[⟨a, scR⟩]` multiply: `[⟨a*b, scR⟩] = [⟨a, scR⟩] * [⟨b, scR⟩]` for coprime
divisors `a, b` of `30030`. -/
theorem mk0Span_mul {a b : ℕ} (ha : a ∣ 30030) (hb : b ∣ 30030) (hab : Nat.Coprime a b) :
    mk0Span (a * b) (hab.mul_dvd_of_dvd_of_dvd ha hb) = mk0Span a ha * mk0Span b hb := by
  have h : spanScUnit a ha * spanScUnit b hb
      = spanScUnit (a * b) (hab.mul_dvd_of_dvd_of_dvd ha hb) := by
    refine Subtype.ext ?_
    rw [Submonoid.coe_mul]
    simp only [Subtype.coe_mk, spanScUnit, spanSc]
    exact span_sc_mul_span_sc ha hb hab
  rw [mk0Span, mk0Span, mk0Span, ← h, map_mul]

/-- `[⟨d, scR⟩]` is `2`-torsion, because `⟨d, scR⟩² = (d)` is principal. -/
theorem mk0Span_sq (d : ℕ) (hd : d ∣ 30030) : mk0Span d hd ^ 2 = 1 := by
  have h : spanScUnit d hd * spanScUnit d hd
      = ⟨Ideal.span ({(↑d : 𝓞 Kc)} : Set (𝓞 Kc)),
          mem_nonZeroDivisors_of_ne_zero (by
            rw [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
            exact Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hd (by norm_num)).ne')⟩ := by
    refine Subtype.ext ?_
    rw [Submonoid.coe_mul]
    simp only [Subtype.coe_mk, spanScUnit, spanSc]
    rw [← pow_two]
    exact span_sc_sq_eq_of_dvd d hd
  rw [mk0Span, ← map_pow, pow_two, h]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  refine ⟨(↑d : 𝓞 Kc), ?_⟩
  show Ideal.span ({(↑d : 𝓞 Kc)} : Set (𝓞 Kc)) = 𝓞 Kc ∙ (↑d : 𝓞 Kc)
  rfl

/-- `⟨30030, scR⟩ = (scR)`: the product of all ramified primes is principal. -/
theorem spanSc_30030 : spanSc 30030 = Ideal.span ({scR} : Set (𝓞 Kc)) := by
  rw [spanSc]
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with hz | hz
    · rw [hz]
      refine Ideal.mem_span_singleton.mpr ⟨-scR, ?_⟩
      rw [mul_neg, scR_sq]
      ring
    · rw [hz]
      exact Ideal.subset_span (Set.mem_singleton scR)
  · refine Ideal.span_le.mpr ?_
    intro z hz
    rw [hz]
    exact Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR)))

theorem mk0Span_30030 : mk0Span 30030 (by norm_num) = 1 := by
  have h : spanScUnit 30030 (by norm_num)
      = ⟨Ideal.span ({scR} : Set (𝓞 Kc)),
          mem_nonZeroDivisors_of_ne_zero (by
            rw [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
            exact scR_ne_zero)⟩ :=
    Subtype.ext spanSc_30030
  rw [mk0Span, h]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  exact ⟨scR, rfl⟩

/-- Complementary divisors define the same class: `[⟨d, scR⟩] = [⟨30030/d, scR⟩]`. -/
theorem mk0Span_compl (d : ℕ) (hd : d ∣ 30030) :
    mk0Span d hd = mk0Span (30030 / d) (Nat.div_dvd_of_dvd hd) := by
  have hdvdd : 30030 / d ∣ 30030 := Nat.div_dvd_of_dvd hd
  have hcop : Nat.Coprime d (30030 / d) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpd : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have hpd' : p ∣ 30030 / d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    obtain ⟨k, hk⟩ := hpd
    obtain ⟨l, hl⟩ := hpd'
    have hpp : p * p ∣ 30030 := by
      rw [← Nat.mul_div_cancel' hd, hl, hk]
      exact ⟨k * l, by ring⟩
    have hunit : IsUnit p := squarefree_30030 p hpp
    exact hp.ne_one (Nat.isUnit_iff.mp hunit)
  have hmul := mk0Span_mul hd hdvdd hcop
  have hmul' : mk0Span 30030 (by norm_num) = mk0Span d hd * mk0Span (30030 / d) hdvdd := by
    convert hmul using 2
    exact (Nat.mul_div_cancel' hd).symm
  rw [mk0Span_30030] at hmul'
  have hinv : mk0Span d hd = (mk0Span (30030 / d) hdvdd)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hmul'.symm
  have hBsq : mk0Span (30030 / d) hdvdd * mk0Span (30030 / d) hdvdd = 1 := by
    rw [← pow_two]
    exact mk0Span_sq (30030 / d) hdvdd
  have hBinv : mk0Span (30030 / d) hdvdd = (mk0Span (30030 / d) hdvdd)⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr hBsq
  rw [hinv, ← hBinv]

/-- `⟨c*d, c·scR⟩` has the same class as `⟨d, scR⟩` (`c ≠ 0`). -/
theorem mk0_span_pair_eq (c d : ℕ) (hc : c ≠ 0) (hd : d ∣ 30030)
    (h : Ideal.span ({(↑(c * d) : 𝓞 Kc), (↑c : 𝓞 Kc) * scR} : Set (𝓞 Kc))
        ∈ (Ideal (𝓞 Kc))⁰) :
    ClassGroup.mk0 ⟨_, h⟩ = mk0Span d hd := by
  set U : (Ideal (𝓞 Kc))⁰ := ⟨Ideal.span ({(↑c : 𝓞 Kc)} : Set (𝓞 Kc)),
      mem_nonZeroDivisors_of_ne_zero (by
        rw [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact Nat.cast_ne_zero.mpr hc)⟩ with hU
  have hsplit : U * spanScUnit d hd
      = ⟨Ideal.span ({(↑(c * d) : 𝓞 Kc), (↑c : 𝓞 Kc) * scR} : Set (𝓞 Kc)), h⟩ := by
    refine Subtype.ext ?_
    rw [Submonoid.coe_mul]
    simp only [hU, Subtype.coe_mk, spanScUnit, spanSc]
    rw [Ideal.span_mul_span]
    congr 1
    ext z
    rw [Set.mem_mul]
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨a, rfl, b, hb, h'⟩
      rcases hb with rfl | rfl
      · exact Or.inl (by rw [← h']; push_cast; ring)
      · exact Or.inr (by rw [← h'])
    · rintro (h' | h')
      · exact ⟨↑c, rfl, ↑d, Or.inl rfl, by rw [h']; push_cast; ring⟩
      · exact ⟨↑c, rfl, scR, Or.inr rfl, by rw [h']⟩
  have hone : ClassGroup.mk0 U = 1 := by
    refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
    refine ⟨(↑c : 𝓞 Kc), ?_⟩
    show Ideal.span ({(↑c : 𝓞 Kc)} : Set (𝓞 Kc)) = 𝓞 Kc ∙ (↑c : 𝓞 Kc)
    rfl
  rw [← hsplit, map_mul, hone, one_mul]
  rfl


end Work.ShafarevichKoch
