/-
# `Submission.Work.FIArea5.S16Hecke.heckeLam_localRec`

The **local recursion** for the Hecke eigenvalues of `ℤ[i]` (paper (16.30) and the Euler
factor of (16.17)):

  `λ(p^{ν+2}) = λ(p)·λ(p^{ν+1}) - (λ(p)² - λ(p²))·λ(p^ν)`,   and   `‖λ(p)² - λ(p²)‖ ≤ 1`.

The constant `c := λ(p)² - λ(p²)` is the T²-coefficient of the local factor
`Σ_ν λ(p^ν)T^ν = 1/(1 - λ(p)T + cT²)`: at a split prime `p ≡ 1 (4)` it equals
`ψ(π)ψ(π̄)`, at an inert prime `p ≡ 3 (4)` it equals `-ψ(-p)`, and at `p = 2` it is `0`.
In every case `‖c‖ ≤ 1` since `‖ψ‖ ≤ 1`.

The two structural inputs are proved in the sibling modules
`FIArea5/S16Hecke/splitPrimaryClass` and `FIArea5/S16Hecke/inertPrimaryClass`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_one
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## Elementary facts about powers -/

lemma gnorm_pow (z : GaussianInt) (n : ℕ) : gnorm (z ^ n) = (gnorm z) ^ n := by
  induction n with
  | zero => simp [gnorm_one]
  | succ n ih => rw [pow_succ, gnorm_mul, ih, pow_succ]

lemma hlr_isPrimary_pow {z : GaussianInt} (hz : IsPrimary z) (n : ℕ) : IsPrimary (z ^ n) := by
  induction n with
  | zero => simpa using isPrimary_one
  | succ n ih => rw [pow_succ]; exact isPrimary_mul ih hz

lemma psi_pow (chi : GaussianInt → ℂ) (k : ℤ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (z : GaussianInt) (n : ℕ) : psi chi k (z ^ n) = (psi chi k z) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; simp [psi_one, h1]
  | succ n ih => rw [pow_succ, pow_succ, psi_mul chi k hmul, ih]

/-! ## The two local generating sequences -/

/-- At a **split** prime the local eigenvalues are `A_ν = Σ_{a+b=ν} x^a y^b` where
`x = ψ(π)`, `y = ψ(π̄)`. -/
def geo (x y : ℂ) (ν : ℕ) : ℂ := ∑ a ∈ Finset.range (ν + 1), x ^ a * y ^ (ν - a)

lemma geo_succ (x y : ℂ) (ν : ℕ) : geo x y (ν + 1) = y ^ (ν + 1) + x * geo x y ν := by
  unfold geo
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, one_mul]
  have hS : (∑ k ∈ Finset.range (ν + 1), x^(k+1)*y^(ν+1-(k+1)))
          = x * (∑ i ∈ Finset.range (ν + 1), x^i * y^(ν-i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    have h : ν + 1 - (a+1) = ν - a := by omega
    rw [h, pow_succ]; ring
  rw [hS, add_comm]

lemma geo_one (x y : ℂ) : geo x y 1 = x + y := by
  unfold geo; norm_num [Finset.sum_range_succ]; ring

lemma geo_two (x y : ℂ) : geo x y 2 = x^2 + x*y + y^2 := by
  unfold geo; norm_num [Finset.sum_range_succ]; ring

lemma geo_rec (x y : ℂ) (ν : ℕ) :
    geo x y (ν + 2) = geo x y 1 * geo x y (ν + 1) - ((geo x y 1)^2 - geo x y 2) * geo x y ν := by
  have hν : ν + 2 = (ν + 1) + 1 := by omega
  rw [hν, geo_succ, geo_succ, geo_one, geo_two]
  ring

/-- At an **inert** prime the local eigenvalues are `B_ν = x^{ν/2}` for even `ν` and `0`
for odd `ν`, where `x = ψ(-p)`. -/
def geoInert (x : ℂ) (ν : ℕ) : ℂ := if Even ν then x ^ (ν / 2) else 0

lemma geoInert_rec (x : ℂ) (ν : ℕ) :
    geoInert x (ν + 2)
      = geoInert x 1 * geoInert x (ν + 1) - ((geoInert x 1)^2 - geoInert x 2) * geoInert x ν := by
  have h1 : geoInert x 1 = 0 := by simp [geoInert]
  have h2 : geoInert x 2 = x := by norm_num [geoInert]
  rw [h1, h2]
  simp only [geoInert]
  rcases Nat.even_or_odd ν with h | h
  · obtain ⟨k, rfl⟩ := h
    have e2 : Even (k + k + 2) := ⟨k + 1, by ring⟩
    have e1 : ¬ Even (k + k + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨k, by ring⟩
    have e0 : Even (k + k) := ⟨k, rfl⟩
    rw [if_pos e2, if_neg e1, if_pos e0]
    have hd : (k + k + 2) / 2 = (k + k) / 2 + 1 := by omega
    rw [hd, pow_succ]
    ring
  · obtain ⟨k, hk⟩ := h
    subst hk
    have e2 : ¬ Even (2 * k + 1 + 2) := by rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
    have e1 : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
    have e0 : ¬ Even (2 * k + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩
    rw [if_neg e2, if_pos e1, if_neg e0]
    ring

/-! ## The bridges from the classification of primary elements to `heckeLam` -/

/-- **Split bridge.** If `π, π'` are the two primary irreducibles of norm `p` (in the sense of
`splitPrimaryClass`), then `λ(p^ν) = Σ_{a+b=ν} ψ(π)^a ψ(π')^b`. -/
lemma heckeLam_splitSum (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ) (hp : 0 < p)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (π π' : GaussianInt) (hπ : IsPrimary π) (hπ' : IsPrimary π')
    (hgπ : gnorm π = p) (hgπ' : gnorm π' = p)
    (hclass : ∀ ν z, IsPrimary z → gnorm z = p^ν → ∃! a, a ≤ ν ∧ z = π^a * π'^(ν-a))
    (ν : ℕ) :
    heckeLam chi k (p^ν) = geo (psi chi k π) (psi chi k π') ν := by
  classical
  change heckeLam chi k (p^ν) = ∑ a ∈ Finset.range (ν+1), (psi chi k π)^a * (psi chi k π')^(ν-a)
  unfold heckeLam
  set F : ℕ → GaussianInt := fun a => π^a * π'^(ν-a) with hF
  have hFprim : ∀ a, IsPrimary (F a) := by
    intro a; rw [hF]; exact isPrimary_mul (hlr_isPrimary_pow hπ a) (hlr_isPrimary_pow hπ' (ν-a))
  have hFgn : ∀ a, a ≤ ν → gnorm (F a) = p^ν := by
    intro a haa
    rw [hF, gnorm_mul, gnorm_pow, gnorm_pow, hgπ, hgπ', ← pow_add]
    congr 1; omega
  have hS : (gBox ((p^ν : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p^ν)
      = (Finset.range (ν+1)).image F := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨-, hprim, hgn⟩
      obtain ⟨a, ha, haz⟩ := (hclass ν z hprim hgn).exists
      exact ⟨a, Nat.lt_succ_of_le ha, haz.symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨mem_gBox_of_gnorm_le (Nat.cast_pos.mpr (pow_pos hp ν))
          (by rw [hFgn a (Nat.lt_succ_iff.mp ha)]), hFprim a, hFgn a (Nat.lt_succ_iff.mp ha)⟩
  rw [hS, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [hF]
    rw [psi_mul chi k hmul, psi_pow chi k hmul h1, psi_pow chi k hmul h1]
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    refine (hclass ν (F a) (hFprim a) (hFgn a (Nat.lt_succ_iff.mp ha))).unique
      ⟨Nat.lt_succ_iff.mp ha, rfl⟩ ⟨Nat.lt_succ_iff.mp hb, ?_⟩
    rw [hF] at hab ⊢; exact hab

/-- **Inert bridge, even case.** If `q = -p` is the primary generator of the inert prime `p`,
then `λ(p^{2μ}) = ψ(q)^μ`. -/
lemma heckeLam_inertSumEven (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ) (hp : 0 < p)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (q : GaussianInt) (hq : IsPrimary q) (hgq : gnorm q = p ^ 2)
    (hclass : ∀ ν z, IsPrimary z → gnorm z = p^ν → ∃! μ', ν = 2*μ' ∧ z = q^μ')
    (μ : ℕ) : heckeLam chi k (p^(2*μ)) = (psi chi k q)^μ := by
  classical
  unfold heckeLam
  have hqμ_prim : IsPrimary (q^μ) := hlr_isPrimary_pow hq μ
  have hqμ_gn : gnorm (q^μ) = p^(2*μ) := by
    rw [gnorm_pow, hgq, pow_mul]
  have hS : (gBox ((p^(2*μ) : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p^(2*μ))
      = {q^μ} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hprim, hgn⟩
      obtain ⟨μ', hμ', hz⟩ := (hclass (2*μ) z hprim hgn).exists
      have hμeq : μ' = μ := by omega
      rw [hμeq] at hz; exact hz
    · rintro rfl
      exact ⟨mem_gBox_of_gnorm_le (Nat.cast_pos.mpr (pow_pos hp _)) (by rw [hqμ_gn]), hqμ_prim, hqμ_gn⟩
  rw [hS, Finset.sum_singleton]
  exact psi_pow chi k hmul h1 q μ

/-- **Inert bridge, odd case.** For odd `ν` no primary element has norm `p^ν`, so `λ(p^ν) = 0`. -/
lemma heckeLam_inertSumOdd (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ)
    (q : GaussianInt) (hclass : ∀ ν z, IsPrimary z → gnorm z = p^ν → ∃! μ', ν = 2*μ' ∧ z = q^μ')
    (ν : ℕ) (hodd : ¬ Even ν) : heckeLam chi k (p^ν) = 0 := by
  classical
  unfold heckeLam
  have hS : (gBox ((p^ν : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p^ν) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hprim, hgn⟩ := hz
    obtain ⟨μ', hμ', -⟩ := (hclass ν z hprim hgn).exists
    exact hodd ⟨μ', by omega⟩
  rw [hS, Finset.sum_empty]

/-- **Inert bridge.** `λ(p^ν) = ψ(-p)^{ν/2}` for even `ν` and `= 0` for odd `ν`. -/
lemma heckeLam_inertSum (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ) (hp : 0 < p)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (q : GaussianInt) (hq : IsPrimary q) (hgq : gnorm q = p ^ 2)
    (hclass : ∀ ν z, IsPrimary z → gnorm z = p^ν → ∃! μ', ν = 2*μ' ∧ z = q^μ') :
    ∀ ν : ℕ, heckeLam chi k (p^ν) = geoInert (psi chi k q) ν := by
  intro ν
  unfold geoInert
  by_cases hev : Even ν
  · obtain ⟨μ, hμm⟩ : ∃ μ, ν = 2*μ := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have hdiv : ν / 2 = μ := by rw [hμm]; omega
    rw [if_pos hev, hdiv, hμm]
    exact heckeLam_inertSumEven chi k p hp hmul h1 q hq hgq hclass μ
  · rw [if_neg hev]
    exact heckeLam_inertSumOdd chi k p q hclass ν hev

/-! ## The local recursion -/

theorem heckeLam_localRec (chi : GaussianInt → ℂ) (k : ℤ) (p : ℕ) (hp : p.Prime)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    (∀ ν : ℕ, heckeLam chi k (p ^ (ν + 2)) =
        heckeLam chi k p * heckeLam chi k (p ^ (ν + 1)) -
          ((heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)) * heckeLam chi k (p ^ ν)) ∧
      ‖(heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)‖ ≤ 1 := by
  classical
  by_cases hchi0 : chi 1 = 0
  · -- the character vanishes identically
    have hz : ∀ z : GaussianInt, chi z = 0 := by
      intro z
      have h := hmul 1 z
      rw [one_mul] at h
      rw [hchi0, zero_mul] at h
      exact h
    have hlam : ∀ n : ℕ, heckeLam chi k n = 0 := by
      intro n
      unfold heckeLam
      apply Finset.sum_eq_zero
      intro z _
      simp only [psi, hz z, zero_mul]
    refine ⟨?_, ?_⟩
    · intro ν
      simp only [hlam]
      ring
    · simp only [hlam]
      norm_num
  · -- `χ(1) = 1`
    have hchi1 : chi 1 = 1 := by
      have h : chi 1 * chi 1 = chi 1 := by
        have h' := hmul 1 1
        rw [one_mul] at h'
        exact h'.symm
      have h2 : chi 1 * (chi 1 - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
      rcases mul_eq_zero.mp h2 with h0 | h0
      · exact absurd h0 hchi0
      · exact sub_eq_zero.mp h0
    have hlam1 : heckeLam chi k 1 = 1 := by rw [heckeLam_one, hchi1]
    have hp2le : 2 ≤ p := hp.two_le
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · -- `p = 2`
      subst hp2
      have h2 : heckeLam chi k 2 = 0 := heckeLam_even chi k (by norm_num)
      have h2sq : heckeLam chi k (2 ^ 2) = 0 := heckeLam_even chi k (by norm_num)
      refine ⟨?_, ?_⟩
      · intro ν
        have hL : heckeLam chi k (2 ^ (ν + 2)) = 0 := by
          apply heckeLam_even chi k
          exact ⟨2 ^ (ν + 1), by
            rw [show ν + 2 = (ν + 1) + 1 from by omega, pow_succ]; ring⟩
        rw [hL, h2, h2sq]; ring
      · rw [h2, h2sq]; norm_num
    · -- `p` odd, so `p % 4 = 1` or `p % 4 = 3`
      obtain ⟨k0, hk0⟩ := hpodd
      have hp41 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hp41 with h1 | h3
      · -- split prime
        obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp h1
        have hA : ∀ ν, heckeLam chi k (p^ν) = geo (psi chi k π) (psi chi k π') ν :=
          fun ν => heckeLam_splitSum chi k p (by omega) hmul hchi1 π π' hπ hπ' hgπ hgπ' hclass ν
        have hp1 : heckeLam chi k p = geo (psi chi k π) (psi chi k π') 1 := by
          simpa only [pow_one] using hA 1
        have hp2 : heckeLam chi k (p^2) = geo (psi chi k π) (psi chi k π') 2 := hA 2
        have hc : (geo (psi chi k π) (psi chi k π') 1)^2 - geo (psi chi k π) (psi chi k π') 2
            = psi chi k π * psi chi k π' := by
          rw [geo_one, geo_two]; ring
        refine ⟨?_, ?_⟩
        · intro ν
          rw [hA (ν+2), hp1, hA (ν+1), hp2, hA ν]
          exact geo_rec (psi chi k π) (psi chi k π') ν
        · rw [hp1, hp2, hc, norm_mul]
          exact mul_le_one₀ (norm_psi_le_one chi k hb π) (norm_nonneg _)
            (norm_psi_le_one chi k hb π')
      · -- inert prime
        obtain ⟨hqp, -, hqgn, hclass⟩ := inertPrimaryClass p hp h3
        have hA : ∀ ν, heckeLam chi k (p^ν) = geoInert (psi chi k (-(p : GaussianInt))) ν :=
          fun ν => heckeLam_inertSum chi k p (by omega) hmul hchi1 (-(p : GaussianInt))
            hqp hqgn hclass ν
        have hp1 : heckeLam chi k p = geoInert (psi chi k (-(p : GaussianInt))) 1 := by
          simpa only [pow_one] using hA 1
        have hp2 : heckeLam chi k (p^2) = geoInert (psi chi k (-(p : GaussianInt))) 2 := hA 2
        have hc : (geoInert (psi chi k (-(p : GaussianInt))) 1)^2
              - geoInert (psi chi k (-(p : GaussianInt))) 2 = -(psi chi k (-(p : GaussianInt))) := by
          have e1 : geoInert (psi chi k (-(p : GaussianInt))) 1 = 0 := by simp [geoInert]
          have e2 : geoInert (psi chi k (-(p : GaussianInt))) 2 = psi chi k (-(p : GaussianInt)) := by
            norm_num [geoInert]
          rw [e1, e2]; ring
        refine ⟨?_, ?_⟩
        · intro ν
          rw [hA (ν+2), hp1, hA (ν+1), hp2, hA ν]
          exact geoInert_rec (psi chi k (-(p : GaussianInt))) ν
        · rw [hp1, hp2, hc, norm_neg]
          exact norm_psi_le_one chi k hb (-(p : GaussianInt))

end

end Work.FIArea5.S16Hecke
