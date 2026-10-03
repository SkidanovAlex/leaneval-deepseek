import Mathlib.RingTheory.DedekindDomain.Basic
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime
import Submission.Commons.NumberTheory.GaussianInt.associated_of_dvd_of_normNatAbs_eq
import Submission.Commons.Algebra.Ideal.mul_sup_span_eq_of_isCoprime

set_option autoImplicit false

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

noncomputable section

/-! ## Norm divisibility for Gaussian integers -/

/-- If `a ∣ b` in `ℤ[i]` then `‖a‖ ∣ ‖b‖` for the natural absolute norms. -/
lemma normNatAbs_dvd_normNatAbs_of_dvd {a b : GaussianInt} (h : a ∣ b) :
    a.norm.natAbs ∣ b.norm.natAbs := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.norm.natAbs, by rw [Zsqrtd.norm_mul, Int.natAbs_mul]⟩

/-- If `a ∣ (m : ℤ[i])` then `‖a‖ ∣ m ^ 2`. -/
lemma normNatAbs_dvd_sq_of_dvd_natCast {a : GaussianInt} {m : ℕ} (h : a ∣ (m : GaussianInt)) :
    a.norm.natAbs ∣ m ^ 2 := by
  have h2 : a.norm.natAbs ∣ m * m := by
    have h3 := normNatAbs_dvd_normNatAbs_of_dvd h
    rwa [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h3
  simpa [pow_two] using h2

/-! ## Splitting off the part of `z` supported on the primes of `m` -/

/-- The generator of the ideal `(z) + (m)`: the part of `z` carried by the prime
divisors of `m`. -/
def gPart (m : ℕ) (z : GaussianInt) : GaussianInt :=
  Submodule.IsPrincipal.generator (Ideal.span {z} ⊔ Ideal.span {(m : GaussianInt)})

lemma span_gPart (m : ℕ) (z : GaussianInt) :
    Ideal.span {gPart m z} = Ideal.span {z} ⊔ Ideal.span {(m : GaussianInt)} :=
  Submodule.IsPrincipal.span_singleton_generator _

lemma gPart_dvd_left (m : ℕ) (z : GaussianInt) : gPart m z ∣ z :=
  Ideal.mem_span_singleton.mp
    (show z ∈ Ideal.span {gPart m z} from by
      rw [span_gPart]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr dvd_rfl))

lemma gPart_dvd_natCast (m : ℕ) (z : GaussianInt) : gPart m z ∣ (m : GaussianInt) :=
  Ideal.mem_span_singleton.mp
    (show (m : GaussianInt) ∈ Ideal.span {gPart m z} from by
      rw [span_gPart]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr dvd_rfl))

/-- `gPart m ·` only depends on the associate class. -/
lemma gPart_eq_of_associated {m : ℕ} {z z' : GaussianInt} (h : Associated z z') :
    Associated (gPart m z) (gPart m z') := by
  have hspan : Ideal.span {z} = Ideal.span {z'} := Ideal.span_singleton_eq_span_singleton.mpr h
  rw [← Ideal.span_singleton_eq_span_singleton]
  rw [span_gPart, span_gPart, hspan]

/-- `‖gPart m z‖` divides `m`, when `‖z‖ = m * n` with `m` and `n` coprime. -/
lemma normNatAbs_gPart_dvd {z : GaussianInt} {m n : ℕ} (hcop : Nat.Coprime m n)
    (hz : z.norm.natAbs = m * n) : (gPart m z).norm.natAbs ∣ m := by
  have h1 : (gPart m z).norm.natAbs ∣ m ^ 2 :=
    normNatAbs_dvd_sq_of_dvd_natCast (gPart_dvd_natCast m z)
  have h2 : (gPart m z).norm.natAbs ∣ m * n := by
    have h := normNatAbs_dvd_normNatAbs_of_dvd (gPart_dvd_left m z)
    rwa [hz] at h
  have h3 : (gPart m z).norm.natAbs ∣ (m ^ 2).gcd (m * n) := Nat.dvd_gcd h1 h2
  have h4 : (m ^ 2).gcd (m * n) = m := by
    rw [pow_two, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  rwa [h4] at h3

/-- **Splitting a Gaussian integer along coprime factors of its norm.**
If `‖z‖ = m * n` with `m`, `n` coprime and `≥ 1`, then the two parts
`gPart m z`, `gPart n z` have norms `m`, `n` and multiply back to `z` up to units. -/
lemma norm_gPart_eq_and_associated {z : GaussianInt} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : Nat.Coprime m n) (hz : z.norm.natAbs = m * n) :
    (gPart m z).norm.natAbs = m ∧ (gPart n z).norm.natAbs = n ∧
      Associated (gPart m z * gPart n z) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    omega
  have hdvd_mn : z ∣ (m : GaussianInt) * (n : GaussianInt) := by
    have h : ((z.norm.natAbs : ℕ) : GaussianInt) = z * star z := norm_natAbs_cast_eq z
    rw [hz] at h
    exact ⟨star z, by rw [← h, Nat.cast_mul]⟩
  have hcop' : IsCoprime (m : GaussianInt) (n : GaussianInt) := hcop.cast
  have hspan_prod : Ideal.span {gPart m z} * Ideal.span {gPart n z} = Ideal.span {z} := by
    rw [span_gPart, span_gPart]
    exact Commons.Algebra.Ideal.mul_sup_span_eq_of_isCoprime hcop' hdvd_mn
  have hassoc : Associated (gPart m z * gPart n z) z := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← Ideal.span_singleton_mul_span_singleton, hspan_prod]
  have hna : (gPart m z).norm.natAbs ∣ m := normNatAbs_gPart_dvd hcop hz
  have hnb : (gPart n z).norm.natAbs ∣ n :=
    normNatAbs_gPart_dvd (z := z) (m := n) (n := m) hcop.symm (by rw [hz, mul_comm])
  have hprod : (gPart m z).norm.natAbs * (gPart n z).norm.natAbs = m * n := by
    have h := Zsqrtd.norm_eq_of_associated (d := -1) (by norm_num) hassoc
    have h2 : ((gPart m z * gPart n z).norm).natAbs = z.norm.natAbs := by rw [h]
    rw [hz, Zsqrtd.norm_mul, Int.natAbs_mul] at h2
    exact h2
  have hNA : (gPart m z).norm.natAbs ≠ 0 := by
    intro h0
    have hz0' : gPart m z = 0 := GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp h0)
    obtain ⟨c, hc⟩ := gPart_dvd_left m z
    rw [hz0', zero_mul] at hc
    exact hz0 hc
  have hNB : (gPart n z).norm.natAbs ≠ 0 := by
    intro h0
    have hz0' : gPart n z = 0 := GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp h0)
    obtain ⟨c, hc⟩ := gPart_dvd_left n z
    rw [hz0', zero_mul] at hc
    exact hz0 hc
  generalize hNAd : (gPart m z).norm.natAbs = NA at hprod hna hNA
  generalize hNBd : (gPart n z).norm.natAbs = NB at hprod hnb hNB
  obtain ⟨u, hu⟩ := hna
  obtain ⟨v, hv⟩ := hnb
  have h3 : m * n = NA * NB * (u * v) := by rw [hu, hv]; ring
  have h2 : NA * NB = NA * NB * (u * v) := hprod.trans h3
  have huv : u * v = 1 :=
    Nat.mul_left_cancel (Nat.pos_of_ne_zero (mul_ne_zero hNA hNB))
      (by rw [mul_one]; exact h2.symm)
  have hu1 : u = 1 := Nat.dvd_one.mp ⟨v, huv.symm⟩
  have hv1 : v = 1 := by rw [hu1, one_mul] at huv; exact huv
  have hNAeq : NA = m := by rw [hu, hu1, mul_one]
  have hNBeq : NB = n := by rw [hv, hv1, mul_one]
  refine ⟨?_, ?_, hassoc⟩
  · exact hNAeq
  · exact hNBeq

/-- The part of `a * b` supported on the primes of `m` is `a` itself, when
`‖a‖ = m`, `‖b‖ = n` and `m`, `n` are coprime. -/
lemma gPart_mul_eq {a b : GaussianInt} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : Nat.Coprime m n) (ha : a.norm.natAbs = m) (hb : b.norm.natAbs = n) :
    Associated (gPart m (a * b)) a ∧ Associated (gPart n (a * b)) b := by
  have hnorm : (a * b).norm.natAbs = m * n := by
    rw [Zsqrtd.norm_mul, Int.natAbs_mul, ha, hb]
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; omega
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb; simp at hb; omega
  obtain ⟨hA, hB, -⟩ := norm_gPart_eq_and_associated hm hn hcop hnorm
  have ha'0 : gPart m (a * b) ≠ 0 := by
    intro h; rw [h] at hA; simp at hA; omega
  have hb'0 : gPart n (a * b) ≠ 0 := by
    intro h; rw [h] at hB; simp at hB; omega
  have ha_m : a ∣ (m : GaussianInt) := by
    have h := norm_natAbs_cast_eq a
    rw [ha] at h
    exact ⟨star a, h⟩
  have hb_n : b ∣ (n : GaussianInt) := by
    have h := norm_natAbs_cast_eq b
    rw [hb] at h
    exact ⟨star b, h⟩
  constructor
  · refine (associated_of_dvd_of_normNatAbs_eq ?_ ?_ ha'0).symm
    · rw [← Ideal.span_singleton_le_span_singleton]
      rw [span_gPart]
      apply sup_le
      · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr ⟨b, rfl⟩)
      · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr ha_m)
    · rw [ha, hA]
  · refine (associated_of_dvd_of_normNatAbs_eq ?_ ?_ hb'0).symm
    · rw [← Ideal.span_singleton_le_span_singleton]
      rw [span_gPart]
      apply sup_le
      · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr ⟨a, by rw [mul_comm]⟩)
      · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hb_n)
    · rw [hb, hB]

/-! ## The bijection between classes of norm `m * n` and pairs of classes -/

/-- The set of associate classes of Gaussian integers with norm `N`. -/
private def X (N : ℕ) : Set (Associates GaussianInt) :=
  Associates.mk '' {z : GaussianInt | z.norm.natAbs = N}

/-- Send the class of `z` (of norm `m * n`) to the pair of classes of the parts of `z`
supported on the prime divisors of `m` and of `n`. This is well defined on associate
classes because `gPart` is. -/
private noncomputable def phi (m n : ℕ) :
    Associates GaussianInt → Associates GaussianInt × Associates GaussianInt :=
  Quotient.lift (fun z => (Associates.mk (gPart m z), Associates.mk (gPart n z)))
    (fun z z' h => by
      have h1 : Associates.mk (gPart m z) = Associates.mk (gPart m z') :=
        Associates.mk_eq_mk_iff_associated.mpr (gPart_eq_of_associated h)
      have h2 : Associates.mk (gPart n z) = Associates.mk (gPart n z') :=
        Associates.mk_eq_mk_iff_associated.mpr (gPart_eq_of_associated h)
      rw [h1, h2])

/-- Multiplication of associate classes, as a map on pairs. -/
private def psi (p : Associates GaussianInt × Associates GaussianInt) : Associates GaussianInt :=
  p.1 * p.2

private lemma phi_mk (m n : ℕ) (z : GaussianInt) :
    phi m n (Associates.mk z) = (Associates.mk (gPart m z), Associates.mk (gPart n z)) :=
  rfl

private lemma psi_phi (m n : ℕ) {z : GaussianInt} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : Nat.Coprime m n) (hz : z.norm.natAbs = m * n) :
    psi (phi m n (Associates.mk z)) = Associates.mk z := by
  have h := (norm_gPart_eq_and_associated hm hn hcop hz).2.2
  simp only [psi, phi_mk, Associates.mk_mul_mk]
  exact Associates.mk_eq_mk_iff_associated.mpr h

private lemma phi_psi (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (p : Associates GaussianInt × Associates GaussianInt) (hp : p ∈ X m ×ˢ X n) :
    phi m n (psi p) = p := by
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  obtain ⟨a, ha, hpa⟩ := hp1
  obtain ⟨b, hb, hpb⟩ := hp2
  have ha' : a.norm.natAbs = m := ha
  have hb' : b.norm.natAbs = n := hb
  have hp_eq : p = (Associates.mk a, Associates.mk b) := Prod.ext hpa.symm hpb.symm
  rw [hp_eq]
  obtain ⟨h1, h2⟩ := gPart_mul_eq hm hn hcop ha' hb'
  have e1 : Associates.mk (gPart m (a * b)) = Associates.mk a :=
    Associates.mk_eq_mk_iff_associated.mpr h1
  have e2 : Associates.mk (gPart n (a * b)) = Associates.mk b :=
    Associates.mk_eq_mk_iff_associated.mpr h2
  simp only [psi, phi_mk, Associates.mk_mul_mk, e1, e2]

/-- **Multiplicativity of the number of associate classes of Gaussian integers of a
given norm**, for coprime norms. -/
theorem ncard_assoc_norm_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n) :
    (Associates.mk '' {z : GaussianInt | z.norm.natAbs = m * n}).ncard
      = (Associates.mk '' {z : GaussianInt | z.norm.natAbs = m}).ncard
        * (Associates.mk '' {z : GaussianInt | z.norm.natAbs = n}).ncard := by
  show (X (m * n)).ncard = (X m).ncard * (X n).ncard
  have hbij : (X (m * n)).ncard = (X m ×ˢ X n).ncard := by
    refine Set.ncard_congr (fun κ _ => phi m n κ) ?_ ?_ ?_
    · intro κ hκ
      obtain ⟨z, hz, rfl⟩ := hκ
      rw [phi_mk]
      obtain ⟨h1, h2, -⟩ := norm_gPart_eq_and_associated hm hn hcop hz
      exact Set.mem_prod.mpr ⟨⟨gPart m z, h1, rfl⟩, ⟨gPart n z, h2, rfl⟩⟩
    · intro κ κ' hκ hκ' heq
      obtain ⟨z, hz, rfl⟩ := hκ
      obtain ⟨z', hz', rfl⟩ := hκ'
      have h1 := psi_phi m n hm hn hcop hz
      have h2 := psi_phi m n hm hn hcop hz'
      have heq' : phi m n (Associates.mk z) = phi m n (Associates.mk z') := heq
      have hc := congrArg psi heq'
      rw [h1, h2] at hc
      exact hc
    · intro p hp
      have hpsi : psi p ∈ X (m * n) := by
        obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
        obtain ⟨a, ha, hpa⟩ := hp1
        obtain ⟨b, hb, hpb⟩ := hp2
        have ha' : a.norm.natAbs = m := ha
        have hb' : b.norm.natAbs = n := hb
        have hp_eq : p = (Associates.mk a, Associates.mk b) := Prod.ext hpa.symm hpb.symm
        rw [hp_eq]
        change Associates.mk a * Associates.mk b ∈ X (m * n)
        refine ⟨a * b, ?_, ?_⟩
        · show (a * b).norm.natAbs = m * n
          rw [Zsqrtd.norm_mul, Int.natAbs_mul, ha', hb']
        · rw [Associates.mk_mul_mk]
      exact ⟨psi p, hpsi, phi_psi m n hm hn hcop p hp⟩
  rw [hbij, Set.ncard_prod]

end

end Commons.NumberTheory.GaussianInt