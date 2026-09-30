import Mathlib
import Submission.Work.BW.pow_sum_roots_int
import Submission.Work.BW.mvFrobenius_diff
import Submission.Work.BW.powSum_norm_sub_lt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

open Polynomial

/-- **The power sums of a polynomial of small house are "Frobenius-periodic".**  If every complex
root of the monic `P` has norm at most `H`, and `p` is a prime with
`n·H^{kp} + n·H^k < p` (`n = P.natDegree`), then the `kp`-th and `k`-th power sums coincide. -/
theorem powSum_eq_of_small_house (P : Polynomial ℤ) (hP : P.Monic)
    (p : ℕ) (hp : p.Prime) (k : ℕ) {H : ℝ}
    (hroot : ∀ z : ℂ, (P.map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ ≤ H)
    (hbig : (P.natDegree : ℝ) * H ^ (k * p) + (P.natDegree : ℝ) * H ^ k < (p : ℝ)) :
    ∃ c : ℤ,
      ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ (k * p))).sum = (c : ℂ) ∧
      ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k)).sum = (c : ℂ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- The two power sums are integers (Newton's identities / symmetric functions over `ℤ`).
  obtain ⟨ck, hck⟩ := Work.BW.pow_sum_roots_int P hP k
  obtain ⟨ckp, hckp⟩ := Work.BW.pow_sum_roots_int P hP (k * p)
  set m : Multiset ℂ := (P.map (Int.castRingHom ℂ)).roots with hm
  have hck' : (m.map (fun z => z ^ k)).sum = (ck : ℂ) := by rw [hm]; exact hck
  have hckp' : (m.map (fun z => z ^ (k * p))).sum = (ckp : ℂ) := by rw [hm]; exact hckp
  -- ### Congruence `ckp ≡ ck (mod p)`
  -- Freshman's dream in `MvPolynomial (Fin n) ℤ`: `(∑ Xᵢ^k)^p - ∑ Xᵢ^{kp}` is `p` times a
  -- symmetric integral polynomial `Ψ`.
  have hcong : (p : ℤ) ∣ (ckp - ck) := by
    have hcard : m.card = P.natDegree := by
      rw [hm, Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hP.natDegree_map]
    obtain ⟨Ψ, hΨsym, hΨeq⟩ := Work.BW.mvFrobenius_diff P.natDegree k p hp
    -- Evaluation of symmetric polynomials at the roots, as an algebra homomorphism `ℤ → ℂ`.
    let e : MvPolynomial.symmetricSubalgebra (Fin P.natDegree) ℤ →ₐ[ℤ] ℂ :=
      MvPolynomial.symmetricSubalgebra.aevalMultiset (Fin P.natDegree) ℤ m
    let S : MvPolynomial.symmetricSubalgebra (Fin P.natDegree) ℤ :=
      MvPolynomial.symmetricSubalgebra.sumPolynomial (Fin P.natDegree) (Polynomial.X ^ k)
    let T : MvPolynomial.symmetricSubalgebra (Fin P.natDegree) ℤ :=
      MvPolynomial.symmetricSubalgebra.sumPolynomial (Fin P.natDegree)
        (Polynomial.X ^ (k * p))
    have heS : e S = (ck : ℂ) := by
      have h := MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial
        (σ := Fin P.natDegree) (R := ℤ) (S := ℂ) (m := m) (p := Polynomial.X ^ k)
        (by simpa using hcard)
      simp only [Polynomial.aeval_X, map_pow] at h
      exact h.trans hck'
    have heT : e T = (ckp : ℂ) := by
      have h := MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial
        (σ := Fin P.natDegree) (R := ℤ) (S := ℂ) (m := m) (p := Polynomial.X ^ (k * p))
        (by simpa using hcard)
      simp only [Polynomial.aeval_X, map_pow] at h
      exact h.trans hckp'
    have hcoS : (S : MvPolynomial (Fin P.natDegree) ℤ) = ∑ i, MvPolynomial.X i ^ k := by
      have h := MvPolynomial.symmetricSubalgebra.coe_sumPolynomial
        (σ := Fin P.natDegree) (R := ℤ) (p := Polynomial.X ^ k)
      simpa [S] using h
    have hcoT : (T : MvPolynomial (Fin P.natDegree) ℤ) = ∑ i, MvPolynomial.X i ^ (k * p) := by
      have h := MvPolynomial.symmetricSubalgebra.coe_sumPolynomial
        (σ := Fin P.natDegree) (R := ℤ) (p := Polynomial.X ^ (k * p))
      simpa [T] using h
    have hcoST : ((S ^ p - T : MvPolynomial.symmetricSubalgebra (Fin P.natDegree) ℤ)
        : MvPolynomial (Fin P.natDegree) ℤ) = (p : ℤ) • Ψ := by
      rw [Subalgebra.coe_sub, Subalgebra.coe_pow, hcoS, hcoT, hΨeq]
    have heq : (S ^ p - T : MvPolynomial.symmetricSubalgebra (Fin P.natDegree) ℤ)
        = (p : ℤ) • ⟨Ψ, hΨsym⟩ := by
      apply Subtype.ext
      rw [hcoST]
      simp
    have hev : e (S ^ p - T) = (p : ℤ) • e ⟨Ψ, hΨsym⟩ := by
      rw [heq, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]
    -- `Ψ` takes an *integer* value at the roots: the image of the subalgebra is `ℤ`.
    have hm' : Multiset.map (fun x => P.leadingCoeff • x) (P.aroots ℂ) = m := by
      rw [hm, Polynomial.aroots_def, algebraMap_int_eq, hP.leadingCoeff]
      simp
    have hmem : e ⟨Ψ, hΨsym⟩ ∈ Set.range (algebraMap ℤ ℂ) := by
      have h := MvPolynomial.symmetricSubalgebra.aevalMultiset_map_aroots_mem_range_algebraMap
        (σ := Fin P.natDegree) (R := ℤ) (S := ℤ) (A := ℂ) (q := P) (p := ⟨Ψ, hΨsym⟩)
        (IsAlgClosed.splits _)
      rw [hm'] at h
      exact h
    obtain ⟨r, hr⟩ := hmem
    have hr' : e ⟨Ψ, hΨsym⟩ = (r : ℂ) := by
      rw [← hr, algebraMap_int_eq]
      rfl
    -- Hence `ck^p - ckp = p · r`.
    have hkey : ((ck ^ p - ckp : ℤ) : ℂ) = ((p * r : ℤ) : ℂ) := by
      have h1 : e (S ^ p - T) = ((ck ^ p - ckp : ℤ) : ℂ) := by
        rw [map_sub, map_pow, heS, heT]
        push_cast
        ring
      have h2 : e (S ^ p - T) = ((p * r : ℤ) : ℂ) := by
        rw [hev, hr', zsmul_eq_mul]
        push_cast
        ring
      exact h1.symm.trans h2
    have hdiv : (p : ℤ) ∣ (ck ^ p - ckp) := ⟨r, Int.cast_injective hkey⟩
    -- Fermat: `ck^p ≡ ck (mod p)`; combine.
    have h1z : (ck : ZMod p) ^ p = (ck : ZMod p) := ZMod.pow_card (ck : ZMod p)
    have hcong' : ((ckp : ℤ) : ZMod p) = ((ck : ℤ) : ZMod p) := by
      have h0 : ((ck ^ p - ckp : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
      push_cast at h0
      have h0' : (ck : ZMod p) ^ p = (ckp : ZMod p) := sub_eq_zero.mp h0
      rw [← h0', h1z]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (ckp - ck) p]
    push_cast
    rw [hcong']
    ring
  -- ### The size bound: `|ckp - ck| < p`
  have hbound : ‖(ckp : ℂ) - (ck : ℂ)‖ < (p : ℝ) := by
    have h := Work.BW.powSum_norm_sub_lt P hP p k hroot hbig
    rw [hckp', hck'] at h
    exact h
  have hd0 : ckp - ck = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcong
    have h : ‖((ckp - ck : ℤ) : ℂ)‖ < (p : ℝ) := by
      rw [Int.cast_sub]; exact hbound
    rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs] at h
    have h2 : (ckp - ck).natAbs < p := by exact_mod_cast h
    simpa using h2
  -- ### Conclusion
  refine ⟨ck, ?_, hck'⟩
  rw [show ckp = ck from sub_eq_zero.mp hd0] at hckp'
  exact hckp'

end Work.BW
