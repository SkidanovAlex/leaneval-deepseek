/-
  Area E1 (WilE1): the lifted system of a polynomial system is zero-dimensional.

  For `F : Fin k → ℂ[Fin k]` the *lifted* system is `F` together with `1 - Y · det J(F)` in
  `k+1` variables (`Y` being the last variable).  We show that its quotient is a
  finite-dimensional `ℂ`-algebra.

  Route: `ℂ[Fin (k+1)]` is a finitely generated `ℂ`-algebra, so by
  `Module.finite_iff_krullDimLE_zero` it suffices that the quotient has Krull dimension `0`,
  i.e. that every prime above `sysIdeal (lifted F)` is maximal
  (`Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`).

  For such a prime `J`, `J` cannot contain `rename castSucc (det J(F))` (else `1 ∈ J`), so the
  prime `𝔭 = J ∩ ℂ[Fin k]` satisfies the Jacobian criterion
  (`isMaximal_of_isPrime_of_sysIdeal_le_of_det_notMem`): a prime containing a `k`-tuple of
  polynomials and not containing its Jacobian determinant is maximal.  That criterion is the
  classical "nondegenerate point" argument:

  * it suffices to work at a maximal ideal, i.e. at a point `x` (Nullstellensatz).  The
    second order Taylor expansion (`TaylorTwo`) expresses each `F i` modulo `𝔪 ^ 2` by its
    linear part at `x`; since the Jacobian matrix is invertible at `x`, the coordinate
    functions `X j - x j` themselves lie in `(F) + 𝔪 ^ 2` (`SpanLeSysIdealSupSq`);
  * the determinant trick (`DetTrick`) then multiplies every element of `𝔪` into `(F)` by an
    element outside `𝔪`, which forces `𝔭 = 𝔪` (and hence maximality) because `ℂ[X]/𝔭` is a
    domain.
-/
import Mathlib
import Submission.Work.WilE1.Setup
import Submission.Work.WilE1.VanishSpan
import Submission.Work.WilE1.TaylorTwo
import Submission.Work.WilE1.DetTrick
import Submission.Work.WilE1.SpanLeSysIdealSupSq

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE1

/-! ## The inclusion `ℂ[Fin k] → ℂ[Fin (k+1)]` -/

/-- The inclusion of polynomial rings `ℂ[Fin k] → ℂ[Fin (k+1)]` sending `X i` to `X (castSucc i)`. -/
def liftRingHom (k : ℕ) : MvPolynomial (Fin k) ℂ →+* MvPolynomial (Fin (k+1)) ℂ :=
  (MvPolynomial.rename (R := ℂ) (Fin.castSucc : Fin k → Fin (k+1))).toRingHom

@[simp] theorem liftRingHom_X (k : ℕ) (i : Fin k) :
    liftRingHom k (MvPolynomial.X i) = MvPolynomial.X (Fin.castSucc i) := by
  simp [liftRingHom]

@[simp] theorem liftRingHom_C (k : ℕ) (c : ℂ) :
    liftRingHom k (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [liftRingHom]

/-! ## Step 1: the abstract prime lemma. -/

/-- If `p ⊆ M` is a prime ideal of a commutative ring and every element of `M` can be
multiplied into `p` by an element outside `M`, then `p = M`. -/
theorem prime_eq_of_forall_exists_notMem_mul_mem {R : Type*} [CommRing R]
    {p M : Ideal R} (hp : p.IsPrime) (hpM : p ≤ M)
    (h : ∀ y ∈ M, ∃ s : R, s ∉ M ∧ s * y ∈ p) : p = M := by
  haveI : p.IsPrime := hp
  refine le_antisymm hpM ?_
  intro y hy
  obtain ⟨s, hs, hsy⟩ := h y hy
  by_contra hy'
  have hz : (Ideal.Quotient.mk p) s * (Ideal.Quotient.mk p) y = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hsy
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact hs (hpM (Ideal.Quotient.eq_zero_iff_mem.mp h1))
  · exact hy' (Ideal.Quotient.eq_zero_iff_mem.mp h2)

/-! ## Step 2: the Jacobian criterion in `k` variables. -/

/-- **Jacobian criterion.**  A prime ideal `𝔭` of `ℂ[X₀,…,X_{k-1}]` containing a `k`-tuple
`F` of polynomials and not containing `det J(F)` is maximal: the common zero locus of `F` is
nondegenerate at the corresponding point. -/
theorem isMaximal_of_isPrime_of_sysIdeal_le_of_det_notMem {k : ℕ}
    (F : Fin k → MvPolynomial (Fin k) ℂ) {𝔭 : Ideal (MvPolynomial (Fin k) ℂ)}
    (h𝔭 : 𝔭.IsPrime) (hI : sysIdeal F ≤ 𝔭) (hdet : (jac F).det ∉ 𝔭) : 𝔭.IsMaximal := by
  have hrad : 𝔭.radical = 𝔭 := h𝔭.isRadical.radical
  have hdet' : (jac F).det ∉ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ 𝔭) := by
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hrad]
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hdet'
  push Not at hdet'
  obtain ⟨x, hx, hxdet⟩ := hdet'
  have hMmax : (MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ))).IsMaximal := inferInstance
  have h𝔭M : 𝔭 ≤ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ)) := by
    intro q hq
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hx q hq
  have hIle : sysIdeal F ≤ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ)) :=
    le_trans hI h𝔭M
  have hsq : MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ)) ≤
      sysIdeal F ⊔ (MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ)))^2 := by
    rw [VanishSpan x]
    refine SpanLeSysIdealSupSq F x ((jac F).map (MvPolynomial.aeval x)) ?_ ?_
    · have h1 : ((jac F).map (MvPolynomial.aeval x)).det = MvPolynomial.aeval x (jac F).det := by
        rw [AlgHom.map_det (MvPolynomial.aeval x) (jac F), AlgHom.mapMatrix_apply]
      rw [h1]; exact hxdet
    · intro i
      have h0 : MvPolynomial.aeval x (F i) = 0 := hx (F i) (hI (Ideal.subset_span ⟨i, rfl⟩))
      have hty := TaylorTwo x (F i)
      rw [h0, map_zero, sub_zero] at hty
      have hsum : (∑ j, (MvPolynomial.X j - MvPolynomial.C (x j)) *
              MvPolynomial.C (MvPolynomial.aeval x (MvPolynomial.pderiv j (F i))))
            = ∑ j, MvPolynomial.C ((jac F).map (MvPolynomial.aeval x) i j) *
              (MvPolynomial.X j - MvPolynomial.C (x j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
        simp [jac, Matrix.map_apply]
      rw [hsum] at hty
      exact hty
  have hloc := DetTrick hMmax hIle hsq
  have hEq : 𝔭 = MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin k → ℂ)) :=
    prime_eq_of_forall_exists_notMem_mul_mem h𝔭 h𝔭M (fun y hy => by
      obtain ⟨s, hs, hsy⟩ := hloc y hy
      exact ⟨s, hs, hI hsy⟩)
  rw [hEq]; exact hMmax

/-! ## Step 3: primes of the lifted quotient are maximal. -/

/-- Every prime ideal containing the lifted system of `F` is maximal. -/
theorem isMaximal_of_isPrime_of_sysIdeal_lifted_le {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    {J : Ideal (MvPolynomial (Fin (k+1)) ℂ)} (hJ : J.IsPrime)
    (hI : sysIdeal (lifted F) ≤ J) : J.IsMaximal := by
  have hliftlast : lifted F (Fin.last k) =
      1 - MvPolynomial.X (Fin.last k) * liftRingHom k (jac F).det := by
    simp [lifted, liftRingHom]
  have hgen : 1 - MvPolynomial.X (Fin.last k) * liftRingHom k (jac F).det ∈ J := by
    rw [← hliftlast]
    exact hI (Ideal.subset_span ⟨Fin.last k, rfl⟩)
  have hJt : liftRingHom k (jac F).det ∉ J := by
    intro hmem
    have h2 : MvPolynomial.X (Fin.last k) * liftRingHom k (jac F).det ∈ J :=
      J.mul_mem_left _ hmem
    have h1 : (1 : MvPolynomial (Fin (k+1)) ℂ) ∈ J := by
      have := J.add_mem hgen h2
      simpa using this
    exact hJ.ne_top (Ideal.eq_top_iff_one J |>.mpr h1)
  set 𝔭 : Ideal (MvPolynomial (Fin k) ℂ) := Ideal.comap (liftRingHom k) J with h𝔭
  haveI : J.IsPrime := hJ
  have h𝔭prime : 𝔭.IsPrime := by rw [h𝔭]; exact Ideal.IsPrime.comap (liftRingHom k)
  have hI𝔭 : sysIdeal F ≤ 𝔭 := by
    rw [h𝔭, sysIdeal, Ideal.span_le]
    rintro q ⟨i, rfl⟩
    refine Ideal.mem_comap.mpr ?_
    have hli : lifted F (Fin.castSucc i) = liftRingHom k (F i) := by
      simp [lifted, liftRingHom]
    rw [← hli]
    exact hI (Ideal.subset_span ⟨Fin.castSucc i, rfl⟩)
  have hdet𝔭 : (jac F).det ∉ 𝔭 := by
    rw [h𝔭]
    intro h
    exact hJt (Ideal.mem_comap.mp h)
  have h𝔭max : 𝔭.IsMaximal :=
    isMaximal_of_isPrime_of_sysIdeal_le_of_det_notMem F h𝔭prime hI𝔭 hdet𝔭
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ h𝔭max
  have hā : MvPolynomial.aeval a (jac F).det ≠ 0 := by
    intro h0
    apply hdet𝔭
    rw [ha, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact h0
  set pt : Fin (k+1) → ℂ := Fin.lastCases ((MvPolynomial.aeval a (jac F).det))⁻¹ (fun j => a j)
    with hpt
  have hpt_cast (j : Fin k) : pt (Fin.castSucc j) = a j := by simp [hpt]
  have hcast : ∀ j : Fin k,
      (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.C (pt (Fin.castSucc j)) :
        MvPolynomial (Fin (k+1)) ℂ) ∈ J := by
    intro j
    have hmem : (MvPolynomial.X j - MvPolynomial.C (a j) : MvPolynomial (Fin k) ℂ) ∈ 𝔭 := by
      rw [ha, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [h𝔭] at hmem
    have h2 : liftRingHom k (MvPolynomial.X j - MvPolynomial.C (a j)) ∈ J :=
      Ideal.mem_comap.mp hmem
    rw [hpt_cast j]
    simpa using h2
  have hlast : (MvPolynomial.X (Fin.last k) - MvPolynomial.C (pt (Fin.last k)) :
      MvPolynomial (Fin (k+1)) ℂ) ∈ J := by
    have hdt : liftRingHom k (jac F).det - MvPolynomial.C (MvPolynomial.aeval a (jac F).det) ∈ J := by
      have hmem : ((jac F).det - MvPolynomial.C (MvPolynomial.aeval a (jac F).det)) ∈ 𝔭 := by
        rw [ha, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp
      rw [h𝔭] at hmem
      simpa using Ideal.mem_comap.mp hmem
    have hptlast : pt (Fin.last k) = (MvPolynomial.aeval a (jac F).det)⁻¹ := by simp [hpt]
    rw [hptlast]
    have hkey : MvPolynomial.C (MvPolynomial.aeval a (jac F).det) *
        (MvPolynomial.X (Fin.last k) -
          MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹)) ∈ J := by
      have hCm : (MvPolynomial.C (MvPolynomial.aeval a (jac F).det) *
          MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹) :
            MvPolynomial (Fin (k+1)) ℂ) = 1 := by
        rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hā, MvPolynomial.C_1]
      have hid : MvPolynomial.C (MvPolynomial.aeval a (jac F).det) *
          (MvPolynomial.X (Fin.last k) -
            MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹)) =
          -(1 - MvPolynomial.X (Fin.last k) * liftRingHom k (jac F).det) -
            MvPolynomial.X (Fin.last k) *
              (liftRingHom k (jac F).det - MvPolynomial.C (MvPolynomial.aeval a (jac F).det)) := by
        rw [mul_sub, hCm]
        ring
      rw [hid]
      exact J.sub_mem (J.neg_mem hgen) (J.mul_mem_left _ hdt)
    have hid2 : MvPolynomial.X (Fin.last k) - MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹) =
        MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹) *
          (MvPolynomial.C (MvPolynomial.aeval a (jac F).det) *
            (MvPolynomial.X (Fin.last k) -
              MvPolynomial.C ((MvPolynomial.aeval a (jac F).det)⁻¹))) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hā, map_one, one_mul]
    rw [hid2]
    exact J.mul_mem_left _ hkey
  have hspanle : Ideal.span (Set.range fun l : Fin (k+1) =>
      (MvPolynomial.X l - MvPolynomial.C (pt l) : MvPolynomial (Fin (k+1)) ℂ)) ≤ J := by
    rw [Ideal.span_le]
    rintro q ⟨l, rfl⟩
    exact Fin.lastCases hlast hcast l
  have hmaxspan : (Ideal.span (Set.range fun l : Fin (k+1) =>
      (MvPolynomial.X l - MvPolynomial.C (pt l) : MvPolynomial (Fin (k+1)) ℂ))).IsMaximal := by
    rw [← VanishSpan pt]
    exact inferInstance
  have hspanJ : (Ideal.span (Set.range fun l : Fin (k+1) =>
      (MvPolynomial.X l - MvPolynomial.C (pt l) : MvPolynomial (Fin (k+1)) ℂ))) = J :=
    hmaxspan.eq_of_le hJ.ne_top hspanle
  rw [← hspanJ]
  exact hmaxspan

/-! ## Step 4: the target. -/

theorem LiftedFinite (k : ℕ) (F : Fin k → MvPolynomial (Fin k) ℂ) :
    Module.Finite ℂ (MvPolynomial (Fin (k+1)) ℂ ⧸ Work.WilE1.sysIdeal (Work.WilE1.lifted F)) := by
  rw [Module.finite_iff_krullDimLE_zero]
  rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
  intro J hJ
  exact isMaximal_of_isPrime_of_sysIdeal_lifted_le F
    (Ideal.IsMinimalPrime.isPrime hJ) (Ideal.IsMinimalPrime.le hJ)

end Work.WilE1
