import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.ureg_isSMulRegular

/-!
# `π ^ e X - q` is regular modulo `I`

Let `R` be a commutative ring and `I ⊆ R` an ideal.  Suppose `f ∈ R[X]` becomes a
nonzerodivisor of `(R / I)[X]`; then `f` is regular modulo the ideal
`I · R[X] ⊆ R[X]`, i.e. `f · c ∈ I · R[X]` forces `c ∈ I · R[X]`.

This is the "regular modulo an ideal" form of `ureg_isSMulRegular` and is the
workhorse of node `N2b`.
-/

namespace Work.DSM2p

/-- If `f` is a nonzerodivisor of `(R / I)[X]`, then `f` is regular modulo the
extension `I · R[X]` of `I` to `R[X]`. -/
lemma isSMulRegular_map_quot {R : Type*} [CommRing R] (I : Ideal R) (f : Polynomial R)
    (h : IsSMulRegular (Polynomial (R ⧸ I)) (Polynomial.map (Ideal.Quotient.mk I) f)) :
    ∀ c : Polynomial R,
      f * c ∈ Ideal.map Polynomial.C I → c ∈ Ideal.map Polynomial.C I := by
  intro c hc
  have hker : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) =
      Ideal.map Polynomial.C I := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  have hc' : Polynomial.mapRingHom (Ideal.Quotient.mk I) (f * c) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact hc
  rw [Polynomial.coe_mapRingHom, Polynomial.map_mul] at hc'
  have hc0 : Polynomial.map (Ideal.Quotient.mk I) c = 0 := by
    refine h ?_
    change (Polynomial.map (Ideal.Quotient.mk I) f) • (Polynomial.map (Ideal.Quotient.mk I) c) =
      (Polynomial.map (Ideal.Quotient.mk I) f) • (0 : Polynomial (R ⧸ I))
    rw [smul_eq_mul, smul_eq_mul, mul_zero]
    exact hc'
  rw [← hker, RingHom.mem_ker]
  simpa only [Polynomial.coe_mapRingHom] using hc0

/-- `I · R[X]` for `R[X]` over the base is the extension of `I · R`. -/
lemma map_algebraMap_polynomial_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) :
    I.map (algebraMap R (Polynomial S)) = Ideal.map Polynomial.C (I.map (algebraMap R S)) := by
  rw [IsScalarTower.algebraMap_eq R S (Polynomial S), ← Ideal.map_map,
    show (algebraMap S (Polynomial S)) = Polynomial.C from
      RingHom.ext fun r => (Polynomial.C_eq_algebraMap r).symm]

theorem N2b_regular_mod_ideals (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (π : A) (e : ℕ) (q : Lam1 A p) (n : ℕ) (g : Polynomial A)
    (hq : q - Polynomial.aeval (T1 A p n) g ∈ Ideal.span {algebraMap A (Lam1 A p) π})
    (hmr : ∀ (I : Ideal A), IsSMulRegular (Lam1 A p ⧸ I.map (algebraMap A (Lam1 A p)))
      (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) (Polynomial.aeval (T1 A p n) g)))
    (I : Ideal A) (c : Polynomial (Lam1 A p))
    (hc : (Polynomial.C (algebraMap A (Lam1 A p) π ^ e) * Polynomial.X - Polynomial.C q) * c ∈
      I.map (algebraMap A (Polynomial (Lam1 A p)))) :
    c ∈ I.map (algebraMap A (Polynomial (Lam1 A p))) := by
  have hJ := map_algebraMap_polynomial_eq (S := Lam1 A p) I
  rw [hJ] at hc ⊢
  refine isSMulRegular_map_quot (I.map (algebraMap A (Lam1 A p)))
    (Polynomial.C (algebraMap A (Lam1 A p) π ^ e) * Polynomial.X - Polynomial.C q) ?_ c hc
  have hq' : Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) q -
      Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) (Polynomial.aeval (T1 A p n) g) ∈
      Ideal.span {Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) (algebraMap A (Lam1 A p) π)} := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    refine Ideal.mem_span_singleton.mpr
      ⟨Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) r, ?_⟩
    have h1 : Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) q -
        Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) (Polynomial.aeval (T1 A p n) g) =
        Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p)))
          (q - Polynomial.aeval (T1 A p n) g) :=
      (map_sub (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p)))) q
        (Polynomial.aeval (T1 A p n) g)).symm
    rw [h1, hr]
    exact map_mul (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))))
      (algebraMap A (Lam1 A p) π) r
  have hmap : Polynomial.map (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))))
      (Polynomial.C (algebraMap A (Lam1 A p) π ^ e) * Polynomial.X - Polynomial.C q) =
      Polynomial.C ((Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p)))
          (algebraMap A (Lam1 A p) π)) ^ e) * Polynomial.X -
        Polynomial.C (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) q) := by
    have hp : (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))))
        (algebraMap A (Lam1 A p) π ^ e) =
        (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))))
          (algebraMap A (Lam1 A p) π) ^ e :=
      map_pow (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))))
        (algebraMap A (Lam1 A p) π) e
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, hp]
  rw [hmap]
  exact ureg_isSMulRegular _ _ _ e hq' (hmr I)

end Work.DSM2p
