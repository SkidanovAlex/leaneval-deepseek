import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic

namespace Work.DSG4b.gonfPerfect

open MvPolynomial

namespace PData

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField R) p]

/-- Each generator `T_b` of the `N`-th stage is integral over `R`: it is a root of the monic
polynomial `X ^ (p ^ N) - b̃`, since `T_b ^ (p ^ N) = b̃` in `AN D N`. -/
lemma isIntegral_gen (D : PData R p) (N : ℕ) (b : D.pB) : IsIntegral R (D.gen N b) := by
  refine ⟨Polynomial.X ^ p ^ N - Polynomial.C (D.lift b),
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero N (Nat.Prime.ne_zero (Fact.out : p.Prime))), ?_⟩
  have h : Polynomial.eval₂ (algebraMap R (D.AN N)) (D.gen N b)
      (Polynomial.X ^ p ^ N - Polynomial.C (D.lift b))
      = (D.gen N b) ^ p ^ N - algebraMap R (D.AN N) (D.lift b) := by
    simp
  rw [h, D.gen_pow_eq, sub_self]

/-- The generators of `AN D N` generate it as an `R`-algebra. -/
lemma adjoin_range_gen_eq_top (D : PData R p) (N : ℕ) :
    Algebra.adjoin R (Set.range (fun b : D.pB => D.gen N b)) = ⊤ := by
  let q : MvPolynomial D.pB R →ₐ[R] D.AN N := Ideal.Quotient.mkₐ R (RFAux.qI (D.fN N))
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R (RFAux.qI (D.fN N))
  have hqX : ∀ b : D.pB, q (MvPolynomial.X b) = D.gen N b := by
    intro b
    show Ideal.Quotient.mk (RFAux.qI (D.fN N)) (MvPolynomial.X b) = D.gen N b
    rw [D.gen_def]
  have himg : q '' Set.range (MvPolynomial.X : D.pB → MvPolynomial D.pB R)
      = Set.range (fun b : D.pB => D.gen N b) := by
    ext y
    constructor
    · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, (hqX b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨MvPolynomial.X b, ⟨b, rfl⟩, hqX b⟩
  have h1 : (⊤ : Subalgebra R (MvPolynomial D.pB R)).map q
      = Algebra.adjoin R (Set.range (fun b : D.pB => D.gen N b)) := by
    rw [← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, himg]
  have h2 : (⊤ : Subalgebra R (MvPolynomial D.pB R)).map q = ⊤ := by
    rw [Algebra.map_top q]
    exact (AlgHom.range_eq_top q).mpr hq
  exact h1 ▸ h2

/-- The `N`-th stage `AN D N` is integral over `R`: it is generated as an `R`-algebra by the
integral elements `D.gen N b`. -/
lemma isIntegral_AN (D : PData R p) (N : ℕ) : Algebra.IsIntegral R (D.AN N) := by
  have hgen := D.adjoin_range_gen_eq_top N
  rw [Algebra.isIntegral_def]
  intro x
  refine (Subalgebra.isIntegral_iff
    (Algebra.adjoin R (Set.range (fun b : D.pB => D.gen N b)))).mp
    (Algebra.IsIntegral.adjoin ?_) x ?_
  · intro y hy
    obtain ⟨b, rfl⟩ := hy
    exact D.isIntegral_gen N b
  · rw [hgen]
    trivial

/-- The structure map `R →+* AN D N` is integral. -/
lemma isIntegral_toAN (D : PData R p) (N : ℕ) : RingHom.IsIntegral (D.toAN N) := by
  have h : D.toAN N = algebraMap R (D.AN N) :=
    RingHom.ext (fun r => D.toAN_eq_algebraMap N r)
  rw [h]
  exact Algebra.isIntegral_def.mp (D.isIntegral_AN N)

end PData

end Work.DSG4b.gonfPerfect

namespace Work.DSG4b.gonfPerfect.integral

open Work.DSG4b.gonfPerfect

theorem integral_S (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) :
    D.phi.IsIntegral := by
  intro x
  obtain ⟨N, a, rfl⟩ := Ring.DirectLimit.exists_of x
  have hcomp : (D.incl N).comp (D.toAN N) = D.phi :=
    RingHom.ext (fun r => D.incl_toAN N r)
  rw [← hcomp]
  exact RingHom.IsIntegralElem.map (D.isIntegral_toAN N a) (D.incl N)

end Work.DSG4b.gonfPerfect.integral
