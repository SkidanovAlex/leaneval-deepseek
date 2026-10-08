import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for the integral lifting of the `C`-averaged idempotent

Two self-contained algebraic lemmas used in `Submission/Work/NormalComplement/AppVII/RhoCTildeE.lean`:

* `coeff_mapRingHom`: coefficients of `MonoidAlgebra.mapRingHom M φ x` are the images of the
  coefficients of `x` under `φ`;
* `eq_zero_of_mul_eq_zero_of_mapRingHom_eq_single_one`: if `z ∈ R[A]` reduces to a non-zero
  scalar in `S[A]` (`R`, `S` domains) then right multiplication by `z` is injective — proved
  with the adjugate of the matrix of right multiplication by `z`;
* `sum_single_mul_sum_single`: `ρ_C * ρ_C = |C| • ρ_C` for `ρ_C = ∑_{c ∈ C} single c 1`.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

/-- Coefficient of `MonoidAlgebra.mapRingHom M φ x` at `m`: applying a ring homomorphism to the
coefficient ring commutes with taking coefficients. -/
theorem coeff_mapRingHom {R S M : Type*} [Semiring R] [Semiring S] [Monoid M]
    (φ : R →+* S) (x : MonoidAlgebra R M) (m : M) :
    (MonoidAlgebra.mapRingHom M φ x).coeff m = φ (x.coeff m) := by
  change (x.coeff.mapRange (φ : R → S) φ.map_zero) m = φ (x.coeff m)
  rw [Finsupp.mapRange_apply]

/-- **The adjugate / regular-representation step.**  Let `R`, `S` be domains, `φ : R →+* S`,
`c : R` with `φ c ≠ 0`, and `z ∈ R[A]` whose image in `S[A]` is the scalar
`MonoidAlgebra.single 1 (φ c)` (i.e. `φ c • 1`).  Then right multiplication by `z` on `R[A]` is
injective.

Proof: let `M` be the matrix of right multiplication by `z` in the basis `(single a 1)` of `R[A]`
as a free `R`-module, so that `M *ᵥ v = 0` for the coefficient vector `v` of any `f` with
`f * z = 0`.  The image of `M` under `φ` is the matrix of right multiplication by the scalar
`φ c • 1`, i.e. the scalar matrix `(φ c) • 1`; hence `φ M.det = (φ c) ^ |A| ≠ 0` and
`M.det ≠ 0`.  The adjugate identity `M.adjugate * M = M.det • 1` gives `M.det • v = 0`, i.e.
`M.det • f = 0` coefficientwise, and since `R` is a domain and `M.det ≠ 0` this forces `f = 0`. -/
theorem eq_zero_of_mul_eq_zero_of_mapRingHom_eq_single_one {A : Type*} [Group A] [Fintype A]
    [DecidableEq A] {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (c : R) (hc : φ c ≠ 0) (z f : MonoidAlgebra R A)
    (hz : MonoidAlgebra.mapRingHom A φ z = MonoidAlgebra.single (1 : A) (φ c))
    (hf : f * z = 0) : f = 0 := by
  set M : Matrix A A R := fun i j => (MonoidAlgebra.single j 1 * z).coeff i with hM
  set v : A → R := fun i => f.coeff i with hv
  -- The matrix of right multiplication by `z` acts on the coefficient vector of `f` as
  -- right multiplication by `z` does.
  have hcoeff : ∀ i : A, (f * z).coeff i = (M.mulVec v) i := by
    intro i
    have h1 : (f * z).coeff i =
        ∑ a ∈ f.coeff.support, f.coeff a * (MonoidAlgebra.single a 1 * z).coeff i := by
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
      rw [Finsupp.sum, Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h : f.coeff a • (MonoidAlgebra.single a (1 : R)) = MonoidAlgebra.single a (f.coeff a) := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [← h, smul_mul_assoc, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    have h2 : (M.mulVec v) i =
        ∑ a ∈ f.coeff.support, f.coeff a * (MonoidAlgebra.single a 1 * z).coeff i := by
      rw [Matrix.mulVec_apply, dotProduct, hM, hv]
      trans ∑ a : A, f.coeff a * (MonoidAlgebra.single a 1 * z).coeff i
      · exact Finset.sum_congr rfl (fun a _ => by simp [Matrix.row, mul_comm])
      · rw [← Finset.sum_subset (Finset.subset_univ _) (fun a _ ha =>
          by rw [Finsupp.notMem_support_iff.mp ha, zero_mul])]
    rw [h1, h2]
  -- The determinant of the matrix is non-zero.
  have hdet : M.det ≠ 0 := by
    intro h0
    have h2 : φ M.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det] at h2
    have h3 : φ.mapMatrix M = (φ c) • (1 : Matrix A A S) := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
      rw [← coeff_mapRingHom φ (MonoidAlgebra.single j 1 * z) i,
        map_mul (MonoidAlgebra.mapRingHom A φ), MonoidAlgebra.mapRingHom_single, map_one, hz,
        MonoidAlgebra.single_mul_single, one_mul, mul_one, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; simp
      · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hij, if_neg hij, mul_zero]
    rw [h3, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    exact (pow_ne_zero _ hc) h2
  have hMv : M.mulVec v = 0 := by
    funext i
    rw [← hcoeff i, hf, MonoidAlgebra.coeff_zero]
    rfl
  -- The adjugate identity.
  have hdetv : M.det • v = 0 := by
    have h1 := Matrix.mulVec_mulVec v M.adjugate M
    rw [hMv, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    simpa using h1.symm
  ext i
  have h4 := congrFun hdetv i
  rw [Pi.smul_apply, Pi.zero_apply, hv] at h4
  exact (mul_eq_zero.mp h4).resolve_left hdet

/-- For a subgroup `C` of a group `A` and a commutative semiring `R`, the element
`ρ_C = ∑_{c ∈ C} single c 1` of `R[A]` satisfies `ρ_C * ρ_C = |C| • ρ_C`. -/
theorem sum_single_mul_sum_single {R : Type*} [CommSemiring R] {A : Type*} [Group A]
    (C : Subgroup A) [Fintype ↥C] :
    (∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : R)) *
      (∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : R)) =
      (Nat.card ↥C : R) • (∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : R)) := by
  classical
  rw [Finset.sum_mul]
  have hterm : ∀ c : ↥C, MonoidAlgebra.single (c : A) (1 : R) *
      (∑ d : ↥C, MonoidAlgebra.single (d : A) (1 : R)) =
      ∑ d : ↥C, MonoidAlgebra.single ((c * d : ↥C) : A) (1 : R) := by
    intro c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [MonoidAlgebra.single_mul_single, one_mul,
        show ((c * d : ↥C) : A) = (c : A) * (d : A) from rfl]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_comm]
  have hinner : ∀ d : ↥C, (∑ x : ↥C, MonoidAlgebra.single ((x * d : ↥C) : A) (1 : R)) =
      ∑ x : ↥C, MonoidAlgebra.single ((x : ↥C) : A) (1 : R) := by
    intro d
    show (∑ x : ↥C, MonoidAlgebra.single (((Equiv.mulRight d) x : ↥C) : A) (1 : R)) = _
    rw [Equiv.sum_comp (Equiv.mulRight d)
      (fun x : ↥C => MonoidAlgebra.single ((x : ↥C) : A) (1 : R))]
  rw [Finset.sum_congr rfl (fun d _ => hinner d), Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul R]

/-- `MonoidAlgebra.single 1 u` is the scalar `u`. -/
theorem single_one_eq_smul_one {R M : Type*} [Semiring R] [MulOneClass M] (u : R) :
    MonoidAlgebra.single (1 : M) u = u • (1 : MonoidAlgebra R M) := by
  rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]

end Work.NormalComplement.AppVII
