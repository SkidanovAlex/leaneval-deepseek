import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.vanishing_ideal_chart

namespace Work.DSEQP

universe a

open scoped BigOperators
open HomogeneousLocalization

/-!
# `Work.DSEQP.jvan_dehomog_monomial`

The dehomogenisation of a monomial in the chart ring `Away 𝒜 (x_j)`, where `𝒜 = PGr A N` is the
standard grading of `A[x₀,…,x_N]` and `x_j = xS {j} = X j`:

`monomial c b / x_j ^ (deg c) = b · ∏_i (X_i / x_j) ^ (c i)`.

The right hand side is written with the `A`-algebra structure of the chart ring
(`fromZeroRingHom ∘ algebraMap`).

The proof is a two-step computation in the homogeneous localisation: first `Away.mk` of the
numerator of degree `0` is the structure map from `𝒜 0` (the `C b`-component), then a finset
induction (`jvan_away_mk_finset_prod`) multiplies the mono-`Away.mk`-factors `(X_i / x_j) ^ (c i)`
using `away_mk_mul` / `away_mk_pow`.
-/

section Helpers

variable {S : Type*} [CommRing S] {σ₀ : Type*} [SetLike σ₀ S] [AddSubgroupClass σ₀ S]
variable {𝒜 : ℕ → σ₀} [GradedRing 𝒜]

/-- Powers of `Away.mk` for a degree-`1` base element, with the base written as `g` rather than
`g ^ 1`. -/
lemma jvan_away_mk_pow_unit {f : S} (hf : f ∈ 𝒜 1) {g : S} (hg : g ∈ 𝒜 1) (n : ℕ)
    (hg' : g ∈ 𝒜 ((1:ℕ) • (1:ℕ))) :
    (Away.mk 𝒜 hf 1 g hg') ^ n = Away.mk 𝒜 hf n (g ^ n) (SetLike.pow_mem_graded n hg) := by
  have h1 : Away.mk 𝒜 hf 1 (g ^ 1) (by simpa using hg) = Away.mk 𝒜 hf 1 g hg' :=
    away_mk_congr hf rfl (pow_one g) _ hg'
  rw [← h1]
  exact away_mk_pow hf hg n

/-- **Dehomogenisation of a product of monomials.**  The product over a finset of the fractions
`g i ^ n i / f ^ (n i)` is the fraction `(∏ g i ^ n i) / f ^ (∑ n i)`. -/
lemma jvan_away_mk_finset_prod {σ : Type*} [DecidableEq σ] {f : S} (hf : f ∈ 𝒜 1) (s : Finset σ)
    (n : σ → ℕ) (g : σ → S) (hg : ∀ i, g i ∈ 𝒜 1)
    (hx : ∏ i ∈ s, g i ^ n i ∈ 𝒜 ((∑ i ∈ s, n i) • 1)) :
    Away.mk 𝒜 hf (∑ i ∈ s, n i) (∏ i ∈ s, g i ^ n i) hx
      = ∏ i ∈ s, (Away.mk 𝒜 hf 1 (g i) (by simpa using hg i)) ^ n i := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (1 : S) ∈ 𝒜 ((0:ℕ) • (1:ℕ)) := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
      calc Away.mk 𝒜 hf (∑ i ∈ ∅, n i) (∏ i ∈ ∅, g i ^ n i) hx
          = Away.mk 𝒜 hf 0 1 h0 := away_mk_congr hf Finset.sum_empty Finset.prod_empty hx h0
        _ = Away.mk 𝒜 hf 0 (f ^ 0) (SetLike.pow_mem_graded 0 hf) :=
              away_mk_congr hf rfl (pow_zero f).symm h0 _
        _ = 1 := away_mk_self hf 0
        _ = ∏ i ∈ ∅, (Away.mk 𝒜 hf 1 (g i) (by simpa using hg i)) ^ n i :=
              Finset.prod_empty.symm
  | insert a s ha ih =>
      have hxa : g a ^ n a ∈ 𝒜 (n a • 1) := SetLike.pow_mem_graded (n a) (hg a)
      have hxs : ∏ i ∈ s, g i ^ n i ∈ 𝒜 ((∑ i ∈ s, n i) • 1) := by
        have h := SetLike.prod_mem_graded 𝒜 (fun i : σ => n i • (1:ℕ)) (fun i => g i ^ n i)
          (F := s) (fun i _ => SetLike.pow_mem_graded (n i) (hg i))
        simpa only [smul_eq_mul, mul_one] using h
      have hcomb : g a ^ n a * ∏ i ∈ s, g i ^ n i ∈ 𝒜 ((n a + ∑ i ∈ s, n i) • 1) := by
        rw [add_smul]
        exact SetLike.mul_mem_graded hxa hxs
      calc Away.mk 𝒜 hf (∑ i ∈ insert a s, n i) (∏ i ∈ insert a s, g i ^ n i) hx
          = Away.mk 𝒜 hf (n a + ∑ i ∈ s, n i) (g a ^ n a * ∏ i ∈ s, g i ^ n i) hcomb :=
              away_mk_congr hf (Finset.sum_insert ha) (Finset.prod_insert ha) hx hcomb
        _ = Away.mk 𝒜 hf (n a) (g a ^ n a) hxa
              * Away.mk 𝒜 hf (∑ i ∈ s, n i) (∏ i ∈ s, g i ^ n i) hxs :=
              (away_mk_mul hf (n a) (∑ i ∈ s, n i) (g a ^ n a) (∏ i ∈ s, g i ^ n i)
                hxa hxs).symm
        _ = (Away.mk 𝒜 hf 1 (g a) (by simpa using hg a)) ^ (n a)
              * ∏ i ∈ s, (Away.mk 𝒜 hf 1 (g i) (by simpa using hg i)) ^ n i := by
              rw [← jvan_away_mk_pow_unit hf (hg a) (n a) (by simpa using hg a), ih hxs]
        _ = ∏ i ∈ insert a s, (Away.mk 𝒜 hf 1 (g i) (by simpa using hg i)) ^ n i := by
              rw [Finset.prod_insert ha]

end Helpers

/-- The dehomogenisation of a monomial `monomial c b` in the chart `Away 𝒜 (xS {j})`. -/
lemma jvan_dehomog_monomial (A : Type a) [CommRing A] {N : ℕ} (j : Fin (N + 1))
    (c : Fin (N + 1) →₀ ℕ) (b : A) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
        (MvPolynomial.monomial c b)
        (by simpa using (MvPolynomial.mem_homogeneousSubmodule (σ := Fin (N+1)) (R := A) c.degree
          (MvPolynomial.monomial c b)).mpr (MvPolynomial.isHomogeneous_monomial b rfl)) =
      HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
          (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
          (algebraMap A (DSMap.PGr A N 0) b) *
        c.prod (fun i k => (HomogeneousLocalization.Away.mk (DSMap.PGr A N)
            (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 1
            (MvPolynomial.X i) (by simpa using DSMap.Mix2.X_mem_PGr i)) ^ k) := by
  have hC_mem : (MvPolynomial.C b : MvPolynomial (Fin (N+1)) A)
      ∈ DSMap.PGr A N ((0:ℕ) • (1:ℕ)) := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule (σ := Fin (N+1)) (R := A) 0
      (MvPolynomial.C b)).mpr (MvPolynomial.isHomogeneous_C (Fin (N+1)) b)
  have hP_mem : (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k))
      ∈ DSMap.PGr A N (c.degree • (1:ℕ)) := by
    have h := SetLike.prod_mem_graded (DSMap.PGr A N) (fun i : Fin (N+1) => c i • (1:ℕ))
      (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ c i)
      (F := c.support) (fun i _ => SetLike.pow_mem_graded (c i) (DSMap.Mix2.X_mem_PGr i))
    show (∏ i ∈ c.support, (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ c i)
      ∈ DSMap.PGr A N (c.degree • (1:ℕ))
    simpa only [Finsupp.degree_apply, smul_eq_mul, mul_one] using h
  have hcomb_mem : (MvPolynomial.C b * c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k))
      ∈ DSMap.PGr A N (c.degree • (1:ℕ)) := by
    have h := SetLike.mul_mem_graded hC_mem hP_mem
    simpa using h
  have hcomb_mem' : (MvPolynomial.C b * c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k))
      ∈ DSMap.PGr A N ((0 + c.degree) • (1:ℕ)) := by
    simpa only [zero_add] using hcomb_mem
  have key : ∀ (hm : (MvPolynomial.monomial c b) ∈ DSMap.PGr A N (c.degree • (1:ℕ))),
      Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
          (MvPolynomial.monomial c b) hm
        = fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
            (algebraMap A (DSMap.PGr A N 0) b) *
          c.prod (fun i k => (Away.mk (DSMap.PGr A N)
              (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 1
              (MvPolynomial.X i) (by simpa using DSMap.Mix2.X_mem_PGr i)) ^ k) := by
    intro hm
    have hval : (fromZeroRingHom (DSMap.PGr A N)
          (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
          (algebraMap A (DSMap.PGr A N 0) b)).val
        = Localization.mk ((algebraMap A (DSMap.PGr A N 0) b) : MvPolynomial (Fin (N+1)) A)
            (1 : Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1))))) := rfl
    have hCZ : Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 0
          (MvPolynomial.C b) hC_mem
        = fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
            (algebraMap A (DSMap.PGr A N 0) b) := by
      apply HomogeneousLocalization.val_injective
        (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
      rw [Away.val_mk, hval]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul, SetLike.GradeZero.coe_algebraMap,
        MvPolynomial.algebraMap_eq, pow_zero]
    have hP_mem' : (∏ i ∈ c.support, (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ c i)
        ∈ DSMap.PGr A N ((∑ i ∈ c.support, c i) • (1:ℕ)) := by
      have h := SetLike.prod_mem_graded (DSMap.PGr A N) (fun i : Fin (N+1) => c i • (1:ℕ))
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ c i)
        (F := c.support) (fun i _ => SetLike.pow_mem_graded (c i) (DSMap.Mix2.X_mem_PGr i))
      simpa only [smul_eq_mul, mul_one] using h
    have hProd : Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
          (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k)) hP_mem
        = c.prod (fun i k => (Away.mk (DSMap.PGr A N)
            (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 1
            (MvPolynomial.X i) (by simpa using DSMap.Mix2.X_mem_PGr i)) ^ k) := by
      have hstep : Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
            (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k)) hP_mem
          = Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j)
              (∑ i ∈ c.support, c i)
              (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k)) hP_mem' :=
        away_mk_congr (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j)
          (Finsupp.degree_apply c).symm rfl hP_mem hP_mem'
      rw [hstep]
      exact jvan_away_mk_finset_prod (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.support c
        (fun i => MvPolynomial.X i) (fun i => DSMap.Mix2.X_mem_PGr i) hP_mem'
    calc Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
          (MvPolynomial.monomial c b) hm
        = Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
            (MvPolynomial.C b * c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k))
            hcomb_mem :=
          away_mk_congr (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) rfl MvPolynomial.monomial_eq
            hm hcomb_mem
      _ = Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 0
            (MvPolynomial.C b) hC_mem
            * Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
                (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k)) hP_mem :=
          (away_mk_congr (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) (zero_add c.degree).symm
              rfl hcomb_mem hcomb_mem').trans
            (away_mk_mul (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 0 c.degree
              (MvPolynomial.C b) (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k))
              hC_mem hP_mem).symm
      _ = fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
            (algebraMap A (DSMap.PGr A N 0) b)
            * Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) c.degree
                (c.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N+1)) A) ^ k)) hP_mem := by
          rw [hCZ]
      _ = fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers (Work.DSEQP.xS (A := A) ({j} : Finset (Fin (N+1)))))
            (algebraMap A (DSMap.PGr A N 0) b)
            * c.prod (fun i k => (Away.mk (DSMap.PGr A N)
                (Work.DSEQP.xS_singleton_mem (A := A) (N := N) j) 1
                (MvPolynomial.X i) (by simpa using DSMap.Mix2.X_mem_PGr i)) ^ k) := by
          rw [hProd]
  exact key _

end Work.DSEQP
