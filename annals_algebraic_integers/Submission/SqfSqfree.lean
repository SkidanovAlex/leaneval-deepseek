import Mathlib
import Submission.RootData

/-!
# Squarefree over ℤ[X] for primitive-part times distinct integer linear factors

The main assembly needs a *squarefree integer polynomial* (Mathlib monoid
`Squarefree` in `ℤ[X]`: no square of a non-unit divides it).  We construct it
as `R := A.primPart * ∏_{s∈S} (X − C (s:ℤ))` where

  * `A ≠ 0` and the complexification `(A.map (algebraMap ℤ ℂ))` is Separable
    (so `A` has `natDegree`-many distinct complex roots — use
    `Submission.RootData.root_data_of_separable` to get an injective
    enumeration `α : Fin (A.natDegree) → ℂ` with the factorization
    `Qc A = C(lc)·∏(X − C(α i))`, where `Qc Q := Q.map (algebraMap ℤ ℂ)`),
  * `S : Finset ℕ` is a set of *non-roots*: no `s ∈ S` is a root of
    `A.map (algebraMap ℤ ℂ)`,
  * distinctness of the `s ∈ S` is automatic (Finset).

## Outline of a proof

Let `R := A.primPart * ∏ s in S, (X - C (s : ℤ))`.

(a) `R.IsPrimitive` (content `= 1`): `A.primPart` is primitive
    (`Polynomial.isPrimitive_primPart`), each `X − C s` is monic hence
    primitive, and `content` is multiplicative for `ℤ[X]`
    (`Polynomial.content_mul`, which needs the `ℤ` instance of
    `StrongNormalizedGCDMonoid`); you may also use
    `Polynomial.eq_C_content_mul_primPart` / `content_primPart`.

(b) `(R.map (algebraMap ℤ ℂ)).Squarefree` (monoid squarefree in `ℂ[X]`):
    it suffices to prove `(R.map (algebraMap ℤ ℂ)).Separable`
    (`Polynomial.Separable.squarefree`).  Expand:
    `A = C A.content * A.primPart`, so
    `(A.primPart).map ℂ = C (A.content : ℂ)⁻¹ • (A.map ℂ)`; a nonzero constant
    is a unit in `ℂ[X]`, and multiplying by units preserves Separable
    (`Polynomial.Separable.unit_mul` / `Separable.mul_unit`), so
    `(A.primPart).map ℂ` is Separable.  The product
    `∏ s in S, (X − C (s:ℂ))` is Separable by `Polynomial.separable_prod`
    (linear factors are pairwise coprime when the `s` are distinct;
    `separable_X_sub_C` gives each factor's separability).  Finally multiply
    the two separable factors: `Polynomial.Separable.mul` needs `IsCoprime`:
    `(A.primPart).map ℂ` and `X − C s` are coprime because `s` is not a root
    of `A` (over a field, `X − C a` is prime, so not dividing is equivalent to
    being coprime — or prove the coprimeness by a Bézout identity / via the
    division by the monic linear factor; alternatively show the product is
    Separable by first factoring `A.map ℂ = C(lc)·∏(X−C(α i))` from the root
    data and then using `separable_prod` once on ALL linear factors
    `(X − C(α i))` and `(X − C s)` — all roots distinct because `s` is not a
    root of `A` and the `α i` are injective).

(c) Conclude `Squarefree R` in `ℤ[X]`: prove the transfer lemma
    `Squarefree R` from (i) `R.IsPrimitive` and (ii)
    `Squarefree (R.map (algebraMap ℤ ℂ))`:

    - Given `b : ℤ[X]` with `b·b ∣ R`, map to `ℂ[X]`; (ii) makes `b.map ℂ` a
      unit in `ℂ[X]`, i.e. a nonzero constant polynomial; since the map
      `ℤ[X] → ℂ[X]` is injective, `b` is a constant polynomial `C z`,
      `z : ℤ`.
    - If `|z| ≥ 2`, `z² ∣ R` coefficientwise contradicts `R.IsPrimitive`
      (content `= 1`): all coefficients of `R` divisible by a prime `p ∣ z`;
      use `Polynomial.content` API (content of `R` divides each coefficient /
      is the gcd) or argue mod `p`.  Hence `z = ±1`, a unit of `ℤ[X]`.

The statement below only needs the Separable hypothesis on `A` and the
non-root condition; degree/root-data facts about `A` may be derived inside
(`A.natDegree` is whatever it is; if `A` is constant the root data step is
vacuous — handle `A.natDegree = 0` separately or branch on it).
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.SqfSqfree

/-- Transfer (c): a primitive integer polynomial whose complexification is
`Separable` is squarefree in `ℤ[X]`. -/
lemma squarefree_of_isPrimitive_of_map_separable {Q : Polynomial ℤ} (hQprim : Q.IsPrimitive)
    (hsepQ : (Q.map (algebraMap ℤ ℂ)).Separable) : Squarefree Q := by
  rw [Squarefree]
  intro q hqq
  have hdvd : (q.map (algebraMap ℤ ℂ)) * (q.map (algebraMap ℤ ℂ)) ∣
      Q.map (algebraMap ℤ ℂ) := by
    rcases hqq with ⟨w, hw⟩
    refine ⟨w.map (algebraMap ℤ ℂ), ?_⟩
    calc
      Q.map (algebraMap ℤ ℂ) = (q * q * w).map (algebraMap ℤ ℂ) := by rw [hw]
      _ = q.map (algebraMap ℤ ℂ) * q.map (algebraMap ℤ ℂ) *
          w.map (algebraMap ℤ ℂ) := by simp [Polynomial.map_mul, mul_assoc]
  have hu : IsUnit (q.map (algebraMap ℤ ℂ)) :=
    Polynomial.isUnit_of_self_mul_dvd_separable hsepQ hdvd
  have hdeg : q.natDegree = 0 := by
    have h1 : (q.map (algebraMap ℤ ℂ)).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_map_eq_of_injective
      Submission.RootData.algebraMap_int_complex_injective q] at h1
    exact h1
  have hq_eq : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  rw [hq_eq] at hqq
  have hCaa_dvd : (C ((q.coeff 0) * (q.coeff 0)) : ℤ[X]) ∣ Q := by
    rw [Polynomial.C_mul]
    exact hqq
  have hcont : (q.coeff 0) * (q.coeff 0) ∣ Q.content :=
    (Polynomial.dvd_content_iff_C_dvd (p := Q)
      (r := q.coeff 0 * q.coeff 0)).mpr hCaa_dvd
  have hcont1 : Q.content = 1 := (Polynomial.isPrimitive_iff_content_eq_one).mp hQprim
  have ha_dvd_one : (q.coeff 0) * (q.coeff 0) ∣ (1 : ℤ) := by
    simpa [hcont1] using hcont
  have ha1 : q.coeff 0 ∣ (1 : ℤ) :=
    dvd_trans (dvd_mul_right (q.coeff 0) (q.coeff 0)) ha_dvd_one
  have hua : IsUnit (q.coeff 0) := isUnit_of_dvd_one ha1
  rw [hq_eq]
  exact (Polynomial.isUnit_C).2 hua

/-- The complexification of the primitive part of a separable-complexification
integer polynomial is separable. -/
lemma primPart_map_separable {A : Polynomial ℤ}
    (hsep : (A.map (algebraMap ℤ ℂ)).Separable) :
    ((A.primPart).map (algebraMap ℤ ℂ)).Separable := by
  have hAeq : A.map (algebraMap ℤ ℂ) =
      C ((A.content : ℂ)) * (A.primPart).map (algebraMap ℤ ℂ) := by
    calc
      A.map (algebraMap ℤ ℂ) = (C A.content * A.primPart).map (algebraMap ℤ ℂ) := by
        congr 1
        exact Polynomial.eq_C_content_mul_primPart A
      _ = (C A.content).map (algebraMap ℤ ℂ) * (A.primPart).map (algebraMap ℤ ℂ) := by
        rw [Polynomial.map_mul]
      _ = C ((A.content : ℂ)) * (A.primPart).map (algebraMap ℤ ℂ) := by simp
  have h1 : (C ((A.content : ℂ)) * (A.primPart).map (algebraMap ℤ ℂ)).Separable := by
    rw [← hAeq]
    exact hsep
  exact h1.of_mul_right

/-- A primitive part is coprime with `X − C s` whenever `s` is not a complex
root of `A` (over the field ℂ, `X − C s` is prime, so non-divisibility is
coprimeness). -/
lemma primPart_coprime_X_sub_C {A : Polynomial ℤ}
    (s : ℕ) (hsroot : ¬ Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ)) = 0) :
    IsCoprime ((A.primPart).map (algebraMap ℤ ℂ)) (X - C (s : ℂ) : ℂ[X]) := by
  classical
  let f : Polynomial ℂ := (A.primPart).map (algebraMap ℤ ℂ)
  have hdiv_or : (X - C (s : ℂ) : ℂ[X]) ∣ f ∨ IsCoprime (X - C (s : ℂ) : ℂ[X]) f := by
    exact EuclideanDomain.dvd_or_coprime (X - C (s : ℂ) : ℂ[X]) f
      (Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C (s : ℂ)))
  cases hdiv_or with
  | inl hdiv =>
      exfalso
      apply hsroot
      have heval : f.eval (s : ℂ) = 0 := (Polynomial.dvd_iff_isRoot.mp hdiv)
      have haeval_f : Polynomial.aeval (s : ℂ) f = 0 := by
        simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using heval
      have hAeq : A.map (algebraMap ℤ ℂ) = C ((A.content : ℂ)) * f := by
        calc
          A.map (algebraMap ℤ ℂ) = (C A.content * A.primPart).map (algebraMap ℤ ℂ) := by
            congr 1
            exact Polynomial.eq_C_content_mul_primPart A
          _ = (C A.content).map (algebraMap ℤ ℂ) * (A.primPart).map (algebraMap ℤ ℂ) := by
            rw [Polynomial.map_mul]
          _ = C ((A.content : ℂ)) * (A.primPart).map (algebraMap ℤ ℂ) := by simp
      calc
        Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ))
            = Polynomial.aeval (s : ℂ) (C ((A.content : ℂ)) * f) := by rw [hAeq]
        _ = ((A.content : ℂ)) * Polynomial.aeval (s : ℂ) f := by simp
        _ = 0 := by rw [haeval_f, mul_zero]
  | inr hcop => exact hcop.symm

/-- The complexification of the product
`A.primPart * ∏_{s∈S}(X − C s)` is separable: the primitive-part factor is
separable, the distinct linear factors are pairwise coprime, and the primitive
part is coprime to every linear factor because no `s ∈ S` is a root. -/
lemma R_map_separable {A : Polynomial ℤ}
    (hsep : (A.map (algebraMap ℤ ℂ)).Separable) (S : Finset ℕ)
    (hSroot : ∀ s ∈ S, ¬ Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ)) = 0) :
    ((A.primPart * S.prod (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))).map
      (algebraMap ℤ ℂ)).Separable := by
  rw [Polynomial.map_mul]
  have hfsep : ((A.primPart).map (algebraMap ℤ ℂ)).Separable :=
    primPart_map_separable hsep
  have hprodsep : (S.prod (fun s : ℕ => (X - C (s : ℂ) : ℂ[X]))).Separable := by
    refine Polynomial.separable_prod' ?_ ?_
    · intro x hx y hy hxy
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_
      apply IsUnit.mk0
      exact sub_ne_zero.mpr (fun h => hxy (Nat.cast_injective h))
    · intro x hx
      exact Polynomial.separable_X_sub_C
  have hcop : IsCoprime ((A.primPart).map (algebraMap ℤ ℂ))
      (S.prod (fun s : ℕ => (X - C (s : ℂ) : ℂ[X]))) := by
    refine IsCoprime.prod_right ?_
    intro s hs
    exact primPart_coprime_X_sub_C s (hSroot s hs)
  have hmap_prod : (S.prod (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))).map (algebraMap ℤ ℂ) =
      S.prod (fun s : ℕ => (X - C (s : ℂ) : ℂ[X])) := by
    rw [Polynomial.map_prod]
    simp [Polynomial.map_sub]
  rw [hmap_prod]
  exact hfsep.mul hprodsep hcop

/-- Multiplying the primitive part of a separable-complexification integer
polynomial by `∏_{s∈S}(X − C s)` over natural `s` that are not complex roots
of the original gives a squarefree integer polynomial. -/
theorem squarefree_mul_primPart {A : Polynomial ℤ} (hA : A ≠ 0)
    (hsep : (A.map (algebraMap ℤ ℂ)).Separable)
    (S : Finset ℕ)
    (hSroot : ∀ s ∈ S, ¬ Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ)) = 0) :
    Squarefree (A.primPart * S.prod (fun s : ℕ => (Polynomial.X - Polynomial.C (s : ℤ)))) := by
  let R : Polynomial ℤ := A.primPart * S.prod (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))
  have hsepR : (R.map (algebraMap ℤ ℂ)).Separable := by
    dsimp [R]
    exact R_map_separable hsep S hSroot
  have hprimR : R.IsPrimitive := by
    dsimp [R]
    have hprimA : (A.primPart).IsPrimitive := Polynomial.isPrimitive_primPart A
    have hmonP : (S.prod (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))).Monic :=
      Polynomial.monic_prod_of_monic S (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))
        (by intro s _hs; exact Polynomial.monic_X_sub_C (s : ℤ))
    have hprimP : (S.prod (fun s : ℕ => (X - C (s : ℤ) : ℤ[X]))).IsPrimitive :=
      hmonP.isPrimitive
    exact hprimA.mul hprimP
  have hsq : Squarefree R := squarefree_of_isPrimitive_of_map_separable hprimR hsepR
  simpa [R] using hsq

end Submission.SqfSqfree
