import Mathlib
import Submission.Work.DSG4b.ReesIdeal
import Submission.Work.DSG4b.coeff_mem_span_monomial
import Submission.Work.DSG4b.coeff_mem_map_algebraMap_reesAlgebra
import Submission.Work.DSG4b.le_span_of_forall_corrections

/-!
# The graded descent: a complete separated ring with Noetherian associated graded is Noetherian

This is the abstract form of Stacks 05GH / EGA 0_I 7.3.6: if `A` is complete and separated for the
`I`-adic topology and `gr_I(A) = ⨁ I^n/I^{n+1}` is Noetherian, then `A` is Noetherian.

The proof follows Stacks: for an ideal `J ⊆ A`, the Rees ideal `𝔍 = ⨁ (J ∩ I^n)X^n` of `J` in the
Rees algebra `A[IX]` has image `K = 𝔍/𝔍∩I·A[IX] = gr(J) ⊆ gr_I(A)`, which is finitely generated
because `gr_I(A)` is Noetherian. Lifting generators of `K` to `𝔍` and splitting them into
homogeneous components produces finitely many `g j ∈ J ∩ I ^ (d j)` whose associated graded pieces
generate `gr(J)`; equivalently, every `x ∈ J ⊓ I ^ n` differs from an `I`-combination of the `g j`
(weighted by `I ^ (n - d j)`) by an element of `J ⊓ I ^ (n+1)`. Iterating this correction
infinitely often and taking limits (possible since `A` is complete; the limit is unique by
separatedness) produces `a j ∈ A` with `x = ∑ j, a j * g j`, exactly as in
`Work.DSG4b.le_span_of_forall_corrections`.
-/

namespace Work.DSG4b

set_option linter.style.haveILetI false

open Polynomial

variable {A : Type*} [CommRing A]

theorem isNoetherianRing_of_isAdicComplete_graded (I : Ideal A) (hcomp : IsAdicComplete I A)
    (hgr : IsNoetherianRing (reesAlgebra I ⧸ Ideal.map (algebraMap A (reesAlgebra I)) I)) :
    IsNoetherianRing A := by
  classical
  rw [isNoetherianRing_iff_ideal_fg]
  intro J
  let 𝔞 : Ideal (reesAlgebra I) := Ideal.map (algebraMap A (reesAlgebra I)) I
  haveI : IsNoetherianRing (reesAlgebra I ⧸ 𝔞) := hgr
  -- The image of the Rees ideal of `J` in the associated graded ring is finitely generated.
  have hK : (Ideal.map (Ideal.Quotient.mk 𝔞) (reesIdealOf I J)).FG :=
    Ideal.fg_of_isNoetherianRing _
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hmem_span : ∀ i, s i ∈ Ideal.map (Ideal.Quotient.mk 𝔞) (reesIdealOf I J) := fun i =>
    hs ▸ Submodule.subset_span (Set.mem_range_self i)
  choose t ht hts using fun i =>
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk 𝔞)
      Ideal.Quotient.mk_surjective).mp (hmem_span i)
  -- Split each `t i` into homogeneous components; this yields the finite family of generators.
  let T : Fin m → Polynomial A := fun i => (t i : Polynomial A)
  let D : ℕ := (Finset.univ.sup fun i : Fin m => (T i).natDegree) + 1
  let d : Fin m × Fin D → ℕ := fun p => p.2.val
  let g : Fin m × Fin D → A := fun p => (T p.1).coeff p.2.val
  have hmem : ∀ p : Fin m × Fin D, g p ∈ I ^ (d p) := fun p =>
    (coeff_mem_of_mem_reesIdealOf I J (ht p.1) p.2.val).2
  have hgJ : ∀ p : Fin m × Fin D, g p ∈ J := fun p =>
    (coeff_mem_of_mem_reesIdealOf I J (ht p.1) p.2.val).1
  let gen : Fin m × Fin D → reesAlgebra I := fun p =>
    ⟨Polynomial.monomial (d p) (g p), reesAlgebra.monomial_mem.mpr (hmem p)⟩
  have hsub : ∀ i : Fin m, (T i).support ⊆ Finset.range D := by
    intro i k hk
    rw [Finset.mem_range]
    calc k ≤ (T i).natDegree := Polynomial.le_natDegree_of_mem_supp k hk
      _ ≤ Finset.univ.sup (fun i : Fin m => (T i).natDegree) :=
          Finset.le_sup (f := fun i : Fin m => (T i).natDegree) (Finset.mem_univ i)
      _ < D := Nat.lt_succ_self _
  -- The homogeneous decomposition of `t i`.
  have hpoly : ∀ i : Fin m, T i = ∑ k : Fin D, Polynomial.monomial k.val ((T i).coeff k.val) := by
    intro i
    calc T i = (T i).sum (fun n a => Polynomial.C a * Polynomial.X ^ n) :=
          (Polynomial.sum_C_mul_X_pow_eq (T i)).symm
      _ = ∑ n ∈ (T i).support, Polynomial.C ((T i).coeff n) * Polynomial.X ^ n :=
          Polynomial.sum_def (T i) _
      _ = ∑ n ∈ (T i).support, Polynomial.monomial n ((T i).coeff n) :=
          Finset.sum_congr rfl (fun n _ => Polynomial.C_mul_X_pow_eq_monomial)
      _ = ∑ n ∈ Finset.range D, Polynomial.monomial n ((T i).coeff n) :=
          (Finset.sum_subset (hsub i) (fun n _ hn =>
            (Polynomial.monomial_eq_zero_iff ((T i).coeff n) n).mpr
              (Polynomial.notMem_support_iff.mp hn)))
      _ = ∑ k : Fin D, Polynomial.monomial k.val ((T i).coeff k.val) :=
          (Fin.sum_univ_eq_sum_range (α := Polynomial A)
            (fun k : ℕ => Polynomial.monomial k ((T i).coeff k)) D).symm
  have hgen_eq : ∀ i, Ideal.Quotient.mk 𝔞 (t i) =
      ∑ k : Fin D, Ideal.Quotient.mk 𝔞 (gen (i, k)) := by
    intro i
    have hpoly_i : (∑ k : Fin D, ((gen (i, k) : reesAlgebra I) : Polynomial A)) = T i := by
      refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hpoly i).symm
      show Polynomial.monomial (d (i, k)) (g (i, k)) =
        Polynomial.monomial k.val ((T i).coeff k.val)
      rw [show d (i, k) = k.val from rfl, show g (i, k) = (T i).coeff k.val from rfl]
    have hS : (t i : reesAlgebra I) = ∑ k : Fin D, gen (i, k) := by
      apply Subtype.ext
      change (T i) = (Subalgebra.val (reesAlgebra I)) (∑ k : Fin D, gen (i, k))
      exact (hpoly_i.symm).trans (map_sum (Subalgebra.val (reesAlgebra I))
        (fun k : Fin D => gen (i, k)) Finset.univ).symm
    rw [hS]
    exact map_sum (Ideal.Quotient.mk 𝔞) (fun k : Fin D => gen (i, k)) Finset.univ
  -- The images of the `gen` generate the image `K`.
  have hle : Ideal.map (Ideal.Quotient.mk 𝔞) (reesIdealOf I J) ≤
      Ideal.span (Set.range fun p : Fin m × Fin D => Ideal.Quotient.mk 𝔞 (gen p)) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [← hts i, hgen_eq i]
    exact Submodule.sum_mem _ (fun k _ => Submodule.subset_span ⟨(i, k), rfl⟩)
  -- Hence the Rees ideal is contained in the span of the monomials plus `𝔞`.
  have h𝔍 : reesIdealOf I J ≤ Ideal.span (Set.range gen) ⊔ 𝔞 := by
    intro x hx
    have h2 : Ideal.span (Set.range fun p : Fin m × Fin D => Ideal.Quotient.mk 𝔞 (gen p)) =
        Ideal.map (Ideal.Quotient.mk 𝔞) (Ideal.span (Set.range gen)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have h1 : x ∈ Ideal.comap (Ideal.Quotient.mk 𝔞)
        (Ideal.map (Ideal.Quotient.mk 𝔞) (Ideal.span (Set.range gen))) :=
      Ideal.mem_comap.mpr (h2 ▸ hle (Ideal.mem_map_of_mem (Ideal.Quotient.mk 𝔞) hx))
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective
      (Ideal.span (Set.range gen))] at h1
    simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using h1
  -- The correction hypothesis.
  have hstep : ∀ n (x : A), x ∈ J ⊓ I ^ n → ∃ a : Fin m × Fin D → A,
      (∀ p, a p ∈ I ^ (n - d p)) ∧ x - ∑ p, a p * g p ∈ J ⊓ I ^ (n + 1) := by
    intro n x hx
    have hx𝔍 : (⟨Polynomial.monomial n x, reesAlgebra.monomial_mem.mpr hx.2⟩ : reesAlgebra I) ∈
        reesIdealOf I J := monomial_mem_reesIdealOf I J hx
    obtain ⟨k, hk, a, ha, hsum⟩ := Submodule.mem_sup.mp (h𝔍 hx𝔍)
    have hcoeff : x = (k : Polynomial A).coeff n + (a : Polynomial A).coeff n := by
      have h3 : ((k + a : reesAlgebra I) : Polynomial A).coeff n = x := by
        rw [hsum]
        change (Polynomial.monomial n x).coeff n = x
        rw [Polynomial.coeff_monomial, ite_eq_left rfl]
      rw [← h3, Subalgebra.coe_add, Polynomial.coeff_add]
    obtain ⟨a', ha', ha'eq⟩ := coeff_mem_span_monomial (I := I) (n := n) hmem hk
    have haI : (a : Polynomial A).coeff n ∈ I ^ (n + 1) :=
      coeff_mem_map_algebraMap_reesAlgebra ha n
    refine ⟨a', ha', ?_⟩
    have hsubst : x - ∑ p, a' p * g p = (a : Polynomial A).coeff n := by
      rw [hcoeff, ha'eq]; ring
    refine ⟨?_, ?_⟩
    · rw [hsubst, ← hsubst]
      exact J.sub_mem hx.1 (Submodule.sum_mem J fun p _ => J.mul_mem_left (a' p) (hgJ p))
    · rw [hsubst]; exact haI
  -- The limit step: `J` is generated by the `g p`.
  have hle' : J ≤ Ideal.span (Set.range g) :=
    le_span_of_forall_corrections hcomp g d hgJ hstep
  have hge : Ideal.span (Set.range g) ≤ J :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hgJ)
  rw [le_antisymm hle' hge]
  exact Submodule.fg_span (Set.finite_range g)

end Work.DSG4b
