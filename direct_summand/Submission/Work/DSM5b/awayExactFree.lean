import Mathlib
import Submission.Work.DSM5b.awayComplex
import Submission.Work.DSM5b.prod_dvd_mul_of_subset_insert

/-!
# `Work.DSM5b.awayExactFree` — exactness of the `T`-localised chart complex, clash-free

`AWX t T m = ∀ τ : Fin (m+1) → ι, Localization.Away (T * tS t (tupRng τ))` with the alternating
coface differential `AWd t T m` (`Submission/Work/DSM5b/awayComplex.lean`).  When `t j₀ = T ^ e`, the
image of `t j₀ = T ^ e` is a unit in every term, so the localisation map
`awayT (tupRng_ins_subset j₀ σ) : R[1/(T t_σ)] → R[1/(T t_{σ ∪ {j₀}})]` is an isomorphism; the
standard cosimplicial contraction `y σ = (that isomorphism).symm (z (tupIns j₀ σ))` then exhibits
every positive-degree cycle as a boundary.

This is the content of `Submission/Work/DSM5b/awayPsi.lean` + `Submission/Work/DSM5b/awayExact.lean`,
**re-derived here under non-clashing names**.  The reason for the duplication is a workspace name
clash: `awayPsi.lean` and `CechIsoDefs.lean` both define `Work.DSM5b.psi`, so no module can import
both, and the M5b node needs the `cechIso` chain (`CechIsoDefs`) together with the exactness here
(via `Work.DSM5b.honestKillingCore`, which is importable and takes `hexact` as a hypothesis).  The
inverse map is called `awayInv` here.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Psi

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- The localisation map `awayT` depends only on the two finsets, not on the proof of the inclusion. -/
lemma aef_awayT_congr (t : ι → R) (T : R) {S S' : Finset ι} (h h' : S ⊆ S') :
    awayT t T h = awayT t T h' := by
  haveI : Subsingleton (Localization.Away (T * tS t S) →ₐ[R] Localization.Away (T * tS t S')) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (T * tS t S))
  exact Subsingleton.elim _ _

/-- The inverse of the localisation map `AWX·σ → AWX·(tupIns k σ)`, when `t k = T ^ e`. -/
noncomputable def awayInv (t : ι → R) (T : R) (k : ι) (e : ℕ) (hj₀ : t k = T ^ e) {m : ℕ}
    (σ : Fin (m + 1) → ι) :
    Localization.Away (T * tS t (tupRng (tupIns k σ))) →ₐ[R]
      Localization.Away (T * tS t (tupRng σ)) :=
  IsLocalization.Away.liftAlgHom (T * tS t (tupRng (tupIns k σ)))
    (f := Algebra.ofId R (Localization.Away (T * tS t (tupRng σ))))
    (by
      have hdiv : tS t (tupRng (tupIns k σ)) ∣ tS t (tupRng σ) * t k :=
        prod_dvd_mul_of_subset_insert t (tupRng_ins_subset k σ)
          (le_of_eq (tupRng_tupIns k σ))
      have hdvd : T * tS t (tupRng (tupIns k σ)) ∣ (T * tS t (tupRng σ)) * t k := by
        rw [mul_assoc]
        exact mul_dvd_mul_left T hdiv
      have hTunit : IsUnit (algebraMap R (Localization.Away (T * tS t (tupRng σ))) T) :=
        isUnit_of_dvd_unit
          (map_dvd (algebraMap R (Localization.Away (T * tS t (tupRng σ))))
            (dvd_mul_right T (tS t (tupRng σ))))
          (IsLocalization.Away.algebraMap_isUnit (T * tS t (tupRng σ)))
      have htkunit : IsUnit (algebraMap R (Localization.Away (T * tS t (tupRng σ))) (t k)) := by
        rw [hj₀, map_pow]
        exact hTunit.pow e
      refine isUnit_of_dvd_unit
        (map_dvd (algebraMap R (Localization.Away (T * tS t (tupRng σ)))) hdvd) ?_
      rw [map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit (T * tS t (tupRng σ))).mul htkunit)

/-- `awayInv` is a left inverse of the canonical map `awayT`. -/
lemma awayInv_awayT (t : ι → R) (T : R) (k : ι) (e : ℕ) (hj₀ : t k = T ^ e) {m : ℕ}
    (σ : Fin (m + 1) → ι) (x : Localization.Away (T * tS t (tupRng σ))) :
    awayInv t T k e hj₀ σ (awayT t T (tupRng_ins_subset k σ) x) = x := by
  haveI : Subsingleton (Localization.Away (T * tS t (tupRng σ)) →ₐ[R]
      Localization.Away (T * tS t (tupRng σ))) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (T * tS t (tupRng σ)))
  have h : (awayInv t T k e hj₀ σ).comp (awayT t T (tupRng_ins_subset k σ)) = AlgHom.id R _ :=
    Subsingleton.elim _ _
  exact AlgHom.congr_fun h x

/-- `awayInv` is a right inverse of the canonical map `awayT`. -/
lemma awayT_awayInv (t : ι → R) (T : R) (k : ι) (e : ℕ) (hj₀ : t k = T ^ e) {m : ℕ}
    (σ : Fin (m + 1) → ι) (x : Localization.Away (T * tS t (tupRng (tupIns k σ)))) :
    awayT t T (tupRng_ins_subset k σ) (awayInv t T k e hj₀ σ x) = x := by
  haveI : Subsingleton (Localization.Away (T * tS t (tupRng (tupIns k σ))) →ₐ[R]
      Localization.Away (T * tS t (tupRng (tupIns k σ)))) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (T * tS t (tupRng (tupIns k σ))))
  have h : (awayT t T (tupRng_ins_subset k σ)).comp (awayInv t T k e hj₀ σ) = AlgHom.id R _ :=
    Subsingleton.elim _ _
  exact AlgHom.congr_fun h x

/-- Compatibility of `awayInv` with the "delete a coordinate" maps. -/
lemma awayInv_awayT_comp (t : ι → R) (T : R) (k : ι) (e : ℕ) (hj₀ : t k = T ^ e) {m : ℕ}
    (ρ : Fin (m + 2) → ι) (i : Fin (m + 2)) :
    (awayInv t T k e hj₀ ρ).comp (awayT t T (tupRng_ins_del_subset k ρ i)) =
      (awayT t T (tupRng_del_subset i ρ)).comp (awayInv t T k e hj₀ (tupDel i ρ)) := by
  haveI : Subsingleton
      (Localization.Away (T * tS t (tupRng (tupIns k (tupDel i ρ)))) →ₐ[R]
        Localization.Away (T * tS t (tupRng ρ))) :=
    IsLocalization.algHom_subsingleton
      (Submonoid.powers (T * tS t (tupRng (tupIns k (tupDel i ρ)))))
  exact Subsingleton.elim _ _

end Psi

section Contract

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- Transport of an element of `AWX` along an equality of tuples. -/
lemma aef_cast_apply (t : ι → R) (T : R) {m : ℕ} (z : AWX t T m)
    {b c : Fin (m + 1) → ι} (h : b = c) :
    (AlgEquiv.cast (R := R) (A := fun τ => Localization.Away (T * tS t (tupRng τ))) h) (z b)
      = z c := by
  cases h
  rfl

/-- The `i = 0` summand: `tupDel 0 (tupIns k ρ) = ρ`. -/
lemma aef_term_ident_zero {n : ℕ} (t : ι → R) (T : R) (k : ι)
    (z : AWX t T (n+1)) (ρ : Fin (n+2) → ι) :
    awayT t T (tupRng_del_subset (0 : Fin (n+3)) (tupIns k ρ)) (z (tupDel 0 (tupIns k ρ)))
      = awayT t T (tupRng_ins_subset k ρ) (z ρ) := by
  have h : tupDel (0 : Fin (n+3)) (tupIns k ρ) = ρ := tupDel_ins_zero k ρ
  let E : Localization.Away (T * tS t (tupRng (tupDel (0 : Fin (n+3)) (tupIns k ρ)))) →ₐ[R]
        Localization.Away (T * tS t (tupRng ρ)) :=
      AlgEquiv.cast (R := R) (A := fun τ => Localization.Away (T * tS t (tupRng τ))) h
  have hzE : E (z (tupDel (0 : Fin (n+3)) (tupIns k ρ))) = z ρ := aef_cast_apply t T z h
  have hmap : (awayT t T (tupRng_ins_subset k ρ)).comp E
      = awayT t T (tupRng_del_subset (0 : Fin (n+3)) (tupIns k ρ)) := by
    haveI : Subsingleton
        (Localization.Away (T * tS t (tupRng (tupDel (0 : Fin (n+3)) (tupIns k ρ)))) →ₐ[R]
          Localization.Away (T * tS t (tupRng (tupIns k ρ)))) :=
      IsLocalization.algHom_subsingleton
        (Submonoid.powers (T * tS t (tupRng (tupDel (0 : Fin (n+3)) (tupIns k ρ)))))
    exact Subsingleton.elim _ _
  rw [← hmap, AlgHom.comp_apply, hzE]

/-- The `i.succ` summand: `tupDel i.succ (tupIns k ρ) = tupIns k (tupDel i ρ)`. -/
lemma aef_term_ident {n : ℕ} (t : ι → R) (T : R) (k : ι)
    (z : AWX t T (n+1)) (ρ : Fin (n+2) → ι) (i : Fin (n+2)) :
    awayT t T (tupRng_del_subset i.succ (tupIns k ρ)) (z (tupDel i.succ (tupIns k ρ)))
      = awayT t T (tupRng_ins_del_subset k ρ i) (z (tupIns k (tupDel i ρ))) := by
  have h : tupDel i.succ (tupIns k ρ) = tupIns k (tupDel i ρ) := tupDel_ins_succ k ρ i
  let E : Localization.Away (T * tS t (tupRng (tupDel i.succ (tupIns k ρ)))) →ₐ[R]
        Localization.Away (T * tS t (tupRng (tupIns k (tupDel i ρ)))) :=
      AlgEquiv.cast (R := R) (A := fun τ => Localization.Away (T * tS t (tupRng τ))) h
  have hzE : E (z (tupDel i.succ (tupIns k ρ))) = z (tupIns k (tupDel i ρ)) :=
    aef_cast_apply t T z h
  have hmap : (awayT t T (tupRng_ins_del_subset k ρ i)).comp E
      = awayT t T (tupRng_del_subset i.succ (tupIns k ρ)) := by
    haveI : Subsingleton
        (Localization.Away (T * tS t (tupRng (tupDel i.succ (tupIns k ρ)))) →ₐ[R]
          Localization.Away (T * tS t (tupRng (tupIns k ρ)))) :=
      IsLocalization.algHom_subsingleton
        (Submonoid.powers (T * tS t (tupRng (tupDel i.succ (tupIns k ρ)))))
    exact Subsingleton.elim _ _
  rw [← hmap, AlgHom.comp_apply, hzE]

/-- The cycle equation at `tupIns k ρ`, rearranged. -/
lemma aef_cycle_ins_eq {n : ℕ} (t : ι → R) (T : R) (k : ι) (e : ℕ) (hj₀ : t k = T ^ e)
    (z : AWX t T (n+1)) (hz : AWd t T (n+1) z = 0) (ρ : Fin (n+2) → ι) :
    awayT t T (tupRng_ins_subset k ρ) (z ρ) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
        awayT t T (tupRng_ins_del_subset k ρ i) (z (tupIns k (tupDel i ρ))) := by
  have hzρ : AWd t T (n + 1) z (tupIns k ρ) = 0 := by
    have := congrFun hz (tupIns k ρ); simpa using this
  rw [AWd_apply] at hzρ
  rw [Fin.sum_univ_succ] at hzρ
  simp only [Fin.val_zero, pow_zero, one_smul] at hzρ
  rw [aef_term_ident_zero t T k z ρ] at hzρ
  have hterm : ∀ i : Fin (n+2),
      ((-1:R)^((i.succ : Fin (n+3)) : ℕ)) •
          awayT t T (tupRng_del_subset i.succ (tupIns k ρ)) (z (tupDel i.succ (tupIns k ρ)))
      = - (((-1:R)^(i : ℕ)) •
          awayT t T (tupRng_ins_del_subset k ρ i) (z (tupIns k (tupDel i ρ)))) := by
    intro i
    rw [aef_term_ident t T k z ρ i, Fin.val_succ, pow_succ]
    rw [show ((-1:R) ^ (i : ℕ) * (-1)) = -((-1:R) ^ (i:ℕ)) from by ring, neg_smul]
  have hsum : (∑ i : Fin (n+2),
        ((-1:R)^((i.succ : Fin (n+3)) : ℕ)) •
          awayT t T (tupRng_del_subset i.succ (tupIns k ρ)) (z (tupDel i.succ (tupIns k ρ))))
      = - ∑ i : Fin (n+2), (((-1:R)^(i : ℕ)) •
          awayT t T (tupRng_ins_del_subset k ρ i) (z (tupIns k (tupDel i ρ)))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hsum] at hzρ
  rw [add_neg_eq_zero] at hzρ
  exact hzρ

end Contract

/-- **Exactness of the `T`-localised chart Čech complex in positive degrees** (clash-free version of
`Work.DSM5b.awayExact`). -/
theorem awayExactFree (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (T : R) (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e) :
    ∀ (n : ℕ) (z : AWX t T (n + 1)), AWd t T (n + 1) z = 0 →
      ∃ y : AWX t T n, AWd t T n y = z := by
  intro n z hz
  refine ⟨fun σ => awayInv t T j₀ e hj₀ σ (z (tupIns j₀ σ)), ?_⟩
  funext ρ
  rw [AWd_apply]
  have key := aef_cycle_ins_eq t T j₀ e hj₀ z hz ρ
  have h2 := congrArg (awayInv t T j₀ e hj₀ ρ) key
  rw [awayInv_awayT t T j₀ e hj₀ ρ (z ρ)] at h2
  have h3 : awayInv t T j₀ e hj₀ ρ
      (∑ i : Fin (n+2), ((-1:R)^(i:ℕ)) •
        awayT t T (tupRng_ins_del_subset j₀ ρ i) (z (tupIns j₀ (tupDel i ρ))))
      = ∑ i : Fin (n+2), ((-1:R)^(i:ℕ)) •
        awayT t T (tupRng_del_subset i ρ)
          (awayInv t T j₀ e hj₀ (tupDel i ρ) (z (tupIns j₀ (tupDel i ρ)))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    congr 1
    exact AlgHom.congr_fun (awayInv_awayT_comp t T j₀ e hj₀ ρ i) (z (tupIns j₀ (tupDel i ρ)))
  rw [h3] at h2
  exact h2.symm

end Work.DSM5b
