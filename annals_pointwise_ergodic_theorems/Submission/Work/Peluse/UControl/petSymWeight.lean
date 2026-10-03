import Mathlib
import Submission.Work.Peluse.UControl.PetStateSym

/-!
# The weight-vector decrease of one PET step, at the *minimum* degree

`PetStateSym.weight S d` is Peluse's termination measure for the PET chain, read over the parameter
ring `MvPolynomial (Fin k) ℤ`: `V j` is the number of *distinct* leading coefficients among the
slots `i` with `(S.P i).natDegree = j`.

This file proves `petSymWeight`: if every slot of the symbolic state `S` has `natDegree ≥ 1`
(`hnc`), if `d'` is the *smallest* degree occurring among the slots (`hd'`, read through `hnc`), and
`i₀` is a slot of degree exactly `d'` (`hi₀`), then one PET step at `i₀` strictly lowers the weight
vector in the order `PetStep.petLt` — *whether or not* the leading coefficients of the slots of
degree `d'` are distinct.

This is the hypothesis-free form of `petChainSymWeight` (which assumes additionally that the leading
coefficient `lc (P i₀)` does not occur among the other slots of degree `d'`).  The distinction is
exactly the two cases of the counting argument at the critical degree `d'`:

* slots of degree `> d'` keep their degree and leading coefficient, so the weight vectors agree at
  every coordinate above `d'`;
* a slot of degree `d'` with `i ≠ i₀` keeps degree `d'` exactly when
  `lc (P i) ≠ lc (P i₀)`; then its leading coefficient becomes `lc (P i) − lc (P i₀)`.  When
  `lc (P i) = lc (P i₀)` the leading terms cancel and the slot drops *strictly below* `d'`
  (`d' ≥ 1` because of `hnc`), and the same happens for the slot `(i₀, ε)`.

Hence the set of leading coefficients at degree `d'` of the stepped state is, up to the injective
maps `v ↦ ren (v − lc (P i₀))`, the set `A \ {lc (P i₀)}` where `A` is the set of leading
coefficients of the *other* slots of degree `d'`; that of the original state is
`insert (lc (P i₀)) A`.  Since `card (insert x A) = card (A \ {x}) + 1` for any `x`, the weight
strictly decreases at the coordinate `d'`, and there is no coordinate above it where the two weight
vectors differ.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep
open Polynomial

/-! ## 1. Polynomial bookkeeping over a general ring -/

private lemma psw_comp_X_add_C_natDegree {R : Type*} [Semiring R] [NoZeroDivisors R] [Nontrivial R]
    (p : Polynomial R) (t : R) :
    (p.comp (Polynomial.X + Polynomial.C t)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

private lemma psw_comp_X_add_C_leadingCoeff {R : Type*} [Semiring R] [NoZeroDivisors R]
    [Nontrivial R] (p : Polynomial R) (t : R) :
    (p.comp (Polynomial.X + Polynomial.C t)).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num),
    Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

/-- If `p` and `q` have the same degree and the same leading coefficient then `p - q` has strictly
smaller degree (for `p` nonconstant). -/
private lemma psw_sub_lt_case {R : Type*} [Ring R] (p q : Polynomial R)
    (hp : 0 < p.natDegree) (hdeg : p.natDegree = q.natDegree)
    (hlc : p.leadingCoeff = q.leadingCoeff) : (p - q).natDegree < p.natDegree := by
  by_contra h
  rw [not_lt] at h
  have hzero : (p - q).coeff ((p - q).natDegree) = 0 := by
    rw [Polynomial.coeff_sub]
    rcases lt_or_eq_of_le h with hlt | heq
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hdeg]; exact hlt), sub_zero]
    · rw [← heq, Polynomial.coeff_natDegree, hdeg, Polynomial.coeff_natDegree, hlc, sub_self]
  rw [Polynomial.coeff_natDegree] at hzero
  have hpq : p - q = 0 := Polynomial.leadingCoeff_eq_zero.mp hzero
  have h0 : (p - q).natDegree = 0 := by rw [hpq, Polynomial.natDegree_zero]
  omega

/-- If `p` and `q` have the same degree and *different* leading coefficients then `p - q` has the
same degree as `p`, with leading coefficient the difference. -/
private lemma psw_sub_eq_case {R : Type*} [Ring R] (p q : Polynomial R) (hpos : 0 < p.natDegree)
    (hdeg : p.natDegree = q.natDegree) (hlc : p.leadingCoeff ≠ q.leadingCoeff) :
    (p - q).natDegree = p.natDegree ∧ (p - q).leadingCoeff = p.leadingCoeff - q.leadingCoeff := by
  have hp : p ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega
  have hq : q ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hdeg; omega
  have hcoeff : (p - q).coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_natDegree, hdeg, Polynomial.coeff_natDegree]
    exact sub_ne_zero.mpr hlc
  have hle : (p - q).natDegree ≤ p.natDegree := by
    have h := Polynomial.natDegree_sub_le p q
    rw [max_eq_right hdeg.le] at h
    omega
  have hge : p.natDegree ≤ (p - q).natDegree := by
    by_contra hcon
    rw [not_le] at hcon
    exact hcoeff (Polynomial.coeff_eq_zero_of_natDegree_lt hcon)
  have hdeg' : (p - q).natDegree = p.natDegree := le_antisymm hle hge
  refine ⟨hdeg', ?_⟩
  rw [Polynomial.leadingCoeff_sub_of_degree_eq ?_ hlc]
  rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, hdeg]

/-- If `q` has strictly smaller degree than `p` then `p - q` has the degree and the leading
coefficient of `p`. -/
private lemma psw_sub_gt_case {R : Type*} [Ring R] (p q : Polynomial R)
    (hlt : q.natDegree < p.natDegree) :
    (p - q).natDegree = p.natDegree ∧ (p - q).leadingCoeff = p.leadingCoeff := by
  have hpq : p ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hlt; omega
  have hle : (p - q).natDegree ≤ p.natDegree := by
    have h := Polynomial.natDegree_sub_le p q
    rw [max_eq_left hlt.le] at h; exact h
  have hcoeff : (p - q).coeff p.natDegree = p.coeff p.natDegree := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hlt, sub_zero]
  have hne : (p - q).coeff p.natDegree ≠ 0 := by
    rw [hcoeff, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpq
  have hdeg : (p - q).natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hne
  refine ⟨hdeg, ?_⟩
  rw [← Polynomial.coeff_natDegree, hdeg]
  exact hcoeff

/-- `card (insert x A) = card (A \ {x}) + 1`: the elementary counting fact behind the decrease of
the weight at the critical degree. -/
private lemma psw_card_insert_erase {α : Type*} [DecidableEq α] (A : Finset α) (x : α) :
    (insert x A).card = (A.erase x).card + 1 := by
  by_cases hx : x ∈ A
  · rw [Finset.card_insert_of_mem hx, Finset.card_erase_add_one hx]
  · rw [Finset.card_insert_of_notMem hx, Finset.erase_eq_of_notMem hx]

/-! ## 2. The coefficient-ring extension `ren k` -/

/-- The coefficient-ring extension of the PET step: `MvPolynomial.rename Fin.castSucc`, sending the
`k` formal parameters introduced so far into the first `k` of the `k+1` parameters. -/
private noncomputable def ren (k : ℕ) : MvPolynomial (Fin k) ℤ →+* MvPolynomial (Fin (k+1)) ℤ :=
  (MvPolynomial.rename (Fin.castSucc : Fin k → Fin (k+1))).toRingHom

private lemma ren_injective (k : ℕ) : Function.Injective (ren k) := by
  intro x y h
  exact MvPolynomial.rename_injective (Fin.castSucc : Fin k → Fin (k+1))
    (Fin.castSucc_injective k) h

private lemma map_ren_natDegree (k : ℕ) (p : Polynomial (MvPolynomial (Fin k) ℤ)) :
    (p.map (ren k)).natDegree = p.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (ren_injective k) p

private lemma map_ren_leadingCoeff (k : ℕ) (p : Polynomial (MvPolynomial (Fin k) ℤ)) :
    (p.map (ren k)).leadingCoeff = ren k p.leadingCoeff :=
  Polynomial.leadingCoeff_map_of_injective (ren_injective k) p

/-! ## 3. The slot polynomial of a stepped symbolic state -/

/-- The polynomial carried by the slot `(i, ε)` of the state `S.step i₀`: it is
`(P i)(X + ε·t) - P i₀`, with all coefficients transported by `ren k`.  For `t = X (Fin.last k)`
this is the slot polynomial of the stepped state. -/
private noncomputable def pswStep (k : ℕ) (S : PetStateSym k) (i₀ : S.ι)
    (t : MvPolynomial (Fin (k+1)) ℤ) (j : S.ι × Bool) : Polynomial (MvPolynomial (Fin (k+1)) ℤ) :=
  ((S.P j.1).map (ren k)).comp (Polynomial.X + Polynomial.C (if j.2 then t else 0))
    - (S.P i₀).map (ren k)

private lemma pswStep_apply (k : ℕ) (S : PetStateSym k) (i₀ : S.ι)
    (t : MvPolynomial (Fin (k+1)) ℤ) (i : S.ι) (ε : Bool) :
    pswStep k S i₀ t (i, ε)
      = ((S.P i).map (ren k)).comp (Polynomial.X + Polynomial.C (if ε then t else 0))
          - (S.P i₀).map (ren k) := rfl

/-- The slot polynomial of `S.step i₀` is `pswStep` at the new formal parameter. -/
private lemma pswStep_eq_step (k : ℕ) (S : PetStateSym k) (i₀ : S.ι) (j : (S.step i₀).ι) :
    (S.step i₀).P j = pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1 := rfl

private lemma pswStep_comp_natDegree (k : ℕ) (S : PetStateSym k) (i : S.ι)
    (t : MvPolynomial (Fin (k+1)) ℤ) :
    (((S.P i).map (ren k)).comp (Polynomial.X + Polynomial.C t)).natDegree
      = (S.P i).natDegree := by
  rw [psw_comp_X_add_C_natDegree, map_ren_natDegree]

private lemma pswStep_comp_leadingCoeff (k : ℕ) (S : PetStateSym k) (i : S.ι)
    (t : MvPolynomial (Fin (k+1)) ℤ) :
    (((S.P i).map (ren k)).comp (Polynomial.X + Polynomial.C t)).leadingCoeff
      = ren k ((S.P i).leadingCoeff) := by
  rw [psw_comp_X_add_C_leadingCoeff, map_ren_leadingCoeff]

/-- Slots of degree strictly larger than `d'` keep their degree and leading coefficient. -/
private lemma pswStep_gt (k : ℕ) (S : PetStateSym k) (i₀ : S.ι) {d' : ℕ}
    (hi₀ : (S.P i₀).natDegree = d') (i : S.ι) (ε : Bool) (t : MvPolynomial (Fin (k+1)) ℤ)
    (hgt : d' < (S.P i).natDegree) :
    (pswStep k S i₀ t (i, ε)).natDegree = (S.P i).natDegree ∧
    (pswStep k S i₀ t (i, ε)).leadingCoeff = ren k ((S.P i).leadingCoeff) := by
  rw [pswStep_apply]
  have hlt : ((S.P i₀).map (ren k)).natDegree
      < (((S.P i).map (ren k)).comp
          (Polynomial.X + Polynomial.C (if ε then t else 0))).natDegree := by
    rw [pswStep_comp_natDegree, map_ren_natDegree, hi₀]
    exact hgt
  obtain ⟨h1, h2⟩ := psw_sub_gt_case (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))) ((S.P i₀).map (ren k)) hlt
  exact ⟨h1.trans (pswStep_comp_natDegree k S i (if ε then t else 0)),
    h2.trans (pswStep_comp_leadingCoeff k S i (if ε then t else 0))⟩

/-- Slots of degree exactly `d'` and with a leading coefficient different from `lc (P i₀)` keep
degree `d'`, and their leading coefficient loses `lc (P i₀)`. -/
private lemma pswStep_eq_of_lc_ne (k : ℕ) (S : PetStateSym k) (i₀ : S.ι) {d' : ℕ} (hd'1 : 1 ≤ d')
    (hi₀ : (S.P i₀).natDegree = d')
    (i : S.ι) (ε : Bool) (t : MvPolynomial (Fin (k+1)) ℤ)
    (heq : (S.P i).natDegree = d')
    (hlc : (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff) :
    (pswStep k S i₀ t (i, ε)).natDegree = d' ∧
    (pswStep k S i₀ t (i, ε)).leadingCoeff
      = ren k ((S.P i).leadingCoeff - (S.P i₀).leadingCoeff) := by
  rw [pswStep_apply]
  have hdegp : (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))).natDegree = d' := by
    rw [pswStep_comp_natDegree, heq]
  have hlcp : (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))).leadingCoeff
      = ren k ((S.P i).leadingCoeff) := pswStep_comp_leadingCoeff k S i (if ε then t else 0)
  have hlcne : (((S.P i).map (ren k)).comp
        (Polynomial.X + Polynomial.C (if ε then t else 0))).leadingCoeff
      ≠ ((S.P i₀).map (ren k)).leadingCoeff := by
    rw [hlcp, map_ren_leadingCoeff]
    intro hh
    exact hlc (ren_injective k hh)
  obtain ⟨h1, h2⟩ := psw_sub_eq_case (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))) ((S.P i₀).map (ren k))
      (by rw [hdegp]; omega) (by rw [hdegp, map_ren_natDegree, hi₀]) hlcne
  exact ⟨h1.trans hdegp, by rw [h2, hlcp, map_ren_leadingCoeff, map_sub]⟩

/-- A slot of degree `d'` and with the *same* leading coefficient as `P i₀` drops strictly below
`d'` (the leading terms cancel). -/
private lemma pswStep_lt_of_lc_eq (k : ℕ) (S : PetStateSym k) (i₀ : S.ι) {d' : ℕ} (hd'1 : 1 ≤ d')
    (hi₀ : (S.P i₀).natDegree = d')
    (i : S.ι) (ε : Bool) (t : MvPolynomial (Fin (k+1)) ℤ)
    (heq : (S.P i).natDegree = d')
    (hlc : (S.P i).leadingCoeff = (S.P i₀).leadingCoeff) :
    (pswStep k S i₀ t (i, ε)).natDegree < d' := by
  rw [pswStep_apply]
  have hpos : 0 < (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))).natDegree := by
    rw [pswStep_comp_natDegree, heq]; omega
  have hdegp : (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))).natDegree
      = ((S.P i₀).map (ren k)).natDegree := by
    rw [pswStep_comp_natDegree, heq, map_ren_natDegree, hi₀]
  have hlcp : (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))).leadingCoeff
      = ((S.P i₀).map (ren k)).leadingCoeff := by
    rw [pswStep_comp_leadingCoeff, map_ren_leadingCoeff, hlc]
  have h := psw_sub_lt_case (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))) ((S.P i₀).map (ren k))
      hpos hdegp hlcp
  rw [pswStep_comp_natDegree, heq] at h
  exact h

/-- If `natDegree (P i) ≤ d'` then the stepped slot has degree at most `d'`. -/
private lemma pswStep_le (k : ℕ) (S : PetStateSym k) (i₀ : S.ι) {d' : ℕ}
    (hi₀ : (S.P i₀).natDegree = d')
    (i : S.ι) (ε : Bool) (t : MvPolynomial (Fin (k+1)) ℤ)
    (hle : (S.P i).natDegree ≤ d') : (pswStep k S i₀ t (i, ε)).natDegree ≤ d' := by
  rw [pswStep_apply]
  have h := Polynomial.natDegree_sub_le (((S.P i).map (ren k)).comp
      (Polynomial.X + Polynomial.C (if ε then t else 0))) ((S.P i₀).map (ren k))
  rw [pswStep_comp_natDegree, map_ren_natDegree, hi₀] at h
  exact le_trans h (max_le hle le_rfl)

/-! ## 4. The weight-vector decrease -/

theorem petSymWeight {k : ℕ} (S : Work.Peluse.UControl.PetStep.PetStateSym k) (i₀ : S.ι)
    {d d' : ℕ}
    (hnc : ∀ i, 1 ≤ (S.P i).natDegree)
    (hd : ∀ i, (S.P i).natDegree ≤ d)
    (hd' : ∀ i, 1 ≤ (S.P i).natDegree → d' ≤ (S.P i).natDegree)
    (hi₀ : (S.P i₀).natDegree = d') :
    Work.Peluse.UControl.PetStep.petLt ((S.step i₀).weight d) (S.weight d) := by
  classical
  have hd'1 : 1 ≤ d' := by rw [← hi₀]; exact hnc i₀
  have hdle : d' ≤ d := by rw [← hi₀]; exact hd i₀
  refine ⟨⟨d', Nat.lt_succ_of_le hdle⟩, ?_, ?_⟩
  · change (((Finset.univ : Finset (S.step i₀).ι).filter
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).natDegree = d')).image
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).leadingCoeff)).card
      < (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d')).image
          (fun i => (S.P i).leadingCoeff)).card
    have hnew : (((Finset.univ : Finset (S.step i₀).ι).filter
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).natDegree = d')).image
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).leadingCoeff))
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => ren k ((S.P i).leadingCoeff - (S.P i₀).leadingCoeff))) := by
      refine Finset.ext fun y => ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hjd, hjl⟩
        obtain ⟨⟨i, ε⟩, hne⟩ := j
        have hjd' : (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) (i, ε)).natDegree = d' := hjd
        have hjl' : (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) (i, ε)).leadingCoeff = y := hjl
        rcases lt_or_eq_of_le (hd' i (hnc i)) with hgt | heq
        · exfalso
          have hk := (pswStep_gt k S i₀ hi₀ i ε (MvPolynomial.X (Fin.last k)) hgt).1
          rw [hk] at hjd'
          omega
        · by_cases hlceq : (S.P i).leadingCoeff = (S.P i₀).leadingCoeff
          · exfalso
            have hk := pswStep_lt_of_lc_eq k S i₀ hd'1 hi₀ i ε
              (MvPolynomial.X (Fin.last k)) heq.symm hlceq
            omega
          · have hk := pswStep_eq_of_lc_ne k S i₀ hd'1 hi₀ i ε
              (MvPolynomial.X (Fin.last k)) heq.symm hlceq
            have hnei : i ≠ i₀ := by
              intro hii
              exact hlceq (by rw [hii])
            exact ⟨i, ⟨heq.symm, hnei, hlceq⟩, hk.2.symm.trans hjl'⟩
      · rintro ⟨i, ⟨hid, hnei, hlcne⟩, hily⟩
        have hk := pswStep_eq_of_lc_ne k S i₀ hd'1 hi₀ i true
          (MvPolynomial.X (Fin.last k)) hid hlcne
        exact ⟨⟨(i, true), by simp⟩, hk.1, hk.2.trans hily⟩
    have hB1 : (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => ren k ((S.P i).leadingCoeff - (S.P i₀).leadingCoeff))).card
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => (S.P i).leadingCoeff - (S.P i₀).leadingCoeff)).card := by
      have key : ((((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
              (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
            (fun i => (S.P i).leadingCoeff - (S.P i₀).leadingCoeff)).image (ren k))
          = (((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
              (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
            (fun i => ren k ((S.P i).leadingCoeff - (S.P i₀).leadingCoeff))) :=
        Finset.image_image
      rw [← key]
      exact Finset.card_image_of_injective _ (ren_injective k)
    have hB2 : (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => (S.P i).leadingCoeff - (S.P i₀).leadingCoeff)).card
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => (S.P i).leadingCoeff)).card := by
      have key : ((((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
              (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
            (fun i => (S.P i).leadingCoeff)).image
            (fun y => y - (S.P i₀).leadingCoeff))
          = (((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
              (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
            (fun i => (S.P i).leadingCoeff - (S.P i₀).leadingCoeff)) :=
        Finset.image_image
      rw [← key]
      exact Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h)
    have hD : (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀ ∧
            (S.P i).leadingCoeff ≠ (S.P i₀).leadingCoeff)).image
          (fun i => (S.P i).leadingCoeff))
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀)).image
          (fun i => (S.P i).leadingCoeff)).erase ((S.P i₀).leadingCoeff) := by
      refine Finset.ext fun y => ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      constructor
      · rintro ⟨i, ⟨hid, hnei, hlcne⟩, hily⟩
        exact ⟨fun hy => hlcne (hily.trans hy), ⟨i, ⟨hid, hnei⟩, hily⟩⟩
      · rintro ⟨hne, i, ⟨hid, hnei⟩, hily⟩
        exact ⟨i, ⟨hid, hnei, fun h => hne (hily.symm.trans h)⟩, hily⟩
    have hOld : (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d')).image (fun i => (S.P i).leadingCoeff))
        = insert ((S.P i₀).leadingCoeff) (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀)).image
          (fun i => (S.P i).leadingCoeff)) := by
      refine Finset.ext fun y => ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨i, hid, hily⟩
        by_cases hi : i = i₀
        · rw [hi] at hily; exact Or.inl hily.symm
        · exact Or.inr ⟨i, ⟨hid, hi⟩, hily⟩
      · rintro (h | ⟨i, ⟨hid, hnei⟩, hily⟩)
        · exact ⟨i₀, hi₀, h.symm⟩
        · exact ⟨i, hid, hily⟩
    rw [hnew, hB1, hB2, hD, hOld]
    have harith := psw_card_insert_erase (((Finset.univ : Finset S.ι).filter
        (fun i => (S.P i).natDegree = d' ∧ i ≠ i₀)).image
        (fun i => (S.P i).leadingCoeff)) ((S.P i₀).leadingCoeff)
    omega
  · intro m hm
    have hm' : d' < (m : ℕ) := hm
    change (((Finset.univ : Finset (S.step i₀).ι).filter
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).natDegree
            = (m : ℕ))).image
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).leadingCoeff)).card
      = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = (m : ℕ))).image
          (fun i => (S.P i).leadingCoeff)).card
    have himg1 : (((Finset.univ : Finset (S.step i₀).ι).filter
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).natDegree
            = (m : ℕ))).image
          (fun j => (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) j.1).leadingCoeff))
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = (m : ℕ))).image
          (fun i => ren k ((S.P i).leadingCoeff))) := by
      refine Finset.ext fun y => ?_
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hjd, hjl⟩
        obtain ⟨⟨i, ε⟩, hne⟩ := j
        have hjd' : (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) (i, ε)).natDegree
            = (m : ℕ) := hjd
        have hjl' : (pswStep k S i₀ (MvPolynomial.X (Fin.last k)) (i, ε)).leadingCoeff = y := hjl
        rcases lt_or_eq_of_le (hd' i (hnc i)) with hgt | heq
        · have hk := pswStep_gt k S i₀ hi₀ i ε (MvPolynomial.X (Fin.last k)) hgt
          exact ⟨i, hk.1.symm.trans hjd', hk.2.symm.trans hjl'⟩
        · exfalso
          have hle2 := pswStep_le k S i₀ hi₀ i ε (MvPolynomial.X (Fin.last k))
            (le_of_eq heq.symm)
          omega
      · rintro ⟨i, hid, hil⟩
        have hgt : d' < (S.P i).natDegree := by rw [hid]; exact hm'
        have hk := pswStep_gt k S i₀ hi₀ i true (MvPolynomial.X (Fin.last k)) hgt
        exact ⟨⟨(i, true), by simp⟩, hk.1.trans hid, hk.2.trans hil⟩
    have himg2 : (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = (m : ℕ))).image
          (fun i => ren k ((S.P i).leadingCoeff))).card
        = (((Finset.univ : Finset S.ι).filter
          (fun i => (S.P i).natDegree = (m : ℕ))).image
          (fun i => (S.P i).leadingCoeff)).card := by
      have key : ((((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = (m : ℕ))).image
            (fun i => (S.P i).leadingCoeff)).image (ren k))
          = (((Finset.univ : Finset S.ι).filter
            (fun i => (S.P i).natDegree = (m : ℕ))).image
            (fun i => ren k ((S.P i).leadingCoeff))) :=
        Finset.image_image
      rw [← key]
      exact Finset.card_image_of_injective _ (ren_injective k)
    rw [himg1, himg2]

end Work.Peluse.UControl
