import Mathlib
import Submission.Work.DSM5b.H0Defs

universe a

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-!
# `HCd` is a differential

`HCd t m : HCX t m →ₗ[R] HCX t (m+1)` is the alternating coface map of the honest chart Čech
complex in coordinates (`Submission/Work/DSM5b/H0Defs.lean`):

`(HCd t m z) τ = ∑ i : Fin (m+2), (-1)^i • rhoH t (tupRng_del_subset i τ) (z (tupDel i τ))`.

This file proves `HCd t (m+1) ∘ HCd t m = 0` (`Work.DSM5b.HCd_comp`).

The proof is the standard cosimplicial computation, made explicit on the index pair
`(i, j) : Fin (m+3) × Fin (m+2)` of "outer" and "inner" deleted coordinate.  The term indexed by
`(i, j)` is a scalar `(-1)^{i+j}` times the value of `z` at the tuple obtained from `τ` by deleting
the two positions; by `tupDel_tupDel` the *same* tuple (and the *same* canonical restriction) is
obtained from the pair `(i.succAbove j, j.predAbove i)`, and the map

`(i, j) ↦ (i.succAbove j, j.predAbove i)`

is a fixed point free involution of the index set (`Fin.succAbove_succAbove_predAbove`,
`Fin.predAbove_predAbove_succAbove`, `Fin.succAbove_ne`) whose two exponents add up to an odd
number.  Hence the double sum splits into cancelling pairs (`Finset.sum_involution`).

Note: this is *not* the frozen `DSMap.Mix2.area_M5b`; it is elementary bookkeeping on the explicit
coordinates.
-/

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- Proof irrelevance for the restriction maps `rhoH` between chart rings. -/
lemma HCd_rhoH_congr {t : ι → R} {S T : Finset ι} {h h' : S ⊆ T} (x : chartRing t S) :
    rhoH t h x = rhoH t h' x :=
  Subtype.ext (DFunLike.congr_fun (locRes_eq t h' (locRes t h)) x.1)

/-- Restriction maps between chart rings compose. -/
lemma HCd_rhoH_comp {t : ι → R} {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V)
    (x : chartRing t S) : rhoH t h₂ (rhoH t h₁ x) = rhoH t (h₁.trans h₂) x :=
  Subtype.ext (DFunLike.congr_fun (locRes_eq t (h₁.trans h₂)
    ((locRes t h₂).comp (locRes t h₁))) x.1)

omit [DecidableEq ι] in
/-- Deleting two coordinates in the two possible orders: the cosimplicial identity
`δ^{j} δ^{i} = δ^{i.succAbove j} δ^{j.predAbove i}` in the coordinates used by `HCd`. -/
lemma HCd_tupDel_swap {m : ℕ} (i : Fin (m + 3)) (j : Fin (m + 2)) (τ : Fin (m + 3) → ι) :
    tupDel j (tupDel i τ) = tupDel (j.predAbove i) (tupDel (i.succAbove j) τ) := by
  funext k
  simp only [tupDel_apply]
  exact congrArg τ (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

/-- The restriction of `z` to the component indexed by a tuple does not depend on how that tuple is
presented: if `A = B` then the two canonical restrictions to `S` agree. -/
lemma HCd_rhoH_del_congr {t : ι → R} {m : ℕ} {S : Finset ι} {A B : Fin (m + 1) → ι}
    (hAB : A = B) (z : HCX t m) {hA : tupRng A ⊆ S} {hB : tupRng B ⊆ S} :
    rhoH t hA (z A) = rhoH t hB (z B) := by
  cases hAB
  exact Subtype.ext (DFunLike.congr_fun (locRes_eq t _ (locRes t _)) (z A).1)

/-- The two exponents of a cancelling pair have opposite parity: they add up to an odd number. -/
lemma HCd_sign_pair {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (-1 : R) ^ ((i : ℕ) + (j : ℕ)) +
      (-1 : R) ^ (((i.succAbove j : Fin (n + 1)) : ℕ) + ((j.predAbove i : Fin n) : ℕ)) = 0 := by
  rcases lt_or_ge j.castSucc i with h | h
  · have hs : ((i.succAbove j : Fin (n + 1)) : ℕ) = (j : ℕ) := by
      rw [Fin.succAbove_of_castSucc_lt i j h]; rfl
    have hp : ((j.predAbove i : Fin n) : ℕ) = (i : ℕ) - 1 := by
      rw [Fin.predAbove_of_castSucc_lt j i h, Fin.val_pred]
    rw [hs, hp]
    have hb : ((j : ℕ) + ((i : ℕ) - 1)) + 1 = (i : ℕ) + (j : ℕ) := by
      have : (j : ℕ) < (i : ℕ) := h
      omega
    rw [← hb, pow_succ]
    ring
  · have hs : ((i.succAbove j : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by
      rw [Fin.succAbove_of_le_castSucc i j h, Fin.val_succ]
    have hp : ((j.predAbove i : Fin n) : ℕ) = (i : ℕ) := by
      rw [Fin.predAbove_of_le_castSucc j i h, Fin.coe_castPred]
    rw [hs, hp]
    have hb : (j : ℕ) + 1 + (i : ℕ) = (i : ℕ) + (j : ℕ) + 1 := by omega
    rw [hb, pow_succ]
    ring

/-- The summand of the double sum `∑_i ∑_j ...`, indexed by a pair of deleted coordinates. -/
noncomputable def HCd_hdTerm (t : ι → R) {m : ℕ} (τ : Fin (m + 3) → ι) (z : HCX t m)
    (p : Fin (m + 3) × Fin (m + 2)) : chartRing t (tupRng τ) :=
  (-1 : R) ^ ((p.1 : ℕ) + (p.2 : ℕ)) •
    rhoH t ((tupRng_del_subset p.2 (tupDel p.1 τ)).trans (tupRng_del_subset p.1 τ))
      (z (tupDel p.2 (tupDel p.1 τ)))

/-- The value of the summand is insensitive to the order in which the two coordinates are deleted. -/
lemma HCd_hdTerm_eq (t : ι → R) {m : ℕ} (τ : Fin (m + 3) → ι) (z : HCX t m)
    (i : Fin (m + 3)) (j : Fin (m + 2)) :
    rhoH t ((tupRng_del_subset j (tupDel i τ)).trans (tupRng_del_subset i τ))
        (z (tupDel j (tupDel i τ)))
      = rhoH t ((tupRng_del_subset (j.predAbove i) (tupDel (i.succAbove j) τ)).trans
          (tupRng_del_subset (i.succAbove j) τ))
          (z (tupDel (j.predAbove i) (tupDel (i.succAbove j) τ))) :=
  HCd_rhoH_del_congr (HCd_tupDel_swap i j τ) z

theorem HCd_comp {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (m : ℕ) : (HCd t (m + 1)).comp (HCd t m) = 0 := by
  classical
  apply LinearMap.ext
  intro z
  funext τ
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [HCd_apply]
  -- expand the inner differential and absorb the outer scalar
  have hinner : ∀ i : Fin (m + 3),
      rhoH t (tupRng_del_subset i τ) (HCd t m z (tupDel i τ))
        = ∑ j : Fin (m + 2), (-1 : R) ^ (j : ℕ) •
            rhoH t ((tupRng_del_subset j (tupDel i τ)).trans (tupRng_del_subset i τ))
              (z (tupDel j (tupDel i τ))) := by
    intro i
    rw [HCd_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, HCd_rhoH_comp (t := t) (tupRng_del_subset j (tupDel i τ))
      (tupRng_del_subset i τ) (z (tupDel j (tupDel i τ)))]
  trans ∑ i : Fin (m + 3), ∑ j : Fin (m + 2), HCd_hdTerm t τ z (i, j)
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinner i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_smul, ← pow_add]
    simp only [HCd_hdTerm]
  · -- the double sum is an alternating sum over an involution and its index pairs cancel
    rw [← Fintype.sum_prod_type]
    refine Finset.sum_involution (s := (Finset.univ : Finset (Fin (m + 3) × Fin (m + 2))))
      (g := fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ -
      show HCd_hdTerm t τ z (i, j) + HCd_hdTerm t τ z (i.succAbove j, j.predAbove i) = 0
      simp only [HCd_hdTerm]
      rw [HCd_hdTerm_eq t τ z i j]
      rw [← add_smul, HCd_sign_pair (R := R) i j, zero_smul]
    · rintro ⟨i, j⟩ - _ h
      exact Fin.succAbove_ne i j (congrArg Prod.fst h)
    · intro p _
      exact Finset.mem_univ _
    · rintro ⟨i, j⟩ -
      show ((i.succAbove j).succAbove (j.predAbove i), (j.predAbove i).predAbove (i.succAbove j))
        = (i, j)
      rw [Fin.succAbove_succAbove_predAbove i j, Fin.predAbove_predAbove_succAbove i j]

end Work.DSM5b
