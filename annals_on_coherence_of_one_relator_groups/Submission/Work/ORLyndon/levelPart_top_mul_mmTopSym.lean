import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.topPart_mul
import Submission.Work.ORLyndon.levelPart_rootVec_eq_base
import Submission.Work.ORLyndon.mapDomainRingHom_mmBaseHom_rootVec_eq
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero_mm
import Submission.Work.ORLyndon.mmTopSym_mem_relatorLetters

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- A decoration `j` occurring in the Magnus rewriting of `u` at the letter `x` is at most
`mmHi t u x`. -/
theorem mem_mmDecs_le_mmHi {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (x : {a : α // a ≠ t}) {j : ℤ} (hj : j ∈ Work.OROneRel.mmDecs t u x) :
    j ≤ Work.OROneRel.mmHi t u x := by
  classical
  rw [Work.OROneRel.mmHi, dif_pos ⟨j, hj⟩]
  exact Finset.le_max' _ _ hj

/-- A decoration strictly above `mmHi t u x` does not occur in the Magnus rewriting of `u` at
`x`. -/
theorem not_mem_mmDecs_of_mmHi_lt {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (x : {a : α // a ≠ t}) {j : ℤ} (hj : Work.OROneRel.mmHi t u x < j) :
    j ∉ Work.OROneRel.mmDecs t u x :=
  fun h => absurd (mem_mmDecs_le_mmHi t u x h) (not_le.mpr hj)

/-- The Fox derivative of the Magnus rewriting of `u` at the decorated letter `(x, j)` vanishes as
soon as the decoration `j` is strictly above `mmHi t u x`. -/
theorem foxD_magRewRel_eq_zero_of_mmHi_lt {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (x : {a : α // a ≠ t}) {j : ℤ}
    (hj : Work.OROneRel.mmHi t u x < j) :
    foxD (K := K) (X := MagnusBeta t) (((x, j)) : MagnusBeta t) (Work.OROneRel.magRewRel t u)
      = 0 :=
  foxD_eq_zero_of_notMem_relatorLetters _ _
    (fun hmem => not_mem_mmDecs_of_mmHi_lt t u x hj
      ((mem_relatorLetters_magRewRel_iff t u x j).mp hmem))

theorem levelPart_top_mul_mmTopSym {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) (he : Work.OROneRel.eps t u = 0)
    (x : α) (hxt : x ≠ t) (N : ℤ)
    (b : MonoidAlgebra K (OneRelatorGroup (u ^ l)))
    (hbN : ∀ g ∈ b.coeff.support,
      (levelOf t (u ^ l) u l rfl
        ((Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he) g).toAdd ≤ N)
    (hb : b * rootVec K (u ^ l) u x = 0) :
    levelPart t (u ^ l) u l rfl
        ((Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he) N b *
      MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
        (Work.ORLyndon.mmEpsPow t u l he))
        (rootVec K (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl)
          (mmTopSym t u l x hxt)) = 0 := by
  classical
  have hσ : Work.OROneRel.sigma t u = 1 :=
    (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he
  -- the top decoration of the letter `x` in the Magnus rewriting of `u ^ l`
  set i : ℤ := Work.OROneRel.mmHi t (u ^ l) ⟨x, hxt⟩ with hi
  -- the level bound: every level occurring in the root Fox vector is at most `i`
  have hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (((⟨x, hxt⟩ : {a : α // a ≠ t}), j))
        (Work.OROneRel.magRewRel t u) = 0 := by
    intro j hj
    refine foxD_magRewRel_eq_zero_of_mmHi_lt (K := K) t u ⟨x, hxt⟩ ?_
    rw [← Work.OROneRel.mmHi_pow t u hcyc he l hl ⟨x, hxt⟩, ← hi]
    exact hj
  have hDbound : ∀ g ∈ (rootVec K (u ^ l) u x).coeff.support,
      (levelOf t (u ^ l) u l rfl hσ g).toAdd ≤ i :=
    level_le_of_foxD_eq_zero (K := K) (t := t) (r := u ^ l) (u := u) (l := l) (hpow := rfl)
      (hσ := hσ) hxt hdec
  -- the top level part of the product `b * (∂u/∂x)` vanishes
  have htop := topPart_mul (t := t) (r := u ^ l) (u := u) (l := l) (hpow := rfl) (hσ := hσ)
    (a := b) (b := rootVec K (u ^ l) u x) (N := N) (M := i) hbN hDbound
  rw [hb, levelPart_zero] at htop
  rw [levelPart_rootVec_eq_base t x hxt (u ^ l) u l rfl hσ i] at htop
  -- the top level part of the root Fox vector is the pushed forward base Fox derivative
  have hX : MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.mmBaseHom (t := t) (r := u ^ l)
      (Work.ORLyndon.mmEpsPow t u l he))
      (rootVec K (Work.OROneRel.mmW t (u ^ l)) (Work.OROneRel.rootW t u l hcyc he hl)
        (mmTopSym t u l x hxt)) =
      MonoidAlgebra.mapDomainRingHom K ((presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := MagnusBeta t) (((⟨x, hxt⟩ : {a : α // a ≠ t}), i))
          (Work.OROneRel.magRewRel t u)) := by
    rw [mapDomainRingHom_mmBaseHom_rootVec_eq (K := K) t u l hcyc he hl (mmTopSym t u l x hxt),
      mmTopSym_val, hi]
  rw [hX]
  -- cancel the unit `τ ^ i`
  have hτ : MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        ((presentRho (u ^ l) (FreeGroup.of t)) ^ i) *
      MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        (((presentRho (u ^ l) (FreeGroup.of t)) ^ i))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hAE : (levelPart t (u ^ l) u l rfl hσ N b *
      MonoidAlgebra.mapDomainRingHom K ((presentRho (u ^ l)).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := MagnusBeta t) (((⟨x, hxt⟩ : {a : α // a ≠ t}), i))
          (Work.OROneRel.magRewRel t u))) *
      MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        ((presentRho (u ^ l) (FreeGroup.of t)) ^ i) = 0 := by
    rw [mul_assoc]
    exact htop
  have h3 := congrArg (fun z => z * MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        (((presentRho (u ^ l) (FreeGroup.of t)) ^ i))⁻¹) hAE
  rw [mul_assoc, hτ, mul_one, zero_mul] at h3
  exact h3

end Work.ORLyndon
