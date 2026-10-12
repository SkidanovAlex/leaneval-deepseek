import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotInt_measurable_bounded
import Submission.Work.BoseBoxFock.slotInt_peelMB
import Submission.Work.BoseBoxFock.slotProj1_idem_commMB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj_idem_and_comm` — the slot projections are idempotent and commute

The box ↔ Fock bridge of the FS chapter needs the *mode projection* `slotProj e S` to be a genuine
projection, with the projections of different slot sets commuting.  Both facts are consequences of
the single identity

`slotInt e S (slotInt e T Φ) = slotInt e (S ∪ T) Φ`  (`slotInt_comp`),

which says that projecting the slots of `T` and then those of `S` is projecting the slots of the
union (`slotInt` is `slotProj`, see `slotProj_eq_slotInt_fun`):
* idempotence is the case `T = S` (`S ∪ S = S`);
* commutation is the case `S ∪ T = T ∪ S`.

The composition law is proved by induction on `S`, the induction step being the *peel lemma*
`slotInt_peelMB` (`slotInt e (S ∪ {i}) Φ = slotProj1 e i (slotInt e S Φ)`, valid for measurable
bounded states) together with the *absorption* `slotProj1_slotInt_self`
(`i ∈ U → slotProj1 e i (slotInt e U Φ) = slotInt e U Φ`), which follows from the peel and the
idempotence of the single slot projection `slotProj1_idem_commMB`.

The results of `Submission.Work.BoseBoxFock.SlotProjAux` and of the three sibling modules
(`slotInt_peelMB`, `slotProj1_idem_commMB`, `slotInt_measurable_bounded`) are used here.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **Absorption of an already projected slot.**  If `i ∈ U` then projecting the slot `i` after the
slots of `U` changes nothing: the slot `i` of the union is simply projected twice. -/
theorem slotProj1_slotInt_self {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Finset ι} (Φ : (ι → Ω) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) {u : ι} (hu : u ∈ U) :
    slotProj1 e u (slotInt e U Φ) = slotInt e U Φ := by
  set U' := U.erase u with hU'
  have hU : U' ∪ {u} = U := by
    rw [hU', Finset.union_comm, ← Finset.insert_eq]
    exact Finset.insert_erase hu
  have hu' : u ∉ U' := by simp [hU']
  obtain ⟨hsm, hsb⟩ := slotInt_measurable_bounded e he hec U' Φ hΦm hΦb
  have hpeel : slotInt e U Φ = slotProj1 e u (slotInt e U' Φ) := by
    rw [← hU]; exact slotInt_peelMB e he hec hu' Φ hΦm hΦb
  rw [hpeel]
  exact (slotProj1_idem_commMB e he hec horth (slotInt e U' Φ) hsm hsb).1 u

/-- **The composition law of the slot projections.**  Projecting the slots of `T` and then those of
`S` is projecting the slots of `S ∪ T`. -/
theorem slotInt_comp {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : (ι → Ω) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    ∀ S T : Finset ι, slotInt e S (slotInt e T Φ) = slotInt e (S ∪ T) Φ := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro T; rw [Finset.empty_union, slotInt_empty]
  | insert u S' hu ih =>
    intro T
    have hins : insert u S' = S' ∪ {u} := by
      rw [Finset.insert_eq, Finset.union_comm]
    obtain ⟨hsm, hsb⟩ := slotInt_measurable_bounded e he hec T Φ hΦm hΦb
    rw [hins]
    -- peel the extra slot `u` off the outer projection
    rw [slotInt_peelMB e he hec hu (slotInt e T Φ) hsm hsb]
    rw [ih T]
    by_cases huT : u ∈ T
    · -- then `u` is already a slot of `S' ∪ T`, and the extra projection is absorbed
      have hset : (S' ∪ {u}) ∪ T = S' ∪ T := by
        rw [Finset.union_assoc, Finset.singleton_union, Finset.insert_eq_self.mpr huT]
      rw [hset]
      exact slotProj1_slotInt_self e he hec horth Φ hΦm hΦb (Finset.mem_union_right _ huT)
    · -- otherwise `(S' ∪ T) ∪ {u} = (S' ∪ {u}) ∪ T` and the peel applies in reverse
      have hnotin : u ∉ S' ∪ T := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hu, huT⟩
      have hset : (S' ∪ {u}) ∪ T = (S' ∪ T) ∪ {u} := by
        rw [Finset.union_assoc, Finset.union_comm {u} T, ← Finset.union_assoc]
      rw [hset, ← slotInt_peelMB e he hec hnotin Φ hΦm hΦb]

theorem slotProj_idem_and_comm {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S T : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    (∀ x, slotProj e S (slotProj e S Φ) x = slotProj e S Φ x) ∧
    (∀ x, slotProj e S (slotProj e T Φ) x = slotProj e T (slotProj e S Φ) x) := by
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hidem : slotInt e S (slotInt e S Φ) = slotInt e S Φ := by
    rw [slotInt_comp e he hec horth Φ hΦm hΦb S S, Finset.union_self]
  have hcomm : slotInt e S (slotInt e T Φ) = slotInt e T (slotInt e S Φ) := by
    rw [slotInt_comp e he hec horth Φ hΦm hΦb S T,
      slotInt_comp e he hec horth Φ hΦm hΦb T S, Finset.union_comm]
  constructor
  · intro x
    simp only [slotProj_eq_slotInt_fun]
    exact congrFun hidem x
  · intro x
    simp only [slotProj_eq_slotInt_fun]
    exact congrFun hcomm x

end Work.BoseBoxFock
