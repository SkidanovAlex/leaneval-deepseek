/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# What the ramification filtration determines

This file collects the statements in which the higher ramification filtration is used to *read
off* invariants of the extension `L/K` (`K`, `L` fields, `A : ValuationSubring L` a valuation ring
fixed by the decomposition subgroup, as in `Submission/Work/Ramification/Defs.lean`).

Three layers are distinguished, and only the first two are proved here:

1. **Formal consequences of the definition.**  The filtration determines the lower indices
   `g_i = #G_i = lowerIndex A i`, hence the Herbrand function `φ` (`herbrand`) and the break set
   (`LowerBreak`, `lowerBreak_iff_lowerIndex_lt` in the companion file), and the *upper* filtration
   is a function of the lower one (`upperRamificationSubgroup`).  The maximal tamely ramified
   subextension is the fixed field of `G_1`; for a tamely ramified extension the filtration is
   completely explicit: `φ(n) = 1 + (n-1)/g_0` for `n ≥ 1` and `0` is the only lower break
   (`IsTamelyRamified`, `ramificationSubgroup_eq_bot_of_tame`, `herbrand_of_tame`).

2. **Invariance of the filtration under isomorphisms of valued fields.**  An isomorphism
   `e : L ≃ₐ[K] L₂` carrying `A` onto `A₂` carries `G_i` onto `G_i`
   (`NK.Ramification.ramificationSubgroup_map_conj`), whence the lower indices `g_i` and the
   Herbrand function agree (`lowerIndex_eq_of_map_conj`, `herbrand_eq_of_map_conj`).  Thus the
   ramification filtration is an invariant of the valued field `(L, A)` over `K`, not of the
   chosen model — this is the *provable* half of the invariance required by the local
   Neukirch–Uchida theorem.

3. **The classical statement that the filtration, together with the residue data, determines the
   `p`-adic field `κ` from its absolute Galois group `G_κ`** — Neukirch, *Kennzeichnung der
   `p`-adischen und der endlich algebraischen Zahlkörper*, Invent. Math. **6** (1969); NSW
   (12.1.4)–(12.1.5).  This is *not* proved here: it requires the higher ramification filtration of
   the *infinite* level `Gal(κ̄/κ)` and its group-theoretic definability, i.e. the statement that
   the filtration of `Gal(κ̄/κ)` is an invariant of the abstract group `G_κ`.  The honest account is
   in `Submission/Work/Ramification/README.md`; the reduction that this workspace needs is in
   `Submission/Work/Ramification/Headline.lean`.
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.ramificationSubgroup_map_conj

open scoped Classical
open scoped Pointwise

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## Tamely ramified extensions -/

/-- **`L/K` is tamely ramified** (with respect to the valuation ring `A`) when the wild inertia
subgroup `G_1` is trivial, i.e. when the higher ramification filtration is concentrated at the
inertia subgroup `G_0`. -/
def IsTamelyRamified (A : ValuationSubring L) : Prop :=
  ramificationSubgroup (K := K) A 1 = ⊥

theorem isTamelyRamified_iff (A : ValuationSubring L) :
    IsTamelyRamified (K := K) A ↔ ramificationSubgroup (K := K) A 1 = ⊥ := Iff.rfl

/-- In a tamely ramified extension the filtration is trivial from level `1` on. -/
theorem ramificationSubgroup_eq_bot_of_tame (A : ValuationSubring L)
    (h : IsTamelyRamified (K := K) A) {i : ℕ} (hi : 1 ≤ i) :
    ramificationSubgroup (K := K) A i = ⊥ :=
  le_bot_iff.mp ((ramificationSubgroup_antitone A hi).trans_eq h)

/-- A subgroup of cardinality one is trivial. -/
theorem eq_bot_of_natCard_eq_one (A : ValuationSubring L) (H : Subgroup (A.decompositionSubgroup K))
    (h : Nat.card ↥H = 1) : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  haveI : Subsingleton ↥H := (Nat.card_eq_one_iff_unique.mp h).1
  have hx1 : (⟨x, hx⟩ : ↥H) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val hx1

/-- **In a tamely ramified extension the lower indices are explicit**: `g_0 = #I` and `g_i = 1`
for `i ≥ 1`. -/
theorem lowerIndex_eq_one_of_tame (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)]
    (h : IsTamelyRamified (K := K) A) {i : ℕ} (hi : 1 ≤ i) :
    lowerIndex (K := K) A i = 1 := by
  rw [lowerIndex, ramificationSubgroup_eq_bot_of_tame A h hi]
  exact Nat.card_unique

/-! ## The filtration determines the Herbrand function -/

/-- The Herbrand function is a function of the lower indices `g_i = lowerIndex A i`. -/
theorem herbrand_eq_of_lowerIndex_eq {L₂ : Type*} [Field L₂] [Algebra K L₂]
    (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (h : ∀ i, lowerIndex (K := K) A i = lowerIndex (K := K) A₂ i) (n : ℕ) :
    herbrand (K := K) A n = herbrand (K := K) A₂ n := by
  simp only [herbrand, h]

/-! ## Invariance under isomorphisms of valued fields -/

/-- **The lower indices are invariant under an isomorphism of valued fields.**  If `e : L ≃ₐ[K] L₂`
carries the valuation ring `A` onto `A₂`, then the ramification subgroups correspond under the
conjugation by `e` (`NK.Ramification.ramificationSubgroup_map_conj`), hence have the same
cardinality. -/
theorem lowerIndex_eq_of_map_conj {L₂ : Type*} [Field L₂] [Algebra K L₂]
    (A : ValuationSubring L) (A₂ : ValuationSubring L₂) (e : L ≃ₐ[K] L₂)
    (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂) (i : ℕ) :
    lowerIndex (K := K) A i = lowerIndex (K := K) A₂ i := by
  obtain ⟨φ, hφ⟩ := ramificationSubgroup_map_conj A A₂ e hA i
  rw [lowerIndex, lowerIndex]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨φ x.1, (hφ x.1).mp x.2⟩
      invFun := fun y => ⟨φ.symm y.1, (hφ (φ.symm y.1)).mpr (by
        rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

/-- **The Herbrand function is invariant under an isomorphism of valued fields.** -/
theorem herbrand_eq_of_map_conj {L₂ : Type*} [Field L₂] [Algebra K L₂]
    (A : ValuationSubring L) (A₂ : ValuationSubring L₂) (e : L ≃ₐ[K] L₂)
    (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂) (n : ℕ) :
    herbrand (K := K) A n = herbrand (K := K) A₂ n :=
  herbrand_eq_of_lowerIndex_eq A A₂ (fun i => lowerIndex_eq_of_map_conj A A₂ e hA i) n

end

end NK.Ramification
