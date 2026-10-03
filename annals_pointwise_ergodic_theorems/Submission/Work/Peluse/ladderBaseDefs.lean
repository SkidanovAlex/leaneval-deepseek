import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily
import Submission.Work.Peluse.ladderA_defs
import Submission.Work.Peluse.Prop36SW.cardSlotSetOne

/-!
# The base definitions of Peluse's §5 support chain (moved out of the node file)

This module holds the `D`-specific *definitions and bookkeeping lemmas* that the §5 chain uses
(`slotCoeff` and its family identity, the flattening of the parameter family, the appending map
`splitUpd` and its box Fubini `parBox_succ_average`).  They were originally in the node file
`Submission/Work/Peluse/prop36SW_of_ladderA.lean`; they live here so that the chain's modules can
import them **without** importing the node file (which would be a cycle, since the node file
assembles the chain).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl

/-- The direction coefficient of the slot `s ∈ S (j+1)` in the recursion of `IdxDatum.dir`:
`dir (j+1) ω a = ∑_{s ∈ ω} (slotCoeff D d c j s a) · a_{j+1,s}`, where
`slotCoeff D d c j s a = (d - j) · dir D d c j (par j s) a`.  This is the `p`-datum of
`PeluseLadderA` for the "support chain". -/
def slotCoeff (D : IdxDatum) (d : ℕ) (c : ℤ) (j : ℕ) (s : D.S (j + 1))
    (a : (j' : ℕ) → D.S j' → ℤ) : ℤ :=
  ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s) a

/-- **The family identity.**  The level-`(j+1)` direction of `ω` is the sum over the slots of `ω` of
the slot coefficients times the level-`(j+1)` parameters: this is the exact shape of the hypothesis
of `PeluseLadderA` (`pDir`), and it is what makes the "support chain" step an identity. -/
theorem dir_succ_eq_sum_slotCoeff (D : IdxDatum) (d : ℕ) (c : ℤ) (j : ℕ) (ω : D.I (j + 1))
    (a : (j' : ℕ) → D.S j' → ℤ) :
    D.dir d c (j + 1) ω a = ∑ s ∈ ω.1, slotCoeff D d c j s a * a (j + 1) s := rfl

/-- The box the ladder's hypothesis averages over is the box of parameters with `|a| < H`: the
restricted parameter box `Ioo (-H) H` on the slots. -/
theorem paramBox_eq_piFinset (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (H : ℕ) :
    paramBox (k := k) H
      = Fintype.piFinset (fun _ : Slot ι k => Finset.Ioo (-(H : ℤ)) (H : ℤ)) := rfl

/-! ## The support chain: state and step -/

/-- **The proper-subset collapse** (the combinatorial heart of `chainStep`).

If the multiplicity function `kω` of `PeluseLadderA` is supported on the *full* subset `univ`, then
every subset occurring in the conclusion's index type `ConclIdx s₀ kω t'` — which by definition omits
`s₀`, hence is a *proper* subset of `univ` — carries multiplicity `0`.  So `Fin (kω ω)` is `Fin 0`,
the `Sum.inr` part of `ConclIdx s₀ kω t'` is empty, and the conclusion of the ladder has **no short
directions**: it is already a uniformity-norm power at the new level `t'`. -/
theorem kω_eq_zero_of_proper {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ}
    (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (hkω : ∀ ω : SlotSet ι k, ω.1 ≠ Finset.univ → kω ω = 0) :
    ∀ ω : {s : Finset (Slot ι k) // s.Nonempty ∧ s₀ ∉ s}, kω ⟨ω.1, ω.2.1⟩ = 0 := by
  intro ω
  refine hkω ⟨ω.1, ω.2.1⟩ (fun h => ?_)
  exact ω.2.2 (h.symm ▸ Finset.mem_univ s₀)

/-- **The conclusion's level collapses to `t'`.**  With `kω` supported on `univ` as above, the index
type of the ladder's conclusion has exactly `t'` elements, so the conclusion's box-norm level is
`t'` — the level of the uniformity norm produced by the step. -/
theorem card_conclIdx_eq {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ}
    (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) (t' : ℕ)
    (hkω : ∀ ω : SlotSet ι k, ω.1 ≠ Finset.univ → kω ω = 0) :
    Fintype.card (ConclIdx s₀ kω t') = t' := by
  have hzero : Fintype.card
      (Σ ω : {s : Finset (Slot ι k) // s.Nonempty ∧ s₀ ∉ s}, Fin (kω ⟨ω.1, ω.2.1⟩)) = 0 := by
    rw [Fintype.card_sigma]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [kω_eq_zero_of_proper kω s₀ hkω ω]
    simp
  simp only [ConclIdx, Fintype.card_sum, hzero, add_zero, Fintype.card_fin]

/-- **The flattening of the index family** (the `p`-datum's parameter type).

The ladder's `p` is a function of a `(Fin n → ℤ)`-tuple, while the chain's "old parameters" at
level `ℓ + 1` are the parameters of the levels `≤ ℓ`, i.e. `D.Idx (ℓ + 1)
= (j : Fin (ℓ + 1)) → D.S j → ℤ`.  This is exactly the currying of the slot type
`Σ j : Fin (ℓ + 1), D.S j`, followed by `Fintype.equivFin`; it is the only bookkeeping the
instantiation of `PeluseLadderA` in `chainStep` needs for the parameter type. -/
noncomputable def idxFlat (D : IdxDatum) (ℓ : ℕ) :
    D.Idx (ℓ + 1) ≃ (Fin (Fintype.card (Σ j : Fin (ℓ + 1), D.S j)) → ℤ) :=
  (Equiv.piCurry (γ := fun (_ : Fin (ℓ + 1)) (_ : D.S _) => ℤ)).symm.trans
    (Equiv.arrowCongr (Fintype.equivFin (Σ j : Fin (ℓ + 1), D.S j)) (Equiv.refl ℤ))

/-- The ladder's parameter type for the chain at level `ℓ` (the "old parameters", i.e. the levels
`≤ ℓ`, flattened): the domain of the `p`-datum below. -/
abbrev ChainParam (D : IdxDatum) (ℓ : ℕ) : Type :=
  Fin (Fintype.card (Σ j : Fin (ℓ + 1), D.S j)) → ℤ

/-- **The `p`-datum of the chain.**  For the slot `s` of the support `i ∈ I (ℓ+1)`, the coefficient
`Λ · slotCoeff D d c ℓ s a = Λ · (d - ℓ) · dir ℓ (par ℓ s) a` — so that on the *full* subset of the
slots the ladder's hypothesis is, by `dir_succ_eq_sum_slotCoeff`, literally
`Λ · dir (ℓ+1) i (a, a')`: the manufactured-hypothesis identity. -/
noncomputable def chainP (D : IdxDatum) (d : ℕ) (c : ℤ) {ℓ : ℕ} (i : D.I (ℓ + 1)) (Λ : ℕ)
    (s : ↥i.1) (a : ChainParam D ℓ) : ℤ :=
  (Λ : ℤ) * slotCoeff D d c ℓ (s : D.S (ℓ + 1)) (D.pad (ℓ + 1) ((idxFlat D ℓ).symm a))

/-- The slot type of the chain datum at the support `i ∈ I (ℓ+1)`: `ι := ↥i.1` with `k := fun _ => 1`.
So the ladder's slots are the slots of the support, each carrying the junk index `Fin 1`. -/
abbrev ChainSlot {D : IdxDatum} {ℓ : ℕ} (i : D.I (ℓ + 1)) : Type := Slot (↥i.1) (fun _ => 1)

/-- **The joint parameter family** of the chain step: the ladder's "old parameters" `a` (the levels
`≤ ℓ`, flattened by `idxFlat`) together with its "new parameters" `a'`, read as the level-`(ℓ+1)`
parameters of the slots of the support `i`.  This is the family `A` for which
`dir_succ_eq_sum_slotCoeff` turns the ladder's hypothesis into the current direction
`Λ · dir (ℓ+1) i A`. -/
noncomputable def chainParamJoint (D : IdxDatum) {ℓ : ℕ} (i : D.I (ℓ + 1))
    (a : ChainParam D ℓ) (a' : ChainSlot i → ℤ) (j' : ℕ) (s : D.S j') : ℤ :=
  if h : j' = ℓ + 1 then
    (if hs : (h ▸ s : D.S (ℓ + 1)) ∈ i.1 then a' ⟨⟨_, hs⟩, 0⟩ else 0)
  else D.pad (ℓ + 1) ((idxFlat D ℓ).symm a) j' s

/-- Off the peeled level, the joint family is the ladder's old parameters. -/
lemma chainParamJoint_of_ne {D : IdxDatum} {ℓ : ℕ} {i : D.I (ℓ + 1)} {a : ChainParam D ℓ}
    {a' : ChainSlot i → ℤ} {j' : ℕ} (hj : j' ≠ ℓ + 1) (s : D.S j') :
    chainParamJoint D i a a' j' s = D.pad (ℓ + 1) ((idxFlat D ℓ).symm a) j' s := by
  rw [chainParamJoint, dif_neg hj]

/-- On the peeled level and on the support, the joint family is the ladder's new parameter. -/
lemma chainParamJoint_at {D : IdxDatum} {ℓ : ℕ} {i : D.I (ℓ + 1)} {a : ChainParam D ℓ}
    {a' : ChainSlot i → ℤ} {s : D.S (ℓ + 1)} (hs : s ∈ i.1) :
    chainParamJoint D i a a' (ℓ + 1) s = a' ⟨⟨s, hs⟩, 0⟩ := by
  rw [chainParamJoint, dif_pos rfl, dif_pos hs]

/-- **`dir` depends only on the parameters of the levels `≤ j`.**  This is what lets the chain step
identify the ladder's old parameters (the levels `≤ ℓ`) with the joint family, whose values at the
level `ℓ+1` are the ladder's new parameters. -/
theorem dir_congr (D : IdxDatum) (l : ℕ) (c : ℤ) : ∀ (j : ℕ) (i : D.I j)
    (a b : (j' : ℕ) → D.S j' → ℤ),
    (∀ j' ≤ j, ∀ s : D.S j', a j' s = b j' s) → D.dir l c j i a = D.dir l c j i b := by
  intro j
  induction j with
  | zero => intro i a b _; rfl
  | succ j ih =>
      intro i a b h
      simp only [IdxDatum.dir]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ih (D.par j s) a b (fun j' hj' s' => h j' (by omega) s'), h (j + 1) le_rfl s]

/-- The parameter family obtained from `al : D.Idx (ℓ+1)` (the levels `≤ ℓ`) by overwriting the
level-`(ℓ+1)` coordinates by `s`: the "split off the top level" of the Fubini between the state's box
`D.parBox (ℓ+2) M` and the ladder's two-box average `A × paramBox`. -/
noncomputable def padUpdate (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ) :
    (j' : ℕ) → D.S j' → ℤ :=
  fun j' t => if h : j' = ℓ + 1 then s (h ▸ t) else D.pad (ℓ + 1) al j' t

/-- **The restricted congruence for `dir` at the peeled level.**  The level-`(ℓ+1)` direction of the
support `i` depends only on the parameters of the levels `≤ ℓ` and on the level-`(ℓ+1)` parameters *of
the slots of `i`*: the level-`(ℓ+1)` parameters of the other slots are irrelevant.  This is what makes
the average over the state's box `D.parBox (ℓ+2) M` collapse onto the ladder's two-box average (the
junk coordinates average out). -/
theorem dir_succ_congr_of_eq_on (D : IdxDatum) (d : ℕ) (c : ℤ) {ℓ : ℕ} (i : D.I (ℓ + 1))
    {a b : (j' : ℕ) → D.S j' → ℤ}
    (hlo : ∀ j' ≤ ℓ, ∀ s : D.S j', a j' s = b j' s)
    (hi : ∀ s ∈ i.1, a (ℓ + 1) s = b (ℓ + 1) s) :
    D.dir d c (ℓ + 1) i a = D.dir d c (ℓ + 1) i b := by
  rw [dir_succ_eq_sum_slotCoeff D d c ℓ i a, dir_succ_eq_sum_slotCoeff D d c ℓ i b]
  simp only [slotCoeff]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [dir_congr D d c ℓ (D.par ℓ s) a b (fun j' hj' s' => hlo j' hj' s'), hi s hs]

/-- **The manufactured-hypothesis identity.**  On the *full* subset of the slots, the ladder's
hypothesis family for the chain datum is the current direction: the sum of the slot coefficients times
the new parameters is `Λ · dir (ℓ+1) i A` for the joint family `A = chainParamJoint D i a a'`.  This is
the identity that makes `chainStep`'s ladder hypothesis *equal* the state (no loss). -/
theorem chainP_sum_univ (D : IdxDatum) (d : ℕ) (c : ℤ) {ℓ : ℕ} (i : D.I (ℓ + 1)) (Λ : ℕ)
    (a : ChainParam D ℓ) (a' : ChainSlot i → ℤ) :
    (∑ s : ChainSlot i, chainP D d c i Λ s.1 a * a' s)
      = (Λ : ℤ) * D.dir d c (ℓ + 1) i (chainParamJoint D i a a') := by
  rw [dir_succ_eq_sum_slotCoeff D d c ℓ i (chainParamJoint D i a a'), Finset.mul_sum]
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_attach (s := i.1), Finset.attach_eq_univ]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Fin.sum_univ_one, chainParamJoint_at s'.2, chainP]
  rw [slotCoeff, slotCoeff,
    dir_congr D d c ℓ (D.par ℓ (↑s')) _ _
      (fun j' hj' s'' => chainParamJoint_of_ne (by omega) s'')]
  ring

/-- **The multiplicity function of the chain datum** (the "manufactured hypothesis"): all the weight
`m` is on the *full* subset of the slots and `0` elsewhere.  This is what makes the ladder's
hypothesis the current uniformity-norm power (`m` copies of the direction of the full subset, which
by `dir_succ_eq_sum_slotCoeff` is literally `Λ · dir ℓ i a`) and what makes the conclusion carry no
short directions (`kω_eq_zero_of_proper`). -/
def chainKω {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (m : ℕ) : SlotSet ι k → ℕ :=
  fun ω => if ω.1 = Finset.univ then m else 0

/-- `chainKω` vanishes off the full subset — the hypothesis of the proper-subset collapse. -/
theorem chainKω_eq_zero_of_ne_univ {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (m : ℕ)
    (ω : SlotSet ι k) (hω : ω.1 ≠ Finset.univ) : chainKω (k := k) m ω = 0 := by
  simp only [chainKω, if_neg hω]

/-- **The conclusion of the ladder applied to the chain datum is already a uniformity norm.**  With
`chainKω`, the conclusion's index type has exactly `t'` elements and every short direction has
multiplicity `0`: this is the "no short directions" half of `chainStep`, packaged for the datum. -/
theorem card_conclIdx_chainKω {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (m : ℕ)
    (s₀ : Slot ι k) (t' : ℕ) :
    Fintype.card (ConclIdx s₀ (chainKω (k := k) m) t') = t' :=
  card_conclIdx_eq _ _ _ (fun ω hω => chainKω_eq_zero_of_ne_univ m ω hω)

/-! ### The cardinality of the family index sets

The family index `D.I j` (nonempty subsets of the level-`j` slots) and the ladder's index type
`FamIdx kω` for `kω ≡ 1` on the slot set `D.S j` (with `k ≡ 1`) have the same cardinality
`2 ^ card (D.S j) - 1`: this is the *level* of Peluse's Proposition 3.4/3.6.  The identification of
the two families (needed to read `D.famNorm` as the ladder's hypothesis) is `sumSlotDir` together
with `Prop36SW.existsSlotSetEquivI`. -/

/-- The level-`j` family index `D.I j` has `2 ^ card (D.S j) - 1` elements. -/
lemma card_I (D : IdxDatum) (j : ℕ) :
    Fintype.card (D.I j) = 2 ^ Fintype.card (D.S j) - 1 := by
  obtain ⟨⟨e⟩, hcard, -⟩ := Prop36SW.cardSlotSetOne (D.S j)
  rw [← hcard]
  exact (Fintype.card_congr e).symm

/-- The ladder's family index for `k ≡ 1` on `D.S j` and `kω ≡ 1` has `2 ^ card (D.S j) - 1`
elements. -/
lemma card_famIdx_one (D : IdxDatum) (j : ℕ) :
    Fintype.card (FamIdx (k := fun _ : D.S j => 1)
      (fun _ : SlotSet (D.S j) (fun _ => 1) => 1)) = 2 ^ Fintype.card (D.S j) - 1 :=
  (Prop36SW.cardSlotSetOne (D.S j)).2.2

/-- The two family index sets of a level of Peluse's chain have the same cardinality. -/
lemma card_famIdx_eq_cardI (D : IdxDatum) (j : ℕ) :
    Fintype.card (FamIdx (k := fun _ : D.S j => 1)
      (fun _ : SlotSet (D.S j) (fun _ => 1) => 1)) = Fintype.card (D.I j) := by
  rw [card_famIdx_one, card_I]


/-! ## Splitting a parameter family at the peeled level

The state in the corrected chain below averages over the closed parameter box `D.parBox (ℓ+2) M` of
the levels `0,…,ℓ+1`.  The ladder applied at the peeled level `ℓ+1` averages over its "old
parameters" `D.parBox (ℓ+1) M` (the levels `0,…,ℓ`) and its "new parameters"
`paramBox (k := k) (M+1)` (the level-`(ℓ+1)` coordinates of the slots, each in
`Ioo (-(M+1)) (M+1) = [-M,M]`).  The two averages agree, by the card-splitting identity below: the
*closed* box `[-M,M]` is exactly the ladder's `paramBox (k := k) (M+1)`, so no shrinking occurs at
this step (contrary to the earlier reading of `parBoxMixed`, whose second factor was `Ioo (-M) M`).
-/

/-- Append the level-`(ℓ+1)` coordinates `s` to the lower ones `al`. -/
abbrev splitUpd (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ) : D.Idx (ℓ + 2) :=
  Fin.snoc al s

/-- The pair of a level-`(ℓ+2)` family: the lower coordinates and the level-`(ℓ+1)` coordinates. -/
abbrev idxSplit (D : IdxDatum) (ℓ : ℕ) (a : D.Idx (ℓ + 2)) :
    D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) :=
  (Fin.init a, a (Fin.last (ℓ + 1)))

lemma idxSplit_splitUpd (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ) :
    idxSplit D ℓ (splitUpd D ℓ al s) = (al, s) := by
  simp only [idxSplit, splitUpd, Fin.init_snoc, Fin.snoc_last]

lemma splitUpd_idxSplit (D : IdxDatum) (ℓ : ℕ) (a : D.Idx (ℓ + 2)) :
    splitUpd D ℓ (idxSplit D ℓ a).1 (idxSplit D ℓ a).2 = a := by
  simp only [idxSplit, splitUpd, Fin.snoc_init_self]

lemma splitUpd_injective (D : IdxDatum) (ℓ : ℕ) :
    Function.Injective (fun p : D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) =>
      splitUpd D ℓ p.1 p.2) := by
  intro p q h
  have := congrArg (idxSplit D ℓ) h
  simp only [idxSplit_splitUpd] at this
  exact this

lemma splitUpd_at {D : IdxDatum} {ℓ : ℕ} {al : D.Idx (ℓ + 1)} {s : D.S (ℓ + 1) → ℤ}
    (t : D.S (ℓ + 1)) : splitUpd D ℓ al s (Fin.last (ℓ + 1)) t = s t := by
  simp only [splitUpd, Fin.snoc_last]

lemma splitUpd_castSucc {D : IdxDatum} {ℓ : ℕ} {al : D.Idx (ℓ + 1)} {s : D.S (ℓ + 1) → ℤ}
    (i : Fin (ℓ + 1)) (t : D.S i) : splitUpd D ℓ al s i.castSucc t = al i t := by
  simp only [splitUpd, Fin.snoc_castSucc]

/-- `D.pad (ℓ+2) (splitUpd al s) = padUpdate D ℓ al s`: the level-`(ℓ+2)` family appended from `al`
and `s`, padded, is the `ℕ`-indexed family with the level-`(ℓ+1)` coordinates `s` and the lower ones
`al`. -/
lemma pad_splitUpd (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ) :
    D.pad (ℓ + 2) (splitUpd D ℓ al s) = padUpdate D ℓ al s := by
  funext j' t
  simp only [IdxDatum.pad, padUpdate]
  by_cases h : j' = ℓ + 1
  · subst h
    rw [dif_pos (show ℓ + 1 < ℓ + 1 + 1 by omega), dif_pos rfl]
    exact splitUpd_at t
  · rw [dif_neg h]
    by_cases h2 : j' < ℓ + 1
    · rw [dif_pos h2, dif_pos (show j' < ℓ + 2 by omega)]
      exact splitUpd_castSucc ⟨j', h2⟩ t
    · rw [dif_neg h2, dif_neg (show ¬ j' < ℓ + 2 by omega)]

/-- The split box: the levels `≤ ℓ` closed in `[-M,M]` and the level `ℓ+1` also in `[-M,M]`. -/
abbrev succBox (D : IdxDatum) (ℓ M : ℕ) : Finset (D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ)) :=
  D.parBox (ℓ + 1) M ×ˢ
    Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))

/-- Factoring a constant out of a finite sum over `ℝ`: the normalisation step of the card-splitting
Fubini (`Finset.mul_sum`, stated in the direction that fires under `rw`). -/
lemma mul_sum_factor {α : Type} (s : Finset α) (g : α → ℝ) (a b : ℝ) :
    a * ∑ i ∈ s, b * g i = (a * b) * ∑ i ∈ s, g i := by
  calc a * ∑ i ∈ s, b * g i
      = ∑ i ∈ s, a * (b * g i) := Finset.mul_sum s (fun i => b * g i) a
    _ = ∑ i ∈ s, (a * b) * g i := Finset.sum_congr rfl fun i _ => by ring
    _ = (a * b) * ∑ i ∈ s, g i := (Finset.mul_sum s g (a * b)).symm

/-- The card-splitting normalisation of a sum over a product set: the generic form of the
card-splitting Fubini's arithmetic. -/
lemma sum_prod_normalise {α β : Type} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (G : α × β → ℝ) :
    ((P.card * Q.card : ℕ) : ℝ)⁻¹ * ∑ p ∈ P.product Q, G p
      = (P.card : ℝ)⁻¹ * ∑ al ∈ P, (Q.card : ℝ)⁻¹ * ∑ s ∈ Q, G (al, s) := by
  have hp : ∑ p ∈ P.product Q, G p = ∑ al ∈ P, ∑ s ∈ Q, G (al, s) := Finset.sum_product P Q G
  rw [hp, mul_sum_factor P (fun al => ∑ s ∈ Q, G (al, s)) (P.card : ℝ)⁻¹ (Q.card : ℝ)⁻¹]
  rw [Nat.cast_mul, mul_inv_rev]
  ring

/-- **The closed box `D.parBox (ℓ+2) M` is the image of the split box** under the appending map:
the level-`(ℓ+2)` parameter families are exactly the pairs (lower parameters, level-`(ℓ+1)`
coordinates) with every coordinate in `[-M,M]`. -/
theorem parBox_succ_eq_image (D : IdxDatum) (ℓ M : ℕ) :
    D.parBox (ℓ + 2) M
      = (succBox D ℓ M).image (fun p => splitUpd D ℓ p.1 p.2) := by
  ext a
  rw [Finset.mem_image]
  constructor
  · intro ha
    rw [IdxDatum.mem_parBox] at ha
    refine ⟨(Fin.init a, a (Fin.last (ℓ + 1))), ?_, ?_⟩
    · simp only [succBox, Finset.mem_product, IdxDatum.mem_parBox, Fintype.mem_piFinset,
        Finset.mem_Icc]
      exact ⟨fun j s => ha j.castSucc s, fun t => ha (Fin.last (ℓ + 1)) t⟩
    · exact splitUpd_idxSplit D ℓ a
  · rintro ⟨p, hp, rfl⟩
    simp only [succBox, Finset.mem_product, IdxDatum.mem_parBox, Fintype.mem_piFinset,
      Finset.mem_Icc] at hp
    rw [IdxDatum.mem_parBox]
    intro j t
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', hj'⟩ | hj'
    · subst hj'
      rw [splitUpd_castSucc]
      exact hp.1 j' t
    · subst hj'
      rw [splitUpd_at]
      exact hp.2 t

/-- **The card-splitting Fubini at the peeled level.**  The uniform average over the closed box
`D.parBox (ℓ+2) M` is the iterated average over the ladder's two boxes `D.parBox (ℓ+1) M` (the old
parameters) and `Finset.Icc (-M) M` (the new ones, which is the ladder's `paramBox (k := k) (M+1)`
up to the identification `Ioo (-(M+1)) (M+1) = Icc (-M) M`). -/
theorem parBox_succ_average (D : IdxDatum) (ℓ M : ℕ)
    (Φ : ((j' : ℕ) → D.S j' → ℤ) → ℝ) :
    ((D.parBox (ℓ + 2) M).card : ℝ)⁻¹ * ∑ a ∈ D.parBox (ℓ + 2) M, Φ (D.pad (ℓ + 2) a)
      = ((D.parBox (ℓ + 1) M).card : ℝ)⁻¹ *
        ∑ al ∈ D.parBox (ℓ + 1) M,
          ((Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)⁻¹ *
            ∑ s ∈ Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ)),
              Φ (padUpdate D ℓ al s) := by
  classical
  have hinj : Set.InjOn (fun p : D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) =>
      splitUpd D ℓ p.1 p.2) ↑(succBox D ℓ M) :=
    fun x _ y _ h => splitUpd_injective D ℓ h
  have hcard : (D.parBox (ℓ + 2) M).card
      = (D.parBox (ℓ + 1) M).card *
        (Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card := by
    rw [parBox_succ_eq_image, Finset.card_image_of_injOn hinj]
    exact Finset.card_product _ _
  have hsum : ∑ a ∈ D.parBox (ℓ + 2) M, Φ (D.pad (ℓ + 2) a)
      = ∑ p ∈ succBox D ℓ M, Φ (padUpdate D ℓ p.1 p.2) := by
    rw [parBox_succ_eq_image]
    rw [Finset.sum_image (f := fun a => Φ (D.pad (ℓ + 2) a)) hinj]
    exact Finset.sum_congr rfl (fun p _ => by rw [pad_splitUpd])
  rw [hcard, hsum]
  exact sum_prod_normalise (D.parBox (ℓ + 1) M)
    (Fintype.piFinset (fun _ : D.S (ℓ + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ)))
    (fun p => Φ (padUpdate D ℓ p.1 p.2))

/-- `padUpdate` at the peeled level. -/
lemma padUpdate_at (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ)
    (t : D.S (ℓ + 1)) : padUpdate D ℓ al s (ℓ + 1) t = s t := by
  rw [padUpdate, dif_pos rfl]

/-- `padUpdate` off the peeled level: the old parameters. -/
lemma padUpdate_of_ne (D : IdxDatum) (ℓ : ℕ) (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ)
    {j' : ℕ} (hj : j' ≠ ℓ + 1) (t : D.S j') :
    padUpdate D ℓ al s j' t = D.pad (ℓ + 1) al j' t := by
  rw [padUpdate, dif_neg hj]

/-- `D.pad` at a level below its cutoff: the corresponding old parameter. -/
lemma pad_apply_of_lt (D : IdxDatum) {l : ℕ} (a : D.Idx l) {j' : ℕ} (hj : j' < l)
    (t : D.S j') : D.pad l a j' t = a ⟨j', hj⟩ t := by
  rw [IdxDatum.pad, dif_pos hj]

/-- **`padUpdate` is injective**: the joint family determines both the old parameters and the new
ones.  This is the fibre computation underlying the mixed-box Fubini. -/
lemma padUpdate_inj (D : IdxDatum) (ℓ : ℕ) :
    Function.Injective
      (fun p : D.Idx (ℓ + 1) × (D.S (ℓ + 1) → ℤ) => padUpdate D ℓ p.1 p.2) := by
  intro p q h
  have hs : p.2 = q.2 := by
    funext t
    rw [← padUpdate_at D ℓ p.1 p.2 t, ← padUpdate_at D ℓ q.1 q.2 t]
    exact congrFun (congrFun h (ℓ + 1)) t
  have hal : p.1 = q.1 := by
    funext j t
    have hj : (j : ℕ) ≠ ℓ + 1 := by have := j.isLt; omega
    rw [← pad_apply_of_lt D p.1 j.isLt, ← padUpdate_of_ne D ℓ p.1 p.2 hj t,
      ← pad_apply_of_lt D q.1 j.isLt, ← padUpdate_of_ne D ℓ q.1 q.2 hj t]
    exact congrFun (congrFun h (j : ℕ)) t
  exact Prod.ext hal hs

end

end Work.Peluse
