import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.count_le
import Submission.Work.PSU3.StageB.Omega.count_le_self
import Submission.Work.PSU3.StageB.Omega.coset_sep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open Submission.Blueprint
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB
open Classical

namespace Work.PSU3.StageB.Omega

/-!
# `Work.PSU3.StageB.Omega.count_self_eq` — Peterfalvi II, Ch. VII §2 (8), the self-orbit equality

For `ω ∈ Q ∖ Q₀` the number of `x ∈ Q₀` whose `f(ω x)` lies in the `KW`-orbit of `ω`
(up to a `Q₀`-shift) is exactly `m - 1`, `m = |KW : K| = orderOf ζ`.

`count_le_self` already gives the upper bound `≤ m - 1`.  The lower bound is a *counting*
argument.  Write `Q₀` as the disjoint union, over the `KW`-orbits `O` of `E n^×`, of the
fibres `N O = {x ∈ Q₀ : bar(f(ω x)) ∈ O}`.

* The number of orbits satisfies `#orbits · orderOf ζ = 2ⁿ + 1` (`orbE_card`), while
  `|Q₀| = 2ⁿ` (`hcard`).
* Each `N O ≤ m` (`count_le`, via `orbit_mem_to_witness`, item (5)) and the orbit `O₀` of
  `ω` itself satisfies `N O₀ ≤ m - 1` (`count_le_self`).

Hence `2ⁿ = Σ_O N O ≤ (m-1) + (#orbits - 1)·m = 2ⁿ`, forcing `N O₀ = m - 1`; since
`N O₀` is the set counted by the statement, the goal follows.

The file isolates three reusable pieces:

* `orbit_mem_to_witness` — the algebraic core, item (5) in "orbit" form: `bar(f(ω x))` lying
  in the `KW`-orbit of `bar(ω')` produces the witness `d ∈ KW`, `y ∈ Q₀` of (5);
* `natCard_eq_sum_card_fiber` — the fibre partition of a map;
* `card_fiber_eq_of_sum_bound` — the abstract arithmetic (a fibre attaining `m-1`, all others
  at most `m`, `#β · m = q + 1` and the total `q` force the value `m-1`).
-/

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## `kact` versus `qconj` -/

/-- The `KW`-action `kact d z = d⁻¹ z d` agrees with the conjugation `qconj` by `d ∈ KW ⊆ D`. -/
lemma kact_eq_qconj (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (z : ↥Q) :
    kact hS fr d z = qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ z := rfl

/-- The `KW`-action is multiplicative in its argument. -/
lemma kact_mul_pointwise (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW)
    (a b : ↥Q) :
    kact hS fr d (a * b) = kact hS fr d a * kact hS fr d b := by
  apply Subtype.ext
  simp only [kact_coe, Subgroup.coe_mul]
  group

/-! ## Item (5) in orbit form -/

/-- **Item (5) of §2, "orbit" form.**  If `bar (f (ω x))` lies in the `KW`-orbit of
`bar ω'` in `E n^×`, then `f (ω x) = (ω' y)^d` for some `d ∈ KW` and `y ∈ Q₀` — i.e. exactly
the witness demanded by items (5)/(7) of the source. -/
theorem orbit_mem_to_witness (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω ω' x : ↥Q}
    (h : Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω'))) :
    ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * x) =
        qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω' * y) := by
  obtain ⟨d, hd⟩ := h
  have hzbar : fr.bar (fcan hS.split (ω * x)) = fr.bar (kact hS fr d ω') := by
    apply Multiplicative.toAdd.injective
    rw [kact_bar]
    exact hd
  set c : ↥Q := fcan hS.split (ω * x) * (kact hS fr d ω')⁻¹ with hcdef
  have hcQ0 : (c : G) ∈ fr.Q0 := by
    apply (fr.bar_eq_one_iff c).mp
    rw [hcdef, map_mul, hzbar, map_inv, mul_inv_cancel]
  have h1 : c * kact hS fr d ω' = fcan hS.split (ω * x) := by
    apply Subtype.ext
    simp only [hcdef, kact_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h2 : c * kact hS fr d ω' = kact hS fr d ω' * c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, kact_coe]
    exact fr.Q0_central (c : G) hcQ0 (kact hS fr d ω' : G) (kact hS fr d ω').2
  have hz_eq : fcan hS.split (ω * x) = kact hS fr d ω' * c := by
    rw [← h1]; exact h2
  refine ⟨d, kact hS fr d⁻¹ c, ?_, ?_⟩
  · simp only [kact_coe, Subgroup.coe_inv, inv_inv]
    exact conj_mem_Q0_of_mem_D hS fr (fr.KW_le d.2) hcQ0
  · have hyk : kact hS fr d (kact hS fr d⁻¹ c) = c := by
      rw [kact_mul, inv_mul_cancel, kact_one]
    have hstep : kact hS fr d ω' * c = kact hS fr d (ω' * kact hS fr d⁻¹ c) := by
      rw [kact_mul_pointwise hS fr d ω', hyk]
    rw [hz_eq, hstep, kact_eq_qconj hS fr d (ω' * kact hS fr d⁻¹ c)]

/-! ## The orbit set and the maps used in the counting -/

/-- The set of `KW`-orbits on `E n^×`. -/
abbrev OrbSet (fr : CoarseFrame H Q t n) : Type :=
  {O : Set (E n) // ∃ a : E n, a ≠ 0 ∧ O = orbE fr a}

/-- `Q₀` as a subtype of `Q`. -/
abbrev Q0Dom (fr : CoarseFrame H Q t n) : Type := {x : ↥Q // (x : G) ∈ fr.Q0}

/-- The set of `x ∈ Q₀` satisfying the witness condition with base point `ω` and target `ω'`. -/
abbrev ConjSet (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (ω ω' : ↥Q) : Type :=
  {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * x) =
        qconj hS.split (⟨(d : G), fr.KW_le d.2⟩ : ↥(twoPoint H t)) (ω' * y)}

/-- The set counted by `count_self_eq` (the `ω' = ω` case of `ConjSet`). -/
abbrev SelfSet (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (ω : ↥Q) : Type :=
  ConjSet hS fr ω ω

/-- `toAdd (bar ω) ≠ 0` for `ω ∉ Q₀`. -/
lemma toAdd_bar_ne_zero (fr : CoarseFrame H Q t n) {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    Multiplicative.toAdd (fr.bar ω) ≠ 0 := by
  intro hcon
  apply bar_ne_one_of_not_mem_Q0 fr hω
  have h := congrArg Multiplicative.ofAdd hcon
  simpa using h

/-- **(W1) in `E`-form.**  For `x ∈ Q₀` and `ω ∉ Q₀`, `toAdd (bar (f (ω x))) ≠ 0`. -/
lemma phi_ne_zero (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {ω : ↥Q}
    (hω : (ω : G) ∉ fr.Q0) (x : ↥Q) (hx : (x : G) ∈ fr.Q0) :
    Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x))) ≠ 0 := by
  intro hcon
  have h1 : fr.bar (fcan hS.split (ω * x)) = 1 := by
    have h := congrArg Multiplicative.ofAdd hcon
    simpa using h
  have h2 : ((fcan hS.split (ω * x) : ↥Q) : G) ∈ fr.Q0 := (fr.bar_eq_one_iff _).mp h1
  have h3 : ((ω * x : ↥Q) : G) ∈ fr.Q0 := (fcan_mem_Q0_iff hS fr (ω * x)).mp h2
  have h4 : fr.bar (ω * x) = 1 := (fr.bar_eq_one_iff _).mpr h3
  rw [map_mul, bar_eq_one_of_mem_Q0 fr hx, mul_one] at h4
  exact bar_ne_one_of_not_mem_Q0 fr hω h4

/-- The map `x ↦ orbE fr (bar (f (ω x)))` from `Q₀` to the set of `KW`-orbits on `E n^×`. -/
noncomputable def orbPhi (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (ω : ↥Q)
    (hω : (ω : G) ∉ fr.Q0) (x : Q0Dom fr) : OrbSet fr :=
  ⟨orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1)))),
   ⟨_, phi_ne_zero hS fr hω x.1 x.2, rfl⟩⟩

/-- Every `KW`-orbit on `E n^×` is the orbit of `bar ω'` for some `ω' ∈ Q ∖ Q₀`. -/
lemma orbSet_exists_rep (fr : CoarseFrame H Q t n) (O : OrbSet fr) :
    ∃ ω' : ↥Q, (ω' : G) ∉ fr.Q0 ∧
      (O : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar ω')) := by
  obtain ⟨Oset, a, ha, hO⟩ := O
  obtain ⟨ω', hω'⟩ := fr.bar_surjective (Multiplicative.ofAdd a)
  refine ⟨ω', ?_, ?_⟩
  · intro hc
    have h1 : fr.bar ω' = 1 := (fr.bar_eq_one_iff ω').mpr hc
    rw [hω'] at h1
    have h2 : a = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    exact ha h2
  · change Oset = orbE fr (Multiplicative.toAdd (fr.bar ω'))
    have h3 : Multiplicative.toAdd (fr.bar ω') = a := by rw [hω']; rfl
    rw [h3, hO]

/-! ## The two generic counting lemmas -/

/-- The fibre partition of a map between finite types: `α` is the disjoint union of the fibres
of `f`. -/
lemma natCard_eq_sum_card_fiber {α β : Type} [Finite α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // f a = b} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  exact Nat.card_sigma

/-- **Abstract counting.**  If a finite type `β` (with a distinguished `O₀`) carries a function
`N` with total `q`, all values `≤ m`, the value at `O₀` `≤ m - 1`, and `#β · m = q + 1`, then
`N O₀ = m - 1`. -/
lemma card_fiber_eq_of_sum_bound {β : Type} [Fintype β] (O₀ : β) (N : β → ℕ) (m q : ℕ)
    (hm : 1 ≤ m) (hcard : Fintype.card β * m = q + 1)
    (hN₀ : N O₀ ≤ m - 1) (hN : ∀ b, b ≠ O₀ → N b ≤ m)
    (hsum : (∑ b : β, N b) = q) :
    N O₀ = m - 1 := by
  classical
  have hM : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨O₀⟩
  have hmq : m ≤ q + 1 := by
    calc m = 1 * m := (one_mul m).symm
      _ ≤ Fintype.card β * m := Nat.mul_le_mul_right m hM
      _ = q + 1 := hcard
  have hsplit : N O₀ + ∑ b ∈ (Finset.univ.erase O₀), N b = q := by
    rw [← hsum, ← Finset.add_sum_erase Finset.univ N (Finset.mem_univ O₀)]
  have htail : ∑ b ∈ (Finset.univ.erase O₀), N b ≤ (Fintype.card β - 1) * m := by
    calc ∑ b ∈ (Finset.univ.erase O₀), N b ≤ ∑ _b ∈ (Finset.univ.erase O₀), m := by
          apply Finset.sum_le_sum; intro b hb; exact hN b (Finset.mem_erase.mp hb).1
      _ = (Finset.univ.erase O₀).card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ = (Fintype.card β - 1) * m := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ O₀), Finset.card_univ]
  have hmul : (Fintype.card β - 1) * m = Fintype.card β * m - m := by
    rw [Nat.sub_mul, one_mul]
  have hkey : (Fintype.card β - 1) * m = q + 1 - m := by rw [hmul, hcard]
  have hge : m - 1 ≤ N O₀ := by
    have h1 : N O₀ = q - ∑ b ∈ (Finset.univ.erase O₀), N b := by omega
    have h2 : q - (Fintype.card β - 1) * m ≤ q - ∑ b ∈ (Finset.univ.erase O₀), N b :=
      Nat.sub_le_sub_left htail q
    rw [← h1, hkey] at h2
    have : q - (q + 1 - m) = m - 1 := by omega
    rwa [this] at h2
  omega

/-! ## The self-orbit equality -/

theorem count_self_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hcard : Nat.card ↥fr.Q0 = 2 ^ n)
    (hdiv : Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) = orderOf fr.ζ)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        Work.PSU3.StageB.fcan hS.split (ω * x) =
          Work.PSU3.StageB.qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω * y)}
      = orderOf fr.ζ - 1 := by
  classical
  change Nat.card (SelfSet hS fr ω) = orderOf fr.ζ - 1
  haveI : Fintype (OrbSet fr) := Fintype.ofFinite (OrbSet fr)
  -- the orbit of `ω`
  let O0 : OrbSet fr := ⟨orbE fr (Multiplicative.toAdd (fr.bar ω)),
    ⟨_, toAdd_bar_ne_zero fr hω, rfl⟩⟩
  -- the fibre-count function
  let N : OrbSet fr → ℕ := fun O => Nat.card {x : Q0Dom fr // orbPhi hS fr ω hω x = O}
  -- `|Q₀| = 2ⁿ`
  have hcard_dom : Nat.card (Q0Dom fr) = 2 ^ n := by
    rw [show Nat.card (Q0Dom fr) = Nat.card ↥fr.Q0 from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe fr.Q0_le).toEquiv, hcard]
  -- the fibres partition `Q₀`
  have hsum : ∑ O : OrbSet fr, N O = 2 ^ n := by
    rw [← hcard_dom]
    exact (natCard_eq_sum_card_fiber (orbPhi hS fr ω hω)).symm
  -- the number of orbits
  have hcard_orbit : Fintype.card (OrbSet fr) * orderOf fr.ζ = 2 ^ n + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact (orbE_card hS fr).2
  have hm : 1 ≤ orderOf fr.ζ := by have := orderOf_pos fr.ζ; omega
  -- every fibre but the one of `ω` has at most `m` points
  have hN : ∀ O : OrbSet fr, O ≠ O0 → N O ≤ orderOf fr.ζ := by
    intro O _
    obtain ⟨ω', hω', hrep⟩ := orbSet_exists_rep fr O
    have hwit : ∀ x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O},
        Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar ω')) := by
      intro x
      have hval : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1)))) =
          (O : Set (E n)) := congrArg Subtype.val x.2
      rw [← hrep, ← hval]
      exact orbE_refl fr _
    have hinj : Function.Injective (fun x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O} =>
        (⟨x.1.1, x.1.2, orbit_mem_to_witness hS fr (hwit x)⟩ : ConjSet hS fr ω ω')) := by
      intro x y hxy
      have h1 : (x.1.1 : ↥Q) = (y.1.1 : ↥Q) := congrArg (fun z => (z.1 : ↥Q)) hxy
      exact Subtype.ext (Subtype.ext h1)
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    have h := count_le hS fr hω hω'
    rw [hdiv] at h
    exact h
  -- the fibre of `ω` injects into the set counted by `count_self_eq`
  have hge : N O0 ≤ Nat.card (SelfSet hS fr ω) := by
    have hwit : ∀ x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O0},
        Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar ω)) := by
      intro x
      have hval : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * x.1.1)))) =
          (O0 : Set (E n)) := congrArg Subtype.val x.2
      have hO0val : (O0 : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar ω)) := rfl
      rw [← hO0val, ← hval]
      exact orbE_refl fr _
    have hinj : Function.Injective (fun x : {x : Q0Dom fr // orbPhi hS fr ω hω x = O0} =>
        (⟨x.1.1, x.1.2, orbit_mem_to_witness hS fr (hwit x)⟩ : SelfSet hS fr ω)) := by
      intro x y hxy
      have h1 : (x.1.1 : ↥Q) = (y.1.1 : ↥Q) := congrArg (fun z => (z.1 : ↥Q)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Nat.card_le_card_of_injective _ hinj
  -- the upper bound `≤ m - 1`
  have hCS_le : Nat.card (SelfSet hS fr ω) ≤ orderOf fr.ζ - 1 := by
    have h := count_le_self hS fr hω
    rw [hdiv] at h
    exact h
  have hN0 : N O0 ≤ orderOf fr.ζ - 1 := hge.trans hCS_le
  -- the abstract counting pins the fibre of `ω`
  have hN0_eq : N O0 = orderOf fr.ζ - 1 :=
    card_fiber_eq_of_sum_bound O0 N (orderOf fr.ζ) (2 ^ n) hm hcard_orbit hN0 hN hsum
  exact le_antisymm hCS_le (hN0_eq ▸ hge)

end Work.PSU3.StageB.Omega
