/-
# `Work.PSU3.StageB.Omega.count_le` — Peterfalvi II, Ch. VII §2 (8): the count of
`Q₀`-shifts with image in a prescribed `KW`-orbit

Peterfalvi II, Ch. VII §2, item **(8)** (p. 270) states that for the representatives
`ω_1, …, ω_n` of the `KW`-orbits on `(Q/Q₀)#`, the number `m_i` of `x ∈ Q₀` such that the image of
`f(ω_1 x)` in `E ≅ Q/Q₀` lies in the orbit of `ω_i` satisfies `m_i ≤ m` for `i > 1` and
`m_1 ≤ m − 1`, where `m = |KW : K| = |KW| / |Ksub|`.  This file proves the uniform weaker bound
`≤ m`, valid for **arbitrary** `ω, ω' ∈ Q ∖ Q₀`:

  the number of `x ∈ Q₀` for which there are `d ∈ fr.KW` and `y ∈ Q₀` with
  `f(ω x) = (ω' y)^d` is at most `|KW| / |Ksub|`.

The mathematics is item **(7)** of §2: if `x₁ ≠ x₂` in `Q₀` and, for `i = 1, 2`, `y_i ∈ Q₀` and
`a_i ∈ D` satisfy `f(ω x_i) = (ω' y_i)^{a_i}`, then `a₁⁻¹ a₂ ∉ K`; i.e. the `a_x` attached to
distinct solutions lie in **distinct cosets of `K` in `KW`**.  Fixing a witness `d_x ∈ fr.KW` for
each solution (the axiom of choice), the map `x ↦ d_x · K` is therefore injective, and the number
of solutions is at most the number of cosets of `Ksub` in `KW`, which is `|KW| / |Ksub|`.

Item (7) is `Work.PSU3.StageB.Omega.coset_sep` (proved in `Omega/coset_sep.lean`) and rests on
items (5) and (6), `Work.PSU3.StageB.Omega.fcan_eq_qconj` and
`Work.PSU3.StageB.Omega.fcan_mul_eq_qconj`.  The two `conversion` lemmas `fcan_item5`,
`fcan_item6` below merely reshape (5), (6) into the hypothesis format expected by `coset_sep`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.coset_sep
import Submission.Work.PSU3.StageB.Omega.fcan_eq_qconj
import Submission.Work.PSU3.StageB.Omega.fcan_mul_eq_qconj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

open Submission.Blueprint
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

namespace Work.PSU3.StageB.Omega

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Items (5) and (6) of §2 in the shape required by item (7) -/

/-- **§2 (5)**, in the form used by `coset_sep` as item (6)'s hypothesis: if `f(ω) = (ω y)^a`
with `ω ∉ Q₀`, `y ∈ Q₀` and `a ∈ D`, then `a ∉ K`.  (The companion conclusion `y ≠ 1` is
discarded here.) -/
theorem fcan_item5 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {y : ↥Q} (hy : (y : G) ∈ fr.Q0)
    {a : ↥(twoPoint H t)} (h : fcan hS.split ω = qconj hS.split a (ω * y)) :
    (a : G) ∉ Ksub H t :=
  (fcan_eq_qconj hS fr hω hy h).2

/-- **§2 (6)**: if `f(ω x) = (f(ω) y)^a` with `ω ∉ Q₀`, `x, y ∈ Q₀`, `x ≠ 1` and `a ∈ D`, then
`a ∉ K`. -/
theorem fcan_item6 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {x y : ↥Q}
    (hx : (x : G) ∈ fr.Q0) (hx1 : x ≠ 1) (hy : (y : G) ∈ fr.Q0)
    {a : ↥(twoPoint H t)} (h : fcan hS.split (ω * x) = qconj hS.split a (fcan hS.split ω * y)) :
    (a : G) ∉ Ksub H t :=
  fcan_mul_eq_qconj hS fr (fcan_item5 hS fr) hω hx hx1 hy h

/-! ## §2 (7): distinct solutions yield distinct cosets of `K` in `KW` -/

/-- **§2 (7)**, in terms of `fr.KW`-witnesses: if `x₁ ≠ x₂` in `Q₀` and, for `i = 1, 2`,
`y_i ∈ Q₀` and `d_i ∈ fr.KW ⊆ D` satisfy `f(ω x_i) = (ω' y_i)^{d_i}`, then
`d₁⁻¹ d₂ ∉ Ksub`, i.e. `d₁` and `d₂` lie in distinct cosets of `Ksub` in `fr.KW`. -/
theorem coset_sep_KW (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω ω' : ↥Q} (hω : (ω : G) ∉ fr.Q0) (hω' : (ω' : G) ∉ fr.Q0)
    {x₁ x₂ y₁ y₂ : ↥Q} (hx₁ : (x₁ : G) ∈ fr.Q0) (hx₂ : (x₂ : G) ∈ fr.Q0)
    (hxx : x₁ ≠ x₂) (hy₁ : (y₁ : G) ∈ fr.Q0) (hy₂ : (y₂ : G) ∈ fr.Q0)
    {d₁ d₂ : fr.KW}
    (h₁ : fcan hS.split (ω * x₁) = qconj hS.split ⟨(d₁ : G), fr.KW_le d₁.2⟩ (ω' * y₁))
    (h₂ : fcan hS.split (ω * x₂) = qconj hS.split ⟨(d₂ : G), fr.KW_le d₂.2⟩ (ω' * y₂)) :
    (d₁ : G)⁻¹ * (d₂ : G) ∉ Ksub H t := by
  have key := coset_sep hS fr (fcan_item6 hS fr) hω hω' hx₁ hx₂ hxx hy₁ hy₂ h₁ h₂
  simpa using key

/-! ## The count -/

theorem count_le {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω ω' : ↥Q} (hω : (ω : G) ∉ fr.Q0) (hω' : (ω' : G) ∉ fr.Q0) :
    Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        Work.PSU3.StageB.fcan hS.split (ω * x) =
          Work.PSU3.StageB.qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω' * y)}
      ≤ Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) := by
  classical
  -- the solution predicate
  let P : ↥Q → Prop := fun x => (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * x) = qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω' * y)
  -- the subgroup of `fr.KW` by which we quotient
  let K0 : Subgroup fr.KW := (Ksub H t).comap fr.KW.subtype
  have hK0def : K0 = (Ksub H t).comap fr.KW.subtype := rfl
  /- `K0` is the copy of `Ksub` inside `fr.KW`, so it has the same cardinality. -/
  have hK0card : Nat.card ↥K0 = Nat.card ↥(Ksub H t) := by
    rw [hK0def, Subgroup.comap_subtype]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Ksub H t) (K := fr.KW) (fr.K_le)).toEquiv
  /- the coset space of `Ksub` in `fr.KW` has `|KW| / |Ksub|` elements -/
  have hquot : Nat.card (fr.KW ⧸ K0) = Nat.card fr.KW / Nat.card ↥(Ksub H t) := by
    rw [← Subgroup.index_eq_card K0, Subgroup.index_eq_card_div K0, hK0card]
  -- a witness `d ∈ fr.KW` for each solution, and the associated `y ∈ Q₀`
  let witD : {x : ↥Q // P x} → fr.KW := fun x => Classical.choose x.2.2
  let witY : {x : ↥Q // P x} → ↥Q := fun x => Classical.choose (Classical.choose_spec x.2.2)
  have witY_mem : ∀ x : {x : ↥Q // P x}, (witY x : G) ∈ fr.Q0 := fun x =>
    (Classical.choose_spec (Classical.choose_spec x.2.2)).1
  have wit_eq : ∀ x : {x : ↥Q // P x},
      fcan hS.split (ω * (x : ↥Q)) =
        qconj hS.split ⟨(witD x : G), fr.KW_le (witD x).2⟩ (ω' * witY x) := fun x =>
    (Classical.choose_spec (Classical.choose_spec x.2.2)).2
  /- the solution set injects into the cosets of `Ksub` in `fr.KW`, by §2 (7) -/
  have hinj : Function.Injective
      (fun x : {x : ↥Q // P x} => (QuotientGroup.mk (witD x) : fr.KW ⧸ K0)) := by
    intro x y hxy
    by_contra hne
    have hne1 : (x : ↥Q) ≠ (y : ↥Q) := fun h => hne (Subtype.ext h)
    have hmem : (witD x)⁻¹ * (witD y) ∈ K0 := QuotientGroup.eq.mp hxy
    have hmemK : (witD x : G)⁻¹ * (witD y : G) ∈ Ksub H t := by
      have h := hmem
      rw [hK0def, Subgroup.mem_comap] at h
      simpa using h
    exact coset_sep_KW hS fr hω hω' x.2.1 y.2.1 hne1 (witY_mem x) (witY_mem y)
      (wit_eq x) (wit_eq y) hmemK
  have hle : Nat.card {x : ↥Q // P x} ≤ Nat.card (fr.KW ⧸ K0) :=
    Nat.card_le_card_of_injective _ hinj
  rw [hquot] at hle
  exact hle

end Work.PSU3.StageB.Omega
