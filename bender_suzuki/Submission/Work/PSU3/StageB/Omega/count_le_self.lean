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

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Submission.Blueprint
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB
open Classical

namespace Work.PSU3.StageB.Omega

/-!
# `Work.PSU3.StageB.Omega.count_le_self` — Peterfalvi II, Ch. VII §2 (8), the self-orbit count

For `ω ∈ Q ∖ Q₀`, the number of `x ∈ Q₀` with `f(ω x) ∈ (ω Q₀)^{KW}` (i.e. `f(ω x) = (ω y)^d`
for some `d ∈ KW`, `y ∈ Q₀`) is at most `|KW : K| - 1`, where `K = KW ∩ Ksub`.

The proof is the one of the source, and rests on the two items already proved:

* (7) `coset_sep`: if `x₁ ≠ x₂` are two such `Q₀`-shifts with witnesses `d₁, d₂`, then
  `d₁⁻¹ d₂ ∉ Ksub` — so distinct `x`'s occupy distinct cosets of `K` in `KW`;
* (5) `fcan_eq_qconj`, applied to the base point `ω x` with shift `x⁻¹ y`: the trivial coset
  `K` itself is never occupied (it would give a witness `d ∈ Ksub`).

Hence `x ↦ d_x·K` is an injection into the `[KW : K] - 1` nontrivial cosets of `K` in `KW`.
-/

/-- The set counted by `count_le_self`: the `x ∈ Q₀` for which `f(ω x)` lies in the `KW`-orbit
of `ω`, up to a `Q₀`-shift. -/
abbrev cntSet {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (ω : ↥Q) : Type :=
  {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
    Work.PSU3.StageB.fcan hS.split (ω * x) =
      Work.PSU3.StageB.qconj hS.split
        (⟨(d : G), fr.KW_le d.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω * y)}

/-- `K = KW ∩ Ksub = KW ∩ cKsub`, as a subgroup of `KW`. -/
abbrev KWcapKsub {G : Type} [Group G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : CoarseFrame H Q t n) : Subgroup ↥fr.KW :=
  (Work.ThmF.Ksub H t).comap fr.KW.subtype

/-- A finite type with one point removed has one element less. -/
lemma natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {b : α // b ≠ a} = Nat.card α - 1 := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun b : α => b = a), Fintype.card_subtype_eq]

theorem count_le_self {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    Nat.card {x : ↥Q // (x : G) ∈ fr.Q0 ∧ ∃ d : fr.KW, ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧
        Work.PSU3.StageB.fcan hS.split (ω * x) =
          Work.PSU3.StageB.qconj hS.split
            (⟨(d : G), fr.KW_le d.2⟩ : ↥(Submission.Blueprint.twoPoint H t)) (ω * y)}
      ≤ Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) - 1 := by
  classical
  change Nat.card (cntSet hS fr ω) ≤ Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) - 1
  -- ## membership in `K = KW ∩ Ksub`
  have hKm : ∀ d : ↥fr.KW, d ∈ KWcapKsub fr ↔ (d : G) ∈ Work.ThmF.Ksub H t :=
    fun d => Subgroup.mem_comap
  -- ## `|K| = |Ksub|` and `[KW : K] = |KW| / |Ksub|`
  have hKcard : Nat.card ↥(KWcapKsub fr) = Nat.card ↥(Work.ThmF.Ksub H t) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun d : ↥(KWcapKsub fr) =>
        (⟨((d.1 : fr.KW) : G), (hKm d.1).mp d.2⟩ : ↥(Work.ThmF.Ksub H t)))
      ⟨?_, ?_⟩)
    · intro d e hde
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) hde
    · intro k
      exact ⟨⟨⟨(k : G), fr.K_le k.2⟩, (hKm _).mpr k.2⟩, rfl⟩
  have hidx : Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) = (KWcapKsub fr).index := by
    have h := Subgroup.card_mul_index (KWcapKsub fr)
    rw [hKcard] at h
    rw [← h, Nat.mul_div_right (KWcapKsub fr).index Nat.card_pos]
  -- ## the witnesses chosen from the existential
  let W : cntSet hS fr ω → fr.KW := fun x => Classical.choose x.2.2
  let Y : cntSet hS fr ω → ↥Q := fun x => Classical.choose (Classical.choose_spec x.2.2)
  have hY : ∀ x : cntSet hS fr ω, ((Y x : ↥Q) : G) ∈ fr.Q0 :=
    fun x => (Classical.choose_spec (Classical.choose_spec x.2.2)).1
  have hEq : ∀ x : cntSet hS fr ω,
      fcan hS.split (ω * x.1) =
        qconj hS.split (⟨(W x : G), fr.KW_le (W x).2⟩ : ↥(twoPoint H t)) (ω * Y x) :=
    fun x => (Classical.choose_spec (Classical.choose_spec x.2.2)).2
  -- ## `ω x ∉ Q₀` for `x ∈ Q₀`
  have hbase : ∀ x : cntSet hS fr ω, ((ω * x.1 : ↥Q) : G) ∉ fr.Q0 := by
    intro x hc
    have hbar : fr.bar (ω * x.1) = 1 := (fr.bar_eq_one_iff (ω * x.1)).mpr hc
    have hsplit : fr.bar (ω * x.1) = fr.bar ω * fr.bar x.1 := map_mul fr.bar ω x.1
    rw [hsplit, bar_eq_one_of_mem_Q0 fr x.2.1, mul_one] at hbar
    exact bar_ne_one_of_not_mem_Q0 fr hω hbar
  -- ## (5): the trivial coset `K` is never attained
  have hA : ∀ x : cntSet hS fr ω, W x ∉ KWcapKsub fr := by
    intro x hx
    have hmem : (W x : G) ∈ Work.ThmF.Ksub H t := (hKm (W x)).mp hx
    have hz : ((x.1⁻¹ * Y x : ↥Q) : G) ∈ fr.Q0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (fr.Q0).mul_mem ((fr.Q0).inv_mem x.2.1) (hY x)
    have heq : fcan hS.split (ω * x.1) =
        qconj hS.split (⟨(W x : G), fr.KW_le (W x).2⟩ : ↥(twoPoint H t))
          ((ω * x.1) * (x.1⁻¹ * Y x)) := by
      rw [hEq x]
      refine congrArg (fun z : ↥Q => qconj hS.split
        (⟨(W x : G), fr.KW_le (W x).2⟩ : ↥(twoPoint H t)) z) ?_
      apply Subtype.ext
      show (ω : G) * (Y x : G) = (ω : G) * (x.1 : G) * ((x.1 : G)⁻¹ * (Y x : G))
      group
    exact (fcan_eq_qconj hS fr (hbase x) hz heq).2 hmem
  -- ## (7): distinct `x`'s give distinct cosets
  have h5 : ∀ {θ : ↥Q}, (θ : G) ∉ fr.Q0 → ∀ {y : ↥Q}, (y : G) ∈ fr.Q0 →
      ∀ {a : ↥(twoPoint H t)},
      fcan hS.split θ = qconj hS.split a (θ * y) → (a : G) ∉ Work.ThmF.Ksub H t := by
    intro θ hθ y hy a h
    exact (fcan_eq_qconj hS fr hθ hy h).2
  have hsep : ∀ x₁ x₂ : cntSet hS fr ω, x₁ ≠ x₂ → (W x₁)⁻¹ * (W x₂) ∉ KWcapKsub fr := by
    intro x₁ x₂ hne
    have hxx : x₁.1 ≠ x₂.1 := fun h => hne (Subtype.ext h)
    have h := coset_sep hS fr (fcan_mul_eq_qconj hS fr h5) (ω := ω) (ω' := ω) hω hω
      (x₁ := x₁.1) (x₂ := x₂.1) x₁.2.1 x₂.2.1 hxx (hY x₁) (hY x₂) (hEq x₁) (hEq x₂)
    rw [hKm]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
  -- ## the injection into the nontrivial cosets of `K` in `KW`
  haveI : Finite (↥fr.KW ⧸ KWcapKsub fr) :=
    Finite.of_surjective (QuotientGroup.mk (s := KWcapKsub fr))
      (QuotientGroup.mk_surjective (s := KWcapKsub fr))
  let ψ : cntSet hS fr ω → {c : ↥fr.KW ⧸ KWcapKsub fr // c ≠ QuotientGroup.mk (1 : ↥fr.KW)} :=
    fun x => ⟨QuotientGroup.mk (W x), by
      intro h
      refine hA x ((Subgroup.inv_mem_iff (KWcapKsub fr)).mp ?_)
      simpa using (QuotientGroup.eq.mp h)⟩
  have hψ_inj : Function.Injective ψ := by
    intro x₁ x₂ h
    by_contra hne
    have hq : QuotientGroup.mk (W x₁) = QuotientGroup.mk (W x₂) := congrArg Subtype.val h
    exact hsep x₁ x₂ hne (QuotientGroup.eq.mp hq)
  -- ## the count
  calc Nat.card (cntSet hS fr ω)
      ≤ Nat.card {c : ↥fr.KW ⧸ KWcapKsub fr // c ≠ QuotientGroup.mk (1 : ↥fr.KW)} :=
        Nat.card_le_card_of_injective ψ hψ_inj
    _ = (KWcapKsub fr).index - 1 := by
        rw [natCard_subtype_ne, ← Subgroup.index_eq_card]
    _ = Nat.card fr.KW / Nat.card ↥(Work.ThmF.Ksub H t) - 1 := by rw [hidx]

end Work.PSU3.StageB.Omega
