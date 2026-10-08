import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.caseB_centD_eq_bot
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.ThmF.ChV12.canonicalForm
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.PSU3.StageB.CanonData
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.PSU3.StageA.HValueOfRRk
import Submission.Work.PSU3.StageA.KOrbitsOfQ_full

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseB_tQt_subset_of_Ksub` — Peterfalvi II Ch. VI §2 (p. 261)

In case b) of the Proposition of Ch. VI §1 (`Q` non-abelian of order `q²`, `q = |Q0sub H|`,
`orderOf (s*t) = 5`, `W = C_V(K) = ⊥`), every `x ∈ Q#` satisfies

  `t x t ∈ Q · Kset · t · Q`,   i.e.  `t x t = a k t b` with `a, b ∈ Q`, `k ∈ Kset H t = J(D,t)`.

Equivalently, the `D`-component `h(x)` of the canonical form `t x t = g(x) h(x) t f(x)` lies in
`Kset H t`.  This is the input that makes `G₀ = (QK) ∪ (QKtQ)` a subgroup of `G`, hence
(by `Work.RankOneUniqueness.closure_Q_t_eq_top`) a proper normal subgroup of index `|V| > 1`,
contradicting simplicity — the elimination of case b).

## The source's proof (p. 261–263) and how it is organised here

`Good h x` means `h(x) ∈ Kset H t`; by `good_iff` this is exactly the requested conclusion.

* **`K`-conjugation invariance** (`good_conj`): Peterfalvi's formula (1), read off
  `Work.PSU3.StageB.canon_conj_fun`: for `a ∈ D`, `h(a⁻¹ x a) = (t a t)⁻¹ h(x) a`; for
  `a = k ∈ Kset` this is `h(k⁻¹ x k) = k h(x) k`, and `K = Kset = Ksub` being a subgroup
  (`hKsub`) makes `Good` `K`-invariant.
* **The good representatives** (`GoodReps H t s r`): `s`, `r`, `r⁻¹` — where `Good` follows from
  the structure identity `t s t = r⁻¹ t r` and its consequences `t r t = r t s`,
  `t r⁻¹ t = s t r⁻¹` (proved here); and the `r r^{-k}` (`1 ≠ k ∈ Kset`), Peterfalvi's
  computation (4), where `h(rr^{-k}) = ℓ²k² ∈ K` with `s^k = s^ℓ` (`caseB_dValue_reps`).
* **The orbit structure** (`caseB_K_orbits_Q`): every `x ∈ Q#` is `K`-conjugate to one of the
  listed representatives — the one place where the arithmetic of `𝔽_q` enters (App. V, and the
  source's equations (5)–(7)).

## State of this file (for the next session)

Proved here, hole-free:

* `GoodReps` (the representative set), `Good` (the `D`-component lies in `Kset`), `good_iff`
  (`Good` ⟺ the requested conclusion), `good_conj` (Peterfalvi's formula (1), hence
  `K`-invariance of `Good` — uses only that `Kset` is a subgroup);
* `caseB_t_conj_r_inv`, `caseB_t_conj_r` (`t r⁻¹ t = s t r⁻¹`, `t r t = r t s` from the
  structure identity);
* `caseB_dValue_reps`: the conclusion at `s`, `r`, `r⁻¹` (from the structure identity) and at
  `r r^{-k}` (via the delegated `Work.PSU3.StageA.HValueOfRRk`, whose `hfree` input is
  `Work.ThmF.ChV12.prop1a`; `r ≠ 1` is derived from `hsr`);
* `caseB_tQt_subset_of_orbits_and_values` (the assembly) and `caseB_tQt_subset_of_Ksub`
  (the target) — modulo the single remaining gap below.

Remaining gap: `caseB_K_orbits_Q`, the Ch. VI §2 orbit count.  It is the only place where the
`𝔽_q`-arithmetic is used and it is *not* derivable from the library as it stands: a fleet prover
handed exactly this statement declared it unprovable, and the missing ingredient is the explicit
Suzuki model `Q ≅ SzA(𝔽_q, θ)` (obtainable from `HigmanProp` + `IsSuzukiTwoGroup ↥Q` +
`|Q| = |Z(Q)|²` via `Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup`, where `IsSuzukiTwoGroup ↥Q`
follows from the regular action of `Kset` on `Inv H` = `Z(Q)#`, `Kset_regular`) together with
`Prop 3` (`Work.ThmF.ChV12.prop3`), which gives `κ : Ksub H t ≃* 𝔽_q^*` and the action of `K` on
`Q₀sub` by multiplication.  In those coordinates the `K`-action is the diagonal
`(a,b) ↦ (λ a, λ^{1+θ} b)`, the `K`-orbits on `Q#` are the level sets of `c = b/a^{1+θ}`, and the
pairwise distinctness of the orbits of `s`, `r`, `r⁻¹`, `r r^{-k}` is the source's computation
(5)–(7).
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}

/-! ## `Good`: the `D`-component lies in `Kset` -/

/-- `Good h x` : the `D`-component `h(x)` of the canonical form `t x t = g(x) h(x) t f(x)` lies
in `Kset H t = J(D,t)`.  This is the assertion of Peterfalvi II Ch. VI §2 for `x`. -/
def Good (h : Submission.Blueprint.IsSplitRankOne H Q t) (x : ↥Q) : Prop :=
  ((Work.PSU3.StageB.hcan h x : G)) ∈ Work.ThmF.Kset H t

/-- `Good` is exactly the requested conclusion. -/
theorem good_iff (h : Submission.Blueprint.IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    Good h x ↔ ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * (x : G) * t = a * k * t * b := by
  constructor
  · intro hgood
    exact ⟨(Work.PSU3.StageB.gcan h x : G), (Work.PSU3.StageB.gcan h x).2,
      (Work.PSU3.StageB.hcan h x : G), hgood,
      (Work.PSU3.StageB.fcan h x : G), (Work.PSU3.StageB.fcan h x).2,
      Work.PSU3.StageB.canon_spec h hx⟩
  · rintro ⟨a, ha, k, hk, b, hb, heq⟩
    have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hk
    have h1 := Work.PSU3.StageB.canon_unique'' h hx (g := ⟨a, ha⟩) (d := ⟨k, hkD⟩) (y := ⟨b, hb⟩) heq
    change ((Work.PSU3.StageB.hcan h x : G)) ∈ Work.ThmF.Kset H t
    rw [← h1.2.1]
    exact hk

/-- **Peterfalvi's formula (1)**: `Good` is invariant under conjugation by `Kset`.  This is
`Work.PSU3.StageB.canon_conj_fun`, `h(a⁻¹ x a) = (t a t)⁻¹ h(x) a`, together with
`t k t = k⁻¹` for `k ∈ Kset` and the closure of `Kset` coming from `hKsub`. -/
theorem good_conj (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {k : G} (hkK : k ∈ Work.ThmF.Kset H t) {x x' : ↥Q} (hx : (x : G) ≠ 1)
    (hx' : (x' : G) = k⁻¹ * (x : G) * k) : Good h x' ↔ Good h x := by
  classical
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hkK
  have hkinv : t * k * t = k⁻¹ := by
    have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self h
    have h' := (Work.ThmF.mem_Kset_iff.mp hkK).2
    rwa [hti] at h'
  have hKset_mul : ∀ u ∈ Work.ThmF.Kset H t, ∀ v ∈ Work.ThmF.Kset H t,
      u * v ∈ Work.ThmF.Kset H t := by
    intro u hu v hv
    have h1 : u ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hu
    have h2 : v ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hv
    have h3 : u * v ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).mul_mem h1 h2
    rwa [hKsub] at h3
  have hKset_inv : ∀ u ∈ Work.ThmF.Kset H t, u⁻¹ ∈ Work.ThmF.Kset H t := by
    intro u hu
    have h1 : u ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hu
    have h3 : u⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).inv_mem h1
    rwa [hKsub] at h3
  obtain ⟨y, hy, -, -, hhh⟩ := Work.PSU3.StageB.canon_conj_fun h hx ⟨k, hkD⟩
  have hyx' : (y : G) = (x' : G) := by rw [hy, hx']
  have hyx'' : y = x' := Subtype.ext hyx'
  have hfoo : (Work.PSU3.StageB.hcan h y : G) = (Work.PSU3.StageB.hcan h x' : G) := by
    rw [hyx'']
  rw [hfoo] at hhh
  have hkcoe : ((⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t)) : G) = k := rfl
  have hhh' : (Work.PSU3.StageB.hcan h x' : G) =
      k * (Work.PSU3.StageB.hcan h x : G) * k := by
    simp only [hkcoe] at hhh
    simpa [hkinv] using hhh
  have hkey : (Work.PSU3.StageB.hcan h x : G) =
      k⁻¹ * (Work.PSU3.StageB.hcan h x' : G) * k⁻¹ := by
    rw [hhh']
    group
  constructor
  · intro hgood
    change ((Work.PSU3.StageB.hcan h x : G)) ∈ Work.ThmF.Kset H t
    rw [hkey]
    exact hKset_mul (k⁻¹ * (Work.PSU3.StageB.hcan h x' : G))
      (hKset_mul k⁻¹ (hKset_inv k hkK) _ hgood) k⁻¹ (hKset_inv k hkK)
  · intro hgood
    change ((Work.PSU3.StageB.hcan h x : G)) ∈ Work.ThmF.Kset H t at hgood
    change ((Work.PSU3.StageB.hcan h x' : G)) ∈ Work.ThmF.Kset H t
    rw [hhh']
    exact hKset_mul (k * (Work.PSU3.StageB.hcan h x : G))
      (hKset_mul k hkK _ hgood) k hkK

-- The two computational inputs of the source's Ch. VI §2 proof.
--
-- The orbit structure (every `x ∈ Q#` is `K`-conjugate to a representative of `GoodReps`) is
-- proved in the sibling module `Submission.Work.PSU3.StageA.KOrbitsOfQ_full`; there the
-- `𝔽_q`-model of `Q` is set up and the source's computation (5)–(7) is run.

/-- **The `d`-values on the representatives** (Peterfalvi II Ch. VI §2, computation (4), p. 262):
`Good` holds at all of `GoodReps H t s r`.  The cases `s`, `r`, `r⁻¹` are read off the structure
identity; the case `r r^{-k}` is the source's computation (4), where `h(rr^{-k}) = ℓ²k² ∈ K`. -/
theorem caseB_dValue_reps (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hr1 : r ≠ 1)
    (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    (∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * s * t = a * k * t * b) ∧
    (∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * r * t = a * k * t * b) ∧
    (∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * r⁻¹ * t = a * k * t * b) ∧
    (∀ k ∈ Work.ThmF.Kset H t, k ≠ 1 → ∃ a ∈ Q, ∃ k' ∈ Work.ThmF.Kset H t, ∃ b ∈ Q,
      t * (r * (k⁻¹ * r⁻¹ * k)) * t = a * k' * t * b) := by
  have h : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one h
  have htrt := caseB_t_conj_r ht2 hs2 hsr
  have htrinvt := caseB_t_conj_r_inv ht2 hsr
  exact ⟨⟨r⁻¹, Q.inv_mem hr, 1, Work.ThmF.one_mem_Kset H t, r, hr, by simpa using hsr⟩,
    ⟨r, hr, 1, Work.ThmF.one_mem_Kset H t, s, hs, by simpa using htrt⟩,
    ⟨s, hs, 1, Work.ThmF.one_mem_Kset H t, r⁻¹, Q.inv_mem hr, by simpa using htrinvt⟩,
    Work.PSU3.StageA.HValueOfRRk hS hC4 hs hs2 hr hr1 hsr hKsub (fun k hk hk1 x hx hc => by
      have h1 : x * k = k * x := by
        have h2 := congrArg (fun z => k * z) hc
        simpa [mul_assoc] using h2
      exact Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t h k hk hk1 x hx h1)⟩

/-- **The assembly.**  The orbit structure and the `d`-values on the representatives give the
target: for `x ∈ Q#` choose `k ∈ Kset` with `k⁻¹ x k ∈ GoodReps`, use `good_conj` and the
`d`-value at the representative. -/
theorem caseB_tQt_subset_of_orbits_and_values (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r)
    (horbit : ∀ x ∈ Q, x ≠ 1 → ∃ k ∈ Work.ThmF.Kset H t, k⁻¹ * x * k ∈ GoodReps H t s r)
    (hvals : ∀ y ∈ GoodReps H t s r, ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q,
      t * y * t = a * k * t * b) :
    ∀ x ∈ Q, x ≠ 1 → ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * x * t = a * k * t * b := by
  intro x hx hx1
  obtain ⟨k, hkK, hkx⟩ := horbit x hx hx1
  have hkH : k ∈ H :=
    (Work.RankOneUniqueness.twoPoint_le_left H t) (Work.ThmF.Kset_subset H t hkK)
  have hconjQ : k⁻¹ * x * k ∈ Q := by
    have hh := ((Subgroup.mem_normalizer_iff.mp (h.normal (H.inv_mem hkH))) x).mp hx
    simpa using hh
  have hx'1 : k⁻¹ * x * k ≠ 1 := by
    intro hcon
    have : x = 1 := by
      have hc := congrArg (fun z : G => k * z * k⁻¹) hcon
      rw [show k * (k⁻¹ * x * k) * k⁻¹ = x from by group] at hc
      simpa using hc
    exact hx1 this
  have hGx : Good h ⟨k⁻¹ * x * k, hconjQ⟩ := (good_iff h hx'1).mpr (hvals _ hkx)
  have hback := (good_conj h hKsub hkK (x := ⟨x, hx⟩) hx1
    (x' := ⟨k⁻¹ * x * k, hconjQ⟩) rfl).mp hGx
  exact (good_iff h hx1).mp hback

theorem caseB_tQt_subset_of_Ksub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {s r : G}
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ∀ x ∈ Q, x ≠ 1 → ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * x * t = a * k * t * b := by
  -- `r ≠ 1`: if `r = 1` the structure identity gives `s = t ∉ H`, contradicting `s ∈ Q ≤ H`
  have hr1 : r ≠ 1 := by
    rintro rfl
    have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
    have h1 : t * s * t = t := by simpa using hsr
    have h2 : s * t = 1 := by
      have h1' : t * (t * s * t) = 1 := by rw [h1, ht2]
      have key : t * (t * s * t) = s * t := by
        rw [show t * (t * s * t) = (t * t) * (s * t) from by group, ht2, one_mul]
      rwa [key] at h1'
    have hs_eq_t : s = t := by
      calc s = s * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = 1 * t := by rw [h2]
        _ = t := one_mul t
    exact hS.split.not_mem (hs_eq_t ▸ hS.split.le hs)
  refine caseB_tQt_subset_of_orbits_and_values hS.split hKsub hs hs2 hr hsr
    (KOrbitsOfQ_full hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub) ?_
  intro y hy
  have hall := caseB_dValue_reps hS hC4 hs hs2 hr hr1 hsr hKsub
  rcases hy with hy | ⟨k, hkK, hk1, rfl⟩
  · rcases (Set.mem_insert_iff.mp hy) with h1 | h1
    · rw [Set.mem_singleton_iff.mp h1]; exact hall.1
    · rcases (Set.mem_insert_iff.mp h1) with h2 | h2
      · rw [Set.mem_singleton_iff.mp h2]; exact hall.2.1
      · rw [Set.mem_singleton_iff.mp h2]; exact hall.2.2.1
  · exact hall.2.2.2 k hkK hk1

end Work.PSU3.StageA
