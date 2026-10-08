import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

open Subgroup

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 0. A fibre-decomposition counting lemma

If `p : α → Prop` selects a set and `f : α → β` is any map, the selected set is the disjoint union
of the fibres of `f`.  (This is the standard "count by fibres" tool, kept local so that the module
depends on Mathlib only.) -/
lemma ncard_eq_sum_ncard_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → Prop) :
    ({x : α | p x} : Set α).ncard =
      ∑ c : β, ({x : α | p x ∧ f x = c} : Set α).ncard := by
  classical
  have h1 : ({x : α | p x} : Set α).ncard = (Finset.univ.filter p).card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [h1]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ.filter p)
    (t := Finset.univ) (by intro a _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [Finset.filter_filter]

/-! ## 1. The sets of subgroups that get counted -/

/-- The conjugates of `P` lying inside `P ⊔ E`. -/
def Sset {G : Type*} [Group G] (P E : Subgroup G) : Set (Subgroup G) :=
  {X : Subgroup G | X ≤ P ⊔ E ∧ ∃ g : G, X = Work.GW2.conjSub g P}

/-- The subgroups of `E` of order `p`. -/
def Tset {G : Type*} [Group G] (E : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {Y : Subgroup G | Y ≤ E ∧ Nat.card Y = p}

/-- The conjugates of `P` lying inside `P ⊔ Y`. -/
def Fib {G : Type*} [Group G] (P Y : Subgroup G) : Set (Subgroup G) :=
  {X : Subgroup G | X ≤ P ⊔ Y ∧ ∃ g : G, X = Work.GW2.conjSub g P}

/-! ## 2. Conjugation preserves `Nat.card` -/

lemma card_conjSub {G : Type*} [Group G] (g : G) (P : Subgroup G) :
    Nat.card (Work.GW2.conjSub g P) = Nat.card P := by
  rw [Work.GW2.conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-! ## 3. The projection `π` and the induced `proj` on subgroups -/

section Projection

variable {G : Type*} [Group G] [Finite G]
variable (P E : Subgroup G) (π : ↥(P ⊔ E) →* ↥E)
variable {p : ℕ}

/-- `π` viewed as a map to the ambient group. -/
noncomputable def pi2 : ↥(P ⊔ E) →* G := (Subgroup.subtype E).comp π

/-- The image of a subgroup of `G` under `π` (a subgroup of `G` contained in `E`). -/
noncomputable def proj (X : Subgroup G) : Subgroup G := (X.subgroupOf (P ⊔ E)).map (pi2 P E π)

lemma pi2_eq_coe_pi (x : ↥(P ⊔ E)) : pi2 P E π x = ((π x : ↥E) : G) := rfl

lemma pi2_mem (x : ↥(P ⊔ E)) : pi2 P E π x ∈ E := (π x).2

lemma proj_le_E (X : Subgroup G) : proj P E π X ≤ E := by
  rw [proj, Subgroup.map_le_iff_le_comap]
  intro x _
  exact pi2_mem P E π x

/-- `x * (π x)⁻¹ ∈ P` is exactly the hypothesis `hπ`, phrased for `pi2`. -/
lemma hpi2 (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P) (x : ↥(P ⊔ E)) :
    (x : G) * (pi2 P E π x)⁻¹ ∈ P := hπ x

/-- The kernel of `π` (i.e. of `pi2`) is `P`. -/
lemma pi2_eq_one_iff (hinf : P ⊓ E = ⊥)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P) (x : ↥(P ⊔ E)) :
    pi2 P E π x = 1 ↔ (x : G) ∈ P := by
  constructor
  · intro h
    have := hpi2 P E π hπ x
    rwa [h, inv_one, mul_one] at this
  · intro hx
    have h1 : pi2 P E π x ∈ P := by
      have hmem := hpi2 P E π hπ x
      have h2 : (pi2 P E π x)⁻¹ ∈ P := by
        have h3 := P.mul_mem (P.inv_mem hx) hmem
        rwa [show (x : G)⁻¹ * ((x : G) * (pi2 P E π x)⁻¹) = (pi2 P E π x)⁻¹ from
          by group] at h3
      simpa using P.inv_mem h2
    have hmem2 : pi2 P E π x ∈ P ⊓ E := Subgroup.mem_inf.mpr ⟨h1, pi2_mem P E π x⟩
    rw [hinf] at hmem2
    exact Subgroup.mem_bot.mp hmem2

/-- `π` fixes `E` pointwise. -/
lemma pi2_eq_of_mem_E (hinf : P ⊓ E = ⊥)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {y : ↥(P ⊔ E)} (hy : (y : G) ∈ E) : pi2 P E π y = (y : G) := by
  have hmem : ((y : G) * (pi2 P E π y)⁻¹) ∈ P ⊓ E :=
    Subgroup.mem_inf.mpr ⟨hpi2 P E π hπ y, E.mul_mem hy (E.inv_mem (pi2_mem P E π y))⟩
  rw [hinf] at hmem
  have h1 : (y : G) * (pi2 P E π y)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  have h2 : (pi2 P E π y)⁻¹ = (y : G)⁻¹ := by
    have h3 := congrArg (fun t => (y : G)⁻¹ * t) h1
    simpa [inv_mul_cancel_left] using h3
  exact inv_injective h2

/-- For `Y ≤ E`, the projection of `P ⊔ Y` is `Y`. -/
lemma pi2_mem_of_mem_sup (hinf : P ⊓ E = ⊥)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {Y : Subgroup G} (hY : Y ≤ E) {x : ↥(P ⊔ E)} (hx : (x : G) ∈ P ⊔ Y) :
    pi2 P E π x ∈ Y := by
  have hle : (P ⊔ Y).subgroupOf (P ⊔ E) ≤ Y.comap (pi2 P E π) := by
    rw [Subgroup.subgroupOf_sup (A := P) (A' := Y) (B := P ⊔ E) le_sup_left
      (le_trans hY le_sup_right)]
    apply sup_le
    · intro z hz
      rw [Subgroup.mem_comap]
      have hzP : (z : G) ∈ P := Subgroup.mem_subgroupOf.mp hz
      rw [show pi2 P E π z = 1 from (pi2_eq_one_iff P E π hinf hπ z).mpr hzP]
      exact Y.one_mem
    · intro z hz
      rw [Subgroup.mem_comap]
      have hzY : (z : G) ∈ Y := Subgroup.mem_subgroupOf.mp hz
      rw [pi2_eq_of_mem_E P E π hinf hπ (hY hzY)]
      exact hzY
  exact hle (Subgroup.mem_subgroupOf.mpr hx)

/-- The image under `π` of a subgroup of `P ⊔ Y` lies in `Y`. -/
lemma proj_le_of_le_sup (hinf : P ⊓ E = ⊥)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {X Y : Subgroup G} (hY : Y ≤ E) (hX : X ≤ P ⊔ Y) : proj P E π X ≤ Y := by
  rw [proj, Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap]
  exact pi2_mem_of_mem_sup P E π hinf hπ hY (hX (Subgroup.mem_subgroupOf.mp hx))

/-- Every `X ≤ P ⊔ E` is contained in `P ⊔ proj X`. -/
lemma le_sup_proj (hinf : P ⊓ E = ⊥)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {X : Subgroup G} (hX : X ≤ P ⊔ E) : X ≤ P ⊔ proj P E π X := by
  intro x hx
  let xh : ↥(P ⊔ E) := ⟨x, hX hx⟩
  have hxeq : x = ((xh : G) * (pi2 P E π xh)⁻¹) * (pi2 P E π xh) := by
    simp only [xh]
    group
  rw [hxeq]
  refine Subgroup.mul_mem_sup (hpi2 P E π hπ xh) ?_
  rw [proj, Subgroup.mem_map]
  exact ⟨xh, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩

/-- If `X ≠ P` has order `p` and `X ≤ P ⊔ E`, then `proj X` also has order `p`. -/
lemma card_proj (hinf : P ⊓ E = ⊥) (hcardP : Nat.card P = p) (hp : p.Prime)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {X : Subgroup G} (hX : Nat.card X = p) (hXne : X ≠ P) (hXH : X ≤ P ⊔ E) :
    Nat.card (proj P E π X) = p := by
  have hdvd : Nat.card (proj P E π X) ∣ p := by
    have h1 : Nat.card (proj P E π X) ∣ Nat.card (X.subgroupOf (P ⊔ E)) :=
      Subgroup.card_map_dvd (X.subgroupOf (P ⊔ E)) (pi2 P E π)
    have h2 : Nat.card (X.subgroupOf (P ⊔ E)) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    rw [h2, hX] at h1
    exact h1
  have hne1 : Nat.card (proj P E π X) ≠ 1 := by
    intro h1
    have hbot : proj P E π X = ⊥ :=
      (Subgroup.eq_of_le_of_card_ge (bot_le : (⊥ : Subgroup G) ≤ proj P E π X)
        (by rw [Subgroup.card_bot, h1])).symm
    have hex : ∃ x ∈ X, x ∉ P := by
      by_contra hcon
      push Not at hcon
      have hle : X ≤ P := fun x hx => hcon x hx
      exact hXne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hX]))
    obtain ⟨x, hxX, hxP⟩ := hex
    have hxH : x ∈ P ⊔ E := hXH hxX
    let xh : ↥(P ⊔ E) := ⟨x, hxH⟩
    have hmem : pi2 P E π xh ∈ proj P E π X := by
      rw [proj, Subgroup.mem_map]
      exact ⟨xh, by rw [Subgroup.mem_subgroupOf]; exact hxX, rfl⟩
    rw [hbot] at hmem
    have h1' : pi2 P E π xh = 1 := Subgroup.mem_bot.mp hmem
    have : (xh : G) ∈ P := (pi2_eq_one_iff P E π hinf hπ xh).mp h1'
    exact hxP this
  rcases hp.eq_one_or_self_of_dvd (Nat.card (proj P E π X)) hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- **The uniqueness of the index of a conjugate.**  If `X ≤ P ⊔ Y` with `X ≠ P` of order `p` and
`Y ≤ E` of order `p`, then `proj X = Y`. -/
lemma proj_eq (hinf : P ⊓ E = ⊥) (hcardP : Nat.card P = p) (hp : p.Prime)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    {Y X : Subgroup G} (hY : Y ≤ E) (hYcard : Nat.card Y = p) (hX : X ≤ P ⊔ Y)
    (hXcard : Nat.card X = p) (hXne : X ≠ P) : proj P E π X = Y := by
  have hXH : X ≤ P ⊔ E := le_trans hX (sup_le le_sup_left (le_trans hY le_sup_right))
  have hle : proj P E π X ≤ Y := proj_le_of_le_sup P E π hinf hπ hY hX
  have hcard : Nat.card (proj P E π X) = p :=
    card_proj P E π hinf hcardP hp hπ hXcard hXne hXH
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hYcard, hcard])

end Projection

/-! ## 4. The main count -/

theorem CountFibre {G : Type} [Group G] [Finite G]
    (P E : Subgroup G) (p p1 : ℕ)
    (hp : p.Prime) (hcardP : Nat.card P = p) (hinf : P ⊓ E = ⊥)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P)
    (hfib : ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = p →
      {X : Subgroup G | X ≤ P ⊔ Y ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard = p1) :
    {X : Subgroup G | X ≤ P ⊔ E ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (p1 - 1) * {Y : Subgroup G | Y ≤ E ∧ Nat.card Y = p}.ncard + 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Subgroup G) := inferInstance
  change (Sset P E).ncard = (p1 - 1) * (Tset E p).ncard + 1
  have hfib' : ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = p → (Fib P Y).ncard = p1 := hfib
  -- `P` lies in every `Fib P Y` (in particular in `Sset P E`).
  have hPmemFy : ∀ Y : Subgroup G, P ∈ Fib P Y := by
    intro Y
    refine ⟨le_sup_left, ⟨1, ?_⟩⟩
    rw [Work.GW2.conjSub]
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by
      ext x; simp [MulAut.conj_apply]]
    exact (Subgroup.map_id P).symm
  have hPmem : P ∈ Sset P E := hPmemFy E
  -- `proj X` lies in `Tset E p` for `X ∈ Sset P E`, `X ≠ P`.
  have hprojT : ∀ X : Subgroup G, X ∈ Sset P E → X ≠ P → proj P E π X ∈ Tset E p := by
    intro X hX hXne
    obtain ⟨hXle, g, hg⟩ := hX
    refine ⟨proj_le_E P E π X, ?_⟩
    have hXcard : Nat.card X = p := by rw [hg, card_conjSub g P, hcardP]
    exact card_proj P E π hinf hcardP hp hπ hXcard hXne hXle
  -- The index type of order-`p` subgroups of `E`.
  let Tt : Type := {Y : Subgroup G // Y ∈ Tset E p}
  haveI : Fintype Tt := Fintype.ofFinite Tt
  have hTtcard : Fintype.card Tt = (Tset E p).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- Step 1: `Sset P E \ {P}` is in bijection with the pairs `(Y, X)`, `Y ∈ Tset E p`,
  -- `X ∈ Fib P Y`, `X ≠ P`.
  have hbi : (Sset P E \ {P}).ncard =
      ({q : Tt × Subgroup G | q.2 ∈ Fib P (q.1 : Subgroup G) ∧ q.2 ≠ P}).ncard := by
    refine Set.ncard_congr (s := Sset P E \ {P})
      (t := {q : Tt × Subgroup G | q.2 ∈ Fib P (q.1 : Subgroup G) ∧ q.2 ≠ P})
      (fun X hX => ?_) ?_ ?_ ?_
    · obtain ⟨hXS, hXnot⟩ := (Set.mem_sdiff X).mp hX
      have hXne : X ≠ P := by simpa using hXnot
      exact ⟨⟨proj P E π X, hprojT X hXS hXne⟩, X⟩
    · rintro X hX
      obtain ⟨hXS, hXnot⟩ := (Set.mem_sdiff X).mp hX
      have hXne : X ≠ P := by simpa using hXnot
      obtain ⟨hXle, g, hg⟩ := hXS
      exact ⟨⟨le_sup_proj P E π hinf hπ hXle, ⟨g, hg⟩⟩, hXne⟩
    · rintro X X' hX hX' heq
      exact congrArg Prod.snd heq
    · rintro ⟨c, X⟩ hq
      obtain ⟨hXfib, hXne⟩ := hq
      have hXfib' : X ∈ Fib P (c : Subgroup G) := hXfib
      have hXne' : X ≠ P := hXne
      obtain ⟨hXle, g, hg⟩ := hXfib'
      have hXleE : X ≤ P ⊔ E := le_trans hXle (sup_le le_sup_left (le_trans c.2.1 le_sup_right))
      have hXcard : Nat.card X = p := by rw [hg, card_conjSub g P, hcardP]
      have hprojeq : proj P E π X = (c : Subgroup G) :=
        proj_eq P E π hinf hcardP hp hπ c.2.1 c.2.2 hXle hXcard hXne'
      refine ⟨X, ⟨⟨hXleE, ⟨g, hg⟩⟩, by simpa using hXne'⟩, ?_⟩
      exact Prod.ext (Subtype.ext hprojeq) rfl
  -- Step 2: decompose the pairs by the first component.
  have hfiber : ({q : Tt × Subgroup G | q.2 ∈ Fib P (q.1 : Subgroup G) ∧ q.2 ≠ P}).ncard =
      ∑ c : Tt, ({X : Subgroup G | X ∈ Fib P (c : Subgroup G) ∧ X ≠ P}).ncard := by
    have hdec := ncard_eq_sum_ncard_fiber (fun q : Tt × Subgroup G => q.1)
      (fun q : Tt × Subgroup G => q.2 ∈ Fib P (q.1 : Subgroup G) ∧ q.2 ≠ P)
    rw [hdec]
    apply Finset.sum_congr rfl
    intro c _
    refine Set.ncard_congr
      (s := {q : Tt × Subgroup G | (q.2 ∈ Fib P (q.1 : Subgroup G) ∧ q.2 ≠ P) ∧ q.1 = c})
      (t := {X : Subgroup G | X ∈ Fib P (c : Subgroup G) ∧ X ≠ P})
      (fun q _ => q.2) ?_ ?_ ?_
    · rintro ⟨d, X⟩ ⟨⟨hXfib, hXne⟩, hdc⟩
      have hXfib' : X ∈ Fib P (d : Subgroup G) := hXfib
      have hXne' : X ≠ P := hXne
      have hd : d = c := hdc
      rw [hd] at hXfib'
      exact ⟨hXfib', hXne'⟩
    · rintro ⟨d1, X1⟩ ⟨d2, X2⟩ ⟨⟨hXfib1, hXne1⟩, hdc1⟩ ⟨⟨hXfib2, hXne2⟩, hdc2⟩ hval
      have hval' : X1 = X2 := hval
      have hdc1' : d1 = c := hdc1
      have hdc2' : d2 = c := hdc2
      simp only [Prod.mk.injEq]
      exact ⟨hdc1'.trans hdc2'.symm, hval'⟩
    · rintro X ⟨hXfib, hXne⟩
      refine ⟨(c, X), ⟨⟨?_, hXne⟩, rfl⟩, rfl⟩
      exact hXfib
  -- Step 3: every fibre has `p1 - 1` elements.
  have hfibc : ∀ c : Tt, ({X : Subgroup G | X ∈ Fib P (c : Subgroup G) ∧ X ≠ P}).ncard = p1 - 1 := by
    intro c
    have hsub : ({P} : Set (Subgroup G)) ⊆ Fib P (c : Subgroup G) := by
      intro X hX
      rw [Set.mem_singleton_iff] at hX
      rw [hX]
      exact hPmemFy _
    have hset : {X : Subgroup G | X ∈ Fib P (c : Subgroup G) ∧ X ≠ P} =
        Fib P (c : Subgroup G) \ {P} := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    rw [hset, Set.ncard_sdiff hsub, Set.ncard_singleton, hfib' (c : Subgroup G) c.2.1 c.2.2]
  have hsum : (∑ c : Tt, ({X : Subgroup G | X ∈ Fib P (c : Subgroup G) ∧ X ≠ P}).ncard) =
      (Tset E p).ncard * (p1 - 1) := by
    simp_rw [hfibc]
    rw [Finset.sum_const, Finset.card_univ, hTtcard]
    simp
  -- Step 4: add back the element `P`.
  have hsplit : (Sset P E).ncard = (Sset P E \ {P}).ncard + 1 :=
    (Set.ncard_sdiff_singleton_add_one hPmem).symm
  rw [hsplit, hbi, hfiber, hsum]
  rw [Nat.mul_comm (Tset E p).ncard (p1 - 1)]

end Work.CORE4
