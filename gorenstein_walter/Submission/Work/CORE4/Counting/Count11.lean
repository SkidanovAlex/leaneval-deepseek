import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Counting.Fibre11

/-!
# Bender §4 (11): the count `(p₁ − 1) q k′` of conjugates of `P` inside `P · E(M)`

Bender 1981, §4 (11) (p. 227):

> As `E` has cyclic `S_p`-subgroups and has `q k′` subgroups of order `p`, `P × E` contains
> `(p₁ − 1) q k′` conjugates `X ≠ P` of `P`.

This file assembles (11) from three independent inputs:

* `Work.CORE4.Counting.Fibre11` — the fibre decomposition: the conjugates of `P` inside `P ⊔ E`
  other than `P` are partitioned by the order-`p` subgroups `Y ≤ E`, the fibre over `Y` being the
  set of order-`p` subgroups of `P ⊔ Y`; if each fibre contains `p₁` conjugates of `P`, the total
  is `1 + (p₁ − 1)·#{Y ≤ E : |Y| = p}`.
* `fibreCount_conj_eq` (below) — **uniformity**: all the `(p,p)`-groups `P ⊔ Y` (`Y ≤ E` of order
  `p`) contain the same number of conjugates of `P`.  This uses that `E` acts transitively on its
  order-`p` subgroups (Bender's "`E` has cyclic `S_p`-subgroups") and that `P` commutes with `E`,
  so conjugation by `e ∈ E` fixes `P` and sends `P ⊔ Y` to `P ⊔ Y^e`.
* the count `#{Y ≤ E : |Y| = p} = q k′` (Bender §4 (11), first half) — supplied by the caller
  (`Work.CORE4.L2PrimeCountTransfer` in the §4 configuration).
-/

namespace Work.CORE4.Counting

open Subgroup

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary transport lemmas for `conjSub` -/

/-- Conjugation of subgroups by a fixed `g` is injective (with inverse conjugation by `g⁻¹`). -/
theorem conjSub_injective (g : G) :
    Function.Injective (fun K : Subgroup G => Work.GW2.conjSub g K) := by
  intro A B h
  have h1 : A.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj g).toMonoidHom := h
  have h2 := congrArg (fun K : Subgroup G => K.map (MulAut.conj g⁻¹).toMonoidHom) h1
  rw [Subgroup.map_map, Subgroup.map_map] at h2
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    show (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id, Subgroup.map_id] at h2
  exact h2

/-- `Set.ncard` is invariant under conjugation of subgroups. -/
theorem ncard_conjSub_image (g : G) (s : Set (Subgroup G)) :
    (Work.GW2.conjSub g '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s (conjSub_injective g)

/-- `conjSub (a * b) K = conjSub a (conjSub b K)`. -/
theorem conjSub_mul (a b : G) (K : Subgroup G) :
    Work.GW2.conjSub (a * b) K = Work.GW2.conjSub a (Work.GW2.conjSub b K) := by
  have hcomp : (MulAut.conj (a * b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
    ext x
    show (MulAut.conj (a * b)) x = (MulAut.conj a) ((MulAut.conj b) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, hcomp, Subgroup.map_map]

/-- `conjSub g⁻¹ (conjSub g K) = K`. -/
theorem conjSub_inv_conjSub (g : G) (K : Subgroup G) :
    Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g K) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hyx, ← hzy]
    have h : (MulAut.conj g⁻¹) ((MulAut.conj g) z) = z := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    change (MulAut.conj g⁻¹) ((MulAut.conj g) z) ∈ K
    rw [h]
    exact hz
  · intro hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj g) x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

/-- Conjugation sends a supremum to the supremum of the images. -/
theorem conjSub_sup (g : G) (A B : Subgroup G) :
    Work.GW2.conjSub g (A ⊔ B) = Work.GW2.conjSub g A ⊔ Work.GW2.conjSub g B := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_sup]

/-- Conjugation preserves the order of a subgroup. -/
theorem conjSub_card (g : G) (K : Subgroup G) :
    Nat.card ↥(Work.GW2.conjSub g K) = Nat.card ↥K := by
  rw [Work.GW2.conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- `P` is fixed by conjugation by any `e ∈ E` when `P` commutes elementwise with `E`. -/
theorem conjSub_eq_self_of_mem (P E : Subgroup G)
    (hcent : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) {e : G} (he : e ∈ E) :
    Work.GW2.conjSub e P = P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show e * y * e⁻¹ ∈ P
    have : e * y * e⁻¹ = y := by rw [← hcent y hy e he]; group
    rw [this]; exact hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    show e * x * e⁻¹ = x
    rw [← hcent x hx e he]
    group

/-! ## Uniformity of the fibre counts -/

/-- The **fibre** over an order-`p` subgroup `Y`: the set of order-`p` conjugates of `P` inside
the `(p,p)`-group `P ⊔ Y`. -/
def conjIn (P Y : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ Y ∧ ∃ g : G, X = Work.GW2.conjSub g P}

/-- **Uniformity of the fibre counts.**  If `E` acts transitively on its order-`p` subgroups,
`P` commutes elementwise with `E` and `Kp ≤ E` has order `p`, then for *every* order-`p`
subgroup `Y ≤ E` the `(p,p)`-group `P ⊔ Y` contains exactly as many conjugates of `P` as
`P ⊔ Kp` does. -/
theorem fibreCount_conj_eq (P E Kp : Subgroup G) (p : ℕ)
    (hcent : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hconj : ∀ Y : Subgroup G, Y ≤ E → Nat.card ↥Y = p →
      ∃ e ∈ E, Y = Work.GW2.conjSub e Kp) :
    ∀ Y : Subgroup G, Y ≤ E → Nat.card ↥Y = p →
      (conjIn P Y p).ncard = (conjIn P Kp p).ncard := by
  intro Y hYE hYcard
  obtain ⟨e, heE, rfl⟩ := hconj Y hYE hYcard
  have hsup : P ⊔ Work.GW2.conjSub e Kp = Work.GW2.conjSub e (P ⊔ Kp) := by
    rw [conjSub_sup, conjSub_eq_self_of_mem P E hcent heE]
  have himage : Work.GW2.conjSub e '' conjIn P Kp p = conjIn P (Work.GW2.conjSub e Kp) p := by
    ext X
    constructor
    · rintro ⟨Z, ⟨hZcard, hZle, g, hZg⟩, rfl⟩
      refine ⟨?_, ?_, e * g, ?_⟩
      · rw [conjSub_card]; exact hZcard
      · rw [hsup]; exact Subgroup.map_mono hZle
      · rw [hZg, conjSub_mul]
    · rintro ⟨hXcard, hXle, g, hXg⟩
      refine ⟨Work.GW2.conjSub e⁻¹ X, ⟨?_, ?_, e⁻¹ * g, ?_⟩, ?_⟩
      · rw [conjSub_card]; exact hXcard
      · have h2 : (P ⊔ Work.GW2.conjSub e Kp).map (MulAut.conj e⁻¹).toMonoidHom = P ⊔ Kp := by
          rw [← Work.GW2.conjSub, conjSub_sup, conjSub_inv_conjSub,
            conjSub_eq_self_of_mem P E hcent (E.inv_mem heE)]
        exact h2 ▸ Subgroup.map_mono hXle
      · rw [hXg, conjSub_mul]
      · have h1 := conjSub_inv_conjSub e⁻¹ X
        rwa [inv_inv] at h1
  rw [← himage, ncard_conjSub_image]

/-! ## Bender §4 (11) -/

/-- **Bender §4 (11).**  If `P ≤ G` has prime order `p`, `E ≤ G` contains the order-`p` subgroup
`Kp`, `P` commutes elementwise with `E` and meets `E` trivially, `E` acts transitively on its
order-`p` subgroups, and `P ⊔ Kp` (the `(p,p)`-group `A` of Bender's notation) contains exactly
`p1` conjugates of `P`, then the whole of `P ⊔ E` contains `(p1 - 1) * qk' + 1` conjugates of `P`,
where `qk'` is the number of order-`p` subgroups of `E`. -/
theorem Count11 (P E Kp : Subgroup G) (p p1 qk' : ℕ) (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hcardKp : Nat.card ↥Kp = p)
    (hKpE : Kp ≤ E) (hPE : P ⊓ E = ⊥)
    (hcent : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hconj : ∀ Y : Subgroup G, Y ≤ E → Nat.card ↥Y = p →
      ∃ e ∈ E, Y = Work.GW2.conjSub e Kp)
    (hbase : (conjIn P Kp p).ncard = p1)
    (hcount : {Y : Subgroup G | Y ≤ E ∧ Nat.card ↥Y = p}.ncard = qk') :
    {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ E ∧
      (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = (p1 - 1) * qk' + 1 := by
  have hunif := fibreCount_conj_eq P E Kp p hcent hconj
  have hbase' : ∀ Y : Subgroup G, Y ≤ E → Nat.card ↥Y = p →
      {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ Y ∧
        (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = p1 :=
    fun Y hYE hYc => (hunif Y hYE hYc).trans hbase
  have := Fibre11 P E p p1 hp hcardP hPE hcent hbase'
  rw [hcount] at this
  exact this

end Work.CORE4.Counting
