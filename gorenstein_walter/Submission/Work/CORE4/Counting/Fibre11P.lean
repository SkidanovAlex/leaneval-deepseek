import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CountFibre
import Submission.Work.CORE4.ProjOfInfBot

/-!
# Fibre decomposition of the conjugates of `P` inside `P ⊔ E`

`Fibre11P` is Bender §4 (11)'s counting step: if `P` has prime order `p`, `P` commutes
elementwise with `E` and `P ⊓ E = ⊥`, and every `(p,p)`-group `P ⊔ Y` (`Y ≤ E` of order `p`)
contains exactly `p₁` conjugates of `P`, then `P ⊔ E` contains

    (p₁ - 1) · #{Y ≤ E : |Y| = p} + 1

conjugates of `P`.

This is assembled from the two library lemmas already proved in area `CORE4`:

* `Work.CORE4.ProjOfInfBot` — since `P` commutes with `E` and `P ⊓ E = ⊥`, the group `P ⊔ E`
  is the internal direct product of `P` and `E`, so there is a projection
  `π : ↥(P ⊔ E) →* ↥E` that is the identity on `E` and trivial on `P`;
* `Work.CORE4.CountFibre` — the fibre decomposition itself, which needs only `π` together with
  the identity `x · (π x)⁻¹ ∈ P`.

The only remaining glue is (a) `π` satisfies `x · (π x)⁻¹ ∈ P`, and (b) the two occurrences of
the hypothesis/conclusion in the present statement, which additionally demand `Nat.card X = p`,
are equivalent to the corresponding sets in `CountFibre`, the cardinality hypothesis being
redundant because `X = g P g⁻¹` forces `Nat.card X = Nat.card P = p`.
-/

namespace Work.CORE4.Counting

open Subgroup

/-- Every element of `P ⊔ E` is a product `p * e` with `p ∈ P`, `e ∈ E`, when `P` and `E`
commute elementwise. -/
private theorem mem_sup_prod {G : Type} [Group G] (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    ∀ x : G, x ∈ (P ⊔ E : Subgroup G) ↔ ∃ p ∈ P, ∃ e ∈ E, p * e = x := by
  have hPcent : ∀ x ∈ P, x ∈ Subgroup.centralizer (E : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr (fun h hh => (hcomm x hx h hh).symm)
  have hLE : P ≤ Subgroup.normalizer (E : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer (E : Set G) (hPcent x hx)
  intro x
  constructor
  · intro hx
    have hx' : x ∈ (↑(P ⊔ E) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P E hLE] at hx'
    exact Set.mem_mul.mp hx'
  · rintro ⟨p, hp, e, he, rfl⟩
    exact Subgroup.mul_mem_sup hp he

theorem Fibre11P {G : Type} [Group G] [Finite G]
    (P E : Subgroup G) (p p1 : ℕ) (hp : p.Prime)
    (hcardP : Nat.card P = p) (hPE : P ⊓ E = ⊥)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hbase : ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = p →
      {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ Y ∧
        (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = p1) :
    {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ E ∧
      (∃ g : G, X = Work.GW2.conjSub g P)}.ncard =
      (p1 - 1) * {Y : Subgroup G | Y ≤ E ∧ Nat.card Y = p}.ncard + 1 := by
  classical
  -- A conjugate of `P` has cardinality `p`.
  have hcard_conj : ∀ g : G, Nat.card (Work.GW2.conjSub g P) = p := fun g => by
    rw [Work.CORE4.card_conjSub g P, hcardP]
  -- The projection onto the `E`-factor of the internal direct product `P ⊔ E`.
  obtain ⟨π, hπval⟩ := Work.CORE4.ProjOfInfBot P E hcomm hPE
  -- The projection identity `x · (π x)⁻¹ ∈ P` required by `CountFibre`.
  have hπ : ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P := by
    intro x
    obtain ⟨p, hp', e, he, hpe⟩ := (mem_sup_prod P E hcomm x).mp x.2
    have hxe : x = ⟨p * e, Subgroup.mul_mem_sup hp' he⟩ := Subtype.ext hpe.symm
    rw [hxe, hπval p hp' e he]
    show (p * e) * e⁻¹ ∈ P
    rw [show p * e * e⁻¹ = p from by group]
    exact hp'
  -- The hypothesis of `CountFibre` is the present `hbase` up to the redundant `Nat.card` clause.
  have hFib : ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = p →
      (Work.CORE4.Fib P Y).ncard = p1 := by
    intro Y hYE hYc
    have hset : {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ Y ∧
        (∃ g : G, X = Work.GW2.conjSub g P)} = Work.CORE4.Fib P Y := by
      ext X
      constructor
      · rintro ⟨-, hle, hconj⟩
        exact ⟨hle, hconj⟩
      · rintro ⟨hle, g, hg⟩
        exact ⟨by rw [hg, hcard_conj g], hle, ⟨g, hg⟩⟩
    have := hbase Y hYE hYc
    rwa [hset] at this
  -- The conclusion is the `CountFibre` conclusion up to the same redundant `Nat.card` clause.
  have hSset : {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ E ∧
      (∃ g : G, X = Work.GW2.conjSub g P)} = Work.CORE4.Sset P E := by
    ext X
    constructor
    · rintro ⟨-, hle, hconj⟩
      exact ⟨hle, hconj⟩
    · rintro ⟨hle, g, hg⟩
      exact ⟨by rw [hg, hcard_conj g], hle, ⟨g, hg⟩⟩
  rw [hSset]
  exact Work.CORE4.CountFibre P E p p1 hp hcardP hPE hcomm π hπ hFib

end Work.CORE4.Counting
