import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

open Work.Zassenhaus

/-! ## The action of the Borel subgroup

`Work.Zassenhaus.borel G inf = G_∞ = B` acts on `X` by restriction.  The orbit of any
point `zero ≠ inf` is `X ∖ {∞}` (2-pretransitivity), of size `q = |X| - 1`, and the
stabilizer of `zero` inside `B` is the two-point stabilizer `G_{∞,0}`, of size `(q - 1)/2`.
Orbit–stabilizer then gives `|B| = q · (q - 1)/2`. -/

/-- The stabilizer of `zero` in the restricted action of `B = G_∞` on `X` has the same
cardinality as the two-point stabilizer `G_{∞,0} = G_∞ ⊓ G_0`.  The two are identified
elementwise: an element `b ∈ B` fixes `zero` iff its underlying group element lies in both
`G_∞` and `G_0`. -/
theorem natCard_stabilizer_borel {G X : Type} [Group G] [MulAction G X] (inf zero : X) :
    Nat.card (MulAction.stabilizer ↥(borel G inf) zero) =
      Nat.card ↥(MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun b => ⟨b.1.1, b.1.2, ?_⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact b.2
  · exact g.2.2
  · intro b
    rfl
  · intro g
    rfl

/-- The orbit of a point `zero ≠ inf` under `B = G_∞` is the complement of `inf`: an element
of the orbit fixes `inf` and cannot send `zero` to `inf` (as `B` acts by a bijection), while
`2`-pretransitivity applied to the pairs `(zero, inf)` and `(y, inf)` supplies an element of
`B` sending `zero` to any `y ≠ inf`. -/
theorem orbit_borel_eq {G X : Type} [Group G] [Finite G] [MulAction G X] {q : ℕ}
    (h : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero) :
    MulAction.orbit ↥(borel G inf) zero = {x : X | x ≠ inf} := by
  ext y
  constructor
  · intro hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨b, hb⟩ := hy
    intro hyy
    have hbinf : b.1 • inf = inf := b.2
    have h1 : b.1 • zero = inf := by
      have : (b : ↥(borel G inf)) • zero = inf := by rw [hb, hyy]
      exact this
    have : b.1 • zero = b.1 • inf := by rw [h1, hbinf]
    exact hne (MulAction.injective b.1 this).symm
  · intro hy
    rw [MulAction.mem_orbit_iff]
    obtain ⟨g, hgz, hgi⟩ :=
      (MulAction.is_two_pretransitive_iff.mp h.2.2.1) hne.symm hy
    exact ⟨⟨g, hgi⟩, hgz⟩

/-- **Z2 (blueprint §ZASS).** `|B| = q * (q-1)/2`: orbit-stabilizer applied to the transitive
action of `B = G_∞` on `X ∖ {∞}` (orbit of size `q`, point stabilizer the two-point
stabilizer of order `(q-1)/2`, from `ZassHyps2`).  Uses `MulAction.index_stabilizer`.
(Hypothesis amended to `Work.GW2.ZassHyps2`, design pass 2.) -/
theorem card_borel {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero) :
    Nat.card (Work.Zassenhaus.borel G inf) = q * ((q - 1) / 2) := by
  have hcardX : Nat.card X = q + 1 := h.2.1
  -- The two-point stabilizer has order `(q - 1)/2`.
  have hstab : Nat.card ↥(MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero) =
      (q - 1) / 2 := by
    have h5 := h.2.2.2.2 inf zero hne
    rw [← h5]
    exact (Nat.mul_div_right _ (by norm_num : 0 < 2)).symm
  -- The orbit of `zero` under `B` is `X ∖ {∞}`, of size `q`.
  have hcard_orbit : (MulAction.orbit ↥(borel G inf) zero).ncard = q := by
    rw [orbit_borel_eq h hne]
    have hset : {x : X | x ≠ inf} = ({inf} : Set X)ᶜ := by ext x; simp
    rw [hset, Set.ncard_compl, Set.ncard_singleton, hcardX]
    omega
  -- Orbit-stabilizer for the action of `B` on `X`.
  have hidx := MulAction.index_stabilizer (↥(borel G inf)) zero
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(borel G inf) zero)
  rw [hidx, hcard_orbit, natCard_stabilizer_borel (G := G), hstab,
    Nat.mul_comm ((q - 1) / 2) q] at hmul
  exact hmul.symm

end Work.ZASS
