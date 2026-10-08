import Mathlib
import Submission.Work.AppXIDickson.card_eq_one_of_dickson
import Submission.Work.AppXIDickson.field_of_free_comm_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson

/-- **The Dickson step** (App. XI Prop. 2 assembled from `field_of_free_comm_action` (L0) and
`card_eq_one_of_dickson` (B1)).  In the abstract situation of L0, let `y ∈ B` act on `A`
"as an involution" (`φ (y * y) = 1`) but non-trivially (`φ y ≠ 1`), and let `C ≤ A` be a
`φ y`-fixed subgroup of odd order with `|V| = 8·|C| + 1`.  Then `|C| = 1`.

Route.  Apply L0, getting `K`, `e`, `ι` (injective) and `σ : B →* (K ≃+* K)`.  Then `σ y` is an
involutive field automorphism: `σ y * σ y = σ (y * y) = 1`, because `φ (y * y) = 1` and two field
automorphisms agreeing on `ι(A)` are equal (last conjunct of L0); and `σ y ≠ 1` because
`φ y ≠ 1` gives `a : A` with `φ y a ≠ a`, whence `σ y (ι a) = ι (φ y a) ≠ ι a` by injectivity of
`ι`.  The image `C' = Subgroup.map ι C ≤ Kˣ` is a subgroup of odd order
(`Subgroup.card_map_of_injective`) fixed pointwise by `σ y` (`hCfix`), and
`Fintype.card K = Nat.card V = 8·|C'| + 1` (`Nat.card_congr e.toEquiv`,
`Nat.card_eq_fintype_card`).  Now `card_eq_one_of_dickson (σ y) hσ1 hσ2 C' hCodd' hCfix' hcard'`
gives `|C'| = 1`, so `|C| = 1`.  Note `1 < Nat.card V` and `Odd (Nat.card V)` follow from
`hcardV` since `1 ≤ Nat.card C` (a subgroup is nonempty) and
`8 * Nat.card C + 1 = 2 * (4 * Nat.card C) + 1`. -/
theorem dickson_step {V A B : Type} [AddCommGroup V] [Finite V] [CommGroup A] [Finite A]
    [Group B] [DistribMulAction A V] [DistribMulAction B V] (φ : B →* MulAut A)
    (hcompat : ∀ (b : B) (a : A) (v : V), b • (a • v) = (φ b a) • (b • v))
    (hfree : ∀ (a : A) (v : V), v ≠ 0 → a • v = v → a = 1)
    (hbig : Nat.card V ≤ 2 * Nat.card A + 1)
    (y : B) (hy2 : φ (y * y) = 1) (hyne : φ y ≠ 1)
    (C : Subgroup A) (hCodd : Odd (Nat.card C)) (hCfix : ∀ c ∈ C, φ y c = c)
    (hcardV : Nat.card V = 8 * Nat.card C + 1) : Nat.card C = 1 := by
  classical
  -- `C` is nonempty, so it has cardinality at least one
  haveI : Nonempty C := ⟨1⟩
  have hC1 : 1 ≤ Nat.card C := Nat.card_pos
  -- the hypotheses of L0 on `V`
  have hV : 1 < Nat.card V := by omega
  have hoddV : Odd (Nat.card V) := ⟨4 * Nat.card C, by omega⟩
  -- L0
  obtain ⟨K, hKfield, hKft, e, ι, σ, hinj, _he, hsig, heq⟩ :=
    field_of_free_comm_action φ hcompat hV hoddV hfree hbig
  -- `hKfield : Field K` and `hKft : Fintype K` are already usable as typeclass instances
  -- `σ y` is an involution
  have hsq : σ y * σ y = 1 := by
    have h1 : σ (y * y) = 1 := by
      apply heq
      intro a
      rw [hsig (y * y) a, hy2]
      simp
    rwa [map_mul] at h1
  have hσ2 : ∀ k : K, σ y (σ y k) = k := by
    intro k
    have h := congrArg (fun (f : K ≃+* K) => f k) hsq
    simpa using h
  -- `σ y` is not the identity: `φ y ≠ 1` produces `a` with `φ y a ≠ a`
  have hσ1 : σ y ≠ RingEquiv.refl K := by
    obtain ⟨a, ha⟩ : ∃ a : A, φ y a ≠ a := by
      by_contra h
      push_neg at h
      exact hyne (MulEquiv.ext fun a => h a)
    intro h
    apply ha
    have h2 : σ y (ι a : K) = (ι a : K) := by rw [h]; rfl
    rw [hsig y a] at h2
    exact hinj (Units.ext h2)
  -- the image `C' = ι(C) ≤ Kˣ`
  let C' : Subgroup Kˣ := C.map ι
  have hcardC' : Nat.card C' = Nat.card C := Subgroup.card_map_of_injective hinj
  have hCodd' : Odd (Nat.card C') := by rw [hcardC']; exact hCodd
  have hCfix' : ∀ c ∈ C', σ y (c : K) = c := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hc
    rw [hsig y a, hCfix a ha]
  have hcard' : Fintype.card K = 8 * Nat.card C' + 1 := by
    have hKV : Nat.card K = Nat.card V := (Nat.card_congr e.toEquiv).symm
    rw [← Nat.card_eq_fintype_card, hKV, hcardV, hcardC']
  -- B1
  have hC'done : Nat.card C' = 1 :=
    card_eq_one_of_dickson (σ y) hσ1 hσ2 C' hCodd' hCfix' hcard'
  rw [← hcardC', hC'done]

end Work.AppXIDickson
