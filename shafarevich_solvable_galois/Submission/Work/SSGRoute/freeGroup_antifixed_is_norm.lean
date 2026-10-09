import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Anti-fixed elements of a free group with a fixed-point-free involution are norms

Let `X` be a type with a fixed-point-free involution `σ`, `F = FreeGroup X` and `Φ = freeGroupCongr σ`
the induced automorphism of `F`.  If `w ∈ F` satisfies `Φ w = w⁻¹` then `w = (Φ v)⁻¹ * v` for some
`v ∈ F`.

The proof works on the reduced word `L = w.toWord`.  Applying `toWord` (or, equivalently, the
relation `mk L = w`) to `Φ w = w⁻¹` one obtains

  `L.map (fun p => (σ p.1, p.2)) = FreeGroup.invRev L`   (`*`)

which says that `L` is the reverse-flip of its own `σ`-image.  From `*`:

* `L.length` is even: the middle letter of an odd-length word would satisfy `σ x = x` for its
  `X`-component, contradicting fixed-point-freeness;
* writing `m = L.length / 2` and splitting `L = L.take m ++ L.drop m`, identity `*` gives
  `(L.drop m).map (fun p => (σ p.1, p.2)) = FreeGroup.invRev (L.take m)`.

Then `v := FreeGroup.mk (L.drop m)` is the required half word: the last identity inverts to
`Φ v = (FreeGroup.mk (L.take m))⁻¹`, and `mk (L.take m) * mk (L.drop m) = mk L = w`.
-/

namespace Work.SSGRoute

open FreeGroup

private lemma reduce_map_of_injective {X Y : Type*} [DecidableEq X] [DecidableEq Y] (f : X → Y)
    (hf : Function.Injective f) (L : List (X × Bool)) :
    FreeGroup.reduce (L.map (fun p => (f p.1, p.2)))
      = (FreeGroup.reduce L).map (fun p => (f p.1, p.2)) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, FreeGroup.reduce.cons (f hd.1, hd.2), ih, FreeGroup.reduce.cons hd]
    cases hred : FreeGroup.reduce tl with
    | nil => simp
    | cons h2 t2 =>
      simp only [List.map_cons]
      by_cases hc : hd.1 = h2.1 ∧ hd.2 = !h2.2
      · have hc' : (f hd.1 = f h2.1) ∧ (hd.2 = !h2.2) := ⟨by rw [hc.1], hc.2⟩
        rw [if_pos hc, if_pos hc']
      · have hc' : ¬ ((f hd.1 = f h2.1) ∧ (hd.2 = !h2.2)) := fun h => hc ⟨hf h.1, h.2⟩
        rw [if_neg hc, if_neg hc']
        simp

/-- A `σ`-palindrome has even length: the middle letter of an odd-length `σ`-palindrome would have
to be `σ`-fixed. -/
private lemma gmap_even_length {X : Type*} (σ : X ≃ X) (hfree : ∀ x, σ x ≠ x)
    (L : List (X × Bool))
    (hL : L.map (fun p => (σ p.1, p.2)) = FreeGroup.invRev L) : Even L.length := by
  rw [FreeGroup.invRev] at hL
  rw [← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨k, hk⟩ := hodd
  have hklt : k < L.length := by omega
  have h2 : (L.map (fun p => (σ p.1, p.2)))[k]? = ((L.map (fun p => (p.1, !p.2))).reverse)[k]? := by
    rw [hL]
  rw [List.getElem?_map] at h2
  have hklt_map : k < (L.map (fun p => (p.1, !p.2))).length := by
    rw [List.length_map]; omega
  rw [List.getElem?_reverse hklt_map] at h2
  rw [List.length_map] at h2
  have hidx : L.length - 1 - k = k := by omega
  rw [hidx] at h2
  rw [List.getElem?_map, List.getElem?_eq_getElem hklt] at h2
  rw [Option.map_some, Option.map_some] at h2
  exact hfree (L[k]'hklt).1 (congrArg Prod.fst (Option.some.inj h2))

/-- Splitting a `σ`-palindrome into its two halves: the `σ`-image of the second half is the word
inverse of the first half. -/
private lemma gmap_take_drop {X : Type*} (σ : X ≃ X) (m : ℕ) (L : List (X × Bool))
    (hLen : L.length = 2 * m)
    (hL : L.map (fun p => (σ p.1, p.2)) = FreeGroup.invRev L) :
    (L.drop m).map (fun p => (σ p.1, p.2)) = FreeGroup.invRev (L.take m) := by
  have hlen : L.length - m = m := by omega
  calc (L.drop m).map (fun p => (σ p.1, p.2))
      = (L.map (fun p => (σ p.1, p.2))).drop m := List.map_drop
    _ = ((L.map (fun p => (p.1, !p.2))).reverse).drop m := by rw [hL, FreeGroup.invRev]
    _ = ((L.map (fun p => (p.1, !p.2))).take (L.length - m)).reverse := by
          rw [List.drop_reverse, List.length_map]
    _ = ((L.map (fun p => (p.1, !p.2))).take m).reverse := by rw [hlen]
    _ = ((L.take m).map (fun p => (p.1, !p.2))).reverse := by rw [List.map_take]
    _ = FreeGroup.invRev (L.take m) := by rw [FreeGroup.invRev]

theorem freeGroup_antifixed_is_norm {X : Type*} (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (w : FreeGroup X)
    (hw : FreeGroup.freeGroupCongr σ w = w⁻¹) :
    ∃ v : FreeGroup X, w = (FreeGroup.freeGroupCongr σ v)⁻¹ * v := by
  classical
  -- The reduced word of `w` is the reverse-flip of its own `σ`-image.
  have hL : (w.toWord).map (fun p => (σ p.1, p.2)) = FreeGroup.invRev w.toWord := by
    have h2 : FreeGroup.mk ((w.toWord).map (fun p => (σ p.1, p.2)))
        = FreeGroup.mk (FreeGroup.invRev w.toWord) := by
      rw [← FreeGroup.map.mk (L := w.toWord) (f := σ), FreeGroup.mk_toWord]
      rw [show FreeGroup.map σ w = w⁻¹ from hw, ← FreeGroup.inv_mk, FreeGroup.mk_toWord]
    have h3 := FreeGroup.reduce.sound h2
    rw [reduce_map_of_injective σ σ.injective (w.toWord), FreeGroup.reduce_invRev,
        FreeGroup.IsReduced.reduce_eq (FreeGroup.isReduced_toWord (x := w))] at h3
    exact h3
  -- The length of `L` is even.
  obtain ⟨m, hm⟩ : ∃ m, (w.toWord).length = 2 * m := by
    obtain ⟨k, hk⟩ := gmap_even_length σ hfree (w.toWord) hL
    exact ⟨k, by omega⟩
  -- The half-word identity.
  have hsplit : ((w.toWord).drop m).map (fun p => (σ p.1, p.2))
      = FreeGroup.invRev ((w.toWord).take m) :=
    gmap_take_drop σ m (w.toWord) hm hL
  refine ⟨FreeGroup.mk ((w.toWord).drop m), ?_⟩
  rw [show FreeGroup.freeGroupCongr σ (FreeGroup.mk ((w.toWord).drop m))
        = FreeGroup.mk (((w.toWord).drop m).map (fun p => (σ p.1, p.2))) from
        FreeGroup.map.mk (L := (w.toWord).drop m) (f := σ),
      hsplit, FreeGroup.inv_mk, FreeGroup.invRev_invRev, FreeGroup.mul_mk]
  conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
  rw [List.take_append_drop]

end Work.SSGRoute
