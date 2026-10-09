import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

open scoped commutatorElement

/-! ## Auxiliary lemmas

Two facts are used in the proof of `mag2_commutator_of`:

* `degq_eq_red2_degPart_of_sub_mem_filq` — the mod-`2` degree-`j` component of a class in the
  truncation `FreeAssoc X ⧸ fil X 5` is computed by the degree-`j` part of *any* lift, as soon as
  the lift is correct modulo a filtration piece `filq X 5 k` with `k > j`;
* `red2_degPart_two_commutator` — the explicit degree-`2` computation for the algebra commutator of
  two letters.
-/

/-- **The mod-`2` degree-`j` component is determined by any lift modulo a deeper filtration
piece.**  If `u ∈ FreeAssoc X ⧸ fil X 5` agrees with the class of `a : FreeAssoc X` modulo
`filq X 5 k` (the image of `fil X k`), and `j < 5`, `j < k`, then the degree-`j` part of `a`
computes `degq j X u`. -/
theorem degq_eq_red2_degPart_of_sub_mem_filq {X : Type} {j k : ℕ} (hj : j < 5) (hjk : j < k)
    {u : FreeAssoc X ⧸ fil X 5} {a : FreeAssoc X}
    (h : u - Ideal.Quotient.mk (fil X 5) a ∈ filq X 5 k) :
    degq j X u = red2 X (degPart j a) := by
  -- lift the difference `u - mk a` to `s ∈ fil X k`
  obtain ⟨s, hs, hse⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X 5))
    (Ideal.Quotient.mk_surjective)).1 h
  have hu : u = Ideal.Quotient.mk (fil X 5) (a + s) := by
    rw [map_add, hse]
    abel
  rw [hu, degq_mk hj X (a + s), map_add, degPart_eq_zero_of_mem_fil hs hjk, add_zero]

/-- **The degree-`2` part of the algebra commutator of two letters, reduced mod `2`.** -/
theorem red2_degPart_two_commutator {X : Type} (x y : X) :
    red2 X (degPart 2 (wordEl [x] * wordEl [y] - wordEl [y] * wordEl [x]))
      = brk X (flg_ltr X x) (flg_ltr X y) := by
  have hA : wordEl [x] * wordEl [y]
      = MonoidAlgebra.single (FreeMonoid.of x * FreeMonoid.of y) (1 : ℤ) := by
    simp only [wordEl, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one,
      MonoidAlgebra.single_mul_single]
  have hB : wordEl [y] * wordEl [x]
      = MonoidAlgebra.single (FreeMonoid.of y * FreeMonoid.of x) (1 : ℤ) := by
    simp only [wordEl, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one,
      MonoidAlgebra.single_mul_single]
  have hlen1 : (FreeMonoid.of x * FreeMonoid.of y).length = 2 := by
    rw [FreeMonoid.length_mul, FreeMonoid.length_of, FreeMonoid.length_of]
  have hlen2 : (FreeMonoid.of y * FreeMonoid.of x).length = 2 := by
    rw [FreeMonoid.length_mul, FreeMonoid.length_of, FreeMonoid.length_of]
  rw [hA, hB, map_sub, degPart_single, degPart_single, if_pos hlen1, if_pos hlen2,
    map_sub, red2_single, red2_single]
  have h1 : MonoidAlgebra.single (FreeMonoid.of x * FreeMonoid.of y) ((1 : ℤ) : ZMod 2)
      = flg_ltr X x * flg_ltr X y := by
    rw [show ((1 : ℤ) : ZMod 2) = 1 from by norm_num]
    rw [flg_ltr, flg_ltr, MonoidAlgebra.single_mul_single, mul_one]
  have h2 : MonoidAlgebra.single (FreeMonoid.of y * FreeMonoid.of x) ((1 : ℤ) : ZMod 2)
      = flg_ltr X y * flg_ltr X x := by
    rw [show ((1 : ℤ) : ZMod 2) = 1 from by norm_num]
    rw [flg_ltr, flg_ltr, MonoidAlgebra.single_mul_single, mul_one]
  rw [h1, h2, brk, sub_eq_add_neg, neg_eq_self_zmodTwo]

/-- **The degree-`2` class of a commutator of two generators.**

`mag2 X z` (defined in `Submission/Work/SSGRoute/magFourDefs.lean`) is the mod-`2` degree-`2`
component of the Magnus image of `z` at truncation `5`, and `brk X a b = a * b + b * a`.  For two
letters `x y : X` one has
`mag2 X (of x * of y * (of x)⁻¹ * (of y)⁻¹) = brk X (flg_ltr X x) (flg_ltr X y)`
(the first argument is Mathlib's group commutator `⁅of x, of y⁆`, written out to avoid the scoped
bracket notation in the statement).

Proof route: `prop5.magLead_commutator 5 1 1 (by norm_num) (by norm_num) (by norm_num)` applied to
`u = FreeGroup.of x`, `v = FreeGroup.of y` (both lie in `lowerCentralSeries 0 = ⊤`) gives
`magLead 5 ⁅of x, of y⁆ - (magLead 5 (of x) * magLead 5 (of y) - magLead 5 (of y) * magLead 5 (of x)) ∈ filq X 5 3`;
`prop5.magLead_of` identifies `magLead 5 (of x) = mk (wordEl [x])`; `wordEl [x] * wordEl [y] - wordEl [y] * wordEl [x]`
is homogeneous of degree `2`; and `filq X 5 3` is killed by `degPart 2`, so `mag2` (which is
`red2 ∘ degPart 2 ∘ Quotient.out`) of the commutator equals `red2` of that degree-`2` element, which
is `brk X (flg_ltr X x) (flg_ltr X y)` because `-1 = 1` in `ZMod 2`. -/
theorem mag2_commutator_of (X : Type) (x y : X) :
    mag2 X (FreeGroup.of x * FreeGroup.of y * (FreeGroup.of x)⁻¹ * (FreeGroup.of y)⁻¹)
      = brk X (flg_ltr X x) (flg_ltr X y) := by
  rw [← commutatorElement_def]
  -- the group commutator `⁅of x, of y⁆` and the ring commutator agree modulo `filq X 5 3`
  have hcomm := magLead_commutator (X := X) 5 1 1 (by norm_num) (by norm_num) (by norm_num)
    (u := FreeGroup.of x) (v := FreeGroup.of y) (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [magLead_of, magLead_of] at hcomm
  have hma : (Ideal.Quotient.mk (fil X 5))
        (wordEl [x] * wordEl [y] - wordEl [y] * wordEl [x])
      = (Ideal.Quotient.mk (fil X 5)) (wordEl [x]) * (Ideal.Quotient.mk (fil X 5)) (wordEl [y])
        - (Ideal.Quotient.mk (fil X 5)) (wordEl [y])
          * (Ideal.Quotient.mk (fil X 5)) (wordEl [x]) := by
    rw [map_sub, map_mul, map_mul]
  rw [← hma] at hcomm
  -- `mag2` is the degree-`2` component of the Magnus leading term
  change degq 2 X (magLead 5 ⁅FreeGroup.of x, FreeGroup.of y⁆)
    = brk X (flg_ltr X x) (flg_ltr X y)
  rw [degq_eq_red2_degPart_of_sub_mem_filq (j := 2) (k := 3) (by norm_num) (by norm_num) hcomm]
  exact red2_degPart_two_commutator x y

end Work.SSGRoute.CC
