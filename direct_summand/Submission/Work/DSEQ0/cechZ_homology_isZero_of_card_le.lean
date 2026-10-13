import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.cech_level
import Submission.Work.DSEQ0.cech_raise
import Submission.Work.DSEQ0.cechZ_of_cech_isZero
import Submission.Work.DSEQ0.cech_homology_isZero_of_isEmpty

namespace Work.DSEQ0

/-! **The vanishing half of the Cech coherence statement.**  For *any* family of opens
`U : ι → X.Opens` (`ι` finite) of a scheme over `A` — no projectivity, no Noetherian hypothesis —
the homology of the unnormalised Cech complex `DSMap.cechZ A X f U` vanishes in degrees
`i ≥ Nat.card ι`.

Route (the "image size" filtration): the degree-`q` term of `DSMap.cechZ` is the product over
*all* maps `x : Fin (q+1) → ι` of `Γ(X, ⋂_a U (x a))`, and the differential is the alternating sum
of the deletion cofaces.  Because `Γ(X, ⋂_a U (x a))` depends only on the *image* of `x`, putting
`F^r = {c | c_x = 0 unless r ≤ |im x|} ⊆ Č` gives a decreasing filtration by subcomplexes
(deleting a position cannot increase the image), `0 = F^{|ι|+1} ⊆ F^{|ι|} ⊆ ⋯ ⊆ F^0 = Č`.  The
graded pieces are, for each `S ⊆ ι` with `|S| = r`, the *surjective* complex with *constant*
coefficients `Γ(X, ⋂_{i ∈ S} U i)`.  By `Work.DSEQ0.surjCech_vanishing`, such a complex has
`H^n = 0` for `n ≥ r`.  The long exact sequences of `0 → F^{r+1} → F^r → gr^r → 0` then give, by
descending induction on `r` (base `F^{|ι|+1} = 0`), `H^n(F^r) = 0` for all `n ≥ |ι|`, hence
`H^n(Č) = 0` for `n ≥ |ι|`. -/

universe a

/-- The `ℕ`-indexed vanishing statement, in the case of a nonempty index type: this is the
image-size filtration argument (`Work.DSEQ0.cech_homology_isZero_succ`), starting the count at
degree `1`. -/
theorem cech_homology_isZero_of_card_le_of_nonempty {A : Type a} [CommRing A]
    {X : AlgebraicGeometry.Scheme.{a}} (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} [Fintype ι] (U : ι → X.Opens) (hcard : 1 ≤ Nat.card ι) :
    ∀ n : ℕ, Nat.card ι ≤ n →
      CategoryTheory.Limits.IsZero ((DSMap.cech A X f U).homology n) := by
  intro n hn
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact cech_homology_isZero_succ A X f U K (by omega)

theorem cechZ_homology_isZero_of_card_le {A : Type a} [CommRing A]
    {X : AlgebraicGeometry.Scheme.{a}} (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type a} [Finite ι] (U : ι → X.Opens) :
    ∀ i : ℤ, (Nat.card ι : ℤ) ≤ i →
      CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  by_cases hem : IsEmpty ι
  · haveI : IsEmpty ι := hem
    exact cechZ_of_cech_isZero f U
      (fun n _ => cech_homology_isZero_of_isEmpty f U n)
  · haveI : Nonempty ι := not_isEmpty_iff.mp hem
    have hcard : 1 ≤ Nat.card ι := Nat.card_pos
    exact cechZ_of_cech_isZero f U (cech_homology_isZero_of_card_le_of_nonempty f U hcard)

end Work.DSEQ0
