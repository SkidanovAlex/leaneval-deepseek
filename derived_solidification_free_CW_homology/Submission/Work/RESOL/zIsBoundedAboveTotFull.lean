/-
AREA RESOL — the total complex of the column-wise resolution of a bounded-above complex is
bounded above.

The degree `n` part of `Zero.totFull F π hπ B` is the coproduct of the summands
`(Rco.obj (B.X q)).X p` over the indices `(q, p)` with `p + q = n`.  The degreewise resolution
`Zero.Rco` lands in cochain degrees `≤ 0` (`Zero.Rco.obj M = ((LR).chainComplex M).extend
embeddingDownNat`), so for a summand with `p + q = n` we have either

* `p > 0`, in which case the summand vanishes by the strict support of `Rco` in degrees `≤ 0`
  (`CochainComplex.isZero_of_isStrictlyLE`), or
* `p ≤ 0`, hence `q = n - p ≥ n`; if `n > N` for a bound `N` of `B` then `B.X q` is a zero
  object, so the whole complex `Rco.obj (B.X q)` is zero and in particular its degree `p`
  term vanishes.

A coproduct of zero objects is a zero object, which finishes the proof.
-/
import Mathlib
import Submission.Work.RESOL.ZeroTotal

open CategoryTheory Limits LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

namespace Zero

/-- A coproduct of zero objects is a zero object: it suffices to test the identity against all
the coproduct inclusions, and those are zero because their sources are zero objects. -/
lemma isZero_coprod_of_isZero {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type}
    (Y : J → C) [HasCoproduct Y] (h : ∀ j, IsZero (Y j)) : IsZero (∐ Y) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro j
  rw [Category.comp_id, Limits.comp_zero]
  exact (h j).eq_of_src _ _

/-- The degreewise resolution functor sends zero objects to the zero complex. -/
lemma isZero_Rco_obj (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms]
    (π : F ⟶ 𝟭 LightCondAb) (hπ : ∀ M, Epi (π.app M)) {M : LightCondAb}
    (hM : IsZero M) : IsZero ((Rco F π hπ).obj M) := by
  rw [IsZero.iff_id_eq_zero] at hM ⊢
  rw [← (Rco F π hπ).map_id M, hM, (Rco F π hπ).map_zero]

/-- The terms of a zero cochain complex are zero objects. -/
lemma isZero_X_of_isZero_complex {K : Cpx} (hK : IsZero K) (i : ℤ) : IsZero (K.X i) := by
  rw [IsZero.iff_id_eq_zero] at hK ⊢
  have := HomologicalComplex.congr_hom hK i
  simpa using this

end Zero

theorem zIsBoundedAboveTotFull (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (B : Work.RESOL.Cpx)
    (hB : Work.RESOL.IsBoundedAbove B) :
    Work.RESOL.IsBoundedAbove (Work.RESOL.Zero.totFull F π hπ B) := by
  obtain ⟨N, hN⟩ := hB
  refine ⟨N, fun n hn => ?_⟩
  -- the degree `n` term is the coproduct of the summands indexed by `(q, p)` with `p + q = n`
  show IsZero (∐ (Zero.totFam F π hπ Zero.topP B n))
  refine Zero.isZero_coprod_of_isZero _ (fun x => ?_)
  obtain ⟨⟨a, b⟩, _hsum, -⟩ := x
  by_cases hb : 0 < b
  · -- the resolution degree `b` is positive, where `Rco.obj _` vanishes
    exact CochainComplex.isZero_of_isStrictlyLE ((Zero.Rco F π hπ).obj (B.X a)) 0 b hb
  · -- `b ≤ 0` forces `n ≤ a`, so `B.X a` is zero by boundedness
    push Not at hb
    have ha : N < a := by omega
    exact Zero.isZero_X_of_isZero_complex (Zero.isZero_Rco_obj F π hπ (hN a ha)) b

end Work.RESOL
