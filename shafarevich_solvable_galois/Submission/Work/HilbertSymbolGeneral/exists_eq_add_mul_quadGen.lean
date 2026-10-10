import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.HilbertSymbolGeneral.Gens
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.HilbertSymbolGeneral

/-!
# Every element of the quadratic level is `u + v √b`

Let `F` be a field with `2 ≠ 0`, `F'` a Galois extension of `F`, `y ∈ F'` with `y * y = b`, and
suppose `y` is not a base-field element.  Then every element `w` of the quadratic level
`F(√b) = NK.NUV2.LC.quadLevel y b hy` is of the form `u + v * quadGen y b hy` with `u, v ∈ F`
(`quadGen` is the image of `y` in the level, from `Submission/Work/HilbertSymbolGeneral/Gens.lean`).

Intended proof (the same argument as `NK.NUV2.exists_eq_add_mul_qGen` in
`Submission/NK/NUV2/QuadFaithful2_Basic.lean`, which can be imported and used as a template):
`quadGen` is not in the range of `algebraMap F ↥(quadLevel y b hy)`
(`Work.HilbertSymbolGeneral.quadGen_notMem_range`), so `![algebraMap F _ 1, quadGen]` is linearly
independent over `F` (`linearIndependent_fin2`); its span has finrank `2`, which equals the finrank
of the level (one may use the helper `quadLevel_finrank_eq_two_of_notMem`, or re-derive it), so the
span is `⊤`; `Submodule.mem_span_pair` then gives the two coordinates.
-/

open scoped Classical

theorem exists_eq_add_mul_quadGen {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] [NeZero (2 : F)] (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    (hx : y ∉ Set.range (algebraMap F F')) (w : ↥(NK.NUV2.LC.quadLevel y b hy)) :
    ∃ u v : F, w = algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) u +
      algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) v * quadGen y b hy := by
  haveI : FiniteDimensional F ↥(NK.NUV2.LC.quadLevel y b hy) :=
    NK.NUV2.LC.quadLevel_finiteDimensional y b hy
  -- The quadratic level has degree two: `≤ 2` is `quadLevel_finrank_le_two`, and degree one would
  -- force the generator to be a base-field element.
  have hfin : Module.finrank F ↥(NK.NUV2.LC.quadLevel y b hy) = 2 := by
    have hle : Module.finrank F ↥(NK.NUV2.LC.quadLevel y b hy) ≤ 2 :=
      NK.NUV2.LC.quadLevel_finrank_le_two y b hy
    have hne : Module.finrank F ↥(NK.NUV2.LC.quadLevel y b hy) ≠ 1 := by
      intro h1
      have hbot : NK.NUV2.LC.quadLevel y b hy = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
      have hmem : (quadGen y b hy : ↥(NK.LocalReciprocity.maxAbelianSubext F F')) ∈
          (⊥ : IntermediateField F ↥(NK.LocalReciprocity.maxAbelianSubext F F')) := by
        rw [← hbot]; exact (quadGen y b hy).2
      obtain ⟨u, hu⟩ := IntermediateField.mem_bot.mp hmem
      exact hx ⟨u, by
        have := congrArg (fun z : ↥(NK.LocalReciprocity.maxAbelianSubext F F') => (z : F')) hu
        simpa [quadGen] using this⟩
    have hpos : 0 < Module.finrank F ↥(NK.NUV2.LC.quadLevel y b hy) := Module.finrank_pos
    omega
  -- `1` and `quadGen` are linearly independent over `F`.
  have hli : LinearIndependent F
      ![algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) (1 : F), quadGen y b hy] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · intro h0
      have hb0 : quadGen y b hy = 0 := by simpa using h0
      exact quadGen_notMem_range y b hy hx ⟨0, by rw [hb0, map_zero]⟩
    · intro a ha
      by_cases ha0 : a = 0
      · rw [ha0, zero_smul] at ha
        have h10 : (1 : ↥(NK.NUV2.LC.quadLevel y b hy)) = 0 := by simpa using ha.symm
        exact one_ne_zero h10
      · refine quadGen_notMem_range y b hy hx ⟨a⁻¹, ?_⟩
        have h1 : algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) a * quadGen y b hy = 1 := by
          have := ha
          rw [Algebra.smul_def] at this
          simpa using this
        rw [map_inv₀]
        exact inv_eq_of_mul_eq_one_right h1
  -- Hence their span is everything.
  have hspan : Submodule.span F
      {algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) (1 : F), quadGen y b hy} = ⊤ := by
    have hrange : (Set.range ![algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) (1 : F),
        quadGen y b hy]) =
        {algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) (1 : F), quadGen y b hy} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    rw [← hrange, finrank_span_eq_card hli, hfin]
    simp
  have hmem : w ∈ Submodule.span F
      {algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) (1 : F), quadGen y b hy} := by
    rw [hspan]; trivial
  obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨u, v, ?_⟩
  rw [← huv]
  simp only [Algebra.smul_def, map_one, mul_one]

end Work.HilbertSymbolGeneral
