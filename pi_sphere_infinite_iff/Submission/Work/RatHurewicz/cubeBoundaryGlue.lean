import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs

/-!
# Gluing a continuous map on the boundary of a cube from finitely many closed pieces

`Work.RatHurewicz.exists_cubeBoundary`: if `∂I^{n+1}` is covered by finitely many closed sets
`E i`, and on each `E i` a continuous function `f i` is given, and the `f i` agree on the
overlaps, then there is a continuous `B : ↥(∂I^{n+1}) → X` with `B z = f i z` for every `z ∈ E i`.

This is the assembly step of the cubical `K`-operator: the boundary data of the filling
`K (n+1) p` is prescribed face by face, and the prescribed functions are defined (and continuous)
on the whole cube, so only the agreement on the overlaps (the consistency of the prescribed data)
has to be checked.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem exists_cubeBoundary (n : ℕ) {X : Type} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (E : ι → Set (IC (n + 1))) (hE : ∀ i, IsClosed (E i))
    (hcover : ∀ z : IC (n + 1), z ∈ Cube.boundary (Fin (n + 1)) → ∃ i, z ∈ E i)
    (f : ι → IC (n + 1) → X) (hf : ∀ i, ContinuousOn (f i) (E i))
    (hagree : ∀ i j, ∀ z, z ∈ E i → z ∈ E j → f i z = f j z) :
    ∃ B : C(↥(Cube.boundary (Fin (n + 1))), X),
      ∀ (z : ↥(Cube.boundary (Fin (n + 1)))) (i : ι), (z : IC (n + 1)) ∈ E i → B z = f i z := by
  classical
  have hwit : ∀ z : ↥(Cube.boundary (Fin (n + 1))), ∃ i, (z : IC (n + 1)) ∈ E i :=
    fun z => hcover z.1 z.2
  let Bfun : ↥(Cube.boundary (Fin (n + 1))) → X :=
    fun z => f (Classical.choose (hwit z)) z.1
  have hBval : ∀ (z : ↥(Cube.boundary (Fin (n + 1)))) (i : ι),
      (z : IC (n + 1)) ∈ E i → Bfun z = f i z.1 := by
    intro z i hi
    exact hagree _ i z.1 (Classical.choose_spec (hwit z)) hi
  have hcont : Continuous Bfun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : Bfun ⁻¹' T =
        ⋃ (i : ι), {z : ↥(Cube.boundary (Fin (n + 1))) | (z : IC (n + 1)) ∈ E i ∧ f i z.1 ∈ T} := by
      ext z; constructor
      · intro hz
        refine Set.mem_iUnion.mpr ⟨Classical.choose (hwit z), Classical.choose_spec (hwit z), ?_⟩
        show f (Classical.choose (hwit z)) (z : IC (n + 1)) ∈ T
        exact hz
      · intro hz
        obtain ⟨i, hi, hzT⟩ := Set.mem_iUnion.mp hz
        rw [Set.mem_preimage, hBval z i hi]
        exact hzT
    rw [hsub]
    refine isClosed_iUnion_of_finite fun i => ?_
    obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hf i)) T hT
    have hpiece : {z : ↥(Cube.boundary (Fin (n + 1))) | (z : IC (n + 1)) ∈ E i ∧ f i z.1 ∈ T}
        = Subtype.val ⁻¹' (U ∩ E i) := by
      ext z; constructor
      · rintro ⟨hzE, hzT⟩
        refine ⟨?_, hzE⟩
        have hmem : z.1 ∈ f i ⁻¹' T ∩ E i := ⟨hzT, hzE⟩
        rw [hUeq] at hmem
        exact hmem.1
      · rintro ⟨hzU, hzE⟩
        refine ⟨hzE, ?_⟩
        have hmem : z.1 ∈ U ∩ E i := ⟨hzU, hzE⟩
        rw [← hUeq] at hmem
        exact hmem.1
    rw [hpiece]
    exact ((hU.inter (hE i))).preimage continuous_subtype_val
  exact ⟨⟨Bfun, hcont⟩, hBval⟩

end

end Work.RatHurewicz
