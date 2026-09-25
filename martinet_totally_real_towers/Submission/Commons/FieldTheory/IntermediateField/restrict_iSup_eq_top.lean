import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Order.CompletePartialOrder

namespace Commons.FieldTheory.IntermediateField

/-- If `K = ⨆ i, f i` with each `f i ≤ K`, then viewing each `f i` as an
intermediate field of `K` over `F` (via `IntermediateField.restrict`), their
supremum is the whole of `K`, i.e. the top intermediate field of `K / F`.

Equivalently: `lift` (`IntermediateField.lift`, mapping subfields of `K` back
into `E`) commutes with `iSup`, is injective, sends `⊤` to `K`, and sends each
`restrict (hle i)` back to `f i`; hence the `iSup` of the restricts must be `⊤`. -/
lemma restrict_iSup_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} [Fintype ι] (f : ι → IntermediateField F E) (K : IntermediateField F E)
    (hK : K = ⨆ i, f i) (hle : ∀ i, f i ≤ K) :
    (⨆ i, IntermediateField.restrict (hle i)) = ⊤ := by
  classical
  have hsup :
      IntermediateField.lift (⨆ i, IntermediateField.restrict (hle i)) =
        ⨆ i, IntermediateField.lift (IntermediateField.restrict (hle i)) := by
    exact (IntermediateField.gc_map_comap (K := F) (L := ↥K) (L' := E)
      (f := IntermediateField.val K)).l_iSup
  have hlift_restrict : ∀ i, IntermediateField.lift (IntermediateField.restrict (hle i)) = f i := by
    intro i
    exact IntermediateField.lift_restrict (hle i)
  have htop : IntermediateField.lift (⊤ : IntermediateField F ↥K) = K := by
    apply le_antisymm
    · exact IntermediateField.lift_le (K := F) (L := E) (F := K) (⊤ : IntermediateField F ↥K)
    · rw [SetLike.le_def]
      intro x hx
      exact (IntermediateField.mem_lift (K := F) (L := E) (F := K)
        (E := (⊤ : IntermediateField F ↥K)) (x := ⟨x, hx⟩)).mpr (by simp)
  apply (IntermediateField.lift_inj (K := F) (L := E) (F := K)
    (⨆ i, IntermediateField.restrict (hle i)) (⊤ : IntermediateField F ↥K)).mp
  calc
    IntermediateField.lift (⨆ i, IntermediateField.restrict (hle i))
        = ⨆ i, IntermediateField.lift (IntermediateField.restrict (hle i)) := hsup
    _ = ⨆ i, f i := by
        apply iSup_congr
        intro i
        exact hlift_restrict i
    _ = K := hK.symm
    _ = IntermediateField.lift (⊤ : IntermediateField F ↥K) := htop.symm

end Commons.FieldTheory.IntermediateField