import Mathlib
import Submission.Work.SG.sgTauDefs
import Submission.Work.SG.sgMulPair_toPair

/-!
# `zClose_map_toPair`: the `ℚ`-side closure is covered by the `toPair` image

`sgClose` (the `ℚ`-side breadth-first closure of `Defs`) and its integer mirror `zClose`
(`SGprelude`) iterate the same round with `sgMulPair` resp. `zMul d` in place of each other.
Since `sgMulPair` commutes with `toPair d` (`sgMulPair_toPair`), every element of the
`ℚ`-side closure of the `toPair`-images of `gens` over the `toPair`-images of `acc` is the
`toPair`-image of an element of the integer closure `zClose gens d m acc`.

Note there is no side condition on the denominator `d`: `toPair d` need not be injective
(for `d = 0` it collapses all translations), so the `ℚ`-side `dedup` may merge points; the
statement is only about *membership*, and the argument is carried out purely at the level of
`∈`, where `List.mem_map` / `List.mem_dedup` / `mem_zF` / `mem_sgF` replace any equality of
the underlying lists.
-/

namespace Work.SG
namespace Tau

/-- One closure round on the `ℚ`-side, applied to a list `B` of pairs whose elements are
`toPair`-images of a list `A` of integer pairs, lands inside the `toPair`-image of the
integer round `zF gens d A`. -/
private lemma sgF_subset_image (d : ℕ) (gens : List (List ℤ × List ℤ))
    {A : List (List ℤ × List ℤ)} {B : List (List ℤ × List ℚ)}
    (hB : ∀ b ∈ B, b ∈ A.map (toPair d)) :
    ∀ x ∈ sgF (gens.map (toPair d)) B, x ∈ (zF gens d A).map (toPair d) := by
  intro x hx
  rw [mem_sgF] at hx
  rcases hx with hx | ⟨a, ha, g, hg, hx⟩
  · rcases List.mem_map.mp (hB x hx) with ⟨y, hy, rfl⟩
    exact List.mem_map.mpr ⟨y, mem_zF.mpr (Or.inl hy), rfl⟩
  · rcases List.mem_map.mp (hB a ha) with ⟨y, hy, rfl⟩
    rcases List.mem_map.mp hg with ⟨h, hh, rfl⟩
    refine List.mem_map.mpr ⟨zMul d y h, mem_zF.mpr (Or.inr ⟨y, hy, h, hh, rfl⟩), ?_⟩
    rw [← hx]
    exact (sgMulPair_toPair d y h).symm

theorem zClose_map_toPair (d : ℕ) (gens acc : List (List ℤ × List ℤ)) (m : ℕ) :
    ∀ p ∈ sgClose (gens.map (toPair d)) m (acc.map (toPair d)),
      ∃ y ∈ zClose gens d m acc, toPair d y = p := by
  induction m generalizing acc with
  | zero =>
      intro p hp
      change p ∈ acc.map (toPair d) at hp
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hp
      exact ⟨y, by rw [zClose_zero]; exact hy, hyeq⟩
  | succ m ih =>
      intro p hp
      rw [zClose_succ]
      have hB : ∀ x ∈ sgF (gens.map (toPair d)) (acc.map (toPair d)),
          x ∈ (zF gens d acc).map (toPair d) :=
        sgF_subset_image d gens (A := acc) (B := acc.map (toPair d)) (fun _ hb => hb)
      have hmono : p ∈ sgClose (gens.map (toPair d)) m ((zF gens d acc).map (toPair d)) :=
        sgClose_mono_acc (gens := gens.map (toPair d)) hB m hp
      obtain ⟨y, hy, hyeq⟩ := ih (zF gens d acc) p hmono
      exact ⟨y, hy, hyeq⟩

end Tau
end Work.SG
