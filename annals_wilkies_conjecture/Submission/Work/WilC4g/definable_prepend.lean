import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4g

open FirstOrder FirstOrder.Language
open WilkiesDesign.CG

/-- **Prepending a parameter preserves definability.**

If `Y ⊆ M^{k+2}` is `LRc`-definable with parameters in `A`, then for any `x : M` the set of
tuples `w : Fin (k+1) → M` whose `cons` with `x` lies in `Y` is `LRc`-definable with parameters
in `A ∪ {x}`.

Concretely, `{w | Fin.cons x w ∈ Y}` is the image of `Y ∩ {g | g 0 = x}` under the (definable
over `{x}`) projection `g ↦ g ∘ Fin.succ`, using `Fin.cons x w ∘ Fin.succ = w` and
`Fin.cons_self_tail`.  Definability of the image under the finite projection `Fin.succ` is
`Set.Definable.image_comp`. -/
theorem definable_prepend {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {k : ℕ} {A : Set M} {Y : Set (Fin (k + 2) → M)} (hY : A.Definable WilkiesDesign.CG.LRc Y) (x : M) : (A ∪ {x}).Definable WilkiesDesign.CG.LRc {w : Fin (k + 1) → M | Fin.cons x w ∈ Y} := by
  have hY' : (A ∪ {x}).Definable LRc Y := hY.mono Set.subset_union_left
  have hx : x ∈ A ∪ {x} := Set.mem_union_right _ (Set.mem_singleton x)
  -- the slice `g 0 = x` is definable over `{x}`, hence over `A ∪ {x}`
  have hPt : (A ∪ {x}).Definable LRc {g : Fin (k + 2) → M | g 0 = x} := by
    have h1 : (A ∪ {x}).Definable LRc {v : Fin 1 → M | v 0 ∈ ({x} : Set M)} :=
      Set.Definable.singleton_of_mem (L := LRc) (A := A ∪ {x}) hx
    have h2 := h1.preimage_comp (fun _ : Fin 1 => (0 : Fin (k + 2)))
    convert h2 using 1
    ext g
    simp [Function.comp_def]
  -- project the definable slice of `Y` onto its tail
  have himg := (hY'.inter hPt).image_comp (Fin.succ : Fin (k + 1) → Fin (k + 2))
  have hset : ({w : Fin (k + 1) → M | Fin.cons x w ∈ Y} : Set (Fin (k + 1) → M)) =
      ((fun g : Fin (k + 2) → M => g ∘ (Fin.succ : Fin (k + 1) → Fin (k + 2))) ''
        (Y ∩ {g : Fin (k + 2) → M | g 0 = x})) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
    constructor
    · intro hw
      exact ⟨Fin.cons x w, ⟨hw, by rw [Fin.cons_zero]⟩, Fin.cons_comp_succ x w⟩
    · rintro ⟨g, ⟨hgY, hg0⟩, hgw⟩
      convert hgY using 1
      funext i
      cases i using Fin.cases with
      | zero => rw [Fin.cons_zero, hg0]
      | succ i => simpa using (congrFun hgw i).symm
  rw [hset]
  exact himg

end Work.WilC4g
