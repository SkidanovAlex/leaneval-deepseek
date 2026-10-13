import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.bnd_ordConnected_finite
import Submission.Work.WilC2.bnd_sUnion_finset

set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

/-- **The boundary points of a definable set form a finite set.**

In a model `M ⊨ TR` (hence o-minimal, by `C2_models_ominimal_proved`), the set of "boundary
points" of an `A`-definable set `D` -- the points `x` such that `D` is not a neighbourhood of `x`
and `Dᶜ` is not a neighbourhood of `x` -- is contained in a finite set.

Proof sketch: by o-minimality `D` is a finite union of order-convex sets `D = ⋃₀ s`; one checks
that `E_D ⊆ ⋃_{I ∈ s} ∂I` where `∂I` is the analogue for `I`, and for a convex `I` the set `∂I`
has at most two elements (three elements `x < y < z` of `∂I` force `y` into the interior of `I`
by convexity). -/
theorem boundary_finite
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {A : Set M} {D : Set M}
    (hD : A.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ D}) :
    ∃ F : Finset M, ∀ x : M,
      (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D) →
      (¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ) → x ∈ F := by
  -- o-minimality of every model of `TR` (area C2) with parameters from `M`
  have hD' : (Set.univ : Set M).Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ D} :=
    hD.mono (Set.subset_univ A)
  obtain ⟨s, hconn, heq⟩ :=
    C2_models_ominimal_proved hR hC0 hUF M {v : Fin 1 → M | v 0 ∈ D} hD'
  -- `D` is the union of the finitely many order-convex pieces
  have hDun : D = ⋃₀ (s : Set (Set M)) := by
    ext x
    have hx := Set.ext_iff.mp heq (fun _ : Fin 1 => x)
    simpa using hx
  -- each piece has finitely many boundary points, and `D`'s boundary points lie in their union
  have huni : (⋃ I ∈ (s : Set (Set M)), {x : M | IsBnd I x}).Finite :=
    Set.Finite.biUnion s.finite_toSet (fun I hI => bnd_ordConnected_finite (hconn I hI))
  have hfin : {x : M | IsBnd D x}.Finite := by
    rw [hDun]
    refine huni.subset ?_
    intro x hx
    obtain ⟨I, hI, hIx⟩ := bnd_sUnion_finset hx
    exact Set.mem_biUnion hI hIx
  exact ⟨hfin.toFinset, fun x hx1 hx2 => hfin.mem_toFinset.mpr ⟨hx1, hx2⟩⟩

end Work.WilC2
