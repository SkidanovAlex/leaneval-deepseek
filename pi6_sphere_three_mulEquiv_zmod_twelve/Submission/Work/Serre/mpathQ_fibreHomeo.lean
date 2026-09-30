import Submission.Work.Serre.MapPathDefs

/-!
# The fibre of the mapping path space is the homotopy fibre

The fibre of `mpathQ p` over `p e₀` consists of the pairs `(e, γ)` with `γ` a path from `p e` to
`p e₀`, while the homotopy fibre `Work.RatHurewicz.homotopyFibre p e₀` consists of the pairs
`(e, δ)` with `δ` a path from `p e₀` to `p e`.  They are homeomorphic by reversing the path,
`γ ↦ γ ∘ (s ↦ 1 - s)`, which is a homeomorphism `revPath B` of the path space `C(I, B)`.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The fibre of `mpathQ p` over `p e₀` is homeomorphic to the homotopy fibre of `p` at
`e₀`**, by reversal of paths. -/
theorem mpathQ_fibreHomeo (p : C(E, B)) (e₀ : E) :
    Nonempty (Work.StemsB.fibre (mpathQ p) (p e₀) ≃ₜ
      Work.RatHurewicz.homotopyFibre p e₀) := by
  have hps : ∀ x : Work.StemsB.fibre (mpathQ p) (p e₀),
      (revPath B x.1.1.2) 0 = p e₀ := fun x => by rw [revPath_zero]; exact x.2
  have hpm : ∀ x : Work.StemsB.fibre (mpathQ p) (p e₀),
      (revPath B x.1.1.2) 1 = p x.1.1.1 := fun x => by rw [revPath_one]; exact x.1.2
  have hqs : ∀ y : Work.RatHurewicz.homotopyFibre p e₀,
      (revPath B y.1.2.1) 0 = p y.1.1 := fun y => by rw [revPath_zero]; exact y.2
  have hqm : ∀ y : Work.RatHurewicz.homotopyFibre p e₀,
      (revPath B y.1.2.1) 1 = p e₀ := fun y => by rw [revPath_one]; exact y.1.2.2
  let F : Work.StemsB.fibre (mpathQ p) (p e₀) → Work.RatHurewicz.homotopyFibre p e₀ := fun x =>
    ⟨(x.1.1.1, ⟨revPath B x.1.1.2, hps x⟩), hpm x⟩
  let G : Work.RatHurewicz.homotopyFibre p e₀ → Work.StemsB.fibre (mpathQ p) (p e₀) := fun y =>
    ⟨⟨(y.1.1, revPath B y.1.2.1), hqs y⟩, hqm y⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact revPath_revPath B x.1.1.2
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact revPath_revPath B y.1.2.1
  have hFc : Continuous F := by
    refine Continuous.subtype_mk
      (f := fun x : Work.StemsB.fibre (mpathQ p) (p e₀) =>
        (x.1.1.1, (⟨revPath B x.1.1.2, hps x⟩ : Work.StemsB.PathSpace B (p e₀)))) ?_ hpm
    refine Continuous.prodMk ?_ ?_
    · exact (mpathFst p).continuous.comp
        (continuous_subtype_val : Continuous fun x : Work.StemsB.fibre (mpathQ p) (p e₀) => x.1)
    · exact Continuous.subtype_mk
        (f := fun x : Work.StemsB.fibre (mpathQ p) (p e₀) => revPath B x.1.1.2)
        ((revPath B).continuous.comp ((mpathSnd p).continuous.comp
          (continuous_subtype_val : Continuous fun x : Work.StemsB.fibre (mpathQ p) (p e₀) => x.1)))
        hps
  have hGc : Continuous G := by
    refine Continuous.subtype_mk
      (f := fun y : Work.RatHurewicz.homotopyFibre p e₀ =>
        (⟨(y.1.1, revPath B y.1.2.1), hqs y⟩ : mpath p)) ?_ hqm
    refine Continuous.subtype_mk
      (f := fun y : Work.RatHurewicz.homotopyFibre p e₀ =>
        (y.1.1, revPath B y.1.2.1)) ?_ hqs
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp
        (continuous_subtype_val : Continuous fun y : Work.RatHurewicz.homotopyFibre p e₀ => y.1)
    · exact (revPath B).continuous.comp
        (continuous_subtype_val.comp (continuous_snd.comp
          (continuous_subtype_val : Continuous fun y : Work.RatHurewicz.homotopyFibre p e₀ => y.1)))
  exact ⟨{ toFun := F, invFun := G, left_inv := hFG, right_inv := hGF,
            continuous_toFun := hFc, continuous_invFun := hGc }⟩

end

end Work.Serre
