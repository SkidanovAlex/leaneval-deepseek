/-
  WilC6 — Robinson's test for model completeness, made effective by compactness:

  over all models of `TE = Th(ℝ_exp)`, every formula is equivalent to an existential formula.
-/
import Submission.Work.WilC6.Base
import Submission.Work.WilC6.Transfer.transfer_of_isEF
import Submission.Work.WilC6.Compact.exists_model_of_isEF
import Submission.Work.WilC6.Compact.exists_isEF_of_entails

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6

/-- The `IsEF`-consequences of `φ` entail `φ` over all models of `TE`.

This combines the amalgamation step (`transfer_of_isEF`, which uses model completeness) with the
compactness step (`exists_model_of_isEF`): if `φ` failed at `(N, b)` we could build `(M, a)` with
`φ` true at `a` and the same existential type as `b`, and the transfer would force `φ` at `b`. -/
theorem ef_entails (hMC : ModelComplete TE) {n : ℕ} (φ : LEc.Formula (Fin n))
    (N : Type) [LEc.Structure N] [N ⊨ TE] (b : Fin n → N)
    (hΓ : ∀ Ψ : LEc.Formula (Fin n), IsEF Ψ → EFCons φ Ψ → Ψ.Realize b) :
    φ.Realize b := by
  by_contra hnot
  obtain ⟨M, strM, modM, a, hφa, hinc⟩ := Compact.exists_model_of_isEF φ N b hΓ
  letI := strM
  haveI := modM
  exact hnot (Transfer.transfer_of_isEF hMC M N a b hinc φ hφa)

/-- **Robinson's test, made effective.**  For every formula `φ` of `LEc` there is an existential
formula `Ψ` which is equivalent to `φ` over every model of `TE`. -/
theorem exists_isEF_iff_of_modelComplete (hMC : ModelComplete TE) {n : ℕ}
    (φ : LEc.Formula (Fin n)) :
    ∃ Ψ : LEc.Formula (Fin n), IsEF Ψ ∧ EFCons φ Ψ ∧ EFCons Ψ φ := by
  refine Compact.exists_isEF_of_entails φ fun N _ _ b hΓ => ?_
  exact ef_entails hMC φ N b hΓ

end Work.WilC6
