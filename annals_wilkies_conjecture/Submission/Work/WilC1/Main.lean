/-
  WilC1 — `C1_TR_modelComplete`: `T_r = Th(ℝ_rexp, (r)_{r ∈ ℝ})` is model complete.

  This is the deliverable of area C1.  It instantiates the parametrized assembly of
  `Submission/Work/WilC1/Core.lean` with the proved inputs:
  * `REx_iff_RExpExist_self`, `REx_compl` (the bridge to the frozen `RExpExist` and complement
    closure),
  * `REx_graph_tAdd`, `REx_graph_tMul`, `REx_graph_tNeg`, `REx_graph_tRexp` (the inductive cases of
    the graph of a term), `REx_eq_of_terms` (the atomic case),
  * `exists_term_of_poly` (exp-polynomials are `LRc`-terms),
  * `IsQF_isExistential_iExs` (existential closure of a quantifier-free formula).
-/
import Submission.Work.WilC1.Core
import Submission.Work.WilC1.REx_frozen
import Submission.Work.WilC1.REx_compl
import Submission.Work.WilC1.REx_graph_tAdd
import Submission.Work.WilC1.REx_graph_tMul
import Submission.Work.WilC1.REx_graph_tNeg
import Submission.Work.WilC1.REx_graph_tRexp
import Submission.Work.WilC1.REx_eq_of_terms
import Submission.Work.WilC1.exists_term_of_poly
import Submission.Work.WilC1.IsQF_isExistential_iExs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-- **C1.** `T_r` is model complete: embeddings between models of the complete theory of
`ℝ_rexp` (with every real named) are elementary. -/
theorem C1_TR_modelComplete_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) :
    ModelComplete TR :=
  modelComplete_of_parts
    (fun X hX => REx_compl (fun n X => REx_iff_RExpExist_self X) hR X hX)
    (fun ha hb => REx_graph_tAdd ha hb)
    (fun ha hb => REx_graph_tMul ha hb)
    (fun h => REx_graph_tNeg h)
    (fun h => REx_graph_tRexp h)
    (fun t₁ t₂ hg => REx_eq_of_terms t₁ t₂ hg)
    (fun P => exists_term_of_poly P)
    (fun h => IsQF_isExistential_iExs (L := LRc) h)

end Work.WilC1

namespace WilkiesDesign.CG

/-- **C1** in the namespace of the frozen specification: `T_r` is model complete. -/
theorem C1_TR_modelComplete_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) :
    ModelComplete TR :=
  Work.WilC1.C1_TR_modelComplete_proved hR

end WilkiesDesign.CG
