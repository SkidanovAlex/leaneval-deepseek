import Submission.E8Cert

/-! Certificate chunk for the weight `ord40 33` of the c-table. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

noncomputable section
namespace Submission.E8Cert

open Submission.E8Extract Submission.E8Orbit Submission.E8Character Submission.E8Casimir
open Submission.E8Enum Submission.E8Numerics Submission.E8Engine
open Submission.WeylReflect Submission.WeylWeights

theorem cert_sid_33 : ∀ (j : Fin 120) (k : Fin 4),
    domIdx (term ⟨33, by omega⟩ j k)
      = (if h : sidTab ⟨33, by omega⟩ j k < 40
         then some ⟨sidTab ⟨33, by omega⟩ j k, h⟩ else none) := by
  decide

theorem brk_eq_33 : ∀ (j : Fin 120) (k : Fin 4), sidTab ⟨33, by omega⟩ j k < 40 →
    brkF (term ⟨33, by omega⟩ j k) j = brkTab ⟨33, by omega⟩ j k := by
  decide

theorem ctab_eq_33 : ∀ e : Fin 40,
    ctab ⟨33, by omega⟩ e = ctabN ⟨33, by omega⟩ e := by
  decide

end Submission.E8Cert
