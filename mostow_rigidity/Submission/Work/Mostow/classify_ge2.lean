import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.classifyProp

/-! Guidance from the project lead (the requester):

# Low-dimensional copies (lead's request). The strata / Kazhdan-Margulis / geodesic-stratum chapters need the toolkit in
# every dimension k >= 1 (strata of dimension 1, 2, ... inside H^n). Your statement is the SAME Prop as an already-PROVED
# area lemma, only with a weaker dimension hypothesis:
#   poAction_ge1      <- Work.Mostow.poAction (proved for 3 <= n; its proof only uses 2 <= n via poCenter).
#                        n = 1 needs its own centre argument: A central in O(1,1) commutes with diag(-1,1) and diag(1,-1)
#                        => A diagonal => A = diag(a,b), a,b in {+1,-1}; commuting with a boost forces a = b => A = +-1.
#   hypIsometry_ge1   <- Work.Mostow.hypIsometry (proved for 3 <= n). For n = 1: E 1 = R is H^1, isometries of R are
#                        x -> +-x + c, all realised by PO(1,1) (boosts = translations, diag(-1,1) = reflection).
#   classify_ge2      <- your geomFinite colleagues have `classifyProp n hn hA hI` (search Submission/Work/Mostow for
#                        classifyProp); restate/reprove for 2 <= n.
#   multThick_ge2     <- Work.Mostow.geomFiniteMultThick (PROVED in the geomFinite tree); restate for 2 <= n.
# COPY the existing proofs (import their modules; do not re-derive), check every use of the dimension hypothesis, and
# patch only the places that genuinely used 3 <= n. Never use `λ` as a variable name.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem classify_ge2 (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ClassifyProp n :=
  classifyProp n hn hA hI

end Work.Mostow
