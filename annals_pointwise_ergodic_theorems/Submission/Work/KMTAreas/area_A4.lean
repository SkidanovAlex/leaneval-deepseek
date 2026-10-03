import Mathlib
import Submission.Work.KMTAreas.A4.improvOfImprovGood
import Submission.Work.KMTAreas.A4.ImprovGoodAssembly
import Submission.Work.KMTAreas.A4.eLpNorm_ahalfR_eq
import Submission.Work.KMTAreas.A4.improvOneZ
import Submission.Work.KMTAreas.A4.improvTwoZ

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN KMT contract (Submission/Work/KMTContract/Areas.lean; composition
exists_varEstHalfFin_Cv_of_areas PROVED, so proving all eight areas closes the problem). Read first:
* Submission/Work/KMTPlan/ROUTE_LEAD.md: §1 the DAG, §3.1 your area with its proof sketch, §3.3 the quantifier order, §3.4 the audit;
* Submission/Work/KMTContract/README.md;
* KMTContract/QUARANTINE.md: never use the quarantined statements (the old Peluse/Improv/SingleScale ones are false or vacuous).
Many tools are already proved in Submission/Work/** and Submission/Commons/** (ROUTE_LEAD §2.1 lists them); reuse them and do not
re-request what exists. Parallelise: request all independent pieces at once, and write the assembly against their statements while they run.

A4 = improv as an implication from A1, PeluseInverseKMT P, PolyImproving(P−X), PolyImproving(X−P): the paper's §5 chain
PP → LIP → HAHN → STRUCT-I → PROPDUAL → STRUCT-III → STRUCT-IV (ROUTE_LEAD §1.1). You get A1 and Peluse as hypotheses; do NOT prove them.

STATE OF THIS FILE (see `NOTES_A4_improv_SESSION.md` at the workspace root for the full report).
`Work.KMTContract.AreaA4` is the paper's §5 (minor arc single scale estimate, `improv`), which is a large
development.  The following pieces of the chain are already proved in this directory:

* `Submission/Work/KMTAreas/A4/Hahn.lean` — Lemma `hahn` of §5 (`hahn_structure`, the closed-convex-hull
  form) and its decomposition form (`hahn_decomposition`), which is the engine of Corollary `struct`.
* `A4/kmtProjMono.lean` — monotonicity of `kmtProj` in `(l,k)` (needed for the good-major-arc
  reduction producing the second summand `(logN N)^{-c/\rho}`);
* `A4/AhalfTransposeBound.lean` — the `(anf)` bounds for the dual function `Ã*`;
* `A4/Struct.lean` — the interface of Corollary `struct` (`LipOutput`, `structPhi`, the dual function
  `Ã*` as an element of `ℓ²(ℤ)`);
* `A4/peluseLipUniform.lean` — **Proposition `lip`** (the inverse-theoretic step of §5.1) from
  `PeluseInverseKMT P`;
* `A4/kmtProjEqSelf.lean`, `A4/kmtProjStar.lean`, `A4/kmtProjMono.lean` — the IW projection API
  used by PROPDUAL and by the good-major-arc reduction;
* `A4/ImprovGoodDefs.lean` — `ImprovGood`, the good-major-arc form in which §5 is proved;
* `A4/Struct.lean` — the interface of Corollary `struct`;
* in flight (delegated, not yet available): `A4/improvOfImprovGood` (the good-major-arc reduction
  `ImprovGood P → ImprovKMT P`), `A4/peluseLipL1Tail` (Proposition `lip` with the honest `ℓ¹`
  bound and the spatial tail bound needed by `struct`).

UPDATE (see `NOTES_A4_session4.md` at the workspace root, and `NOTES_A4_window_pin_GAP.md`).

**THIS FILE BUILDS, and the only `sorry` in its dependency closure is in the two delegated
statements `A4/improvOneZ` (Theorem `improv`(i) in `Z`-language) and `A4/improvTwoZ` (Theorem
`improv`(ii)), both of which take `PeluseInverseKMT P` directly.**  So `AreaA4` is proved modulo
those two halves.  The guaranteed-good-arc reduction `A4/improvOfImprovGood` is proved, and the
assembly is `A4/improvGood_of_Z` of `A4/ImprovGoodAssembly.lean`, which combines the two halves with
the two elementary transfers `A4/eLpNorm_ahalfR_eq` (`AhalfR TZ` is `AhalfZ` up to the reflection
`x -> -x`) and `A4/kmtProj_reflect_zero`.

WARNING.  The support window `N0 <= 2 N^d` hardcoded in `A4/Struct.lean`'s `LipOutputTail` (and in
`peluseLipL1Tail`, `lip2`, `propdual`) is too tight for polynomials with a large leading
coefficient: for `P = 100 X^2` those statements are provably *vacuous*, so the section-5 chains must
be built with a window parameter `A >= 1` (exactly as `PeluseInverseKMT` and
`A4/LipOutputTailA`/`A4/peluseLipL1TailA` do). -/

namespace Work.KMTAreas

open Polynomial

/-- **A4 reduced to the good-major-arc form of `improv`.**

The only remaining content of A4 is the paper's §5 in the regime of *good* major arcs, i.e.
`A4.ImprovGood` (`Submission/Work/KMTAreas/A4/ImprovGoodDefs.lean`): the estimate with the single
gain `2^{-cl}` for `(l, l - Log N)` of good major arcs.  The paper's "largest good `l' ≤ l`"
argument, which produces the second summand `(Log N)^{-c/ρ}` of `ImprovKMT`, is proved in
`A4.improvOfImprovGood` (`Submission/Work/KMTAreas/A4/improvOfImprovGood.lean`). -/
theorem area_A4_of_improvGood
    (h : ∀ P : ℤ[X], 2 ≤ P.natDegree → Work.KMTContract.AreaA1 →
      Work.KMTContract.PeluseInverseKMT P → Work.KMTContract.PolyImproving (P - X) →
      Work.KMTContract.PolyImproving (X - P) → Work.KMTAreas.A4.ImprovGood P) :
    Work.KMTContract.AreaA4 := by
  intro P hP h1 h2 h3 h4
  exact Work.KMTAreas.A4.improvOfImprovGood P (h P hP h1 h2 h3 h4)

theorem area_A4 : Work.KMTContract.AreaA4 := by
  intro P hP h1 h2 h3 h4
  refine Work.KMTAreas.A4.improvOfImprovGood P ?_
  refine Work.KMTAreas.A4.improvGood_of_Z P hP
    (fun N f g p => Work.KMTAreas.A4.eLpNorm_ahalfR_eq P N f g p)
    (fun ρ l k f hf h => Work.KMTAreas.A4.kmtProj_reflect_zero ρ l k f hf h) ?_ ?_
  · exact Work.KMTAreas.A4.improvOneZ P hP h1 h2 h4
  · exact Work.KMTAreas.A4.improvTwoZ P hP h1 h2 h3

end Work.KMTAreas
