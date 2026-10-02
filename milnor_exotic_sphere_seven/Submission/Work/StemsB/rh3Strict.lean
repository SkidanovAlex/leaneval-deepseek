import Mathlib
import Submission.Work.StemsB.gysinStrict
import Submission.Work.StemsB.c2FreeStrict
import Submission.Work.StemsB.evenStepLocalStrict
import Submission.Work.RatHurewicz.stableStemsTorsion_of_stable3
import Submission.Work.Stems.c2OddBase
import Submission.Work.Stems.c2FreeMain
import Submission.Work.Stems.rangeModelRatAcyclic3
import Submission.Work.Serre.serreC3FiniteOne
import Submission.Work.RatHurewicz.S3Final
import Submission.Work.Drive.rh3OfE3b

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `RationalHurewiczStable3` from the **strict** Gysin range

`Submission/Work/Drive/rh3OfE3b.lean` proves

  `Work.Drive.rh3_of_e3b : Work.Serre.SerreE3b → Work.Drive.RationalHurewiczStable3`

by `rationalHurewiczStable3_of_rangeModel (rangeModelRatAcyclic_of_C2odd_C3one 3
(c2oddFree_three serreE3a h) serreC3FiniteOne)`.  By
`Submission/Work/StemsB/gysinStrict.lean` + `Submission/Work/StemsB/c2FreeStrict.lean` the C2 layer
only needs the **strict** Gysin range `m + r + 1 ≤ N` (allowance `c = 3`, two degrees of slack), so
the same conclusion follows from `Work.StemsB.SerreE3bStrict` — a hedge on `SerreE3b`, as requested
by the project lead.

The strict even step is taken here as an explicit hypothesis in the shape of the delegated port
`Work.StemsB.evenStepLocalStrict`; when that lands, `Work.StemsB.rh3_of_e3bStrict` below is obtained
by one instantiation.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The strict-range variant of `Work.Stems.c2oddFree_three`**, with the even step supplied as a
hypothesis (the shape of the port `Work.StemsB.evenStepLocalStrict` specialised to `c = 3`). -/
theorem c2oddFree_three_strict_of_port
    (hStrict : ∀ (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1),
      (∀ M : ℕ, Work.Stems.OddClause 3 m (by omega) M) → ∀ N : ℕ, Work.Stems.EvenClause 3 j hj N)
    (hE3b : Work.StemsB.SerreE3bStrict) :
    Work.Stems.Engine.C2oddFree 3 :=
  (c2evenFree_and_c2oddFree_strict 3 (by norm_num) Work.Serre.serreE3a hStrict
    (fun N => by
      intro X tX pt hX
      letI : TopologicalSpace X := tX
      obtain ⟨hgen, hvan⟩ := Work.Stems.oddClauseOne X pt N hX
        (Work.Stems.bottomCellOne X pt N hX)
      exact ⟨hgen, fun d hd0 hdN hdn => hvan d hd0 (by omega) hdn⟩)).2

/-- **`RationalHurewiczStable3` from the strict Gysin range**, mirroring
`Submission/Work/Drive/rh3OfE3b.lean`. -/
theorem rh3_of_e3bStrict_of_port
    (hStrict : ∀ (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1),
      (∀ M : ℕ, Work.Stems.OddClause 3 m (by omega) M) → ∀ N : ℕ, Work.Stems.EvenClause 3 j hj N)
    (hE3b : Work.StemsB.SerreE3bStrict) :
    Work.Drive.RationalHurewiczStable3 :=
  Work.RatHurewicz.rationalHurewiczStable3_of_rangeModel
    (Work.Stems.rangeModelRatAcyclic_of_C2odd_C3one 3
      (c2oddFree_three_strict_of_port hStrict hE3b) Work.Serre.serreC3FiniteOne)

/-- **The hedge**: `SerreE3b` (full range) also gives the strict range, hence
`RationalHurewiczStable3` through the strict chain. -/
theorem rh3_of_e3b_via_strict_of_port
    (hStrict : ∀ (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1),
      (∀ M : ℕ, Work.Stems.OddClause 3 m (by omega) M) → ∀ N : ℕ, Work.Stems.EvenClause 3 j hj N)
    (h : Work.Serre.SerreE3b) :
    Work.Drive.RationalHurewiczStable3 :=
  rh3_of_e3bStrict_of_port hStrict (serreE3bStrict_of_serreE3b h)


/-- **The strict even step, at `c = 3`** (the port, instantiated). -/
theorem strictStep3 (hE3b : Work.StemsB.SerreE3bStrict) :
    ∀ (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1),
      (∀ M : ℕ, Work.Stems.OddClause 3 m (by omega) M) → ∀ N : ℕ, Work.Stems.EvenClause 3 j hj N :=
  fun j hj m hm hodd N => Work.StemsB.evenStepLocalStrict 3 (by norm_num) hE3b j hj m hm hodd N

/-- **`RationalHurewiczStable3` from the strict Gysin range** (the lead's requested hedge). -/
theorem rh3_of_e3bStrict (hE3b : Work.StemsB.SerreE3bStrict) :
    Work.Drive.RationalHurewiczStable3 :=
  rh3_of_e3bStrict_of_port (strictStep3 hE3b) hE3b

/-- **The contract from the strict Gysin range.** -/
theorem stableStemsTorsionB_of_E3bStrict (hE3b : Work.StemsB.SerreE3bStrict) :
    Work.Drive.StableStemsTorsion :=
  -- NOTE (area STEMSB, 2026-09-27): the helper `Work.StemsB.stableStemsTorsionB_of_stable3` lives
  -- in `Submission/Work/StemsB/stableStemsTorsionB.lean` (the contract file), which must NOT be
  -- imported here: the contract file has to be able to import *this* module (`Serre.All` and the
  -- `SerreE3bStrict` route do), so importing it back would create an import cycle.  The helper is
  -- the one-liner below, inlined.
  Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable3 (rh3_of_e3bStrict hE3b)

#print axioms Work.StemsB.strictStep3
#print axioms Work.StemsB.rh3_of_e3bStrict
#print axioms Work.StemsB.stableStemsTorsionB_of_E3bStrict

#print axioms Work.StemsB.c2oddFree_three_strict_of_port
#print axioms Work.StemsB.rh3_of_e3bStrict_of_port

end

end Work.StemsB
