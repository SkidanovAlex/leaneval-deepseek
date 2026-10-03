/-
# Theorem `improv`(ii) of Krause--Mirek--Tao, §5.2, for the integer shift

The single scale minor arc estimate for the *second* function: if `𝓕_ℤ g` vanishes on the major
arcs `𝓜_{≤l,≤d(-Log N+l)}` (`d = deg P`), then

`‖Ã_N(f,g)‖_{ℓ¹(ℤ)} ≤ C 2^{-cl} ‖f‖_{ℓ²(ℤ)}‖g‖_{ℓ²(ℤ)}`

on good major arcs, with a rate `c > 0` independent of the Ionescu--Wainger parameter `ρ`.

The proof is the paper's: §5.2 reduces the statement to the estimate (`siv-second`) for the second
dual function `Ã_N^{**}(f,h)`, and the final duality is the elementary identity `(ℓ¹)' = ℓ^∞`.  The
reduction is assembled from the interfaces of `Submission/Work/KMTAreas/A4Z/`:

* `A4Z.lipTwoGen` — Proposition `lip-2` with a free support window and a spatial tail clause;
* `A4Z.structDecompClaim_of_lipGen` — Corollary `struct-dual` (Hahn--Banach);
* `A4Z.propdualSecondClaim_of_structDecompClaim` — Proposition `propdual-second`;
* `A4Z.structIiiSecondClaim_of_propdualSecondClaim` — Corollary `struct-iii-second` (uses `A3`);
* `A4Z.sivSecondClaim_of_structIiiSecondClaim` — Corollary `siv-second` (uses `off-decay`);
* `A4Z.offDecayTwo` — Lemma `iw-prop`(i), off-diagonal decay (from `AreaA1`);
* `A4Z.pairingBound_of_sivSecondClaim` — the transposition/self-adjointness bookkeeping;
* `A4Z.Assembly` — the final duality `(ℓ¹)' = ℓ^∞` and the passage from the pairing bound to the
  `ℓ¹` estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Assembly
import Submission.Work.KMTAreas.A4Z.lipTwoGenTail
import Submission.Work.KMTAreas.A4Z.offDecayTwo
import Submission.Work.KMTAreas.A4Z.structDecompClaim_of_lipGen
import Submission.Work.KMTAreas.A4Z.structIiiSecondClaim_of_propdualSecondClaim
import Submission.Work.KMTAreas.A4Z.sivSecondClaim_of_structIiiSecondClaim
import Submission.Work.KMTAreas.A4Z.pairingBound_of_sivSecondClaim

namespace Work.KMTAreas.A4

theorem improvTwoZ (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hPel : Work.KMTContract.PeluseInverseKMT P) (hA3 : Work.KMTContract.PolyImproving (P - Polynomial.X)) : ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧ ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) → Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) g = 0 → MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfZ N P f g x) 1 MeasureTheory.Measure.count ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  -- Corollary `siv-second` from the chain of §5.2
  have hSiv : Work.KMTAreas.A4Z.SivSecondClaim P :=
    Work.KMTAreas.A4Z.sivSecondClaim_of_structIiiSecondClaim P hP
      (fun ρ hρ0 hρ1 => Work.KMTAreas.A4Z.offDecayTwo hA1 ρ hρ0 hρ1)
      (Work.KMTAreas.A4Z.structIiiSecondClaim_of_propdualSecondClaim P hP hA1 hA3
        (Work.KMTAreas.A4Z.propdualSecondClaim_of_structDecompClaim P hP hA1
          (Work.KMTAreas.A4Z.structDecompClaim_of_lipGen P hP
            (Work.KMTAreas.A4Z.lipTwoGenTail P hP hPel))))
  obtain ⟨c, hc, hSivc⟩ := hSiv
  -- the pairing bound, and the final `(ℓ¹)' = ℓ^∞` duality
  exact ⟨c, hc, Work.KMTAreas.A4Z.improvTwoZ_of_pairingBound P c hc
    (Work.KMTAreas.A4Z.pairingBound_of_sivSecondClaim P c hc hSivc)⟩

end Work.KMTAreas.A4
