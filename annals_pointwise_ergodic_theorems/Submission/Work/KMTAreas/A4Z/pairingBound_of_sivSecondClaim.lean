/-
# The pairing bound of Theorem `improv`(ii) from Corollary `siv-second`

Krause--Mirek--Tao, §5.2.  The last step of the proof of Theorem `improv`(ii) is the duality
`(ℓ¹)' = ℓ^∞`: from the `ℓ²` bound of Corollary `siv-second` for the minor-arc part of the second
dual function one deduces the *pairing* bound

  `|⟨Ã_N(f,g), φ⟩| ≤ C 2^{-cl} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`

for every finitely supported `1`-bounded test function `φ`, on good major arcs, whenever
`Π_{≤l,≤d(l-Log N)} g = 0`.  The assembly of Theorem `improv`(ii) from this pairing bound is
`Work.KMTAreas.A4Z.improvTwoZ_of_pairingBound` (`Submission/Work/KMTAreas/A4Z/Assembly.lean`).

The proof is the paper's duality, with the three ingredients

* the transposition identity `⟨Ã_N(f,g), φ⟩ = ⟨Ã_N^{**}(f,φ), g⟩`
  (`Work.KMTAreas.A4.transposeTwoFinSupp`, which needs only `FinSupp φ`);
* the self-adjointness of `Π = Π_{≤l,≤d(l-Log N)}` on `ℓ²(ℤ)`
  (`Work.KMTAreas.A4.kmtProjSelfAdjoint`), together with `Π g = 0`, which kills the projection of
  `Ã_N^{**}(f,φ)` in the pairing against `g`;
* Cauchy--Schwarz for the bilinear pairing `⟨u,v⟩ = ∑_x u x v x` on `ℓ²(ℤ)`.

The hypothesis `‖φ‖_∞ ≤ 1` is *not* upgraded to an `ℓ²` bound on `φ` (a finitely supported
`1`-bounded function has arbitrarily large `ℓ²` norm): it is used exactly once, to make
`Ã_N^{**}(f,φ)` an `ℓ²` function of `f` alone -- which is the content of Corollary `siv-second`,
via `Work.KMTAreas.A4Z.memLp_ahalfTransposeTwo_of_bdd`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4Z.memLp_ahalfTransposeTwo_of_bdd
import Submission.Work.KMTAreas.A4.kmtProjSelfAdjoint
import Submission.Work.KMTAreas.A4.transposeTwoFinSupp
import Submission.Work.KMTAreas.A4.memLp_two_count_summable_norm_sq
import Submission.Work.KMTAreas.A4.summable_mul_shift_mul_of_sq
import Submission.Work.KMTPlan.A6.memLp_kmtProj

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTContract

namespace Work.KMTAreas.A4Z

/-! ## Elementary summability and Cauchy--Schwarz for the bilinear pairing -/

/-- A product of two `ℓ²(ℤ)` functions is summable, by the elementary `2ab ≤ a² + b²`. -/
theorem summable_mul_of_memLp_two {u f : ℤ → ℂ}
    (hu : MemLp u 2 Measure.count) (hf : MemLp f 2 Measure.count) :
    Summable (fun x : ℤ => u x * f x) := by
  have h1 := Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hu
  have h2 := Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hf
  have h3 := Work.KMTAreas.A4.summable_mul_shift_mul_of_sq (f := u) (g := f)
    (φ := fun _ : ℤ => (1 : ℂ)) 0 0 h1 h2 ⟨1, fun x => by simp⟩
  simpa using h3

/-- Cauchy--Schwarz for the bilinear pairing `⟨u, v⟩ = ∑_x u x · v x` on `ℓ²(ℤ)`. -/
theorem enorm_bilinPair_le_of_memLp {u v : ℤ → ℂ}
    (hu : MemLp u 2 Measure.count) (hv : MemLp v 2 Measure.count) :
    ‖bilinPair u v‖ₑ ≤ eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  have h1 : ‖bilinPair u v‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := by
    rw [bilinPair]
    exact enorm_tsum_le_tsum_enorm
  have h2 : (∑' x : ℤ, ‖u x * v x‖ₑ) = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := by
    simp only [eLpNorm_one_eq_lintegral_enorm MeasureTheory.AEStronglyMeasurable.of_discrete, lintegral_count, enorm_mul]
  have h3 : eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count
      ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
    refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) (measurable_of_countable u).aestronglyMeasurable (measurable_of_countable v).aestronglyMeasurable ?_
      (p := 2) (q := 2) (r := 1)
    filter_upwards with x
    simp
  calc ‖bilinPair u v‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := h1
    _ = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := h2
    _ ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := h3
    _ = eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by rw [one_mul]

/-! ## The final duality of §5.2 -/

/-- **The pairing bound of Theorem `improv`(ii) at fixed constants.**  From Corollary
`siv-second` for the second dual function `Ã_N^{**}(f,φ)` of the `ℓ²` function `f` and the
`1`-bounded test function `φ`: for every finitely supported `1`-bounded `φ` the pairing of
`Ã_N(f,g)` with `φ` is bounded by `C 2^{-cl} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`, on good major arcs, whenever
`Π_{≤l,≤d(l-Log N)} g = 0`. -/
theorem pairingBound_of_sivSecondHyp (P : Polynomial ℤ) (c : ℝ) (ρ Cρ : ℝ) (C : NNReal)
    (hSiv : SivSecondHyp P c ρ Cρ C) :
    ∀ (N l : ℕ) (f g φ : ℤ → ℂ), 1 ≤ N →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count → FinSupp φ →
      (∀ x : ℤ, ‖φ x‖ ≤ 1) →
      GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
      kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) g = 0 →
      ‖bilinPair (AhalfZ N P f g) φ‖ₑ
        ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  intro N l f g φ hN hf hg hfin hφ1 harc hproj
  set k : ℤ := (P.natDegree : ℤ) * ((l : ℤ) - logN N) with hk
  -- the second dual function `Ã_N^{**}(f,φ)` is an `ℓ²` function, and so is its projection
  have hU : MemLp (fun x : ℤ => AhalfTranspose₂ N P f φ x) 2 Measure.count :=
    (memLp_ahalfTransposeTwo_of_bdd N P hN hf hφ1).1
  have hPU : MemLp (fun x : ℤ => kmtProj ρ l k (AhalfTranspose₂ N P f φ) x) 2 Measure.count :=
    Work.KMTPlan.A6.memLp_kmtProj ρ l k hU
  have hsum1 : Summable (fun x : ℤ => AhalfTranspose₂ N P f φ x * g x) :=
    summable_mul_of_memLp_two hU hg
  have hsum2 : Summable (fun x : ℤ => kmtProj ρ l k (AhalfTranspose₂ N P f φ) x * g x) :=
    summable_mul_of_memLp_two hPU hg
  -- the projection of the second dual function pairs to `0` with `g`, because `Π g = 0`
  have hzero : bilinPair (kmtProj ρ l k (AhalfTranspose₂ N P f φ)) g = 0 := by
    rw [show bilinPair (kmtProj ρ l k (AhalfTranspose₂ N P f φ)) g
        = ∑' x : ℤ, kmtProj ρ l k (AhalfTranspose₂ N P f φ) x * g x from rfl,
      Work.KMTAreas.A4.kmtProjSelfAdjoint ρ l k hU hg]
    rw [tsum_congr (fun x : ℤ => by
      rw [show kmtProj ρ l k g x = 0 from congrFun hproj x, mul_zero])]
    exact tsum_zero
  have hsplit : bilinPair (AhalfTranspose₂ N P f φ) g
      = bilinPair (fun x : ℤ => AhalfTranspose₂ N P f φ x
          - kmtProj ρ l k (AhalfTranspose₂ N P f φ) x) g := by
    have hsub : bilinPair (AhalfTranspose₂ N P f φ) g
        - bilinPair (kmtProj ρ l k (AhalfTranspose₂ N P f φ)) g
        = bilinPair (fun x : ℤ => AhalfTranspose₂ N P f φ x
            - kmtProj ρ l k (AhalfTranspose₂ N P f φ) x) g := by
      simp only [bilinPair]
      rw [← hsum1.tsum_sub hsum2]
      exact tsum_congr fun x => by ring
    rw [hzero, sub_zero] at hsub
    exact hsub
  -- Corollary `siv-second` in the vocabulary of the proof
  have hsivC : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f φ x
        - kmtProj ρ l k (AhalfTranspose₂ N P f φ) x) 2 Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm f 2 Measure.count := by
    have h := hSiv N l f φ hN hf hφ1 harc
    simp only [projTwo_apply] at h
    rw [← hk] at h
    simpa only [← ENNReal.ofReal_coe_nnreal] using h
  rw [Work.KMTAreas.A4.transposeTwoFinSupp hfin N P, hsplit]
  refine (enorm_bilinPair_le_of_memLp (hU.sub hPU) hg).trans ?_
  calc eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f φ x
          - kmtProj ρ l k (AhalfTranspose₂ N P f φ) x) 2 Measure.count
        * eLpNorm g 2 Measure.count
      ≤ (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
            * eLpNorm f 2 Measure.count) * eLpNorm g 2 Measure.count :=
        by gcongr
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring

/-- **The pairing bound of Theorem `improv`(ii) from Corollary `siv-second`.**  This is the final
duality step of §5.2: the hypothesis is `SivSecondHyp` for every `ρ ∈ (0,1]`, the conclusion the
pairing bound consumed by `Work.KMTAreas.A4Z.improvTwoZ_of_pairingBound`. -/
theorem pairingBound_of_sivSecondClaim (P : Polynomial ℤ) (c : ℝ) (hc : 0 < c) (hSiv : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧ Work.KMTAreas.A4Z.SivSecondHyp P c ρ Cρ C) : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧ ∀ (N l : ℕ) (f g φ : ℤ → ℂ), 1 ≤ N → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → Work.Analysis.InverseTheory.FinSupp φ → (∀ x : ℤ, ‖φ x‖ ≤ 1) → Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) → Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) g = 0 → ‖Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) φ‖ₑ ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  intro ρ hρ0 hρ1
  obtain ⟨Cρ, hCρ, C, hC, hSivC⟩ := hSiv ρ hρ0 hρ1
  exact ⟨Cρ, hCρ, C, hC, pairingBound_of_sivSecondHyp P c ρ Cρ C hSivC⟩

end Work.KMTAreas.A4Z
