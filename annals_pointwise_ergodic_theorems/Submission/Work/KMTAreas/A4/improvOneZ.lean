/-
# Theorem improv(i) of Krause--Mirek--Tao 5.1 in the Z-language

This file proves the target Work.KMTAreas.A4.improvOneZ.  The proof is the paper 5.1, split into
the chain

  hPel -> LipWinA -> StructWinA -> PropdualAClaim -> StructiiiAClaim -> SivClaimZ -> improvOneZ

(the pieces live in the sibling modules A4/peluseLipL1TailA + A4/LipOutputTailA, A4/structWinA,
A4/propdualWinA, A4/structiiiWinA, A4/sivClaimZ; see A4/improvOneZDefs.lean for the interfaces).
What this file adds is

* pairingBoundOne_of_sivHyp -- the final duality of 5.1(i): from Corollary siv for the dual
  function of (phi, g) we get the pairing bound for finitely supported 1-bounded phi, whenever
  Pi f = 0.  The ingredients are the transposition identity (A4.TransposeFinSupp), the
  self-adjointness of the projection Pi (A4.kmtProjSelfAdjoint) and Cauchy--Schwarz;
* improvOneZ_of_sivClaimZ -- the L1 estimate itself, by the elementary duality (L1) = Linf
  (A4Z.eLpNorm_one_le_of_bilinPair_le).
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Assembly
import Submission.Work.KMTAreas.A4.TransposeFinSupp
import Submission.Work.KMTAreas.A4.kmtProjSelfAdjoint
import Submission.Work.KMTAreas.A4.summable_mul_shift_mul_of_sq
import Submission.Work.KMTPlan.A6.memLp_kmtProj
import Submission.Work.KMTAreas.A4.peluseLipL1TailA
import Submission.Work.KMTAreas.A4.structWinA
import Submission.Work.KMTAreas.A4.propdualWinA
import Submission.Work.KMTAreas.A4.structiiiWinA
import Submission.Work.KMTAreas.A4.sivClaimZ
import Submission.Work.KMTAreas.A4.offDecayKMT

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger (GoodMajorArcs)

/-! ## Elementary summability and Cauchy--Schwarz for the bilinear pairing -/

/-- A product of two l2 functions is summable, by the elementary 2ab <= a^2 + b^2. -/
theorem summable_mul_of_memLp_two {u f : ℤ → ℂ}
    (hu : MemLp u 2 Measure.count) (hf : MemLp f 2 Measure.count) :
    Summable (fun x : ℤ => u x * f x) := by
  have h1 := memLp_two_count_summable_norm_sq hu
  have h2 := memLp_two_count_summable_norm_sq hf
  have h3 := summable_mul_shift_mul_of_sq (f := u) (g := f) (φ := fun _ => (1 : ℂ)) 0 0 h1 h2
    ⟨1, fun x => by simp⟩
  simpa using h3

/-- Cauchy--Schwarz for the bilinear pairing. -/
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

/-! ## The final duality of 5.1(i) -/

/-- The pairing bound of Theorem improv(i) at fixed constants, from Corollary siv for the first
dual function.  For finitely supported 1-bounded phi, we get the bound C 2^(-cl) |f|_2 |g|_2 on
the pairing of AhalfZ N P f g with phi, whenever (l, l - Log N) has good major arcs and
Pi_{<=l,<=-Log N+l} f = 0. -/
theorem pairingBoundOne_of_sivHyp (P : Polynomial ℤ) (c ρ Cρ : ℝ) (C : NNReal)
    (hSiv : SivHyp P c ρ Cρ C) :
    ∀ (N l : ℕ) (f g φ : ℤ → ℂ), 1 ≤ N →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count → FinSupp φ →
      (∀ x : ℤ, ‖φ x‖ ≤ 1) →
      GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
      Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) f = 0 →
      ‖bilinPair (AhalfZ N P f g) φ‖ₑ
        ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  intro N l f g φ hN hf hg hfin hφ1 harc hproj
  have hmemu : MemLp (AhalfTranspose N P φ g) 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (eLpNorm_ahalfTranspose_le_of_bdd N P hφ1) hg.eLpNorm_lt_top)
  have hmemPu : MemLp (Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
      (AhalfTranspose N P φ g)) 2 Measure.count :=
    Work.KMTPlan.A6.memLp_kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) hmemu
  have hsum1 : Summable (fun x : ℤ => AhalfTranspose N P φ g x * f x) :=
    summable_mul_of_memLp_two hmemu hf
  have hsum2 : Summable (fun x : ℤ =>
      Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
        (AhalfTranspose N P φ g) x * f x) :=
    summable_mul_of_memLp_two hmemPu hf
  have hzero : bilinPair (Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
      (AhalfTranspose N P φ g)) f = 0 := by
    rw [show bilinPair (Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
          (AhalfTranspose N P φ g)) f
        = ∑' x : ℤ, Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
            (AhalfTranspose N P φ g) x * f x from rfl,
      Work.KMTAreas.A4.kmtProjSelfAdjoint ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) hmemu hf]
    rw [tsum_congr (fun x : ℤ => by
      rw [show Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) f x = 0 from
        congrFun hproj x, mul_zero])]
    exact tsum_zero
  have hsplit : bilinPair (AhalfTranspose N P φ g) f
      = bilinPair (AhalfTranspose N P φ g - Work.KMTContract.kmtProj ρ l
          ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g)) f := by
    have hsub : bilinPair (AhalfTranspose N P φ g) f - bilinPair (Work.KMTContract.kmtProj ρ l
          ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g)) f
        = bilinPair (AhalfTranspose N P φ g - Work.KMTContract.kmtProj ρ l
            ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g)) f := by
      simp only [bilinPair]
      rw [← hsum1.tsum_sub hsum2]
      exact tsum_congr fun x => by simp only [Pi.sub_apply]; ring
    rw [hzero, sub_zero] at hsub
    exact hsub
  rw [Work.KMTAreas.A4.bilinPair_AhalfZ_eq_transpose_of_finSupp hfin N P, hsplit]
  refine (enorm_bilinPair_le_of_memLp (hmemu.sub hmemPu) hf).trans ?_
  have hsiv := hSiv N l g φ hN hg hφ1 harc
  have hsivC : eLpNorm (fun x : ℤ => AhalfTranspose N P φ g x - Work.KMTContract.kmtProj ρ l
        ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g) x) 2 Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
        * eLpNorm g 2 Measure.count := by
    simpa only [← ENNReal.ofReal_coe_nnreal] using hsiv
  have hfun : (AhalfTranspose N P φ g - Work.KMTContract.kmtProj ρ l
        ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g))
      = fun x : ℤ => AhalfTranspose N P φ g x - Work.KMTContract.kmtProj ρ l
          ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g) x := rfl
  rw [hfun]
  calc eLpNorm (fun x : ℤ => AhalfTranspose N P φ g x - Work.KMTContract.kmtProj ρ l
          ((l : ℤ) - Work.Analysis.EndVar.logN N) (AhalfTranspose N P φ g) x) 2 Measure.count
        * eLpNorm f 2 Measure.count
      ≤ (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
            * eLpNorm g 2 Measure.count) * eLpNorm f 2 Measure.count := by
        gcongr
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring

/-- Theorem improv(i) from Corollary siv: the elementary L1/Linf duality converts the pairing
bound of pairingBoundOne_of_sivHyp into the L1 estimate of Theorem improv(i). -/
theorem improvOneZ_of_sivClaimZ (P : Polynomial ℤ) (hSiv : SivClaimZ P) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
        Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) f = 0 →
        eLpNorm (fun x : ℤ => AhalfZ N P f g x) 1 Measure.count
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  obtain ⟨c, hc, hS⟩ := hSiv
  refine ⟨c, hc, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨Cρ, hCρ, C, hC, hSC⟩ := hS ρ hρ0 hρ1
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro N l f g hN hf hg harc hproj
  exact Work.KMTAreas.A4Z.eLpNorm_one_le_of_bilinPair_le _
    (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
      * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
    (fun φ hfin hφ1 =>
      pairingBoundOne_of_sivHyp P c ρ Cρ C hSC N l f g φ hN hf hg hfin hφ1 harc hproj)

/-! ## The chain of 5.1(i) -/

/-- **Proposition  at the window **, from Peluse's inverse theorem: the window-parameterised
 (), converted to the  form. -/
theorem lipWinA_of_peluse (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hPel : Work.KMTContract.PeluseInverseKMT P) :
    ∀ A : ℝ, 1 ≤ A → LipWinA P A :=
  fun A hA => Work.KMTAreas.A4.lipOutputTailA_of_lipL1A P hP
    (Work.KMTAreas.A4.peluseLipL1TailA P hP hPel) A hA

/-- **Proposition  at the window **, from  and Peluse's inverse theorem. -/
theorem propdualAClaim_of_peluse (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hPel : Work.KMTContract.PeluseInverseKMT P) :
    ∀ A : ℝ, 1 ≤ A → PropdualAClaim P A :=
  fun A hA => Work.KMTAreas.A4.propdualWinA P hP hA1 A hA
    (Work.KMTAreas.A4.structWinA P hP A hA (lipWinA_of_peluse P hP hPel A hA))

/-- Corollary siv, from the chain of modules: the window-parameterised struct-iii bound for all
windows A >= 1 (from A1, the Peluse inverse theorem and PolyImproving (X-P)), together with the
off-diagonal decay of the Ionescu--Wainger projections (Lemma iw-prop(i)), give Corollary siv
without any support hypotheses. -/
theorem sivClaimZ_of_chain (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hPel : Work.KMTContract.PeluseInverseKMT P)
    (hA3 : Work.KMTContract.PolyImproving (Polynomial.X - P))
    (hOff : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → OffDecayClaim ρ) :
    SivClaimZ P :=
  Work.KMTAreas.A4.sivClaimZ P hP
    (fun A hA => Work.KMTAreas.A4.structiiiWinA P hP hA1 hA3 A hA
      (propdualAClaim_of_peluse P hP hA1 hPel A hA)) hOff

/-- **Theorem improv(i)** from the chain of the paper 5.1, with the off-diagonal decay of the
Ionescu--Wainger projections as the only remaining input. -/
theorem improvOneZ_of_offDecay (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hPel : Work.KMTContract.PeluseInverseKMT P)
    (hA3 : Work.KMTContract.PolyImproving (Polynomial.X - P))
    (hOff : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → OffDecayClaim ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
        Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) f = 0 →
        eLpNorm (fun x : ℤ => AhalfZ N P f g x) 1 Measure.count
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
  improvOneZ_of_sivClaimZ P (sivClaimZ_of_chain P hP hA1 hPel hA3 hOff)

end Work.KMTAreas.A4

namespace Work.KMTAreas.A4

theorem improvOneZ (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hPel : Work.KMTContract.PeluseInverseKMT P) (hA3 : Work.KMTContract.PolyImproving (Polynomial.X - P)) : ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧ ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) → Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) f = 0 → MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfZ N P f g x) 1 MeasureTheory.Measure.count ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  exact improvOneZ_of_offDecay P hP hA1 hPel hA3
    (Work.KMTAreas.A4.offDecayKMT hA1)

end Work.KMTAreas.A4
