import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.chiRowDict
import Submission.Work.BoseBoxFock.pinQ_etaOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem honestPins {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    {e : Fin ((HM μ).m) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ D : ℝ, ∀ x, ‖e l x‖ ≤ D)
    (hsupp : ∀ l, Function.support (e l)
      ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v)))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hpairC : ∀ (k : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin ((HM μ).m)),
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
        * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
      = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) * (HM μ).f k l : ℝ) : ℂ))
    (hpairS : ∀ (s : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin ((HM μ).m)), s ≠ 0 →
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
        * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
      = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) * (HM μ).g s l : ℝ) : ℂ))
    (hpin0 : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3))⁻¹ : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z) :
    ((fun z => ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
        * Work.BoseDict.etaOf e (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k • (HM μ).f k) z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.chiMode (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
    ∧ ((fun z => ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
        * Work.BoseDict.etaOf e (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s • (HM μ).g s) z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.thMode (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N) := by
  classical
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hℓ]
  -- the modes `e l` are square integrable: the orthonormality pin gives the
  -- diagonal integral `1 ≠ 0`, hence integrability of `‖e l‖²`.
  have hmemE : ∀ l : Fin ((HM μ).m),
      MeasureTheory.MemLp (e l) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    fun l => Work.BoseBoxFock.memLp_two_of_orth_pairing horth
      (fun l => (hmeas l).aestronglyMeasurable) l
  constructor
  · -- ## the χ-row
    have hpairC' : ∀ (k : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin ((HM μ).m)),
        (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
          * Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).f k l : ℝ) : ℂ) := by
      intro k l
      rw [hell]
      exact hpairC k l
    have hmemQ : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        MeasureTheory.MemLp (Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k)) 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      fun k => (Work.BoseBoxFock.memLp_modes (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.ellH_pos v μ)).1 _
    have hq : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k)
          =ᵐ[MeasureTheory.volume] fun x =>
            ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
              * Work.BoseDict.etaOf e ((HM μ).f k) x := by
      intro k
      have hh := Work.BoseBoxFock.qVec_eq_etaOf_of_pairing v μ (HM μ) e horth hpairC' hmemE hmemQ k
      rwa [hell] at hh
    have hC : (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k • (HM μ).f k)
        = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            Work.BoseK15.corpusBox.hatChi (Work.BoseBox.sideAt μ (BoseGases.a v)
              • Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k)
              • (HM μ).f k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Work.BoseBoxFock.honest_hatChi_eq v h fc fu HM μ hℓ k,
        Work.BoseBoxFock.smul_kmomLab (ne_of_gt hℓ) (HM μ).N k]
    exact Work.BoseBoxFock.pin_chiMode_of_sum hℓ hC hq
  · -- ## the χ²-row
    have hpairS' : ∀ (s : Work.BoseBoxFock.Lab (HM μ).N) (l : Fin ((HM μ).m)), s ≠ 0 →
        (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z)
          * Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N s) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * (HM μ).g s l : ℝ) : ℂ) := by
      intro s l hs
      rw [hell]
      exact hpairS s l hs
    have hmemT : ∀ s : Work.BoseBoxFock.Lab (HM μ).N,
        MeasureTheory.MemLp (Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N s)) 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      fun s => (Work.BoseBoxFock.memLp_modes (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.ellH_pos v μ)).2.1 _
    have hqS : ∀ s : Work.BoseBoxFock.Lab (HM μ).N, s ≠ 0 →
        Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s)
          =ᵐ[MeasureTheory.volume] fun x =>
            ((Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) : ℝ) : ℂ)
              * Work.BoseDict.etaOf e ((HM μ).g s) x := by
      intro s hs
      have hh := Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing v μ (HM μ) e horth hpairS' hmemE
        hmemT s hs
      rwa [hell] at hh
    have hex : Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)
        = Finset.univ.filter (fun s : Work.BoseBoxFock.Lab (HM μ).N => s ≠ 0) := by
      unfold Work.BoseB7.excited
      exact (Finset.filter_ne' Finset.univ (0 : Work.BoseBoxFock.Lab (HM μ).N)).symm
    have hC' : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s • (HM μ).g s)
        = ∑ s with s ≠ 0,
            Work.BoseK15.corpusBox.hatChiSq (Work.BoseBox.sideAt μ (BoseGases.a v)
              • Work.BoseBoxFock.kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s)
              • (HM μ).g s := by
      rw [hex]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Work.BoseBoxFock.honest_hatChiSq_eq v h fc fu HM μ hℓ s,
        Work.BoseBoxFock.smul_kmomLab (ne_of_gt hℓ) (HM μ).N s]
    exact Work.BoseBoxFock.pin_thMode_of_sum hℓ hC' hqS

end Work.BoseBoxFock
