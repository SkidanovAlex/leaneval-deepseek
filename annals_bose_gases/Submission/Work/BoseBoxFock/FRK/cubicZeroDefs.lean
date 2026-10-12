import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.FRK.lowBandSqrtDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# curric-46 design `cbc/bose_deadrow_cubicfree.md` — NODE B (`PotCubicFree_exists`)

* There is NO ordering mismatch: on `L²(ℝ³)`, `(Q_j f_L)^* = f_L Q_j`, so the corpus word
  `⟨f_L Q_j P_i Φ, w₁ Q_j Q_i Φ⟩` (`q3lowWord`, whole-space `lowMult` of the zero extension) IS
  FS's `⟨Φ, P_i Q_{L,j} w₁ Q_j Q_i Φ⟩` with FS's `Q_L = Q f_L(√−Δ_{ℝ³})`; FS's "not self-adjoint"
  remark concerns `Q_L` itself and is irrelevant here.
* The pixel identity `W₁(k) = ℓ⁻³Ŵ₁(k−τ)` is an artefact of comparing NON-symmetrised
  coefficients: `potCubic` puts `f(s−k)` in slot `i` and `f k` in slot `j`; the word's basis
  expansion is matched exactly by the transposed assignment, and the two assignments agree on
  permutation-invariant states (`slotSwap_rankOne`).
* REAL defect: `excited = univ.erase 0` drops the `k = 0` lattice term (an exact term of the
  periodised expansion, not a Riemann cell): `ℓ⁻³Ŵ₁(0)Σ_s f_L(s)a₀†ã_s†a(q₀)a(q_s)`, of size
  `≲ ℓ⁻³a√n·𝓜·√n₊`.  Payable by `γℓ⁻²n₊ + o(errKafz)` for every `γ > 0`, NOT by `½errKafz` alone
  under `n₊ ≤ 𝓜` (short by `t^{-1/8}`).  Fix: dictionary over `Finset.univ`, zero cell in the low
  band (whose allowance carries the gap).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- (B1) **The corrected dictionary** — `PotCubicFree` with the `k`-sum over ALL lattice labels
(`k = 0` included).  TRUE: equals `q3lowWord` up to (i) `k`-images, (ii) periodic-vs-whole-space
`f_L` images (both on the face layer where `χ` is flat: `O(d^K)` for every `K`), (iii) the
`Lab N`/`uvCut` truncation (`Nmin`; kinetic energy from `IsLowB`). -/
noncomputable def PotCubicFreeU (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      (Finset.univ : Finset (Lab (HM μ).N))
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ Work.BoseBoxFix.q3lowWord fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Submission.BoseGases.g0 v h) 0)
                    (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ


/-- (B3) the zero cell alone: `mode(excited) − mode(univ) = −(k = 0 term)`, at gap fraction `γ`. -/
noncomputable def PotCubicZeroCell (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C γ : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                      (Work.BoseB7.excited (Lab (HM μ).N))
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              - (∫ x : Submission.BoseGases.X n,
                  star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                    * potCubic (fun T => boxSlotSum e T) (HM μ).f (HM μ).g
                        (Finset.univ : Finset (Lab (HM μ).N))
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ γ * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

end Work.BoseBoxFock.FRK


namespace Work.BoseBoxFock.FRK
open Work.BoseB4 Work.BoseDict
set_option maxHeartbeats 4000000
/-- REVIEW wiring: zero cell as a SEPARATE summand; low band reserve from the existing leaf
`LowBandSqrt` (untouched) + `LowBandSqrtArith` at `2K`. -/
theorem PotCubicG_of_freeU_zero_sqrt (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₁ ε₂ ε₃ ε₄ C₁ C₃ K γ : ℝ)
    (hK : 0 ≤ K) (hγ : γ ≤ 3 / 400)
    (hfree : PotCubicFreeU v h fc fu R J Nmin ε₁ C₁)
    (hzero : PotCubicZeroCell v h fc fu R J Nmin ε₃ C₃ γ)
    (hS : LowBandSqrt v h fc fu J Nmin ε₂ K)
    (hA : LowBandSqrtArith v h fc fu Nmin ε₄ (2 * K)) :
    PotCubicG v h fc fu R J Nmin (min (min ε₁ ε₂) (min ε₃ ε₄)) (C₁ + C₃) := by
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin
    hKp hLp hθp T_NH hTNH
  have hm : ∀ {ε : ℝ}, min (min ε₁ ε₂) (min ε₃ ε₄) ≤ ε → Work.BoseBoxFix.Adm v ε μ :=
    fun hle => ⟨hAdm.1, le_trans hAdm.2.1 hle, hAdm.2.2⟩
  have h1 := hfree HM hMono μ (hm (le_trans (min_le_left _ _) (min_le_left _ _))) hJ n Φ hn hnorm
    hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin hKp hLp hθp T_NH hTNH
  have h2 := hS HM hMono μ (hm (le_trans (min_le_left _ _) (min_le_right _ _))) hJ n Φ hn hnorm
    hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin hKp hLp hθp T_NH hTNH
  have h3 := hzero HM hMono μ (hm (le_trans (min_le_right _ _) (min_le_left _ _))) hJ n Φ hn hnorm
    hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin hKp hLp hθp T_NH hTNH
  have h4 := hA HM hMono μ (hm (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hb : (Work.BoseBox.paramsAt μ (BoseGases.a v)).b = 1 / 16 := rfl
  rw [hb] at h4 ⊢
  have hcn := cnPlus_nonneg' (Work.BoseBox.sideAt μ (BoseGases.a v))
    (Φ : Submission.BoseGases.X n → ℝ)
  have hℓ := Work.BoseBox.sideAt_pos hAdm.1 hav
  have hz : 0 ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ) := zpow_nonneg hℓ.le _
  have hgap : 0 ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
      * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ) := mul_nonneg hz hcn
  have h4' := mul_le_mul_of_nonneg_right h4 hcn
  have h3e : Work.BoseFixR.errKafz v R μ (C₁ + C₃)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₃ := by
    simp only [Work.BoseFixR.errKafz]; ring
  rw [h3e]
  nlinarith [h1, h2, h3, h4', hgap, mul_le_mul_of_nonneg_right hγ hgap]
end Work.BoseBoxFock.FRK
