import ChallengeDeps
import Submission.Work.BoseB7AK.W1low.chat_sub_le
import Submission.Work.BoseGateFS.GateHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.ChiPin` — the two χ-rows of the honest bundle

Two of the rows of `HonestRows` that are *theorems* rather than inputs:

* `hon_box` — the **box-model equation** of the honest Fock data: the
  commutator kernel `F.ccrK i j` is the corpus box kernel at the momentum
  difference.  It is the definition of `Work.BoseB4.boxFockData` (the field
  `Work.BoseB4.BoxData.boxKernel`), so it costs nothing at the honest model;
* `chat_chiFun_eq` — the **χ-pin**: the `chat`-transform of the scaled bump is
  `ℓ³` times the corpus `χ̂` at `ℓ • p` (`Work.BoseB4.BoxData.integral_chiLam_mul_cos`).
  This is the identity that makes `E.hatChi k = corpusBox.hatChi (ℓ • kmom k)`
  (the field `K15Input.hatChi_eq`, hence the box-model equation `hE` of
  `Work.BoseK15.exists_K15Input_box`) *provable* at the honest environment,
  whose `hatChi` is the *normalised* `chat (χ_ℓ)` with the normaliser
  `chat (χ_ℓ²)(0) = ℓ³` (`Work.BoseFixR.chat_chiSq_zero`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-- `χ_ℓ` is integrable. -/
lemma integrable_chiFun (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z) :=
  (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))

/-- The corpus `χ̂` at `ℓ • p` is the normalised `chat`-transform of `χ_ℓ`
(`Work.BoseFixR.ChatChiFunEq`).  Proved here directly, from the `chat`-cosine
identity (`Work.BoseB7AK.W1low.chat_eq_integral_cos`) and the scaling lemma
`Work.BoseB4.BoxData.integral_chiLam_mul_cos`, so that this area does not depend
on the module that happens to carry the `BoseFixR` copy. -/
theorem chat_chiFun_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (Work.BoseFixR.chiFun ℓ) p
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (integrable_chiFun ℓ hℓ) p]
  exact Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ p

/-- `χ_ℓ²` is integrable. -/
lemma integrable_chiFun_sq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z ^ 2) := by
  have hcs : HasCompactSupport
      (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z ^ 2) := by
    refine (Submission.BoseGases.chiScale_hasCompactSupport (ℓ := ℓ) (ne_of_gt hℓ)).mono ?_
    intro x hx
    exact Function.mem_support.mpr
      (fun h => Function.mem_support.mp hx (by simp [Work.BoseFixR.chiFun, h]))
  exact ((Submission.BoseGases.chiScale_continuous ℓ).pow 2).integrable_of_hasCompactSupport hcs

/-- The corpus `χ̂²` at `ℓ • q` is the normalised `chat`-transform of `χ_ℓ²`. -/
theorem chat_chiFun_sq_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun ℓ z ^ 2) q
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChiSq (ℓ • q) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (integrable_chiFun_sq ℓ hℓ) q]
  exact Work.BoseB4.BoxData.integral_chiLam_sq_mul_cos Work.BoseK15.corpusBox hℓ q

/-- **The box-model equation at the honest model**: the commutator kernel of the
honest Fock data is the corpus box kernel at the momentum difference — this is
the definition of `boxFockData` (`boxFockData_ccrK`). -/
theorem hon_box {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < a v) :
    ∀ i j : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).F.ccrK i j
        = Work.BoseK15.corpusBox.hatChiSq
            ((HonestBoxFam v h fc fu HM μ).E.ell •
              ((HonestBoxFam v h fc fu HM μ).F.kmom i
                - (HonestBoxFam v h fc fu HM μ).F.kmom j))
          - Work.BoseK15.corpusBox.hatChi
              ((HonestBoxFam v h fc fu HM μ).E.ell •
                (HonestBoxFam v h fc fu HM μ).F.kmom i)
            * Work.BoseK15.corpusBox.hatChi
                ((HonestBoxFam v h fc fu HM μ).E.ell •
                  (HonestBoxFam v h fc fu HM μ).F.kmom j) := by
  intro i j
  have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (a v) := by
    simp only [Work.BoseBoxFock.ellH, Work.BoseBox.sideAt_pos hμ hav, ↓reduceIte]
  simp only [hell, Work.BoseBoxFock.HonestBoxFam, Work.BoseB4.boxFockData,
    Work.BoseB4.b7FockDataBox, Work.BoseB4.b7FockDataBox_ccrK,
    Work.BoseB4.ccrKernel_eq_boxKernel,
    Work.BoseB4.BoxData.boxKernel, Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs]

end Work.BoseGateFS
