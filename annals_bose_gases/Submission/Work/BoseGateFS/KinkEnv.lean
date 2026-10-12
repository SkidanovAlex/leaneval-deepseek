import ChallengeDeps
import Submission.Work.BoseGateFS.ChiPin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.KinkEnv` — the kinked-environment equation at the honest model

The field `kinkEnv F E` of the honest bundle is the environment
`Work.BoseK15.exists_K15Input_box` consumes: it wants
`E' = Q3Env.ofSect4 kmom z ℓ μ a K_H K_ℓ K_L d s ε_T b M 𝓜 δ f_L Ŵ₁ Ŵ₁ω τ W₁ω(0) χ`.

This module proves the two χ-rows that make that equation hold at
`KzEnvHon` (whose `χ̂`, `χ̂²` are the *normalised* `chat`-transforms of `χ_ℓ`):

* `honE_hatChi` — `E.hatChi k = corpusBox.hatChi (E.ell • F.kmom k)`;
* `honE_hatChiSq` — `E.hatChiSq k = corpusBox.hatChiSq (E.ell • F.kmom k)`.

They use `ChiPin.chat_chiFun_eq`, `ChiPin.chat_chiFun_sq_eq` and
`Work.BoseFixR.chat_chiSq_zero` (the normaliser `chat (χ_ℓ²)(0) = ℓ³`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The honest environment's `χ̂` is the corpus `χ̂` at `ℓ • ·`. -/
theorem honE_hatChi {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) (F : FockData Mode) (N : ℕ) :
    ∀ k : Mode,
      (KzEnvHon v h μ F fc fu N).hatChi k
        = Work.BoseK15.corpusBox.hatChi ((KzEnvHon v h μ F fc fu N).ell • F.kmom k) := by
  intro k
  have hℓ : 0 < Work.BoseBox.sideAt μ (a v) := Work.BoseBox.sideAt_pos hμ hav
  have h1 := chat_chiFun_eq (Work.BoseBox.sideAt μ (a v)) hℓ (F.kmom k)
  have h2 : Work.BoseFixR.chat
      (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (a v)) z ^ 2) 0
        = (Work.BoseBox.sideAt μ (a v)) ^ 3 :=
    Work.BoseFixR.chat_chiSq_zero hℓ
  simp only [Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs]
  rw [h1, h2]
  field_simp

/-- The honest environment's `χ̂²` is the corpus `χ̂²` at `ℓ • ·`. -/
theorem honE_hatChiSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) (F : FockData Mode) (N : ℕ) :
    ∀ k : Mode,
      (KzEnvHon v h μ F fc fu N).hatChiSq k
        = Work.BoseK15.corpusBox.hatChiSq ((KzEnvHon v h μ F fc fu N).ell • F.kmom k) := by
  intro k
  have hℓ : 0 < Work.BoseBox.sideAt μ (a v) := Work.BoseBox.sideAt_pos hμ hav
  have h1 := chat_chiFun_sq_eq (Work.BoseBox.sideAt μ (a v)) hℓ (F.kmom k)
  have h2 : Work.BoseFixR.chat
      (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (a v)) z ^ 2) 0
        = (Work.BoseBox.sideAt μ (a v)) ^ 3 :=
    Work.BoseFixR.chat_chiSq_zero hℓ
  simp only [Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs]
  rw [h1, h2]
  field_simp

end Work.BoseGateFS
