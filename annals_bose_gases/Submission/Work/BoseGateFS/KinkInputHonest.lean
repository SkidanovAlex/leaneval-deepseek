import ChallengeDeps
import Submission.Work.BoseB7AK.K15R.BoxInhabited
import Submission.Work.BoseGateFS.KinkEnv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.KinkInputHonest` — inhabiting the kinked bundle at the honest model

`Work.BoseB7AK.K15R.exists_K15Input_box` produces the (Ŵ₁ω-pointwise-free) K15R
bundle for a mode system `ℓ, kmom, f, g, F, T` and an environment `E` written as
`Q3Env.ofSect4 …`.  This module instantiates it at the **honest data**:
`kmom = kmomLab (ellH v μ) (HM μ).N`, `F`/`T` from `HonestBoxFam`, and `E` the
honest environment, whose `ofSect4`-form is `KinkEnv.hon_kinkEnv`.

The remaining hypotheses are exactly the honest §11/§12 rows of
`BOSE_BOXFOCK_LEAD.md` §5.6 (the rows of `Ŵ₁`, `Ŵ₁ω`, `ĝ`, `f_L`, and the
`ω`/`sum_diff`/`q2`/`α`/`intOne` rows), plus the two mode-geometry rows
`hℓ1 : 1 ≤ ℓ` and `hlat : OnDualLattice ℓ kmom` and the guarded label
arithmetic `haddO`/`haddI` (available from `LabAdd.kmomLab_sub_of_norm_le` with
the factor-2 `f_L` support and the cut radius `2Λ`, once the cube satisfies
`N ≥ Ng μ`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-- The honest family's Fock data. -/
noncomputable abbrev honF (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : FockData (Lab (HM μ).N) :=
  (HonestBoxFam v h fc fu HM μ).F

/-- The honest family's θ-mode data. -/
noncomputable abbrev honT (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : TildeData (honF v h fc fu HM μ) :=
  (HonestBoxFam v h fc fu HM μ).T

/-- The honest family's environment. -/
noncomputable abbrev honE (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : Q3Env (Lab (HM μ).N) :=
  (HonestBoxFam v h fc fu HM μ).E

/-- The honest cube's momentum map. -/
noncomputable abbrev honKmom (v : EuclideanSpace ℝ (Fin 3) → ℝ) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) : Lab (HM μ).N → EuclideanSpace ℝ (Fin 3) :=
  kmomLab (ellH v μ) (HM μ).N

/-- The honest family's **kinked** environment (the K15R input port). -/
noncomputable abbrev honK (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : Q3Env (Lab (HM μ).N) :=
  kinkEnv (honF v h fc fu HM μ) (honE v h fc fu HM μ)

/-- **The kinked K15R bundle at the honest model**, from the honest §11/§12 rows. -/
theorem exists_kinkInput_honest
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hav : 0 < a v) (hμ : 0 < μ)
    (hℓ1 : 1 ≤ ellH v μ)
    (hlat : Work.BoseK15.OnDualLattice (ellH v μ) (honKmom v HM μ))
    (hv : FSParamsView (honK v h fc fu HM μ))
    (fLf W1f W1omegaf : EuclideanSpace ℝ (Fin 3) → ℝ)
    (gHat : Lab (HM μ).N → ℝ)
    (hE' : honK v h fc fu HM μ
      = Work.BoseB4.Q3Env.ofSect4 (honKmom v HM μ) (honK v h fc fu HM μ).z
          (ellH v μ) (honK v h fc fu HM μ).mu (honK v h fc fu HM μ).aScat
          (honK v h fc fu HM μ).KH (honK v h fc fu HM μ).Kl (honK v h fc fu HM μ).KL
          (honK v h fc fu HM μ).d (honK v h fc fu HM μ).s (honK v h fc fu HM μ).eT
          (honK v h fc fu HM μ).b (honK v h fc fu HM μ).intM (honK v h fc fu HM μ).bigM
          (honK v h fc fu HM μ).delta fLf W1f W1omegaf
          (Work.BoseB4.tauFun (honK v h fc fu HM μ).eT (honK v h fc fu HM μ).s
            (honK v h fc fu HM μ).d (ellH v μ))
          (honK v h fc fu HM μ).W1omega0 Work.BoseB7AK.K15R.corpusBox)
    (haddO : ∀ i j : Lab (HM μ).N, (honK v h fc fu HM μ).fL i ≠ 0 →
      j ∈ (honF v h fc fu HM μ).PHset (honK v h fc fu HM μ) →
      honKmom v HM μ (i - j) = honKmom v HM μ i - honKmom v HM μ j)
    (haddI : ∀ i j : Lab (HM μ).N, (honK v h fc fu HM μ).fL i ≠ 0 →
      (honK v h fc fu HM μ).fL j ≠ 0 →
      honKmom v HM μ (i - j) = honKmom v HM μ i - honKmom v HM μ j)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hW1le : ∀ p : EuclideanSpace ℝ (Fin 3), |W1f p| ≤ Cw * (honK v h fc fu HM μ).aScat)
    (hW1decay : ∀ p : EuclideanSpace ℝ (Fin 3),
      |W1f p| * (1 + ‖p‖) ^ 2 ≤ Cw * (honK v h fc fu HM μ).aScat)
    (hW1grad : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖fderiv ℝ W1f p‖ ≤ Cw * (honK v h fc fu HM μ).aScat * (1 + ‖p‖))
    (hW1even : ∀ p : EuclideanSpace ℝ (Fin 3), W1f (-p) = W1f p)
    (hW1cd : ContDiff ℝ 1 W1f)
    (hW1om0 : ∃ C : ℝ, 0 ≤ C ∧ 0 ≤ (honK v h fc fu HM μ).W1omega0 ∧
      (honK v h fc fu HM μ).W1omega0 ≤ C * (honK v h fc fu HM μ).aScat)
    (hfL0 : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ fLf p)
    (hfL1 : ∀ p : EuclideanSpace ℝ (Fin 3), fLf p ≤ 1)
    (hfLe : ∀ p : EuclideanSpace ℝ (Fin 3), fLf (-p) = fLf p)
    (hfLsup : ∀ p : EuclideanSpace ℝ (Fin 3), fLf p ≠ 0 →
      ‖p‖ ≤ (honK v h fc fu HM μ).KL * Real.sqrt ((honK v h fc fu HM μ).mu
        * (honK v h fc fu HM μ).aScat))
    (hfLone : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖p‖ ≤ (honK v h fc fu HM μ).KL * Real.sqrt ((honK v h fc fu HM μ).mu
        * (honK v h fc fu HM μ).aScat) → fLf p = 1)
    (hCg : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Lab (HM μ).N,
      |gHat k| ≤ C * (honK v h fc fu HM μ).aScat)
    (ha1 : (honK v h fc fu HM μ).aScat ≤ 1)
    (homega : ∃ C : ℝ, 0 ≤ C ∧ |(honK v h fc fu HM μ).W1omega0
      - (honK v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ excited (Lab (HM μ).N), (honK v h fc fu HM μ).W1 k * gHat k
          / (2 * ‖honKmom v HM μ k‖ ^ 2)|
        ≤ C * (honK v h fc fu HM μ).aScat ^ 2 / (honK v h fc fu HM μ).ell)
    (hsumdiff : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, (honK v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
      ∑ k ∈ (honF v h fc fu HM μ).PHset (honK v h fc fu HM μ),
        (gHat k - (honK v h fc fu HM μ).W1 k) ^ 2 / ‖honKmom v HM μ k‖ ^ 2
        ≤ C * (honK v h fc fu HM μ).aScat * (R / (honK v h fc fu HM μ).ell) ^ 4)
    (hq2 : ∀ Ψ : (honF v h fc fu HM μ).H,
      2 * (honK v h fc fu HM μ).rho * (honK v h fc fu HM μ).W1omega0
          * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honK v h fc fu HM μ))
        ≤ (honF v h fc fu HM μ).qw Ψ ((honF v h fc fu HM μ).Q2ex (honK v h fc fu HM μ))
          + ((honK v h fc fu HM μ).b / 400)
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).gapOpT (honK v h fc fu HM μ)))
    (halpha : ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Lab (HM μ).N,
      (honF v h fc fu HM μ).PHq (honK v h fc fu HM μ).KH (honK v h fc fu HM μ).aScat p →
      (honF v h fc fu HM μ).PHq (honK v h fc fu HM μ).KH (honK v h fc fu HM μ).aScat q →
      |(honK v h fc fu HM μ).alpha p - (honK v h fc fu HM μ).alpha q|
        ≤ C * (honK v h fc fu HM μ).lille
          * ((honK v h fc fu HM μ).KH * (honK v h fc fu HM μ).aScat)
          * ‖honKmom v HM μ p - honKmom v HM μ q‖)
    (hint : ∃ C : ℝ, 0 ≤ C ∧ |(honK v h fc fu HM μ).rho * (honK v h fc fu HM μ).W1omega0
      - (honK v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (honF v h fc fu HM μ).PHset (honK v h fc fu HM μ),
          (honK v h fc fu HM μ).W1 k * (honK v h fc fu HM μ).alpha k|
        ≤ C * (honK v h fc fu HM μ).rho * (honK v h fc fu HM μ).aScat
          * (honK v h fc fu HM μ).KH⁻¹) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ Nonempty (Work.BoseB7AK.K15R.K15Input K₀
      (honF v h fc fu HM μ) (honT v h fc fu HM μ)
      (kinkEnv (honF v h fc fu HM μ) (honK v h fc fu HM μ))) := by
  have hF : honF v h fc fu HM μ
      = Work.BoseK15.boxFockDataBox (ellH v μ) (honKmom v HM μ)
          (Work.BoseBoxFock.kmomLab_neg (ellH v μ) (HM μ).N) (HM μ).m (HM μ).f (HM μ).hf := rfl
  have hccrX : ∀ s k : Lab (HM μ).N, (honT v h fc fu HM μ).ccrX s k
      = Work.BoseK15.corpusBox.hatChi ((ellH v μ) • (honKmom v HM μ k - honKmom v HM μ s)) :=
    fun s k => (HM μ).hcross s k
  exact Work.BoseB7AK.K15R.exists_K15Input_box (ellH v μ) hℓ1 (honKmom v HM μ)
    (Work.BoseBoxFock.kmomLab_neg (ellH v μ) (HM μ).N) hlat (HM μ).m (HM μ).f (HM μ).g
    (HM μ).hf (HM μ).hg (HM μ).hcross (honF v h fc fu HM μ) (honT v h fc fu HM μ) hF hccrX
    (honK v h fc fu HM μ).z (honK v h fc fu HM μ).mu
    (honK v h fc fu HM μ).aScat (honK v h fc fu HM μ).KH (honK v h fc fu HM μ).Kl
    (honK v h fc fu HM μ).KL (honK v h fc fu HM μ).d (honK v h fc fu HM μ).s
    (honK v h fc fu HM μ).eT (honK v h fc fu HM μ).b (honK v h fc fu HM μ).intM
    (honK v h fc fu HM μ).bigM (honK v h fc fu HM μ).delta fLf W1f W1omegaf
    (honK v h fc fu HM μ).W1omega0 gHat (honK v h fc fu HM μ) hE' hv haddO haddI Cw hCw
    hW1le hW1decay hW1grad hW1even hW1cd hW1om0 hfL0 hfL1 hfLe hfLsup hfLone hCg ha1
    homega hsumdiff hq2 halpha hint

end Work.BoseGateFS
