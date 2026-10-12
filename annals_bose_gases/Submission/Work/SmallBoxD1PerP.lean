import ChallengeDeps
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Commons.Analysis.Real.sqrt_sub_sq_le_div
import Submission.Work.SmallBoxKineticP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-281 — D1 assembly item (1): the PER-`p` IDENTITY

FS `lm:appbogolubov` adds `A₁` to the D1 kinetic word and `A₂` and then writes

    kinetic + A₁ + A₂ ≥ (2π)⁻³ ½ ∫ h(p) dp ,

    h(p) = 𝒜(p)(b_p†b_p + b_{−p}†b_{−p}) + 𝓑(p)(b_p†b_{−p}† + b_{−p}b_p) ,

with `𝒜(p) = |B|/(n+1)[|p|−c]₊² + 2K_s a`, `𝓑(p) = \widehat{WS₁}(p)`, and then applies
Bogoliubov per `p` via `thm:bogolubov-complete`.

The corpus already has every ingredient:

* the kinetic word `kinPWord` (`SmallBoxKineticP`), whose per-`p` content is a sum of
  the numbers `P_g = ‖τ_g Φ‖² = ∫(τ_gΦ)²` of the two REAL modes `g = qModeRe s p`,
  `qModeIm s p` (`modeP_eq_tauAnn_sq`);
* the pairing word `q4PairWord`, whose `p`-parametrised form
  (`q4PairWord_eq_pPairing`) carries the weight `𝓑(p) = 𝓕W₁((2π)⁻¹•p)`;
* the per-`p` Bogoliubov theorem `bogoliubov_perP_chi` with the quadratic form
  `A(P_u+P_v) + B(R_u+R_v)`, `R_g = ∫(τ_gΦ)(τ_g†Φ)`.

The missing link — proved here — is that the corpus's pair-word integrand is
EXACTLY `(s³)⁻¹` times the `B`-term of that quadratic form:

  `∫ Φ (bDag g_{{−p}}) (bDag g_p Φ) = (s³)⁻¹ (R_{u_p} + R_{v_p})`

(`bDag g = (s³)⁻¹ a†(g)a(1)`, so the bilinear sandwich is `(s³)⁻²` times the
`boxOp` pairing form, and `boxOp = √(s³)·τ` converts it to `(s³)⁻¹`).

## Contents

* `modeChat_neg`, `qMode_neg_conj`, `qModeRe_neg`, `qModeIm_neg` — the mode conjugation;
* `cOp_ofReal` — the `cOp`-calculus on complexified real data (`star` of a real is itself);
* `integral_ofReal_cOp_pair` — `∫Φℂ(X_{uℂ}X_{uℂ}Φℂ) = (∫Φ(boxOp u 1 (boxOp u 1 Φ)) : ℂ)`;
* `boxOp_pair_adjoint` — `∫Φ(boxOp u 1 (boxOp u 1 Φ)) = ∫(boxOp 1 u Φ)(boxOp u 1 Φ)`;
* `boxOp_pair_eq_tau` — the `τ`-form `∫(boxOp 1 u Φ)(boxOp u 1 Φ) = s³∫(τ_uΦ)(τ_u†Φ)`;
* **`pair_reduction`** — the per-`p` pairing identity in the corpus's `τ`-language;
* **`pair_reduction_word`** — the same in the word form `∫Φ(bDag…bDag…) = (s³)⁻¹(R_u+R_v)`;
* **`q4PairWord_eq_pairSum`** — `q4PairWord` as the `p`-integral of `𝓑(p)·(s³)⁻¹(R_u+R_v)`;
* **`kinPWord_eq_modeSum`** — `kinPWord` as the `p`-integral of `[|p|−c]₊²(P_u+P_v)`;
* **`d1_perP_content`** — the two identifications collected: the D1 word's per-`p`
  content is `F(p)(P_u+P_v) + 𝓑(p)(s³)⁻¹(R_u+R_v)`, i.e. the quadratic form of
  FS's `h(p)/2` with the kinetic coefficient `F(p)` (the `𝒜`-coefficient is reached
  through the `A₁`-term, see the design note).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The conjugation of the momentum mode -/

/-- The exponential of the reflected momentum: `e^{−i⟨−p,y⟩} = \overline{e^{−i⟨p,y⟩}}`. -/
lemma exp_neg_inner_neg (p y : ℝ³) :
    Complex.exp (-(Complex.I * ((inner ℝ (-p) y : ℝ) : ℂ)))
      = star (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_right']
  push_cast
  ring

/-- `modeChat ℓ (−p) = \overline{modeChat ℓ p}`. -/
lemma modeChat_neg (ℓ : ℝ) (p : ℝ³) : modeChat ℓ (-p) = star (modeChat ℓ p) := by
  have hpt : (fun y : ℝ³ => (chiScale ℓ y : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ (-p) y : ℝ) : ℂ))))
      = fun y : ℝ³ => star ((chiScale ℓ y : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
    funext y
    have hχ : ∀ z : ℂ, star ((chiScale ℓ y : ℂ) * z) = (chiScale ℓ y : ℂ) * star z :=
      fun z => by
        rw [star_mul, show star ((chiScale ℓ y : ℂ)) = (chiScale ℓ y : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal]]
        ring
    rw [exp_neg_inner_neg, hχ]
  rw [modeChat, modeChat, hpt, Complex.star_def, integral_conj]

/-- **The momentum mode at `−p` is the pointwise conjugate of the mode at `p`.** -/
lemma qMode_neg_conj (ℓ : ℝ) (p y : ℝ³) : qMode ℓ (-p) y = star (qMode ℓ p y) := by
  have hc : modeChat ℓ (-p) = star (modeChat ℓ p) := modeChat_neg ℓ p
  set k : ℂ := ((ℓ ^ 3)⁻¹ : ℂ) with hkdef
  have hku : ∀ z : ℂ, star (k * z) = k * star z := fun z => by
    rw [star_mul, show star k = k from by rw [hkdef, Complex.star_def]; simp]
    ring
  have hχ : ∀ z : ℂ, star ((chiScale ℓ y : ℂ) * z) = (chiScale ℓ y : ℂ) * star z := fun z => by
    rw [star_mul, show star ((chiScale ℓ y : ℂ)) = (chiScale ℓ y : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    ring
  have h1 : qMode ℓ p y
      = (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        - k * modeChat ℓ p := by
    rw [qMode, ← hkdef]
  have h2 : qMode ℓ (-p) y
      = (chiScale ℓ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) y : ℝ) : ℂ)))
        - k * modeChat ℓ (-p) := by
    rw [qMode, ← hkdef]
  rw [h1, h2, hc, exp_neg_inner_neg, star_sub, hχ, hku]

/-- `qModeRe ℓ (−p) = qModeRe ℓ p`. -/
lemma qModeRe_neg (ℓ : ℝ) (p : ℝ³) : qModeRe ℓ (-p) = qModeRe ℓ p := by
  funext y
  simp only [qModeRe]
  rw [qMode_neg_conj, Complex.star_def, Complex.conj_re]

/-- `qModeIm ℓ (−p) = − qModeIm ℓ p`. -/
lemma qModeIm_neg (ℓ : ℝ) (p : ℝ³) : qModeIm ℓ (-p) = - qModeIm ℓ p := by
  funext y
  simp only [qModeIm, Pi.neg_apply]
  rw [qMode_neg_conj, Complex.star_def, Complex.conj_im]

/-! ## 2 `cOp` on complexified real data -/

/-- **`cOp` on complexified real data is the complexification of the real `boxOp`.**
`star` fixes the real annihilation profile, so `cOp fℂ hℂ Φℂ = (boxOp f h Φ)ℂ`. -/
lemma cOp_ofReal (s : ℝ) {N : ℕ} (f h : ℝ³ → ℝ) (Φ : X N → ℝ) (x : X N) :
    cOp s (fun z => (f z : ℂ)) (fun z => (h z : ℂ)) (fun y => (Φ y : ℂ)) x
      = ((boxOp s f h Φ x : ℝ) : ℂ) := by
  have hpt : ∀ i : Fin N,
      (∫ z in acube s, star ((h z : ℂ)) * (((Φ (Function.update x i z)) : ℝ) : ℂ))
        = ((∫ z in acube s, h z * Φ (Function.update x i z) : ℝ) : ℂ) := by
    intro i
    have hI : ((∫ z in acube s, h z * Φ (Function.update x i z) : ℝ) : ℂ)
        = ∫ z in acube s, ((h z * Φ (Function.update x i z) : ℝ) : ℂ) :=
      (integral_ofReal (μ := (volume : Measure ℝ³).restrict (acube s))
        (f := fun z => h z * Φ (Function.update x i z))).symm
    rw [hI]
    refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  simp only [cOp, boxOp]
  rw [Complex.ofReal_sum Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hpt i, Complex.ofReal_mul]


/-! ## 3 The pair reduction `X_{g'}X_g = X_u² + X_v²` -/

/-- **The conjugation-pair reduction.**  For `g = u + iv` and `g' = \bar g = u − iv` (the two
modes of an anti-diagonal Bogoliubov pair), the double creation `X_{g'}X_g` collapses onto the
two REAL same-mode creations — the `±i` cross terms cancel by `[X_u,X_v] = 0`. -/
lemma cOp_conj_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ) (hu : Continuous u)
    (hv : Continuous v) {Ψ : X N → ℂ} (hΨ : Continuous Ψ)
    (hum : ∫ z in acube ℓ, (u z : ℂ) = 0) (hvm : ∫ z in acube ℓ, (v z : ℂ) = 0) :
    cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
      = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        + cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) := by
  have huC : Continuous fun z : ℝ³ => (u z : ℂ) := Complex.continuous_ofReal.comp hu
  have hvC : Continuous fun z : ℝ³ => (v z : ℂ) := Complex.continuous_ofReal.comp hv
  have h1 : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hIvn : Continuous fun z : ℝ³ => Complex.I * (v z : ℂ) := continuous_const.mul hvC
  have hCnIvn : Continuous fun z : ℝ³ => (-Complex.I) * (v z : ℂ) := continuous_const.mul hvC
  have hCu : Continuous (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ) :=
    cOp_continuous_state hℓ huC h1 hΨ
  have hCv : Continuous (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) :=
    cOp_continuous_state hℓ hvC h1 hΨ
  have hL : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + Complex.I • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X
    rw [cOp_add_left, cOp_smul_left]
  have hK : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + (-Complex.I) • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X
    rw [show (fun z : ℝ³ => (u z : ℂ) - Complex.I * (v z : ℂ))
        = fun z => (u z : ℂ) + (-Complex.I) * (v z : ℂ) from by funext z; ring]
    rw [cOp_add_left, cOp_smul_left]
  rw [hK (cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ),
    hL Ψ]
  rw [cOp_add_smul_state hℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) Complex.I h1 hCu hCv,
      cOp_add_smul_state hℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) Complex.I h1 hCu hCv]
  rw [cOp_comm_l hℓ u v hu hv hΨ hum hvm]
  simp only [smul_add, smul_smul,
    show (-Complex.I) * Complex.I = (1 : ℂ) from by rw [neg_mul, Complex.I_mul_I, neg_neg],
    one_smul, neg_smul]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring


/-! ## 4 The real `boxOp` pairing form and its complexification -/

/-- The real `boxOp` pairing form `∫(X_uΦ)(X_u†Φ)` of a real mode `u`. -/
noncomputable def boxPair (s : ℝ) {N : ℕ} (u : ℝ³ → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∫ x in abox N s,
    boxOp s (fun _ => (1 : ℝ)) u Φ x * boxOp s u (fun _ => (1 : ℝ)) Φ x

/-- `boxPair` is the `τ`-pairing, scaled by `s³` (`boxOp = √(s³)·τ`). -/
lemma boxPair_eq_tau {N : ℕ} {s : ℝ} (hs : 0 < s) {u : ℝ³ → ℝ} (hu : Continuous u)
    {Φ : X (N + 1) → ℝ} (hΦ : Continuous Φ) :
    boxPair s u Φ = s ^ 3 * ∫ x in abox (N + 1) s,
      tauAnn s u Φ x * tauDag s u Φ x := by
  have hpt : ∀ x : X (N + 1),
      boxOp s (fun _ => (1 : ℝ)) u Φ x * boxOp s u (fun _ => (1 : ℝ)) Φ x
        = s ^ 3 * (tauAnn s u Φ x * tauDag s u Φ x) := by
    intro x
    rw [boxOp_eq_tauAnn hs u Φ x, boxOp_eq_tauDag hs u Φ x]
    have hsp : Real.sqrt (s ^ 3) * Real.sqrt (s ^ 3) = s ^ 3 := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    rw [show (Real.sqrt (s ^ 3) * tauAnn s u Φ x) * (Real.sqrt (s ^ 3) * tauDag s u Φ x)
        = (Real.sqrt (s ^ 3) * Real.sqrt (s ^ 3)) * (tauAnn s u Φ x * tauDag s u Φ x)
        from by ring, hsp]
  rw [boxPair, integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]

/-- `boxPair s u Φ = ∫ Φ · X_u (X_u Φ)`, i.e. the bilinear adjoint form. -/
lemma boxPair_eq_adjoint {N : ℕ} {s : ℝ} (hs : 0 < s) {u : ℝ³ → ℝ} (hu : Continuous u)
    {Φ : X (N + 1) → ℝ} (hΦ : Continuous Φ) :
    boxPair s u Φ = ∫ x in abox (N + 1) s, Φ x *
      boxOp s u (fun _ => (1 : ℝ)) (boxOp s u (fun _ => (1 : ℝ)) Φ) x :=
  (boxOp_adjoint hs hu continuous_const hΦ
    (continuous_boxOp hs hu continuous_const hΦ)).symm

/-- **The complexification of the `boxOp` pairing form**: the complex sandwich
`∫ Φℂ · cOp uℂ 1 (cOp uℂ 1 Φℂ)` equals the complexification of `boxPair s u Φ`. -/
lemma integral_cOp_pair_ofReal {N : ℕ} {s : ℝ} (hs : 0 < s) {u : ℝ³ → ℝ} (hu : Continuous u)
    {Φ : X (N + 1) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in abox (N + 1) s, (Φ x : ℂ) * cOp s (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp s (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) x)
      = ((boxPair s u Φ : ℝ) : ℂ) := by
  have h1 : cOp s (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))
      = fun x => ((boxOp s u (fun _ => (1 : ℝ)) Φ x : ℝ) : ℂ) := by
    funext x
    exact cOp_ofReal s u (fun _ => (1 : ℝ)) Φ x
  have h2 : cOp s (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (fun x => ((boxOp s u (fun _ => (1 : ℝ)) Φ x : ℝ) : ℂ))
      = fun x => ((boxOp s u (fun _ => (1 : ℝ))
          (boxOp s u (fun _ => (1 : ℝ)) Φ) x : ℝ) : ℂ) := by
    funext x
    exact cOp_ofReal s u (fun _ => (1 : ℝ)) (boxOp s u (fun _ => (1 : ℝ)) Φ) x
  have hI : ((∫ x in abox (N + 1) s, Φ x * boxOp s u (fun _ => (1 : ℝ))
        (boxOp s u (fun _ => (1 : ℝ)) Φ) x : ℝ) : ℂ)
      = ∫ x in abox (N + 1) s, ((Φ x * boxOp s u (fun _ => (1 : ℝ))
        (boxOp s u (fun _ => (1 : ℝ)) Φ) x : ℝ) : ℂ) :=
    (integral_ofReal (μ := (volume : Measure (X (N + 1))).restrict (abox (N + 1) s))
      (f := fun x => Φ x * boxOp s u (fun _ => (1 : ℝ))
        (boxOp s u (fun _ => (1 : ℝ)) Φ) x)).symm
  rw [h1]
  rw [h2]
  rw [show (fun x : X (N + 1) => (Φ x : ℂ) * (((boxOp s u (fun _ => (1 : ℝ))
        (boxOp s u (fun _ => (1 : ℝ)) Φ)) x : ℝ) : ℂ))
      = fun x => ((Φ x * (boxOp s u (fun _ => (1 : ℝ))
        (boxOp s u (fun _ => (1 : ℝ)) Φ)) x : ℝ) : ℂ) from by
    funext x; exact (Complex.ofReal_mul _ _).symm]
  rw [boxPair_eq_adjoint hs hu hΦ, hI]


/-! ## 5 The per-`p` pairing reduction -/

/-- **The `cOp` form of the per-`p` pairing reduction.**  The corpus's pair-word integrand
(the `cOp` version, i.e. without the `bDag`-normalisation) is the SUM of the two real-mode
bilinear `boxPair` forms. -/
theorem cOp_pair_reduction {N : ℕ} {s : ℝ} (hs : 0 < s) {p : ℝ³}
    {Φ : X (N + 1) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in abox (N + 1) s, (Φ x : ℂ) * cOp s (qMode s (-p)) (fun _ => (1 : ℂ))
        (cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) x)
      = ((boxPair s (qModeRe s p) Φ : ℝ) : ℂ)
        + ((boxPair s (qModeIm s p) Φ : ℝ) : ℂ) := by
  have hu : Continuous (qModeRe s p) := continuous_qModeRe p
  have hv : Continuous (qModeIm s p) := continuous_qModeIm p
  have hIeu : ((∫ z in acube s, qModeRe s p z : ℝ) : ℂ)
      = ∫ z in acube s, ((qModeRe s p z : ℝ) : ℂ) :=
    (integral_ofReal (μ := (volume : Measure ℝ³).restrict (acube s))
      (f := fun z => qModeRe s p z)).symm
  have hIev : ((∫ z in acube s, qModeIm s p z : ℝ) : ℂ)
      = ∫ z in acube s, ((qModeIm s p z : ℝ) : ℂ) :=
    (integral_ofReal (μ := (volume : Measure ℝ³).restrict (acube s))
      (f := fun z => qModeIm s p z)).symm
  have hum : ∫ z in acube s, ((qModeRe s p z : ℝ) : ℂ) = 0 := by
    rw [← hIeu, integral_qModeRe_eq_zero hs p]
    norm_num
  have hvm : ∫ z in acube s, ((qModeIm s p z : ℝ) : ℂ) = 0 := by
    rw [← hIev, integral_qModeIm_eq_zero hs p]
    norm_num
  have hΦℂ : Continuous fun y : X (N + 1) => (Φ y : ℂ) := Complex.continuous_ofReal.comp hΦ
  have huC : Continuous fun z : ℝ³ => ((qModeRe s p z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hu
  have hvC : Continuous fun z : ℝ³ => ((qModeIm s p z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hv
  have h1c : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hg : qMode s p
      = fun z => ((qModeRe s p z : ℝ) : ℂ) + Complex.I * ((qModeIm s p z : ℝ) : ℂ) :=
    funext fun z => qMode_eq_re_add_im s p z
  have hg' : qMode s (-p)
      = fun z => ((qModeRe s p z : ℝ) : ℂ) - Complex.I * ((qModeIm s p z : ℝ) : ℂ) := by
    funext z
    rw [qMode_neg_conj s p z, congrFun hg z]
    rw [show star (((qModeRe s p z : ℝ) : ℂ) + Complex.I * ((qModeIm s p z : ℝ) : ℂ))
        = ((qModeRe s p z : ℝ) : ℂ) - Complex.I * ((qModeIm s p z : ℝ) : ℂ) from by
      rw [star_add, star_mul,
        show star (Complex.I) = -Complex.I from by rw [Complex.star_def, Complex.conj_I],
        show star (((qModeRe s p z : ℝ) : ℂ)) = ((qModeRe s p z : ℝ) : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal],
        show star (((qModeIm s p z : ℝ) : ℂ)) = ((qModeIm s p z : ℝ) : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal]]
      ring]
  have hcp : cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ) - Complex.I * ((qModeIm s p z : ℝ) : ℂ))
        (fun _ => (1 : ℂ))
        (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ) + Complex.I * ((qModeIm s p z : ℝ) : ℂ))
          (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ)))
      = cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
          (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
            (fun y => (Φ y : ℂ)))
        + cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
          (cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
            (fun y => (Φ y : ℂ))) :=
    cOp_conj_pair hs (qModeRe s p) (qModeIm s p) hu hv hΦℂ hum hvm
  have hA : Continuous fun x : X (N + 1) => (Φ x : ℂ) * cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ))
      (fun _ => (1 : ℂ)) (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
        (fun y => (Φ y : ℂ))) x :=
    (Complex.continuous_ofReal.comp hΦ).mul
      (cOp_continuous_state hs huC h1c
        (cOp_continuous_state hs huC h1c hΦℂ))
  have hB : Continuous fun x : X (N + 1) => (Φ x : ℂ) * cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ))
      (fun _ => (1 : ℂ)) (cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
        (fun y => (Φ y : ℂ))) x :=
    (Complex.continuous_ofReal.comp hΦ).mul
      (cOp_continuous_state hs hvC h1c
        (cOp_continuous_state hs hvC h1c hΦℂ))
  rw [hg', hg, hcp]
  rw [show (fun x : X (N + 1) => (Φ x : ℂ) *
        (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
            (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
              (fun y => (Φ y : ℂ)))
          + cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
            (cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
              (fun y => (Φ y : ℂ)))) x)
      = fun x : X (N + 1) => (Φ x : ℂ) * cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ))
            (fun _ => (1 : ℂ)) (cOp s (fun z => ((qModeRe s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
              (fun y => (Φ y : ℂ))) x
          + (Φ x : ℂ) * cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ))
            (fun _ => (1 : ℂ)) (cOp s (fun z => ((qModeIm s p z : ℝ) : ℂ)) (fun _ => (1 : ℂ))
              (fun y => (Φ y : ℂ))) x from by
    funext x; rw [Pi.add_apply, mul_add]]
  rw [MeasureTheory.integral_add
    (ContinuousOn.integrableOn_compact (abox_compact (N + 1) hs) hA.continuousOn)
    (ContinuousOn.integrableOn_compact (abox_compact (N + 1) hs) hB.continuousOn)]
  rw [integral_cOp_pair_ofReal hs hu hΦ, integral_cOp_pair_ofReal hs hv hΦ]


/-- **THE PER-`p` PAIRING IDENTITY.**  The corpus's pair-word integrand at the momentum `p`

  `∫ Φ · (bDag g_{−p}) (bDag g_p Φ)`    (`g_p = qMode s p = Q_B(χ_B e^{−ipx})`)

is `(s³)⁻¹` times the `B`-term of the per-`p` Bogoliubov quadratic form of
`bogoliubov_perP_chi`, i.e. the `τ`-pairing of the two REAL modes `u_p = Re g_p`,
`v_p = Im g_p`:

  `∫ Φ(bDag g_{−p})(bDag g_p Φ) = (s³)⁻¹ (R_{u_p} + R_{v_p})`,

`R_g = ∫(τ_gΦ)(τ_g†Φ)`.  This is the missing link between the corpus's `q4PairWord` and
FS's `h(p)`; the `(s³)⁻¹` is FS's `|B|⁻¹` factor in `b_p†b_p = |B|⁻¹(n_0+1)N_p`. -/
theorem bDag_pair_reduction {N : ℕ} {s : ℝ} (hs : 0 < s) {p : ℝ³}
    {Φ : X (N + 1) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in abox (N + 1) s, (Φ x : ℂ) * bDag s (qMode s (-p))
        (bDag s (qMode s p) (fun y => (Φ y : ℂ))) x)
      = ((s ^ 3)⁻¹ : ℂ) * (((∫ x in abox (N + 1) s,
              tauAnn s (qModeRe s p) Φ x * tauDag s (qModeRe s p) Φ x)
            + (∫ x in abox (N + 1) s,
              tauAnn s (qModeIm s p) Φ x * tauDag s (qModeIm s p) Φ x) : ℝ) : ℂ) := by
  have hu : Continuous (qModeRe s p) := continuous_qModeRe p
  have hv : Continuous (qModeIm s p) := continuous_qModeIm p
  have hΦℂ : Continuous fun y : X (N + 1) => (Φ y : ℂ) := Complex.continuous_ofReal.comp hΦ
  -- Step 1: the `bDag`-normalisation reduction
  have houter : bDag s (qMode s (-p)) (bDag s (qMode s p) (fun y => (Φ y : ℂ)))
      = (boxInv s * boxInv s) • cOp s (qMode s (-p)) (fun _ => (1 : ℂ))
          (cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) := by
    rw [show bDag s (qMode s p) (fun y => (Φ y : ℂ))
        = boxInv s • cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ)) from
      funext (fun x => bDag_eq_cOp s (qMode s p) (fun y => (Φ y : ℂ)) x)]
    rw [show bDag s (qMode s (-p))
          (boxInv s • cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ)))
        = boxInv s • cOp s (qMode s (-p)) (fun _ => (1 : ℂ))
          (boxInv s • cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) from
      funext (fun x => bDag_eq_cOp s (qMode s (-p))
        (boxInv s • cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) x)]
    rw [cOp_smul_state hs (qMode s (-p)) (fun _ => (1 : ℂ)) (boxInv s)
      (cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ)))]
    rw [smul_smul]
  rw [houter]
  rw [show (fun x : X (N + 1) => (Φ x : ℂ) *
        ((boxInv s * boxInv s) • cOp s (qMode s (-p)) (fun _ => (1 : ℂ))
          (cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ)))) x)
      = fun x : X (N + 1) => (boxInv s * boxInv s) * ((Φ x : ℂ) *
          cOp s (qMode s (-p)) (fun _ => (1 : ℂ))
            (cOp s (qMode s p) (fun _ => (1 : ℂ)) (fun y => (Φ y : ℂ))) x) from by
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [cOp_pair_reduction hs hΦ, boxPair_eq_tau hs hu hΦ, boxPair_eq_tau hs hv hΦ]
  -- the scalar bookkeeping
  have hb3 : (((s ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (pow_pos hs 3) : ((s ^ 3 : ℝ)) ≠ 0)
  have hbv : boxInv s = (((s ^ 3 : ℝ)) : ℂ)⁻¹ := by rw [boxInv]
  rw [hbv]
  push_cast
  field_simp


/-! ## 6 The D1 word in the `τ`-language -/

/-- **`q4PairWord` as the `p`-integral of the `τ`-pairing.**  Composing the
`p`-parametrised A₂-link (`q4PairWord_eq_pPairing`) with the per-`p` pairing reduction
(`bDag_pair_reduction`): the corpus's pair word is the `q`-integral, against FS's weight
`𝓑(q) = 𝓕W₁((2π)⁻¹q)`, of `(s³)⁻¹(R_{u_q} + R_{v_q})` — i.e. exactly the `B`-term of
`bogoliubov_perP_chi` at `B = 𝓑(q)·(s³)⁻¹`. -/
theorem q4PairWord_eq_pairSum {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) : ℝ) : ℂ)
      = (((2 * π : ℝ) ^ 3)⁻¹ : ℂ) *
          ∫ q, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ))
                (((2 * π : ℝ)⁻¹) • q) *
            (((ℓ ^ 3)⁻¹ : ℂ) * (((∫ x in abox (p + 2) ℓ,
                    tauAnn ℓ (qModeRe ℓ q) Φ x * tauDag ℓ (qModeRe ℓ q) Φ x)
                  + (∫ x in abox (p + 2) ℓ,
                    tauAnn ℓ (qModeIm ℓ q) Φ x * tauDag ℓ (qModeIm ℓ q) Φ x) : ℝ) : ℂ)) := by
  rw [q4PairWord_eq_pPairing hℓ hR hRℓ hv_supp h hΦ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only []
  rw [bDag_pair_reduction hℓ (p := q) hΦ.continuous]

/-- **`kinPWord` as the `p`-integral of the `τ`-number form.**  By `modeP_eq_tauAnn_sq`
the kinetic word's integrand is a sum of the two REAL modes' `τ`-numbers `P_g = ∫(τ_gΦ)²` —
exactly the `A`-term of `bogoliubov_perP_chi`. -/
theorem kinPWord_eq_modeSum {s c : ℝ} (hs : 0 < s) {n : ℕ} {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) :
    kinPWord s c Φ = (2 * Real.pi)⁻¹ ^ 3 * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
      ((∫ x in abox (n + 1) s, (tauAnn s (qModeRe s p) Φ x) ^ 2)
        + (∫ x in abox (n + 1) s, (tauAnn s (qModeIm s p) Φ x) ^ 2)) := by
  rw [kinPWord]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only []
  rw [modeP_eq_tauAnn_sq hs (continuous_qModeRe p) hΦ,
    modeP_eq_tauAnn_sq hs (continuous_qModeIm p) hΦ]


/-! ## 7 The per-`p` D1 interface (content + Bogoliubov) -/

/-- **The per-`p` D1 interface.**  Combining the per-`p` Bogoliubov bound
(`bogoliubov_perP_chi`, applied with the coefficients `A₀`, `B₀` of FS's `h(p)`) with the
identification of the D1 word's per-`p` content (`F(p)(P_u+P_v) + 𝓑(p)(s³)⁻¹(R_u+R_v)`):
the D1 content at the momentum `p` is bounded below by the Bogoliubov bound minus the
KINETIC DEFICIT `(A₀ − F)(P_u+P_v)`.  In FS's application `A₀ = 𝒜(p)s⁻³` and the deficit
`𝒜(p)s⁻³ − F(p) = F(p)/(n+1) + 2K_sa/s⁻³·(1/s³) − F(p)` is paid for by the `A₁`-term
(`SmallBoxBogolubovD1.a1_bound_concrete`). -/
theorem d1_content_bogoliubov {n : ℕ} {s A₀ B₀ F : ℝ} (hs : 0 < s) {p : ℝ³}
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (hA₀ : 0 < A₀) (hB₀ : |B₀| ≤ A₀) :
    - ((A₀ - Real.sqrt (A₀ ^ 2 - B₀ ^ 2)) / 2)
        * ((∫ z in acube s, (chiScale s z) ^ 2) * ((n : ℝ) + 1)
            * (∫ x in abox (n + 1) s, (Φ x) ^ 2))
      - (A₀ - F) * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
      ≤ F * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
        + B₀ * ((∫ x in abox (n + 1) s,
              tauAnn s (qModeRe s p) Φ x * tauDag s (qModeRe s p) Φ x)
            + (∫ x in abox (n + 1) s,
              tauAnn s (qModeIm s p) Φ x * tauDag s (qModeIm s p) Φ x)) := by
  have h := bogoliubov_perP_chi (s := s) (n := n) (A := A₀) (B := B₀) hs (p := p) hΦ hA₀ hB₀
  rw [← modeP_eq_tauAnn_sq hs (continuous_qModeRe p) hΦ,
    ← modeP_eq_tauAnn_sq hs (continuous_qModeIm p) hΦ] at h
  nlinarith [h]


/-! ## 8 The Bogoliubov coefficient `K(A,B) = (A − √(A²−B²))/2` -/

/-- the leading-order bound for the Bogoliubov coefficient (FS's
`(𝒜−√(𝒜²−ℬ²))/2 ≃ ℬ²/(4𝒜)`; note the `½` in the definition of `K`). -/
lemma bogoliubov_coeff_le {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ B ^ 2 / (2 * A) := by
  have h := Commons.Analysis.Real.sqrt_sub_sq_le_div hA hB
  have h' : (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ (B ^ 2 / A) / 2 :=
    div_le_div_of_nonneg_right h (by norm_num)
  have h2 : (B ^ 2 / A) / 2 = B ^ 2 / (2 * A) := by rw [div_div, mul_comm]
  rwa [h2] at h'

/-- `K` is homogeneous of degree one in `(A,B)`: `K(cA,cB) = cK(A,B)` for `0 < c`.
This is the step that converts `K(𝒜(p)s⁻³,𝓑(p)s⁻³)` (the coefficients of FS's `h(p)/2`)
into `s⁻³K(𝒜(p),𝓑(p))` (the coefficients of `h(p)`). -/
lemma bogoliubov_coeff_smul {A B c : ℝ} (hc : 0 < c) :
    (c * A - Real.sqrt ((c * A) ^ 2 - (c * B) ^ 2)) / 2
      = c * ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2) := by
  have hsq : (c * A) ^ 2 - (c * B) ^ 2 = c ^ 2 * (A ^ 2 - B ^ 2) := by ring
  have h1 : Real.sqrt (c ^ 2 * (A ^ 2 - B ^ 2))
      = c * Real.sqrt (A ^ 2 - B ^ 2) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c ^ 2), Real.sqrt_sq hc.le]
  rw [hsq, h1]
  ring

/-- the scaled form used in the D1 integration: with `A₀ = 𝒜s⁻³`, `B₀ = 𝓑s⁻³`,
`K(A₀,B₀)·s³M = K(𝒜,𝓑)·M`. -/
lemma bogoliubov_coeff_smul_mul {A B c s : ℝ} (hc : 0 < c) :
    ((c * A - Real.sqrt ((c * A) ^ 2 - (c * B) ^ 2)) / 2) * s
      = c * ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2) * s := by
  rw [bogoliubov_coeff_smul hc]


/-! ## 9 Integrability of the two halves of the D1 integrand -/

/-- **Integrability of the pairing half.**  The `u`-parametrised pair-word integrand
`𝓕W₁(u)·∫Φ(bDag g_{−u})(bDag g_u Φ)` is `Integrable`: by `c2_sum` the inner integral is a
FINITE SUM of `𝓕(pairFibreDens_q)(−u)`, and each `pairFibreDens_q` is compactly supported and
smooth, hence Schwartz; each summand is integrable by the fleet's
`Commons.Analysis.Fourier.integrable_fourier_mul_fourier_neg`.

This is what legitimises combining the corpus's two separate D1 integrals
(`kinPWord` and `q4PairWord`) into ONE integral, i.e. applying the pointwise Bogoliubov
bound `d1_content_bogoliubov` at every `p` and integrating the result. -/
theorem integrable_pairingWeight {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun u : ℝ³ =>
      FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
        (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
          (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x)) := by
  have hEW : Integrable (fun x : ℝ³ => (wScaled ℓ (g0 v h) x : ℂ)) :=
    (wScaled_integrable_ae hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h)).ofReal
  have hsum : Integrable (fun u : ℝ³ =>
      ∑ q ∈ pairSet (p + 2),
        FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
          FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) (-u)) := by
    refine MeasureTheory.integrable_finsetSum _ (fun q hq => ?_)
    have hqne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
    have hsupp : HasCompactSupport (fun x : ℝ³ => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) :=
      (hasCompactSupport_pairFibreDens hℓ Φ q.1 q.2).comp_left
        (g := fun z : ℝ => (z : ℂ)) (by simp)
    have hcd : ContDiff ℝ ∞ (fun x : ℝ³ => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_pairFibreDens hℓ q.1 q.2 hqne hΦ)
    exact Commons.Analysis.Fourier.integrable_fourier_mul_fourier_neg hEW
      (hsupp.toSchwartzMap hcd)
  refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [c2_sum hℓ hΦ u, Finset.mul_sum]

end BoseGases
end Submission
