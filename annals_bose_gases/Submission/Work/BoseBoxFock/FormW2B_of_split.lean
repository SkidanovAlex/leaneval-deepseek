import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.AVgen_split_kin_pot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FormW2B_of_split` — the row table from its two halves

`Work.BoseBoxFock.AVgen` (`Submission/Work/BoseBoxFock/slotAVgen.lean`) is the sector-friendly box
twin of `H2ndF` written as a sum of twelve summands.  Grouping them as in
`Submission/Work/BoseBoxFock/rowSplitDefs.lean`,

* **kinetic group** — rows 1,2,3 (the `τ̃`-symbol kinetic row, the `b`-gap and the `n₊^H`-gap);
* **potential group** — rows 4..11 (contact, chemical, `(Ŵ₁+Ŵ₁ω)a₀†a†aa₀`, Bogoliubov,
  `χ̂`-linear, `χ̂²`-linear and cubic);

gives the two halves `FormW2Bkin` and `FormW2Bpot` of the row table `FormW2B`.  The isolation
identity `Work.BoseBoxFock.AVgen_split_kin_pot` (PROVED) says that, at *every* configuration,

    AVgen (fun T => boxSlotSum e T) id f g T_NH PHs E (8πa) x
      = AVgen (fun T => boxSlotSum e T) id f g T_NH ∅ (kinOnlyEnv E) 0 x
        + AVgen (fun T => boxSlotSum e T) id f g T_NH PHs (potOnlyEnv E) (8πa) x ;

this module turns that *pointwise* identity into the quadratic-form inequality by splitting the
Bochner integral of the left-hand side.

## The one non-formal input: integrability

`∫ x, star (boxRestrict Φ x) * AVgen … (boxRestrict Φ) x` is a Bochner integral, so the
additivity `∫ (f + g) = ∫ f + ∫ g` needs both summands **integrable** (Mathlib's
`MeasureTheory.integral_add`; for a non-integrable summand the integral is `0` by convention and
the identity can fail).  Here it is supplied structurally:

* the box restriction `boxRestrictC ℓ Φ` is `SlotGood` (measurable and everywhere bounded) and
  supported in the box `Work.MB.boxPow n ℓ` (`Work.BoseBoxFock.boxRestrictState`, PROVED);
* `AVgen` maps good states to good states — **`rowGood_AVgen`** below, obtained from the PROVED
  `Work.MB.GenLin_AVgen` + `Work.MB.GenLin_boxSlotSum_weak` (the weak, honest mode bundle
  `Measurable`/everywhere bounded/`boxL`-supported, which is exactly the bundle the row table
  carries — the strong `Continuous`/`HasCompactSupport` bundle is unsatisfiable there, see
  `FINDING_continuous_hypotheses_UNSATISFIABLE.md`);
* hence `Work.BoseBoxFock.integrable_star_mul_of_box_support` gives the integrability.

## The constant bookkeeping

The two halves are granted at possibly different pairs `(ε₁,C₁)`, `(ε₂,C₂)`.  The threshold is
`min ε₁ ε₂` (`Adm` is monotone in its threshold), and the error constant is `(C₁ + C₂)/2`: since
`errKafz v R μ C = C ·`(a positive bracket) is *linear* in `C`, we have the exact identity

    errKafz v R μ ((C₁+C₂)/2) = (errKafz v R μ C₁ + errKafz v R μ C₂)/2 ,

so the sum `(1/2)·errKafz C₁·‖Φ‖² + (1/2)·errKafz C₂·‖Φ‖²` of the two halves is *exactly*
`errKafz ((C₁+C₂)/2)·‖Φ‖²` — no sign hypothesis on the bracket is needed.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. The error constant is linear in `C` -/

/-- **`errKafz` is linear in its constant**, in the exact form in which the two halves of the row
table are added: `errKafz v R μ ((C₁+C₂)/2) = (errKafz v R μ C₁ + errKafz v R μ C₂)/2`. -/
lemma errKafz_div_two (v : ℝ³ → ℝ) (R μ C₁ C₂ : ℝ) :
    Work.BoseFixR.errKafz v R μ ((C₁ + C₂) / 2)
      = (Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂) / 2 := by
  simp only [Work.BoseFixR.errKafz]
  ring

/-! ## 2. `AVgen` preserves measurable, everywhere bounded states (the weak mode bundle) -/

/-- **`RowGood` for the sector-friendly box twin `AVgen`**, at the *weak* mode bundle
(`Measurable`, everywhere bounded, supported in `corpusBox.boxL ℓ`) that the row table carries.
This is the `good` field of `Work.MB.GenLin_AVgen` at the instance
`Work.MB.GenLin_boxSlotSum_weak`. -/
theorem rowGood_AVgen {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    RowGood (ι := Fin n)
      (AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0) :=
  (GenLin_AVgen (ι := Fin n) (fun T => Work.BoseDict.boxSlotSum e T)
    (fun T => Work.MB.GenLin_boxSlotSum_weak (d := n) hmeas hbdE hsupp T)
    (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0).good

/-! ## 3. Splitting the real part of a Bochner integral -/

/-- **The real part of the integral of a pointwise sum**: for integrable summands,
`(∫ Ψ̄ (A₁ + A₂)Ψ).re = (∫ Ψ̄ A₁Ψ).re + (∫ Ψ̄ A₂Ψ).re`. -/
lemma integral_re_add_of_integrable {n : ℕ} {Ψ : Submission.BoseGases.X n → ℂ}
    {A₁ A₂ : Submission.BoseGases.X n → ℂ}
    (h1 : MeasureTheory.Integrable (fun x => star (Ψ x) * A₁ x))
    (h2 : MeasureTheory.Integrable (fun x => star (Ψ x) * A₂ x)) :
    (∫ x, star (Ψ x) * (A₁ + A₂) x).re
      = (∫ x, star (Ψ x) * A₁ x).re + (∫ x, star (Ψ x) * A₂ x).re := by
  have hp : (fun x : Submission.BoseGases.X n => star (Ψ x) * (A₁ + A₂) x)
      = fun x => star (Ψ x) * A₁ x + star (Ψ x) * A₂ x := by
    funext x
    simp only [Pi.add_apply, mul_add]
  rw [hp, MeasureTheory.integral_add h1 h2, Complex.add_re]

/-! ## 4. The assembly -/

theorem FormW2B_of_split (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ)
    (hkin : ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FormW2Bkin v h fc fu R J Nmin ε₀ C)
    (hpot : ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FormW2Bpot v h fc fu R J Nmin ε₀ C) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FormW2B v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hK⟩ := hkin
  obtain ⟨ε₂, C₂, hε₂, hC₂, hP⟩ := hpot
  refine ⟨min ε₁ ε₂, (C₁ + C₂) / 2, lt_min hε₁ hε₂, by linarith, ?_⟩
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 T_NH hT
  -- the two threshold instances of `Adm` (`Adm` is monotone in its threshold)
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hk := hK HM hNmin μ hAdm₁ hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    T_NH hT
  have hp := hP HM hNmin μ hAdm₂ hJ n Φ hn hnorm hlow hmom e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    T_NH hT
  -- the box side is positive, and the box restriction is a good, box-supported state
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hAdm.1 hav
  obtain ⟨hΘcm, hΘcb, hΘsupp, -, -⟩ := Work.BoseBoxFock.boxRestrictState hℓ Φ
  have hGoodΨ : SlotGood (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) :=
    ⟨hΘcm, hΘcb⟩
  -- the pointwise isolation of the two groups
  have hsplit := Work.BoseBoxFock.AVgen_split_kin_pot (n := n)
    (B := fun T => Work.BoseDict.boxSlotSum e T)
    (idop := (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)))
    (f := (HM μ).f) (g := (HM μ).g) (T_NH := T_NH)
    (PHs := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (gHat0 := 8 * Real.pi * BoseGases.a v)
  -- `AVgen` preserves good states in both groups
  have hRowK : RowGood
      (AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
        (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0) :=
    rowGood_AVgen (n := n) h1 h2 h3 (HM μ).f (HM μ).g T_NH
      (∅ : Finset (Lab (HM μ).N))
      (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
  have hRowP : RowGood
      (AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        (HM μ).f (HM μ).g T_NH
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
        (8 * Real.pi * BoseGases.a v)) :=
    rowGood_AVgen (n := n) h1 h2 h3 (HM μ).f (HM μ).g T_NH
      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (8 * Real.pi * BoseGases.a v)
  -- integrability of the two integrands (the box restriction is box supported)
  have hi1 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
        * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
            (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x) :=
    Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hRowK (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).1
      (hRowK (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).2
  have hi2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
        * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            (HM μ).f (HM μ).g T_NH
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
            (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
            (8 * Real.pi * BoseGases.a v)
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x) :=
    Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hRowP (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).1
      (hRowP (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) hGoodΨ).2
  -- the pointwise split of the left-hand integrand
  have hpt : (fun x : Submission.BoseGases.X n =>
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x)
      = fun x =>
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x
          + star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x := by
    funext x
    rw [hsplit]
    simp only [Pi.add_apply, mul_add]
  -- the split of the left-hand side
  have hkey : (∫ x : Submission.BoseGases.X n,
        star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
          * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
              (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
              (HM μ).f (HM μ).g T_NH
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
      = (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH (∅ : Finset (Lab (HM μ).N))
                (kinOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E) 0
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
        + (∫ x : Submission.BoseGases.X n,
          star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
            * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                (HM μ).f (HM μ).g T_NH
                ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                  (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (potOnlyEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                (8 * Real.pi * BoseGases.a v)
                (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re := by
    rw [hpt]
    rw [MeasureTheory.integral_add hi1 hi2, Complex.add_re]
  -- the arithmetic of the two error rows
  have harith : (Work.BoseBoxFock.W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₁ * Work.BoseBoxFix.normB v μ n Φ
        + (Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * Work.BoseFixR.errKafz v R μ C₂ * Work.BoseBoxFix.normB v μ n Φ))
      = Work.BoseBoxFock.W2B v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseFixR.errKafz v R μ ((C₁ + C₂) / 2) * Work.BoseBoxFix.normB v μ n Φ := by
    rw [Work.BoseBoxFock.W2B, errKafz_div_two]
    ring
  exact le_trans hkey.le (le_trans (add_le_add hk hp) harith.le)

end Work.BoseBoxFock
