import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.BoseBand.neuWord_fibre_offdiag
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.mainWord_offdiag_mem
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.momWord_offdiag
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.KinOffdiag.slotTerm_zero_of_mem`

**The polarised slot-`a` kinetic integrand of two *different* joint sector projections
vanishes** as soon as the slot `a` belongs to both sectors.

In the notation of the corpus (`Work.BoseFixB2.jointProj ℓ S Φ = E_SΦ`,
`E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j`), for `a ∈ S ∩ T` and `S ≠ T`,

    `∫_{abox n ℓ} 1_{Λ(0)}(x_a)·[fsT(fibre_a(E_SΦ + E_TΦ)(x)) − fsT(fibre_a(E_SΦ − E_TΦ)(x))]/4 = 0`.

## Proof

`fsT` is the sum of the four kinetic words of FS `eq:DefT`
(`Work.BoseKinLoc.fsT_eq_sum`), each of which is *quadratic* in the one-body state, so the
pointwise polarisation splits:

    `fsT(fibre(·)) difference = Σ_{word} [ word(fibre(E_SΦ+E_TΦ)) − word(fibre(E_SΦ−E_TΦ)) ]`.

Each of the four summands is `IntegrableOn (abox n ℓ)` along the fibre of a smooth state
(`KinOffdiag.pieces_integrableOn_fibre`), so the integral of the sum is the sum of the four
integrals, and each of the four vanishes by the corresponding off-diagonal lemma
(`gapWord_fibre_offdiag`, `neuWord_fibre_offdiag`, `momWord_fibre_offdiag`,
`mainWord_fibre_offdiag`) — these are the FS §6 "band" cancellations: since `S ≠ T` there is a
slot `i ≠ a` in `S △ T`, carrying `Q_i` on one side and `P_i` on the other, while `a ∈ S ∩ T`
makes both slot-`a` fibres mean-free.

The main body of the work is therefore an *assembly*: it is isolated in the (private) lemma
`slotTerm_aux`, whose four off-diagonal hypotheses are the delegations, and the theorem below
is the one-line instantiation.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- `IntegrableOn` of a product with a sign is `IntegrableOn` of the product with the
difference: the polarisation bracket of a word `W`. -/
private lemma integrableOn_offdiag_bracket {ℓ : ℝ} {n : ℕ} (a : Fin n)
    {U V : Submission.BoseGases.X n → ℝ} {W : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ}
    (h1 : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
        W (Work.BoseKinLoc.fibre n a U x)) (Submission.BoseGases.abox n ℓ))
    (h2 : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
        W (Work.BoseKinLoc.fibre n a V x)) (Submission.BoseGases.abox n ℓ)) :
    IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
        (W (Work.BoseKinLoc.fibre n a U x) - W (Work.BoseKinLoc.fibre n a V x)))
      (Submission.BoseGases.abox n ℓ) := by
  refine (h1.sub h2).congr_fun (fun x _ => ?_) (Submission.BoseGases.abox_measurable n ℓ)
  simp only [Pi.sub_apply]
  ring

/-- **The assembly.**  The polarised slot-`a` kinetic integrand vanishes off-diagonally, given
the four off-diagonal vanishing statements for the four one-body kinetic words. -/
private theorem slotTerm_aux {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (haS : (a : ℕ) ∈ S) (haT : (a : ℕ) ∈ T) (hST : S ≠ T)
    (hneu : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.neuWord ℓ d εT 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.neuWord ℓ d εT 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0)
    (hgap : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.gapWord ℓ b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0)
    (hmom : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.momWord ℓ d εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.momWord ℓ d εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0)
    (hmain : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.mainWord ℓ d s εT 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.mainWord ℓ d s εT 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) / 4) = 0 := by
  classical
  let ES : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ S Φ
  let ET : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ T Φ
  have hES : ContDiff ℝ (⊤ : ℕ∞) ES := Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hET : ContDiff ℝ (⊤ : ℕ∞) ET := Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  have hP : ContDiff ℝ (⊤ : ℕ∞) (ES + ET) := hES.add hET
  have hM : ContDiff ℝ (⊤ : ℕ∞) (ES - ET) := hES.sub hET
  -- integrability of the four one-body words along the two fibres
  obtain ⟨hgapP, hmomP, hmainP, hneuP⟩ :=
    pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ a hP
  obtain ⟨hgapM, hmomM, hmainM, hneuM⟩ :=
    pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ a hM
  -- integrability of the four polarisation brackets
  have hIneu : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      (Submission.BoseGases.abox n ℓ) := integrableOn_offdiag_bracket a hneuP hneuM
  have hIgap : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      (Submission.BoseGases.abox n ℓ) := integrableOn_offdiag_bracket a hgapP hgapM
  have hImom : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      (Submission.BoseGases.abox n ℓ) := integrableOn_offdiag_bracket a hmomP hmomM
  have hImain : IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      (Submission.BoseGases.abox n ℓ) := integrableOn_offdiag_bracket a hmainP hmainM
  -- integrability of the three partial sums
  have hI12 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      (Submission.BoseGases.abox n ℓ) := hIneu.add hIgap
  have hI123 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      (Submission.BoseGases.abox n ℓ) := hI12.add hImom
  have hI1234 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (((Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      (Submission.BoseGases.abox n ℓ) := hI123.add hImain
  -- the four off-diagonal integrals vanish
  have h0neu : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) = 0 := hneu
  have h0gap : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) = 0 := hgap
  have h0mom : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) = 0 := hmom
  have h0main : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) = 0 := hmain
  -- the pointwise four-way split of `fsT`
  have hfun : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      = fun x : Submission.BoseGases.X n =>
      ((Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x)))
      + (Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
         - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) := by
    funext x
    simp only [Work.BoseKinLoc.fsT_eq_sum]
    ring
  have key : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (ES + ET) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n a (ES - ET) x))) = 0 := by
    rw [hfun]
    rw [MeasureTheory.integral_add hI123 hImain,
        MeasureTheory.integral_add hI12 hImom,
        MeasureTheory.integral_add hIneu hIgap]
    rw [h0neu, h0gap, h0mom, h0main]
    ring
  rw [MeasureTheory.integral_div, key]
  norm_num

theorem slotTerm_zero_of_mem {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (haS : (a : ℕ) ∈ S) (haT : (a : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) / 4) = 0 :=
  slotTerm_aux hℓ a hΦ hS hT haS haT hST
    (Work.Analysis.BoseBand.neuWord_fibre_offdiag hℓ a hΦ hS hT haS haT hST)
    (gapWord_fibre_offdiag hℓ a hΦ hS hT haS haT hST)
    (momWord_offdiag hℓ a hΦ hS hT haS haT hST)
    (mainWord_offdiag_mem hℓ a hΦ hS hT haS haT hST)

end Work.BoseFixB2.DvApriori.KinOffdiag
