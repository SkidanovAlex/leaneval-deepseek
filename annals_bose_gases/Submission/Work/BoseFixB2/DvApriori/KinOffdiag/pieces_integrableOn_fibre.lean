import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre`

**Each of the four one-body pieces of FS `eq:DefT` is integrable on the box along the slot-`j`
fibre of a smooth `n`-body state** — as a function of the configuration `x`:

    `x ↦ 1_{Λ(0)}(xⱼ) · word ℓ … 0 (fibre n j Φ x)`   for
    `word ∈ {gapWord, momWord, mainWord, neuWord}`.

These are the four summands of the box-restricted slot integrand
`1_{Λ(0)}(xⱼ)·fsT ℓ d s ε_T b 0 (fibre n j Φ x)`, whose integrability on `abox n ℓ` is
`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`.  Consumers (the off-diagonal fibre
brackets `gapWord_fibre_offdiag`, `neuWord_fibre_offdiag`, `momWord_fibre_offdiag`,
`mainWord_fibre_offdiag`) need the pieces *individually*, to split
`∫ (f − g) = ∫ f − ∫ g`.

## The argument: separation in the parameters, not in the fibre

The four words, read at the anchored box `u = 0` as functions of the **parameters**
`(ε_T, b)` (with `ℓ, d, s` and the state fixed), satisfy

    `fsT ℓ d s ε_T b 0 ψ = ε_T·N + b·G + (ε_T·b)·M + (1−ε_T)·B₁ + ε_T·B₂`

where

* `N = neuWord ℓ d 1 0 ψ`,  `G = gapWord ℓ 1 0 ψ`,  `M = momWord ℓ d 1 1 0 ψ`  (the first three
  words are *homogeneous* in their parameters: `neuWord` is linear in `ε_T`, `gapWord` is linear
  in `b`, `momWord` is bilinear in `(ε_T, b)`);
* `B₁ = mainWord ℓ d s 0 0 ψ`, `B₂ = mainWord ℓ d s 1 0 ψ` (the `mainWord` is *affine* in
  `ε_T`).

This is a pointwise identity of functions of `x` (`fsT_decompose` below), so it holds for every
configuration.  Since `integrableOn_fsT_fibre_smooth` gives the integrability of the
*whole* parametrised integrand for **every** `(ε_T, b) ∈ ℝ²` (and every `s`), the atoms — and
hence the four words at the requested parameters — are integrable as *linear combinations of
integrable functions*:

* `B₁ = S(0,0)`,  `G = S(0,1) − S(0,0)`,  `M = S(1,1) − S(1,0) − S(0,1) + S(0,0)`,
  `N + B₂ − B₁ = S(1,0) − S(0,0)`, where `S(ε_T,b) := x ↦ 1_{Λ(0)}(xⱼ)·fsT ℓ d s ε_T b 0 (fibre)`;
* `B₂` is the `ε_T = 0` value of the family with `s` replaced by `d·s` (`mainWord`'s second
  coefficient is `[·−(2dsℓ)⁻¹]₊²`, and the first coefficient at parameter `d·s` is
  `[·−(2·(d·s)·ℓ)⁻¹]₊² = [·−(2dsℓ)⁻¹]₊²`), hence integrable as well;
* therefore `N = (S(1,0) − S(0,0)) − B₂ + B₁` is integrable.

So no measurability, no uniform bound and no compactly supported modification of the fibre are
needed: everything follows from `IntegrableOn` being closed under sums, differences and scalar
multiples, plus the pointwise algebra of the definitions.
-/

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `IntegrableOn` is closed under left multiplication by a constant. -/
private lemma integrableOn_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (h : IntegrableOn f s μ) (c : ℝ) :
    IntegrableOn (fun x => c * f x) s μ :=
  h.integrable.const_mul c

/-- **The parameter decomposition of the localised box word at the anchored box.**

For every one-body state `ψ`, every `(ε_T, b)` and every `s`, the word `fsT` is the following
explicit combination of the four *unit-parameter* words: the Neumann word is linear in `ε_T`,
the gap word linear in `b`, the momentum word bilinear in `(ε_T, b)`, and the main word is
`(1−ε_T)·mainWord(ε_T = 0) + ε_T·mainWord(ε_T = 1)` (affine in `ε_T`). -/
private lemma fsT_decompose (ℓ d s eT bp : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s eT bp 0 ψ
      = eT * Work.BoseKinLoc.neuWord ℓ d 1 0 ψ
        + bp * Work.BoseKinLoc.gapWord ℓ 1 0 ψ
        + (eT * bp) * Work.BoseKinLoc.momWord ℓ d 1 1 0 ψ
        + (1 - eT) * Work.BoseKinLoc.mainWord ℓ d s 0 0 ψ
        + eT * Work.BoseKinLoc.mainWord ℓ d s 1 0 ψ := by
  rw [Work.BoseKinLoc.fsT_eq_sum]
  simp only [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.gapWord, Work.BoseKinLoc.momWord,
    Work.BoseKinLoc.mainWord]
  ring

theorem pieces_integrableOn_fibre {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
  classical
  -- the box is measurable
  have hs : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  -- the whole parametrised integrand is integrable for *every* value of the parameters
  have hInt : ∀ (s' eT bp : ℝ), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) * Work.BoseKinLoc.fsT ℓ d s' eT bp 0
          (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    intro s' eT bp
    exact Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s')
      (εT := eT) (b := bp) hℓ j hΦ
  -- ## the atoms
  -- `B₁ = mainWord(ε_T = 0)`: the `ε_T = b = 0` value of the family
  have hB₁ : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d s 0 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (hInt s 0 0).congr_fun ?_ hs
    intro x hx
    beta_reduce
    rw [fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 0)]
    ring
  -- `B₂ = mainWord(ε_T = 1)`: the `ε_T = 0` value of the family with `s := d*s`
  have hB₂ : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d s 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (hInt (d * s) 0 0).congr_fun ?_ hs
    intro x hx
    beta_reduce
    rw [fsT_decompose (ℓ := ℓ) (d := d) (s := d * s) (eT := 0) (bp := 0)]
    simp only [Work.BoseKinLoc.mainWord]
    ring
  -- `G = gapWord(1)`: the `b`-difference of the family
  have hG : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.gapWord ℓ 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine ((hInt s 0 1).sub (hInt s 0 0)).congr_fun ?_ hs
    intro x hx
    simp only [Pi.sub_apply]
    rw [fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 1),
      fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 0)]
    ring
  -- `M = momWord(1,1)`: the mixed second difference of the family
  have hM : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.momWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (((hInt s 1 1).sub (hInt s 1 0)).sub
      ((hInt s 0 1).sub (hInt s 0 0))).congr_fun ?_ hs
    intro x hx
    simp only [Pi.sub_apply]
    rw [fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 1) (bp := 1),
      fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 1) (bp := 0),
      fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 1),
      fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 0)]
    ring
  -- `N = neuWord(1)`: from `S(1,0) − S(0,0) = N + B₂ − B₁`
  have hN : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.neuWord ℓ d 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine ((((hInt s 1 0).sub (hInt s 0 0)).sub hB₂).add hB₁).congr_fun ?_ hs
    intro x hx
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 1) (bp := 0),
      fsT_decompose (ℓ := ℓ) (d := d) (s := s) (eT := 0) (bp := 0)]
    ring
  -- ## the four words at the requested parameters
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (integrableOn_const_mul hG b).congr_fun ?_ hs
    intro x hx
    simp only [Work.BoseKinLoc.gapWord]
    ring
  · refine (integrableOn_const_mul hM (εT * b)).congr_fun ?_ hs
    intro x hx
    simp only [Work.BoseKinLoc.momWord]
    ring
  · refine ((integrableOn_const_mul hB₁ (1 - εT)).add
      (integrableOn_const_mul hB₂ εT)).congr_fun ?_ hs
    intro x hx
    simp only [Pi.add_apply, Work.BoseKinLoc.mainWord]
    ring
  · refine (integrableOn_const_mul hN εT).congr_fun ?_ hs
    intro x hx
    simp only [Work.BoseKinLoc.neuWord]
    ring

end Work.BoseFixB2.DvApriori.KinOffdiag
