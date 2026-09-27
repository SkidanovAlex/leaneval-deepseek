import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLC6Core.conjBox_nsmul_mass
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLComp.BirkhoffDefs
import Submission.Work.EKLC6Core.atomInfo_chain
import Submission.Work.EKLC6Core.covariant_iterate
import Submission.Work.EKLC6Core.shape_comap_iterate
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.aemeasurable_atomInfo
import Submission.Work.EKLC6Core.HcondSig_le_lintegral_atomInfo
import Submission.Work.EKLC6Core.box_mass_asymptotic_condExp
import Submission.Work.EKLC6Core.goodset_borel

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

open Work.EKLContract


/-!
# `EKLC6Core.HcondSig_le_growth_plain` — Pisa 7.34/7.35, the "shape comparison" half

Target (Pisa 7.34, `≤` direction): for an `A`-ergodic probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a
leaf-wise system `ν = μ_x^{U}` for the contracted horospherical subgroup `U = Uminus t`, and a
plaque algebra `A` for `U` which is `aDiag t ·`-descending (`comap (aDiag t ·) A ≤ A`),

`HcondSig μ A (comap (aDiag t ·) A) ≤ ofReal (∫ growthFun (Uminus t) ν t dμ)`.

## What is proved here (sorry-free)

* `UBoxDef.lean`: the entrywise box `UBox U R`, with compactness/measurability lemmas.
* `shape_iterate_eq`, `shape_iterate_subset_conjBy_UBox`: the *shape sandwich* of Pisa 7.35 -- if
  the atom shape at `a^n x` is contained in `UBox (Uminus t) R`, then the shape of the `n`-fold
  pull-back at `x` is contained in the conjugated box `conjBy (-(n•t)) (UBox (Uminus t) R)`.
* `log_mass_conjBy_eq`: the mass of the conjugated box at `x` is the mass of the box at `a^n x`
  divided by the product of the contracted-box masses (`covariant_iterate`), i.e.
  `log ν x (conjBy (-(n•t)) S) = log ν (a^n x) S + ∑_{i<n} growthFun (a^{i+1} x)`.
* `atomInfo_sum_le_log_UBox`: **the good-time bound** -- for a.e. `x` and every time `n` with
  `shape A U (a^n x) ⊆ UBox (Uminus t) R`,
  `∑_{i<n} atomInfo (a^i x) ≤ log ν x (conjBy (-(n•t)) (UBox (Uminus t) R)) − log ν x (shape A U x)`.
  (This is Pisa's sandwich with the constant `c(x) = ν x (shape A U x)`.)

Together with `box_mass_asymptotic` (Pisa 7.18: the limit of the first term divided by `n` is
`∫ growthFun`) and `HcondSig_le_lintegral_atomInfo` (already proved: `HcondSig ≤ ∫⁻ ofReal
atomInfo`, both *directions* of `∫⁻ ofReal atomInfo = HcondSig` are now in the workspace), the
remaining step of the target is the analytic half

`∫⁻ x, ofReal (atomInfo A (Uminus t) ν t x) ∂μ ≤ ofReal (∫ growthFun (Uminus t) ν t ∂μ)`.

## The argument (resolved)

The analytic half `∫⁻ ofReal atomInfo ≤ ofReal (∫ growthFun)` — the content of Pisa 7.34/7.35 — is
proved here as `lintegral_atomInfo_le_ofReal_growth`, with **no ergodicity assumption beyond the
`A`-invariance of `μ`**, by combining four facts.

1. *A countable family of good sets.*  For `k : ℕ` let
   `G k = {y ∈ Z | shape A (Uminus t) y ⊆ UBox (Uminus t) (k+2)}`.  Each `G k` is **Borel**
   (`EKLC6Core.goodset_borel`).  Note the box is the *closed* entrywise box: this is exactly what
   makes the set measurable, since `U \ UBox U R` is then *open* in `U`, so that a shape (which
   is relatively open in `U` by `IsPlaqueAlgebra`) is contained in `UBox U R` iff it avoids a fixed
   countable dense `D ∩ (U \ UBox U R)`.  (With an *open* ball the complement is closed and the
   set is only co-analytic.)
2. *The good sets cover `Z`.*  `Z` is conull and every `y ∈ Z` has bounded atom shape, so
   `y ∈ G k` for `k = ⌈C⌉₊`.
3. *Poincaré recurrence, per point.*  For a.e. `x` and every `k`, if `x ∈ G k` then
   `a^{n}x ∈ G k` for infinitely many `n` (`MeasurePreserving.conservative` +
   `Conservative.ae_mem_imp_frequently_image_mem`).  Since the `G k` cover `Z`, for a.e. `x` there
   is a *single* `k = k(x)` (depending on `x`) with `a^{n}x ∈ G k` infinitely often.  This is the
   step where Pisa's proof uses `a`-ergodicity; the pointwise choice of `k` replaces it.
4. *Truncation + Birkhoff + monotone convergence.*  With `fN N = min (max ai 0) N` for a
   measurable representative `ai =ᵐ atomInfo`, the good-time bound `atomInfo_sum_le_log_UBox`
   bounds the Birkhoff sums of `fN N` at the good times by
   `log ν x (conjBy (-(n•t)) (UBox (Uminus t) (k+2))) - log ν x (shape A U x)`, whose `(1/n)`
   limit is `condExp (invariants (aDiag t ·)) μ (growthFun (Uminus t) ν t) x`
   (`EKLC6Core.box_mass_asymptotic_condExp`, the non-ergodic form of Pisa 7.18, combined with
   `Work.EKLComp.birkhoff_all`), the `log (shape)`-term contributing `o (n)`.  Hence
   `condExp (invariants (aDiag t ·)) μ (fN N) ≤ condExp (invariants (aDiag t ·)) μ (growthFun)`
   a.e. for every `N`; integrating with `integral_condExp` and letting `N → ∞` with
   `lintegral_iSup` gives the claim.

The two auxiliary facts are proved in the sibling modules `EKLC6Core.goodset_borel` and
`EKLC6Core.box_mass_asymptotic_condExp`; they are restated below as `aux_goodset_borel` and
`aux_box_asymptotic` only so that the assembly can be read in one file.

NOTE on the `σ`-algebra variable: `lintegral_atomInfo_le_ofReal_growth` carries the plaque algebra
as a field of `Work.EKLRelCross.MSAlg` rather than as a hypothesis `A : MeasurableSpace X3`.  A
local hypothesis of class type is offered to typeclass search, and would silently capture the
ambient `MeasurableSpace X3` instance in every statement below mentioning `MeasurableSet`,
`condExp`, `invariants` or `∫⁻`; since `A ≤ borel X3` the two instances are not defeq, so the
mistake surfaces as an elaboration error.
-/

/-! ## The shape sandwich and the mass comparison (Pisa 7.34/7.35) -/

/-- Iterated shape identity in the form used below: the shape of the atom of the `n`-fold
pull-back of `A` at `x` is the conjugate of the shape of the `A`-atom at the `n`-th iterate. -/
theorem shape_iterate_eq (t : Fin 3 → ℝ) (hU : IsHoro (Uminus t)) (A : MeasurableSpace X3)
    (n : ℕ) (x : X3) :
    shape (MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A) (Uminus t) x
      = conjBy (-((n : ℝ) • t))
          (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x)) :=
  shape_comap_iterate hU t A n x

/-- **The shape sandwich.**  If the atom shape at the `n`-th iterate `a^n x` of `x` is contained
in the entrywise box `UBox (Uminus t) R`, then the shape of the atom of the `n`-fold pull-back of
`A` at `x` is contained in the conjugated box. -/
theorem shape_iterate_subset_conjBy_UBox (t : Fin 3 → ℝ) (hU : IsHoro (Uminus t))
    {A : MeasurableSpace X3} {n : ℕ} {x : X3} {R : ℝ}
    (hsub : shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x) ⊆ UBox (Uminus t) R) :
    shape (MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A) (Uminus t) x
      ⊆ conjBy (-((n : ℝ) • t)) (UBox (Uminus t) R) := by
  rw [shape_iterate_eq t hU A n x]
  exact conjBy_mono _ hsub

/-- **The mass comparison underlying the sandwich:** the mass of the box `conjBy (-(n • t)) S` at
`x` is the mass of `S` at `a^n x` divided by the product of the contracted-box masses along the
orbit, hence its logarithm is `log ν (a^n x) S + ∑_{i<n} growthFun (a^{i+1} x)`.  Stated for an
arbitrary measurable `S` of finite positive mass at the tip. -/
theorem log_mass_conjBy_eq (t : Fin 3 → ℝ) {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : X3 → MeasureTheory.Measure SL3} {X' X'' : Set X3}
    (hL : IsLeafwise μ (Uminus t) ν X') (hcov : ACovariant ν X'') {n : ℕ} {x : X3}
    (hxG : ∀ j : ℕ, j ≤ n + 1 → ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'')
    {S : Set SL3} (hS : MeasurableSet S)
    (hfin : 0 < ν (((fun y : X3 => aDiag t • y)^[n]) x) S ∧
      ν (((fun y : X3 => aDiag t • y)^[n]) x) S < ⊤) :
    Real.log ((ν x (conjBy (-((n : ℝ) • t)) S)).toReal)
      = Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) S).toReal)
        + ∑ i ∈ Finset.range n,
            growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(i+1)]) x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hit := covariant_iterate t hL hU hcov n x (fun j hj => hxG j hj) hS
  have hbox : ∀ j ∈ Finset.range n,
      0 < ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) ∧
      ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) < ⊤ := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact conjBox_mass_pos hL hU t (hxG (j+1) (by omega)).1
  set P : ℝ≥0∞ := ∏ j ∈ Finset.range n,
      ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) with hP
  have hPpos : 0 < P := by
    rw [hP, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j hj
    exact (hbox j hj).1.ne'
  have hPtop : P < ⊤ := by
    rw [hP]
    exact ENNReal.prod_lt_top (fun j hj => (hbox j hj).2)
  have hsplit : ν x (conjBy (-((n : ℝ) • t)) S)
      = ν (((fun y : X3 => aDiag t • y)^[n]) x) S / P := by
    rw [ENNReal.eq_div_iff hPpos.ne' hPtop.ne, mul_comm]
    exact hit
  have hlogdiv : Real.log ((ν x (conjBy (-((n : ℝ) • t)) S)).toReal)
      = Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) S).toReal) - Real.log P.toReal := by
    rw [hsplit, ENNReal.toReal_div,
      Real.log_div (ENNReal.toReal_pos hfin.1.ne' hfin.2.ne).ne'
        (ENNReal.toReal_pos hPpos.ne' hPtop.ne).ne']
  have hPlog : Real.log P.toReal = ∑ j ∈ Finset.range n,
      Real.log ((ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x)
        (conjBox (Uminus t) t)).toReal) := by
    rw [hP, ENNReal.toReal_prod, Real.log_prod]
    intro j hj
    exact (ENNReal.toReal_pos (hbox j hj).1.ne' (hbox j hj).2.ne).ne'
  rw [hlogdiv, hPlog]
  have hgf : ∀ j ∈ Finset.range n,
      Real.log ((ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x)
          (conjBox (Uminus t) t)).toReal)
        = - growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(j+1)]) x) := by
    intro j _
    simp only [growthFun]
    ring
  rw [Finset.sum_congr rfl hgf, Finset.sum_neg_distrib]
  ring


/-! ## The pointwise bound at "good" times -/

/-- **The good-time bound (Pisa 7.34/7.35).**  For a.e. `x`, at every time `n` at which the atom
shape of `a^n x` is contained in the entrywise box `UBox (Uminus t) R`, the `n`-step
information of `x` is bounded by the logarithm of the mass of the conjugated box minus the
logarithm of the mass of the initial atom shape:

`∑_{i<n} atomInfo (a^i x) ≤ log ν x (a⁻ⁿ · UBox R · aⁿ) − log ν x (shape A U x)`.

This is the sandwich of Pisa 7.35 with the constant `c(x) = ν x (shape A U x)`; the right-hand
side (divided by `n`) has limit `∫ growthFun (Uminus t) ν t dμ` by `box_mass_asymptotic`
(Pisa 7.18), which is how the entropy upper bound is obtained. -/
theorem atomInfo_sum_le_log_UBox (t : Fin 3 → ℝ) {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : X3 → MeasureTheory.Measure SL3} {X' X'' : Set X3}
    (hErg : IsAErgodic μ) (hL : IsLeafwise μ (Uminus t) ν X')
    (hcov : ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uminus t) Z A) (hZ : μ Zᶜ = 0) {R : ℝ} (hR : 1 ≤ R) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      ((fun y : X3 => aDiag t • y)^[n]) x ∈ Z →
      shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x) ⊆ UBox (Uminus t) R →
      (∑ i ∈ Finset.range n,
          atomInfo A (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[i]) x))
        ≤ Real.log ((ν x (conjBy (-((n : ℝ) • t)) (UBox (Uminus t) R))).toReal)
          - Real.log ((ν x (shape A (Uminus t) x)).toReal) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hUc : IsClosed ((Uminus t : Subgroup SL3) : Set SL3) := hU.1
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  have hboxmeas : MeasurableSet (UBox (Uminus t) R) := measurableSet_UBox hUc R
  have hboxcomp : IsCompact (UBox (Uminus t) R) := isCompact_UBox hUc hR0
  have hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ := hErg.1 t
  -- the conull set of points all of whose iterates are good
  have hGae : ∀ᵐ x ∂μ, ∀ j : ℕ,
      ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' ∩ Z := by
    rw [ae_all_iff]
    intro j
    have hj : MeasurePreserving ((fun y : X3 => aDiag t • y)^[j]) μ μ := hmp.iterate j
    have h1 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hL.conull)
    have h2 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X'' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hX'')
    have h3 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ Z :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hZ)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact ⟨⟨hx1, hx2⟩, hx3⟩
  have hchain := atomInfo_chain (A := A) (Z := Z) t hErg hL hcov hX'' hplq hZ
  filter_upwards [hGae, hchain] with x hxG hchainx
  intro n hnZ hsub
  have hxG' : ∀ j : ℕ, j ≤ n + 1 →
      ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' := fun j _ => (hxG j).1
  have hxGZ' : ∀ j : ℕ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' ∩ Z := hxG
  -- the iterate identity for the shape at the tip and the box
  have htip : 0 < ν (((fun y : X3 => aDiag t • y)^[n]) x)
      (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x)) ∧
      ν (((fun y : X3 => aDiag t • y)^[n]) x)
        (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x)) < ⊤ :=
    shape_mass_pos hL hplq (hxG n).1.1 (hxG n).2
  have hboxpos : 0 < ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R) ∧
      ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R) < ⊤ :=
    ⟨lt_of_lt_of_le htip.1 (measure_mono hsub),
      (hL.radon _ (hxG n).1.1).lt_top_of_isCompact hboxcomp⟩
  -- (a) the iterate identity for the shape of the pulled-back atom
  have h1 : Real.log ((ν x (shape (MeasurableSpace.comap
        ((fun y : X3 => aDiag t • y)^[n]) A) (Uminus t) x)).toReal)
      = Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x)
            (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x))).toReal)
        + ∑ i ∈ Finset.range n,
            growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(i+1)]) x) :=
    iterate_log_pointwise t hL hU hcov hplq hxGZ' n
  -- (b) the shape at the tip is inside the box
  have h2 : Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x)
          (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x))).toReal)
      ≤ Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R)).toReal) :=
    Real.log_le_log (ENNReal.toReal_pos htip.1.ne' htip.2.ne)
      (ENNReal.toReal_mono hboxpos.2.ne (measure_mono hsub))
  -- (c) the mass of the conjugated box
  have h3 : Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R)).toReal)
        + ∑ i ∈ Finset.range n,
            growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(i+1)]) x)
      = Real.log ((ν x (conjBy (-((n : ℝ) • t)) (UBox (Uminus t) R))).toReal) :=
    (log_mass_conjBy_eq t hL hcov hxG' hboxmeas hboxpos).symm
  -- the initial atom shape has positive finite mass
  have hinit : 0 < ν x (shape A (Uminus t) x) ∧ ν x (shape A (Uminus t) x) < ⊤ :=
    shape_mass_pos hL hplq (hxG 0).1.1 (hxG 0).2
  rw [hchainx n]
  linarith [h1, h2, h3]


/-! ## Auxiliary facts, the analytic core, and the target

`aux_goodset_borel` and `aux_box_asymptotic` are proved in the sibling modules
`EKLC6Core.goodset_borel` and `EKLC6Core.box_mass_asymptotic_condExp`; they are restated here so
that the assembly below can be read in one file.

NOTE.  The `σ`-algebra variable is carried as a field of the structure
`Work.EKLRelCross.MSAlg` rather than as a hypothesis `A : MeasurableSpace X3`: a local hypothesis
of class type is offered to typeclass search by Lean, and would silently capture the ambient
`MeasurableSpace X3` instance in every statement below that mentions `MeasurableSet`, `condExp`,
`invariants` or `∫⁻`.  (`A ≤ borel X3` makes the two instances unequal, so the mistake would be
caught, but the statements would not elaborate.) -/

/-- For an `aDiag t ·`-descending plaque algebra the pointwise surprisal `atomInfo` is
nonnegative: the `A`-atom is contained in its `comap (aDiag t ·) A`-atom, so the `ν x`-mass of its
shape is no larger. -/
theorem atomInfo_nonneg_of_dec {U : Subgroup SL3} {ν : X3 → Measure SL3} {t : Fin 3 → ℝ}
    {A : MeasurableSpace X3}
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A) (x : X3) :
    0 ≤ atomInfo A U ν t x := by
  have hsub : shape A U x ⊆ shape (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) U x := by
    rintro u ⟨huU, hux⟩
    exact ⟨huU, Set.mem_sInter.mpr (fun s hs => hux s ⟨hdec s hs.1, hs.2⟩)⟩
  rw [atomInfo]
  rcases eq_or_ne (ν x (shape (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) U x))
      ⊤ with htop | hne
  · rw [htop, ENNReal.toReal_top, div_zero, Real.log_zero, neg_zero]
  · have hle : (ν x (shape A U x)).toReal
        ≤ (ν x (shape (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) U x)).toReal :=
      ENNReal.toReal_mono hne (measure_mono hsub)
    have hden0 : (0 : ℝ) ≤ (ν x (shape (MeasurableSpace.comap
        (fun x : X3 => aDiag t • x) A) U x)).toReal := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hden0 with h0 | hpos
    · rw [← h0, div_zero, Real.log_zero, neg_zero]
    · exact neg_nonneg.mpr (Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg hden0)
        ((div_le_one hpos).mpr hle))

/-- If `u n ≤ v n` frequently in `atTop` and `u → L`, `v → M`, then `L ≤ M`. -/
theorem le_of_frequently_le_of_tendsto {u v : ℕ → ℝ} {L M : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) (hv : Tendsto v atTop (𝓝 M))
    (h : ∃ᶠ n in atTop, u n ≤ v n) : L ≤ M := by
  by_contra hcon
  push_neg at hcon
  have hε : (0 : ℝ) < (L - M) / 3 := div_pos (sub_pos.mpr hcon) (by norm_num)
  have hLt : L - (L - M) / 3 < L := by
    rw [sub_lt_self_iff]; exact hε
  have hMt : M < M + (L - M) / 3 := lt_add_of_pos_right M hε
  have hevu : ∀ᶠ n in atTop, L - (L - M) / 3 < u n := hu.eventually (isOpen_Ioi.mem_nhds hLt)
  have hevv : ∀ᶠ n in atTop, v n < M + (L - M) / 3 := hv.eventually (isOpen_Iio.mem_nhds hMt)
  obtain ⟨n, hn, hnu, hnv⟩ := (h.and_eventually (hevu.and hevv)).exists
  linarith

/-- **Pisa 7.34, non-ergodic form (analytic half).**  The Lebesgue integral of the pointwise
surprisal `atomInfo` is bounded by `ofReal` of the integral of `growthFun`.

Proof: the sets `G k` of points of `Z` whose atom shape lies in the closed box
`UBox (Uminus t) (k+2)` are Borel (`aux_goodset_borel`) and cover `Z` (the shapes are bounded on
`Z`).  Poincaré recurrence for the measure-preserving `T = aDiag t ·` makes a.e. point of `G k`
return to `G k` infinitely often, and at the return times the shape sandwich
`atomInfo_sum_le_log_UBox` bounds the Birkhoff sums of `atomInfo` by the logarithm of the
conjugated box mass minus `log (ν x (shape A U x))`; the former has rate `gb` by
`aux_box_asymptotic` and the latter contributes `o (n)`.  Comparing with the Birkhoff theorem
`Work.EKLComp.birkhoff_all` applied to the truncations `fN N = min (max ai 0) N ∈ L¹` (with `ai` a
measurable representative of `atomInfo`) and integrating gives `∫ fN N ≤ ∫ gb = ∫ growthFun`;
monotone convergence in `N` finishes since `fN N ↑ atomInfo`. -/
theorem lintegral_atomInfo_le_ofReal_growth {μ : MeasureTheory.Measure X3}
    [IsProbabilityMeasure μ] {ν : X3 → Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hErg : IsAErgodic μ) (hL : IsLeafwise μ (Uminus t) ν X') (hcov : ACovariant ν X'')
    (hX'' : μ X''ᶜ = 0) (hmeas : Measurable (growthFun (Uminus t) ν t))
    (hint : Integrable (growthFun (Uminus t) ν t) μ)
    (S : Work.EKLRelCross.MSAlg) {Z : Set X3} (hplq : IsPlaqueAlgebra (Uminus t) Z S.m)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : X3 => aDiag t • x) S.m ≤ S.m) :
    ∫⁻ x, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x) ∂μ
      ≤ ENNReal.ofReal (∫ x, growthFun (Uminus t) ν t x ∂μ) := by
  classical
  have hUc : IsClosed ((Uminus t : Subgroup SL3) : Set SL3) := (uminus_isHoro t).1.1
  have hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ := hErg.1 t
  -- the conditional expectation of `growthFun` on the invariant σ-algebra
  set gb : X3 → ℝ := (fun x => condExp (MeasurableSpace.invariants (fun y : X3 => aDiag t • y))
    μ (growthFun (Uminus t) ν t) x) with hgb
  -- STEP 1: the countable family of good sets
  set G : ℕ → Set X3 :=
    (fun k => {y | y ∈ Z ∧ shape S.m (Uminus t) y ⊆ UBox (Uminus t) ((k : ℝ) + 2)}) with hG
  have hGmeas : ∀ k : ℕ, MeasurableSet (G k) := fun k => by
    simpa only [hG] using goodset_borel (A := S.m) (Z := Z) hUc hplq ((k : ℝ) + 2)
  have hcover : ∀ y ∈ Z, ∃ k : ℕ, y ∈ G k := by
    intro y hy
    obtain ⟨C, hC⟩ := (hplq.2.2.2 y hy).2.2.2
    refine ⟨⌈C⌉₊, ?_⟩
    simp only [hG, Set.mem_ofPred_eq]
    refine ⟨hy, fun u hu => ⟨hu.1, fun i j => ?_⟩⟩
    have h1 : |u i j| ≤ C := hC u hu i j
    have h3 : C ≤ ((⌈C⌉₊ : ℕ) : ℝ) := Nat.le_ceil C
    linarith
  -- STEP 2: Poincaré recurrence for the measure preserving `aDiag t ·`
  have hrec : ∀ k : ℕ, ∀ᵐ x ∂μ, x ∈ G k →
      ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k := fun k =>
    (hmp.conservative).ae_mem_imp_frequently_image_mem (hGmeas k).nullMeasurableSet
  have hgt : ∀ᵐ x ∂μ, ∃ k : ℕ, x ∈ G k ∧
      ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k := by
    have h1 : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
    have h2 : ∀ᵐ x ∂μ, ∀ k : ℕ, (x ∈ G k →
        ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k) := ae_all_iff.mpr hrec
    filter_upwards [h1, h2] with x hxZ hall
    obtain ⟨k, hk⟩ := hcover x hxZ
    exact ⟨k, hk, hall k hk⟩
  -- STEP 3: the box asymptotics (Pisa 7.18 in the non-ergodic case)
  have hbox : ∀ᵐ x ∂μ, ∀ k : ℕ, Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
      (𝓝 (gb x)) := by
    have h0 : ∀ k : ℕ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
        ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
        (𝓝 (gb x)) := by
      intro k
      have h2 : (2 : ℝ) ≤ ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      filter_upwards [box_mass_asymptotic_condExp (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hL
        hcov hX'' hErg.1 hmeas hint h2] with x hx
      rw [hgb]
      exact hx
    exact ae_all_iff.mpr h0
  -- STEP 4: the shape sandwich at the good times
  have hsw : ∀ᵐ x ∂μ, ∀ (k n : ℕ), ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k →
      (∑ i ∈ Finset.range n,
        atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x))
        ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t))
            (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
          - Real.log ((ν x (shape S.m (Uminus t) x)).toReal) := by
    have h0 : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ n : ℕ, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k →
        (∑ i ∈ Finset.range n,
          atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x))
          ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t))
              (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
            - Real.log ((ν x (shape S.m (Uminus t) x)).toReal) := by
      intro k
      have h2 : (1 : ℝ) ≤ ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      filter_upwards [atomInfo_sum_le_log_UBox (μ := μ) (ν := ν) (X' := X') (X'' := X'') t
        hErg hL hcov hX'' hplq hZ (R := ((k : ℝ) + 2)) h2] with x hx
      intro n hn
      exact hx n hn.1 hn.2
    exact ae_all_iff.mpr h0
  -- STEP 5: a measurable representative of `atomInfo` and the truncations
  obtain ⟨ai, hai_meas, hai_eq⟩ :=
    aemeasurable_atomInfo (μ := μ) (ν := ν) (X' := X') (A := S.m) (Z := Z) t hErg hL hplq hZ
  set fN : ℕ → X3 → ℝ := (fun N x => min (max (ai x) 0) N) with hfN
  have hfNmeas : ∀ N : ℕ, Measurable (fN N) := fun N => by
    rw [hfN]
    exact (hai_meas.max measurable_const).min measurable_const
  have hfNint : ∀ N : ℕ, Integrable (fN N) μ := by
    intro N
    refine Integrable.of_bound (hfNmeas N).aestronglyMeasurable (N : ℝ) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have h1 : 0 ≤ fN N x := by
      rw [hfN]; simp only []
      exact le_min (le_max_right _ _) (Nat.cast_nonneg N)
    rw [abs_of_nonneg h1]
    rw [hfN]; simp only []
    exact min_le_right _ _
  have horb : ∀ᵐ x ∂μ, ∀ i : ℕ,
      atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x)
        = ai (((fun x : X3 => aDiag t • x)^[i]) x) := by
    have h0 : ∀ i : ℕ, ∀ᵐ x ∂μ,
        atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x)
          = ai (((fun x : X3 => aDiag t • x)^[i]) x) := fun i =>
      (hmp.iterate i).quasiMeasurePreserving.ae_eq_comp hai_eq
    exact ae_all_iff.mpr h0
  -- STEP 6: Birkhoff's theorem for the truncations
  have hbirk : ∀ᵐ x ∂μ, ∀ N : ℕ, Tendsto
      (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x)) :=
    ae_all_iff.mpr (fun N => Work.EKLComp.birkhoff_all μ (fun x : X3 => aDiag t • x) hmp
      (fN N) (hfNint N))
  -- STEP 7: the pointwise comparison at a.e. point, using the good return times
  have hcmp : ∀ᵐ x ∂μ, ∀ N : ℕ,
      condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x ≤ gb x := by
    filter_upwards [hgt, hbox, hsw, horb, hbirk] with x hgtx hboxx hswx horbx hbirkx
    intro N
    obtain ⟨k, -, hfreq⟩ := hgtx
    set B : ℕ → ℝ := (fun n => ((n : ℝ))⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
        - ((n : ℝ))⁻¹ * Real.log ((ν x (shape S.m (Uminus t) x)).toReal)) with hB
    have hAB : ∃ᶠ n in atTop,
        Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x ≤ B n := by
      refine hfreq.mono (fun n hn => ?_)
      have hS := hswx k n hn
      have hle : (∑ i ∈ Finset.range n, fN N (((fun x : X3 => aDiag t • x)^[i]) x))
          ≤ ∑ i ∈ Finset.range n,
              atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h0 : 0 ≤ atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
          atomInfo_nonneg_of_dec hdec _
        have h1 : ai (((fun x : X3 => aDiag t • x)^[i]) x)
            = atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
          (horbx i).symm
        rw [hfN]
        simp only []
        refine le_trans (min_le_left _ _) ?_
        rw [max_le_iff]
        exact ⟨by rw [h1], h0⟩
      have hπ : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
      calc Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x
          = ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
              fN N (((fun x : X3 => aDiag t • x)^[i]) x) := by
            rw [Work.EKLComp.Birkhoff.birkA_def]
        _ ≤ ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
              atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
            mul_le_mul_of_nonneg_left hle hπ
        _ ≤ B n := by
            rw [hB]
            simpa only [mul_sub] using mul_le_mul_of_nonneg_left hS hπ
    have hAlim : Tendsto (fun n : ℕ =>
        Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x) atTop
        (𝓝 (condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x)) :=
      hbirkx N
    have hBlim : Tendsto B atTop (𝓝 (gb x)) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
          ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
          (𝓝 (gb x)) := hboxx k
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹
          * Real.log ((ν x (shape S.m (Uminus t) x)).toReal)) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa using h3.mul_const (Real.log ((ν x (shape S.m (Uminus t) x)).toReal))
      have h4 := h1.sub h2
      rw [sub_zero] at h4
      refine h4.congr' (Filter.Eventually.of_forall (fun n => ?_))
      rw [hB]
    exact le_of_frequently_le_of_tendsto hAlim hBlim hAB
  -- STEP 8: integration
  have hgbint : Integrable gb μ := by
    rw [hgb]
    exact MeasureTheory.integrable_condExp (m := MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) (μ := μ) (f := growthFun (Uminus t) ν t)
  have hInt1 : ∀ N : ℕ, ∫ x, fN N x ∂μ ≤ ∫ x, gb x ∂μ := by
    intro N
    have h2 : ∫ x, condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ
          (fN N) x ∂μ ≤ ∫ x, gb x ∂μ := by
      refine integral_mono_ae (MeasureTheory.integrable_condExp (m := MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) (μ := μ) (f := fN N)) hgbint ?_
      exact hcmp.mono (fun x hx => hx N)
    have h3 : ∫ x, condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ
          (fN N) x ∂μ = ∫ x, fN N x ∂μ :=
      MeasureTheory.integral_condExp (m := MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) (μ := μ) (f := fN N)
        (MeasurableSpace.invariants_le (fun x : X3 => aDiag t • x))
    rw [h3] at h2
    exact h2
  have hIntg : ∫ x, gb x ∂μ = ∫ x, growthFun (Uminus t) ν t x ∂μ := by
    rw [hgb]
    exact MeasureTheory.integral_condExp (m := MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) (μ := μ) (f := growthFun (Uminus t) ν t)
      (MeasurableSpace.invariants_le (fun x : X3 => aDiag t • x))
  -- STEP 9: monotone convergence in `N`
  have hMCT : ∫⁻ x, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x) ∂μ
      = ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (fN N x) ∂μ := by
    have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x)
        = ⨆ N : ℕ, ENNReal.ofReal (fN N x) := by
      filter_upwards [hai_eq.symm] with x hx1
      rw [← hx1]
      have hc0 : (0 : ℝ) ≤ ai x := by
        have h0 : 0 ≤ atomInfo S.m (Uminus t) ν t x := atomInfo_nonneg_of_dec hdec x
        rwa [← hx1] at h0
      have hfNc : ∀ N : ℕ, fN N x = min (ai x) N := by
        intro N
        rw [hfN]; simp only []
        rw [max_eq_left hc0]
      refine le_antisymm ?_ ?_
      · refine le_trans ?_ (le_iSup (fun N : ℕ => ENNReal.ofReal (fN N x)) ⌈ai x⌉₊)
        rw [hfNc ⌈ai x⌉₊, min_eq_left (Nat.le_ceil (ai x))]
      · refine iSup_le (fun N => ENNReal.ofReal_le_ofReal ?_)
        rw [hfNc N]
        exact min_le_left _ _
    have hmono : Monotone (fun N x => ENNReal.ofReal (fN N x)) := by
      intro i j hij x
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hfN]; simp only []
      exact min_le_min le_rfl (Nat.cast_le.mpr hij)
    have hmeas' : ∀ N : ℕ, Measurable (fun x => ENNReal.ofReal (fN N x)) :=
      fun N => ENNReal.measurable_ofReal.comp (hfNmeas N)
    have hmain := lintegral_iSup (μ := μ) (f := fun N x => ENNReal.ofReal (fN N x)) hmeas' hmono
    rw [← hmain]
    exact lintegral_congr_ae hpt
  calc ∫⁻ x, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x) ∂μ
      = ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (fN N x) ∂μ := hMCT
    _ = ⨆ N : ℕ, ENNReal.ofReal (∫ x, fN N x ∂μ) := by
        refine iSup_congr (fun N => ?_)
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfNint N)
          (ae_of_all _ (fun x => by
            rw [hfN]; simp only []
            exact le_min (le_max_right _ _) (Nat.cast_nonneg N)))).symm
    _ ≤ ENNReal.ofReal (∫ x, growthFun (Uminus t) ν t x ∂μ) := by
        refine iSup_le (fun N => ENNReal.ofReal_le_ofReal ?_)
        exact le_trans (hInt1 N) (le_of_eq hIntg)


theorem HcondSig_le_growth_plain {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3 (borel Work.EKLContract.X3) μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  refine le_trans (HcondSig_le_lintegral_atomInfo (ν := ν) (X' := X') t hErg hL hplq hZ hdec) ?_
  exact lintegral_atomInfo_le_ofReal_growth (S := ⟨A⟩) t hErg hL hcov hX'' hmeas hint hplq hZ hdec

end Work.EKLC6Core
