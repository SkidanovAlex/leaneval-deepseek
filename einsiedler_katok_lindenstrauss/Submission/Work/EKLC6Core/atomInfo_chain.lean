import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.growth_le_atomInfo
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.shape_comap_iterate
import Submission.Work.EKLC6Core.covariant_iterate
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.atomInfo_chain` — the telescoping of the atom information along the `a`-orbit

For a leaf-wise system `ν = μ_x^{U}` of an `A`-ergodic probability `μ`, `U = Uminus t` the stable
horospherical subgroup of `a = aDiag t`, and `A` a plaque algebra for `U`, the pointwise
information `atomInfo A U ν t` (Pisa 7.34) telescopes along the `a`-orbit: for a.e. `x` and every
`n`,

  `∑_{i<n} atomInfo (a^i x) = log ν x (shape (comap (a^n) A) U x) - log ν x (shape A U x)`.

The two ingredients are

* the **one-step covariance** of the leaf-wise system (`covariant_step`, Pisa 7.16/7.18):
  `ν x (conjBy (-t) S) · ν (a x) (conjBox U t) = ν (a x) S`, which combined with
  `shape (comap a A) U x = conjBy (-t) (shape A U (a x))` (`shape_comap_conj`) says that the
  shape of the pulled-back atom at `x` is the conjugated shape of the atom at `a x`;
* the **pointwise identity** `atomInfo x = ψ (a x) - ψ x + growthFun (a x)` with
  `ψ y = log ν y (shape A U y)` (Pisa 7.34, a.e. form `atomInfo_ae_eq_aux`), whose sum along the
  orbit is a telescoping `ψ (a^n x) - ψ x` plus the Birkhoff sum of `growthFun`.

Iterating the one-step covariance (`covariant_iterate`) and taking logarithms gives the "iterate
covariance"
`log ν x (shape (comap (a^n) A) U x) = log ν (a^n x) (shape A U (a^n x)) + ∑_{i<n} growthFun (a^{i+1} x)`,
which converts the telescoped `ψ`-difference into the shape masses of the target statement.

The a.e. statement is obtained by restricting to the conull set
`{x | ∀ j, a^j x ∈ X' ∩ X'' ∩ Z}`: every iterate of a "good" point is again good, and each of the
three conditions is preserved by the measure-preserving flow `a`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The flow, its iterates, and the iterated pull-back of a `σ`-algebra -/

/-- The `n`-fold pull-back of a `σ`-algebra along the flow `aDiag t`. -/
def Aiter (t : Fin 3 → ℝ) (A : MeasurableSpace X3) (n : ℕ) : MeasurableSpace X3 :=
  MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A

/-- The `n`-th iterate of the flow `y ↦ aDiag t • y`. -/
def aIter (t : Fin 3 → ℝ) (n : ℕ) (x : X3) : X3 := ((fun y : X3 => aDiag t • y)^[n]) x

@[simp] theorem Aiter_zero (t : Fin 3 → ℝ) (A : MeasurableSpace X3) : Aiter t A 0 = A :=
  MeasurableSpace.comap_id

@[simp] theorem aIter_zero (t : Fin 3 → ℝ) (x : X3) : aIter t 0 x = x := rfl

theorem aIter_succ (t : Fin 3 → ℝ) (n : ℕ) (x : X3) :
    aIter t (n + 1) x = aDiag t • aIter t n x := Function.iterate_succ_apply' _ _ _

theorem aIter_succ' (t : Fin 3 → ℝ) (n : ℕ) (x : X3) :
    aIter t (n + 1) x = aIter t n (aDiag t • x) := Function.iterate_succ_apply _ _ _

/-- **Iterated shape identity** (`shape_comap_iterate` in the `Aiter`/`aIter` vocabulary): the
shape of the atom of the `n`-fold pull-back of `A` is the conjugate of the shape of the `A`-atom
at the `n`-th iterate. -/
theorem shape_Aiter {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ)
    (A : MeasurableSpace X3) (n : ℕ) (x : X3) :
    shape (Aiter t A n) U x = conjBy (-((n : ℝ) • t)) (shape A U (aIter t n x)) :=
  shape_comap_iterate hU t A n x

/-- The shape of a plaque algebra is Borel measurable (its atom is an open `U`-plaque). -/
theorem measurableSet_shape_of_mem {U : Subgroup SL3} (hU : IsHoro U)
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra U Z A) {y : X3} (hy : y ∈ Z) :
    MeasurableSet (shape A U y) := by
  obtain ⟨O, hOopen, hOshape⟩ := (hplq.2.2.2 y hy).2.2.1
  rw [hOshape]
  exact hOopen.measurableSet.inter hU.1.measurableSet

/-- **One step of the covariance** of a leaf-wise system, in the `conjBy (-t)` orientation:
`ν x (conjBy (-t) C) · ν (a x) (conjBox U t) = ν (a x) C`. -/
theorem covariant_step_conj {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (hL : IsLeafwise μ U ν X') (hU : IsHoro U)
    (hcov : ACovariant ν X'') (t : Fin 3 → ℝ) {x : X3}
    (hx : x ∈ X' ∩ X'') (hax : aDiag t • x ∈ X' ∩ X'') {C : Set SL3} (hC : MeasurableSet C) :
    ν x (conjBy (-t) C) * ν (aDiag t • x) (conjBox U t) = ν (aDiag t • x) C := by
  have hC' : MeasurableSet (conjBy (-t) C) := measurableSet_conjBy (-t) hC
  have h := covariant_step hL hcov (measurableSet_box1 hU) t (y := aDiag t • x) hax
    (by rw [aDiag_neg_smul]; exact hx) (C := conjBy (-t) C) hC'
  rw [aDiag_neg_smul,
    show conjBy t (conjBy (-t) C) = C from by simpa using conjBy_neg_conjBy (-t) C] at h
  exact h

/-- `comap` of the flow, one step further: `comap a (Aiter t A n) = Aiter t A (n+1)`. -/
theorem comap_iterate_succ (t : Fin 3 → ℝ) (A : MeasurableSpace X3) (n : ℕ) :
    MeasurableSpace.comap (fun y : X3 => aDiag t • y) (Aiter t A n) = Aiter t A (n + 1) := by
  rw [Aiter, Aiter, MeasurableSpace.comap_comp, Function.iterate_succ]

/-- `covariant_iterate` rephrased in the `Aiter`/`aIter` vocabulary. -/
theorem covariant_iterate' {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup SL3} {ν : X3 → Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    (n : ℕ) (x : X3)
    (hx : ∀ j : ℕ, j ≤ n + 1 → aIter t j x ∈ X' ∩ X'')
    {S : Set SL3} (hS : MeasurableSet S) :
    ν x (conjBy (-((n : ℝ) • t)) S) *
        ∏ j ∈ Finset.range n, ν (aIter t (j + 1) x) (conjBox U t) = ν (aIter t n x) S :=
  covariant_iterate t hL hU hcov n x hx hS

/-! ## The iterate covariance in logarithmic form -/

/-- **The iterate identity.**  Along the orbit of a point `x` all of whose iterates lie in
`X' ∩ X'' ∩ Z`, the mass of the shape of the `n`-fold pull-back of `A` is the product of the
mass of the `A`-atom shape at the `n`-th iterate with the contracted-box masses along the orbit;
in logarithms this is

`log ν x (shape (Aiter t A n) U x)
   = log ν (aIter t n x) (shape A U (aIter t n x)) + ∑_{i<n} growthFun U ν t (aIter t (i+1) x)`. -/
theorem iterate_log_pointwise {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    {A : MeasurableSpace X3} {Z : Set X3} (hplq : IsPlaqueAlgebra U Z A)
    {x : X3} (hxG : ∀ j : ℕ, aIter t j x ∈ X' ∩ X'' ∩ Z) :
    ∀ n : ℕ,
      Real.log ((ν x (shape (Aiter t A n) U x)).toReal)
        = Real.log ((ν (aIter t n x) (shape A U (aIter t n x))).toReal)
          + ∑ i ∈ Finset.range n, growthFun U ν t (aIter t (i+1) x) := by
  intro n
  set S : Set SL3 := shape A U (aIter t n x) with hS
  have hSZ : aIter t n x ∈ Z := (hxG n).2
  have hSmeas : MeasurableSet S := by rw [hS]; exact measurableSet_shape_of_mem hU hplq hSZ
  -- the iterated covariance
  have hit : ν x (conjBy (-((n : ℝ) • t)) S) *
      ∏ j ∈ Finset.range n, ν (aIter t (j + 1) x) (conjBox U t) = ν (aIter t n x) S :=
    covariant_iterate' t hL hU hcov n x (fun j _ => ⟨(hxG j).1.1, (hxG j).1.2⟩) hSmeas
  have hmain : ν x (shape (Aiter t A n) U x) *
      ∏ j ∈ Finset.range n, ν (aIter t (j + 1) x) (conjBox U t) = ν (aIter t n x) S := by
    rw [shape_Aiter hU t A n x]; exact hit
  -- positivity of the factors
  have hbox : ∀ j : ℕ, 0 < ν (aIter t (j + 1) x) (conjBox U t) ∧
      ν (aIter t (j + 1) x) (conjBox U t) < ⊤ :=
    fun j => conjBox_mass_pos hL hU t (hxG (j + 1)).1.1
  have hCpos : 0 < ν (aIter t n x) S ∧ ν (aIter t n x) S < ⊤ := by
    rw [hS]; exact shape_mass_pos hL hplq (hxG n).1.1 hSZ
  -- take real values
  set a : ℝ := (ν x (shape (Aiter t A n) U x)).toReal with ha
  set P : ℝ := ∏ j ∈ Finset.range n, (ν (aIter t (j + 1) x) (conjBox U t)).toReal with hP
  set c : ℝ := (ν (aIter t n x) S).toReal with hc
  have haPc : a * P = c := by
    have h := congrArg ENNReal.toReal hmain
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod] at h
    rw [ha, hP, hc]; exact h
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun j _ => ENNReal.toReal_pos (hbox j).1.ne' (hbox j).2.ne)
  have hcpos : 0 < c := by
    rw [hc]; exact ENNReal.toReal_pos hCpos.1.ne' hCpos.2.ne
  have hapos : 0 < a := by nlinarith [haPc, hPpos, hcpos]
  -- logarithms
  have hlog : Real.log c = Real.log a +
      ∑ j ∈ Finset.range n, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) := by
    calc Real.log c = Real.log (a * P) := by rw [haPc]
      _ = Real.log a + Real.log P := Real.log_mul hapos.ne' hPpos.ne'
      _ = Real.log a + ∑ j ∈ Finset.range n,
            Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) := by
          rw [hP, Real.log_prod (fun j _ =>
            (ENNReal.toReal_pos (hbox j).1.ne' (hbox j).2.ne).ne')]
  have hgf : ∀ j : ℕ, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) =
      - growthFun U ν t (aIter t (j + 1) x) := by
    intro j; simp only [growthFun]; ring
  have hsum : ∑ j ∈ Finset.range n, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal)
      = - ∑ j ∈ Finset.range n, growthFun U ν t (aIter t (j + 1) x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => hgf j)
  rw [hsum] at hlog
  have hgoal : Real.log a = Real.log c +
      ∑ j ∈ Finset.range n, growthFun U ν t (aIter t (j + 1) x) := by
    rw [hlog]; ring
  exact hgoal

/-! ## The telescoping -/

/-- **The telescoping of the atom information along the `a`-orbit.** -/
theorem atomInfo_chain {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
          Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t
            ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[i] x))
        = Real.log ((ν x (Work.EKLContract.shape
              (MeasurableSpace.comap ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) A)
              (Work.EKLC6Core.Uminus t) x)).toReal)
          - Real.log ((ν x (Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) x)).toReal) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ := hErg.1 t
  -- the conull set on which all iterates are good
  have hGae : ∀ᵐ x ∂μ, ∀ j : ℕ, aIter t j x ∈ X' ∩ X'' ∩ Z := by
    show ∀ᵐ x ∂μ, ∀ j : ℕ, (fun y : X3 => aDiag t • y)^[j] x ∈ X' ∩ X'' ∩ Z
    rw [ae_all_iff]
    intro j
    have hj : MeasurePreserving ((fun y : X3 => aDiag t • y)^[j]) μ μ := hmp.iterate j
    have h1 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ X' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hL.conull)
    have h2 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ X'' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hX'')
    have h3 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ Z :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hZ)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact ⟨⟨hx1, hx2⟩, hx3⟩
  -- the pointwise identity of Pisa 7.34, along the orbit
  have hAtomAe : ∀ᵐ x ∂μ, ∀ k : ℕ,
      atomInfo A (Uminus t) ν t (aIter t k x)
        = Real.log ((ν (aIter t (k+1) x) (shape A (Uminus t) (aIter t (k+1) x))).toReal)
          - Real.log ((ν (aIter t k x) (shape A (Uminus t) (aIter t k x))).toReal)
          + growthFun (Uminus t) ν t (aIter t (k+1) x) := by
    have hbase := atomInfo_ae_eq_aux (t := t) hL hU hcov hX'' hErg.1 hplq hZ
    rw [ae_all_iff]
    intro k
    have hk := (hmp.iterate k).quasiMeasurePreserving.ae hbase
    filter_upwards [hk] with x hx
    rw [show ((fun y : X3 => aDiag t • y)^[k]) x = aIter t k x from rfl] at hx
    rw [← aIter_succ t k x] at hx
    exact hx
  -- the iterate identity
  have hIterAe : ∀ᵐ x ∂μ, ∀ n : ℕ,
      Real.log ((ν x (shape (Aiter t A n) (Uminus t) x)).toReal)
        = Real.log ((ν (aIter t n x) (shape A (Uminus t) (aIter t n x))).toReal)
          + ∑ i ∈ Finset.range n, growthFun (Uminus t) ν t (aIter t (i+1) x) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hGae] with x hx
    exact iterate_log_pointwise t hL hU hcov hplq hx n
  filter_upwards [hGae, hAtomAe, hIterAe] with x hxG hAtom hIter
  intro n
  change (∑ i ∈ Finset.range n, atomInfo A (Uminus t) ν t (aIter t i x))
      = Real.log ((ν x (shape (Aiter t A n) (Uminus t) x)).toReal)
        - Real.log ((ν x (shape A (Uminus t) x)).toReal)
  -- telescoping of the pointwise identities
  have hsplit : (∑ i ∈ Finset.range n, atomInfo A (Uminus t) ν t (aIter t i x))
      = (∑ i ∈ Finset.range n,
          (Real.log ((ν (aIter t (i+1) x) (shape A (Uminus t) (aIter t (i+1) x))).toReal)
            - Real.log ((ν (aIter t i x) (shape A (Uminus t) (aIter t i x))).toReal)))
        + ∑ i ∈ Finset.range n, growthFun (Uminus t) ν t (aIter t (i+1) x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hAtom i])
  have htel := Finset.sum_range_sub
    (fun i : ℕ => Real.log ((ν (aIter t i x) (shape A (Uminus t) (aIter t i x))).toReal)) n
  simp only [aIter_zero] at htel
  rw [hsplit, htel]
  rw [hIter n]
  ring

end Work.EKLC6Core

end
