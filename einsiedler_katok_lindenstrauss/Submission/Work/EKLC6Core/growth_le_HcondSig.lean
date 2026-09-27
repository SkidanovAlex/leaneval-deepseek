import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLProd.plaque_shape_mass
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.growth_le_HcondSig` — the entropy contribution is bounded by the σ-algebra entropy

Target (Pisa 7.34/7.35/7.40, integrated form): for a leaf-wise system `ν = μ_x^U` of a
probability `μ`, an `a = aDiag t`-invariant measure, an `a`-descending plaque algebra `A`
whose atoms are `U`-plaques, and the contraction hypothesis on `U`,

`ofReal (∫ growthFun U ν t dμ) ≤ HcondSig μ A (comap a A)`,

which combined with `ent_ge_HcondSig` (`HcondSig μ A (comap a A) ≤ ent μ a`) yields the
requested `ofReal (∫ growthFun) ≤ ent μ (a ·)`.

## Structure of the argument (Pisa §7.34)

Write `V x := shape A U x` (the `U`-shape of the atom `[x]_A`) and
`W x := shape (comap a A) U x = a⁻¹ · V (a·x) · a` (the shape of the atom of `comap a A`,
`Work.EKLC6Core.shape_comap_eq` below).  The condexp field of `IsLeafwise` identifies the
conditional measure of `comap a A` with `ν x` restricted to `W x`, while the covariance of the
leaf-wise system (`covariant_step`) gives `ν x (W x) = ν (a·x) (V (a·x)) · ν (a·x) (conjBox U t)`.
Writing `ψ x := log (ν x (V x))`, this is the pointwise identity

`atomInfo x = ψ (a·x) - ψ x + growthFun U ν t (a·x)`      (Pisa 7.34)

where `atomInfo` is the surprisal `- log (ν x (V x) / ν x (W x))` of the `A`-atom under the
conditional measure of `comap a A`.  Birkhoff averaging this identity makes the `ψ`-coboundary
harmless (its Birkhoff averages are bounded by `2 ‖ψ‖_∞ / n`, so it has mean zero as soon as `ψ`
is essentially bounded), and one obtains `∫ atomInfo = ∫ growthFun U ν t`.

Two further pieces:

* the `σ`-algebra side `lintegral_atomInfo_le`: for the finite approximations `P_n` of `A`
  (with `partSigma P_n ≤ A`), the conditional entropy `Hcond μ P_n (comap a A)` is at least the
  integral of the surpise `- log μ_x^{comap a A}(P_n(x)) ≥ atomInfo x`, so that `HcondSig`
  (the supremum over such `P`) dominates `∫⁻ ofReal (atomInfo ·)`;
* `ofReal (∫ atomInfo) ≤ ∫⁻ ofReal (atomInfo ·)`, which together with `∫ atomInfo = ∫ growthFun`
  gives the claim.

This file contains only the *definitions* and the elementary σ-algebra/geometry bookkeeping;
the analytic pieces live in the sibling modules
`EKLC6Core.atomInfo_eq`, `EKLC6Core.lintegral_atomInfo_le`, `EKLC6Core.growth_le_atomInfo`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The information (in the sense of Shannon) of the `A`-atom `[x]_A` under the conditional
measure of `comap (aDiag t ·) A`, i.e. `- log (ν x (V x) / ν x (W x))` where `V x` is the
`U`-shape of the atom `[x]_A` and `W x = a⁻¹ · V (a·x) · a` the shape of the atom of
`comap (aDiag t ·) A`.  This is the pointwise summand in Pisa 7.34, whose Birkhoff average
converges to the entropy contribution `D_μ(a,U)`. -/
def atomInfo (A : MeasurableSpace X3) (U : Subgroup SL3)
    (ν : X3 → Measure SL3) (t : Fin 3 → ℝ) (x : X3) : ℝ :=
  - Real.log (((ν x (shape A U x)).toReal) /
             ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal))

variable {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
  {ν : X3 → Measure SL3} {X' X'' : Set X3} {t : Fin 3 → ℝ}

/-- The atom of the pull-back σ-algebra `comap f A` is the preimage of the atom of `A`:
`[x]_{f^{-1}A} = f^{-1}([f x]_A)`. -/
theorem atom_comap_HcondSig (f : X3 → X3) (A : MeasurableSpace X3) (x : X3) :
    atom (MeasurableSpace.comap f A) x = f ⁻¹' (atom A (f x)) := by
  ext y
  simp only [atom, Set.mem_preimage]
  constructor
  · intro hy s hs
    exact hy (f ⁻¹' s) ⟨by
      rw [MeasurableSpace.measurableSet_comap]; exact ⟨s, hs.1, rfl⟩, by simpa using hs.2⟩
  · intro hy s hs
    have hmeas : MeasurableSet[MeasurableSpace.comap f A] s := hs.1
    rw [MeasurableSpace.measurableSet_comap] at hmeas
    obtain ⟨t, ht, hts⟩ := hmeas
    have hfx : f x ∈ t := by simpa only [Set.mem_preimage, ← hts] using hs.2
    have hfy : f y ∈ t := hy t ⟨ht, hfx⟩
    simpa only [Set.mem_preimage, ← hts] using hfy

/-- `shape (comap (aDiag t ·) A) U x = conjBy (-t) (shape A U (aDiag t • x))`: the shape of the
atom of the pull-back σ-algebra is the conjugate of the shape at the shifted point. -/
theorem shape_comap_eq {A : MeasurableSpace X3} (hU : IsHoro U) (x : X3) :
    shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x =
      conjBy (-t) (shape A U (aDiag t • x)) := by
  have hnorm : ∀ s : Fin 3 → ℝ, ∀ u ∈ (U : Set SL3),
      aDiag s * u * (aDiag s)⁻¹ ∈ (U : Set SL3) := hU.2.1
  have hconj : ∀ (u : SL3) (y : X3),
      (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • y) = aDiag t • (u • y) := by
    intro u y
    rw [← mul_smul, show aDiag t * u * (aDiag t)⁻¹ * aDiag t = aDiag t * u from by group,
      ← mul_smul]
  ext u
  simp only [shape, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨huU, huA⟩
    have huA' : aDiag t • (u • x) ∈ atom A (aDiag t • x) := by
      rw [atom_comap_HcondSig] at huA; simpa using huA
    refine ⟨aDiag t * u * (aDiag t)⁻¹, ⟨hnorm t u huU, ?_⟩, ?_⟩
    · show (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x) ∈ atom A (aDiag t • x)
      rw [hconj]; exact huA'
    · rw [← aDiag_inv_eq_neg]; group
  · rintro ⟨g, ⟨hgU, hgA⟩, rfl⟩
    simp only []
    rw [aDiag_neg_eq_inv, inv_inv]
    have hmem' : (aDiag t)⁻¹ * g * aDiag t ∈ (U : Set SL3) := by
      have hmem : aDiag (-t) * g * (aDiag (-t))⁻¹ ∈ (U : Set SL3) := hnorm (-t) g hgU
      simpa only [aDiag_neg_eq_inv, inv_inv] using hmem
    refine ⟨hmem', ?_⟩
    rw [atom_comap_HcondSig]
    show aDiag t • (((aDiag t)⁻¹ * g * aDiag t) • x) ∈ atom A (aDiag t • x)
    have hval : aDiag t • (((aDiag t)⁻¹ * g * aDiag t) • x) = g • (aDiag t • x) := by
      rw [← mul_smul,
        show aDiag t * ((aDiag t)⁻¹ * g * aDiag t) = g * aDiag t from by group, ← mul_smul]
    rw [hval]
    exact hgA

end Work.EKLC6Core

end
