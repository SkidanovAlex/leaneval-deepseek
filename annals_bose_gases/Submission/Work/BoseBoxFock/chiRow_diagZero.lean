import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_diagZero`

The diagonal (squared) `χ`-row of the condensate projection `aP` vanishes against a
mean-zero test function: for `ℓ > 0`, a configuration space `X N = (ℝ³)^N`, a function
`Φ : X N → ℝ` and `w : ℝ³ → ℝ` with `∫_{Λ(ℓ)} w = 0`,

  `∫_{Λ(ℓ)^N} (aP ℓ i Φ x) * w (x i) * (aP ℓ i Φ x) dx = 0`.

The mathematical content is twofold:

* **`aP` does not depend on the `i`-th coordinate.**  `aP ℓ i Φ x = (ℓ³)⁻¹ ∫_{Λ(ℓ)} Φ(x[i ↦ y]) dy`
  depends on `x` only through the coordinates `j ≠ i` (`Work.BoseBoxFock.aP_update`).
* **The box measure is a product measure** (`Submission.BoseGases.restrict_abox_eq_pi`), so the
  integral of a function which is a product of a function of `x i` alone and a function of the
  remaining coordinates factorises, and the factor `∫_{Λ(ℓ)} w` vanishes.

The formal work is the second point: splitting `Measure.pi` along the `i`-th coordinate via
`MeasurableEquiv.piEquivPiSubtypeProd` (`MeasureTheory.measurePreserving_piEquivPiSubtypeProd`),
identifying the one-point factor with `volume.restrict (acube ℓ)` via
`MeasureTheory.measurePreserving_piUnique`, and Fubini for the product measure
(`MeasureTheory.integral_prod_mul`).  This is packaged in the general lemma
`Work.BoseBoxFock.piIntegral_factor_zero`, which is what the target reduces to.
-/

set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseBoxFock

/-- The condensate projection `aP ℓ i Φ` is invariant under changing the `i`-th coordinate:
`aP ℓ i Φ (x[i ↦ z]) = aP ℓ i Φ x`.  Indeed the mean of `y ↦ Φ (x[i ↦ y])` is unchanged. -/
lemma aP_update {N : ℕ} {ℓ : ℝ} (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.aP ℓ i Φ (Function.update x i z) = Submission.BoseGases.aP ℓ i Φ x := by
  simp only [Submission.BoseGases.aP, Function.update_idem]

/-- **Factorisation of a `Measure.pi` integral along one coordinate.**  Let `ι` be a finite type,
`i : ι`, `μ` a σ-finite measure on `α` and `G : (ι → α) → ℝ` a function which does not depend on
the `i`-th coordinate (`hG`).  Then for any `F : α → ℝ` with `∫ F ∂μ = 0`,

  `∫ x, G x * F (x i) ∂(Measure.pi (fun _ => μ)) = 0`.

This is the product-measure factorisation `∫ G(x_{≠i}) F(x_i) = (∫ F ∂μ) · (∫ G)` together with
`∫ F ∂μ = 0`. -/
lemma piIntegral_factor_zero {N : ℕ} (i : Fin N)
    (μz : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) [MeasureTheory.SigmaFinite μz]
    (F : EuclideanSpace ℝ (Fin 3) → ℝ) (G : Submission.BoseGases.X N → ℝ)
    (hG : ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
      G (Function.update x i z) = G x)
    (hF : ∫ z, F z ∂μz = 0) :
    (∫ x, G x * F (x i)
      ∂(MeasureTheory.Measure.pi (fun _ : Fin N => μz))) = 0 := by
  classical
  -- Pin the `Fintype` instance on the one-point subtype `{j // j = i}` to the one used by
  -- `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` (namely `Subtype.fintype`).
  letI : Fintype {j : Fin N // j = i} := Subtype.fintype (fun j => j = i)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => EuclideanSpace ℝ (Fin 3))
    (fun j => j = i)
  have hmp :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => μz) (fun j => j = i)
  -- Split `Measure.pi μz` as the product of the `i`-th coordinate and the remaining ones.
  have hsplit : ∫ x, G x * F (x i) ∂(MeasureTheory.Measure.pi (fun _ : Fin N => μz))
      = ∫ y, G (e.symm y) * F ((e.symm y) i)
          ∂((MeasureTheory.Measure.pi fun j : {j // j = i} => μz).prod
              (MeasureTheory.Measure.pi fun j : {j // ¬(j = i)} => μz)) := by
    simpa [e] using hmp.integral_comp' (fun y => G (e.symm y) * F ((e.symm y) i))
  rw [hsplit]
  -- Rewrite the integrand: `G` only sees the remaining coordinates, `F` only the `i`-th one.
  have hfac : (fun y : ((j : {j // j = i}) → EuclideanSpace ℝ (Fin 3)) ×
        ((j : {j // ¬(j = i)}) → EuclideanSpace ℝ (Fin 3)) =>
          G (e.symm y) * F ((e.symm y) i))
      = fun y => F (y.1 ⟨i, rfl⟩) * G (e.symm ((fun _ => 0), y.2)) := by
    funext y
    obtain ⟨u, r⟩ := y
    have hBi : (e.symm (u, r)) i = u ⟨i, rfl⟩ := by
      have h1 : e.symm (u, r) = (fun x => if h : (x = i) then u ⟨x, h⟩ else r ⟨x, h⟩) := by
        funext x
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      rw [h1]
      simp
    have hAi : G (e.symm (u, r)) = G (e.symm ((fun _ => 0), r)) := by
      have hupd : e.symm (u, r) =
          Function.update (e.symm ((fun _ => 0), r)) i (u ⟨i, rfl⟩) := by
        funext x
        by_cases hx : x = i
        · rw [hx, Function.update_self]; exact hBi
        · rw [Function.update_of_ne hx]
          congr 1
          have h1 : e.symm (u, r) = (fun x => if h : (x = i) then u ⟨x, h⟩ else r ⟨x, h⟩) := by
            funext x
            simp [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
          have h2 : e.symm ((fun _ => 0), r) =
              (fun x => if h : (x = i) then 0 else r ⟨x, h⟩) := by
            funext x
            simp [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
          rw [h1, h2]
          simp [hx]
      rw [hupd, hG]
    rw [hBi, hAi]
    ring
  rw [hfac]
  -- Fubini for the product measure.
  have hprod : (∫ y : ((j : {j // j = i}) → EuclideanSpace ℝ (Fin 3)) ×
        ((j : {j // ¬(j = i)}) → EuclideanSpace ℝ (Fin 3)),
        F (y.1 ⟨i, rfl⟩) * G (e.symm ((fun _ => 0), y.2))
        ∂((MeasureTheory.Measure.pi fun j : {j // j = i} => μz).prod
            (MeasureTheory.Measure.pi fun j : {j // ¬(j = i)} => μz)))
      = (∫ u, F (u ⟨i, rfl⟩) ∂(MeasureTheory.Measure.pi fun j : {j // j = i} => μz)) *
        (∫ r, G (e.symm ((fun _ => 0), r))
          ∂(MeasureTheory.Measure.pi fun j : {j // ¬(j = i)} => μz)) :=
    MeasureTheory.integral_prod_mul
      (fun u : ({j : Fin N // j = i} → EuclideanSpace ℝ (Fin 3)) => F (u ⟨i, rfl⟩))
      (fun r : ({j : Fin N // ¬(j = i)} → EuclideanSpace ℝ (Fin 3)) =>
        G (e.symm ((fun _ => 0), r)))
  rw [hprod]
  -- The one-point factor is just `μz`, so its integral of `F` is `∫ F ∂μz = 0`.
  have hF1 : (∫ u, F (u ⟨i, rfl⟩)
      ∂(MeasureTheory.Measure.pi fun j : {j // j = i} => μz)) = 0 := by
    have hpu := MeasureTheory.measurePreserving_piUnique (fun _ : {j // j = i} => μz)
    have hcomp := hpu.integral_comp' F
    simp only [MeasurableEquiv.piUnique_apply] at hcomp
    have hfn : (fun u : ({j // j = i} → EuclideanSpace ℝ (Fin 3)) => F (u ⟨i, rfl⟩))
        = fun u => F (u default) := by
      funext u
      have h : (⟨i, rfl⟩ : {j : Fin N // j = i}) = default := Subsingleton.elim _ _
      exact congrArg F (congr_arg u h)
    rw [hfn, hcomp, hF]
  rw [hF1, zero_mul]

theorem chiRow_diagZero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwc : Continuous w)
    (hmean : (∫ z in Submission.BoseGases.acube ℓ, w z) = 0) :
    (∫ x in Submission.BoseGases.abox N ℓ,
      (Submission.BoseGases.aP ℓ i Φ x) * w (x i) * (Submission.BoseGases.aP ℓ i Φ x)) = 0 := by
  classical
  -- `aP ℓ i Φ` depends only on the coordinates `j ≠ i`.
  have hG : ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
      (fun y : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i Φ y) ^ 2)
          (Function.update x i z)
        = (fun y : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i Φ y) ^ 2) x := by
    intro x z
    show (Submission.BoseGases.aP ℓ i Φ (Function.update x i z)) ^ 2
        = (Submission.BoseGases.aP ℓ i Φ x) ^ 2
    rw [aP_update]
  have hmain : (∫ y, (Submission.BoseGases.aP ℓ i Φ y) ^ 2 * w (y i)
      ∂(MeasureTheory.Measure.pi (fun _ : Fin N =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))) = 0 :=
    piIntegral_factor_zero i _ w (fun y => (Submission.BoseGases.aP ℓ i Φ y) ^ 2) hG hmean
  -- The box measure is the `N`-fold product of `volume ↾ acube ℓ` ...
  rw [Submission.BoseGases.restrict_abox_eq_pi N ℓ]
  -- ... and the integrand is `(aP)² · w`.
  rw [show (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ i Φ x) * w (x i) * (Submission.BoseGases.aP ℓ i Φ x))
      = (fun x => (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * w (x i)) from
        funext (fun x => by ring)]
  exact hmain

end Work.BoseBoxFock
