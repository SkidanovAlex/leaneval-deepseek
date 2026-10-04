/-
# Cutting a DeTurck nonlinearity off away from the singular set

The flat DeTurck nonlinearity `Φ` (a quasilinear parabolic operator) is smooth only on the set
`{det (reMat A) ≠ 0}` where the metric matrix is invertible: Mathlib's matrix inverse is
Cramer's rule `(det A)⁻¹ • A.adjugate`, hence discontinuous at singular matrices with nonvanishing
adjugate, so *no* smooth extension of `secOpFlat` to all matrices exists.  Every analytic argument
below (Galerkin approximation, energy estimates, Grönwall) however needs a *globally* smooth
nonlinearity.

The remedy is the standard one: multiply `Φ` by a smooth cutoff `χ` whose closed support lies in
the nondegenerate set.  The product `(χ ∘ snd) • Φ` is then smooth *everywhere*:

* where `χ` is nonzero the point already lies in the set on which `Φ` is smooth (so `Φ` is
  `ContDiffAt` there, by openness of `{det ≠ 0}`), and `χ` is smooth; the product of two smooth
  maps is smooth;
* where `χ` vanishes the product is *identically* zero on a whole neighbourhood of the point
  (`tsupport χ` is closed), hence smooth as a constant function.

This file proves exactly that (`cutoff_mul_contDiff`), together with the openness of the
nondegenerate set.
-/

import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter

namespace Work.Diff.STE.flat

/-- The set of jets whose value has invertible real part is open: it is the preimage of
`{x : ℝ | x ≠ 0}` under the continuous map `w ↦ (reMat w.1).det`. -/
lemma isOpen_det_reMat_ne_zero (n : ℕ) :
    IsOpen {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := by
  have hcont : Continuous fun w : Work.Diff.STE.Flat.Jet n =>
      (Work.Diff.STE.Flat.reMat w.1).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Complex.continuous_re.comp
      (((continuous_apply j).comp (continuous_apply i)).comp
        (continuous_fst (X := Work.Diff.STE.Flat.MatC n)))
  exact (isOpen_ne (x := (0 : ℝ))).preimage hcont

theorem cutoff_mul_contDiff (n : ℕ)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (χ : Work.Diff.STE.Flat.Jet n → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ0 : tsupport χ ⊆ {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n => (χ p.2 : ℂ) • Φ p) := by
  have hSopen : IsOpen {w : Work.Diff.STE.Flat.Jet n |
      (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := isOpen_det_reMat_ne_zero n
  -- the scalar factor `p ↦ (χ p.2 : ℂ)` is smooth (it is `χ` composed with the projection and
  -- the inclusion `ℝ ↪ ℂ`)
  have hχc : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n => (χ p.2 : ℂ)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n => p.2) :=
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Work.Diff.STE.Flat.Jet n)).contDiff
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp h1)
  -- smoothness is local
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 ∈ tsupport χ
  · -- `χ` is nonzero here, so the point is in the nondegenerate set, where `Φ` is smooth
    have hpS : p.2 ∈ {w : Work.Diff.STE.Flat.Jet n |
        (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := hχ0 hp
    have hmem : Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n |
        (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} ∈ nhds p :=
      (IsOpen.prod isOpen_univ hSopen).mem_nhds ⟨trivial, hpS⟩
    exact hχc.contDiffAt.smul (hΦ.contDiffAt hmem)
  · -- `χ` vanishes on the whole (open) complement of `tsupport χ`, so the product is locally `0`
    have hev : (fun _ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n =>
          (0 : Work.Diff.STE.Flat.MatC n))
        =ᶠ[nhds p]
        (fun q : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n => (χ q.2 : ℂ) • Φ q) := by
      have hmemU : Set.univ ×ˢ (tsupport χ)ᶜ ∈ nhds p :=
        (IsOpen.prod isOpen_univ (isClosed_tsupport χ).isOpen_compl).mem_nhds ⟨trivial, hp⟩
      refine Filter.eventually_of_mem hmemU ?_
      intro q hq
      have hq' : q.2 ∉ tsupport χ := hq.2
      have hz : χ q.2 = 0 :=
        Function.notMem_support.mp (fun h => hq' (subset_closure h))
      simp [hz]
    exact (contDiffAt_const (c := (0 : Work.Diff.STE.Flat.MatC n))).congr_of_eventuallyEq hev.symm

end Work.Diff.STE.flat
