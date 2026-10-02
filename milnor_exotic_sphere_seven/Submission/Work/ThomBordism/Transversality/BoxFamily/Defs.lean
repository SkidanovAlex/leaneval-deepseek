import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The box family of a submersion point: definitions

This file collects the *data* used to build, at a point `y₀ : X.E` where the vertical coordinate
`Φ : E → ℝ^k` of a `CoreTarget n k` is a submersion, the local family

`Ψ : E → ℝ^k → E`,  `Ψ y t` with `Φ (Ψ y t) = Φ y + t` and `Ψ y 0 = y`

(`Work.ThomBordism.Transversality.TransversalApproximation.exists_boxFamily`, step 2 of the
transversality homotopy theorem).

The construction is the submersion normal form of `Manifold.IsSubmersionAtOfComplement`: for a
submersion `Φ` at `y₀` there are charts `domChart` (on `E`) and `codChart` (on `ℝ^k`) and a linear
equivalence `equiv : ℝ^n ≃L ℝ^k × F` such that

`(codChart.extend 𝓡k) (Φ ((domChart.extend 𝓡n).symm x)) = (equiv x).1`  for `x` in the target of
`domChart.extend 𝓡n`  (`IsSubmersionAtOfComplement.writtenInCharts`).

The point of `E` with vertical coordinate `Φ y + s` is then obtained by keeping the second
`equiv`-coordinate `(equiv (domChart y)).2` of `y` and replacing the first by
`codChart (Φ y + s)`, i.e. by applying `(domChart.extend 𝓡n).symm` to

`boxCoord hF y s := equiv.symm (codChart (Φ y + s), (equiv (domChart y)).2)`.

**Everything in this file is stated for an explicit `hF : IsSubmersionAtOfComplement F 𝓡n 𝓡k ∞ Φ y₀`**
(the complement `F` and the charts come from `hF`); the module is deliberately free of any
`Classical.choose` of the submersion data, so that the statements are stable.

## Main definitions

* `boxCoord` — the model-space coordinate of `Ψ y s`;
* `box` — the point `Ψ y s = (domChart.extend 𝓡n).symm (boxCoord hF y s)`;
* `boxSet` — the set of pairs `(y, s)` on which the construction is *valid*: `y` in the source of
  `domChart`, `Φ y + s` in the source of `codChart`, and `boxCoord hF y s` in the target of
  `domChart.extend 𝓡n`.  On `boxSet` the exact identity `Φ (box hF y s) = Φ y + s` holds.

## Main results (elementary, proved here)

* `boxSet_mem_iff` — the defining conditions of `boxSet`, unpacked;
* `boxSet_mem_domChart`, `boxSet_mem_codChart`, `boxSet_mem_target` — the three components;
* `extend_domChart_target`, `extend_domChart_symm`, `extend_domChart_coe`, and the `codChart`
  analogues: for the models `𝓡 n`, `𝓡 k` the extension of a chart is the chart itself, so all the
  statements about `IsSubmersionAtOfComplement.writtenInCharts` can be read in the plain charts.

The identity `Φ (box hF y s) = Φ y + s` on `boxSet` is `BoxFamily.box_Phi`; the smoothness of
`(y, s) ↦ box hF y s` on `boxSet` is `BoxFamily.contMDiffOn_box`.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.BoxFamily

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ}

/-- The model-space coordinate of the point with vertical coordinate `Φ y + s` in the normal form
of the submersion `Φ` at `y₀`. -/
def boxCoord {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (y : X.E) (s : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin n) :=
  hF.equiv.symm (hF.codChart (X.Φ y + s), (hF.equiv (hF.domChart y)).2)

/-- The point of `X.E` with vertical coordinate `Φ y + s`: the inverse of the domain chart applied
to `boxCoord hF y s`. -/
def box {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (y : X.E) (s : EuclideanSpace ℝ (Fin k)) : X.E :=
  (hF.domChart.extend (𝓡 n)).symm (boxCoord hF y s)

/-- The set of pairs `(y, s)` on which the box construction is valid. -/
def boxSet {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    Set (X.E × EuclideanSpace ℝ (Fin k)) :=
  {p | p.1 ∈ hF.domChart.source ∧ X.Φ p.1 + p.2 ∈ hF.codChart.source ∧
    boxCoord hF p.1 p.2 ∈ (hF.domChart.extend (𝓡 n)).target}

variable {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boxSet_mem_iff (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) {p : X.E × EuclideanSpace ℝ (Fin k)} :
    p ∈ boxSet hF ↔ p.1 ∈ hF.domChart.source ∧ X.Φ p.1 + p.2 ∈ hF.codChart.source ∧
      boxCoord hF p.1 p.2 ∈ (hF.domChart.extend (𝓡 n)).target :=
  Iff.rfl

theorem boxSet_mem_domChart (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) {p : X.E × EuclideanSpace ℝ (Fin k)}
    (hp : p ∈ boxSet hF) : p.1 ∈ hF.domChart.source := hp.1

theorem boxSet_mem_codChart (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) {p : X.E × EuclideanSpace ℝ (Fin k)}
    (hp : p ∈ boxSet hF) : X.Φ p.1 + p.2 ∈ hF.codChart.source := hp.2.1

theorem boxSet_mem_target (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) {p : X.E × EuclideanSpace ℝ (Fin k)}
    (hp : p ∈ boxSet hF) :
    boxCoord hF p.1 p.2 ∈ (hF.domChart.extend (𝓡 n)).target := hp.2.2

/-! ### The extended charts of the models `𝓡 n`, `𝓡 k` are the charts -/

theorem extend_domChart_target (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    (hF.domChart.extend (𝓡 n)).target = hF.domChart.target := by
  rw [OpenPartialHomeomorph.extend_target']
  simp

theorem extend_domChart_source (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    (hF.domChart.extend (𝓡 n)).source = hF.domChart.source :=
  OpenPartialHomeomorph.extend_source hF.domChart

theorem extend_domChart_coe (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ⇑(hF.domChart.extend (𝓡 n)) = ⇑hF.domChart := by
  rw [OpenPartialHomeomorph.extend_coe]
  ext x
  simp

theorem extend_domChart_symm (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ⇑(hF.domChart.extend (𝓡 n)).symm = ⇑hF.domChart.symm := by
  rw [OpenPartialHomeomorph.extend_coe_symm]
  ext x
  simp

theorem extend_codChart_coe (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k)
    ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ⇑(hF.codChart.extend (𝓡 k)) = ⇑hF.codChart := by
  rw [OpenPartialHomeomorph.extend_coe]
  ext x
  simp

end

end Work.ThomBordism.Transversality.BoxFamily
