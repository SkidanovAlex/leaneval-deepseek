import Mathlib
import Submission.Work.Drive.endTripleRegOfMeet3

/-!
# The box-restricted class-level regularity of the ends clause

The design's class-level end data (`Work.Drive.PairReg`, `Work.Drive.EndTripleReg`,
`Drive/encodedEndData.lean`) are quantified over **all** of `ℝ²`, while the producers available from
the sweeps' `Meet3Hyp` (`Drive/endTripleRegOfMeet3.lean`) supply them on the **closed unit square**
(the counting engine's triple points never leave the box).  This file gives the box-restricted
notions a name, so that the consumers can switch by changing one definition rather than seven
hypothesis lists:

* `BoxPairReg A B` — the spanning condition at common values, for parameters in the square;
* `BoxEndTripleReg F A B` — the `EndTripleReg` conjunction at common values, for parameters in the
  square;
* `BoxEndTripleReg_of_meet3Hyp_sweeps` — the producer (row 1 *and* row 2 of the lead's §3 table);
* `endTripleReg_of_boxEndTripleReg` — the passage back to the *unrestricted* `EndTripleReg` at the
  price of the box-residency hypothesis on the common-value triples.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartB :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-- The three plane parameters of a common-value triple all lie in the closed unit square. -/
def BoxPt (y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ k : Fin 3, (![y₀, y₁, y₂] : Fin 3 → EuclideanSpace ℝ (Fin 2)) k ∈ Submission.Drive.unitBox 1

/-- **The box-restricted pair regularity**: the spanning condition of two class `2`-planes at common
values, for plane parameters in the closed unit square. -/
def BoxPairReg (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) : Prop :=
  ∀ y y' : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 →
    y' ∈ Submission.Drive.unitBox 1 → A y = B y' →
    (mfderiv (𝓡 2) (𝓡 3) A y).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B y').range = ⊤

/-- **The box-restricted end-triple regularity**: the `EndTripleReg` conjunction at common values, for
plane parameters in the closed unit square. -/
def BoxEndTripleReg (F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) : Prop :=
  ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2), BoxPt y₀ y₁ y₂ → F y₀ = A y₁ → F y₀ = B y₂ →
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) F y₀) ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) A y₁) ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) B y₂) ∧
    (mfderiv (𝓡 2) (𝓡 3) F y₀).range ⊓ (mfderiv (𝓡 2) (𝓡 3) A y₁).range ⊓
      (mfderiv (𝓡 2) (𝓡 3) B y₂).range = ⊥

/-- **The producer of the box-restricted end-triple data** (rows 1 and 2 of the lead's §3 table):
from the sweeps' `Meet3Hyp` and the level bound, at every common-class triple in the square. -/
theorem BoxEndTripleReg_of_meet3Hyp_sweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k))) :
    BoxEndTripleReg (Work.Drive.planeClassMap (P 0)) (Work.Drive.planeClassMap (P 1))
      (Work.Drive.planeClassMap (P 2)) := by
  intro y₀ y₁ y₂ hbox h01 h02
  have hcc : Work.Drive.CommonClass P ![y₀, y₁, y₂] := by
    intro k
    fin_cases k
    · rfl
    · simpa using h01.symm
    · simpa using h02.symm
  have h := endTripleReg_of_meet3Hyp_sweeps c ψ P hψ hP hcpos hc10 hc20 hψ0 hψ1 hcont hanti hlev
    hmeet ![y₀, y₁, y₂] (by simpa [BoxPt] using hbox) hcc
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **From the box-restricted data to the unrestricted `EndTripleReg`**, at the price of the
box-residency of every common-value triple. -/
theorem endTripleReg_of_boxEndTripleReg
    {F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : BoxEndTripleReg F A B)
    (hbox : ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2), F y₀ = A y₁ → F y₀ = B y₂ → BoxPt y₀ y₁ y₂) :
    Work.Drive.EndTripleReg F A B :=
  fun y₀ y₁ y₂ h01 h02 => h y₀ y₁ y₂ (hbox y₀ y₁ y₂ h01 h02) h01 h02

end

end Work.Drive
