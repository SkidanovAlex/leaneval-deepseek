import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotGroupsIntegrable_holds` — the integrability brick of the row split

`Work.BoseBoxFock.PotGroupsIntegrable` (`Submission/Work/BoseBoxFock/PotGroupDefs.lean`) asserts
that, at every admissible context of the row table, each of the four integrands

    x ↦ conj (boxRestrictC ℓ Φ x) · (Gᵢ (boxRestrictC ℓ Φ)) x      (i = 0,1,2,3)

is Bochner-integrable, where `G₀ = potContactChem`, `G₁ = potChiLin`, `G₂ = potPairRows`,
`G₃ = potCubic` are the four row groups of `AVgen (potOnlyEnv E)`.

## The proof

Each `Gᵢ` is built — by sums, real multiples, differences and compositions — from the atoms
`B T = boxSlotSum e T`, which preserve *good* states (measurable and everywhere bounded,
`Work.BoseBoxFock.GenLin_boxSlotSum_weak`).  Hence each `Gᵢ` preserves good states
(`GenLin_potContactChem`, `GenLin_potChiLin`, `GenLin_potPairRows`, `GenLin_potCubic` below, by the
closure lemmas `GenLin.addLin`/`subLin`/`smulLin`/`realSmulLin`/`compLin`/`sumLin`/`sumLin_univ`).

The state `Θ := boxRestrictC ℓ Φ` is good and supported in the box
(`Work.BoseBoxFock.boxRestrictState`), so `Gᵢ Θ` is good, and
`Work.BoseBoxFock.integrable_star_mul_of_box_support` gives the integrability of
`star Θ · Gᵢ Θ` — a bounded measurable function supported in the finite-measure box.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ} [NeZero m]
variable {ι : Type*}

/-! ## 1. `GenLin` for the four row groups

Each group is a nested combination (sums, real multiples, differences, compositions) of the atoms
`B T`; the closure lemmas of `GenLin` (`AVgen_add_I_smul.lean`) apply verbatim. -/

/-- **Group 0** — the contact + chemical group is `ℂ`-linear on good states. -/
theorem GenLin_potContactChem
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (hB : ∀ T, GenLin (B T))
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    GenLin (potContactChem B E gHat0) := by
  unfold potContactChem
  refine GenLin.subLin ?_ ?_ <;>
    apply GenLin.realSmulLin
  · apply GenLin.subLin
    · exact GenLin.compLin (hB _) (hB _)
    · exact hB _
  · exact hB _

/-- **Group 1** — the `chi`-linear group is `ℂ`-linear on good states. -/
theorem GenLin_potChiLin
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (hB : ∀ T, GenLin (B T))
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    GenLin (potChiLin B f g E) := by
  unfold potChiLin
  refine GenLin.addLin ?_ ?_
  · apply GenLin.sumLin_univ
    intro k
    apply GenLin.realSmulLin
    apply GenLin.addLin
    · apply GenLin.subLin
      · apply GenLin.realSmulLin
        exact GenLin.compLin (hB _) (hB _)
      · apply GenLin.realSmulLin
        exact hB _
    · apply GenLin.subLin
      · apply GenLin.realSmulLin
        exact GenLin.compLin (hB _) (hB _)
      · apply GenLin.realSmulLin
        exact hB _
  · apply GenLin.sumLin
    intro s
    apply GenLin.realSmulLin
    apply GenLin.addLin
    · apply GenLin.realSmulLin
      exact GenLin.compLin (hB _) (hB _)
    · apply GenLin.realSmulLin
      exact GenLin.compLin (hB _) (hB _)

/-- **Group 2** — the pair-row group is `ℂ`-linear on good states. -/
theorem GenLin_potPairRows
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (hB : ∀ T, GenLin (B T))
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    GenLin (potPairRows B f E) := by
  unfold potPairRows
  refine GenLin.addLin (GenLin.addLin ?_ ?_) ?_
  · apply GenLin.realSmulLin
    apply GenLin.sumLin_univ
    intro k
    apply GenLin.realSmulLin
    apply GenLin.subLin
    · exact GenLin.compLin (hB _) (hB _)
    · exact hB _
  · apply GenLin.realSmulLin
    apply GenLin.sumLin_univ
    intro k
    apply GenLin.realSmulLin
    apply GenLin.addLin
    · apply GenLin.subLin
      · exact GenLin.compLin (hB _) (hB _)
      · exact hB _
    · apply GenLin.subLin
      · exact GenLin.compLin (hB _) (hB _)
      · exact hB _
  · apply GenLin.sumLin_univ
    intro k
    apply GenLin.subLin
    · apply GenLin.realSmulLin
      exact GenLin.compLin (hB _) (hB _)
    · apply GenLin.realSmulLin
      exact hB _

/-- **Group 3** — the cubic group is `ℂ`-linear on good states. -/
theorem GenLin_potCubic
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ))
    (hB : ∀ T, GenLin (B T))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    GenLin (potCubic B f g PHs E) := by
  unfold potCubic
  apply GenLin.realSmulLin
  apply GenLin.sumLin
  intro s
  apply GenLin.sumLin
  intro k
  apply GenLin.realSmulLin
  apply GenLin.subLin
  · apply GenLin.addLin
    · apply GenLin.subLin
      · exact GenLin.compLin (hB _) (hB _)
      · exact hB _
    · exact GenLin.compLin (hB _) (hB _)
  · exact hB _

/-! ## 2. The integrability brick -/

theorem PotGroupsIntegrable_holds (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ) (ε₀ : ℝ) :
    Work.BoseBoxFock.PotGroupsIntegrable v h hav fc fu R J Nmin ε₀ := by
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom e h1m h2b h3s h4o h5i h6t h7θ h8q h9t h10θ
    T_NH hT
  -- the box side is positive, and the box restriction is a good, box-supported state
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hAdm.1 hav
  obtain ⟨hΘcm, hΘcb, hΘsupp, -, -⟩ := Work.BoseBoxFock.boxRestrictState hℓ Φ
  have hGoodΘ : SlotGood (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) :=
    ⟨hΘcm, hΘcb⟩
  -- the atoms `B T = boxSlotSum e T` are good-preserving
  have hB : ∀ T : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ),
      GenLin (fun Θ : Submission.BoseGases.X n → ℂ => Work.BoseDict.boxSlotSum e T Θ) :=
    fun T => Work.MB.GenLin_boxSlotSum_weak (d := n) h1m h2b h3s T
  -- the four row groups preserve good states
  have hR0 : RowGood (potContactChem (fun T => Work.BoseDict.boxSlotSum e T)
      (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)) :=
    (GenLin_potContactChem (fun T => Work.BoseDict.boxSlotSum e T) hB
      (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)).good
  have hR1 : RowGood (potChiLin (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
      (HonestBoxFam v h fc fu HM μ).E) :=
    (GenLin_potChiLin (fun T => Work.BoseDict.boxSlotSum e T) hB (HM μ).f (HM μ).g
      (HonestBoxFam v h fc fu HM μ).E).good
  have hR2 : RowGood (potPairRows (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f
      (HonestBoxFam v h fc fu HM μ).E) :=
    (GenLin_potPairRows (fun T => Work.BoseDict.boxSlotSum e T) hB (HM μ).f
      (HonestBoxFam v h fc fu HM μ).E).good
  have hR3 : RowGood (potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
      ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
      (HonestBoxFam v h fc fu HM μ).E) :=
    (GenLin_potCubic (fun T => Work.BoseDict.boxSlotSum e T) hB (HM μ).f (HM μ).g
      ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
      (HonestBoxFam v h fc fu HM μ).E).good
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hR0 _ hGoodΘ).1 (hR0 _ hGoodΘ).2
  · exact Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hR1 _ hGoodΘ).1 (hR1 _ hGoodΘ).2
  · exact Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hR2 _ hGoodΘ).1 (hR2 _ hGoodΘ).2
  · exact Work.BoseBoxFock.integrable_star_mul_of_box_support hΘcm hΘcb hΘsupp
      (hR3 _ hGoodΘ).1 (hR3 _ hGoodΘ).2

end Work.BoseBoxFock
