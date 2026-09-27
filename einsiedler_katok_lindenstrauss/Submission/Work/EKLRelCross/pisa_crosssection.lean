import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLNonExc.DinjFacts
import Submission.Work.EKLRelCross.CrossSectionSetup
import Submission.Work.EKLRelCross.exists_shrink_nhds
import Submission.Work.EKLRelCross.exists_inj_nhds
import Submission.Work.EKLRelCross.exists_Ucl_bound
import Submission.Work.EKLProd.sl3EntryBox_compact

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- Monotonicity of the closed displacement balls. -/
theorem Ucl_mono {U : Subgroup SL3} {r r' : ℝ} (h : r ≤ r') : Ucl U r ⊆ Ucl U r' :=
  fun g hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

/-- A local cross-section of the `U`-flow on `X₃`, after Einsiedler–Lindenstrauss, *Diagonal actions on locally homogeneous spaces* (REFS/Pisa_EinsiedlerLindenstrauss.txt), Proposition 6.7 together with the construction of §6.9–6.12. For a closed subgroup `U ≤ SL₃(ℝ)`, a point `x₀` with free `U`-orbit and a scale `ρ > 2` there are a closed neighbourhood `E` of `x₀` and a Borel set `C ⊆ E` such that every `x ∈ E` is moved into `C` by a unique element of the closed unit displacement ball `Ucl U 1` of `U`, and such that inside the ball `Ucl U ρ` the set `C` meets each `U`-orbit at most once (i.e. if `c ∈ C` and `u ∈ Ucl U ρ` with `u • c ∈ C` then `u = 1`). A compatible metric on `X₃` may be introduced inside the proof by `letI := upgradeIsCompletelyMetrizable X₃` (the global `PolishSpace X₃` instance comes from `Work.EKLComp.LeafDefs`, imported by `LeafBasic`). Uniform local freeness and uniform injectivity on compacta are available as `Work.EKLComp.locallyFree_compacta` and `Work.EKLNonExc.compact_subset_Dinj` (`x ∈ Dinj δ` means the orbit map at `x` is injective on `V δ`); closedness of `U` makes the displacement balls `Ucl U ρ` compact, which is the compactness input of Pisa §6.8. -/
theorem pisa_crosssection {U : Subgroup Work.EKLContract.SL3} (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    (x₀ : Work.EKLContract.X3) {ρ : ℝ} (hρ : 2 < ρ)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) :
    ∃ (E C : Set Work.EKLContract.X3), IsClosed E ∧ x₀ ∈ interior E ∧ C ⊆ E ∧ MeasurableSet C ∧
      (∀ x ∈ E, ∃! t : Work.EKLContract.SL3, t ∈ Work.EKLRelCross.Ucl U 1 ∧ t • x ∈ C) ∧
      (∀ c ∈ C, ∀ u ∈ Work.EKLRelCross.Ucl U ρ, u • c ∈ C → u = 1) := by
  classical
  obtain ⟨R₀, hR₀inv, hR₀mul, hR₀mulinv⟩ := exists_Ucl_bound U
  set R : ℝ := max R₀ ρ with hRdef
  have hRρ : ρ ≤ R := le_max_right _ _
  have hRR₀ : R₀ ≤ R := le_max_left _ _
  have hRpos : 0 ≤ R := le_trans (by linarith : (0 : ℝ) ≤ ρ) hRρ
  have hR1 : (1 : ℝ) ≤ R := le_trans (by linarith : (1 : ℝ) ≤ ρ) hRρ
  obtain ⟨E₁, hE₁c, hE₁int, hshrink⟩ := exists_shrink_nhds hUcl x₀ hfree (R := R) hRpos
  obtain ⟨E₂, hE₂c, hE₂int, hinj₂⟩ := exists_inj_nhds hUcl x₀ hfree (R := R)
  set E : Set X3 := E₁ ∩ E₂ with hEdef
  have hEc : IsCompact E := hE₁c.inter hE₂c
  have hEint : x₀ ∈ interior E := by
    rw [hEdef, interior_inter]
    exact ⟨hE₁int, hE₂int⟩
  have hshrinkE : ∀ x ∈ E, ∀ x' ∈ E, ∀ u ∈ Ucl U R, ∀ u' ∈ Ucl U R, u • x = u' • x' →
      u' * u⁻¹ ∈ Ucl U 1 ∧ u⁻¹ * u' ∈ Ucl U 1 :=
    fun x hx x' hx' u hu u' hu' h => hshrink x hx.1 x' hx'.1 u hu u' hu' h
  have hinjE : ∀ x ∈ E, ∀ u ∈ Ucl U 1, ∀ u' ∈ Ucl U 1, u • x = u' • x → u = u' :=
    fun x hx u hu u' hu' h => hinj₂ x hx.2 u (Ucl_mono hR1 hu) u' (Ucl_mono hR1 hu') h
  have h1R : Ucl U 1 ⊆ Ucl U R := Ucl_mono hR1
  have hR₀R : Ucl U R₀ ⊆ Ucl U R := Ucl_mono hRR₀
  have hBc : IsCompact (Ucl U 1) := isCompact_Ucl hUcl 1
  have hAc : IsCompact (Ucl U R) := isCompact_Ucl hUcl R
  have h1Ucl1 : (1 : SL3) ∈ Ucl U 1 :=
    Uball_subset_Ucl U 1 (one_mem_Uball U (by norm_num))
  have hρR : ∀ g ∈ Ucl U ρ, g ∈ Ucl U R := Ucl_mono hRρ
  have hBinv : ∀ g ∈ Ucl U 1, g⁻¹ ∈ Ucl U R := fun g hg => hR₀R (hR₀inv g hg)
  have hBB : ∀ g ∈ Ucl U 1, ∀ g' ∈ Ucl U 1, g * g' ∈ Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mul g hg g' hg')
  have hBBinv : ∀ g ∈ Ucl U 1, ∀ g' ∈ Ucl U 1, g * g'⁻¹ ∈ Ucl U R :=
    fun g hg g' hg' => hR₀R (hR₀mulinv g hg g' hg')
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X3
  obtain ⟨C, hCE, hCmeas, huniq⟩ :=
    exists_borel_crossSection (B := Ucl U 1) (A := Ucl U R) (E := E)
      (d := TopologicalSpace.denseSeq X3) hEc (TopologicalSpace.denseRange_denseSeq X3)
      hBc hAc h1Ucl1 h1R hBinv hBB hBBinv hshrinkE hinjE
  refine ⟨E, C, hEc.isClosed, hEint, hCE, hCmeas, huniq, ?_⟩
  intro c hc u hu huc
  have hucE : u • c ∈ E := hCE huc
  have hcE : c ∈ E := hCE hc
  have huR : u ∈ Ucl U R := hρR u hu
  obtain ⟨hgen1, _⟩ := hshrink (u • c) hucE.1 c hcE.1 (1 : SL3)
    (h1R (Uball_subset_Ucl U 1 (one_mem_Uball U (by norm_num)))) u huR (by rw [one_smul])
  have hu1 : u ∈ Ucl U 1 := by simpa using hgen1
  obtain ⟨b, hb, huniqb⟩ := huniq c hcE
  rw [huniqb u ⟨hu1, huc⟩, huniqb 1 ⟨h1Ucl1, by rw [one_smul]; exact hc⟩]

end Work.EKLRelCross
