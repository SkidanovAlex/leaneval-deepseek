import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLRelCross.W.W_flower_local

/-!
# `Work.EKLRelCross.flower_family` — Pisa Corollary 6.15

For a horospherical subgroup `U ≤ SL₃(ℝ)` whose `U`-orbits are `μ`-a.e. free, and every `R > 0`,
there is a countable family of plaque algebras `(Z i, m i)` together with measurable bases
`G i ⊆ Z i`, such that on `G i` the shape contains the whole ambient ball `V R ∩ U` and the union
of the bases is conull.

The local geometric input (Pisa Proposition 6.7 + §6.9–6.12) is
`Work.EKLRelCross.W.W_flower_local`; the countable extraction is the standard
second-countable-basis argument (compare `Work.EKLC7.flowersAtRadius`).
-/

namespace Work.EKLRelCross

set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

theorem flower_family (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (R : ℝ) (hR : 0 < R) :
    ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set Work.EKLContract.X3)
      (mm : ι → MeasurableSpace Work.EKLContract.X3) (G : ι → Set Work.EKLContract.X3),
      (∀ i, Work.EKLContract.IsPlaqueAlgebra U (Z i) (mm i)) ∧
      (∀ i, MeasurableSet (G i)) ∧ (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)
        ⊆ Work.EKLContract.shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 := by
  classical
  -- a.e. pair-freeness of the `U`-orbits
  have hfree_ae : ∀ᵐ x ∂μ, ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
    filter_upwards [ae_free_orbit h2 μ U hU t0 ht0 hcontr] with x hx
    intro u₁ h₁ u₂ h₂ heq
    have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
    have h1 : u₂⁻¹ * u₁ = 1 := hx _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
    calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
      _ = u₂ := by rw [h1, mul_one]
  -- a.e. positivity of open neighbourhoods
  have hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s :=
    Work.EKLC7.ae_isOpen_pos (μ := μ)
  -- the set of "good" points
  let S : Set X3 := {x | (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) ∧
    (∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s)}
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hfree_ae, hpos] with x h1 h2
    exact ⟨h1, h2⟩
  -- the local flower at every good point
  have hloc : ∀ x : S, ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧
      @MeasurableSet X3 Work.EKLContract.instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      IsPlaqueAlgebra U Z m ∧ (x : X3) ∈ G ∧
      O ∩ {y | ∀ u ∈ U, u • y = y → u = 1} ⊆ G ∧
      ∀ y ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U y := by
    intro x
    exact Work.EKLRelCross.W.W_flower_local h2 hU (x : X3) x.property.1 R hR
  choose Zfun mfun Gfun Ofun hOopen hxO hGmeas hGsub hplaq hxG hOG hshape using hloc
  -- a countable basis of `X₃`
  haveI : SecondCountableTopology X3 := Work.EKLC7.X3_secondCountable
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  -- index the flowers by basis elements lying inside the neighbourhood of a good point
  let ι : Type := {n : ℕ // ∃ s : S, basis n ⊆ Ofun s}
  let sf : ι → S := fun i => Classical.choose i.property
  have hsf : ∀ i : ι, basis i.1 ⊆ Ofun (sf i) := fun i => Classical.choose_spec i.property
  haveI : Countable ι := inferInstance
  refine ⟨ι, inferInstance, fun i => Zfun (sf i), fun i => mfun (sf i), fun i => Gfun (sf i),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact hplaq (sf i)
  · intro i; exact hGmeas (sf i)
  · intro i; exact hGsub (sf i)
  · intro i x hx; exact hshape (sf i) x hx
  · -- the bases cover almost every point
    have hcover : ∀ᵐ y ∂μ, y ∈ ⋃ i : ι, Gfun (sf i) := by
      filter_upwards [hSae] with y hyS
      have hyO : y ∈ Ofun ⟨y, hyS⟩ := hxO ⟨y, hyS⟩
      have hyF : y ∈ {z : X3 | ∀ u ∈ U, u • z = z → u = 1} :=
        fun u hu hux => hyS.1 u hu 1 U.one_mem (by rw [hux, one_smul])
      obtain ⟨t, htB, hyt, hts⟩ :=
        hbas.exists_subset_of_mem_open hyO (hOopen ⟨y, hyS⟩)
      obtain ⟨n, rfl⟩ := htB
      let i : ι := ⟨n, ⟨⟨y, hyS⟩, hts⟩⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      exact hOG (sf i) (Set.mem_inter ((hsf i) hyt) hyF)
    have h2' := MeasureTheory.ae_iff.mp hcover
    have hEq : (⋃ i : ι, Gfun (sf i))ᶜ = {y : X3 | ¬ y ∈ ⋃ i : ι, Gfun (sf i)} := rfl
    rw [hEq]
    exact h2'

end Work.EKLRelCross
