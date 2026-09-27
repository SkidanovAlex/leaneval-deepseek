import Mathlib
import Submission.Work.EKLC7.LeafNuFields
import Submission.Work.EKLC7.preimage_coord_eq_plaque

/-!
# `Work.EKLC7.LeafNuMaster` — the patching identity (Pisa 6.19a)

The heart of the construction: for a point `x` of the good set and *any* plaque algebra
`(Z, m)` whose atom at `x` contains the plaque of `Box1 U` and the plaque of `D`, the patched
measure is the normalised conditional measure transported along the orbit map:

`ν x (D) = μ^{A_m}_x (D • x) / μ^{A_m}_x (B₁ᵁ • x)`.

The proof evaluates the annulus sum defining `ν x` term by term and replaces the conditional
measure of each chosen flower by that of `(Z, m)` using the proportionality of Pisa 5.17.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- **The plaque of a Borel set of group elements is Borel** (for a point with free orbit): the
orbit map `U → X₃`, `u ↦ u • x` is a measurable embedding, as `U` is a closed subgroup of the
Polish group `SL₃(ℝ)`. -/
theorem measurableSet_pla (hcl : IsClosed (U : Set SL3)) {x : X3}
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) {D : Set SL3}
    (hD : MeasurableSet D) :
    MeasurableSet ((fun u : SL3 => u • x) '' (D ∩ (U : Set SL3))) := by
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hcl.polishSpace
  haveI : Nonempty U := ⟨⟨1, U.one_mem⟩⟩
  let ψ : U → X3 := fun u => (u : SL3) • x
  have hψcont : Continuous ψ := by fun_prop
  have hψinj : Function.Injective ψ := by
    intro u v huv
    have huv' : (u : SL3) • x = (v : SL3) • x := huv
    have h1 : ((v : SL3)⁻¹ * (u : SL3)) • x = x := by
      rw [mul_smul, huv', inv_smul_smul]
    have h2 : (v : SL3)⁻¹ * (u : SL3) = 1 :=
      hfree _ (U.mul_mem (U.inv_mem v.2) u.2) _ U.one_mem (by rw [h1, one_smul])
    exact Subtype.ext (by
      have := congrArg (fun t => (v : SL3) * t) h2
      simpa using this)
  have hME : MeasurableEmbedding ψ := Continuous.measurableEmbedding hψcont hψinj
  have hset : (fun u : SL3 => u • x) '' (D ∩ (U : Set SL3)) = ψ '' (Subtype.val ⁻¹' D) := by
    ext y
    constructor
    · rintro ⟨u, ⟨huD, huU⟩, rfl⟩
      exact ⟨⟨u, huU⟩, huD, rfl⟩
    · rintro ⟨u, huD, rfl⟩
      exact ⟨u, ⟨huD, u.2⟩, rfl⟩
  rw [hset]
  exact hME.measurableSet_image.mpr (hD.preimage measurable_subtype_coe)

end Work.EKLC7

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- **Ratio equality from proportionality** (Pisa 5.17): if two measures are proportional on `I`,
then the normalised ratio `κ E / κ B` agrees for the two, for `E, B ⊆ I`. -/
theorem div_eq_of_propor {κ κ' : Measure X3} {I E B : Set X3}
    (hI : MeasurableSet I) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hEI : E ⊆ I) (hBI : B ⊆ I) (hprop : ProporOn κ κ' I)
    (hB0 : κ B ≠ 0) (hBt : κ B ≠ ⊤) :
    κ E / κ B = κ' E / κ' B := by
  obtain ⟨c, hc0, hct, hceq⟩ := hprop
  have h1E : (κ.restrict I) E = κ E := by
    rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEI]
  have h2E : (κ'.restrict I) E = κ' E := by
    rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEI]
  have h1B : (κ.restrict I) B = κ B := by
    rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBI]
  have h2B : (κ'.restrict I) B = κ' B := by
    rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBI]
  have hEeq : κ' E = c * κ E := by
    calc κ' E = (κ'.restrict I) E := h2E.symm
      _ = (c • (κ.restrict I)) E := congrArg (fun ν : Measure X3 => ν E) hceq
      _ = c * ((κ.restrict I) E) := by rw [Measure.smul_apply, smul_eq_mul]
      _ = c * κ E := by rw [h1E]
  have hBeq : κ' B = c * κ B := by
    calc κ' B = (κ'.restrict I) B := h2B.symm
      _ = (c • (κ.restrict I)) B := congrArg (fun ν : Measure X3 => ν B) hceq
      _ = c * ((κ.restrict I) B) := by rw [Measure.smul_apply, smul_eq_mul]
      _ = c * κ B := by rw [h1B]
  rw [hEeq, hBeq]
  exact (ENNReal.mul_div_mul_left (κ E) (κ B) hc0 hct).symm

end Work.EKLC7.FlowerFam

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- **The patching identity (Pisa 6.19a)**.  For a point `x` of the good set and a plaque algebra
`(Z, m)` whose atom at `x` contains the plaque of `Box1 U` and the plaque of `D`, the patched
measure at `D` is the normalised conditional measure of `(Z, m)` of the plaque `D • x`. -/
theorem raw_eq_ratio (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
      y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set X3} (hX' : F.Good X') {x : X3} (hx : x ∈ X') {Z : Set X3}
    (𝔪 : SigAlg) (hplaq : IsPlaqueAlgebra U Z 𝔪.m) (hxZ : x ∈ Z)
    (hB : (fun g : SL3 => g • x) '' Box1 U ⊆ atom 𝔪.m x)
    (hprop : ∀ n : ℕ, ProporOn (F.kap n x)
      (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
      (atom (F.m (F.chose n x)) x ∩ atom 𝔪.m x))
    {D : Set SL3} (hD : MeasurableSet D) (hDU : D ⊆ U)
    (hDat : (fun g : SL3 => g • x) '' D ⊆ atom 𝔪.m x) :
    F.raw coord x D
      = (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
          ((fun g : SL3 => g • x) '' D)
        / (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
          ((fun g : SL3 => g • x) '' Box1 U) := by
  classical
  have hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := free_of_fix (hX'.free x hx)
  have hcoordx := coord_at F hU coord hcoordm hcsub hX' hx
  have hcl : IsClosed (U : Set SL3) := hU.1
  set kM : Measure X3 :=
    ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x with hkM
  have hBmeas : MeasurableSet ((fun g : SL3 => g • x) '' Box1 U) := by
    have h : Box1 U ∩ (U : Set SL3) = Box1 U := Set.inter_eq_left.mpr fun g hg => hg.1
    rw [← h]
    exact measurableSet_pla hcl hfree (measurableSet_Box1 hcl)
  have hEmeas : ∀ n : ℕ, MeasurableSet ((fun g : SL3 => g • x) '' (D ∩ Ann U n)) := by
    intro n
    have h : D ∩ Ann U n ∩ (U : Set SL3) = D ∩ Ann U n :=
      Set.inter_eq_left.mpr (Set.Subset.trans Set.inter_subset_right (Ann_subset_U U n))
    rw [← h]
    exact measurableSet_pla hcl hfree (hD.inter (measurableSet_Ann hcl n))
  have hImeas : ∀ n : ℕ, MeasurableSet (atom (F.m (F.chose n x)) x ∩ atom 𝔪.m x) := fun n =>
    (F.atom_meas _ x).inter
      (Work.EKLComp.measurableSet_atom_of_countablyGen 𝔪 hplaq.1 hplaq.2.1 x)
  have hEsubI : ∀ n : ℕ, (fun g : SL3 => g • x) '' (D ∩ Ann U n)
      ⊆ atom (F.m (F.chose n x)) x ∩ atom 𝔪.m x := by
    intro n y hy
    refine ⟨?_, ?_⟩
    · exact F.pla_pla_subset_atom hX' hx n (Set.image_mono
        (Set.Subset.trans Set.inter_subset_right (Ann_subset_Blk U n)) hy)
    · exact hDat (Set.image_mono Set.inter_subset_left hy)
  have hBsubI : ∀ n : ℕ, (fun g : SL3 => g • x) '' Box1 U
      ⊆ atom (F.m (F.chose n x)) x ∩ atom 𝔪.m x := by
    intro n y hy
    exact ⟨Set.Subset.trans (Set.image_mono (fun g hg => Ucl_subset_Uball (by norm_num) hg))
      (Set.Subset.trans (Upla_mono (F.chose_two_le hX' hx n) x)
        ((F.big _).2.2 x (F.chose_mem hX' hx n).1)) hy, hB hy⟩
  have hdd : ∀ n : ℕ, F.kap n x ((fun g : SL3 => g • x) '' Box1 U) = F.dd n x := fun n => rfl
  have hterm : ∀ n : ℕ, (F.trm coord n x) D
      = kM ((fun g : SL3 => g • x) '' (D ∩ Ann U n))
        / kM ((fun g : SL3 => g • x) '' Box1 U) := by
    intro n
    have h1 : (F.trm coord n x) D
        = (F.dd n x)⁻¹ * (F.prp coord n x) (D ∩ Ann U n) := by
      rw [trm, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hD]
    rw [h1, F.prp_apply hX' coord hcoordm hcoordx hx n (hD.inter (measurableSet_Ann hcl n))
      (Set.Subset.trans Set.inter_subset_right (Ann_subset_U U n))]
    have hdiv := div_eq_of_propor (κ := F.kap n x) (κ' := kM)
      (I := atom (F.m (F.chose n x)) x ∩ atom 𝔪.m x)
      (E := (fun g : SL3 => g • x) '' (D ∩ Ann U n))
      (B := (fun g : SL3 => g • x) '' Box1 U)
      (hImeas n) (hEmeas n) hBmeas (hEsubI n) (hBsubI n) (hprop n)
      (F.dd_ne_zero hX' hx n) (F.dd_ne_top hX' hx n)
    have hdd : F.dd n x = F.kap n x ((fun g : SL3 => g • x) '' Box1 U) := rfl
    rw [hdd, ← hdiv, ENNReal.div_eq_inv_mul]
  have hdisj : Pairwise fun n m : ℕ => Disjoint ((fun g : SL3 => g • x) '' (D ∩ Ann U n))
      ((fun g : SL3 => g • x) '' (D ∩ Ann U m)) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨u', hu', huu⟩ := hy'
    have huv : u = u' := hfree u (hDU hu.1) u' (hDU hu'.1) huu.symm
    subst huv
    exact (Set.disjoint_left.mp (Ann_pairwise U hnm) hu.2) hu'.2
  have hUnion : (⋃ n, (fun g : SL3 => g • x) '' (D ∩ Ann U n))
      = (fun g : SL3 => g • x) '' D := by
    have h1 : (⋃ n, D ∩ Ann U n) = D := by
      ext y
      constructor
      · intro hy
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
        exact hn.1
      · intro hy
        have hyU : y ∈ (U : Set SL3) := hDU hy
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (by rw [iUnion_Ann U]; exact hyU)
        exact Set.mem_iUnion.mpr ⟨n, ⟨hy, hn⟩⟩
    rw [← Set.image_iUnion, h1]
  have hsumraw : F.raw coord x D
      = ∑' n, kM ((fun g : SL3 => g • x) '' (D ∩ Ann U n))
        / kM ((fun g : SL3 => g • x) '' Box1 U) := by
    rw [raw, Measure.sum_apply _ hD]
    exact tsum_congr hterm
  rw [hsumraw]
  rw [show (∑' n, kM ((fun g : SL3 => g • x) '' (D ∩ Ann U n))
      / kM ((fun g : SL3 => g • x) '' Box1 U))
      = (∑' n, kM ((fun g : SL3 => g • x) '' (D ∩ Ann U n)))
        / kM ((fun g : SL3 => g • x) '' Box1 U) from by
    have h := ENNReal.tsum_mul_right
      (f := fun n => kM ((fun g : SL3 => g • x) '' (D ∩ Ann U n)))
      (a := (kM ((fun g : SL3 => g • x) '' Box1 U))⁻¹)
    simpa only [div_eq_mul_inv] using h]
  rw [← MeasureTheory.measure_iUnion (μ := kM) hdisj hEmeas]
  rw [hUnion]

end Work.EKLC7.FlowerFam
