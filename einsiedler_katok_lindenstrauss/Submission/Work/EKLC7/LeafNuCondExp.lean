import Mathlib
import Submission.Work.EKLC7.LeafNuMaster

/-!
# `Work.EKLC7.LeafNuCondExp` — the `condexp` field (Pisa 6.3(iv))

For an arbitrary plaque algebra `(Z, m)` the conditional measure of `μ|Z` w.r.t. `m` is the
leafwise measure transported along the orbit map, normalised on the atom: this is the patching
identity `raw_eq_ratio` read at the *shape* of `(Z, m)`, combined with the proportionality of
Pisa 5.17.  This is the clause `IsLeafwise.condexp`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-! ## Support and transport for a fixed flower index -/

theorem kappa_compl_atom (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (j : ℕ) (hxZ : x ∈ F.Z j) :
    F.kappa j x (atom (F.m j) x)ᶜ = 0 := by
  have h1 : F.kappa j x (atom (F.m j) x) = 1 := h.atom_one j x hx hxZ
  have h2 : F.kappa j x Set.univ = 1 := by
    simp only [kappa]
    exact measure_univ
  rw [MeasureTheory.measure_compl (F.atom_meas j x) (by rw [h1]; exact ENNReal.one_ne_top),
    h2, h1, tsub_self]

theorem kappa_congr (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (j : ℕ) (hxZ : x ∈ F.Z j) {s t : Set X3}
    (h1 : s ⊆ t ∪ (atom (F.m j) x)ᶜ) (h2 : t ⊆ s ∪ (atom (F.m j) x)ᶜ) :
    F.kappa j x s = F.kappa j x t := by
  refine le_antisymm ?_ ?_
  · calc F.kappa j x s ≤ F.kappa j x (t ∪ (atom (F.m j) x)ᶜ) := measure_mono h1
      _ ≤ F.kappa j x t + F.kappa j x ((atom (F.m j) x)ᶜ) := measure_union_le _ _
      _ = F.kappa j x t := by rw [F.kappa_compl_atom h hx j hxZ, add_zero]
  · calc F.kappa j x t ≤ F.kappa j x (s ∪ (atom (F.m j) x)ᶜ) := measure_mono h2
      _ ≤ F.kappa j x s + F.kappa j x ((atom (F.m j) x)ᶜ) := measure_union_le _ _
      _ = F.kappa j x s := by rw [F.kappa_compl_atom h hx j hxZ, add_zero]

/-- **Transport identity for a fixed flower**: `(κ_j x) (D • x) = ((κ_j x).map (coord x)) D`. -/
theorem kappa_map_apply (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    {x : X3}
    (hcoord : ∀ y ∈ (fun u : SL3 => u • x) '' (U : Set SL3),
      coord x y ∈ U ∧ coord x y • x = y)
    (hx : x ∈ X') (j : ℕ) (hxZ : x ∈ F.Z j) {D : Set SL3} (hD : MeasurableSet D)
    (hDU : D ⊆ (U : Set SL3)) :
    F.kappa j x ((fun u : SL3 => u • x) '' D) = (F.kappa j x).map (coord x) D := by
  have hfix := h.free x hx
  have hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := free_of_fix hfix
  have hm : Measurable (fun y => coord x y) :=
    hcoordm.comp (measurable_const.prodMk measurable_id)
  have hatom : atom (F.m j) x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
    F.atom_subset_orbit j hxZ
  have hone : (F.kappa j x).map (coord x) D = F.kappa j x ((coord x) ⁻¹' D) :=
    Measure.map_apply hm hD
  have hkey : F.kappa j x ((coord x) ⁻¹' D)
      = F.kappa j x ((fun u : SL3 => u • x) '' D) := by
    refine F.kappa_congr h hx j hxZ ?_ ?_
    · intro y hy
      by_cases ha : y ∈ atom (F.m j) x
      · obtain ⟨v, hv, hvy⟩ := hatom ha
        have hcv : coord x y = v := coord_eq_of_mem coord hcoord hfix hv hvy ⟨v, hv, hvy⟩
        have hyD : coord x y ∈ D := hy
        have himg : y ∈ (fun u : SL3 => u • x) '' D := by
          refine ⟨coord x y, hyD, ?_⟩
          exact (hcoord y ⟨v, hv, hvy⟩).2
        exact Set.mem_union_left _ himg
      · exact Set.mem_union_right _ ha
    · rintro y ⟨u, huD, rfl⟩
      by_cases ha : u • x ∈ atom (F.m j) x
      · obtain ⟨v, hv, hvy⟩ := hatom ha
        have hcu : coord x (u • x) = u :=
          coord_eq_of_mem coord hcoord hfix (hDU huD) rfl ⟨v, hv, hvy⟩
        have hmem : (fun u : SL3 => u • x) u ∈ (coord x) ⁻¹' D := by
          show coord x (u • x) ∈ D
          rw [hcu]; exact huD
        exact Set.mem_union_left _ hmem
      · exact Set.mem_union_right _ ha
  rw [hone, hkey]

/-- **The restriction of `ν x` to the shape of a plaque algebra** is the push-forward of the
conditional measure of the reference flower. -/
theorem nu_restrict_shape (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (coord : X3 → X3 → SL3) (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
      y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set X3} (hX' : F.Good X') {x : X3} (hx : x ∈ X')
    (𝔪 : SigAlg) {Z : Set X3} (hplaq : IsPlaqueAlgebra U Z 𝔪.m) (hxZ : x ∈ Z)
    (j : ℕ) (hxj : x ∈ F.E j) (hRj : 2 ≤ F.R j)
    (hshape : (fun u : SL3 => u • x) '' shape 𝔪.m U x ⊆ atom (F.m j) x)
    (hproper : ∀ n : ℕ, ProporOn (F.kap n x) (F.kappa j x)
      (atom (F.m (F.chose n x)) x ∩ atom (F.m j) x)) :
    (F.nu coord X' x).restrict (shape 𝔪.m U x)
      = (F.ddAt j x)⁻¹ • ((F.kappa j x).map (coord x)).restrict (shape 𝔪.m U x) := by
  have hxjZ : x ∈ F.Z j := (F.big j).2.1 hxj
  have hcoordx := coord_at F hU coord hcoordm hcsub hX' hx
  have hcl : IsClosed (U : Set SL3) := hU.1
  have hshapemeas : MeasurableSet (shape 𝔪.m U x) := by
    obtain ⟨O, hO, hOeq⟩ := (hplaq.2.2.2 x hxZ).2.2.1
    rw [hOeq]
    exact hO.measurableSet.inter hcl.measurableSet
  have hBsub : (fun g : SL3 => g • x) '' Box1 U ⊆ atom (F.m j) x :=
    Set.Subset.trans (Set.image_mono (fun g hg => Ucl_subset_Uball (by norm_num) hg))
      (Set.Subset.trans (Upla_mono hRj x) ((F.big j).2.2 x hxj))
  rw [F.nu_of_mem hx]
  refine Measure.ext fun D hD => ?_
  rw [Measure.restrict_apply hD, Measure.smul_apply, Measure.restrict_apply hD]
  have hDsub : D ∩ shape 𝔪.m U x ⊆ (U : Set SL3) := fun y hy => hy.2.1
  have hDmeas : MeasurableSet (D ∩ shape 𝔪.m U x) := hD.inter hshapemeas
  have hDsub_atom : (fun g : SL3 => g • x) '' (D ∩ shape 𝔪.m U x) ⊆ atom (F.m j) x :=
    Set.Subset.trans (Set.image_mono Set.inter_subset_right) hshape
  rw [raw_eq_ratio F hU coord hcoordm hcsub hX' hx ⟨F.m j⟩ (F.big j).1 hxjZ hBsub hproper
    hDmeas hDsub hDsub_atom]
  have hnum : F.kappa j x ((fun u : SL3 => u • x) '' (D ∩ shape 𝔪.m U x))
      = ((F.kappa j x).map (coord x)) (D ∩ shape 𝔪.m U x) :=
    F.kappa_map_apply hX' coord hcoordm hcoordx hx j hxjZ hDmeas hDsub
  show F.kappa j x ((fun g : SL3 => g • x) '' (D ∩ shape 𝔪.m U x))
      * (F.kappa j x ((fun g : SL3 => g • x) '' Box1 U))⁻¹
      = (F.ddAt j x)⁻¹ • (Measure.map (coord x) (F.kappa j x)) (D ∩ shape 𝔪.m U x)
  rw [hnum, smul_eq_mul,
    show F.ddAt j x = F.kappa j x ((fun g : SL3 => g • x) '' Box1 U) from rfl, mul_comm]

end Work.EKLC7.FlowerFam

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- The atom of a plaque algebra is the plaque of its shape. -/
theorem atom_eq_shape_smul {Z : Set X3} {𝔪 : SigAlg} (hplaq : IsPlaqueAlgebra U Z 𝔪.m)
    {x : X3} (hxZ : x ∈ Z) :
    atom 𝔪.m x = (fun u : SL3 => u • x) '' shape 𝔪.m U x := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := (hplaq.2.2.2 x hxZ).2.1 hy
    exact ⟨u, ⟨hu, hy⟩, rfl⟩
  · rintro y ⟨u, hu, rfl⟩
    exact hu.2

/-- **The `condexp` field (Pisa 6.3(iv))** for the patched family `ν = F.nu coord X'`. -/
theorem condexp_nu (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (hprop : ProporHyp U μ) (coord : X3 → X3 → SL3)
    (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
      y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set X3} (hX' : F.Good X') :
    ∀ (Z : Set X3) (𝔪 : SigAlg), IsPlaqueAlgebra U Z 𝔪.m →
      ∀ f : X3 → ℝ, Measurable f → (∃ C, ∀ y, |f y| ≤ C) →
      ∀ᵐ x ∂(μ.restrict Z), condExp 𝔪.m (μ.restrict Z) f x =
        (∫ u in shape 𝔪.m U x, f (u • x) ∂(F.nu coord X' x))
          / (F.nu coord X' x (shape 𝔪.m U x)).toReal := by
  intro Z 𝔪 hplaq f hf hC
  classical
  obtain ⟨C₀, hC₀⟩ := hC
  -- the a.e. inputs
  have hX'ae : ∀ᵐ x ∂(μ.restrict Z), x ∈ X' := by
    rw [MeasureTheory.ae_restrict_iff' (hplaq.1 Z hplaq.2.2.1)]
    filter_upwards [MeasureTheory.ae_iff.mpr hX'.null] with x hx _
    simpa using hx
  have hatomZ : ∀ᵐ x ∂(μ.restrict Z),
      ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x
        (atom 𝔪.m x) = 1 :=
    Work.EKLComp.condExpKernel_atom 𝔪 hplaq.1 hplaq.2.1 (μ.restrict Z)
  have hposZ : ∀ᵐ x ∂(μ.restrict Z), 0 < (ProbabilityTheory.condExpKernel
      (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
        ((fun g : SL3 => g • x) '' Uball U 1) := by
    have h := Work.EKLComp.condExpKernel_pos U hU.1 Z 𝔪 hplaq μ (UballOpen 1)
      (isOpen_UballOpen _) (one_mem_UballOpen (by norm_num))
    have hset : UballOpen (1:ℝ) ∩ (U : Set SL3) = Uball U 1 := by
      rw [Set.inter_comm, ← Uball_eq_inter]
    rwa [hset] at h
  have hpropZ : ∀ᵐ x ∂(μ.restrict Z),
      ∀ j : ℕ, x ∈ F.Z j → ProporOn (F.kappa j x)
        (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
        (atom (F.m j) x ∩ atom 𝔪.m x) := by
    have hall : ∀ᵐ x ∂μ, ∀ j : ℕ, x ∈ F.Z j → x ∈ Z → ProporOn (F.kappa j x)
        (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
        (atom (F.m j) x ∩ atom 𝔪.m x) := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      filter_upwards [hprop (F.Z j) Z ⟨F.m j⟩ 𝔪 (F.big j).1 hplaq] with x hx
      exact fun hxZj hxZ => hx ⟨hxZj, hxZ⟩
    rw [MeasureTheory.ae_restrict_iff' (hplaq.1 Z hplaq.2.2.1)]
    filter_upwards [hall] with x hx hxZ
    exact fun j hxZj => hx j hxZj hxZ
  have hcondExp := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
    (m := 𝔪.m) (μ := μ.restrict Z) hplaq.1
    ((MeasureTheory.integrable_const C₀).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hC₀))
  have hmemZ : ∀ᵐ x ∂(μ.restrict Z), x ∈ Z :=
    MeasureTheory.self_mem_ae_restrict (hplaq.1 Z hplaq.2.2.1)
  filter_upwards [hX'ae, hmemZ, hatomZ, hposZ, hpropZ, hcondExp] with x hxX' hxZ hatomx hposx hpropx
    hcex
  classical
  have hcoordx := coord_at F hU coord hcoordm hcsub hX' hxX'
  have hsubZx : atom 𝔪.m x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := (hplaq.2.2.2 x hxZ).2.1
  have hshapemeas : MeasurableSet (shape 𝔪.m U x) := by
    obtain ⟨O, hO, hOeq⟩ := (hplaq.2.2.2 x hxZ).2.2.1
    rw [hOeq]
    exact hO.measurableSet.inter hU.1.measurableSet
  have hAmeas : MeasurableSet (atom 𝔪.m x) :=
    Work.EKLComp.measurableSet_atom_of_countablyGen 𝔪 hplaq.1 hplaq.2.1 x
  -- the bound for the shape and the flower of large enough radius
  obtain ⟨Csh, hCsh⟩ := (hplaq.2.2.2 x hxZ).2.2.2
  have hshape_sub : shape 𝔪.m U x ⊆ Uball U (Csh + 2) := fun u hu => ⟨hu.1, fun i j => by
    have h1 := hCsh u hu i j
    have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> simp
    have h3 := abs_sub_le ((u : Matrix (Fin 3) (Fin 3) ℝ) i j) (0 : ℝ)
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
    rw [sub_zero, zero_sub, abs_neg] at h3
    linarith⟩
  set N : ℕ := Nat.ceil Csh + 1 with hN
  obtain ⟨j, hj⟩ := hX'.cover N x hxX'
  have hxj : x ∈ F.E j := hj.2
  have hRj : (N : ℝ) + 2 ≤ F.R j := hj.1
  have hxjZ : x ∈ F.Z j := (F.big j).2.1 hxj
  have hshapesub : shape 𝔪.m U x ⊆ Uball U (F.R j) := by
    refine Set.Subset.trans hshape_sub (Uball_mono ?_)
    have h1 : (Csh : ℝ) ≤ (Nat.ceil Csh : ℝ) := Nat.le_ceil Csh
    have h2 : ((N : ℕ) : ℝ) = (Nat.ceil Csh : ℝ) + 1 := by simp [hN]
    rw [h2] at hRj
    linarith
  have hshape : (fun u : SL3 => u • x) '' shape 𝔪.m U x ⊆ atom (F.m j) x :=
    Set.Subset.trans (Set.image_mono hshapesub)
      (Set.Subset.trans (Upla_mono le_rfl x) ((F.big j).2.2 x hxj))
  have hRj2 : 2 ≤ F.R j := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hproper : ∀ n : ℕ, ProporOn (F.kap n x) (F.kappa j x)
      (atom (F.m (F.chose n x)) x ∩ atom (F.m j) x) := by
    intro n
    rw [F.kap_eq_kappa]
    exact hX'.propor (F.chose n x) j x hxX' ⟨F.chose_mem_Z hX' hxX' n, hxjZ⟩
  have hsubA : atom 𝔪.m x ⊆ atom (F.m j) x := by
    rw [atom_eq_shape_smul hplaq hxZ]
    exact hshape
  -- the proportionality constant
  have hpropx' : ProporOn (F.kappa j x)
      (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x)
      (atom 𝔪.m x) := by
    have hI : atom (F.m j) x ∩ atom 𝔪.m x = atom 𝔪.m x := Set.inter_eq_right.mpr hsubA
    have h := hpropx j hxjZ
    rwa [hI] at h
  obtain ⟨lam, hlam0, hlamt, hlam⟩ := hpropx'
  have hkj_smul : (F.kappa j x).restrict (atom 𝔪.m x)
      = lam⁻¹ • (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
          (μ.restrict Z) 𝔪.m x).restrict (atom 𝔪.m x) := by
    rw [hlam, smul_smul, ENNReal.inv_mul_cancel hlam0 hlamt, one_smul]
  have hkjA : (F.kappa j x) (atom 𝔪.m x) = lam⁻¹ := by
    have := congrArg (fun ν : Measure X3 => ν (atom 𝔪.m x)) hkj_smul
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hAmeas,
      Set.inter_self, hatomx, mul_one] using this
  -- the shape's plaque is the atom
  have hatom_eq : (fun u : SL3 => u • x) '' shape 𝔪.m U x = atom 𝔪.m x :=
    (atom_eq_shape_smul hplaq hxZ).symm
  -- the restriction identity
  have hnu := F.nu_restrict_shape hU coord hcoordm hcsub hX' hxX' 𝔪 hplaq hxZ j hxj hRj2 hshape
    hproper
  -- the mass of the shape
  have hnu_shape : F.nu coord X' x (shape 𝔪.m U x) = (F.ddAt j x)⁻¹ * lam⁻¹ := by
    have h := congrArg (fun ν : Measure SL3 => ν (shape 𝔪.m U x)) hnu
    rw [Measure.restrict_apply hshapemeas, Set.inter_self, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hshapemeas, Set.inter_self,
      ← F.kappa_map_apply hX' coord hcoordm hcoordx hxX' j hxjZ hshapemeas (fun g hg => hg.1),
      hatom_eq, hkjA] at h
    exact h
  -- the support of the conditional measure of the flower
  have hsupp : ∀ᵐ y ∂(F.kappa j x), y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) := by
    rw [MeasureTheory.ae_iff]
    have h2 : (F.kappa j x) (((fun u : SL3 => u • x) '' (U : Set SL3))ᶜ) = 0 := by
      have h3 : (F.kappa j x) (((fun u : SL3 => u • x) '' (U : Set SL3))ᶜ)
          ≤ (F.kappa j x) ((atom (F.m j) x)ᶜ) :=
        measure_mono fun y hy hmem => hy (F.atom_subset_orbit j hxjZ hmem)
      rw [F.kappa_compl_atom hX' hxX' j hxjZ] at h3
      exact le_antisymm h3 bot_le
    rwa [show {y : X3 | ¬ y ∈ (fun u : SL3 => u • x) '' (U : Set SL3)}
        = (((fun u : SL3 => u • x) '' (U : Set SL3))ᶜ) from rfl]
  have hkZuniv : (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z)
      𝔪.m x) Set.univ = 1 := measure_univ
  have hrestrict : (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
      (μ.restrict Z) 𝔪.m x).restrict (atom 𝔪.m x)
      = ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x := by
    rw [MeasureTheory.Measure.restrict_congr_set (show (atom 𝔪.m x) =ᵐ[
      ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x] Set.univ
      from ?_), MeasureTheory.Measure.restrict_univ]
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [show (atom 𝔪.m x \ Set.univ) = (∅ : Set X3) from Set.diff_univ _, measure_empty]
    · rw [show (Set.univ \ atom 𝔪.m x) = (atom 𝔪.m x)ᶜ from (Set.compl_eq_univ_diff _).symm,
        MeasureTheory.measure_compl hAmeas (by rw [hatomx]; exact ENNReal.one_ne_top),
        hatomx, hkZuniv, tsub_self]
  have hmapmeas : Measurable (coord x) :=
    hcoordm.comp (measurable_const.prodMk measurable_id)
  -- the three steps of the integral computation
  have hInt1 : (∫ u in shape 𝔪.m U x, f (u • x) ∂(F.nu coord X' x))
      = (F.ddAt j x)⁻¹.toReal
        * ∫ u in shape 𝔪.m U x, f (u • x) ∂((F.kappa j x).map (coord x)) := by
    rw [hnu, MeasureTheory.integral_smul_measure, smul_eq_mul]
  have hgm : AEStronglyMeasurable
      (fun u : SL3 => (shape 𝔪.m U x).indicator (fun u : SL3 => f (u • x)) u)
      (Measure.map (coord x) (F.kappa j x)) :=
    (((hf.comp (by fun_prop : Continuous fun u : SL3 => u • x).measurable).indicator
      hshapemeas : Measurable
        (fun u : SL3 => (shape 𝔪.m U x).indicator (fun u : SL3 => f (u • x)) u))).aestronglyMeasurable
  have hInt2 : (∫ u in shape 𝔪.m U x, f (u • x) ∂((F.kappa j x).map (coord x)))
      = ∫ y, (atom 𝔪.m x).indicator f y ∂(F.kappa j x) := by
    rw [← MeasureTheory.integral_indicator hshapemeas,
      MeasureTheory.integral_map (φ := coord x)
        (f := fun u : SL3 => (shape 𝔪.m U x).indicator (fun u : SL3 => f (u • x)) u)
        hmapmeas.aemeasurable hgm]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hsupp] with y hy
    by_cases hyA : y ∈ atom 𝔪.m x
    · have hyshape : coord x y ∈ shape 𝔪.m U x :=
        ⟨(hcoordx y hy).1, by rw [(hcoordx y hy).2]; exact hyA⟩
      rw [Set.indicator_of_mem hyshape, Set.indicator_of_mem hyA]
      show f (coord x y • x) = f y
      rw [(hcoordx y hy).2]
    · have hnot : coord x y ∉ shape 𝔪.m U x := fun hmem =>
        hyA (by rw [← (hcoordx y hy).2]; exact hmem.2)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hyA]
  have hInt3 : (∫ y, (atom 𝔪.m x).indicator f y ∂(F.kappa j x))
      = lam⁻¹.toReal * ∫ y, f y ∂(ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
          (μ.restrict Z) 𝔪.m x) := by
    rw [MeasureTheory.integral_indicator hAmeas]
    rw [show (∫ y in atom 𝔪.m x, f y ∂(F.kappa j x))
        = ∫ y, f y ∂((F.kappa j x).restrict (atom 𝔪.m x)) from rfl]
    rw [hkj_smul, MeasureTheory.integral_smul_measure, smul_eq_mul]
    rw [show (∫ y in atom 𝔪.m x, f y ∂(ProbabilityTheory.condExpKernel
          (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x))
        = ∫ y, f y ∂((ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
            (μ.restrict Z) 𝔪.m x).restrict (atom 𝔪.m x)) from rfl, hrestrict]
  -- combine
  rw [hcex, hInt1, hInt2, hInt3, hnu_shape, ENNReal.toReal_mul]
  have hddt : F.ddAt j x ≠ ⊤ := by
    have h1 : F.kappa j x Set.univ = 1 := by simp only [kappa]; exact measure_univ
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_)
    rw [h1]; norm_num
  have hdd0 : F.ddAt j x ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (hX'.pos j x hxX' hxjZ 1 (by norm_num)) ?_)
    exact measure_mono (Set.image_mono (Uball_subset_Ucl U 1))
  have hcpos : 0 < (F.ddAt j x)⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hddt) (ENNReal.inv_ne_top.mpr hdd0)
  have hlpos : 0 < lam⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hlamt) (ENNReal.inv_ne_top.mpr hlam0)
  rw [show (F.ddAt j x)⁻¹.toReal
        * (lam⁻¹.toReal * ∫ y, f y ∂(ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
            (μ.restrict Z) 𝔪.m x))
      = (∫ y, f y ∂(ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
            (μ.restrict Z) 𝔪.m x)) * ((F.ddAt j x)⁻¹.toReal * lam⁻¹.toReal) from by ring,
    mul_div_cancel_right₀ _ (mul_ne_zero (ne_of_gt hcpos) (ne_of_gt hlpos))]

end Work.EKLC7.FlowerFam
