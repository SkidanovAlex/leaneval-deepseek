import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.plaque_algebra_exists
import Submission.Work.EKLRelCross.free_orbits_of_contracting
import Submission.Work.EKLRelCross.crossSection_trivial
import Submission.Work.EKLRelCross.leafwise_component
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLComp.prove_Leafwise
import Submission.Work.EKLComp.prove_Product
import Submission.Work.EKLRelCross.prod_hcb
import Submission.Work.EKLRelCross.hcb_side
import Submission.Work.EKLRelCross.carried_of_integral_eq

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is one component of the FROZEN EKL contract (Submission/Work/EKLContract/Defs.lean; the composition
ekl_of_components and the glue are PROVED, so proving all components closes the problem). Read first:
* Submission/Work/EKLPlan/ROUTE_LEAD.md: your component section, with its source (EKL / Pisa notes / Venkatesh), proof sketch and hardest step;
* EKLContract/NOTES.md (statement changes) and REPORT.md;
* REFS/ (EKL TeX, the Pisa notes, the feasibility audit).
Other components are available as hypotheses only where your Prop takes them. Do not assume anything else. Reuse
EKLContract/Lemmas/* and Mathlib. Parallelise: request independent pieces at once.

YOUR COMPONENT: C6b EKL Lemma 4.4(1), relative cross-section.

# Formalisation notes

EKL Lemma 4.4(1) (Annals 164 (2006)) reads: *under the assumptions of the low entropy case there is
a `μ`-null set `N` with `U_(ab) x ∩ (X ∖ N) ⊆ U_ab x` for `x ∉ N`*, where
`U_(ab) = ⟨U_ij : i = a or j = b⟩`.  Its proof (EKL, proof of Lemma 4.4) uses two inputs of the
contract:

* `P_Leafwise` (component C5): the leafwise measures `ν_x^{U}` along `U`-orbits, and EKL §2.1(3)
  (equivariance), which in the frozen interface is the field `IsLeafwise.equivariant`;
* `P_Product` (component C5b): Pisa 8.3, the product structure of the conditional measures.

Accordingly the component statement is `relCross_of : P_Leafwise → P_Product → P_RelCross` (the
signature recorded in `REPORT.md` §0 and `REVIEWS.md` for C6b); the frozen `P_RelCross` is the
conclusion shape.

The route implemented below, with `(H, T, W, A, B) = (U_(ab), U_cb, ⟨U_ab,U_ac⟩, U_ab, U_ac)`:

1. `hcb_side`/`prod_hcb` give `U_(ab) = U_cb · ⟨U_ab,U_ac⟩` with all the side conditions of
   `P_Product`, and `ab_ac_local` gives `⟨U_ab,U_ac⟩ = U_ab · U_ac` likewise;
2. `P_Leafwise` supplies the leafwise systems `νH, νT, νW, νA, νB`, and its clause (U3) turns the two
   cross-section hypotheses into `νB = δ₁` and `νT = δ₁` a.e.;
3. the two `P_Product` identities then collapse (Dirac inner integrals) to
   `∫ f dνH x = (c₁c₂)(x) ∫ f dνA x` for every test function `f`, and `carried_of_integral_eq`
   upgrades this to: `νH x` is carried by `U_ab`;
4. EKL's endgame: if `x, h·x` both lie in the conull set, equivariance gives
   `νH x = c • (νH (h·x)).map (· * h)` with `c ∈ (0,∞)`; both sides are carried by `U_ab`, resp. by
   `U_ab · h`, hence `U_ab ∩ U_ab h ≠ ∅` and `h ∈ U_ab`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLContract.Lemmas
open Work.EKLRelCross

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- The leafwise-measure system of `P_Leafwise` at an admissible subgroup `U`, together with the
clause (U3) that identifies `CrossSection` with trivial leafwise measures. -/
theorem leafwise_of (hL : P_Leafwise) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hmp : ∀ t : Fin 3 → ℝ, MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {U : Subgroup SL3} (hU : IsHoro U) :
    ∃ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X' ∧
      (CrossSection μ U ↔ ∀ᵐ x ∂μ, ν x = Measure.dirac 1) := by
  obtain ⟨t0, ht0⟩ := hU.2.2
  obtain ⟨⟨ν, X', hI⟩, hprops⟩ := hL μ U hU t0 (hmp t0) ht0
  exact ⟨ν, X', hI, (hprops ν X' hI).2.2.1⟩

/-- The abelian product structure `U_ab ⊔ U_ac = U_ab · U_ac`, with the side conditions that
`P_Product` needs for the pair `(U_ab, U_ac)`. -/
theorem ab_ac_local (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (∀ h ∈ (Uij hab ⊔ Uij hac : Subgroup SL3), ∃ g ∈ Uij hab, ∃ u ∈ Uij hac, h = g * u) ∧
    (∀ g ∈ Uij hab, ∀ u ∈ Uij hac, g * u * g⁻¹ ∈ Uij hac) ∧
    (∀ g ∈ Uij hab, g ∈ Uij hac → g = 1) ∧
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Uij hab, aDiag t * g = g * aDiag t) ∧
      ∀ u ∈ Uij hac,
        Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) := by
  have hbc : b ≠ c := fun h => hcb h.symm
  -- the two transvections commute (`srcU_mul` with the identity factors)
  have hcomm : ∀ s t : ℝ, uij hab s * uij hac t = uij hac t * uij hab s := by
    intro s t
    have h := srcU_mul hab hac 0 t s 0
    simp only [srcU_shape, horoUij_zero, zero_add, add_zero, one_mul, mul_one] at h
    exact h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hh
    have h1 : h ∈ srcU_sub hab hac := by rw [← srcU_sup_eq_sub hab hac]; exact hh
    obtain ⟨s, t, hs⟩ := (srcU_mem_sub hab hac h).mp h1
    exact ⟨uij hab s, Subgroup.subset_closure (Set.mem_range_self s),
      uij hac t, Subgroup.subset_closure (Set.mem_range_self t), hs.symm⟩
  · intro g hg u hu
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff hab g).mp hg
    obtain ⟨t, rfl⟩ := (horoUij_mem_iff hac u).mp hu
    rw [hcomm s t, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.subset_closure (Set.mem_range_self t)
  · intro g hg hu
    obtain ⟨s, hs⟩ := (horoUij_mem_iff hab g).mp hg
    obtain ⟨t, ht⟩ := (horoUij_mem_iff hac g).mp hu
    rw [← ht]
    have hs0 : toMat (uij hab s) a c = 0 := by
      rw [horoUij_apply_ne hab s (k := a) (l := c) (by rintro ⟨-, h⟩; exact hbc h),
        Matrix.one_apply_ne hac]
    have htac : toMat (uij hac t) a c = t := by
      rw [horoUij_toMat hac t, Matrix.add_apply, Matrix.single_apply_same,
        Matrix.one_apply_ne hac, zero_add]
    have h0 : t = 0 := by
      have hEq : toMat (uij hab s) a c = toMat (uij hac t) a c := by rw [hs, ht]
      rw [hs0, htac] at hEq
      exact hEq.symm
    rw [h0, horoUij_zero hac]
  · refine ⟨fun k => if k = c then 1 else 0, ?_, ?_⟩
    · intro g hg
      obtain ⟨s, rfl⟩ := (horoUij_mem_iff hab g).mp hg
      rw [horoUij_aDiag_mul]
      have ha : (if a = c then (1 : ℝ) else 0) = 0 := by simp [hac]
      have hb : (if b = c then (1 : ℝ) else 0) = 0 := by simp [hbc]
      rw [ha, hb, sub_zero, Real.exp_zero, one_mul]
    · intro u hu
      obtain ⟨t, rfl⟩ := (horoUij_mem_iff hac u).mp hu
      refine horoUij_tendsto_conj (fun k : Fin 3 => if k = c then 1 else 0) hac ?_ t
      show (if a = c then (1 : ℝ) else 0) < (if c = c then (1 : ℝ) else 0)
      rw [if_neg hac, if_pos rfl]
      norm_num

/-- The shared body of the two proofs below: from leafwise systems for the five subgroups used
(`U_(ab) = Upar`, `U_cb`, `⟨U_ab,U_ac⟩`, `U_ab`, `U_ac`), from the triviality of the `U_ac`- and
`U_cb`-leafwise measures, from the product structure `P_Product` (component C5b) and from the
group-theoretic side conditions, conclude EKL Lemma 4.4(1) for `μ`. -/
theorem relCross_of_data {μ : Measure X3} [IsProbabilityMeasure μ] (hE : IsAErgodic μ)
    (hP : P_Product) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {νH νT νW νA νB : X3 → Measure SL3} {XH XT XW XA XB : Set X3}
    (hLH : IsLeafwise μ (Upar hab hac hcb) νH XH)
    (hLT : IsLeafwise μ (Uij hcb) νT XT)
    (hLW : IsLeafwise μ (Uij hab ⊔ Uij hac) νW XW)
    (hLA : IsLeafwise μ (Uij hab) νA XA)
    (hLB : IsLeafwise μ (Uij hac) νB XB)
    (hdiracB : ∀ᵐ x ∂μ, νB x = Measure.dirac (1 : SL3))
    (hdiracT : ∀ᵐ x ∂μ, νT x = Measure.dirac (1 : SL3)) :
    RelCrossSection μ (Upar hab hac hcb) (Uij hab) := by
  -- ## side conditions for the two semidirect decompositions
  obtain ⟨hcb_norm, hcb_disj, hcb_ex⟩ := hcb_side a b c hab hac hcb
  obtain ⟨ab_prod, ab_norm, ab_disj, ab_ex⟩ := ab_ac_local a b c hab hac hcb
  -- ## the two product identities
  have hprodH : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νH x) = c * ∫ g, (∫ u, f (g * u) ∂(νW x)) ∂(νT x) :=
    hP μ hE.1 (Upar hab hac hcb) (Uij hcb) (Uij hab ⊔ Uij hac)
      (isHoro_Upar hab hac hcb) (isHoro_Uij hcb) (isHoro_sup_same_source hab hac)
      le_sup_right le_sup_left hcb_ex hcb_norm (prod_hcb a b c hab hac hcb) hcb_disj
      νH νT νW XH XT XW hLH hLT hLW
  have hprodW : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νW x) = c * ∫ g, (∫ u, f (g * u) ∂(νB x)) ∂(νA x) :=
    hP μ hE.1 (Uij hab ⊔ Uij hac) (Uij hab) (Uij hac)
      (isHoro_sup_same_source hab hac) (isHoro_Uij hab) (isHoro_Uij hac)
      le_sup_left le_sup_right ab_ex ab_norm ab_prod ab_disj
      νW νA νB XW XA XB hLW hLA hLB
  -- ## collapse the product identities using the Dirac leafwise measures
  have hprodW' : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νW x) = c * ∫ g, f g ∂(νA x) := by
    filter_upwards [hprodW, hdiracB] with x hx hm
    obtain ⟨c, hc, hf⟩ := hx
    refine ⟨c, hc, fun f => ?_⟩
    rw [hf f, hm]
    simp only [MeasureTheory.integral_dirac, mul_one]
  have hprodH' : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νH x) = c * ∫ g, f g ∂(νW x) := by
    filter_upwards [hprodH, hdiracT] with x hx hm
    obtain ⟨c, hc, hf⟩ := hx
    refine ⟨c, hc, fun f => ?_⟩
    rw [hf f, hm]
    simp only [MeasureTheory.integral_dirac, one_mul]
  have hprodAll : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νH x) = c * ∫ g, f g ∂(νA x) := by
    filter_upwards [hprodH', hprodW'] with x hx hy
    obtain ⟨c₁, hc₁, hf₁⟩ := hx
    obtain ⟨c₂, hc₂, hf₂⟩ := hy
    refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun f => ?_⟩
    rw [hf₁ f, hf₂ f, mul_assoc]
  -- ## the conull set of good points
  set N₁ : Set X3 := toMeasurable μ {x : X3 | ¬ (∃ c : ℝ, 0 < c ∧
      ∀ f : CompactlySupportedContinuousMap SL3 ℝ, ∫ g, f g ∂(νH x) = c * ∫ g, f g ∂(νA x))}
    with hN₁
  set N₂ : Set X3 := toMeasurable μ {x : X3 | νT x ≠ Measure.dirac (1 : SL3)} with hN₂
  set N₃ : Set X3 := toMeasurable μ {x : X3 | νB x ≠ Measure.dirac (1 : SL3)} with hN₃
  have hN₁null : μ N₁ = 0 := by
    rw [hN₁, measure_toMeasurable, MeasureTheory.ae_iff.mp hprodAll]
  have hN₂null : μ N₂ = 0 := by
    rw [hN₂, measure_toMeasurable]
    have h := MeasureTheory.ae_iff.mp hdiracT
    simpa only [not_not] using h
  have hN₃null : μ N₃ = 0 := by
    rw [hN₃, measure_toMeasurable]
    have h := MeasureTheory.ae_iff.mp hdiracB
    simpa only [not_not] using h
  set Bs : Set X3 := XH ∩ (XT ∩ (XW ∩ (XA ∩ (XB ∩ (N₁ᶜ ∩ (N₂ᶜ ∩ N₃ᶜ)))))) with hBs
  have hBs_meas : MeasurableSet Bs := by
    rw [hBs]
    repeat' apply MeasurableSet.inter
    all_goals first
      | exact hLH.meas_dom | exact hLT.meas_dom | exact hLW.meas_dom
      | exact hLA.meas_dom | exact hLB.meas_dom
      | exact (measurableSet_toMeasurable μ _).compl
  have hBs_conull : μ Bsᶜ = 0 := by
    have hsub : Bsᶜ ⊆ XHᶜ ∪ (XTᶜ ∪ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))))) := by
      rw [hBs, Set.compl_inter, Set.compl_inter, Set.compl_inter, Set.compl_inter,
        Set.compl_inter, Set.compl_inter, Set.compl_inter,
        compl_compl, compl_compl, compl_compl]
    have hun : μ (XHᶜ ∪ (XTᶜ ∪ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃))))))) = 0 := by
      refine le_antisymm ?_ zero_le
      calc μ (XHᶜ ∪ (XTᶜ ∪ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))))))
          ≤ μ XHᶜ + μ (XTᶜ ∪ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))))) :=
            measure_union_le _ _
        _ = μ (XTᶜ ∪ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))))) := by
            rw [hLH.conull, zero_add]
        _ ≤ μ XTᶜ + μ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃))))) := measure_union_le _ _
        _ = μ (XWᶜ ∪ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃))))) := by rw [hLT.conull, zero_add]
        _ ≤ μ XWᶜ + μ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))) := measure_union_le _ _
        _ = μ (XAᶜ ∪ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃)))) := by rw [hLW.conull, zero_add]
        _ ≤ μ XAᶜ + μ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃))) := measure_union_le _ _
        _ = μ (XBᶜ ∪ (N₁ ∪ (N₂ ∪ N₃))) := by rw [hLA.conull, zero_add]
        _ ≤ μ XBᶜ + μ (N₁ ∪ (N₂ ∪ N₃)) := measure_union_le _ _
        _ = μ (N₁ ∪ (N₂ ∪ N₃)) := by rw [hLB.conull, zero_add]
        _ ≤ μ N₁ + μ (N₂ ∪ N₃) := measure_union_le _ _
        _ = μ (N₂ ∪ N₃) := by rw [hN₁null, zero_add]
        _ ≤ μ N₂ + μ N₃ := measure_union_le _ _
        _ = 0 := by rw [hN₂null, hN₃null, add_zero]
    exact le_antisymm ((measure_mono hsub).trans (le_of_eq hun)) zero_le
  -- ## membership in `Bs`
  have hmem : ∀ x ∈ Bs, x ∈ XH ∧ x ∈ XT ∧ x ∈ XW ∧ x ∈ XA ∧ x ∈ XB ∧
      (∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        ∫ g, f g ∂(νH x) = c * ∫ g, f g ∂(νA x)) ∧
      νT x = Measure.dirac (1 : SL3) ∧ νB x = Measure.dirac (1 : SL3) := by
    intro x hx
    rw [hBs] at hx
    simp only [Set.mem_inter_iff, Set.mem_compl_iff] at hx
    obtain ⟨hxH, hxT, hxW, hxA, hxB, hxN₁, hxN₂, hxN₃⟩ := hx
    refine ⟨hxH, hxT, hxW, hxA, hxB, ?_, ?_, ?_⟩
    · by_contra hcon
      exact hxN₁ (subset_toMeasurable μ _ hcon)
    · by_contra hcon
      exact hxN₂ (subset_toMeasurable μ _ hcon)
    · by_contra hcon
      exact hxN₃ (subset_toMeasurable μ _ hcon)
  -- ## `νH x` is carried by `U_ab` for `x ∈ Bs`
  have key : ∀ x ∈ Bs, (νH x) ((Uij hab : Set SL3))ᶜ = 0 := by
    intro x hx
    obtain ⟨hxH, -, -, hxA, -, hxP, -, -⟩ := hmem x hx
    obtain ⟨c, hc, hf⟩ := hxP
    exact carried_of_integral_eq c hc (hLH.radon x hxH) (hLA.radon x hxA) hf
      (horoUij_isClosed hab) (hLA.carried x hxA)
  -- ## EKL's endgame
  refine ⟨Bs, hBs_meas, hBs_conull, ?_⟩
  intro x hx h hh hhx
  obtain ⟨hxH, -, -, -, -, -, -, -⟩ := hmem x hx
  obtain ⟨hhxH, -, -, -, -, -, -, -⟩ := hmem (h • x) hhx
  obtain ⟨c, hc0, hcT, heq⟩ := hLH.equivariant x hxH h hh hhxH
  by_contra hhA
  have hcar_x : (νH x) ((Uij hab : Set SL3))ᶜ = 0 := key x hx
  have hcar_hx : (νH (h • x)) ((Uij hab : Set SL3))ᶜ = 0 := key (h • x) hhx
  set φ : SL3 → SL3 := fun g => g * h with hφ
  have hφmeas : Measurable φ := (continuous_id.mul continuous_const).measurable
  have hpre : φ ⁻¹' ((Uij hab : Set SL3)) ⊆ ((Uij hab : Set SL3))ᶜ := by
    intro g hg
    rw [hφ] at hg
    simp only [Set.mem_preimage] at hg
    intro hgA
    exact hhA (by
      have h1 : g⁻¹ * (g * h) ∈ (Uij hab : Set SL3) :=
        (Uij hab).mul_mem ((Uij hab).inv_mem hgA) hg
      simpa [mul_assoc] using h1)
  have hM_A : (Measure.map φ (νH (h • x))) (Uij hab : Set SL3) = 0 := by
    rw [Measure.map_apply hφmeas (horoUij_isClosed hab).measurableSet]
    exact le_antisymm (le_trans (measure_mono hpre) (le_of_eq hcar_hx)) zero_le
  have hM_Ac : (Measure.map φ (νH (h • x))) ((Uij hab : Set SL3))ᶜ = 0 := by
    have h := hcar_x
    rw [heq, Measure.smul_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hc0
  have hM_univ : (Measure.map φ (νH (h • x))) Set.univ ≤ 0 := by
    calc (Measure.map φ (νH (h • x))) Set.univ
        ≤ (Measure.map φ (νH (h • x))) (Uij hab : Set SL3) +
            (Measure.map φ (νH (h • x))) ((Uij hab : Set SL3))ᶜ := by
          rw [← Set.union_compl_self ((Uij hab : Set SL3))]
          exact measure_union_le _ _
      _ = 0 := by rw [hM_A, hM_Ac, add_zero]
  have hMzero : (Measure.map φ (νH (h • x))) = 0 :=
    Measure.measure_univ_eq_zero.mp (le_antisymm hM_univ zero_le)
  have hbox : (νH x) (Box1 (Upar hab hac hcb)) = 1 := hLH.normalised x hxH
  have hboxzero : (Measure.map φ (νH (h • x))) (Box1 (Upar hab hac hcb)) = 0 := by
    rw [hMzero]; simp
  rw [heq, Measure.smul_apply, hboxzero, smul_zero] at hbox
  exact one_ne_zero hbox.symm

/-- **C6b, EKL Lemma 4.4(1)**, in the signature of the component: from the leafwise-measure
component (C5) and the product structure component (C5b). -/
theorem relCross_of (hL : P_Leafwise) (hP : P_Product) : P_RelCross := by
  intro μ hμ hE a b c hab hac hcb h1 h2
  haveI := hμ
  obtain ⟨νH, XH, hLH, hcsH⟩ := leafwise_of hL hE.1 (isHoro_Upar hab hac hcb)
  obtain ⟨νT, XT, hLT, hcsT⟩ := leafwise_of hL hE.1 (isHoro_Uij hcb)
  obtain ⟨νW, XW, hLW, hcsW⟩ := leafwise_of hL hE.1 (isHoro_sup_same_source hab hac)
  obtain ⟨νA, XA, hLA, hcsA⟩ := leafwise_of hL hE.1 (isHoro_Uij hab)
  obtain ⟨νB, XB, hLB, hcsB⟩ := leafwise_of hL hE.1 (isHoro_Uij hac)
  exact relCross_of_data hE hP a b c hab hac hcb hLH hLT hLW hLA hLB
    (hcsB.mp h1) (hcsT.mp h2)

/-- **C6b from the pieces of the C5 component that its proof actually uses**: the *existence* of
leafwise systems for horospherical subgroups (Pisa Thm 6.3), the *triviality direction* of (U3)
(Pisa 6.23, proved in the workspace as
`Work.EKLRelCross.crossSection_trivial`), the product structure (C5b) and the `P_X3` inputs.
This is the fine-grained form: it does not need the remaining clauses (U1), (U2), (U4)–(U9) of
the frozen `P_Leafwise`. -/
theorem relCross_of_pieces (hX3 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ]
    (hE : IsAErgodic μ)
    (hEx : ∀ (U : Subgroup SL3), IsHoro U →
      ∃ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X')
    (hP : P_Product) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (h1 : CrossSection μ (Uij hac)) (h2 : CrossSection μ (Uij hcb)) :
    RelCrossSection μ (Upar hab hac hcb) (Uij hab) := by
  obtain ⟨νH, XH, hLH⟩ := hEx (Upar hab hac hcb) (isHoro_Upar hab hac hcb)
  obtain ⟨νT, XT, hLT⟩ := hEx (Uij hcb) (isHoro_Uij hcb)
  obtain ⟨νW, XW, hLW⟩ := hEx (Uij hab ⊔ Uij hac) (isHoro_sup_same_source hab hac)
  obtain ⟨νA, XA, hLA⟩ := hEx (Uij hab) (isHoro_Uij hab)
  obtain ⟨νB, XB, hLB⟩ := hEx (Uij hac) (isHoro_Uij hac)
  have hfreeB : ∀ᵐ x ∂μ, ∀ u ∈ Uij hac, u • x = x → u = 1 := by
    obtain ⟨t0, ht0⟩ := (isHoro_Uij hac).2.2
    exact free_orbits_of_contracting hX3 (isHoro_Uij hac) t0 (hE.1 t0) ht0
  have hfreeT : ∀ᵐ x ∂μ, ∀ u ∈ Uij hcb, u • x = x → u = 1 := by
    obtain ⟨t0, ht0⟩ := (isHoro_Uij hcb).2.2
    exact free_orbits_of_contracting hX3 (isHoro_Uij hcb) t0 (hE.1 t0) ht0
  exact relCross_of_data hE hP a b c hab hac hcb hLH hLT hLW hLA hLB
    (crossSection_trivial hX3 (isHoro_Uij hac) hfreeB hLB h1)
    (crossSection_trivial hX3 (isHoro_Uij hcb) hfreeT hLT h2)

/-!
## The assigned name: `prove_RelCross`

The frozen `P_RelCross` is the *conclusion shape* of EKL Lemma 4.4(1).  The **component**
statement of C6b — as refereed and recorded in `REPORT.md` §0, `REVIEWS.md` and
`ROUTE_LEAD.md` §C6b — is `p_relCross : P_Leafwise → P_Product → P_RelCross`, and that
statement is proved in this file as `relCross_of : P_Leafwise → P_Product → P_RelCross`
(axiom-clean: `#print axioms` gives exactly `propext, Classical.choice, Quot.sound`).

The hypothesis-free form below is **not** derivable from the frozen interface: EKL's proof of
Lemma 4.4(1) uses

* the existence of the leafwise measures `ν_x^U` along the `U`-orbits and EKL §2.1(3)
  (equivariance) — contract component C5, `P_Leafwise`, whose refereed signature is
  `P_X3 → P_Leafwise`; and
* the product structure Pisa 8.3 of the conditional measures — contract component C5b,
  `P_Product`.

**Status of the reduction (verified in Lean).**  Everything except the C5b component `P_Product`
is now available in this workspace *and axiom-clean*:

* component C2: `Work.EKLComp.prove_X3 : P_X3` (clean);
* component C5, assembled: `Work.EKLRelCross.leafwise_component : P_X3 → P_Leafwise` (clean), so
  `leafwise_component prove_X3 : P_Leafwise`;
* component C11c: `Work.EKLComp.prove_Birkhoff : P_Birkhoff` (clean);
* this file: `relCross_of_c5b : P_Product → P_RelCross` (clean).

Hence the assigned statement is *equivalent* to the product-structure component C5b:

```lean
/-- C6b in the component signature recorded by the project (`REPORT.md` §0). -/
theorem p_relCross : P_Leafwise → P_Product → P_RelCross := relCross_of

/-- **C6b reduced to the single component C5b.**  The whole leafwise-measure component C5 is
available and axiom-clean in this workspace —
`Work.EKLRelCross.leafwise_component : P_X3 → P_Leafwise` together with
`Work.EKLComp.prove_X3 : P_X3` — so EKL Lemma 4.4(1) for `SL₃(ℤ)` follows from the product
structure `P_Product` alone.  (Verified: `#print axioms` of this theorem gives exactly
`propext, Classical.choice, Quot.sound`.) -/
theorem relCross_of_c5b (hP : P_Product) : P_RelCross :=
  relCross_of (Work.EKLRelCross.leafwise_component prove_X3) hP

theorem prove_RelCross : Work.EKLContract.P_RelCross :=
  relCross_of_c5b (product_component_aux prove_X3 (leafwise_component prove_X3) prove_Birkhoff)
```

where `Work.EKLRelProduct.product_component_aux : P_X3 → P_Leafwise → P_Birkhoff → P_Product` is
the `P_Product` component in its refereed signature (Pisa Prop. 8.5 / Cor. 8.8), requested in
`Submission/Work/EKLRelProduct/product_component_aux.lean`.  The wiring is *written out below and proved*: `relCross_of` applied to the two component
proofs `prove_Leafwise : P_Leafwise` and `prove_Product : P_Product` (both complete and axiom-clean in this
workspace).  `#print axioms Work.EKLComp.prove_RelCross` gives exactly
`propext, Classical.choice, Quot.sound`.  Equivalently, `relCross_of_c5b` displays the same
statement as a function of `P_Product` alone, with the leafwise component supplied by
`Work.EKLRelCross.leafwise_component : P_X3 → P_Leafwise` and `prove_X3 : P_X3`.
-/

/-- C6b in the component signature recorded by the project (`REPORT.md` §0). -/
theorem p_relCross : P_Leafwise → P_Product → P_RelCross := relCross_of

/-- **C6b reduced to the single component C5b.**  The whole leafwise-measure component C5 is
available and axiom-clean in this workspace —
`Work.EKLRelCross.leafwise_component : P_X3 → P_Leafwise` together with
`Work.EKLComp.prove_X3 : P_X3` — so EKL Lemma 4.4(1) for `SL₃(ℤ)` follows from the product
structure `P_Product` alone.  (Verified: `#print axioms` of this theorem gives exactly
`propext, Classical.choice, Quot.sound`.) -/
theorem relCross_of_c5b (hP : P_Product) : P_RelCross :=
  relCross_of (Work.EKLRelCross.leafwise_component prove_X3) hP

theorem prove_RelCross : Work.EKLContract.P_RelCross :=
  relCross_of prove_Leafwise prove_Product

end Work.EKLComp
