import Mathlib
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.LeafExistence
import Submission.Work.EKLComp.AeFreeness
import Submission.Work.EKLComp.smulMS_propor
import Submission.Work.EKLRelCross.exists_compact_nhds_comp_mul_support
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLC7.restrict_smulSt
import Submission.Work.EKLUInv.local_invariance_of_ae_haar
import Submission.Work.EKLRelCross.isUInvariant_of_ae_translation
import Submission.Work.EKLRelCross.rightQuasiInv
import Submission.Work.EKLRelCross.leafwise_propor
import Submission.Work.EKLRelCross.restrict_eq_of_pushforward_relation
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLRelCross.flowerCollarAdmissible

/-!
# `Work.EKLComp.leaf_invariant` — clause (U4) of the frozen contract

Pisa 6.27 / EKL (6): for a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical
subgroup `U`, `t0` with `α^{t0}` preserving `μ` and contracting `U`, and a leafwise system `ν`
for `(μ, U)`,

  `μ` is `U`-invariant  ⟺  `ν x` is right-`U`-invariant for `μ`-a.e. `x`.

* The direction `⟸` is `Work.EKLRelCross.isUInvariant_of_ae_translation` (Pisa 6.27, via the
  big-atom flowers of `Work.EKLUInv`).
* The direction `⟹` is `aeHaar_of_Uinvariant` below.  Its input is the comparison
  `Work.EKLComp.smulMS_propor` of the `condexp` field of `IsLeafwise` at `x` for the plaque
  algebra `(Z, m)` with the field of the transported plaque algebra
  `(Work.EKLC7.smulSt u Z, Work.EKLC7.smulMS u m)` at `u • x`; combined with the `equivariant`
  field this gives, for every `u ∈ U` and `μ`-a.e. `x`, that the left translate of `ν x` by `u`
  is proportional to `ν x` on the shape (`prop_left_of_smulMS`).  The flowers at all radii
  upgrade this to a global proportionality for each `u` (`global_propor`); a countable dense
  subset of `U` together with the closedness of the set of quasi-invariance elements
  (`Work.EKLComp.quasiInv_closed`) upgrades "for all elements of a dense subset" to "for all
  `u ∈ U`" (`leftQuasiInvariance`); finally `Work.EKLRelCross.rightQuasiInv` (left
  quasi-invariance ⇒ right quasi-invariance for a measure carried by a horospherical `U`) and
  clause (U5) `Work.EKLRelCross.leafwise_propor` (a.e. proportional ⇒ equal) turn right
  quasi-invariance into right invariance.
-/

noncomputable section

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- The child statement at `u⁻¹`, in the direction needed below. -/
theorem smulMS_propor_inv (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (hinv : IsUInvariant μ U) {u : SL3} (hu : u ∈ U)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    {Z : Set X3} {m : MeasurableSpace X3} (hpa : IsPlaqueAlgebra U Z m) :
    ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x) := by
  have h := smulMS_propor h2 U hU hinv (U.inv_mem hu) hL hfree hpa
  simpa only [inv_inv] using h

/-- **The `(♠)` step**: comparison of the two `condexp` fields + equivariance. -/
theorem prop_left_of_smulMS {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {u : SL3} (hu : u ∈ U) {Z : Set X3} {m : MeasurableSpace X3}
    (hchild : ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x)) :
    ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν x).map (fun g : SL3 => u * g)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x) := by
  filter_upwards [hchild] with x hx hxX huxX
  obtain ⟨c₁, hc₁0, hc₁T, hc₁⟩ := hx hxX huxX
  obtain ⟨ce, hce0, hceT, hce⟩ := hL.equivariant x hxX u⁻¹ (U.inv_mem hu) huxX
  refine ⟨ce * c₁, mul_ne_zero hce0 hc₁0, ENNReal.mul_ne_top hceT hc₁T, ?_⟩
  have hmap : (ν x).map (fun g : SL3 => u * g)
      = ce • (ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹) := by
    rw [hce, Measure.map_smul] <;> try fun_prop
    rw [Measure.map_map]
    · have hf : ((fun g : SL3 => u * g) ∘ (fun g : SL3 => g * u⁻¹))
          = (fun g : SL3 => u * g * u⁻¹) := by
        funext g
        simp only [Function.comp_apply]
        rw [mul_assoc]
      rw [hf]
    · exact (continuous_const.mul continuous_id).measurable
    · exact (continuous_id.mul continuous_const).measurable
  rw [hmap, Measure.restrict_smul, hc₁, smul_smul]

/-- **The ball proportionality**: for every `u ∈ U` and `R : ℕ`, for `μ`-a.e. `x` the left
translate of `ν x` by `u` is proportional to `ν x` on the ball `V (R+2) ∩ U`, using the flowers
at radius `R+2`. -/
theorem ball_propor (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (t0 : Fin 3 → ℝ) (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (hinv : IsUInvariant μ U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    {u : SL3} (hu : u ∈ U)
    (hchild : ∀ {Z : Set X3} {m : MeasurableSpace X3}, IsPlaqueAlgebra U Z m →
      ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x))
    (R : ℕ) :
    ∀ᵐ x ∂μ, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ((ν x).map (fun g : SL3 => u * g)).restrict (V (((R : ℝ) + 2)) ∩ (U : Set SL3))
        = c • (ν x).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3)) := by
  classical
  obtain ⟨Z, G, m, hpla, hrest⟩ :=
    Work.EKLUInv.bigAtoms_flowers h2 μ U hU t0 hmp hcontr ((R : ℝ) + 2) (by positivity)
  obtain ⟨hGmeas, hcov, hshape⟩ := hrest
  have hGsub : ∀ n, G n ⊆ Z n := fun n => (hGmeas n).2
  set W : Set SL3 := V ((R : ℝ) + 2) ∩ (U : Set SL3) with hWdef
  -- the a.e. proportionality statement at each algebra of the flower
  have hstep : ∀ n : ℕ, ∀ᵐ x ∂(μ.restrict (Z n)), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)
          = c • (ν x).restrict (shape (m n) U x) := by
    intro n
    exact prop_left_of_smulMS hL hu (hchild (hpla n))
  -- the exceptional sets
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff]
    exact hL.conull
  have hpre : μ ((fun x : X3 => u⁻¹ • x) ⁻¹' X'ᶜ) = 0 := by
    have hm : Measure.map (fun x : X3 => u⁻¹ • x) μ = μ := (hinv u⁻¹ (U.inv_mem hu)).map_eq
    rw [← Measure.map_apply (by fun_prop : Measurable fun x : X3 => u⁻¹ • x) hL.meas_dom.compl, hm]
    exact hL.conull
  -- the `G n`-restricted a.e. statements
  have hstep_ae : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ G n → (x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)
          = c • (ν x).restrict (shape (m n) U x)) := by
    intro n
    have h2 : ∀ᵐ x ∂μ, x ∈ Z n → (x ∈ X' → u⁻¹ • x ∈ X' →
        ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
          ((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)
            = c • (ν x).restrict (shape (m n) U x)) := by
      rw [← ae_restrict_iff' ((hpla n).1 _ (hpla n).2.2.1)]
      exact hstep n
    filter_upwards [h2] with x hx
    intro hxG
    exact hx (hGsub n hxG)
  -- the `u⁻¹`-image of `X'` is conull
  have hX'ae' : ∀ᵐ x ∂μ, u⁻¹ • x ∈ X' := by
    have hm : Measure.map (fun x : X3 => u⁻¹ • x) μ = μ := (hinv u⁻¹ (U.inv_mem hu)).map_eq
    have h1 : ∀ᵐ x ∂(Measure.map (fun x : X3 => u⁻¹ • x) μ), x ∈ X' := by rw [hm]; exact hX'
    exact (ae_map_iff ((by fun_prop : Measurable fun x : X3 => u⁻¹ • x)).aemeasurable hL.meas_dom).mp h1
  have hgood : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ G n → (∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)
        = c • (ν x).restrict (shape (m n) U x)) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hstep_ae n, hX', hX'ae'] with x hx hxX huxX
    intro hxG
    exact hx hxG hxX huxX
  have hcov' : ∀ᵐ x ∂μ, x ∈ ⋃ n, G n := by
    rw [ae_iff]
    exact hcov
  have hfin : ∀ᵐ x ∂μ, ∃ n : ℕ, x ∈ G n ∧ ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)
        = c • (ν x).restrict (shape (m n) U x) := by
    filter_upwards [hgood, hcov'] with x hx hxcov
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxcov
    exact ⟨n, hn, hx n hn⟩
  filter_upwards [hfin] with x hx
  obtain ⟨n, hxG, c, hc0, hcT, hc⟩ := hx
  refine ⟨c, hc0, hcT, ?_⟩
  have hsub : W ⊆ shape (m n) U x := hshape n x hxG
  have h1 : (((ν x).map (fun g : SL3 => u * g)).restrict (shape (m n) U x)).restrict W
      = ((ν x).map (fun g : SL3 => u * g)).restrict W :=
    Measure.restrict_restrict_of_subset hsub
  have h2 : ((c • (ν x).restrict (shape (m n) U x))).restrict W = c • (ν x).restrict W := by
    rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub]
  rw [← h1, ← h2, hc]

/-- For every `u ∈ U`, for `μ`-a.e. `x`, the left translate of `ν x` by `u` is proportional to
`ν x` on every ball `V (R+2) ∩ U` simultaneously. -/
theorem ball_propor_all (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (t0 : Fin 3 → ℝ) (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (hinv : IsUInvariant μ U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    {u : SL3} (hu : u ∈ U)
    (hchild : ∀ {Z : Set X3} {m : MeasurableSpace X3}, IsPlaqueAlgebra U Z m →
      ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x)) :
    ∀ᵐ x ∂μ, ∀ R : ℕ, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ((ν x).map (fun g : SL3 => u * g)).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3))
        = c • (ν x).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3)) := by
  rw [ae_all_iff]
  intro R
  exact ball_propor h2 U hU t0 hmp hcontr hinv hL hfree hu hchild R

/-- **Global left quasi-invariance**: for every `u ∈ U`, for `μ`-a.e. `x ∈ X'` the left translate
of `ν x` by `u` is proportional to `ν x` on the whole group. -/
theorem global_propor (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (t0 : Fin 3 → ℝ) (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (hinv : IsUInvariant μ U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    {u : SL3} (hu : u ∈ U)
    (hchild : ∀ {Z : Set X3} {m : MeasurableSpace X3}, IsPlaqueAlgebra U Z m →
      ∀ᵐ x ∂(μ.restrict Z), x ∈ X' → u⁻¹ • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ((ν (u⁻¹ • x)).map (fun g : SL3 => u * g * u⁻¹)).restrict (shape m U x)
          = c • (ν x).restrict (shape m U x)) :
    ∀ᵐ x ∂μ, x ∈ X' → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (ν x).map (fun g : SL3 => u * g) = c • ν x := by
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff]; exact hL.conull
  filter_upwards [ball_propor_all h2 U hU t0 hmp hcontr hinv hL hfree hu hchild, hX']
    with x hx hxX
  intro _
  -- constant chosen at `R = 0`
  obtain ⟨c, hc0, hcT, hc⟩ := hx 0
  haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX
  have hmass : ν x (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) ≠ 0 := by
    have h1' : 0 < ν x (V (((0 : ℕ) : ℝ) + 2)) := hL.pos x hxX _ (by norm_num)
    have h2' : ν x (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)ᶜ) = 0 :=
      measure_mono_null Set.inter_subset_right (hL.carried x hxX)
    have hun : V (((0 : ℕ) : ℝ) + 2) = (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) ∪
        (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)ᶜ) := by
      ext g; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
    have hdisj : Disjoint (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
        (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)ᶜ) := by
      rw [Set.disjoint_left]; rintro g ⟨-, hg⟩ ⟨-, hg'⟩; exact hg' hg
    rw [hun, measure_union hdisj, h2', add_zero] at h1'
    · exact h1'.ne'
    · exact ((Work.EKLContract.Lemmas.V_open_one _
        (by norm_num : (0:ℝ) < (((0 : ℕ) : ℝ) + 2))).1).measurableSet.inter hU.1.measurableSet.compl
  have hmassT : ν x (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) ≠ ⊤ := by
    have hcomp : IsCompact {g : SL3 | ∀ i j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 2 ≤ g i j ∧
        g i j ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 2} :=
      Work.EKLProd.sl3EntryBox_compact _ _
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top)
    intro g hg i j
    have h := hg.1 i j
    rw [abs_lt] at h
    norm_num at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hVsub : ∀ R : ℕ,
      V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3) ⊆ V ((R : ℝ) + 2) ∩ (U : Set SL3) := by
    intro R
    refine Set.inter_subset_inter_left _ (Work.EKLRelCross.V_mono_rad ?_)
    exact add_le_add (Nat.cast_le.mpr (Nat.zero_le R)) le_rfl
  have hconst : ∀ R : ℕ, ∀ c' : ENNReal, c' ≠ 0 → c' ≠ ⊤ →
      ((ν x).map (fun g : SL3 => u * g)).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3))
        = c' • (ν x).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3)) → c' = c := by
    intro R c' hc'0 hc'T hc'
    have h1 : (((ν x).map (fun g : SL3 => u * g)).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3))).restrict
          (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
        = ((c' • (ν x).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3)))).restrict
          (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) := by rw [hc']
    rw [Measure.restrict_restrict_of_subset (hVsub R), Measure.restrict_smul,
      Measure.restrict_restrict_of_subset (hVsub R)] at h1
    have h2 : c' • (ν x).restrict (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
        = c • (ν x).restrict (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) := h1.symm.trans hc
    have h3 : c' * (ν x) (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
        = c * (ν x) (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) := by
      have hAA : (ν x).restrict (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
          (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))
            = ν x (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3)) := by
        rw [Measure.restrict_apply (by
          exact (Work.EKLContract.Lemmas.V_open_one _
            (by norm_num : (0:ℝ) < (((0 : ℕ) : ℝ) + 2))).1.measurableSet.inter hU.1.measurableSet),
          Set.inter_self]
      simpa only [Measure.smul_apply, smul_eq_mul, hAA] using
        congrArg (fun (m : Measure SL3) => m (V (((0 : ℕ) : ℝ) + 2) ∩ (U : Set SL3))) h2
    exact (ENNReal.mul_left_inj hmass hmassT).mp h3
  have hcR : ∀ R : ℕ,
      ((ν x).map (fun g : SL3 => u * g)).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3))
        = c • (ν x).restrict (V ((R : ℝ) + 2) ∩ (U : Set SL3)) := by
    intro R
    obtain ⟨c', hc'0, hc'T, hc'⟩ := hx R
    rw [hconst R c' hc'0 hc'T hc'] at hc'
    exact hc'
  -- the global equality
  refine ⟨c, hc0, hcT, ?_⟩
  have hcar : ν x ((U : Set SL3)ᶜ) = 0 := hL.carried x hxX
  have hcar2 : ((ν x).map (fun g : SL3 => u * g)) ((U : Set SL3)ᶜ) = 0 := by
    rw [Measure.map_apply (by fun_prop : Measurable fun g : SL3 => u * g)
      hU.1.measurableSet.compl]
    refine measure_mono_null ?_ hcar
    intro g hg
    exact fun hgU => hg (U.mul_mem hu hgU)
  refine Measure.ext fun T hT => ?_
  have h1 : ((ν x).map (fun g : SL3 => u * g)) T
      = ((ν x).map (fun g : SL3 => u * g)) (T ∩ (U : Set SL3)) :=
    Work.EKLRelCross.measure_eq_measure_inter_of_compl_null _ hcar2
  have hcar' : (c • ν x) ((U : Set SL3)ᶜ) = 0 := by
    rw [Measure.smul_apply, smul_eq_mul, hcar, mul_zero]
  have h2 : (c • ν x) T = (c • ν x) (T ∩ (U : Set SL3)) :=
    Work.EKLRelCross.measure_eq_measure_inter_of_compl_null _ hcar'
  rw [h1, h2]
  -- the cover of `U` by the balls, and continuity from below
  have hcover : (U : Set SL3) = ⋃ R : ℕ, V ((R : ℝ) + 2) ∩ (U : Set SL3) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun R => Set.inter_subset_right)
    intro g hgU
    have h1 : g ∈ ⋃ n : ℕ, V (n : ℝ) ∩ (U : Set SL3) := by
      rw [Work.EKLRelCross.iUnion_V_inter_eq U]; exact hgU
    obtain ⟨n, hnV, hnU⟩ := Set.mem_iUnion.mp h1
    refine Set.mem_iUnion.mpr ⟨n, ?_, hnU⟩
    refine Work.EKLRelCross.V_mono_rad ?_ hnV
    exact le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 2)
  have hunion : (T ∩ (U : Set SL3))
      = ⋃ R : ℕ, T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3)) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun R => Set.inter_subset_left)
    intro g hg
    have hgU : g ∈ ⋃ R : ℕ, V ((R : ℝ) + 2) ∩ (U : Set SL3) := by
      rw [← hcover]; exact hg.2
    obtain ⟨R, hR⟩ := Set.mem_iUnion.mp hgU
    exact Set.mem_iUnion.mpr ⟨R, ⟨hg.1, hg.2⟩, hR.1, hR.2⟩
  have hmono : Monotone fun R : ℕ => T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3)) := by
    intro R R' hRR'
    have hVV : V ((R : ℝ) + 2) ⊆ V ((R' : ℝ) + 2) :=
      Work.EKLRelCross.V_mono_rad (add_le_add (Nat.cast_le.mpr hRR') le_rfl)
    exact Set.inter_subset_inter subset_rfl (Set.inter_subset_inter hVV subset_rfl)
  have h4 : ∀ R : ℕ, ((ν x).map (fun g : SL3 => u * g))
        (T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3)))
      = (c • ν x) (T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3))) := by
    intro R
    set A : Set SL3 := V ((R : ℝ) + 2) ∩ (U : Set SL3) with hA
    set S : Set SL3 := T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3)) with hS
    have hmeas : MeasurableSet S := by
      rw [hS]
      exact (hT.inter hU.1.measurableSet).inter
        ((Work.EKLComp.isOpen_V _).measurableSet.inter hU.1.measurableSet)
    have hSsub : S ⊆ A := by rw [hS, hA]; exact Set.inter_subset_right
    have h5 := congrArg (fun (m : Measure SL3) => m S) (hcR R)
    have hL : ((ν x).map (fun g : SL3 => u * g)).restrict A S
        = ((ν x).map (fun g : SL3 => u * g)) S := by
      rw [Measure.restrict_apply hmeas, Set.inter_eq_left.mpr hSsub]
    have hR : (c • (ν x).restrict A) S = c * (ν x) S := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hmeas,
        Set.inter_eq_left.mpr hSsub]
    rw [hL, hR] at h5
    simpa only [hS, hA, Measure.smul_apply, smul_eq_mul] using h5
  have hlim1 := MeasureTheory.tendsto_measure_iUnion_atTop
    (μ := (ν x).map (fun g : SL3 => u * g)) hmono
  have hlim2 := MeasureTheory.tendsto_measure_iUnion_atTop (μ := c • ν x) hmono
  have hseq : (⇑((ν x).map (fun g : SL3 => u * g)) ∘ fun R : ℕ =>
        T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3)))
      = (⇑(c • ν x) ∘ fun R : ℕ =>
        T ∩ (U : Set SL3) ∩ (V ((R : ℝ) + 2) ∩ (U : Set SL3))) := by
    funext R
    exact h4 R
  rw [hseq] at hlim1
  have h6 := tendsto_nhds_unique hlim1 hlim2
  rw [← hunion] at h6
  exact h6

/-- The `σ`-mass of a left translate of a test function. -/
def testMass (σ : Measure SL3) (f : C_c(SL3, ℝ≥0)) (u : SL3) : ℝ≥0∞ :=
  ∫⁻ x, (f (u * x) : ℝ≥0∞) ∂σ

theorem testMass_eq_lintegral_map (σ : Measure SL3) (f : C_c(SL3, ℝ≥0)) (u : SL3) :
    testMass σ f u = ∫⁻ y, (f y : ℝ≥0∞) ∂(σ.map (fun g : SL3 => u * g)) := by
  rw [testMass]
  exact (MeasureTheory.lintegral_map (ENNReal.continuous_coe.comp f.continuous).measurable
    (continuous_const.mul continuous_id).measurable).symm

/-- A bound for a compactly supported continuous `ℝ≥0`-valued function. -/
theorem exists_bound_cc (f : C_c(SL3, ℝ≥0)) : ∃ M : ℝ≥0, ∀ x, f x ≤ M := by
  have hc : IsCompact (tsupport (⇑f)) := f.hasCompactSupport
  obtain ⟨M, hM⟩ := (hc.image f.continuous).bddAbove
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : (⇑f) x = 0
  · rw [hx]; exact le_max_right _ _
  · exact le_trans (hM ⟨x, subset_tsupport _ (by simpa [Function.mem_support] using hx), rfl⟩)
      (le_max_left _ _)

theorem isFiniteMeasureOnCompacts_map_mulLeft (σ : Measure SL3)
    (hσ : IsFiniteMeasureOnCompacts σ) (u : SL3) :
    IsFiniteMeasureOnCompacts (σ.map (fun g : SL3 => u * g)) := by
  have h := MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map σ (Homeomorph.mulLeft u)
  rwa [Homeomorph.coe_mulLeft] at h

theorem testMass_lt_top (σ : Measure SL3) (hσ : IsFiniteMeasureOnCompacts σ)
    (f : C_c(SL3, ℝ≥0)) (u : SL3) : testMass σ f u < ⊤ := by
  classical
  haveI := hσ
  obtain ⟨M, hM⟩ := exists_bound_cc f
  have hsupp : IsCompact ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)) := by
    have hset : (fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)
        = (fun y : SL3 => u⁻¹ * y) '' tsupport (⇑f) := by
      ext x; constructor
      · intro hx; exact ⟨u * x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [hset]
    exact (show IsCompact (tsupport (⇑f)) from f.hasCompactSupport).image
      (continuous_const.mul continuous_id)
  have hfin : σ ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)) ≠ ⊤ :=
    (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hsupp).ne
  have hle : ∀ x : SL3, (f (u * x) : ℝ≥0∞)
      ≤ (M : ℝ≥0∞) * ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)).indicator
          (1 : SL3 → ℝ≥0∞) x := by
    intro x
    by_cases hx : x ∈ (fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      exact ENNReal.coe_le_coe.mpr (hM (u * x))
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have h0 : f (u * x) = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ (by simpa [Function.mem_support] using hne))
      simp [h0]
  calc testMass σ f u
      ≤ ∫⁻ x, (M : ℝ≥0∞) * ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)).indicator
          (1 : SL3 → ℝ≥0∞) x ∂σ := lintegral_mono hle
    _ = (M : ℝ≥0∞) * ∫⁻ x, ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)).indicator
          (1 : SL3 → ℝ≥0∞) x ∂σ :=
        MeasureTheory.lintegral_const_mul _ (Measurable.indicator measurable_const
          hsupp.measurableSet)
    _ = (M : ℝ≥0∞) * σ ((fun x : SL3 => u * x) ⁻¹' tsupport (⇑f)) := by
        rw [MeasureTheory.lintegral_indicator_one hsupp.measurableSet]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin.lt_top

theorem testMass_continuous (σ : Measure SL3) (hσ : IsFiniteMeasureOnCompacts σ)
    (f : C_c(SL3, ℝ≥0)) : Continuous (fun u : SL3 => testMass σ f u) := by
  classical
  haveI := hσ
  obtain ⟨M, hM⟩ := exists_bound_cc f
  rw [continuous_iff_continuousAt]
  intro u₀
  obtain ⟨B, U, hBcomp, hUne, hBU⟩ :=
    Work.EKLRelCross.exists_compact_nhds_comp_mul_support (fun x : SL3 => (f x : ℝ≥0∞))
      (f.hasCompactSupport.comp_left (ENNReal.coe_zero)) u₀
  refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence (μ := σ)
    (l := 𝓝 u₀) (F := fun u x => (f (u * x) : ℝ≥0∞)) (f := fun x => (f (u₀ * x) : ℝ≥0∞))
    (fun x => (M : ℝ≥0∞) * B.indicator (1 : SL3 → ℝ≥0∞) x) ?_ ?_ ?_ ?_
  · filter_upwards with u
    exact ((ENNReal.continuous_coe.comp f.continuous).comp
      (continuous_const.mul continuous_id)).measurable
  · filter_upwards [hUne] with u hu
    refine Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      exact ENNReal.coe_le_coe.mpr (hM (u * x))
    · rw [Set.indicator_of_notMem hx]
      have h0 : f (u * x) = 0 := by
        by_contra hne
        exact hx (hBU u hu x (by simpa using hne))
      rw [h0]
      simp
  · rw [MeasureTheory.lintegral_const_mul (M : ℝ≥0∞)
      (f := fun x : SL3 => B.indicator (1 : SL3 → ℝ≥0∞) x)
      (Measurable.indicator measurable_const hBcomp.measurableSet),
      MeasureTheory.lintegral_indicator_one hBcomp.measurableSet]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := σ) hBcomp)).ne
  · refine Eventually.of_forall (fun x => ?_)
    have hcont : Continuous (fun u : SL3 => (f (u * x) : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp f.continuous).comp (continuous_id.mul continuous_const)
    exact hcont.continuousAt

/-- Two regular measures on `SL₃(ℝ)` with equal integrals against all test functions coincide. -/
theorem measure_eq_of_lintegral_cc_eq (μ ν : Measure SL3) [μ.Regular] [ν.Regular]
    (h : ∀ f : C_c(SL3, ℝ≥0), ∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∫⁻ x, (f x : ℝ≥0∞) ∂ν) : μ = ν := by
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have hf : ∀ (ρ : Measure SL3) [ρ.Regular], ∫ x, (f x : ℝ) ∂ρ
      = (∫⁻ x, (f x : ℝ≥0∞) ∂ρ).toReal := by
    intro ρ _
    refine (integral_eq_lintegral_of_nonneg_ae (μ := ρ) (f := fun x : SL3 => (f x : ℝ))
      (Filter.Eventually.of_forall fun x => (f x).2)
      ((continuous_subtype_val.comp f.1.continuous).measurable).aestronglyMeasurable).trans ?_
    congr 1
    refine lintegral_congr fun x => ?_
    simp
  rw [hf μ, hf ν, h f]

/-- **Closedness of the quasi-invariance set** of a non-zero Radon measure. -/
theorem isClosed_quasiInvSet (σ : Measure SL3) (hσ : IsFiniteMeasureOnCompacts σ)
    (hσ0 : σ ≠ 0) :
    IsClosed {u : SL3 | ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ σ.map (fun g => u * g) = c • σ} := by
  classical
  haveI := hσ
  set S : Set SL3 := {u : SL3 | ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
    σ.map (fun g => u * g) = c • σ} with hS
  set T : Set SL3 := {u : SL3 | ∀ f g : C_c(SL3, ℝ≥0),
    testMass σ f u * testMass σ g 1 = testMass σ g u * testMass σ f 1} with hT
  have hex : ∃ f : C_c(SL3, ℝ≥0), testMass σ f 1 ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hzero : σ = 0 := by
      refine measure_eq_of_lintegral_cc_eq σ 0 (fun f => ?_)
      have h1 : testMass σ f 1 = ∫⁻ x, (f x : ℝ≥0∞) ∂σ := by rw [testMass]; simp
      rw [← h1, h f]
      simp
    exact hσ0 hzero
  obtain ⟨f₀, hf₀⟩ := hex
  have hf₀top : testMass σ f₀ 1 ≠ ⊤ := (testMass_lt_top σ hσ f₀ 1).ne
  have hTS : T ⊆ S := by
    intro u hu
    set c : ℝ≥0∞ := testMass σ f₀ u / testMass σ f₀ 1 with hc
    have hgc : ∀ g : C_c(SL3, ℝ≥0), testMass σ g u = c * testMass σ g 1 := by
      intro g
      have h1 : testMass σ g u * testMass σ f₀ 1 = testMass σ f₀ u * testMass σ g 1 := hu g f₀
      have hcalc : c * testMass σ g 1 = testMass σ g u := by
        calc c * testMass σ g 1
            = ((testMass σ f₀ 1)⁻¹ * testMass σ f₀ u) * testMass σ g 1 := by
              rw [hc, ENNReal.div_eq_inv_mul]
          _ = (testMass σ f₀ u * (testMass σ f₀ 1)⁻¹) * testMass σ g 1 := by
              rw [mul_comm (testMass σ f₀ 1)⁻¹ (testMass σ f₀ u)]
          _ = testMass σ f₀ u * ((testMass σ f₀ 1)⁻¹ * testMass σ g 1) := by rw [mul_assoc]
          _ = testMass σ f₀ u * (testMass σ g 1 * (testMass σ f₀ 1)⁻¹) := by
              rw [mul_comm (testMass σ f₀ 1)⁻¹ (testMass σ g 1)]
          _ = (testMass σ f₀ u * testMass σ g 1) * (testMass σ f₀ 1)⁻¹ := by rw [mul_assoc]
          _ = (testMass σ g u * testMass σ f₀ 1) * (testMass σ f₀ 1)⁻¹ := by rw [h1]
          _ = testMass σ g u * (testMass σ f₀ 1 * (testMass σ f₀ 1)⁻¹) := by rw [mul_assoc]
          _ = testMass σ g u * 1 := by rw [ENNReal.mul_inv_cancel hf₀ hf₀top]
          _ = testMass σ g u := by rw [mul_one]
      exact hcalc.symm
    have hcT : c ≠ ⊤ := by
      intro hctop
      have h1 := hgc f₀
      rw [hctop, ENNReal.top_mul hf₀] at h1
      exact (ne_of_lt (testMass_lt_top σ hσ f₀ u)) h1
    haveI hreg : (c • σ).Regular := MeasureTheory.Measure.Regular.smul (μ := σ) hcT
    haveI hmreg : IsFiniteMeasureOnCompacts (σ.map (fun g : SL3 => u * g)) :=
      isFiniteMeasureOnCompacts_map_mulLeft σ hσ u
    have hmap : σ.map (fun g : SL3 => u * g) = c • σ := by
      refine measure_eq_of_lintegral_cc_eq _ _ fun f => ?_
      rw [← testMass_eq_lintegral_map σ f u, MeasureTheory.lintegral_smul_measure, hgc f,
        show testMass σ f 1 = ∫⁻ x, (f x : ℝ≥0∞) ∂σ by rw [testMass]; simp, smul_eq_mul]
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : σ.map (fun g : SL3 => u * g) = 0 := by
        refine measure_eq_of_lintegral_cc_eq _ 0 fun f => ?_
        rw [← testMass_eq_lintegral_map σ f u, hgc f, hc0, zero_mul]
        simp
      have hcomp : σ.map ((fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g)) = 0 := by
        rw [← Measure.map_map (by fun_prop : Measurable fun g : SL3 => u⁻¹ * g)
          (by fun_prop : Measurable fun g : SL3 => u * g), hzero, Measure.map_zero]
      have hid : ((fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g)) = id := by
        funext g
        simp only [Function.comp_apply, id_eq]
        rw [inv_mul_cancel_left]
      rw [hid, Measure.map_id] at hcomp
      exact hσ0 hcomp
    exact ⟨c, hc0, hcT, hmap⟩
  have hST : S ⊆ T := by
    intro u ⟨c, hc0, hcT, hcu⟩
    intro f g
    rw [testMass_eq_lintegral_map σ f u, testMass_eq_lintegral_map σ g u, hcu,
      MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_smul_measure]
    rw [show testMass σ g 1 = ∫⁻ x, (g x : ℝ≥0∞) ∂σ by rw [testMass]; simp,
      show testMass σ f 1 = ∫⁻ x, (f x : ℝ≥0∞) ∂σ by rw [testMass]; simp,
      smul_eq_mul, smul_eq_mul]
    ac_rfl
  have hTclosed : IsClosed T := by
    rw [hT]
    rw [show {u : SL3 | ∀ f g : C_c(SL3, ℝ≥0),
        testMass σ f u * testMass σ g 1 = testMass σ g u * testMass σ f 1}
        = ⋂ f : C_c(SL3, ℝ≥0), ⋂ g : C_c(SL3, ℝ≥0),
            {u : SL3 | testMass σ f u * testMass σ g 1
              = testMass σ g u * testMass σ f 1} from by ext u; simp]
    refine isClosed_iInter fun f => isClosed_iInter fun g => ?_
    refine isClosed_eq ?_ ?_
    · exact (ENNReal.continuous_mul_const (testMass_lt_top σ hσ g 1).ne).comp
        (testMass_continuous σ hσ f)
    · exact (ENNReal.continuous_mul_const (testMass_lt_top σ hσ f 1).ne).comp
        (testMass_continuous σ hσ g)
  have hSTeq : S = T := Set.Subset.antisymm hST hTS
  rw [hSTeq]
  exact hTclosed


/-- **A.e. left quasi-invariance of the leafwise measures**, for all of `U` at once. -/
theorem leftQuasiInvariance (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (t0 : Fin 3 → ℝ) (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (hinv : IsUInvariant μ U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1) :
    ∀ᵐ x ∂μ, x ∈ X' → ∀ u ∈ U, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (ν x).map (fun g : SL3 => u * g) = c • ν x := by
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense (↥(U : Set SL3))
  haveI : Countable ↥S := hScount.to_subtype
  have hper : ∀ᵐ x ∂μ, ∀ s : ↥S, (x ∈ X' → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (ν x).map (fun g : SL3 => ((s : ↥(U : Set SL3)) : SL3) * g) = c • ν x) := by
    rw [ae_all_iff]
    intro s
    exact global_propor h2 U hU t0 hmp hcontr hinv hL hfree ((s : ↥(U : Set SL3))).2
      (fun {Z} {m} hpa => smulMS_propor_inv h2 U hU hinv ((s : ↥(U : Set SL3))).2 hL hfree hpa)
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff]; exact hL.conull
  filter_upwards [hper, hX'] with x hx hxX
  intro _ u hu
  have hsub : (S : Set ↥(U : Set SL3))
      ⊆ (fun s : ↥(U : Set SL3) => (s : SL3)) ⁻¹' {u : SL3 | ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
          (ν x).map (fun g : SL3 => u * g) = c • ν x} := by
    intro s hs
    exact hx ⟨s, hs⟩ hxX
  have hcl : IsClosed {u : SL3 | ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (ν x).map (fun g : SL3 => u * g) = c • ν x} :=
    isClosed_quasiInvSet (ν x) (hL.radon x hxX) (by
      intro h0
      have h1 := hL.normalised x hxX
      rw [h0] at h1
      simp at h1)
  have hclU : IsClosed ((fun s : ↥(U : Set SL3) => (s : SL3)) ⁻¹' {u : SL3 |
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (ν x).map (fun g : SL3 => u * g) = c • ν x}) :=
    hcl.preimage continuous_subtype_val
  have hclosed := hclU.closure_subset_iff.mpr hsub
  rw [hSdense.closure_eq] at hclosed
  exact hclosed (Set.mem_univ ⟨u, hu⟩)

/-- **The `(U4)` forward direction**: an invariant probability measure has a.e. right-invariant
leafwise measures. -/
theorem aeHaar_of_Uinvariant (h2 : P_X3) {μ : Measure X3} [IsProbabilityMeasure μ] (U : Subgroup SL3)
    (hU : IsHoro U) (t0 : Fin 3 → ℝ) (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ w ∈ U, w • x = x → w = 1)
    (hinv : IsUInvariant μ U) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x := by
  have hleft := leftQuasiInvariance h2 U hU t0 hmp hcontr hinv hL hfree
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff]; exact hL.conull
  have h5 := Work.EKLRelCross.leafwise_propor h2 μ U hU t0 hmp hcontr ν X' hL
  filter_upwards [hleft, hX', h5] with x hx hxX h5x
  intro u hu
  have hne : ν x ≠ 0 := by
    intro h0
    have h1 := hL.normalised x hxX
    rw [h0] at h1
    simp at h1
  obtain ⟨c, hc0, hcT, hc⟩ := Work.EKLRelCross.rightQuasiInv U hU (ν x) (hL.radon x hxX)
    (hL.carried x hxX) hne (fun v hv => hx hxX v hv) u hu
  exact h5x u hu c hc

/-- **(U4)** of the frozen contract: `μ` is `U`-invariant if and only if the leafwise measures
are a.e. right-`U`-invariant. -/
theorem leaf_invariant (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsUInvariant μ U ↔ ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x := by
  constructor
  · intro hinv
    exact aeHaar_of_Uinvariant prove_X3 U hU t0 hmp hcontr ν X' hL
      (ae_freeness U hU μ t0 hmp hcontr) hinv
  · intro hae
    have hae' : Work.EKLRelCross.AeHaar μ U ν := hae
    exact Work.EKLRelCross.isUInvariant_of_ae_translation prove_X3 μ U hU t0 hmp hcontr ν X' hL hae'

end
end Work.EKLComp
