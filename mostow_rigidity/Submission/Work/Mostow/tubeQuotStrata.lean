import Mathlib
import Submission.Work.Mostow.fermi_measurePreserving
import Submission.Work.Mostow.tubeMeasure_ball2
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.volH_fermi_prod
import Submission.Work.Mostow.fermi_image_measurable
import Submission.Work.Mostow.tubeUnfoldStrata
import Submission.Work.Mostow.resStdDiscreteStrata
import Submission.Work.Mostow.cardKAux
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.fundamentalDomain_inter_invariant
import Submission.Work.Mostow.centralizer_acts_fermi

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Pointwise

noncomputable section

lemma tqs_fermi_zero (j m : ℕ) (v : E j) : fermi j m v 0 = coordEmb j m v := by
  rw [fermi, coordEmb, norm_zero, Real.cosh_zero]
  apply WithLp.ofLp_injective
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp
  · simp [sinhc]

lemma tqs_fermi_zero_zero (j m : ℕ) : fermi j m (0 : E j) (0 : E m) = (0 : E (j + m)) := by
  rw [tqs_fermi_zero]
  apply WithLp.ofLp_injective
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [coordEmb]

lemma tqs_norm_nrmC_fermi (j m : ℕ) (v : E j) (w : E m) :
    ‖nrmC j m (fermi j m v w)‖ = Real.sinh ‖w‖ := by
  rw [nib_nrmC_fermi, norm_smul, Real.norm_eq_abs, abs_of_pos (fermi_sinhc_pos ‖w‖),
    fermi_sinhc_mul_self]

/-- The action of a subgroup on the chart agrees with the action of the ambient group. -/
lemma tqs_smul_coe {n : ℕ} {C : Subgroup (PO n 1)} (c : ↥C) (x : E n) :
    c • x = (c : PO n 1) • x := rfl


/-- If `g` stabilises the standard stratum, so does `g⁻¹`. -/
lemma tqs_inv_mem_SetStabStd (j m : ℕ) (hA : POActionProp (j + m)) {g : PO (j + m) 1}
    (hg : g ∈ SetStabStd j m) : g⁻¹ ∈ SetStabStd j m := by
  letI : MulAction (PO (j + m) 1) (E (j + m)) :=
    { one_smul := hA.2.2.2.1, mul_smul := hA.2.2.2.2.1 }
  intro u
  rw [hg (g⁻¹ • u), ← hA.2.2.2.2.1, mul_inv_cancel, hA.2.2.2.1]

/-- A centraliser element of `blk j m 1 R` (with `R` having no nonzero fixed vector) lies in the
setwise stabiliser of the standard stratum. -/
lemma tqs_centralizer_mem_SetStabStd (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hnfv : ∀ w, R w = w → w = 0)
    {c : PO (j + m) 1}
    (hc : c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1))) :
    c ∈ SetStabStd j m := by
  letI : MulAction (PO (j + m) 1) (E (j + m)) :=
    { one_smul := hA.2.2.2.1, mul_smul := hA.2.2.2.2.1 }
  letI : MulAction (PO j 1) (E j) :=
    { one_smul := hAj.2.2.2.1, mul_smul := hAj.2.2.2.2.1 }
  have hact := centralizer_acts_fermi j m hAj hIj hA hI R hnfv
  have hbmem : (blk j m 1 R) ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => by rw [Set.mem_singleton_iff.mp hy])
  -- the standard stratum is exactly the zero-normal-vector set
  have hstd : ∀ u : E (j + m), u ∈ stdTG j m ↔ nrmC j m u = 0 := by
    intro u
    constructor
    · rintro ⟨v₀, rfl⟩
      rw [← tqs_fermi_zero j m v₀, nib_nrmC_fermi]
      simp
    · intro hu
      obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
      have h2 : sinhc ‖w‖ • w = 0 := by rw [← nib_nrmC_fermi]; exact hu
      have hw : w = 0 := by
        have h3 := congrArg (fun z : E m => (sinhc ‖w‖)⁻¹ • z) h2
        simpa [smul_smul, inv_mul_cancel₀ (fermi_sinhc_ne_zero ‖w‖)] using h3
      rw [hw, tqs_fermi_zero]
      exact ⟨v, rfl⟩
  -- fixed set of the block element
  have hfixb : ∀ u : E (j + m), (blk j m 1 R) • u = u ↔ u ∈ stdTG j m := by
    intro u
    constructor
    · intro hu
      obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
      rw [hact (blk j m 1 R) hbmem v w, resStd_blk j m hAj hIj hA hI,
        nrmStd_blk j m hAj hIj hA hI] at hu
      have h3 := congrArg (fermiInv j m) hu
      rw [(fermi_inv j m).1, (fermi_inv j m).1] at h3
      have h4 : R w = w := (Prod.ext_iff.mp h3).2
      have hw : w = 0 := hnfv w h4
      rw [hw, tqs_fermi_zero]
      exact ⟨v, rfl⟩
    · rintro ⟨v₀, rfl⟩
      rw [← tqs_fermi_zero j m v₀, hact (blk j m 1 R) hbmem v₀ 0, resStd_blk j m hAj hIj hA hI,
        nrmStd_blk j m hAj hIj hA hI, map_zero, hAj.2.2.2.1]
  -- `c` commutes with `blk j m 1 R`
  have hcomm : c * (blk j m 1 R) = (blk j m 1 R) * c :=
    ((Subgroup.mem_centralizer_iff.mp hc) (blk j m 1 R) (Set.mem_singleton _)).symm
  have hpres : ∀ u : E (j + m), (blk j m 1 R) • (c • u) = c • u ↔ (blk j m 1 R) • u = u := by
    intro u
    constructor
    · intro hu
      have h2 : c • ((blk j m 1 R) • u) = c • u := by
        rw [← hA.2.2.2.2.1 c (blk j m 1 R) u, hcomm, hA.2.2.2.2.1 (blk j m 1 R) c u, hu]
      have h3 : c⁻¹ • (c • ((blk j m 1 R) • u)) = c⁻¹ • (c • u) := by rw [h2]
      rw [← hA.2.2.2.2.1 c⁻¹ c ((blk j m 1 R) • u), inv_mul_cancel, hA.2.2.2.1,
        ← hA.2.2.2.2.1 c⁻¹ c u, inv_mul_cancel, hA.2.2.2.1] at h3
      exact h3
    · intro hu
      rw [← hA.2.2.2.2.1 (blk j m 1 R) c u, ← hcomm, hA.2.2.2.2.1 c (blk j m 1 R) u, hu]
  intro u
  rw [← hfixb u, ← hpres u, hfixb (c • u)]


/-- The tube about the standard stratum is invariant under the centraliser of `blk j m 1 R`. -/
lemma tqs_tube_smul_eq (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (Λ : Subgroup (PO (j + m) 1)) (ρ : ℝ)
    (hblk : ∀ c ∈ (Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)),
      ∀ (v : E j) (w : E m),
        (c : PO (j + m) 1) • fermi j m v w
          = fermi j m (resStd j m (c : PO (j + m) 1) • v) (nrmStd j m (c : PO (j + m) 1) w)) :
    ∀ c ∈ (Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)),
      (fun u : E (j + m) => (c : PO (j + m) 1) • u) '' tube j m ρ = tube j m ρ := by
  letI : MulAction (PO (j + m) 1) (E (j + m)) :=
    { one_smul := hA.2.2.2.1, mul_smul := hA.2.2.2.2.1 }
  intro c hc
  have key : ∀ d ∈ (Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)),
      ∀ u : E (j + m), u ∈ tube j m ρ → (d : PO (j + m) 1) • u ∈ tube j m ρ := by
    intro d hd u hu
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
    have h1 : Real.sinh ‖w‖ ≤ Real.sinh ρ := by
      simpa only [tube, Set.mem_setOf_eq, tqs_norm_nrmC_fermi] using hu
    rw [hblk d hd v w]
    simp only [tube, Set.mem_setOf_eq, tqs_norm_nrmC_fermi, LinearIsometryEquiv.norm_map]
    exact h1
  apply Set.Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    exact key c hc u hu
  · intro z hz
    exact ⟨(c⁻¹ : PO (j + m) 1) • z,
      key c⁻¹ ((Subgroup.centralizer {blk j m 1 R} ⊓ Λ).inv_mem hc) z hz, by
        show c • (c⁻¹ • z) = z
        rw [← hA.2.2.2.2.1 c c⁻¹ z, mul_inv_cancel, hA.2.2.2.1]⟩

/-! **(II) of the strata chapter: the volume of the Fermi tube modulo the centraliser.**

Setting: `Λ ≤ PO (j+m) 1` discrete, `b = blk j m 1 R ∈ Λ` with `R` having no fixed vector,
`C := Subgroup.centralizer {b} ⊓ Λ`, `Dc` a fundamental domain of `C`, `DY` a fundamental domain
of the image `resStd j m '' C` on the stratum, `ρ ≥ 0`, and
`K := {c : PO (j+m) 1 // c ∈ Λ ∧ c ∈ centralizer {b} ∧ resStd j m c = 1}` (this `K` is FINITE:
its elements lie in the pointwise stabiliser of the stratum, which is a compact group intersected
with the discrete `Λ`, e.g. via `Work.Mostow.finite_nearStab` + `Work.Mostow.stab_eq_blk`; so
`Nat.card K ≥ 1` and there is no `Nat.card = 0` degeneracy).

Because `R` has no fixed vector, `Fix b = stdTG j m`; `hblk` says every `c ∈ C` acts on Fermi
coordinates as `(v, w) ↦ (resStd j m c • v, nrmStd j m c • w)` (this is
`Work.Mostow.blk_smul_fermi` + `Work.Mostow.stab_eq_blk`, both PROVED), so `C` preserves the tube
`tube j m ρ` and the `C`-quotient of the tube is the product of `Y / resStd C` (fundamental domain
`DY`) with the normal ball modulo `K`.

Route (two ingredients).
* `Work.Mostow.fermi_measurePreserving`: the Fermi chart `(v,w) ↦ fermi j m v w` is
  measure-preserving from `(volH j).prod (tubeMeasure j m)` to `volH (j+m)`, and it is injective
  (`Work.Mostow.fermi_inv`), so for the measurable set `F := fermi '' (DY ×ˢ closedBall 0 ρ)`,
  `volH (j+m) F = volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ)`, and `F ⊆ tube j m ρ`.
* `Work.Mostow.volH_le_card_mul_of_ae_count` with the group `C`, the measure
  `(volH (j+m)).restrict (tube j m ρ)`, the fundamental domain `tube j m ρ ∩ Dc` (a.e. one for the
  `C`-action on the `C`-invariant tube) and the set `F`: for a.e. `z` in the tube, if `c ∈ C` has
  `c • z ∈ F`, then the foot of `c • z` lies in `DY`; by `hblk` the foot of `c • z` is
  `resStd j m c • (foot z)`, and `DY` being a fundamental domain of `resStd j m '' C` forces
  `resStd j m c` to be one fixed element (a.e. in `z`), i.e. `c` lies in a coset of `K`.  Hence the
  count is at most `|K|` and `volH (j+m) F ≤ |K| * volH (j+m) (tube j m ρ ∩ Dc)`, which is the
  claim. -/
theorem tubeQuotStrata (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m)) (Λ : Subgroup (PO (j + m) 1)) (R : E m ≃ₗᵢ[ℝ] E m) (Dc : Set (E (j + m))) (DY : Set (E j)) (ρ : ℝ) (hρ : 0 ≤ ρ) (hdis : IsDiscrete (SetLike.coe Λ)) (hb : blk j m 1 R ∈ Λ) (hnfv : ∀ w, R w = w → w = 0) (hblk : ∀ c ∈ (Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)), ∀ (v : E j) (w : E m), (c : PO (j + m) 1) • fermi j m v w = fermi j m (resStd j m (c : PO (j + m) 1) • v) (nrmStd j m (c : PO (j + m) 1) w)) (hDc : IsFundamentalDomain (↑(Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1))) Dc (volH (j + m))) (hDY : IsFundamentalDomain (Subgroup.closure (resStd j m '' ((Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1)) : Set (PO (j + m) 1)))) DY (volH j)) : volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ) ≤ (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : ENNReal) * volH (j + m) (tube j m ρ ∩ Dc) := by
  classical
  have hOne : ∀ u : E (j + m), (1 : PO (j + m) 1) • u = u := hA.2.2.2.1
  have hMul : ∀ (g h : PO (j + m) 1) (u : E (j + m)), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hOnej : ∀ u : E j, (1 : PO j 1) • u = u := hAj.2.2.2.1
  have hMulj : ∀ (g h : PO j 1) (u : E j), (g * h) • u = g • (h • u) := hAj.2.2.2.2.1
  have hContDiff : ∀ g : PO (j + m) 1, ContDiff ℝ 1 (fun u : E (j + m) => g • u) :=
    hI.2.2.2.2.2.2.2.2.1
  have hMP : ∀ g : PO (j + m) 1,
      MeasurePreserving (fun u : E (j + m) => g • u) (volH (j + m)) (volH (j + m)) :=
    hI.2.2.2.2.2.2.2.2.2.2.2.1
  have hMPj : ∀ g : PO j 1, MeasurePreserving (fun u : E j => g • u) (volH j) (volH j) :=
    hIj.2.2.2.2.2.2.2.2.2.2.2.1
  have hdist0 : ∀ u v : E (j + m), hdist u v = 0 ↔ u = v := hI.2.2.1
  letI : MulAction (PO (j + m) 1) (E (j + m)) := { one_smul := hOne, mul_smul := hMul }
  letI : MulAction (PO j 1) (E j) := { one_smul := hOnej, mul_smul := hMulj }
  set C : Subgroup (PO (j + m) 1) := Subgroup.centralizer {blk j m 1 R} ⊓ Λ with hCdef
  set H : Subgroup (PO j 1) := Subgroup.closure (resStd j m '' (C : Set (PO (j + m) 1))) with hHdef
  set K : Type _ := {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} with hKdef
  set Ty : Set (E (j + m)) := tube j m ρ with hTydef
  set ball : Set (E m) := Metric.closedBall 0 ρ with hballdef
  haveI : Countable ↥C := by
    have hΛc : (↑Λ : Set (PO (j + m) 1)).Countable := countable_of_isDiscrete _ hdis
    exact (hΛc.mono (fun x hx => (Subgroup.mem_inf.mp hx).2)).to_subtype
  haveI : MeasurableConstSMul ↥C (E (j + m)) :=
    ⟨fun c => (hContDiff (c : PO (j + m) 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure ↥C (E (j + m)) (volH (j + m)) :=
    ⟨fun c s hs => (hMP (c : PO (j + m) 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : SMulInvariantMeasure ↥H (E j) (volH j) :=
    ⟨fun c s hs => (hMPj (c : PO j 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : SMulInvariantMeasure (PO (j + m) 1) (E (j + m)) (volH (j + m)) :=
    ⟨fun c s hs => (hMP c).measure_preimage hs.nullMeasurableSet⟩
  haveI : SMulInvariantMeasure (PO j 1) (E j) (volH j) :=
    ⟨fun c s hs => (hMPj c).measure_preimage hs.nullMeasurableSet⟩
  have hCstab : ∀ c ∈ C, (c : PO (j + m) 1) ∈ SetStabStd j m :=
    fun c hc => tqs_centralizer_mem_SetStabStd j m hAj hIj hA hI R hnfv (Subgroup.mem_inf.mp hc).1
  have hTymeas : MeasurableSet Ty := by
    rw [hTydef]; exact (tu_isClosed_tube j m ρ).measurableSet
  have hTyinv0 : ∀ c : ↥C,
      (fun x : E (j + m) => c • x) '' tube j m ρ = tube j m ρ :=
    fun c => tqs_tube_smul_eq j m hAj hIj hA hI R Λ ρ hblk (c : PO (j + m) 1) c.2
  have hTyinv : ∀ c : ↥C, (fun x : E (j + m) => c • x) '' Ty = Ty := by
    intro c
    rw [hTydef]
    exact hTyinv0 c
  have hDc' : IsFundamentalDomain ↥C (Ty ∩ Dc) ((volH (j + m)).restrict Ty) := by
    have h := fundamentalDomain_inter_invariant (G := ↥C) (α := E (j + m)) (volH (j + m))
      hTymeas hTyinv hDc
    exact h
  haveI : SMulInvariantMeasure ↥C (E (j + m)) ((volH (j + m)).restrict Ty) := by
    refine ⟨fun c s hs => ?_⟩
    have hTy_c : (c : PO (j + m) 1) • Ty = Ty := by
      rw [hTydef]
      exact tqs_tube_smul_eq j m hAj hIj hA hI R Λ ρ hblk (c : PO (j + m) 1) c.2
    have hpre : (fun x : E (j + m) => c • x) ⁻¹' s = (c : PO (j + m) 1)⁻¹ • s := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inv_smul_set_iff, tqs_smul_coe]
    rw [hpre, Measure.restrict_apply₀' hTymeas.nullMeasurableSet,
      Measure.restrict_apply₀' hTymeas.nullMeasurableSet,
      measure_inv_smul_inter (volH (j + m)) (c : PO (j + m) 1) s Ty, hTy_c]
  set A' : Set (E j) := toMeasurable (volH j) DY with hA'def
  set F : Set (E (j + m)) := (fun p : E j × E m => fermi j m p.1 p.2) '' (DY ×ˢ ball) with hFdef
  set F' : Set (E (j + m)) := (fun p : E j × E m => fermi j m p.1 p.2) '' (A' ×ˢ ball) with hF'def
  have hA'meas : MeasurableSet A' := by rw [hA'def]; exact measurableSet_toMeasurable _ _
  have hDYA' : DY ⊆ A' := by rw [hA'def]; exact subset_toMeasurable _ _
  have hA'vol : volH j A' = volH j DY := by rw [hA'def]; exact measure_toMeasurable _
  have hnull_diff : volH j (A' \ DY) = 0 := by
    have hae : A' =ᵐ[volH j] DY := by rw [hA'def]; exact hDY.nullMeasurableSet.toMeasurable_ae_eq
    exact (ae_eq_set.mp hae).1
  have hball_meas : MeasurableSet ball := by rw [hballdef]; exact Metric.isClosed_closedBall.measurableSet
  have hF'meas : MeasurableSet F' := by
    rw [hF'def]; exact fermi_image_measurable j m A' ball hA'meas hball_meas
  have hF'sub : F ⊆ F' := by
    rw [hFdef, hF'def]
    exact Set.image_mono (Set.prod_mono hDYA' (subset_refl ball))
  have hnullF'F : volH (j + m) (F' \ F) = 0 := by
    have hsub : F' \ F ⊆ (fun p : E j × E m => fermi j m p.1 p.2) ''
        ((toMeasurable (volH j) (A' \ DY)) ×ˢ ball) := by
      intro y hy
      obtain ⟨hyF', hyF⟩ := hy
      rw [hF'def] at hyF'
      obtain ⟨q, hq, hqe⟩ := hyF'
      have hq2 : q.1 ∉ DY := by
        intro hqd
        exact hyF (by rw [hFdef]; exact ⟨q, ⟨hqd, hq.2⟩, hqe⟩)
      exact ⟨q, ⟨subset_toMeasurable _ _ ⟨hq.1, hq2⟩, hq.2⟩, hqe⟩
    refine measure_mono_null hsub ?_
    rw [volH_fermi_prod j m _ ball (measurableSet_toMeasurable _ _) hball_meas]
    rw [show volH j (toMeasurable (volH j) (A' \ DY)) = 0 from by rw [measure_toMeasurable, hnull_diff]]
    rw [zero_mul]
  have hF_null : NullMeasurableSet F (volH (j + m)) := by
    have h1 : NullMeasurableSet (F' \ F) (volH (j + m)) := NullMeasurableSet.of_null hnullF'F
    have hEq : F = F' ∩ (F' \ F)ᶜ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [hEq]
    exact hF'meas.nullMeasurableSet.inter h1.compl
  have hF_vol : volH (j + m) F = volH j DY * tubeMeasure j m ball := by
    have hle1 : volH (j + m) F ≤ volH (j + m) F' := measure_mono hF'sub
    have hF'vol : volH (j + m) F' = volH j DY * tubeMeasure j m ball := by
      rw [hF'def, volH_fermi_prod j m A' ball hA'meas hball_meas, hA'vol]
    have hle2 : volH (j + m) F' ≤ volH (j + m) F := by
      have hunion : F ∪ (F' \ F) = F' := by
        ext y
        constructor
        · rintro (hy | ⟨hyF', -⟩)
          · exact hF'sub hy
          · exact hyF'
        · intro hy
          by_cases h : y ∈ F
          · exact Or.inl h
          · exact Or.inr ⟨hy, h⟩
      calc volH (j + m) F' = volH (j + m) (F ∪ (F' \ F)) := by rw [hunion]
        _ ≤ volH (j + m) F + volH (j + m) (F' \ F) := measure_union_le _ _
        _ = volH (j + m) F := by rw [hnullF'F, add_zero]
    rw [le_antisymm hle1 hle2, hF'vol]
  have hFsubTy : F ⊆ Ty := by
    rw [hFdef, hTydef]
    rintro y ⟨q, hq, rfl⟩
    simp only [tube, Set.mem_setOf_eq, tqs_norm_nrmC_fermi]
    have hqB : ‖q.2‖ ≤ ρ := by
      have h := hq.2
      rw [hballdef, Metric.mem_closedBall, dist_zero_right] at h
      exact h
    exact (Real.sinh_le_sinh).mpr hqB
  set s : Set (E (j + m)) := Ty ∩ Dc with hsdef
  set μ' : Measure (E (j + m)) := (volH (j + m)).restrict Ty with hμ'def
  obtain ⟨t₀, ht₀sub, ht₀meas, ht₀ae⟩ := hF_null.exists_measurable_subset_ae_eq
  have ht₀vol : volH (j + m) t₀ = volH (j + m) F := measure_congr ht₀ae
  let Foot : E (j + m) → E j := fun z => (fermiInv j m z).1
  have hmemH : ∀ c : ↥C, resStd j m (c : PO (j + m) 1) ∈ H :=
    fun c => Subgroup.subset_closure (Set.mem_image_of_mem (f := resStd j m) c.2)
  let hOf : ↥C → ↥H := fun c => ⟨resStd j m (c : PO (j + m) 1), hmemH c⟩
  have hOf_coe : ∀ c : ↥C, (hOf c : PO j 1) = resStd j m (c : PO (j + m) 1) := fun c => rfl
  have footmem : ∀ (d : ↥C) (z : E (j + m)), d • z ∈ F →
      resStd j m (d : PO (j + m) 1) • Foot z ∈ DY := by
    intro d z hd
    rw [hFdef] at hd
    obtain ⟨q, hq, hqe⟩ := hd
    have h1 : fermi j m (resStd j m (d : PO (j + m) 1) • Foot z)
        (nrmStd j m (d : PO (j + m) 1) (fermiInv j m z).2) = fermi j m q.1 q.2 := by
      calc fermi j m (resStd j m (d : PO (j + m) 1) • Foot z)
            (nrmStd j m (d : PO (j + m) 1) (fermiInv j m z).2)
          = (d : PO (j + m) 1) • fermi j m (Foot z) ((fermiInv j m z).2) :=
            (hblk (d : PO (j + m) 1) d.2 (Foot z) ((fermiInv j m z).2)).symm
        _ = (d : PO (j + m) 1) • z := by rw [(fermi_inv j m).2.1]
        _ = d • z := tqs_smul_coe d z
        _ = fermi j m q.1 q.2 := hqe.symm
    have h2 := congrArg (fermiInv j m) h1
    rw [(fermi_inv j m).1, (fermi_inv j m).1] at h2
    have h3 : resStd j m (d : PO (j + m) 1) • Foot z = q.1 := (Prod.ext_iff.mp h2).1
    rw [h3]
    exact hq.1
  let Idx : Type _ := {q : ↥C × ↥C // resStd j m (Subtype.val q.1) ≠ resStd j m (Subtype.val q.2)}
  haveI : Countable Idx := inferInstance
  let Vb : Idx → Set (E j) := fun p => toMeasurable (volH j)
    {v : E j | (hOf p.1.1) • v ∈ DY ∧ (hOf p.1.2) • v ∈ DY}
  let BadI : Idx → Set (E (j + m)) := fun p =>
    (fun q : E j × E m => fermi j m q.1 q.2) '' (Vb p ×ˢ Set.univ)
  have hBadI_vol : ∀ p : Idx, volH (j + m) (BadI p) = 0 := by
    intro p
    have hVb : volH j (Vb p) = 0 := by
      rw [show Vb p = toMeasurable (volH j)
          {v : E j | (hOf p.1.1) • v ∈ DY ∧ (hOf p.1.2) • v ∈ DY} from rfl, measure_toMeasurable]
      refine measure_mono_null (t := (hOf p.1.1)⁻¹ • DY ∩ (hOf p.1.2)⁻¹ • DY) ?_ ?_
      · intro v hv
        exact ⟨Set.mem_inv_smul_set_iff.mpr hv.1, Set.mem_inv_smul_set_iff.mpr hv.2⟩
      · rw [measure_inv_smul_inter (volH j) (hOf p.1.1) DY ((hOf p.1.2)⁻¹ • DY)]
        have hsm : (hOf p.1.1) • ((hOf p.1.2)⁻¹ • DY) = ((hOf p.1.1) * (hOf p.1.2)⁻¹) • DY := by
          rw [smul_smul]
        rw [hsm, Set.inter_comm]
        have hne : ((hOf p.1.1) * (hOf p.1.2)⁻¹ : ↥H) ≠ 1 := by
          intro hcon
          have h1 : hOf p.1.1 = hOf p.1.2 := mul_inv_eq_one.mp hcon
          exact p.2 (by rw [← hOf_coe p.1.1, ← hOf_coe p.1.2, h1])
        have hz := hDY.aedisjoint hne
        simp only [AEDisjoint] at hz
        rwa [one_smul] at hz
    rw [show BadI p = (fun q : E j × E m => fermi j m q.1 q.2) '' (Vb p ×ˢ Set.univ) from rfl,
      volH_fermi_prod j m (Vb p) Set.univ (measurableSet_toMeasurable _ _) MeasurableSet.univ,
      hVb, zero_mul]
  have hBad_null : volH (j + m) (⋃ p, BadI p) = 0 := by
    rw [measure_iUnion_null_iff]
    exact hBadI_vol
  have hBadProp_sub : {z : E (j + m) | ∃ c₁ c₂ : ↥C,
      resStd j m (c₁ : PO (j + m) 1) ≠ resStd j m (c₂ : PO (j + m) 1) ∧
      resStd j m (c₁ : PO (j + m) 1) • Foot z ∈ DY ∧
      resStd j m (c₂ : PO (j + m) 1) • Foot z ∈ DY} ⊆ ⋃ p, BadI p := by
    rintro z ⟨c₁, c₂, hne, h1, h2⟩
    refine Set.mem_iUnion.mpr ⟨⟨(c₁, c₂), hne⟩, ?_⟩
    refine ⟨(Foot z, (fermiInv j m z).2), ⟨?_, Set.mem_univ _⟩, (fermi_inv j m).2.1 z⟩
    refine subset_toMeasurable _ _ ?_
    show resStd j m (c₁ : PO (j + m) 1) • Foot z ∈ DY ∧
      resStd j m (c₂ : PO (j + m) 1) • Foot z ∈ DY
    exact ⟨h1, h2⟩
  have hbad_ae : ∀ᵐ z ∂ (μ'.restrict s), ¬ (∃ c₁ c₂ : ↥C,
      resStd j m (c₁ : PO (j + m) 1) ≠ resStd j m (c₂ : PO (j + m) 1) ∧
      resStd j m (c₁ : PO (j + m) 1) • Foot z ∈ DY ∧
      resStd j m (c₂ : PO (j + m) 1) • Foot z ∈ DY) := by
    rw [ae_iff]
    simp only [not_not]
    refine le_antisymm ?_ bot_le
    have hA0 : (μ'.restrict s) (⋃ p, BadI p) ≤ μ' (⋃ p, BadI p) :=
      (Measure.restrict_le_self (μ := μ') (s := s)) _
    have hB0 : μ' (⋃ p, BadI p) ≤ volH (j + m) (⋃ p, BadI p) :=
      (Measure.restrict_le_self (μ := volH (j + m)) (s := Ty)) _
    rw [hBad_null] at hB0
    exact le_trans (measure_mono hBadProp_sub) (le_trans hA0 hB0)
  have hKfin : ({c : PO (j + m) 1 |
      c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : Set (PO (j + m) 1)).Finite := by
    have hnear : ({γ : Λ | hdist (0 : E (j + m)) ((γ : PO (j + m) 1) • (0 : E (j + m))) ≤ 0} : Set Λ).Finite :=
      finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdis 0
    have himg : ({c : PO (j + m) 1 |
        c ∈ Λ ∧ hdist (0 : E (j + m)) (c • (0 : E (j + m))) ≤ 0} : Set (PO (j + m) 1)).Finite := by
      refine (hnear.image (Subtype.val : Λ → PO (j + m) 1)).subset ?_
      rintro c ⟨hcΛ, hc0⟩
      exact ⟨⟨c, hcΛ⟩, hc0, rfl⟩
    refine himg.subset ?_
    rintro c ⟨hcΛ, hcC, hcS⟩
    refine ⟨hcΛ, ?_⟩
    have hmem : c ∈ C := Subgroup.mem_inf.mpr ⟨hcC, hcΛ⟩
    have hc0 : c • (0 : E (j + m)) = 0 := by
      have hf00 : fermi j m (0 : E j) (0 : E m) = (0 : E (j + m)) := tqs_fermi_zero_zero j m
      have hb := hblk c hmem (0 : E j) (0 : E m)
      rw [hf00] at hb
      rw [hb, hcS, hOnej, map_zero, hf00]
    rw [hc0]
    exact le_of_eq (hdist0 0 0 |>.mpr rfl)
  haveI : Fintype K := hKfin.fintype
  have hcount : ∀ᵐ z ∂ (μ'.restrict s), ∃ S : Finset ↥C, S.card ≤ Nat.card K ∧
      ∀ c : ↥C, c • z ∈ t₀ → c ∈ S := by
    filter_upwards [hbad_ae] with z hz
    by_cases hex : ∃ c₀ : ↥C, c₀ • z ∈ t₀
    · obtain ⟨c₀, hc₀⟩ := hex
      have key : ∀ c : ↥C, c • z ∈ t₀ →
          resStd j m (c : PO (j + m) 1) = resStd j m (c₀ : PO (j + m) 1) := by
        intro c hc
        by_contra hneq
        exact hz ⟨c, c₀, hneq, footmem c z (ht₀sub hc), footmem c₀ z (ht₀sub hc₀)⟩
      have hmemC : ∀ k : K, (c₀ : PO (j + m) 1) * (k : PO (j + m) 1) ∈ C := by
        intro k
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp c₀.2).1 k.2.2.1
        · exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp c₀.2).2 k.2.1
      let Φ : K → ↥C := fun k => ⟨(c₀ : PO (j + m) 1) * (k : PO (j + m) 1), hmemC k⟩
      refine ⟨Finset.univ.image Φ, ?_, ?_⟩
      · calc (Finset.univ.image Φ).card ≤ (Finset.univ : Finset K).card := Finset.card_image_le
          _ = Nat.card K := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      · intro c hc
        have hres := key c hc
        have hstab₀ : (c₀ : PO (j + m) 1) ∈ SetStabStd j m := hCstab _ c₀.2
        have hstab : (c : PO (j + m) 1) ∈ SetStabStd j m := hCstab _ c.2
        have hkK : ((c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1)) ∈ Λ ∧
            ((c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1)) ∈ Subgroup.centralizer {blk j m 1 R} ∧
            resStd j m ((c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1)) = 1 := by
          refine ⟨?_, ?_, ?_⟩
          · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp c₀.2).2)
              (Subgroup.mem_inf.mp c.2).2
          · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.mp c₀.2).1)
              (Subgroup.mem_inf.mp c.2).1
          · rw [rhd_resStd_mul j m hAj hIj hA hI (tqs_inv_mem_SetStabStd j m hA hstab₀) hstab,
              rhd_resStd_inv j m hAj hIj hA hI hstab₀, hres, inv_mul_cancel]
        refine Finset.mem_image.mpr ⟨(⟨_, hkK⟩ : K), Finset.mem_univ _, ?_⟩
        refine Subtype.ext ?_
        show (c₀ : PO (j + m) 1) * ((c₀ : PO (j + m) 1)⁻¹ * (c : PO (j + m) 1)) = (c : PO (j + m) 1)
        group
    · push_neg at hex
      exact ⟨∅, by simp, fun c hc => absurd hc (hex c)⟩
  have hmain : volH j DY * tubeMeasure j m ball ≤ (Nat.card K : ENNReal) * volH (j + m) (Ty ∩ Dc) := by
    have hcnt := measure_le_card_mul_of_ae_count (G := ↥C) (α := E (j + m)) μ' hDc' ht₀meas
      (Nat.card K) hcount
    have hL : μ' t₀ = volH j DY * tubeMeasure j m ball := by
      rw [Measure.restrict_apply ht₀meas]
      have hii : t₀ ∩ Ty = t₀ := Set.inter_eq_left.mpr (fun x hx => hFsubTy (ht₀sub hx))
      rw [hii, ht₀vol, hF_vol]
    have hR : μ' (Ty ∩ Dc) = volH (j + m) (Ty ∩ Dc) := by
      rw [Measure.restrict_apply₀' hTymeas.nullMeasurableSet]
      congr 1
      exact Set.inter_eq_left.mpr Set.inter_subset_left
    rw [hL, hR] at hcnt
    exact hcnt
  exact hmain

end

end Work.Mostow
