import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornCov.covering_of_components
import Submission.Work.HornCov.covering_components_homeomorph
import Submission.Work.HornCov.sheet_Phi
import Submission.Work.HornCov.varphi_image
import Submission.Work.HornCov.sheet_varphi

/-!
# `Work.Horn.cov_of_parts` — the covering property of the horn map from the parts

Assembly of `cov_of_parts` from the four piece statements `HornTopoStatement`,
`HornPhiStatement`, `HornVarphiStatement`, `HornSCStatement` (interfaces in
`Submission/Work/Interfaces/HornParts.lean`).

Mathlib's `IsCoveringMapOn f S := ∀ x ∈ S, IsEvenlyCovered f x (f ⁻¹' {x})`.  The proof
uses the two already-delegated covering statements

* `Work.HornCov.sheet_Phi`      : `Φ : B → ℂ` is a covering over `ball y r` when `y` avoids `Φ c - ℕ`,
* `Work.HornCov.sheet_varphi`   : `φ : BuOf ∪ BlOf → B` is a covering over small balls off `critOrbit`,

together with the general topology

* `Work.HornCov.covering_components_homeomorph` : components of a covering over a simply connected
  base map homeomorphically onto the base,
* `Work.HornCov.covering_of_components`         : a disjoint open family of such homeomorphic
  "sheets" covering `f ⁻¹' S` makes `f` a covering over `S`.

The composite `E = Φ ∘ φ` is then a covering over `ℂ ∖ (Φ c + ℤ)` because a component of
`E ⁻¹' U` is a component of `φ ⁻¹' D` for a component `D` of `Φ ⁻¹' U`, and both are sheets.
-/

noncomputable section

open MandelDim Metric Set Filter Topology
open scoped Topology

namespace Work.Horn

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : ParabData f₀ D₀}

/-! ## Elementary facts -/

/-- `{y : ℂ | ∀ k : ℤ, y ≠ v + k}` is open. -/
lemma isOpen_ne_add_intCast (v : ℂ) : IsOpen {y : ℂ | ∀ k : ℤ, y ≠ v + k} := by
  have h2 : (Set.range (fun k : ℤ => v + (k : ℂ)))
      = (fun z : ℂ => z - v) ⁻¹' (Set.range (fun k : ℤ => (k : ℂ))) := by
    ext y; simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  have h1 : {y : ℂ | ∀ k : ℤ, y ≠ v + k} = (Set.range (fun k : ℤ => v + (k : ℂ)))ᶜ := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    exact forall_congr' fun k => by rw [eq_comm]
  rw [h1, h2]
  exact ((Complex.isClosed_range_intCast.preimage (continuous_id.sub continuous_const))).isOpen_compl

/-- `Φ (f^[k] c) = Φ c + k`. -/
lemma Phi_iterate_crit (hsetup : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀) (k : ℕ) :
    d.Φ ((f₀^[k]) c) = d.Φ c + k := by
  have hcB : c ∈ B := hsetup.2.2.1
  have hbasin : B ⊆ ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hfB : MapsTo f₀ B B := hsetup.2.1.2.2.2.2.1
  have hmem : ∀ n : ℕ, (f₀^[n]) c ∈ B := by
    intro n
    induction n with
    | zero => simpa using hcB
    | succ m ih => simpa [Function.iterate_succ_apply'] using hfB ih
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', d.Φ_abel ((f₀^[n]) c) (hbasin (hmem n)), ih]
      push_cast
      ring

/-- If `Φ z` avoids `Φ c + ℤ` then `z` is not on the critical orbit. -/
lemma not_critOrbit_of_Phi_ne (hsetup : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀)
    {z : ℂ} (h : ∀ m : ℤ, d.Φ z ≠ d.Φ c + m) : z ∉ critOrbit f₀ c := by
  rintro ⟨k, hk1, rfl⟩
  refine h k ?_
  rw [Phi_iterate_crit hsetup d k]
  push_cast
  ring

/-- `E = Φ ∘ φ` is continuous on any subset of its domain `DE`. -/
lemma continuousOn_E (d : ParabData f₀ D₀) {S : Set ℂ} (hS : S ⊆ d.DE) :
    ContinuousOn d.E S := by
  have hdiff : DifferentiableOn ℂ (d.Φ ∘ d.φ) S :=
    d.Φ_holo.comp (d.φ_holo.mono (fun w hw => (hS hw).1)) (fun w hw => (hS hw).2)
  exact hdiff.continuousOn

/-- `E = Φ ∘ φ` agrees definitionally with the composite. -/
lemma E_eq_comp (d : ParabData f₀ D₀) : d.E = d.Φ ∘ d.φ := rfl


end Work.Horn



namespace Work.Horn

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : ParabData f₀ D₀}

/-- **Sheet homeomorphism of the composite.** -/
private lemma sheet_homeo (hTopo : MandelDim.HornTopoStatement) (hPhi : MandelDim.HornPhiStatement)
    (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement)
    (hsetup : IsF0Setup f₀ D₀ B c) (S : Set ℂ) (hSopen : IsOpen S) (hSsub : S ⊆ d.DE)
    (hSB : ∀ w ∈ S, d.φ w ∈ B)
    (hφcov : ∀ z ∈ B, z ∉ critOrbit f₀ c →
      ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ B ∧
        IsCoveringMapOn (fun w : ↥S => d.φ (w : ℂ)) (Metric.ball z r))
    (hφsurj : B \ critOrbit f₀ c ⊆ d.φ '' S)
    {y : ℂ} (hy : ∀ k : ℤ, y ≠ d.Φ c + k) {r : ℝ} (hr : 0 < r)
    (hq : IsCoveringMapOn (fun z : ↥B => d.Φ (z : ℂ)) (Metric.ball y r))
    (hUsub : (Metric.ball y r : Set ℂ) ⊆ {z : ℂ | ∀ k : ℤ, z ≠ d.Φ c + k})
    (x₀ : ↥S) (hx₀ : d.E (x₀ : ℂ) ∈ Metric.ball y r) :
    ∃ H : ↥(connectedComponentIn ((fun w : ↥S => d.E (w : ℂ)) ⁻¹' (Metric.ball y r)) x₀) ≃ₜ
        ↥(Metric.ball y r),
      ∀ z : ↥(connectedComponentIn ((fun w : ↥S => d.E (w : ℂ)) ⁻¹' (Metric.ball y r)) x₀),
        (H z : ℂ) = d.E ((z : ↥S) : ℂ) := by
  have hBopen : IsOpen B := hsetup.2.1.1
  have hBbasin : B ⊆ ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hDφ : S ⊆ d.Dφ := fun w hw => (hSsub hw).1
  haveI : LocallyPathConnectedSpace ↥B := hBopen.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace ↥S := hSopen.locallyPathConnectedSpace
  haveI hCon : ContractibleSpace ↥(Metric.ball y r) :=
    Convex.contractibleSpace (convex_ball y r) ⟨y, mem_ball_self hr⟩
  haveI hSCball : SimplyConnectedSpace ↥(Metric.ball y r) :=
    SimplyConnectedSpace.ofContractible _
  haveI hLPball : LocallyPathConnectedSpace ↥(Metric.ball y r) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  have hqcont : Continuous (fun z : ↥B => d.Φ (z : ℂ)) :=
    (d.Φ_holo.mono hBbasin).continuousOn.restrict
  have hpcont : Continuous (fun w : ↥S => d.φ (w : ℂ)) :=
    (d.φ_holo.mono hDφ).continuousOn.restrict
  have hz₀B : d.φ (x₀ : ℂ) ∈ B := hSB (x₀ : ℂ) x₀.2
  set z₀B : ↥B := ⟨d.φ (x₀ : ℂ), hz₀B⟩ with hz₀Bdef
  set Dq : Set ↥B :=
    connectedComponentIn ((fun z : ↥B => d.Φ (z : ℂ)) ⁻¹' (Metric.ball y r)) z₀B with hDqdef
  have hDqsub : Dq ⊆ ((fun z : ↥B => d.Φ (z : ℂ)) ⁻¹' (Metric.ball y r)) := by
    rw [hDqdef]; exact connectedComponentIn_subset _ z₀B
  have hz₀Dq : z₀B ∈ Dq := by
    rw [hDqdef]
    exact mem_connectedComponentIn (show d.Φ (z₀B : ℂ) ∈ Metric.ball y r from hx₀)
  have hDqopen : IsOpen Dq := by
    rw [hDqdef]
    exact (Metric.isOpen_ball.preimage hqcont).connectedComponentIn
  obtain ⟨Hq, hHq⟩ := Work.HornCov.covering_components_homeomorph
    (p := fun z : ↥B => d.Φ (z : ℂ)) (S := Metric.ball y r) Metric.isOpen_ball hq
    (fun s hs => by
      obtain ⟨z, hzB, hz⟩ := (hPhi f₀ D₀ B c d hsetup).1 s
      exact ⟨⟨z, hzB⟩, hz⟩)
    z₀B (show d.Φ (z₀B : ℂ) ∈ Metric.ball y r from hx₀)
  set D : Set ℂ := (Subtype.val : ↥B → ℂ) '' Dq with hDdef
  have hDsubB : ∀ ζ ∈ D, ζ ∈ B := by rintro ζ ⟨z, hz, rfl⟩; exact z.2
  have hDsubC : ∀ ζ ∈ D, ζ ∉ critOrbit f₀ c := by
    rintro ζ ⟨z, hz, rfl⟩
    exact not_critOrbit_of_Phi_ne hsetup d (hUsub (hDqsub hz))
  have hDopen : IsOpen D := by
    rw [hDdef]
    exact hBopen.isOpenMap_subtype_val Dq hDqopen
  let wB : ↥D → ↥B := fun w => ⟨(w : ℂ), hDsubB (w : ℂ) w.2⟩
  have hwB : ∀ w : ↥D, ((wB w : ↥B) : ℂ) = (w : ℂ) := fun w => rfl
  have hwBmem : ∀ w : ↥D, wB w ∈ Dq := by
    intro w
    obtain ⟨z, hz, hzeq⟩ := w.2
    rw [show wB w = z from Subtype.ext (by rw [hwB w, hzeq])]
    exact hz
  let invF : ↥(Metric.ball y r) → ↥D :=
    fun u => ⟨((Hq.symm u : ↥Dq) : ↥B), ⟨Hq.symm u, (Hq.symm u).2, rfl⟩⟩
  have hinvF : ∀ u : ↥(Metric.ball y r), wB (invF u) = Hq.symm u := by
    intro u
    apply Subtype.ext
    rfl
  let hDball : ↥D ≃ₜ ↥(Metric.ball y r) :=
    { toFun := fun w => Hq ⟨wB w, hwBmem w⟩
      invFun := invF
      left_inv := by
        intro w
        apply Subtype.ext
        show (((Hq.symm (Hq ⟨wB w, hwBmem w⟩) : ↥Dq) : ↥B) : ℂ) = (w : ℂ)
        rw [Homeomorph.symm_apply_apply]
      right_inv := by
        intro u
        show Hq ⟨wB (invF u), hwBmem (invF u)⟩ = u
        rw [show (⟨wB (invF u), hwBmem (invF u)⟩ : ↥Dq) = Hq.symm u from
          Subtype.ext (hinvF u), Homeomorph.apply_symm_apply]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  haveI : ContractibleSpace ↥D := hDball.contractibleSpace
  haveI : SimplyConnectedSpace ↥D := inferInstance
  haveI : LocallyPathConnectedSpace ↥D := hDopen.locallyPathConnectedSpace
  have hpD : IsCoveringMapOn (fun w : ↥S => d.φ (w : ℂ)) D := by
    intro s hs
    obtain ⟨r', hr', hBs, hcov⟩ := hφcov s (hDsubB s hs) (hDsubC s hs)
    exact hcov s (mem_ball_self hr')
  have hpDs : ∀ s ∈ D, ∃ x : ↥S, d.φ (x : ℂ) = s := by
    intro s hs
    obtain ⟨w, hwS, hw⟩ := hφsurj ⟨hDsubB s hs, hDsubC s hs⟩
    exact ⟨⟨w, hwS⟩, hw⟩
  have hp₀ : d.φ (x₀ : ℂ) ∈ D := ⟨z₀B, hz₀Dq, rfl⟩
  obtain ⟨Hp, hHp⟩ := Work.HornCov.covering_components_homeomorph
    (p := fun w : ↥S => d.φ (w : ℂ)) (S := D) hDopen hpD hpDs x₀ hp₀
  set C : Set ↥S := (fun w : ↥S => d.E (w : ℂ)) ⁻¹' (Metric.ball y r) with hCdef
  have hx₀C : x₀ ∈ C := hx₀
  -- the `↥B`-valued companion of `φ`
  set pb : ↥S → ↥B := fun w => ⟨d.φ (w : ℂ), hSB (w : ℂ) w.2⟩ with hpbdef
  have hpbcont : Continuous pb := by
    rw [hpbdef]
    exact hpcont.subtype_mk _
  have hpbx₀ : pb x₀ = z₀B := rfl
  have hpbC : pb '' (connectedComponentIn C x₀) ⊆ Dq := by
    have hpre : IsPreconnected (pb '' (connectedComponentIn C x₀)) :=
      isPreconnected_connectedComponentIn.image (f := pb) hpbcont.continuousOn
    refine hpre.subset_connectedComponentIn ?_ ?_
    · exact ⟨x₀, mem_connectedComponentIn hx₀C, hpbx₀⟩
    · rintro z ⟨w, hw, rfl⟩
      exact (connectedComponentIn_subset C x₀ hw : d.E (w : ℂ) ∈ Metric.ball y r)
  have hpCsub : (fun w : ↥S => d.φ (w : ℂ)) '' (connectedComponentIn C x₀) ⊆ D := by
    rintro ζ ⟨w, hw, rfl⟩
    exact ⟨pb w, hpbC ⟨w, hw, rfl⟩, rfl⟩
  have hWeq : connectedComponentIn C x₀
      = connectedComponentIn ((fun w : ↥S => d.φ (w : ℂ)) ⁻¹' D) x₀ := by
    refine subset_antisymm ?_ ?_
    · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        (mem_connectedComponentIn hx₀C) ?_
      intro w hw
      exact hpCsub ⟨w, hw, rfl⟩
    · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        (mem_connectedComponentIn hp₀) ?_
      intro w hw
      have hwD : d.φ (w : ℂ) ∈ D :=
        connectedComponentIn_subset ((fun w : ↥S => d.φ (w : ℂ)) ⁻¹' D) x₀ hw
      rw [hDdef] at hwD
      obtain ⟨z, hzDq, hz⟩ := hwD
      have h2 : d.Φ (z : ℂ) ∈ Metric.ball y r := hDqsub hzDq
      rw [hz] at h2
      exact h2
  have hDball_apply : ∀ (w : ↥D), ((hDball w : ↥(Metric.ball y r)) : ℂ) = d.Φ (w : ℂ) := by
    intro w
    rw [show (hDball w) = Hq ⟨wB w, hwBmem w⟩ from rfl, hHq]
  refine ⟨(Homeomorph.setCongr hWeq).trans (Hp.trans hDball), ?_⟩
  intro z
  have h1 : ((Hp.trans hDball)
      ((Homeomorph.setCongr hWeq) z) : ℂ) = d.Φ (d.φ ((z : ↥S) : ℂ)) := by
    rw [Homeomorph.trans_apply, hDball_apply, hHp]
    rfl
  show ((Hp.trans hDball) ((Homeomorph.setCongr hWeq) z) : ℂ) = d.E ((z : ↥S) : ℂ)
  rw [h1]
  rfl

/-- **The covering property of `E` on one horn.** -/
private lemma cov_side (hTopo : MandelDim.HornTopoStatement) (hPhi : MandelDim.HornPhiStatement)
    (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement)
    (hsetup : IsF0Setup f₀ D₀ B c) (S : Set ℂ) (hSopen : IsOpen S) (hSsub : S ⊆ d.DE)
    (hSB : ∀ w ∈ S, d.φ w ∈ B)
    (hφcov : ∀ z ∈ B, z ∉ critOrbit f₀ c →
      ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ B ∧
        IsCoveringMapOn (fun w : ↥S => d.φ (w : ℂ)) (Metric.ball z r))
    (hφsurj : B \ critOrbit f₀ c ⊆ d.φ '' S) :
    IsCoveringMapOn (fun w : ↥S => d.E (w : ℂ)) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} := by
  intro y hy
  obtain ⟨r₁, hr₁, hq₁⟩ := Work.HornCov.sheet_Phi hPhi f₀ D₀ B c d hsetup y
    (fun k => by
      have h := hy (-(k : ℤ))
      simpa [sub_eq_add_neg] using h)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_ne_add_intCast (d.Φ c)).mem_nhds hy)
  have hr : 0 < min r₁ ρ := lt_min hr₁ hρ
  have hUsub : (Metric.ball y (min r₁ ρ) : Set ℂ) ⊆ {z : ℂ | ∀ k : ℤ, z ≠ d.Φ c + k} :=
    (ball_subset_ball (min_le_right _ _)).trans hρsub
  have hq : IsCoveringMapOn (fun z : ↥B => d.Φ (z : ℂ)) (Metric.ball y (min r₁ ρ)) :=
    hq₁.mono (ball_subset_ball (min_le_left _ _))
  set U : Set ℂ := Metric.ball y (min r₁ ρ) with hUdef
  set W : Set ↥S := (fun w : ↥S => d.E (w : ℂ)) ⁻¹' U with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef, hUdef]
    exact Metric.isOpen_ball.preimage ((continuousOn_E d hSsub).restrict)
  let ι := {A : Set ↥S // ∃ x : ↥S, x ∈ W ∧ A = connectedComponentIn W x}
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  -- components of `W` are equal or disjoint
  have hcc_eq : ∀ x y : ↥S, y ∈ connectedComponentIn W x →
      connectedComponentIn W x = connectedComponentIn W y :=
    fun x y h => connectedComponentIn_eq h
  haveI hLP : LocallyPathConnectedSpace ↥S := hSopen.locallyPathConnectedSpace
  have sheetI : ∀ i : ι, ∃ H : ↥(i.1 : Set ↥S) ≃ₜ ↥U,
      ∀ z, ((H z : ↥U) : ℂ) = d.E ((z : ↥S) : ℂ) := by
    intro i
    obtain ⟨x, hxW, hAi⟩ := i.2
    have hxU : d.E (x : ℂ) ∈ Metric.ball y (min r₁ ρ) := hxW
    obtain ⟨H, hH⟩ := sheet_homeo hTopo hPhi hVarphi hSC hsetup S hSopen hSsub hSB hφcov
      hφsurj hy hr hq hUsub x hxU
    refine ⟨(Homeomorph.setCongr hAi).trans H, fun z => ?_⟩
    rw [Homeomorph.trans_apply]
    exact hH _
  choose Hsheet hHsheet using sheetI
  refine Work.HornCov.covering_of_components (f := fun w : ↥S => d.E (w : ℂ))
    (S := U) (hS := by rw [hUdef]; exact Metric.isOpen_ball) (ι := ι)
    (C := fun i : ι => (i.1 : Set ↥S)) ?_ ?_ ?_
    (fun i => Hsheet i) (fun i z => hHsheet i z) y ?_
  · -- openness of the components
    rintro ⟨A, x, hxW, rfl⟩
    exact hWopen.connectedComponentIn
  · -- disjointness of the components
    intro i j hij
    rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨x, hxW, hxi⟩ := i.2
    obtain ⟨y, hyW, hyj⟩ := j.2
    have h1 : connectedComponentIn W x = connectedComponentIn W a :=
      connectedComponentIn_eq (x := x) (y := a) (hxi ▸ ha)
    have h2 : connectedComponentIn W y = connectedComponentIn W a :=
      connectedComponentIn_eq (x := y) (y := a) (hyj ▸ hb)
    exact hij (Subtype.ext (by rw [hxi, h1, h2.symm, ← hyj]))
  · -- the components cover `W`
    show W = ⋃ i : ι, (i.1 : Set ↥S)
    ext w
    constructor
    · intro hw
      exact Set.mem_iUnion.mpr ⟨⟨connectedComponentIn W w, w, hw, rfl⟩,
        mem_connectedComponentIn hw⟩
    · intro hw
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
      obtain ⟨x, hxW, hxi⟩ := i.2
      exact connectedComponentIn_subset W x (hxi ▸ hi)
  · show y ∈ Metric.ball y (min r₁ ρ)
    exact mem_ball_self hr




/-- **`Work.Horn.cov_of_parts`.**  `E = Φ ∘ φ` is a covering map on each horn over
`ℂ ∖ (Φ c + ℤ)`. -/
theorem cov_of_parts (hTopo : MandelDim.HornTopoStatement) (hPhi : MandelDim.HornPhiStatement)
    (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x)
      {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
    IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x)
      {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} := by
  have hT := hTopo f₀ D₀ B c d hsetup
  have himg := Work.HornCov.varphi_image hVarphi hTopo hSC f₀ D₀ B c d hsetup
  constructor
  · exact cov_side hTopo hPhi hVarphi hSC hsetup (MandelDim.BuOf d B) hT.1
      (fun w hw => hT.2.2.2.2.2.2 (Set.mem_union_left _ hw))
      (fun w hw => (connectedComponentIn_subset (MandelDim.Btil d B)
        (Complex.I * (d.η₀ + 1)) hw).2)
      (fun z hzB hzc => by
        obtain ⟨r, hr, hrB, hcovU, -⟩ :=
          Work.HornCov.sheet_varphi hTopo hVarphi hSC f₀ D₀ B c d hsetup z hzB hzc
        exact ⟨r, hr, hrB, hcovU⟩)
      himg.1
  · exact cov_side hTopo hPhi hVarphi hSC hsetup (MandelDim.BlOf d B) hT.2.1
      (fun w hw => hT.2.2.2.2.2.2 (Set.mem_union_right _ hw))
      (fun w hw => (connectedComponentIn_subset (MandelDim.Btil d B)
        (-(Complex.I * (d.η₀ + 1))) hw).2)
      (fun z hzB hzc => by
        obtain ⟨r, hr, hrB, -, hcovL⟩ :=
          Work.HornCov.sheet_varphi hTopo hVarphi hSC f₀ D₀ B c d hsetup z hzB hzc
        exact ⟨r, hr, hrB, hcovL⟩)
      himg.2

end Work.Horn
