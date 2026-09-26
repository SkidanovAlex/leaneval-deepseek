import Mathlib
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_boxRegion_le_sdiff_interior_union_boundary
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential
import Submission.Work.Smooth.SphereJordan.disc_image_open_of_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.Peel.exists_gap_periodLattice_image
import Submission.Work.Peel.exists_enlarged_disc

/-!
# Peeling a closed curve off the carrier of an embedded disc, given a collar inside the region

`Work.BoxShrink.PinchOff.peel_curve_sdiff_discRegion`: let `D` be an embedded disc of the surface
`F = P.carrier` of a parametrised torus, let `X ⊆ F` be a region which contains an
*open-in-the-carrier* neighbourhood `N` of the boundary circle `∂D`, and let `δ` be a closed curve
of `F` whose image lies in `X`.  Then there is a closed curve `δ'` of `F` whose image lies in
`X \ D.carrier` and which has the same winding vector as `δ`.

The proof is the standard one:

* lift the disc to the parameter plane (`DiscRegion.exists_lift_disc`) and the plane-enlargement
  lemma (`Work.Peel.exists_enlarged_disc`) produces a slightly larger flat disc `G '' 𝔻` whose
  boundary circle is still inside the collar `Xtilde P N` and whose image stays in a prescribed
  thin neighbourhood of the lifted disc (so that no two of its lattice translates meet, using the
  gap lemma `Work.Peel.exists_gap_periodLattice_image`);
* pushing `G` down to the torus gives an embedded disc `D₂` of `F` with `D.carrier ⊆ D₂.interior`
  and `D₂.boundary ⊆ X \ D.carrier` (the smaller disc sits in the interior of the larger one, the
  larger one's boundary circle sits in the collar, outside the smaller disc);
* the disc re-route `Work.PinchLemma3.ClosedDiscA.disc_reroute_general` applied to `D₂` and `δ`
  produces a closed curve `δ'` which agrees with `δ` wherever `δ` misses `D₂.interior` — hence
  misses `D.carrier` — and lies on `∂D₂ ⊆ X \ D.carrier` where it does not; it is homotopic to
  `δ` in `F`, so it has the same winding vector (`WindingOf.homotopic_eq`).
-/

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The complex lift of an embedded disc -/

/-- The lift of the parametrisation of an embedded disc to the parameter plane, read as a map into
`ℂ` (the parameter plane being `ℂ`, with `periodLattice = 2π(ℤ + iℤ)`). -/
def complexLift (Ξ : C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℝ × ℝ)) :
    C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℂ) :=
  ⟨fun z => ((Ξ z).1 : ℂ) + ((Ξ z).2 : ℂ) * Complex.I,
    ((Complex.continuous_ofReal.comp Ξ.continuous.fst).add
      ((Complex.continuous_ofReal.comp Ξ.continuous.snd).mul continuous_const))⟩

@[simp] theorem complexLift_apply (Ξ : C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℝ × ℝ))
    (z : Work.SurgeryInvariance.DiscRegion.unitDisc) :
    complexLift Ξ z = ((Ξ z).1 : ℂ) + ((Ξ z).2 : ℂ) * Complex.I := rfl

theorem complexLift_re (Ξ : C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℝ × ℝ))
    (z : Work.SurgeryInvariance.DiscRegion.unitDisc) : (complexLift Ξ z).re = (Ξ z).1 := by
  simp [complexLift_apply]

theorem complexLift_im (Ξ : C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℝ × ℝ))
    (z : Work.SurgeryInvariance.DiscRegion.unitDisc) : (complexLift Ξ z).im = (Ξ z).2 := by
  simp [complexLift_apply]

/-! ## The main lemma -/

/-- **Peeling a closed curve off the carrier of an embedded disc.**  See the module docstring. -/
theorem peel_curve_sdiff_discRegion {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hN : ∃ N : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.SurgeryInvariance.IsOpenInCarrier P N ∧ D.boundary ⊆ N ∧ N ⊆ X)
    (δ : Work.CoreTopology.ClosedCurve P) (hδ : ∀ t : ℝ, δ t ∈ X) :
    ∃ δ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, δ' t ∈ X \ D.carrier) ∧
      Work.SurgeryInvariance.windingOf P δ' = Work.SurgeryInvariance.windingOf P δ := by
  classical
  -- ## The three forms of the model disc
  have hball : (Subtype.val ⁻¹' Metric.ball (0 : ℂ) 1 :
      Set Work.SurgeryInvariance.DiscRegion.unitDisc)
      = {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1} := by
    ext z
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, sub_zero]
  have hsphere : (Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1 :
      Set Work.SurgeryInvariance.DiscRegion.unitDisc)
      = {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ = 1} := by
    ext z
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm, sub_zero]
  -- ## Step 1: the lift of the disc to the parameter plane, and its complex form
  obtain ⟨Ξ, hΞ⟩ := Work.SurgeryInvariance.DiscRegion.exists_lift_disc D
  set f : C(Work.SurgeryInvariance.DiscRegion.unitDisc, ℂ) := complexLift Ξ with hfdef
  have hf_apply : ∀ z, f z = ((Ξ z).1 : ℂ) + ((Ξ z).2 : ℂ) * Complex.I := by
    intro z; rw [hfdef]; rfl
  have hf_inj : Function.Injective f := by
    intro z w hzw
    apply D.inj
    rw [← hΞ z, ← hΞ w]
    have h1 : (Ξ z).1 = (Ξ w).1 := by
      have := congrArg Complex.re hzw
      simpa [hf_apply] using this
    have h2 : (Ξ z).2 = (Ξ w).2 := by
      have := congrArg Complex.im hzw
      simpa [hf_apply] using this
    rw [h1, h2]
  have hf_psi : ∀ z : Work.SurgeryInvariance.DiscRegion.unitDisc,
      Work.BoxShrink.PinchOff.planePsi P (f z) = D.e z := by
    intro z
    have hr : (f z).re = (Ξ z).1 := by rw [hf_apply]; simp
    have hi : (f z).im = (Ξ z).2 := by rw [hf_apply]; simp
    show P.psi (f z).re (f z).im = D.e z
    rw [hr, hi]
    exact hΞ z
  -- ## Step 2: replace `N` by `N ∩ F`
  obtain ⟨N₀, hN₀open, hN₀sub, hN₀X⟩ := hN
  set N : Set R3 := N₀ ∩ P.carrier with hNdef
  have hN_carrier : N ⊆ P.carrier := Set.inter_subset_right
  have hN_open : Work.SurgeryInvariance.IsOpenInCarrier P N := by
    rw [hNdef]
    rw [Work.SurgeryInvariance.IsOpenInCarrier] at hN₀open ⊢
    convert hN₀open using 1
    ext x
    simp
  have hN_sub : D.boundary ⊆ N := by
    intro x hx
    refine ⟨hN₀sub hx, ?_⟩
    obtain ⟨z, -, rfl⟩ := hx
    exact D.mem z
  have hN_X : N ⊆ X := fun x hx => hN₀X hx.1
  -- ## Step 3: the collar in the parameter plane
  set U : Set ℂ := Work.BoxShrink.PinchOff.Xtilde P N with hUdef
  have hU_open : IsOpen U := by
    rw [hUdef]
    exact Work.BoxShrink.PinchOff.isOpen_Xtilde hN_carrier hN_open
  have hbd : ⇑f '' (Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1) ⊆ U := by
    rw [hsphere]
    rintro y ⟨z, hz, rfl⟩
    rw [hUdef, Work.BoxShrink.PinchOff.mem_Xtilde, hf_psi z]
    exact hN_sub ⟨z, hz, rfl⟩
  -- ## Step 4: separation, gap, enlargement
  have hsep : ∀ u, u ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      ∀ v, v ∈ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) →
      ∀ ν, ν ∈ Work.BoxShrink.PinchOff.periodLattice → u - v = ν → ν = 0 := by
    rintro u ⟨zu, -, rfl⟩ v ⟨zv, -, rfl⟩ ν hν huv
    have h : (⇑f zu : ℂ) = ⇑f zv + ν := by rw [← huv]; ring
    have hpsi : Work.BoxShrink.PinchOff.planePsi P (⇑f zu) =
        Work.BoxShrink.PinchOff.planePsi P (⇑f zv) :=
      calc Work.BoxShrink.PinchOff.planePsi P (⇑f zu)
          = Work.BoxShrink.PinchOff.planePsi P (⇑f zv + ν) := by rw [h]
        _ = Work.BoxShrink.PinchOff.planePsi P (⇑f zv) :=
            Work.BoxShrink.PinchOff.planePsi_add_periodLattice P (⇑f zv) ν hν
    rw [hf_psi zu, hf_psi zv] at hpsi
    have hzw : zu = zv := D.inj hpsi
    subst hzw
    exact (show (0 : ℂ) = ν from by simpa using huv).symm
  obtain ⟨η, hηpos, hη⟩ := Work.Peel.exists_gap_periodLattice_image f hsep
  set η' : ℝ := η / 4 with hη'def
  have hη'pos : 0 < η' := by rw [hη'def]; linarith
  obtain ⟨G, hGinj, hGbig, hGbnd, hGout, hGclose⟩ :=
    Work.Peel.exists_enlarged_disc f hf_inj U hU_open hbd (η := η') hη'pos
  -- ## Step 5: push the enlarged disc down to the torus
  have hGcont : Continuous fun z : Work.SurgeryInvariance.DiscRegion.unitDisc =>
      Work.BoxShrink.PinchOff.planePsi P (G z) :=
    (Work.BoxShrink.PinchOff.continuous_planePsi P).comp G.continuous
  have hGpsi_inj : Function.Injective (fun z : Work.SurgeryInvariance.DiscRegion.unitDisc =>
      Work.BoxShrink.PinchOff.planePsi P (G z)) := by
    intro z w hzw
    by_contra hne
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ :=
      (P.psi_eq_iff (G z).re (G z).im (G w).re (G w).im).mp hzw
    set ν : ℂ := Work.BoxShrink.PinchOff.periodPt k l with hνdef
    have hνmem : ν ∈ Work.BoxShrink.PinchOff.periodLattice :=
      (Work.BoxShrink.PinchOff.mem_periodLattice ν).mpr ⟨k, l, rfl⟩
    have hGz : (G z : ℂ) = G w + ν := by
      rw [hνdef]
      apply Complex.ext
      · simpa using hk
      · simpa using hl
    by_cases hν0 : ν = 0
    · exact hne (hGinj (by rw [hGz, hν0, add_zero]))
    · obtain ⟨w₁, hw₁⟩ := hGclose z
      obtain ⟨w₂, hw₂⟩ := hGclose w
      have hgap := hη ν hνmem hν0 (⇑f w₂) ⟨w₂, w₂.2, rfl⟩ (⇑f w₁) ⟨w₁, w₁.2, rfl⟩
      have h1 : dist (⇑f w₂ + ν) (G z) = dist (⇑f w₂) (G w) := by
        rw [hGz, dist_eq_norm, dist_eq_norm]
        congr 1
        ring
      have h4 : dist (⇑f w₂) (G w) < η' := by rw [dist_comm]; exact hw₂
      have h5 : dist (G z) (⇑f w₁) < η' := hw₁
      have h2 : dist (⇑f w₂ + ν) (⇑f w₁) < η := by
        have h3 : dist (⇑f w₂ + ν) (⇑f w₁)
            ≤ dist (⇑f w₂ + ν) (G z) + dist (G z) (⇑f w₁) := dist_triangle _ _ _
        rw [h1] at h3
        have h6 : η' + η' < η := by rw [hη'def]; linarith
        linarith
      linarith
  -- ## Step 6: the enlarged disc region
  have hD₂_open_int : Work.SurgeryInvariance.IsOpenInCarrier P
      ((fun z : Work.SurgeryInvariance.DiscRegion.unitDisc =>
          Work.BoxShrink.PinchOff.planePsi P (G z)) ''
        {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1}) := by
    have hGball : IsOpen (⇑G '' {z : Work.SurgeryInvariance.DiscRegion.unitDisc |
        ‖(z : ℂ)‖ < 1}) :=
      Work.Smooth.SphereJordan.disc_image_open_of_injective (F := G) hGinj
    have hφ : IsOpen (Complex.equivRealProdCLM.toHomeomorph ''
        (⇑G '' {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1})) :=
      Complex.equivRealProdCLM.toHomeomorph.isOpenMap _ hGball
    have hmorse : Work.SurgeryInvariance.IsOpenInCarrier P
        (Work.TorusCover.psiMap P.psi '' (Complex.equivRealProdCLM.toHomeomorph ''
          (⇑G '' {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1}))) :=
      Work.Smooth.Morse.Surface.isOpenInCarrier_psiMap_image (P := P) hφ
    have hset : Work.TorusCover.psiMap P.psi '' (Complex.equivRealProdCLM.toHomeomorph ''
          (⇑G '' {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1}))
        = (fun z : Work.SurgeryInvariance.DiscRegion.unitDisc =>
            Work.BoxShrink.PinchOff.planePsi P (G z)) ''
          {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1} := by
      have hcomp : (fun z : ℂ => Work.TorusCover.psiMap P.psi
            (Complex.equivRealProdCLM.toHomeomorph z)) = Work.BoxShrink.PinchOff.planePsi P := by
        funext z
        simp [Work.BoxShrink.PinchOff.planePsi, Work.TorusCover.psiMap]
      rw [Set.image_image, hcomp, Set.image_image]
    rwa [hset] at hmorse
  let D₂ : Work.SurgeryInvariance.DiscRegion P :=
    { e := ⟨fun z => Work.BoxShrink.PinchOff.planePsi P (G z), hGcont⟩
      inj := hGpsi_inj
      mem := fun z => Work.BoxShrink.PinchOff.planePsi_mem_carrier P (G z)
      open_interior := hD₂_open_int }
  have hD₂_e : ∀ z, D₂.e z = Work.BoxShrink.PinchOff.planePsi P (G z) := fun z => rfl
  -- ## Step 7: `D.carrier ⊆ D₂.interior`
  have hcarrier_sub : D.carrier ⊆ D₂.interior := by
    rintro x ⟨z, rfl⟩
    obtain ⟨z', hz', hz'f⟩ := hGbig ⟨z, z.2, rfl⟩
    have hz'ball : z' ∈ {z : Work.SurgeryInvariance.DiscRegion.unitDisc | ‖(z : ℂ)‖ < 1} := by
      rw [← hball]; exact hz'
    have hEq : D₂.e z' = D.e z := by
      calc D₂.e z' = Work.BoxShrink.PinchOff.planePsi P (G z') := hD₂_e z'
        _ = Work.BoxShrink.PinchOff.planePsi P (⇑f z) := by rw [hz'f]
        _ = D.e z := hf_psi z
    exact ⟨z', hz'ball, hEq⟩
  -- ## Step 8: `D₂.boundary ⊆ X \ D.carrier`
  have hbnd_sub : D₂.boundary ⊆ X \ D.carrier := by
    rintro x ⟨z, hz, rfl⟩
    have hzsphere : z ∈ Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1 := by
      rw [hsphere]; exact hz
    have hGzU : G z ∈ U := hGbnd ⟨z, hzsphere, rfl⟩
    have hGzout : G z ∉ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) :=
      hGout z hzsphere
    refine ⟨?_, ?_⟩
    · show Work.BoxShrink.PinchOff.planePsi P (G z) ∈ X
      exact hN_X hGzU
    · rintro ⟨z', hz'eq⟩
      have hpsi_eq : Work.BoxShrink.PinchOff.planePsi P (G z) =
          Work.BoxShrink.PinchOff.planePsi P (⇑f z') := by
        calc Work.BoxShrink.PinchOff.planePsi P (G z) = D.e z' := hz'eq.symm
          _ = Work.BoxShrink.PinchOff.planePsi P (⇑f z') := (hf_psi z').symm
      obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ :=
        (P.psi_eq_iff (G z).re (G z).im (f z').re (f z').im).mp hpsi_eq
      set ν : ℂ := Work.BoxShrink.PinchOff.periodPt k l with hνdef
      have hνmem : ν ∈ Work.BoxShrink.PinchOff.periodLattice :=
        (Work.BoxShrink.PinchOff.mem_periodLattice ν).mpr ⟨k, l, rfl⟩
      have hGz : (G z : ℂ) = ⇑f z' + ν := by
        rw [hνdef]
        apply Complex.ext
        · simpa using hk
        · simpa using hl
      by_cases hν0 : ν = 0
      · refine hGzout ?_
        rw [hGz, hν0, add_zero]
        exact ⟨z', z'.2, rfl⟩
      · obtain ⟨w, hw⟩ := hGclose z
        have hgap := hη ν hνmem hν0 (⇑f z') ⟨z', z'.2, rfl⟩ (⇑f w) ⟨w, w.2, rfl⟩
        have hzero : dist (⇑f z' + ν) (G z) = 0 := by rw [hGz, dist_self]
        have hlt : dist (⇑f z' + ν) (⇑f w) < η := by
          have h3 : dist (⇑f z' + ν) (⇑f w)
              ≤ dist (⇑f z' + ν) (G z) + dist (G z) (⇑f w) := dist_triangle _ _ _
          rw [hzero, zero_add] at h3
          linarith
        linarith
  -- ## Step 9: the re-route and the winding
  obtain ⟨δ', hhom, hfix, hbd'⟩ := Work.PinchLemma3.ClosedDiscA.disc_reroute_general D₂ δ
  refine ⟨δ', ?_, ?_⟩
  · intro t
    by_cases ht : δ t ∈ D₂.interior
    · exact hbnd_sub (hbd' t ht)
    · refine ⟨?_, ?_⟩
      · rw [hfix t ht]; exact hδ t
      · intro hcon
        rw [hfix t ht] at hcon
        exact ht (hcarrier_sub hcon)
  · exact (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm

end

end Work.BoxShrink.PinchOff
