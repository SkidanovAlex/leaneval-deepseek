import Mathlib
import Submission.Work.ThomBordism.KeyLocal.germPullbackEuc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped Topology

namespace Work.ThomBordism.KeyLocal

noncomputable section

open CategoryTheory

/-- **The germ/linearisation principle at an arbitrary base point.**

Generalises the PROVED `Work.ThomBordism.KeyLocal.germPullbackEuc` (the base point `0`) to an
arbitrary base point `a₀ ∈ W`: if two maps `F`, `G` on an open set `W ∋ a₀` have value `0` and
invertible derivatives at `a₀` and do not vanish elsewhere on `W`, then their pullbacks of a class
of `Hⁿ(ℝⁿ, ℝⁿ∖0)` on the pair `(↥W, W∖{a₀})` agree up to the determinant signs of the two
derivatives.  This is the tool that compares the product reading with the ambient translation
reading of the tube in the last-mile plan (`_kl/NOTE_SESSION9.md`, step (GM)).

Proof route: translate by `a₀` (an isomorphism of pairs, contributing no sign), apply the PROVED
`KeyLocal.germPullbackEuc` to `F ∘ (· + a₀)` and `G ∘ (· + a₀)` at `0`, and cancel the common
inclusion pullback (`sign (det M)⁻¹ = sign (det M)`). -/
theorem germPullbackEucAt {n : ℕ} (hn : 1 ≤ n)
    {a₀ : EuclideanSpace ℝ (Fin n)} {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : IsOpen W) (ha₀ : a₀ ∈ W)
    (F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hFc : ContinuousOn F W) (hGc : ContinuousOn G W)
    (hF0 : F a₀ = 0) (hG0 : G a₀ = 0)
    (hFnz : ∀ z ∈ W, z ≠ a₀ → F z ≠ 0)
    (hGnz : ∀ z ∈ W, z ≠ a₀ → G z ≠ 0)
    (L M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : Function.Bijective L) (hM : Function.Bijective M)
    (hdF : HasFDerivAt F L a₀) (hdG : HasFDerivAt G M a₀)
    (hdetL : LinearMap.det L.toLinearMap ≠ 0) (hdetM : LinearMap.det M.toLinearMap ≠ 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      (Work.Thom.relCohMap
          (⟨fun z : W => F z, continuousOn_iff_continuous_domRestrict.mp hFc⟩ :
            C(W, EuclideanSpace ℝ (Fin n)))
          ({z : W | (z : EuclideanSpace ℝ (Fin n)) ≠ a₀})
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
          (fun z hz => hFnz z z.2 hz) ℤ n).hom ξ
        = ((if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1)
            * (if 0 < LinearMap.det M.toLinearMap then (1 : ℤ) else -1)) •
          (Work.Thom.relCohMap
            (⟨fun z : W => G z, continuousOn_iff_continuous_domRestrict.mp hGc⟩ :
              C(W, EuclideanSpace ℝ (Fin n)))
            ({z : W | (z : EuclideanSpace ℝ (Fin n)) ≠ a₀})
            ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
            (fun z hz => hGnz z z.2 hz) ℤ n).hom ξ := by
  intro ξ
  -- ## 0. The two signs and the translated neighbourhood
  set sL : ℤ := (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) with hsL
  set sM : ℤ := (if 0 < LinearMap.det M.toLinearMap then (1 : ℤ) else -1) with hsM
  let V : Set (EuclideanSpace ℝ (Fin n)) := (fun x : EuclideanSpace ℝ (Fin n) => x + a₀) ⁻¹' W
  have hV : IsOpen V := hW.preimage (continuous_id.add continuous_const)
  have h0V : (0 : EuclideanSpace ℝ (Fin n)) ∈ V := by
    show (0 : EuclideanSpace ℝ (Fin n)) + a₀ ∈ W
    simpa using ha₀
  have hmemV : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ V ↔ x + a₀ ∈ W := fun _ => Iff.rfl
  let Cv : Set ↥V := {z | (z : EuclideanSpace ℝ (Fin n)) ≠ 0}
  let Bw : Set ↥W := {z | (z : EuclideanSpace ℝ (Fin n)) ≠ a₀}
  -- ## 1. The translation as a map of pairs, and its inverse
  let t : C(↥V, ↥W) :=
    ⟨fun x => ⟨(x : EuclideanSpace ℝ (Fin n)) + a₀, (hmemV x).mp x.2⟩,
      Continuous.subtype_mk (continuous_subtype_val.add continuous_const)
        (fun x => (hmemV x).mp x.2)⟩
  let sinv : C(↥W, ↥V) :=
    ⟨fun z => ⟨(z : EuclideanSpace ℝ (Fin n)) - a₀,
        (hmemV ((z : EuclideanSpace ℝ (Fin n)) - a₀)).mpr (by rw [sub_add_cancel]; exact z.2)⟩,
      Continuous.subtype_mk (continuous_subtype_val.sub continuous_const)
        (fun z => (hmemV ((z : EuclideanSpace ℝ (Fin n)) - a₀)).mpr (by rw [sub_add_cancel]; exact z.2))⟩
  have ht : ∀ x ∈ Cv, t x ∈ Bw := fun x hx h =>
    hx (add_right_cancel (show (x : EuclideanSpace ℝ (Fin n)) + a₀ = (0 : EuclideanSpace ℝ (Fin n)) + a₀ by
      rw [zero_add]; exact h))
  have hsinv : ∀ z ∈ Bw, sinv z ∈ Cv := fun z hz h => hz (sub_eq_zero.mp h)
  have hts : t.comp sinv = ContinuousMap.id ↥W := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    show ((z : EuclideanSpace ℝ (Fin n)) - a₀) + a₀ = (z : EuclideanSpace ℝ (Fin n))
    rw [sub_add_cancel]
  have hst : sinv.comp t = ContinuousMap.id ↥V := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    show ((x : EuclideanSpace ℝ (Fin n)) + a₀) - a₀ = (x : EuclideanSpace ℝ (Fin n))
    rw [add_sub_cancel_right]
  have hTs : ∀ z ∈ Bw, (t.comp sinv) z ∈ Bw := fun z hz => by rw [hts]; exact hz
  have hSt : ∀ x ∈ Cv, (sinv.comp t) x ∈ Cv := fun x hx => by rw [hst]; exact hx
  -- ## 2. The translated maps and the hypotheses of `germPullbackEuc`
  let F₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => F (x + a₀)
  let G₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => G (x + a₀)
  have hF1c : ContinuousOn F₁ V := by
    have h := hFc.comp_continuous (continuous_subtype_val.comp t.continuous) (fun x : ↥V => (t x).2)
    exact continuousOn_iff_continuous_domRestrict.mpr h
  have hG1c : ContinuousOn G₁ V := by
    have h := hGc.comp_continuous (continuous_subtype_val.comp t.continuous) (fun x : ↥V => (t x).2)
    exact continuousOn_iff_continuous_domRestrict.mpr h
  have hF10 : F₁ 0 = 0 := by
    show F (0 + a₀) = 0
    simpa using hF0
  have hG10 : G₁ 0 = 0 := by
    show G (0 + a₀) = 0
    simpa using hG0
  have hF1nz : ∀ z ∈ V, z ≠ 0 → F₁ z ≠ 0 := fun z hz hz0 =>
    hFnz (z + a₀) ((hmemV z).mp hz) (fun h =>
      hz0 (add_right_cancel (show z + a₀ = (0 : EuclideanSpace ℝ (Fin n)) + a₀ by rw [zero_add]; exact h)))
  have hG1nz : ∀ z ∈ V, z ≠ 0 → G₁ z ≠ 0 := fun z hz hz0 =>
    hGnz (z + a₀) ((hmemV z).mp hz) (fun h =>
      hz0 (add_right_cancel (show z + a₀ = (0 : EuclideanSpace ℝ (Fin n)) + a₀ by rw [zero_add]; exact h)))
  have hdF1 : HasFDerivAt F₁ L 0 := by
    have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x + a₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 :=
      (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin n))).add_const a₀
    have h2 : HasFDerivAt F L ((fun x : EuclideanSpace ℝ (Fin n) => x + a₀) 0) := by
      simpa using hdF
    have h3 := h2.comp (0 : EuclideanSpace ℝ (Fin n)) h1
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hdG1 : HasFDerivAt G₁ M 0 := by
    have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x + a₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 :=
      (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin n))).add_const a₀
    have h2 : HasFDerivAt G M ((fun x : EuclideanSpace ℝ (Fin n) => x + a₀) 0) := by
      simpa using hdG
    have h3 := h2.comp (0 : EuclideanSpace ℝ (Fin n)) h1
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3
  -- ## 3. The maps of the pullbacks
  let F₁C : C(↥V, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun z : ↥V => F₁ z, continuousOn_iff_continuous_domRestrict.mp hF1c⟩
  let G₁C : C(↥V, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun z : ↥V => G₁ z, continuousOn_iff_continuous_domRestrict.mp hG1c⟩
  let kpiV : C(↥V, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun z : ↥V => (z : EuclideanSpace ℝ (Fin n)), continuous_subtype_val⟩
  let tauW : C(↥W, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun z => (z : EuclideanSpace ℝ (Fin n)) - a₀, continuous_subtype_val.sub continuous_const⟩
  have hF1a : ∀ z ∈ Cv, F₁C z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz => hF1nz z z.2 hz
  have hG1a : ∀ z ∈ Cv, G₁C z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz => hG1nz z z.2 hz
  have hVz : ∀ z ∈ Cv, kpiV z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz => hz
  have hFW : ∀ z ∈ Bw, kpFW W F hFc z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz => hFnz z z.2 hz
  have hGW : ∀ z ∈ Bw, kpFW W G hGc z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz => hGnz z z.2 hz
  have hτw : ∀ z ∈ Bw, tauW z ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun z hz h => hz (sub_eq_zero.mp h)
  -- the composites
  have hc1 : ∀ x ∈ Cv, ((kpFW W F hFc).comp t) x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun x hx => hFW (t x) (ht x hx)
  have hc3 : ∀ x ∈ Cv, ((kpFW W G hGc).comp t) x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun x hx => hGW (t x) (ht x hx)
  have hc2 : ∀ x ∈ Cv, (tauW.comp t) x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx h
    refine hx ?_
    have h' : ((t x : ↥W) : EuclideanSpace ℝ (Fin n)) = a₀ := sub_eq_zero.mp h
    exact add_right_cancel (show (x : EuclideanSpace ℝ (Fin n)) + a₀ = (0 : EuclideanSpace ℝ (Fin n)) + a₀ by
      rw [zero_add]; exact h')
  -- ## 4. The map equalities
  have hcomp1map : (kpFW W F hFc).comp t = F₁C := by
    ext x
    rfl
  have hcomp3map : (kpFW W G hGc).comp t = G₁C := by
    ext x
    rfl
  have hcomp2map : tauW.comp t = kpiV := by
    apply ContinuousMap.ext
    intro x
    show ((x : EuclideanSpace ℝ (Fin n)) + a₀) - a₀ = (x : EuclideanSpace ℝ (Fin n))
    rw [add_sub_cancel_right]
  -- ## 5. The conclusions of `germPullbackEuc` at the origin
  have hFres : (Work.Thom.relCohMap F₁C Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hF1a ℤ n).hom ξ
      = sL • (Work.Thom.relCohMap kpiV Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hVz ℤ n).hom ξ :=
    germPullbackEuc hn hV h0V F₁ hF1c hF10 hF1nz L hL hdF1 hdetL ξ
  have hGres : (Work.Thom.relCohMap G₁C Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hG1a ℤ n).hom ξ
      = sM • (Work.Thom.relCohMap kpiV Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hVz ℤ n).hom ξ :=
    germPullbackEuc hn hV h0V G₁ hG1c hG10 hG1nz M hM hdG1 hdetM ξ
  -- ## 6. Pushing the conclusion of `germPullbackEuc` to the pair `(↥W, W∖{a₀})`
  have hid : ∀ y : Work.Thom.RelCoh ℤ n ↥W Bw,
      (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
        ((Work.Thom.relCohMap t Cv Bw ht ℤ n).hom y) = y := by
    intro y
    rw [Work.Thom.relCohMap_compA_apply Bw Cv Bw sinv t hsinv ht hTs ℤ n y]
    rw [Work.Thom.relCohMap_congrA Bw Bw hts hTs (fun _ h => h) ℤ n]
    exact congrArg (fun φ => φ.hom y) (Work.Thom.relCohMap_idA Bw ℤ n)
  have hF1 : (Work.Thom.relCohMap F₁C Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hF1a ℤ n).hom ξ
      = (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ) := by
    rw [← Work.Thom.relCohMap_congrA Cv ({0}ᶜ) hcomp1map hc1 hF1a ℤ n]
    rw [← Work.Thom.relCohMap_compA_apply Cv Bw ({0}ᶜ) t (kpFW W F hFc) ht hFW hc1 ℤ n ξ]
  have hG1 : (Work.Thom.relCohMap G₁C Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hG1a ℤ n).hom ξ
      = (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ) := by
    rw [← Work.Thom.relCohMap_congrA Cv ({0}ᶜ) hcomp3map hc3 hG1a ℤ n]
    rw [← Work.Thom.relCohMap_compA_apply Cv Bw ({0}ᶜ) t (kpFW W G hGc) ht hGW hc3 ℤ n ξ]
  have hF2 : (Work.Thom.relCohMap kpiV Cv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) hVz ℤ n).hom ξ
      = (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ) := by
    rw [← Work.Thom.relCohMap_congrA Cv ({0}ᶜ) hcomp2map hc2 hVz ℤ n]
    rw [← Work.Thom.relCohMap_compA_apply Cv Bw ({0}ᶜ) t tauW ht hτw hc2 ℤ n ξ]
  -- ## 7. The two halves, in `H^n(↥W, W∖{a₀})`
  have hFhalf : (Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ
      = sL • (Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ := by
    have h3 : (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ)
        = sL • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ) := by
      calc (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
            ((Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ)
          = (Work.Thom.relCohMap F₁C Cv ({0}ᶜ) hF1a ℤ n).hom ξ := hF1.symm
        _ = sL • (Work.Thom.relCohMap kpiV Cv ({0}ᶜ) hVz ℤ n).hom ξ := hFres
        _ = sL • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ) := by rw [hF2]
    calc (Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ
        = (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            ((Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ)) :=
          (hid ((Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ)).symm
      _ = (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            (sL • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)) := by rw [h3]
      _ = sL • (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            ((Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)) := map_zsmul _ sL _
      _ = sL • (Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ := by
          rw [hid ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)]
  have hGhalf : (Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ
      = sM • (Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ := by
    have h3 : (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ)
        = sM • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
          ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ) := by
      calc (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
            ((Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ)
          = (Work.Thom.relCohMap G₁C Cv ({0}ᶜ) hG1a ℤ n).hom ξ := hG1.symm
        _ = sM • (Work.Thom.relCohMap kpiV Cv ({0}ᶜ) hVz ℤ n).hom ξ := hGres
        _ = sM • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ) := by rw [hF2]
    calc (Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ
        = (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            ((Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ)) :=
          (hid ((Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ)).symm
      _ = (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            (sM • (Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)) := by rw [h3]
      _ = sM • (Work.Thom.relCohMap sinv Bw Cv hsinv ℤ n).hom
            ((Work.Thom.relCohMap t Cv Bw ht ℤ n).hom
              ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)) := map_zsmul _ sM _
      _ = sM • (Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ := by
          rw [hid ((Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ)]
  -- ## 8. Assembly
  have hsMsq : sM * sM = 1 := by
    rw [hsM]
    split_ifs <;> norm_num
  have hZ : (Work.Thom.relCohMap tauW Bw ({0}ᶜ) hτw ℤ n).hom ξ
      = sM • (Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ := by
    rw [hGhalf, smul_smul, hsMsq, one_smul]
  show (Work.Thom.relCohMap (kpFW W F hFc) Bw ({0}ᶜ) hFW ℤ n).hom ξ
      = (sL * sM) • (Work.Thom.relCohMap (kpFW W G hGc) Bw ({0}ᶜ) hGW ℤ n).hom ξ
  rw [hFhalf, hZ, smul_smul]

end

end Work.ThomBordism.KeyLocal
