import Mathlib
import Submission.Work.Mostow.conjCountGeodV2
import Submission.Work.Mostow.geodSetup

/-!
# `conjGeodStabOfCommuting`

If `a` and `c` commute, `Fix a = stdTG 1 m` (the standard totally geodesic copy of `ℍ¹`),
`c` fixes a point `p` and is `θ`-near the identity there with `θ < 2`, and the fixed set of `c`
is `γ⁻¹ (stdTG 1 m)` (i.e. `c • y = y ↔ γ • y ∈ stdTG 1 m`), then `γ` preserves `stdTG 1 m`.

The argument is the "flip" argument of `conjCountGeodV2`: an isometry of the geodesic
`stdTG 1 m ≅ ℍ¹ ≅ ℝ` that fixes a point `p` of it and moves every point of the unit ball about
`p` by less than `2` must fix the geodesic pointwise (the alternative is the reflection about
`p`, which moves either neighbour of `p` at distance `1` by exactly `2`). Since `c` commutes
with `a` it preserves `Fix a = stdTG 1 m`; applying the flip argument to `c` on `Fix a` gives
`stdTG 1 m ⊆ Fix c`, and applying it to `a` on `Fix c = γ⁻¹(stdTG 1 m)` gives the reverse
inclusion.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **the one-dimensional flip.**  An isometry `b` of `ℍ^(1+m)` which preserves the standard
geodesic `stdTG 1 m` setwise, fixes one of its points `p` and is `θ`-near the identity at `p`
with `θ < 2`, fixes `stdTG 1 m` pointwise. -/
theorem fixes_stdTG_of_nearId (m : ℕ) (hA : POActionProp (1 + m))
    (hI : HypIsometryProp (1 + m)) (b : PO (1 + m) 1) (p : E (1 + m)) (θ : ℝ) (hθ : θ < 2)
    (hpF : p ∈ stdTG 1 m) (hp : b • p = p) (hnear : NearIdAt b p θ)
    (hpre : ∀ t : ℝ, ∃ t', b • (arcGeo m t) = arcGeo m t') :
    ∀ u : E (1 + m), u ∈ stdTG 1 m → b • u = u := by
  have hF_arc : ∀ u : E (1 + m), u ∈ stdTG 1 m ↔ u ∈ Set.range (arcGeo m) := by
    intro u; rw [range_arcGeo m, range_phi m]
  obtain ⟨tp, htp⟩ : ∃ t : ℝ, arcGeo m t = p := (hF_arc p).mp hpF
  intro u hu
  obtain ⟨t, ht⟩ := (hF_arc u).mp hu
  rw [← ht]
  exact flips_fix_geodesic hA hI b (arcGeo m) tp θ (hdist_arcGeo m) hpre
    (by rw [htp]; exact hp) (by rw [htp]; exact hnear) hθ t

theorem conjGeodStabOfCommuting (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (a c γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (p : Submission.Mostow.E (1 + m)) (θ : ℝ) (hθ : θ < 2)
    (hcomm : a * c = c * a)
    (haFix : ∀ y : Submission.Mostow.E (1 + m), a • y = y ↔ y ∈ Submission.Mostow.stdTG 1 m)
    (hcFix : ∀ y : Submission.Mostow.E (1 + m), c • y = y ↔ γ • y ∈ Submission.Mostow.stdTG 1 m)
    (hp : a • p = p) (hcp : c • p = p)
    (hneara : Submission.Mostow.NearIdAt a p θ) (hnearc : Submission.Mostow.NearIdAt c p θ) :
    γ ∈ Submission.Mostow.SetStabStd 1 m := by
  have hb := POBasic.ofProp hA
  have hid := HypIsoData.ofProp hI
  -- commutation, on points
  have hcomm_ac : ∀ x : E (1 + m), a • (c • x) = c • (a • x) := by
    intro x
    rw [← hb.mul_smul a c x, hcomm, hb.mul_smul c a x]
  have hF_arc : ∀ u : E (1 + m), u ∈ stdTG 1 m ↔ u ∈ Set.range (arcGeo m) := by
    intro u; rw [range_arcGeo m, range_phi m]
  have hpF : p ∈ stdTG 1 m := (haFix p).mp hp
  -- ## First flip: `c` acts trivially on `Fix a = stdTG 1 m`
  have hpre1 : ∀ t : ℝ, ∃ t', c • (arcGeo m t) = arcGeo m t' := by
    intro t
    have hfixpsi : a • (arcGeo m t) = arcGeo m t :=
      (haFix _).mpr ((hF_arc _).mpr ⟨t, rfl⟩)
    have hc : a • (c • (arcGeo m t)) = c • (arcGeo m t) := by
      rw [hcomm_ac, hfixpsi]
    obtain ⟨t', ht'⟩ := (hF_arc _).mp ((haFix _).mp hc)
    exact ⟨t', ht'.symm⟩
  have hcfixF : ∀ u : E (1 + m), u ∈ stdTG 1 m → c • u = u :=
    fixes_stdTG_of_nearId m hA hI c p θ hθ hpF hcp hnearc hpre1
  -- ## Second flip: `a` acts trivially on `Fix c = γ⁻¹ (stdTG 1 m)`
  have hγγinv : ∀ u : E (1 + m), γ • (γ⁻¹ • u) = u := fun u => by
    rw [← hb.mul_smul γ γ⁻¹ u, mul_inv_cancel, hb.one_smul]
  have hγinvγ : ∀ u : E (1 + m), γ⁻¹ • (γ • u) = u := fun u => by
    rw [← hb.mul_smul γ⁻¹ γ u, inv_mul_cancel, hb.one_smul]
  set ψ2 : ℝ → E (1 + m) := fun t => γ⁻¹ • arcGeo m t with hψ2def
  have hψ2val : ∀ t : ℝ, ψ2 t = γ⁻¹ • arcGeo m t := fun t => by rw [hψ2def]
  have hFixc : ∀ y : E (1 + m), c • y = y ↔ y ∈ Set.range ψ2 := by
    intro y
    rw [hcFix y]
    constructor
    · intro hy
      obtain ⟨s, hs⟩ := (hF_arc (γ • y)).mp hy
      exact ⟨s, by rw [hψ2val s, hs, hγinvγ]⟩
    · rintro ⟨s, hs⟩
      rw [← hs, hψ2val s, hγγinv]
      exact (hF_arc _).mpr ⟨s, rfl⟩
  have hpre2 : ∀ t : ℝ, ∃ t', a • ψ2 t = ψ2 t' := by
    intro t
    have hcfix : c • ψ2 t = ψ2 t := (hFixc (ψ2 t)).mpr ⟨t, rfl⟩
    have hac : c • (a • ψ2 t) = a • ψ2 t := by rw [← hcomm_ac (ψ2 t), hcfix]
    obtain ⟨s, hs⟩ := (hFixc (a • ψ2 t)).mp hac
    exact ⟨s, hs.symm⟩
  obtain ⟨tp2, htp2⟩ : ∃ t : ℝ, ψ2 t = p := by
    have hgp : γ • p ∈ stdTG 1 m := (hcFix p).mp hcp
    obtain ⟨s, hs⟩ := (hF_arc (γ • p)).mp hgp
    exact ⟨s, by rw [hψ2val s, hs, hγinvγ]⟩
  have hafixAll : ∀ t : ℝ, a • ψ2 t = ψ2 t :=
    flips_fix_geodesic hA hI a ψ2 tp2 θ
      (fun s t => by rw [hψ2val s, hψ2val t, hid.isom_smul, hdist_arcGeo m])
      hpre2 (by rw [htp2]; exact hp) (by rw [htp2]; exact hneara) hθ
  -- ## Conclusion
  show ∀ u : E (1 + m), u ∈ stdTG 1 m ↔ γ • u ∈ stdTG 1 m
  intro u
  constructor
  · intro hu
    exact (hcFix u).mp (hcfixF u hu)
  · intro hu
    obtain ⟨s, hs⟩ := (hF_arc (γ • u)).mp hu
    have hus : u = ψ2 s := by rw [hψ2val s, hs, hγinvγ]
    exact (haFix u).mp (by rw [hus]; exact hafixAll s)

end Work.Mostow
