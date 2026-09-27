import Mathlib
import Submission.Work.Mostow.strataGapUniform
import Submission.Work.Mostow.torsionNearIdGeodesic
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.affineIsometryReal
import Submission.Work.Mostow.axisDichotomy

/-!
# The geodesic gap clause of the `k = 1` stratum (`GAP-A`)

`Work.Mostow.geodGapClause` assembles the clause used by
`Work.Mostow.margRegionInvariant` / the design's L4(ii): there is a bound `θ > 0` such that
for every volume bound `V` there is `η₁ ∈ (0, θ]` with the following property.  If `Λ` is
discrete with a fundamental domain `D` of volume `≤ V` (a lattice of covolume `≤ V`), and
`a ∈ Λ` fixes the standard geodesic `stdTG 1 m` pointwise (`a ∈ SetStabStd 1 m` and
`resStd 1 m a = 1`) and is `η₁`-near the identity at some point `u`, then the fixed set of `a`
is exactly `stdTG 1 m` — i.e. `a` is a translation or a flip of that geodesic.

The mathematical content is the Kazhdan–Margulis/stratum gap for torsion elements, packaged
in `Work.Mostow.torsionNearIdGeodesic` (proved from `Work.Mostow.strataGapUniform` and the
unconditional covolume bound `Work.Mostow.covolLB_uncond`): a torsion element of a lattice of
(oriented) covolume `≤ V` that is near the identity must have a *geodesic* as fixed set.  The
remaining step is geometric: a geodesic whose image under a conjugate contains `stdTG 1 m` and
whose fixed set contains `stdTG 1 m` must be `stdTG 1 m` itself.
-/

set_option synthInstance.maxHeartbeats 800000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## Elementary chart and group facts -/

/-- `fermi k m v 0 = coordEmb k m v`: the stratum is the locus of zero normal coordinate. -/
private lemma ggc_fermi_zero (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  have hs : sinhc (0 : ℝ) = 1 := by rw [sinhc]; norm_num
  simp only [fermi, coordEmb, norm_zero, Real.cosh_zero, hs, one_mul]
  congr 1

/-- Arclength parametrisation of the standard geodesic `stdTG 1 m`. -/
private def ggcSig (m : ℕ) (s : ℝ) : E (1 + m) := coordEmb 1 m (AxisDich.pt s)

private lemma ggc_sig_hdist (m : ℕ) (hI : HypIsometryProp (1 + m)) (s t : ℝ) :
    hdist (ggcSig m s) (ggcSig m t) = |s - t| := by
  rw [ggcSig, ggcSig, hdist_coordEmb 1 m hI, AxisDich.hdist_eq_sc, AxisDich.sc_pt,
    AxisDich.sc_pt]

private lemma ggc_stdTG_eq_range (m : ℕ) : stdTG 1 m = Set.range (ggcSig m) := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨AxisDich.sc v, by rw [ggcSig, AxisDich.pt_sc]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨AxisDich.pt s, rfl⟩

/-- **Containment.**  If `h⁻¹` maps the standard geodesic `stdTG 1 m` into itself then so does
`h`: a geodesic line contained in another geodesic line coincides with it. -/
private lemma ggc_smul_mem_stdTG (m : ℕ) (hA : POActionProp (1 + m))
    (hI : HypIsometryProp (1 + m)) (h : PO (1 + m) 1)
    (hsub : ∀ y ∈ stdTG 1 m, h⁻¹ • y ∈ stdTG 1 m) :
    ∀ x ∈ stdTG 1 m, h • x ∈ stdTG 1 m := by
  have hb : POBasic (1 + m) := POBasic.ofProp hA
  have hi : HypIsoData (1 + m) := HypIsoData.ofProp hI
  have hsig : ∀ s t : ℝ, hdist (ggcSig m s) (ggcSig m t) = |s - t| := ggc_sig_hdist m hI
  have hex : ∀ s : ℝ, ∃ t : ℝ, h⁻¹ • ggcSig m s = ggcSig m t := by
    intro s
    have h1 : h⁻¹ • ggcSig m s ∈ stdTG 1 m :=
      hsub (ggcSig m s) (by rw [ggc_stdTG_eq_range]; exact ⟨s, rfl⟩)
    rw [ggc_stdTG_eq_range] at h1
    obtain ⟨t, ht⟩ := h1
    exact ⟨t, ht.symm⟩
  choose φ hφ using hex
  have hmetry : ∀ s t : ℝ, |φ s - φ t| = |s - t| := by
    intro s t
    have h1 := hsig (φ s) (φ t)
    rw [← hφ s, ← hφ t, hi.isom_smul, hsig s t] at h1
    exact h1.symm
  obtain ⟨ε, c, hε, hφaff⟩ := affineIsometryReal φ hmetry
  intro x hx
  rw [ggc_stdTG_eq_range] at hx ⊢
  obtain ⟨u, rfl⟩ := hx
  refine ⟨ε * (u - c), ?_⟩
  have h1 : h⁻¹ • ggcSig m (ε * (u - c)) = ggcSig m u := by
    rw [hφ (ε * (u - c)), hφaff (ε * (u - c))]
    congr 1
    rcases hε with hε | hε <;> rw [hε] <;> ring
  calc ggcSig m (ε * (u - c)) = h • (h⁻¹ • ggcSig m (ε * (u - c))) := by
        rw [← hb.mul_smul h h⁻¹ (ggcSig m (ε * (u - c))), mul_inv_cancel, hb.one_smul]
    _ = h • ggcSig m u := by rw [h1]

/-! ## The clause -/

theorem geodGapClause (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ V : ℝ, 0 < V → ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ θ ∧
      ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (D : Set (Submission.Mostow.E (1 + m))) (a : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (u : Submission.Mostow.E (1 + m)),
        _root_.IsDiscrete (SetLike.coe Λ) → MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (1 + m)) →
        Submission.Mostow.volH (1 + m) D ≤ ENNReal.ofReal V →
        a ∈ Λ → a ∈ Submission.Mostow.SetStabStd 1 m → Submission.Mostow.resStd 1 m a = 1 → a ≠ 1 →
        Submission.Mostow.NearIdAt a u η₁ → Submission.Mostow.fixSet a = Submission.Mostow.stdTG 1 m := by
  -- the action/isometry axioms in every dimension (unconditional in this workspace)
  have hAk : ∀ k, 1 ≤ k → POActionProp k := fun k hk => poAction_ge1 k hk
  have hIk : ∀ k, 1 ≤ k → HypIsometryProp k := fun k hk => hypIsometry_ge1 k hk (poAction_ge1 k hk)
  -- the gap constants of the stratum inequality, and the unconditional covolume bound
  obtain ⟨θ₀, c, α, hθ₀, hc, hα, hgap⟩ :=
    strataGapUniform m hm hev hAk hIk (fun j hj _ => covolLB_uncond j hj)
  -- `θ = 1` is an arbitrary positive upper bound for `η₁`; `η₁` is chosen from `V`
  refine ⟨1, one_pos, fun V _hV => ?_⟩
  obtain ⟨ηtd, hηtdpos, hηtd⟩ :=
    torsionNearIdGeodesic m hm hev hAk hIk θ₀ c α hθ₀ hc hα hgap V
  refine ⟨min 1 ηtd, lt_min one_pos hηtdpos, min_le_left _ _, ?_⟩
  intro Λ D a u hdisc hfd hvol ha_mem ha_stab ha_res ha_ne ha_near
  have hb : POBasic (1 + m) := POBasic.ofProp hA
  -- (1) `a` is a block with trivial stratum part
  have hblk : a = blk 1 m 1 (nrmStd 1 m a) := by
    have h := stab_eq_blk 1 m hA1 hI1 hA hI a ha_stab
    rw [ha_res] at h
    exact h
  -- (2) `a` fixes `stdTG 1 m` pointwise
  have hfixpt : ∀ v : E 1, a • coordEmb 1 m v = coordEmb 1 m v := by
    intro v
    rw [hblk, ← ggc_fermi_zero 1 m v,
      blk_smul_fermi 1 m hA1 hI1 hA hI 1 (nrmStd 1 m a) v 0, hA1.2.2.2.1 v, map_zero]
  -- (3) `a` has finite order (it fixes the interior point `coordEmb 1 m 0`)
  have htor : IsOfFinOrder a :=
    gapA.isOfFinOrder_of_fixes_point (1 + m) hA hI Λ hdisc a ha_mem (coordEmb 1 m (0 : E 1))
      (hfixpt 0)
  -- (4) the Kazhdan–Margulis stratum gap for torsion elements
  obtain ⟨h, R, hRfree, hah⟩ :=
    hηtd (min 1 ηtd) (lt_min one_pos hηtdpos) (min_le_right _ _) Λ D u a hdisc hfd hvol ha_mem
      ha_ne htor ha_near
  -- (5) `a` is conjugate to the block `blk 1 m 1 R`
  have ha_eq : a = h * blk 1 m 1 R * h⁻¹ := by
    calc a = a * (h * h⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = (a * h) * h⁻¹ := (mul_assoc a h h⁻¹).symm
      _ = (h * blk 1 m 1 R) * h⁻¹ := by rw [hah]
      _ = h * blk 1 m 1 R * h⁻¹ := rfl
  have hab : ∀ z : E (1 + m), a • z = h • (blk 1 m 1 R • (h⁻¹ • z)) := by
    intro z
    calc a • z = (h * blk 1 m 1 R * h⁻¹) • z := by rw [ha_eq]
      _ = h • (blk 1 m 1 R • (h⁻¹ • z)) := by
            rw [hb.mul_smul (h * blk 1 m 1 R) h⁻¹ z, hb.mul_smul h (blk 1 m 1 R) (h⁻¹ • z)]
  have hfixpt' : ∀ x ∈ stdTG 1 m, a • x = x := by
    rintro x ⟨v, rfl⟩
    exact hfixpt v
  -- (6) fixed points of `a` lie on the conjugate geodesic, i.e. `h⁻¹` maps `stdTG` into itself
  have haux : ∀ z : E (1 + m), a • z = z → h⁻¹ • z ∈ stdTG 1 m := by
    intro z hz
    have h2 : h • (blk 1 m 1 R • (h⁻¹ • z)) = h • (h⁻¹ • z) := by
      rw [← hab z, hz, ← hb.mul_smul h h⁻¹ z, mul_inv_cancel, hb.one_smul]
    have h4 := congrArg (fun w : E (1 + m) => h⁻¹ • w) h2
    rw [← hb.mul_smul h⁻¹ h (blk 1 m 1 R • (h⁻¹ • z)), inv_mul_cancel, hb.one_smul,
      ← hb.mul_smul h⁻¹ h (h⁻¹ • z), inv_mul_cancel, hb.one_smul] at h4
    have h5 : h⁻¹ • z ∈ fixSet (blk 1 m 1 R) := h4
    rwa [fixSet_blk_eq_stdTG 1 m hA1 hI1 hA hI R hRfree] at h5
  have hsub : ∀ y ∈ stdTG 1 m, h⁻¹ • y ∈ stdTG 1 m :=
    fun y hy => haux y (hfixpt' y hy)
  -- (7) consequently `h` maps `stdTG` into itself, and the fixed set of `a` is `stdTG`
  have hmem : ∀ x ∈ stdTG 1 m, h • x ∈ stdTG 1 m := ggc_smul_mem_stdTG m hA hI h hsub
  ext u
  constructor
  · intro hu
    have h1 : h⁻¹ • u ∈ stdTG 1 m := haux u hu
    have h2 : h • (h⁻¹ • u) ∈ stdTG 1 m := hmem (h⁻¹ • u) h1
    have h3 : h • (h⁻¹ • u) = u := by
      rw [← hb.mul_smul h h⁻¹ u, mul_inv_cancel, hb.one_smul]
    rwa [h3] at h2
  · intro hu
    exact hfixpt' u hu

end

end Work.Mostow
