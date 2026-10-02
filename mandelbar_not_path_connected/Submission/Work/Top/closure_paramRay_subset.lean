/-
# The closure of a parameter ray meets `Mb` only at the endpoints of the exterior

This module proves that the closure of the parameter ray of angle `θ` is contained in the
union of the ray itself with the connectedness locus `Mb`.  Equivalently: a point of `Mbᶜ`
which is the limit of points of the ray already lies *on* the ray.

The argument uses only the Nakane interface `NakaneData`:

* `Φ` is a homeomorphism `Mbᶜ ≃ₜ exteriorDisc`, so in particular `Φ` is continuous on the
  open set `Mbᶜ` (here `Mb` is closed, being the zero set of the continuous potential);
* the ray condition `Φ c = rayPoint θ t` (`t > 1`) is equivalent, after multiplying by the
  conjugate of the unit complex number `u = exp (2πiθ)`, to `Φ c * conj u` being a real
  number `t > 1`;
* closedness of `[1, ∞) ⊆ ℂ` (the image of `Ici 1` under the closed embedding `ℝ → ℂ`) then
  gives, by continuity, that the limit also satisfies `Φ c * conj u = r ≥ 1`, and since
  `c ∉ Mb` forces `‖Φ c‖ > 1`, we get `r > 1`.
-/
import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Set Filter Topology

/-- The image of `[1, ∞)` under the closed embedding `ℝ → ℂ` is closed in `ℂ`. -/
theorem isClosed_image_ofReal_Ici : IsClosed (((↑) '' Set.Ici (1 : ℝ)) : Set ℂ) := by
  rw [← closure_eq_iff_isClosed, Complex.isometry_ofReal.isClosedEmbedding.closure_image_eq,
    closure_Ici]

theorem closure_paramRay_subset {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) :
    closure (Work.Top.NakaneData.paramRay hN θ) ⊆ Work.Top.NakaneData.paramRay hN θ ∪ Mb := by
  -- `Φ` is continuous on the open set `Mbᶜ`
  have hΦcont : ContinuousOn Φ Mbᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp hN.e.continuous).congr fun x => (hN.he x).symm
  -- the unit complex number `u = exp (2πiθ)` giving the direction of the ray
  set u : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hu
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hu_conj_mul : (starRingEnd ℂ) u * u = 1 := by
    rw [Complex.conj_mul', hu_norm]; norm_num
  have hu_mul_conj : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj', hu_norm]; norm_num
  -- the ray points are exactly the positive multiples of `u`
  have hray : ∀ t : ℝ, Work.Top.NakaneData.rayPoint θ t = (↑t : ℂ) * u := by
    intro t; rw [Work.Top.NakaneData.rayPoint, ← hu]
  intro c hc
  by_cases hcm : c ∈ Mb
  · exact Or.inr hcm
  refine Or.inl ?_
  rw [NakaneData.mem_paramRay_iff]
  have hopen : IsOpen Mbᶜ := hN.isClosed_mb.isOpen_compl
  have hca : ContinuousAt Φ c := hΦcont.continuousAt (hopen.mem_nhds hcm)
  have hFcont : ContinuousAt (fun z : ℂ => Φ z * (starRingEnd ℂ) u) c := hca.mul_const _
  -- points of the ray are mapped by `z ↦ Φ z * conj u` into `[1, ∞) ⊆ ℂ`
  have hmaps : Set.MapsTo (fun z : ℂ => Φ z * (starRingEnd ℂ) u) (NakaneData.paramRay hN θ)
      (((↑) '' Set.Ici (1:ℝ)) : Set ℂ) := by
    intro z hz
    obtain ⟨hzMb, t, ht, hΦz⟩ := hz
    refine ⟨t, ht.le, ?_⟩
    change (↑t : ℂ) = Φ z * (starRingEnd ℂ) u
    rw [hΦz, hray t, mul_assoc, hu_mul_conj, mul_one]
  have hmem : Φ c * (starRingEnd ℂ) u ∈ (((↑) '' Set.Ici (1:ℝ)) : Set ℂ) := by
    have h1 : Φ c * (starRingEnd ℂ) u ∈
        closure ((fun z : ℂ => Φ z * (starRingEnd ℂ) u) '' NakaneData.paramRay hN θ) :=
      mem_closure_image hFcont hc
    exact (closure_minimal (fun w hw => by obtain ⟨z, hz, rfl⟩ := hw; exact hmaps hz)
      isClosed_image_ofReal_Ici) h1
  obtain ⟨r, hr, hr_eq⟩ := hmem
  have hr_eq' : Φ c * (starRingEnd ℂ) u = (↑r : ℂ) := hr_eq.symm
  -- undo the rotation: `Φ c = r * u`
  have hPhi : Φ c = (↑r : ℂ) * u := by
    have h2 := congrArg (fun w : ℂ => w * u) hr_eq'
    rw [mul_assoc, hu_conj_mul, mul_one] at h2
    exact h2
  have hnorm : ‖Φ c‖ = r := by
    have h0 : 0 ≤ r := le_trans zero_le_one (mem_Ici.mp hr)
    rw [hPhi, norm_mul, hu_norm, mul_one]
    simp [abs_of_nonneg h0]
  have hgt : 1 < r := by
    rw [← hnorm]; exact hN.Phi_mem_exteriorDisc hcm
  exact ⟨hcm, r, hgt, by rw [hPhi, hray r]⟩

end Work.Top
