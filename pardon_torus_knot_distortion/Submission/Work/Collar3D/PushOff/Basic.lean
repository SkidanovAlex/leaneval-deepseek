import Submission.Work.Collar3D.PushOff.Defs

/-!
# The elementary properties of the cap

`Work.Collar3D.DiscCollar.cap c ψ` is the push-off of the disc `e` along its collar `c` with
profile `ψ`.  The four properties consumed by the cut-and-paste are proved here:

* `cap_continuous` — the cap is a parametrised disc;
* `cap_injective` — it is embedded;
* `cap_boundary` — it spans the same boundary curve as `e` when `ψ` vanishes on `∂𝔻`;
* `cap_notMem_range` — if `ψ` does not vanish in the interior, the cap misses the disc.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

namespace DiscCollar

variable {e : C(Disc, R3)} (c : DiscCollar e)

/-- **The cap is continuous** for a continuous profile, so that it is a genuine parametrised disc. -/
theorem cap_continuous {ψ : Disc → ℝ} (hψ : Continuous ψ) : Continuous (c.cap ψ) := by
  unfold cap
  exact continuous_subtype_val.comp
    ((c.Φ).symm.continuous.comp (continuous_subtype_val.prodMk hψ))

/-- **The cap of a disc along its collar is embedded.** -/
theorem cap_injective {ψ : Disc → ℝ} : Function.Injective (c.cap ψ) := by
  intro z z' h
  have h1 : (c.Φ).symm ((z : ℂ), ψ z) = (c.Φ).symm ((z' : ℂ), ψ z') := Subtype.ext h
  have h2 : ((z : ℂ), ψ z) = ((z' : ℂ), ψ z') := (c.Φ).symm.injective h1
  exact Subtype.ext (congrArg Prod.fst h2)

/-- **The cap has the same boundary curve as the disc** when the profile vanishes on the boundary
circle. -/
theorem cap_boundary {ψ : Disc → ℝ}
    (hψ : ∀ θ : ℝ, ψ (Work.Smooth.Jordan.circlePoint θ) = 0) (θ : ℝ) :
    c.cap ψ (Work.Smooth.Jordan.circlePoint θ) = e (Work.Smooth.Jordan.circlePoint θ) := by
  rw [cap_apply, hψ θ]
  exact congrArg Subtype.val (c.Φ_symm_zero _)

/-- **The cap is disjoint from the disc except along its boundary curve**: if the profile does not
vanish on the interior of the disc, no interior point of the cap lies on the disc `e(𝔻)`. -/
theorem cap_notMem_range {ψ : Disc → ℝ} (hψ : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ψ z ≠ 0)
    {z : Disc} (hz : ‖(z : ℂ)‖ < 1) : c.cap ψ z ∉ Set.range e := by
  rintro ⟨w, hw⟩
  obtain ⟨z', hz'⟩ := (c.Φ_range ⟨c.cap ψ z, c.cap_mem_U ψ z⟩).mp
    (show c.cap ψ z ∈ Set.range e from ⟨w, hw⟩)
  rw [c.Φ_cap] at hz'
  exact hψ z hz (congrArg Prod.snd hz')

/-- The cap lies on the side of the disc prescribed by the sign of the profile: if `ψ` is positive
on the interior, its interior lies in `side 1`. -/
theorem cap_mem_side {ψ : Disc → ℝ} (hψ : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → 0 < ψ z)
    {z : Disc} (hz : ‖(z : ℂ)‖ < 1) : c.cap ψ z ∈ c.side 1 :=
  ⟨c.cap_mem_U ψ z, by rw [c.Φ_cap]; simpa using hψ z hz⟩

end DiscCollar

end

end Work.Collar3D
