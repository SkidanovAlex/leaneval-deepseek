import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.crit_of_parts
import Submission.Work.Horn.cov_of_parts
import Submission.Work.Horn.surj_of_parts
import Submission.Work.Horn.inf_of_parts
import Submission.Work.Horn.varphi_image_BuOf
import Submission.Work.Horn.Phi_fiber_infinite
import Submission.Work.Horn.two_preimages_of_regular_value

/-!
# `Work.Horn.assembly` — the `∀`-form pieces consumed by `horn_of_parts`

`Work.Horn.horn_of_parts` (`Horn/hornOfParts.lean`) builds `HornStatement` from the lead's pieces
and the four assembly conclusions `crit`, `cov`, `surj`, `inf` in `∀`-form.  This file turns the
proved lemmas (`crit_of_parts`, `cov_of_parts`, `surj_of_parts`, `inf_of_parts`,
`varphi_image_BuOf`, `Phi_fiber_infinite`, `two_preimages_of_regular_value`) into exactly those
`∀`-forms, so that the final `horn.lean` is a single application.
-/

namespace Work.Horn

noncomputable section

open MandelDim Set Filter Topology

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : MandelDim.ParabData f₀ D₀}

/-- Every point of the immediate basin is in the domain of `f₀` (via `B ⊆ basin ⊆ D₀`). -/
theorem immediateBasin_subset_D₀ (hB : MandelDim.IsImmediateBasin f₀ D₀ B) : B ⊆ D₀ := by
  intro z hz
  obtain ⟨U, hU, hmap, -⟩ := hB.2.2.1 hz
  exact hmap 0 (mem_of_mem_nhds hU)

/-- `f₀` is not locally constant at the critical point (else `{c}` would be open in `ℂ`). -/
theorem not_eventually_const_at_critical (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ¬ ∀ᶠ z in nhds c, f₀ z = f₀ c := by
  obtain ⟨hgerm, hB, hcB, hc0, huniq⟩ := hsetup
  intro hev
  have hBopen : IsOpen B := hB.1
  obtain ⟨U, hUsub, hUopen, hcU⟩ := mem_nhds_iff.mp hev
  have hUc : U ∩ B = {c} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · have h1 : f₀ =ᶠ[nhds z] fun _ : ℂ => f₀ c := by
        filter_upwards [hUopen.mem_nhds hz.1] with w hw
        exact hUsub hw
      have h2 : deriv f₀ z = 0 := by
        rw [h1.deriv_eq]
        simp
      exact huniq z hz.2 h2
    · rw [Set.mem_singleton_iff] at hz
      exact ⟨hz ▸ hcU, hz ▸ hcB⟩
  have hopen : IsOpen ({c} : Set ℂ) := by
    have h1 : IsOpen (U ∩ B) := hUopen.inter hBopen
    rwa [hUc] at h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c (Set.mem_singleton c)
  have hmem : c + (ε / 2 : ℝ) ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : c + (ε / 2 : ℝ) - c = ((ε / 2 : ℝ) : ℂ) := by ring
    have h3 : ‖((ε / 2 : ℝ) : ℂ)‖ = |(ε / 2 : ℝ)| := RCLike.norm_ofReal (ε / 2)
    rw [h2, h3, abs_of_pos (by positivity)]
    linarith
  have h3 := hball hmem
  rw [Set.mem_singleton_iff] at h3
  have h4 : ((ε / 2 : ℝ) : ℂ) = 0 := by
    have : c + (ε / 2 : ℝ) - c = 0 := by rw [h3]; ring
    simpa using this
  have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h4
  linarith

/-- **Two distinct preimages of a regular value**, from `IsF0Setup`. -/
theorem two_preimages_of_setup (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ a ∈ B, a ≠ f₀ c →
      ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ f₀ x = a ∧ f₀ y = a := by
  have hnc := not_eventually_const_at_critical hsetup
  intro a haB ha
  obtain ⟨hgerm, hB, hcB, hc, huniq⟩ := hsetup
  exact two_preimages_of_regular_value hB.1 hB.2.1
    (hgerm.2.2.1.mono (immediateBasin_subset_D₀ hB)) hB.2.2.2.2.1
    hB.2.2.2.2.2.2 hcB hc huniq hnc haB ha

/-- **`Φ` has infinite fibres**, from `IsF0Setup` and `HornPhiStatement`. -/
theorem Phi_fiber_infinite_of_parts (hPhi : MandelDim.HornPhiStatement)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ y : ℂ, {z : ℂ | z ∈ B ∧ d.Φ z = y}.Infinite :=
  Phi_fiber_infinite d hsetup.2.1 hsetup.2.2.1
    (two_preimages_of_setup hsetup) ((hPhi f₀ D₀ B c d hsetup).1)

/-! ## The four `∀`-forms consumed by `horn_of_parts` -/

theorem crit_from_parts (hPhi : MandelDim.HornPhiStatement)
    (hVarphi : MandelDim.HornVarphiStatement) :
    ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      ∀ w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B, deriv d.E w = 0 →
        ∃ k : ℤ, d.E w = d.Φ c + k :=
  fun f₀ D₀ B c d h => crit_of_parts hPhi hVarphi f₀ D₀ B c d h

theorem cov_from_parts (hTopo : MandelDim.HornTopoStatement)
    (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement)
    (hSC : MandelDim.HornSCStatement) :
    ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x)
        {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
      IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x)
        {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} :=
  fun f₀ D₀ B c d h => cov_of_parts hTopo hPhi hVarphi hSC f₀ D₀ B c d h

theorem surj_from_parts (hTopo : MandelDim.HornTopoStatement)
    (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement)
    (hSC : MandelDim.HornSCStatement) :
    ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      (∀ y : ℂ, ∃ w ∈ MandelDim.BuOf d B, d.E w = y) ∧
      (∀ y : ℂ, ∃ w ∈ MandelDim.BlOf d B, d.E w = y) :=
  fun f₀ D₀ B c d h =>
    surj_of_parts hTopo hPhi f₀ D₀ B c d h (varphi_image_BuOf hTopo hVarphi hSC f₀ D₀ B c d h)

theorem inf_from_parts (hTopo : MandelDim.HornTopoStatement)
    (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement)
    (hSC : MandelDim.HornSCStatement) :
    ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite) ∧
      (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BlOf d B ∧ d.E w = y}).Infinite) :=
  fun f₀ D₀ B c d h =>
    inf_of_parts hTopo f₀ D₀ B c d h (varphi_image_BuOf hTopo hVarphi hSC f₀ D₀ B c d h)
      (Phi_fiber_infinite_of_parts hPhi h)

end

end Work.Horn
