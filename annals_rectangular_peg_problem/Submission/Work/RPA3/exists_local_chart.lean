import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp

namespace Work.RPA3

/-- **D2, the local inverse chart.**  If `thetaP L` is `C⁷` and a local diffeomorphism at every
point of the strip (`hdiff`), then at each point `w` of the strip there is an open neighbourhood `U`
of `thetaP L w` and a `C⁷` map `σ` on `U` which is a right inverse of `thetaP L` and satisfies
`σ (thetaP L w) = w.2`.

Proof: use the `C^r` inverse function theorem, `ContDiffAt.toOpenPartialHomeomorph` and
`ContDiffAt.localInverse` in `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`;
`hdiff` provides the invertible derivative of `thetaP L` at `w` and `hsm` the `C⁷` regularity, so
the local inverse is `C⁷` near `thetaP L w`, satisfies `g (thetaP L w) = w`, and
`thetaP L (g p) = p` on its target `U`.  Since `thetaP` preserves the first coordinate, the section
`σ p := (g p).2` is `C⁷` on `U` and satisfies both claims. -/
theorem exists_local_chart (L : Work.RPA3.LagFamilyAll) (ε : ℝ)
    (hsm : ContDiff ℝ 7 (fun w : ℝ × Work.RPA3.PS => Work.RPA3.thetaP L w))
    (hdiff : ∀ w : ℝ × Work.RPA3.PS, w.1 ∈ Set.Icc (-1 : ℝ) 2 → |w.2.1.1| ≤ L.X0 + 1 →
      ‖w.2.2‖ < ε → Work.RPA3.IsLocDiffeoAt L w)
    (w : ℝ × Work.RPA3.PS) (hτ : w.1 ∈ Set.Icc (-1 : ℝ) 2) (hx : |w.2.1.1| ≤ L.X0 + 1)
    (hξ : ‖w.2.2‖ < ε) :
    ∃ (U : Set (ℝ × Work.RPA3.PS)) (σ : ℝ × Work.RPA3.PS → Work.RPA3.PS), IsOpen U ∧
      Work.RPA3.thetaP L w ∈ U ∧ σ (Work.RPA3.thetaP L w) = w.2 ∧ ContDiffOn ℝ 7 σ U ∧
      ∀ p ∈ U, Work.RPA3.thetaP L (p.1, σ p) = p := by
  -- the local inverse of `thetaP L` at `w`, from the `C^7` inverse function theorem
  obtain ⟨F', hF'⟩ := hdiff w hτ hx hξ
  have hcd : ContDiffAt ℝ 7 (thetaP L) w := hsm.contDiffAt
  have h7 : (7 : WithTop ℕ∞) ≠ 0 := by norm_num
  let g : ℝ × PS → ℝ × PS := ContDiffAt.localInverse hcd hF' h7
  have hg_img : g (thetaP L w) = w := ContDiffAt.localInverse_apply_image hcd hF' h7
  have hg_cd : ContDiffAt ℝ 7 g (thetaP L w) := ContDiffAt.to_localInverse hcd hF' h7
  have hright : ∀ᶠ p in nhds (thetaP L w), thetaP L (g p) = p :=
    (hcd.hasStrictFDerivAt' hF' h7).eventually_right_inverse
  -- an open neighbourhood of `thetaP L w` on which `g` is `C^7` and is a right inverse
  obtain ⟨u, hu_mem, hu_con⟩ := hg_cd.contDiffOn le_rfl (fun h => by simp at h)
  have hmem : u ∩ {p | thetaP L (g p) = p} ∈ nhds (thetaP L w) :=
    Filter.inter_mem hu_mem hright
  obtain ⟨U, hUsub, hUopen, hUw⟩ := mem_nhds_iff.mp hmem
  -- the section `σ p = (g p).2`; `thetaP` preserves the first coordinate, so it is a right inverse
  refine ⟨U, fun p => (g p).2, hUopen, hUw, congrArg Prod.snd hg_img, ?_, ?_⟩
  · exact (hu_con.mono (hUsub.trans Set.inter_subset_left)).snd
  · intro p hp
    have hge : thetaP L (g p) = p := (hUsub hp).2
    have h1 : (g p).1 = p.1 := by
      have := congrArg Prod.fst hge
      simpa [thetaP] using this
    calc thetaP L (p.1, (g p).2) = thetaP L ((g p).1, (g p).2) := by rw [h1]
      _ = thetaP L (g p) := rfl
      _ = p := hge

end Work.RPA3
