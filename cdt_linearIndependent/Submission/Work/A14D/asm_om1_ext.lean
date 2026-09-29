import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.su_om1_pieces
import Submission.Work.A14D.pieces_seeds
import Submission.Work.A14D.om1_minus_two_cover
import Submission.Work.A14D.om1_geometry
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.OdeCont.uniqueness

/-!
# An independent proof of `Work.A14D.exists_sol_Om1_of_sol_SU`

A solution of the linear system `Y' = A(z)·Y + b(z)` on `SU ∖ {2}` extends to the punctured slit
plane `Om1 ∖ {2}`.  The four convex open pieces `pieceU, pieceD, piece1, piece2` cover
`Om1 ∖ {2}` (`Work.A14D.om1_minus_two_cover`), each meets `SU ∖ {2}` in a nonempty convex open
set (`Work.A14D.pieces_seeds`), and the overlap graph (U–1, D–1, U–2, D–2) is connected.  So the
solution extends to each piece (`Work.C17g.linear_ode_convex`), the pieces agree on the overlaps
(`Work.OdeCont.uniqueness`) and glue.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

private lemma isOpen_pieceU : IsOpen pieceU := isOpen_lt continuous_const Complex.continuous_im
private lemma convex_pieceU : Convex ℝ pieceU := convex_halfSpace_im_gt 0
private lemma isOpen_pieceD : IsOpen pieceD := isOpen_lt Complex.continuous_im continuous_const
private lemma convex_pieceD : Convex ℝ pieceD := convex_halfSpace_im_lt 0
private lemma isOpen_piece1 : IsOpen piece1 :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
private lemma convex_piece1 : Convex ℝ piece1 :=
  (convex_halfSpace_re_gt 1).inter (convex_halfSpace_re_lt 2)
private lemma isOpen_piece2 : IsOpen piece2 := isOpen_lt continuous_const continuous_re
private lemma convex_piece2 : Convex ℝ piece2 := convex_halfSpace_re_gt 2

private lemma pieceU_sub : pieceU ⊆ Om1 \ ({2} : Set ℂ) := by
  intro z hz
  have hz' : 0 < z.im := by simpa only [pieceU, Set.mem_ofPred_eq] using hz
  refine ⟨Or.inl (ne_of_gt hz'), ?_⟩
  intro h2
  rw [h2] at hz'
  norm_num at hz'

private lemma pieceD_sub : pieceD ⊆ Om1 \ ({2} : Set ℂ) := by
  intro z hz
  have hz' : z.im < 0 := by simpa only [pieceD, Set.mem_ofPred_eq] using hz
  refine ⟨Or.inl (ne_of_lt hz'), ?_⟩
  intro h2
  rw [h2] at hz'
  norm_num at hz'

private lemma piece1_sub : piece1 ⊆ Om1 \ ({2} : Set ℂ) := by
  intro z hz
  have hz' : 1 < z.re ∧ z.re < 2 := by simpa only [piece1, Set.mem_ofPred_eq] using hz
  refine ⟨Or.inr hz'.1, ?_⟩
  intro h2
  rw [h2] at hz'
  norm_num at hz'

private lemma piece2_sub : piece2 ⊆ Om1 \ ({2} : Set ℂ) := by
  intro z hz
  have hz' : 2 < z.re := by simpa only [piece2, Set.mem_ofPred_eq] using hz
  refine ⟨Or.inr (by linarith), ?_⟩
  intro h2
  rw [h2] at hz'
  norm_num at hz'

/-- A solution on a convex open set extends to a convex open superset. -/
private theorem asm_sol_extend {k : ℕ} {U V : Set ℂ} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hUV : U ⊆ V)
    {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) V)
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) V)
    {Y : ℂ → Fin k → ℂ} (hYd : DifferentiableOn ℂ Y U)
    (hY : ∀ z ∈ U, HasDerivAt Y (fun i => Finset.univ.sum (fun j => A z i j * Y z j) + b z i) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ F : ℂ → Fin k → ℂ, DifferentiableOn ℂ F V ∧
      (∀ z ∈ V, HasDerivAt F (fun i => Finset.univ.sum (fun j => A z i j * F z j) + b z i) z) ∧
      Set.EqOn F Y U := by
  obtain ⟨F, hFd, hFz₀, hFode⟩ := Work.C17g.linear_ode_convex hVc hVo A b
    (differentiableOn_pi.mpr fun i => differentiableOn_pi.mpr fun j => hA i j)
    (differentiableOn_pi.mpr fun i => hb i) z₀ (hUV hz₀) (Y z₀)
  refine ⟨F, hFd, hFode, ?_⟩
  refine Work.OdeCont.uniqueness hUo hUc.isPreconnected A b
    (fun i j => (hA i j).mono hUV) (fun i => (hb i).mono hUV) F Y (hFd.mono hUV) hYd
    ?_ ?_ hz₀ hFz₀
  · intro z hz; exact hFode z (hUV hz)
  · intro z hz; exact hY z hz

theorem asm_exists_sol_Om1_of_sol_SU {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Om1 \ ({2} : Set ℂ)))
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) (Om1 \ ({2} : Set ℂ)))
    {Y : ℂ → Fin k → ℂ} (hYd : DifferentiableOn ℂ Y (SU \ ({2} : Set ℂ)))
    (hY : ∀ z ∈ SU \ ({2} : Set ℂ),
      HasDerivAt Y (fun i => Finset.univ.sum (fun j => A z i j * Y z j) + b z i) z) :
    ∃ G : ℂ → Fin k → ℂ, DifferentiableOn ℂ G (Om1 \ ({2} : Set ℂ)) ∧
      (∀ z ∈ Om1 \ ({2} : Set ℂ),
        HasDerivAt G (fun i => Finset.univ.sum (fun j => A z i j * G z j) + b z i) z) ∧
      Set.EqOn G Y (SU \ ({2} : Set ℂ)) := by
  -- the source `piece ∩ SU` sits inside `SU ∖ {2}`
  have hsrcU : pieceU ∩ SU ⊆ SU \ ({2} : Set ℂ) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    intro h2
    have hz' : 0 < z.im := by simpa only [pieceU, Set.mem_ofPred_eq] using hz.1
    rw [h2] at hz'
    norm_num at hz'
  have hsrcD : pieceD ∩ SU ⊆ SU \ ({2} : Set ℂ) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    intro h2
    have hz' : z.im < 0 := by simpa only [pieceD, Set.mem_ofPred_eq] using hz.1
    rw [h2] at hz'
    norm_num at hz'
  have hsrc1 : piece1 ∩ SU ⊆ SU \ ({2} : Set ℂ) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    intro h2
    have hz' : 1 < z.re ∧ z.re < 2 := by simpa only [piece1, Set.mem_ofPred_eq] using hz.1
    rw [h2] at hz'
    norm_num at hz'
  have hsrc2 : piece2 ∩ SU ⊆ SU \ ({2} : Set ℂ) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    intro h2
    have hz' : 2 < z.re := by simpa only [piece2, Set.mem_ofPred_eq] using hz.1
    rw [h2] at hz'
    norm_num at hz'
  obtain ⟨hptU, hptD, hpt1, hpt2, hqU1, hqD1, hqU2, hqD2⟩ := pieces_seeds
  -- the four local solutions
  obtain ⟨FU, hFUd, hFUode, hFUeq⟩ := asm_sol_extend (convex_pieceU.inter convex_SU)
    (isOpen_pieceU.inter isOpen_SU_H_cont) convex_pieceU isOpen_pieceU Set.inter_subset_left
    (fun i j => (hA i j).mono pieceU_sub) (fun i => (hb i).mono pieceU_sub)
    (hYd.mono hsrcU) (fun z hz => hY z (hsrcU hz)) ⟨hptU.1, hptU.2.1⟩
  obtain ⟨FD, hFDd, hFDode, hFDeq⟩ := asm_sol_extend (convex_pieceD.inter convex_SU)
    (isOpen_pieceD.inter isOpen_SU_H_cont) convex_pieceD isOpen_pieceD Set.inter_subset_left
    (fun i j => (hA i j).mono pieceD_sub) (fun i => (hb i).mono pieceD_sub)
    (hYd.mono hsrcD) (fun z hz => hY z (hsrcD hz)) ⟨hptD.1, hptD.2.1⟩
  obtain ⟨F1, hF1d, hF1ode, hF1eq⟩ := asm_sol_extend (convex_piece1.inter convex_SU)
    (isOpen_piece1.inter isOpen_SU_H_cont) convex_piece1 isOpen_piece1 Set.inter_subset_left
    (fun i j => (hA i j).mono piece1_sub) (fun i => (hb i).mono piece1_sub)
    (hYd.mono hsrc1) (fun z hz => hY z (hsrc1 hz)) ⟨hpt1.1, hpt1.2.1⟩
  obtain ⟨F2, hF2d, hF2ode, hF2eq⟩ := asm_sol_extend (convex_piece2.inter convex_SU)
    (isOpen_piece2.inter isOpen_SU_H_cont) convex_piece2 isOpen_piece2 Set.inter_subset_left
    (fun i j => (hA i j).mono piece2_sub) (fun i => (hb i).mono piece2_sub)
    (hYd.mono hsrc2) (fun z hz => hY z (hsrc2 hz)) ⟨hpt2.1, hpt2.2.1⟩
  -- disjointness
  have hdisjUD : Disjoint pieceU pieceD := by
    rw [Set.disjoint_iff_inter_eq_empty]; exact om1_minus_two_cover.2.1
  -- gluing on the four overlaps
  have glueU1 : Set.EqOn FU F1 (pieceU ∩ piece1) :=
    Work.OdeCont.uniqueness (isOpen_pieceU.inter isOpen_piece1)
      ((convex_pieceU.inter convex_piece1).isPreconnected) A b
      (fun i j => (hA i j).mono (fun z hz => pieceU_sub hz.1))
      (fun i => (hb i).mono (fun z hz => pieceU_sub hz.1))
      FU F1 (hFUd.mono Set.inter_subset_left) (hF1d.mono Set.inter_subset_right)
      (fun z hz => hFUode z hz.1) (fun z hz => hF1ode z hz.2)
      ⟨hqU1.1.1, hqU1.1.2⟩
      (by rw [hFUeq ⟨hqU1.1.1, hqU1.2.1⟩, hF1eq ⟨hqU1.1.2, hqU1.2.1⟩])
  have glueU2 : Set.EqOn FU F2 (pieceU ∩ piece2) :=
    Work.OdeCont.uniqueness (isOpen_pieceU.inter isOpen_piece2)
      ((convex_pieceU.inter convex_piece2).isPreconnected) A b
      (fun i j => (hA i j).mono (fun z hz => pieceU_sub hz.1))
      (fun i => (hb i).mono (fun z hz => pieceU_sub hz.1))
      FU F2 (hFUd.mono Set.inter_subset_left) (hF2d.mono Set.inter_subset_right)
      (fun z hz => hFUode z hz.1) (fun z hz => hF2ode z hz.2)
      ⟨hqU2.1.1, hqU2.1.2⟩
      (by rw [hFUeq ⟨hqU2.1.1, hqU2.2.1⟩, hF2eq ⟨hqU2.1.2, hqU2.2.1⟩])
  have glueD1 : Set.EqOn FD F1 (pieceD ∩ piece1) :=
    Work.OdeCont.uniqueness (isOpen_pieceD.inter isOpen_piece1)
      ((convex_pieceD.inter convex_piece1).isPreconnected) A b
      (fun i j => (hA i j).mono (fun z hz => pieceD_sub hz.1))
      (fun i => (hb i).mono (fun z hz => pieceD_sub hz.1))
      FD F1 (hFDd.mono Set.inter_subset_left) (hF1d.mono Set.inter_subset_right)
      (fun z hz => hFDode z hz.1) (fun z hz => hF1ode z hz.2)
      ⟨hqD1.1.1, hqD1.1.2⟩
      (by rw [hFDeq ⟨hqD1.1.1, hqD1.2.1⟩, hF1eq ⟨hqD1.1.2, hqD1.2.1⟩])
  have glueD2 : Set.EqOn FD F2 (pieceD ∩ piece2) :=
    Work.OdeCont.uniqueness (isOpen_pieceD.inter isOpen_piece2)
      ((convex_pieceD.inter convex_piece2).isPreconnected) A b
      (fun i j => (hA i j).mono (fun z hz => pieceD_sub hz.1))
      (fun i => (hb i).mono (fun z hz => pieceD_sub hz.1))
      FD F2 (hFDd.mono Set.inter_subset_left) (hF2d.mono Set.inter_subset_right)
      (fun z hz => hFDode z hz.1) (fun z hz => hF2ode z hz.2)
      ⟨hqD2.1.1, hqD2.1.2⟩
      (by rw [hFDeq ⟨hqD2.1.1, hqD2.2.1⟩, hF2eq ⟨hqD2.1.2, hqD2.2.1⟩])
  have hdisj12 : Disjoint piece1 piece2 := by
    rw [Set.disjoint_iff_inter_eq_empty]; exact om1_minus_two_cover.2.2
  -- the glued function
  classical
  set G : ℂ → Fin k → ℂ := fun z =>
    if z ∈ pieceU then FU z else if z ∈ pieceD then FD z else if z ∈ piece1 then F1 z else F2 z
    with hG
  have hlocU : ∀ z ∈ pieceU, G =ᶠ[𝓝 z] FU := by
    intro z hz
    filter_upwards [isOpen_pieceU.mem_nhds hz] with w hw
    simp only [hG, if_pos hw]
  have hlocD : ∀ z ∈ pieceD, G =ᶠ[𝓝 z] FD := by
    intro z hz
    filter_upwards [isOpen_pieceD.mem_nhds hz] with w hw
    simp only [hG, if_neg (fun h => Set.disjoint_left.mp hdisjUD h hw), if_pos hw]
  have hloc1 : ∀ z ∈ piece1, z ∉ pieceU → z ∉ pieceD → G =ᶠ[𝓝 z] F1 := by
    intro z hz hzu hzd
    filter_upwards [isOpen_piece1.mem_nhds hz] with w hw
    by_cases hwu : w ∈ pieceU
    · simp only [hG, if_pos hwu]
      exact glueU1 ⟨hwu, hw⟩
    · by_cases hwd : w ∈ pieceD
      · simp only [hG, if_neg hwu, if_pos hwd]
        exact glueD1 ⟨hwd, hw⟩
      · simp only [hG, if_neg hwu, if_neg hwd, if_pos hw]
  have hloc2 : ∀ z ∈ piece2, z ∉ pieceU → z ∉ pieceD → z ∉ piece1 → G =ᶠ[𝓝 z] F2 := by
    intro z hz hzu hzd hz1
    filter_upwards [isOpen_piece2.mem_nhds hz] with w hw
    by_cases hwu : w ∈ pieceU
    · simp only [hG, if_pos hwu]
      exact glueU2 ⟨hwu, hw⟩
    · by_cases hwd : w ∈ pieceD
      · simp only [hG, if_neg hwu, if_pos hwd]
        exact glueD2 ⟨hwd, hw⟩
      · by_cases hw1 : w ∈ piece1
        · exact absurd hw (Set.disjoint_left.mp hdisj12 hw1)
        · simp only [hG, if_neg hwu, if_neg hwd, if_neg hw1]
  -- `z ∈ piece2` from the cover and the other three negations
  have hmem2 : ∀ z ∈ Om1 \ ({2} : Set ℂ), z ∉ pieceU → z ∉ pieceD → z ∉ piece1 →
      z ∈ piece2 := by
    intro z hz hzu hzd hz1
    rcases om1_minus_two_cover.1 z hz with h | h | h | h
    · exact absurd h hzu
    · exact absurd h hzd
    · exact absurd h hz1
    · exact h
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzU : z ∈ pieceU
    · exact ((hFUd.differentiableAt (isOpen_pieceU.mem_nhds hzU)).congr_of_eventuallyEq
        (hlocU z hzU)).differentiableWithinAt
    · by_cases hzD : z ∈ pieceD
      · exact ((hFDd.differentiableAt (isOpen_pieceD.mem_nhds hzD)).congr_of_eventuallyEq
          (hlocD z hzD)).differentiableWithinAt
      · by_cases hz1 : z ∈ piece1
        · exact ((hF1d.differentiableAt (isOpen_piece1.mem_nhds hz1)).congr_of_eventuallyEq
            (hloc1 z hz1 hzU hzD)).differentiableWithinAt
        · exact ((hF2d.differentiableAt
            (isOpen_piece2.mem_nhds (hmem2 z hz hzU hzD hz1))).congr_of_eventuallyEq
            (hloc2 z (hmem2 z hz hzU hzD hz1) hzU hzD hz1)).differentiableWithinAt
  · intro z hz
    by_cases hzU : z ∈ pieceU
    · have hnb := hlocU z hzU
      exact (hFUode z hzU).congr_of_eventuallyEq hnb |>.congr_deriv
        (by funext i; rw [hnb.eq_of_nhds])
    · by_cases hzD : z ∈ pieceD
      · have hnb := hlocD z hzD
        exact (hFDode z hzD).congr_of_eventuallyEq hnb |>.congr_deriv
          (by funext i; rw [hnb.eq_of_nhds])
      · by_cases hz1 : z ∈ piece1
        · have hnb := hloc1 z hz1 hzU hzD
          exact (hF1ode z hz1).congr_of_eventuallyEq hnb |>.congr_deriv
            (by funext i; simp only [hnb.eq_of_nhds])
        · have hz2 := hmem2 z hz hzU hzD hz1
          have hnb := hloc2 z hz2 hzU hzD hz1
          exact (hF2ode z hz2).congr_of_eventuallyEq hnb |>.congr_deriv
            (by funext i; simp only [hnb.eq_of_nhds])
  · intro z hz
    obtain ⟨hzSU, hz2⟩ := hz
    by_cases hzU : z ∈ pieceU
    · rw [show G z = FU z from (hlocU z hzU).eq_of_nhds]
      exact hFUeq ⟨hzU, hzSU⟩
    · by_cases hzD : z ∈ pieceD
      · rw [show G z = FD z from (hlocD z hzD).eq_of_nhds]
        exact hFDeq ⟨hzD, hzSU⟩
      · by_cases hz1 : z ∈ piece1
        · rw [show G z = F1 z from (hloc1 z hz1 hzU hzD).eq_of_nhds]
          exact hF1eq ⟨hz1, hzSU⟩
        · have hzmem : z ∈ piece2 :=
            hmem2 z ⟨SU_subset_Om1 hzSU, hz2⟩ hzU hzD hz1
          rw [show G z = F2 z from (hloc2 z hzmem hzU hzD hz1).eq_of_nhds]
          exact hF2eq ⟨hzmem, hzSU⟩


end

end Work.A14D
