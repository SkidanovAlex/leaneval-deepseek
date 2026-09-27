import Mathlib
import Submission.Work.Drive.ManifoldParity.FlowSetupChart
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.even_ncard_of_involution

/-!
# The mod-2 pairing of the boundary points of a tangentially flowed set

`Work.Drive.pairPtLine S b`: the other endpoint of the in-box arc of the flow line of `b ∈ K`
through `b`.  Under the crossing hypothesis at every boundary point of `K` (a face `i` on which the
`i`-th component of the field does not vanish), `pairPtLine S` is a fixed-point-free involution of
`K ∩ ∂[0,1]^{m+1}`, so the number of boundary points is even: `even_ncard_boundary`.

This is the abstract form of `Work.Drive.boxParity` (`Submission.Drive.ParityProp`) with the global
cutting function `F` replaced by a tangential flow, which is what the manifold statement
`Work.Drive.ManifoldParity.even_ncard_bInterSet_of_tangential_field` needs.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {m : ℕ}

/-- The candidate partner of a boundary point `b ∈ K`: the point of `K` at the other end of the
in-box arc of the flow line through `b`. -/
noncomputable def pairPtLine (S : FlowSetup m) (b : Amb m) : Amb m :=
  S.line b (arcEnd (S.line b))

/-- Reversing the flow reflects the set of right in-box times into the set of left in-box times. -/
theorem rightBoxTimes_neg_line (S : FlowSetup m) (b : Amb m) :
    rightBoxTimes (fun t => S.line b (-t)) = {t | -t ∈ leftBoxTimes (S.line b)} := by
  ext t
  constructor
  · intro h s hs
    have hs' : -s ∈ Set.Ioo (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa using h (-s) hs'
  · intro h s hs
    have hs' : -s ∈ Set.Ioo (-t) (0 : ℝ) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa using h (-s) hs'

/-- Reversing the flow reflects the set of left in-box times into the set of right in-box times. -/
theorem leftBoxTimes_neg_line (S : FlowSetup m) (b : Amb m) :
    leftBoxTimes (fun t => S.line b (-t)) = {t | -t ∈ rightBoxTimes (S.line b)} := by
  ext t
  constructor
  · intro h s hs
    have hs' : -s ∈ Set.Ioo t (0 : ℝ) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa using h (-s) hs'
  · intro h s hs
    have hs' : -s ∈ Set.Ioo (0 : ℝ) (-t) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simpa using h (-s) hs'

/-- The endpoints of the in-box arc are the same for the flow and its reverse. -/
theorem arcEnd_neg_line (S : FlowSetup m) (b : Amb m) :
    arcEnd (fun t => S.line b (-t)) = -arcEnd (S.line b) := by
  have h1 : rightBoxTimes (fun t => S.line b (-t)) = -leftBoxTimes (S.line b) := by
    rw [rightBoxTimes_neg_line]
    ext t
    simp [Set.mem_neg]
  have h2 : leftBoxTimes (fun t => S.line b (-t)) = -rightBoxTimes (S.line b) := by
    rw [leftBoxTimes_neg_line]
    ext t
    simp [Set.mem_neg]
  rw [arcEnd, h1, h2, Real.sSup_neg, Real.sInf_neg, arcEnd]
  ring

/-- The pairing map is the same for a flow and its reverse. -/
theorem pairPtLine_reverse (S : FlowSetup m) : pairPtLine S.reverse = pairPtLine S := by
  funext b
  have hline : S.reverse.line b = fun t => S.line b (-t) := rfl
  rw [pairPtLine, pairPtLine, hline, arcEnd_neg_line]
  show S.line b (-(-arcEnd (S.line b))) = S.line b (arcEnd (S.line b))
  rw [neg_neg]

/-- **The pairing, in the case that the flow line through `b` enters the box for positive times.**
If `(0,ε)` is inside the box and `(-ε,0)` is outside it, then `pairPtLine S b` is again a boundary
point of `K`, differs from `b`, and `pairPtLine S` is an involution at `b`. -/
theorem pairPtLine_spec_right (S : FlowSetup m) (Cov : FlowCover S)
    (hface : ∀ b ∈ S.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.W b i ≠ 0)
    {b : Amb m} (hbK : b ∈ S.K) (hbB : b ∈ Submission.Drive.unitBoxBdry m)
    {ε : ℝ} (hε : 0 < ε)
    (hR : (∀ t ∈ Set.Ioo (0 : ℝ) ε, S.line b t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (-ε) 0, S.line b t ∉ Submission.Drive.unitBox m)) :
    pairPtLine S b ∈ S.K ∧ pairPtLine S b ∈ Submission.Drive.unitBoxBdry m ∧
      pairPtLine S b ≠ b ∧ pairPtLine S (pairPtLine S b) = b := by
  obtain ⟨M, hM⟩ := arc_bound_pos S Cov hbK hbB
  have hcont : Continuous (S.line b) := S.line_continuous b
  -- ### the arc end
  set β : ℝ := sSup (rightBoxTimes (S.line b)) with hβdef
  have hεmem : ε ∈ rightBoxTimes (S.line b) := hR.1
  have hneR : (rightBoxTimes (S.line b)).Nonempty := ⟨ε, hεmem⟩
  have hbdd : BddAbove (rightBoxTimes (S.line b)) := ⟨M, fun t ht => hM t ht⟩
  have hβge : ε ≤ β := hβdef ▸ le_csSup hbdd hεmem
  have hβpos : 0 < β := lt_of_lt_of_le hε hβge
  have hmem : ∀ t ∈ Ioo (0 : ℝ) β, S.line b t ∈ interior (Submission.Drive.unitBox m) := by
    intro t ht
    obtain ⟨t', ht', hlt⟩ := (lt_csSup_iff hbdd hneR).mp (hβdef ▸ ht.2)
    exact ht' t ⟨ht.1, hlt⟩
  have hnotin : S.line b β ∉ interior (Submission.Drive.unitBox m) := by
    intro hcon
    have hev : (S.line b) ⁻¹' (interior (Submission.Drive.unitBox m)) ∈ 𝓝 β :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hcon)
    obtain ⟨r, hr, hr'⟩ := (nhds_basis_Ioo_pos β).mem_iff.mp hev
    have hr0 : (0 : ℝ) < r := hr
    have hmemβ : β + r / 2 ∈ rightBoxTimes (S.line b) := by
      intro s hs
      rcases lt_or_ge s β with hslt | hsge
      · exact hmem s ⟨hs.1, hslt⟩
      · have hs1 : β - r < s := by linarith [hsge, hr0]
        have hs2 : s < β + r := by linarith [hs.2, hr0]
        exact hr' ⟨hs1, hs2⟩
    have hle := le_csSup hbdd hmemβ
    linarith
  have hboxβ : S.line b β ∈ Submission.Drive.unitBox m := by
    have hsub : S.line b '' Ioo (0 : ℝ) β ⊆ Submission.Drive.unitBox m := by
      rintro x ⟨t, ht, rfl⟩
      exact interior_subset (hmem t ht)
    have hcl : S.line b β ∈ closure (S.line b '' Ioo (0 : ℝ) β) := by
      have h1 : (β : ℝ) ∈ closure (Ioo (0 : ℝ) β) := by
        rw [closure_Ioo (show (0 : ℝ) ≠ β from hβpos.ne'.symm)]
        exact ⟨le_of_lt hβpos, le_rfl⟩
      exact image_closure_subset_closure_image hcont (s := Ioo (0 : ℝ) β) ⟨β, h1, rfl⟩
    exact (isClosed_unitBox m).closure_subset (closure_mono hsub hcl)
  have hleft : leftBoxTimes (S.line b) = Set.Ici 0 := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Ici]
      by_contra hlt
      rw [not_le] at hlt
      have hs : ∃ s ∈ Ioo t (0 : ℝ), s ∈ Ioo (-ε) 0 := by
        rcases le_or_gt (-ε) t with h | h
        · exact ⟨t / 2, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · exact ⟨-ε / 2, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      obtain ⟨s, hs1, hs2⟩ := hs
      exact (hR.2 s hs2) (interior_subset (ht s hs1))
    · intro ht
      rw [Set.mem_Ici] at ht
      intro s hs
      exact absurd (lt_trans hs.1 hs.2) (not_lt.mpr ht)
  have harcEnd : arcEnd (S.line b) = β := by
    rw [arcEnd, ← hβdef, hleft, csInf_Ici, add_zero]
  have hpair : pairPtLine S b = S.line b β := by
    show S.line b (arcEnd (S.line b)) = S.line b β
    rw [harcEnd]
  have hK' : pairPtLine S b ∈ S.K := by
    rw [hpair]
    refine S.mapsTo b hbK β ?_
    intro u hu
    have hu' : 0 ≤ u ∧ u ≤ β := by
      rcases Set.mem_uIcc.mp hu with h | h
      · exact ⟨by linarith [h.1, h.2, hβpos], by linarith [h.1, h.2, hβpos]⟩
      · exact ⟨by linarith [h.1, h.2, hβpos], by linarith [h.1, h.2, hβpos]⟩
    rcases lt_or_eq_of_le hu'.1 with h | h
    · rcases lt_or_eq_of_le hu'.2 with h2 | h2
      · exact interior_subset (hmem u ⟨h, h2⟩)
      · subst h2; exact hboxβ
    · subst h; rw [S.zero b]; exact hbB.1
  have hbdry' : pairPtLine S b ∈ Submission.Drive.unitBoxBdry m := by
    rw [hpair]
    exact ⟨hboxβ, exists_coord_eq_zero_or_one_of_not_mem_interior hboxβ hnotin⟩
  -- ### no fixed point
  have hne_b : pairPtLine S b ≠ b := by
    intro heq
    have hvaleq : S.line b (arcEnd (S.line b)) = S.line b 0 := by
      rw [harcEnd, ← hpair, heq, S.line_zero]
    have hper : Function.Periodic (S.line b) β := by
      have h := S.line_periodic_of_eq (s := arcEnd (S.line b)) (t := 0) hvaleq
      rwa [sub_zero, harcEnd] at h
    have h1 : S.line b (-(ε / 2) + β) ∈ interior (Submission.Drive.unitBox m) :=
      hmem _ ⟨by linarith, by linarith⟩
    have h2 : S.line b (-(ε / 2)) ∉ Submission.Drive.unitBox m :=
      hR.2 _ ⟨by linarith, by linarith⟩
    rw [hper (-(ε / 2))] at h1
    exact h2 (interior_subset h1)
  refine ⟨hK', hbdry', hne_b, ?_⟩
  -- ### involution
  have hshift : S.line (pairPtLine S b) = fun t => S.line b (t + β) := by
    have h := S.line_shift b (arcEnd (S.line b))
    rw [harcEnd] at h
    rw [hpair]
    exact h
  have hshift' : ∀ t, S.line (S.line b β) t = S.line b (t + β) := by
    intro t
    have h1 := congrFun hshift t
    rwa [hpair] at h1
  -- the crossing at the other endpoint
  obtain ⟨i', hb'i', hb'other, hb'ne⟩ := hface _ ⟨hK', hbdry'⟩
  rw [hpair] at hb'i' hb'other hb'ne
  obtain ⟨ε₂, hε₂, hcase₂⟩ := crossing_of_deriv_ne_zero_gen
    (S.line_deriv (S.line b β) 0) (S.line_continuous (S.line b β)) (S.line_zero (S.line b β))
    i' ⟨hb'i', hb'other⟩ (by simpa [S.line_zero (S.line b β)] using hb'ne)
  have hleftcase : (∀ t ∈ Ioo (-ε₂) 0,
        S.line (S.line b β) t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Ioo (0 : ℝ) ε₂, S.line (S.line b β) t ∉ Submission.Drive.unitBox m) := by
    rcases hcase₂ with ⟨a1, a2⟩ | h
    · exfalso
      have hmin : 0 < min ε₂ β := lt_min hε₂ hβpos
      set s : ℝ := -(min ε₂ β) / 2 with hs
      have hs1 : s ∈ Ioo (-ε₂) 0 :=
        ⟨by rw [hs]; linarith [min_le_left ε₂ β], by rw [hs]; linarith [hmin]⟩
      have hs2 : s + β ∈ Ioo (0 : ℝ) β :=
        ⟨by rw [hs]; linarith [min_le_right ε₂ β], by rw [hs]; linarith [hmin]⟩
      have h3 : S.line (S.line b β) s ∈ interior (Submission.Drive.unitBox m) := by
        rw [hshift' s]; exact hmem _ hs2
      exact (a2 s hs1) (interior_subset h3)
    · exact h
  have hright' : rightBoxTimes (fun t => S.line b (t + β)) = Set.Iic 0 := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Iic]
      by_contra hlt
      rw [not_le] at hlt
      have hs : min t ε₂ / 2 ∈ Ioo (0 : ℝ) t :=
        ⟨by linarith [lt_min hlt hε₂], by linarith [min_le_left t ε₂]⟩
      have hlt2 : min t ε₂ / 2 < ε₂ := by linarith [min_le_right t ε₂]
      have h4 : S.line (S.line b β) (min t ε₂ / 2) ∉ Submission.Drive.unitBox m :=
        hleftcase.2 _ ⟨by linarith [lt_min hlt hε₂], hlt2⟩
      rw [hshift'] at h4
      exact h4 (interior_subset (ht _ hs))
    · intro ht
      rw [Set.mem_Iic] at ht
      intro s hs
      exact absurd (lt_trans hs.1 hs.2) (not_lt.mpr ht)
  have hleft' : leftBoxTimes (fun t => S.line b (t + β)) = Set.Ici (-β) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Ici]
      by_contra hlt
      rw [not_le] at hlt
      have h5 : (-β) ∈ Ioo t 0 := ⟨by linarith, by linarith⟩
      have h6 : S.line b ((-β) + β) ∈ interior (Submission.Drive.unitBox m) := ht _ h5
      rw [show (-β) + β = 0 by ring, S.line_zero] at h6
      exact not_mem_interior_unitBox_of_mem_unitBoxBdry hbB h6
    · intro ht
      rw [Set.mem_Ici] at ht
      intro s hs
      have hs' : s + β ∈ Ioo (0 : ℝ) β := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      show S.line b (s + β) ∈ interior (Submission.Drive.unitBox m)
      exact hmem (s + β) hs'
  have harcEnd' : arcEnd (S.line (pairPtLine S b)) = -β := by
    rw [hshift, arcEnd, hright', hleft']
    simp [csSup_Iic, csInf_Ici]
  show pairPtLine S (pairPtLine S b) = b
  rw [pairPtLine, harcEnd', hshift]
  show S.line b ((-β) + β) = b
  rw [show (-β) + β = 0 by ring, S.line_zero]

/-- The reversed setup inherits the crossing hypothesis, since the velocity bound is sign-insensitive
and the boxes are the same. -/
theorem face_reverse (S : FlowSetup m)
    (hface : ∀ b ∈ S.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.W b i ≠ 0) :
    ∀ b ∈ S.reverse.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.reverse.W b i ≠ 0 := by
  intro b hb
  obtain ⟨i, hi⟩ := hface b hb
  exact ⟨i, hi.1, hi.2.1, by simpa using hi.2.2⟩

/-- **The pairing, in the case that the flow line through `b` enters the box for negative times.**
Obtained from the positive case by reversing the flow. -/
theorem pairPtLine_spec_left (S : FlowSetup m) (Cov : FlowCover S)
    (hface : ∀ b ∈ S.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.W b i ≠ 0)
    {b : Amb m} (hbK : b ∈ S.K) (hbB : b ∈ Submission.Drive.unitBoxBdry m)
    {ε : ℝ} (hε : 0 < ε)
    (hL : (∀ t ∈ Set.Ioo (-ε) 0, S.line b t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) ε, S.line b t ∉ Submission.Drive.unitBox m)) :
    pairPtLine S b ∈ S.K ∧ pairPtLine S b ∈ Submission.Drive.unitBoxBdry m ∧
      pairPtLine S b ≠ b ∧ pairPtLine S (pairPtLine S b) = b := by
  have hR' : (∀ t ∈ Set.Ioo (0 : ℝ) ε,
        S.reverse.line b t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (-ε) 0, S.reverse.line b t ∉ Submission.Drive.unitBox m) := by
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hL.1 (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro t ht
      exact hL.2 (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hres := pairPtLine_spec_right S.reverse Cov.reverse (face_reverse S hface) hbK hbB hε hR'
  rw [pairPtLine_reverse] at hres
  exact hres

/-- **The pairing at a boundary point.**  Either the flow line enters the box for positive times or
for negative times; in both cases `pairPtLine S` maps `b` to another boundary point of `K`,
different from `b`, and the map is an involution there. -/
theorem pairPtLine_spec (S : FlowSetup m) (Cov : FlowCover S)
    (hface : ∀ b ∈ S.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.W b i ≠ 0)
    {b : Amb m} (hb : b ∈ S.K ∩ Submission.Drive.unitBoxBdry m) :
    pairPtLine S b ∈ S.K ∧ pairPtLine S b ∈ Submission.Drive.unitBoxBdry m ∧
      pairPtLine S b ≠ b ∧ pairPtLine S (pairPtLine S b) = b := by
  obtain ⟨i, hi01, hiint, hne⟩ := hface b hb
  have hne' : S.W (S.line b 0) i ≠ 0 := by simpa [S.line_zero b] using hne
  obtain ⟨ε, hε, hcase⟩ := crossing_of_deriv_ne_zero_gen (S.line_deriv b 0)
    (S.line_continuous b) (S.line_zero b) i ⟨hi01, hiint⟩ hne'
  rcases hcase with hR | hL
  · exact pairPtLine_spec_right S Cov hface hb.1 hb.2 hε hR
  · exact pairPtLine_spec_left S Cov hface hb.1 hb.2 hε hL

/-- **The number of boundary points of a tangentially flowed set is even.**  If every boundary point
of `K` lies on exactly one face of the box, transversally to the flow, then `K ∩ ∂[0,1]^{m+1}` has
an even number of points. -/
theorem even_ncard_boundary (S : FlowSetup m) (Cov : FlowCover S)
    (hface : ∀ b ∈ S.K ∩ Submission.Drive.unitBoxBdry m,
      ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
        (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ S.W b i ≠ 0) :
    Even (S.K ∩ Submission.Drive.unitBoxBdry m).ncard := by
  by_cases hfin : (S.K ∩ Submission.Drive.unitBoxBdry m).Finite
  · refine even_ncard_of_involution hfin (pairPtLine S) ?_ ?_ ?_
    · intro b hb
      exact ⟨(pairPtLine_spec S Cov hface hb).1, (pairPtLine_spec S Cov hface hb).2.1⟩
    · intro b hb
      exact (pairPtLine_spec S Cov hface hb).2.2.2
    · intro b hb
      exact (pairPtLine_spec S Cov hface hb).2.2.1
  · have hinf : (S.K ∩ Submission.Drive.unitBoxBdry m).Infinite := hfin
    rw [Set.ncard, hinf.encard_eq, ENat.toNat_top]
    exact ⟨0, by norm_num⟩

end

end Work.Drive
