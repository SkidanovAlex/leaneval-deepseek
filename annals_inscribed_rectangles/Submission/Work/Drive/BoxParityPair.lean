import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.in_box_arc_right
import Submission.Work.Drive.in_box_arc_left
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.graph_region_props

/-!
# The mod-2 pairing of the boundary zeros

For a boundary zero `b` of the box on which `F` vanishes transversally, the in-box arc of the flow
line through `b` has a second endpoint, again a boundary zero (`pairPt F hF b`); the resulting map
`pairPt` is a fixed-point-free involution of the boundary zeros.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

open Submission.Drive

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **The pairing, in the case that the flow line through `b` enters the box for positive times.**
If `(0,ε)` is inside the box and `(-ε,0)` is outside it, then `pairPt F hF b` is a boundary zero,
differs from `b`, and is an involution. -/
theorem pairPt_spec_right {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hbdy : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1))
    {b : Amb m} (hb : b ∈ bdyZeros F)
    {ε : ℝ} (hε : 0 < ε)
    (hR : (∀ t ∈ Set.Ioo (0 : ℝ) ε, flowCurve F hF b t ∈ interior (unitBox m)) ∧
      (∀ t ∈ Set.Ioo (-ε) 0, flowCurve F hF b t ∉ unitBox m)) :
    pairPt F hF b ∈ bdyZeros F ∧ pairPt F hF b ≠ b ∧
      pairPt F hF (pairPt F hF b) = b := by
  obtain ⟨i, hbi, hbother, hsurj⟩ := hbdy b hb.1 hb.2
  have hne : flowField F b i ≠ 0 := flowField_apply_ne_zero_of_bdy hb.1.1 hsurj
  obtain ⟨M, hM⟩ := in_box_arc_right hF hreg hb ⟨i, hbi, hbother, hne⟩ hε hR.1
  have hcont : Continuous (flowCurve F hF b) :=
    continuous_iff_continuousAt.mpr fun t => (flowCurve_hasDerivAt F hF b t).continuousAt
  -- ### the arc end
  set β : ℝ := sSup (rightBoxTimes (flowCurve F hF b)) with hβdef
  have hεmem : ε ∈ rightBoxTimes (flowCurve F hF b) := hR.1
  have hneR : (rightBoxTimes (flowCurve F hF b)).Nonempty := ⟨ε, hεmem⟩
  have hbdd : BddAbove (rightBoxTimes (flowCurve F hF b)) := ⟨M, fun t ht => hM t ht⟩
  have hβge : ε ≤ β := hβdef ▸ le_csSup hbdd hεmem
  have hβpos : 0 < β := lt_of_lt_of_le hε hβge
  have hmem : ∀ t ∈ Ioo (0 : ℝ) β, flowCurve F hF b t ∈ interior (unitBox m) := by
    intro t ht
    obtain ⟨t', ht', hlt⟩ := (lt_csSup_iff hbdd hneR).mp (hβdef ▸ ht.2)
    exact ht' t ⟨ht.1, hlt⟩
  have hnotin : flowCurve F hF b β ∉ interior (unitBox m) := by
    intro hcon
    have hev : (flowCurve F hF b) ⁻¹' (interior (unitBox m)) ∈ 𝓝 β :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hcon)
    obtain ⟨r, hr, hr'⟩ := (nhds_basis_Ioo_pos β).mem_iff.mp hev
    have hr0 : (0 : ℝ) < r := hr
    have hmemβ : β + r / 2 ∈ rightBoxTimes (flowCurve F hF b) := by
      intro s hs
      rcases lt_or_ge s β with hslt | hsge
      · exact hmem s ⟨hs.1, hslt⟩
      · have hs1 : β - r < s := by linarith [hsge, hr0]
        have hs2 : s < β + r := by linarith [hs.2, hr0]
        exact hr' ⟨hs1, hs2⟩
    have hle := le_csSup hbdd hmemβ
    linarith
  have hboxβ : flowCurve F hF b β ∈ unitBox m := by
    have hsub : flowCurve F hF b '' Ioo (0 : ℝ) β ⊆ unitBox m := by
      rintro x ⟨t, ht, rfl⟩
      exact interior_subset (hmem t ht)
    have hcl : flowCurve F hF b β ∈ closure (flowCurve F hF b '' Ioo (0 : ℝ) β) := by
      have h1 : (β : ℝ) ∈ closure (Ioo (0 : ℝ) β) := by
        rw [closure_Ioo (show (0 : ℝ) ≠ β from hβpos.ne'.symm)]
        exact ⟨le_of_lt hβpos, le_rfl⟩
      exact image_closure_subset_closure_image hcont (s := Ioo (0 : ℝ) β) ⟨β, h1, rfl⟩
    exact (isClosed_unitBox m).closure_subset (closure_mono hsub hcl)
  have hleft : leftBoxTimes (flowCurve F hF b) = Set.Ici 0 := by
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
  have harcEnd : arcEnd (flowCurve F hF b) = β := by
    rw [arcEnd, ← hβdef, hleft, csInf_Ici, add_zero]
  have hpair : pairPt F hF b = flowCurve F hF b β := by
    show flowCurve F hF b (arcEnd (flowCurve F hF b)) = flowCurve F hF b β
    rw [harcEnd]
  have hbdy' : pairPt F hF b ∈ bdyZeros F := by
    rw [hpair]
    exact mem_bdyZeros_of_mem_unitBox_not_mem_interior hboxβ hnotin
      (by rw [F_flowCurve hF b β]; exact hb.2)
  -- ### no fixed point
  have hne_b : pairPt F hF b ≠ b := by
    intro heq
    have hvaleq : flowCurve F hF b (arcEnd (flowCurve F hF b)) = flowCurve F hF b 0 := by
      rw [harcEnd, ← hpair, heq, flowCurve_zero]
    have hper : Function.Periodic (flowCurve F hF b) β := by
      have h := flowCurve_periodic_of_eq hF (s := arcEnd (flowCurve F hF b)) (t := 0) hvaleq
      rwa [sub_zero, harcEnd] at h
    have h1 : flowCurve F hF b (-(ε / 2) + β) ∈ interior (unitBox m) :=
      hmem _ ⟨by linarith, by linarith⟩
    have h2 : flowCurve F hF b (-(ε / 2)) ∉ unitBox m :=
      hR.2 _ ⟨by linarith, by linarith⟩
    rw [hper (-(ε / 2))] at h1
    exact h2 (interior_subset h1)
  refine ⟨hbdy', hne_b, ?_⟩
  -- ### involution
  have hshift : flowCurve F hF (pairPt F hF b) = fun t => flowCurve F hF b (t + β) := by
    have h := flowCurve_shift (F := F) (hF := hF) (x := b) (t₀ := arcEnd (flowCurve F hF b))
    rw [harcEnd] at h
    rw [hpair]
    exact h
  have hshift' : ∀ t, flowCurve F hF (flowCurve F hF b β) t = flowCurve F hF b (t + β) := by
    intro t
    have h1 := congrFun hshift t
    rwa [hpair] at h1
  -- the one-sidedness at the other endpoint
  have hb' : flowCurve F hF b β ∈ bdyZeros F := by rw [← hpair]; exact hbdy'
  have hne_self : pairPt F hF b ≠ b := hne_b
  obtain ⟨i', hb'i', hb'other, hb'surj⟩ := hbdy _ hb'.1 hb'.2
  have hne' : flowField F (flowCurve F hF b β) i' ≠ 0 :=
    flowField_apply_ne_zero_of_bdy hb'.1.1 hb'surj
  obtain ⟨ε₂, hε₂, hcase₂⟩ := crossing_of_deriv_ne_zero
    (flowCurve_hasDerivAt F hF (flowCurve F hF b β)) (flowCurve_zero F hF (flowCurve F hF b β))
    i' ⟨hb'i', hb'other⟩ hne'
  have hleftcase : (∀ t ∈ Ioo (-ε₂) 0,
        flowCurve F hF (flowCurve F hF b β) t ∈ interior (unitBox m)) ∧
      (∀ t ∈ Ioo (0 : ℝ) ε₂, flowCurve F hF (flowCurve F hF b β) t ∉ unitBox m) := by
    rcases hcase₂ with ⟨a1, a2⟩ | h
    · exfalso
      have hmin : 0 < min ε₂ β := lt_min hε₂ hβpos
      set s : ℝ := -(min ε₂ β) / 2 with hs
      have hs1 : s ∈ Ioo (-ε₂) 0 := ⟨by rw [hs]; linarith [min_le_left ε₂ β], by rw [hs]; linarith [hmin]⟩
      have hs2 : s + β ∈ Ioo (0 : ℝ) β := ⟨by rw [hs]; linarith [min_le_right ε₂ β], by rw [hs]; linarith [hmin]⟩
      have h3 : flowCurve F hF (flowCurve F hF b β) s ∈ interior (unitBox m) := by
        rw [hshift' s]; exact hmem _ hs2
      exact (a2 s hs1) (interior_subset h3)
    · exact h
  have hright' : rightBoxTimes (fun t => flowCurve F hF b (t + β)) = Set.Iic 0 := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Iic]
      by_contra hlt
      rw [not_le] at hlt
      have hs : min t ε₂ / 2 ∈ Ioo (0 : ℝ) t :=
        ⟨by linarith [lt_min hlt hε₂], by linarith [min_le_left t ε₂]⟩
      have hlt2 : min t ε₂ / 2 < ε₂ := by linarith [min_le_right t ε₂]
      have h4 : flowCurve F hF (flowCurve F hF b β) (min t ε₂ / 2) ∉ unitBox m :=
        hleftcase.2 _ ⟨by linarith [lt_min hlt hε₂], hlt2⟩
      rw [hshift'] at h4
      exact h4 (interior_subset (ht _ hs))
    · intro ht
      rw [Set.mem_Iic] at ht
      intro s hs
      exact absurd (lt_trans hs.1 hs.2) (not_lt.mpr ht)
  have hleft' : leftBoxTimes (fun t => flowCurve F hF b (t + β)) = Set.Ici (-β) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Ici]
      by_contra hlt
      rw [not_le] at hlt
      have h5 : (-β) ∈ Ioo t 0 := ⟨by linarith, by linarith⟩
      have h6 : flowCurve F hF b ((-β) + β) ∈ interior (unitBox m) := ht _ h5
      rw [show (-β) + β = 0 by ring, flowCurve_zero] at h6
      exact not_mem_interior_of_mem_bdyZeros hb h6
    · intro ht
      rw [Set.mem_Ici] at ht
      intro s hs
      have hs' : s + β ∈ Ioo (0 : ℝ) β := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      show flowCurve F hF b (s + β) ∈ interior (unitBox m)
      exact hmem (s + β) hs'
  have harcEnd' : arcEnd (flowCurve F hF (pairPt F hF b)) = -β := by
    rw [hshift, arcEnd, hright', hleft']
    simp [csSup_Iic, csInf_Ici]
  show pairPt F hF (pairPt F hF b) = b
  rw [pairPt, harcEnd', hshift]
  show flowCurve F hF b ((-β) + β) = b
  rw [show (-β) + β = 0 by ring, flowCurve_zero]

/-- **The pairing, in the case that the flow line through `b` enters the box for negative times.**
If `(ε,0)` is inside the box and `(0,-ε)` is outside it, then `pairPt F hF b` is a boundary zero,
differs from `b`, and is an involution. -/
theorem pairPt_spec_left {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hbdy : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1))
    {b : Amb m} (hb : b ∈ bdyZeros F)
    {ε : ℝ} (hε : ε < 0)
    (hL : (∀ t ∈ Set.Ioo ε 0, flowCurve F hF b t ∈ interior (unitBox m)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (-ε), flowCurve F hF b t ∉ unitBox m)) :
    pairPt F hF b ∈ bdyZeros F ∧ pairPt F hF b ≠ b ∧
      pairPt F hF (pairPt F hF b) = b := by
  obtain ⟨i, hbi, hbother, hsurj⟩ := hbdy b hb.1 hb.2
  have hne : flowField F b i ≠ 0 := flowField_apply_ne_zero_of_bdy hb.1.1 hsurj
  obtain ⟨M, hM⟩ := in_box_arc_left hF hreg hb ⟨i, hbi, hbother, hne⟩ hε hL.1
  have hcont : Continuous (flowCurve F hF b) :=
    continuous_iff_continuousAt.mpr fun t => (flowCurve_hasDerivAt F hF b t).continuousAt
  -- ### the arc end
  set α : ℝ := sInf (leftBoxTimes (flowCurve F hF b)) with hαdef
  have hεmem : ε ∈ leftBoxTimes (flowCurve F hF b) := hL.1
  have hneL : (leftBoxTimes (flowCurve F hF b)).Nonempty := ⟨ε, hεmem⟩
  have hbdd : BddBelow (leftBoxTimes (flowCurve F hF b)) := ⟨M, fun t ht => hM t ht⟩
  have hαle : α ≤ ε := hαdef ▸ csInf_le hbdd hεmem
  have hαneg : α < 0 := lt_of_le_of_lt hαle hε
  have hmem : ∀ t ∈ Ioo α (0 : ℝ), flowCurve F hF b t ∈ interior (unitBox m) := by
    intro t ht
    obtain ⟨t', ht', hlt⟩ := exists_lt_of_csInf_lt hneL (hαdef ▸ ht.1)
    exact ht' t ⟨hlt, ht.2⟩
  have hnotin : flowCurve F hF b α ∉ interior (unitBox m) := by
    intro hcon
    have hev : (flowCurve F hF b) ⁻¹' (interior (unitBox m)) ∈ 𝓝 α :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hcon)
    obtain ⟨r, hr, hr'⟩ := (nhds_basis_Ioo_pos α).mem_iff.mp hev
    have hr0 : (0 : ℝ) < r := hr
    have hmemα : α - r / 2 ∈ leftBoxTimes (flowCurve F hF b) := by
      intro s hs
      rcases lt_or_ge s α with hslt | hsge
      · have h1 : α - r < s := by linarith [hs.1, hr0]
        exact hr' ⟨h1, by linarith [hslt, hr0]⟩
      · rcases lt_or_eq_of_le hsge with hlt | heq
        · exact hmem s ⟨hlt, hs.2⟩
        · rw [← heq]; exact hcon
    have hle := csInf_le hbdd hmemα
    linarith
  have hboxα : flowCurve F hF b α ∈ unitBox m := by
    have hsub : flowCurve F hF b '' Ioo α (0 : ℝ) ⊆ unitBox m := by
      rintro x ⟨t, ht, rfl⟩
      exact interior_subset (hmem t ht)
    have hcl : flowCurve F hF b α ∈ closure (flowCurve F hF b '' Ioo α (0 : ℝ)) := by
      have h1 : (α : ℝ) ∈ closure (Ioo α (0 : ℝ)) := by
        rw [closure_Ioo (show α ≠ 0 from hαneg.ne)]
        exact ⟨le_rfl, le_of_lt hαneg⟩
      exact image_closure_subset_closure_image hcont (s := Ioo α (0 : ℝ)) ⟨α, h1, rfl⟩
    exact (isClosed_unitBox m).closure_subset (closure_mono hsub hcl)
  have hright : rightBoxTimes (flowCurve F hF b) = Set.Iic 0 := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Iic]
      by_contra hlt
      rw [not_le] at hlt
      have hs : ∃ s ∈ Ioo (0 : ℝ) t, s ∈ Ioo (0 : ℝ) (-ε) := by
        rcases le_or_gt t (-ε) with h | h
        · exact ⟨t / 2, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · exact ⟨-ε / 2, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      obtain ⟨s, hs1, hs2⟩ := hs
      exact (hL.2 s hs2) (interior_subset (ht s hs1))
    · intro ht
      rw [Set.mem_Iic] at ht
      intro s hs
      exact absurd (lt_trans hs.1 hs.2) (not_lt.mpr ht)
  have harcEnd : arcEnd (flowCurve F hF b) = α := by
    rw [arcEnd, hright, csSup_Iic, ← hαdef, zero_add]
  have hpair : pairPt F hF b = flowCurve F hF b α := by
    show flowCurve F hF b (arcEnd (flowCurve F hF b)) = flowCurve F hF b α
    rw [harcEnd]
  have hbdy' : pairPt F hF b ∈ bdyZeros F := by
    rw [hpair]
    exact mem_bdyZeros_of_mem_unitBox_not_mem_interior hboxα hnotin
      (by rw [F_flowCurve hF b α]; exact hb.2)
  -- ### no fixed point
  have hne_b : pairPt F hF b ≠ b := by
    intro heq
    have hvaleq : flowCurve F hF b (arcEnd (flowCurve F hF b)) = flowCurve F hF b 0 := by
      rw [harcEnd, ← hpair, heq, flowCurve_zero]
    have hper : Function.Periodic (flowCurve F hF b) α := by
      have h := flowCurve_periodic_of_eq hF (s := arcEnd (flowCurve F hF b)) (t := 0) hvaleq
      rwa [sub_zero, harcEnd] at h
    have hmin : 0 < min (-α) (-ε) := lt_min (by linarith) (by linarith)
    set s : ℝ := min (-α) (-ε) / 2 with hs
    have hs1 : s ∈ Ioo (0 : ℝ) (-ε) := by
      rw [hs]
      exact ⟨by linarith [hmin], by linarith [min_le_right (-α) (-ε), hαneg]⟩
    have hs2 : s + α ∈ Ioo α 0 := by
      rw [hs]
      exact ⟨by linarith [hmin], by linarith [min_le_left (-α) (-ε), hαneg]⟩
    have h3 : flowCurve F hF b (s + α) ∈ interior (unitBox m) := hmem (s + α) hs2
    rw [hper s] at h3
    exact (hL.2 s hs1) (interior_subset h3)
  refine ⟨hbdy', hne_b, ?_⟩
  -- ### involution
  have hshift : flowCurve F hF (pairPt F hF b) = fun t => flowCurve F hF b (t + α) := by
    have h := flowCurve_shift (F := F) (hF := hF) (x := b) (t₀ := arcEnd (flowCurve F hF b))
    rw [harcEnd] at h
    rw [hpair]
    exact h
  have hshift' : ∀ t, flowCurve F hF (flowCurve F hF b α) t = flowCurve F hF b (t + α) := by
    intro t
    have h1 := congrFun hshift t
    rwa [hpair] at h1
  have hb' : flowCurve F hF b α ∈ bdyZeros F := by rw [← hpair]; exact hbdy'
  obtain ⟨i', hb'i', hb'other, hb'surj⟩ := hbdy _ hb'.1 hb'.2
  have hne' : flowField F (flowCurve F hF b α) i' ≠ 0 :=
    flowField_apply_ne_zero_of_bdy hb'.1.1 hb'surj
  obtain ⟨ε₂, hε₂, hcase₂⟩ := crossing_of_deriv_ne_zero
    (flowCurve_hasDerivAt F hF (flowCurve F hF b α)) (flowCurve_zero F hF (flowCurve F hF b α))
    i' ⟨hb'i', hb'other⟩ hne'
  have hrightcase : (∀ t ∈ Ioo (0 : ℝ) ε₂,
        flowCurve F hF (flowCurve F hF b α) t ∈ interior (unitBox m)) ∧
      (∀ t ∈ Ioo (-ε₂) 0, flowCurve F hF (flowCurve F hF b α) t ∉ unitBox m) := by
    rcases hcase₂ with h | ⟨a1, a2⟩
    · exact h
    · exfalso
      -- the curve is inside the box just to the right of `0`, so the left case is impossible
      have hmin : 0 < min ε₂ (-α) := lt_min hε₂ (by linarith)
      have hmina : 0 < -α := by linarith
      have hle : min ε₂ (-α) ≤ -α := min_le_right ε₂ (-α)
      set s : ℝ := min ε₂ (-α) / 2 with hs
      have hs1 : s ∈ Ioo (0 : ℝ) ε₂ := by
        rw [hs]
        exact ⟨by linarith [hmin], by linarith [min_le_left ε₂ (-α), hmin]⟩
      have hs2 : s + α ∈ Ioo α 0 := by
        rw [hs]
        exact ⟨by linarith [hmin], by linarith [hle, hmin]⟩
      have h3 : flowCurve F hF (flowCurve F hF b α) s ∈ interior (unitBox m) := by
        simpa only [hshift' s] using hmem (s + α) hs2
      exact (a2 s hs1) (interior_subset h3)
  have hright' : rightBoxTimes (fun t => flowCurve F hF b (t + α)) = Set.Iic (-α) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Iic]
      by_contra hlt
      rw [not_le] at hlt
      -- then `-α` lies in the interval `(0,t)` of the shifted curve, but `b` is not interior
      have hu : -α ∈ Ioo (0 : ℝ) t := ⟨by linarith, by linarith⟩
      have h4 : flowCurve F hF b ((-α) + α) ∈ interior (unitBox m) := ht (-α) hu
      rw [show (-α) + α = 0 by ring, flowCurve_zero] at h4
      exact not_mem_interior_of_mem_bdyZeros hb h4
    · intro ht
      rw [Set.mem_Iic] at ht
      intro s hs
      have hs' : s + α ∈ Ioo α 0 := ⟨by linarith [hs.1], by linarith [hs.2, ht]⟩
      show flowCurve F hF b (s + α) ∈ interior (unitBox m)
      exact hmem (s + α) hs'
  have hleft' : leftBoxTimes (fun t => flowCurve F hF b (t + α)) = Set.Ici 0 := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_Ici]
      by_contra hlt
      rw [not_le] at hlt
      have hmin : 0 < min ε₂ (-α) := lt_min hε₂ (by linarith)
      have hmina : 0 < -α := by linarith
      have hc : min ε₂ (-α) ≤ ε₂ := min_le_left ε₂ (-α)
      obtain ⟨s, hs, hs'⟩ : ∃ s, s ∈ Ioo t 0 ∧ s ∈ Ioo (-ε₂) 0 := by
        rcases le_or_gt t (-(min ε₂ (-α)) / 2) with h | h
        · refine ⟨-(min ε₂ (-α)) / 4,
            ⟨by linarith [hmin], by linarith [hmin]⟩, ?_, by linarith [hmin]⟩
          linarith [hc, hmin]
        · refine ⟨t / 2, ⟨by linarith, by linarith [hlt]⟩, ?_, by linarith⟩
          linarith [hc, hmin]
      have h4 : flowCurve F hF (flowCurve F hF b α) s ∉ unitBox m := hrightcase.2 s hs'
      rw [hshift' s] at h4
      exact h4 (interior_subset (ht s hs))
    · intro ht
      rw [Set.mem_Ici] at ht
      intro s hs
      exact absurd hs.1 (not_lt.mpr (le_trans (le_of_lt hs.2) ht))
  have harcEnd' : arcEnd (flowCurve F hF (pairPt F hF b)) = -α := by
    rw [hshift, arcEnd, hright', hleft']
    simp [csSup_Iic, csInf_Ici]
  show pairPt F hF (pairPt F hF b) = b
  rw [pairPt, harcEnd', hshift]
  show flowCurve F hF b ((-α) + α) = b
  rw [show (-α) + α = 0 by ring, flowCurve_zero]

end

end Work.Drive
