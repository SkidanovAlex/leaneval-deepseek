import Mathlib
import Submission.Work.HFN.BlLow.WinDefs

/-!
# The `j`-difference is bounded below far from the coincidence locus

For `τ` in the closed box `clBox` and the contour point `i t` in the window
`[11/40, 5/8]`, the only coincidences `j (it) = j τ` are the two orbit points `zpole τ`
and `crossedPt τ` (`Work.Asymptotics.BlLow.coincidence_classification`).  Consequently, if
`i t` stays at distance `≥ η` from *both* orbit points, the `j`-difference
`‖j (it) - j (zpole τ)‖` is bounded below by a positive constant depending only on `η`.

The proof is a compactness argument: the set
`{(w, τ) : w ∈ ctWin, τ ∈ clBox, dist (w, zpole τ) ≥ η, dist (w, crossedPt τ) ≥ η}`
is a closed subset of the compact `ctWin × clBox`, and `(w,τ) ↦ ‖j w - j τ‖` is continuous
and strictly positive there (a zero would be a coincidence, hence `w = zpole τ` or
`w = crossedPt τ`).  Since `tsign` is constant on each of the two halves `Re τ ≥ 3/4` and
`Re τ ≤ -3/4` of `clBox`, the far set splits into two closed pieces on which the orbit points
are given by the continuous expressions `τ ∓ 1` and `±1 ∓ τ⁻¹`.
-/

noncomputable section

open UpperHalfPlane
open Work.Kernels

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

set_option maxHeartbeats 800000

/-! ## A uniform lower bound on a closed off-coincidence set -/

/-- If `S` is a closed subset of a product of two compact subsets of `ℍ` on which the two
coordinates of `j` never agree, then `‖j p.1 - j p.2‖` is bounded below by a positive constant
on `S`. -/
private lemma exists_lower_j_prod {A B : Set ℍ} (hA : IsCompact A) (hB : IsCompact B)
    (S : Set (ℍ × ℍ)) (hS : IsClosed S) (hsubS : S ⊆ A ×ˢ B)
    (hno : ∀ p ∈ S, jInvariantFun p.1 ≠ jInvariantFun p.2) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ ‖jInvariantFun p.1 - jInvariantFun p.2‖ := by
  have hcont : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1 - jInvariantFun p.2) :=
    (Work.Asymptotics.MiddleRange.continuous_jInvariantFun.comp continuous_fst).sub
      (Work.Asymptotics.MiddleRange.continuous_jInvariantFun.comp continuous_snd)
  have hcomp : IsCompact S := (hA.prod hB).of_isClosed_subset hS hsubS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨p, hp, hmin⟩ := hcomp.exists_isMinOn hne hcont.norm.continuousOn
    exact ⟨‖jInvariantFun p.1 - jInvariantFun p.2‖,
      norm_pos_iff.mpr (sub_ne_zero.mpr (hno p hp)), fun q hq => hmin hq⟩

/-! ## The far set -/

/-- The `+`-branch of the far set: `τ` on the bad line `Re τ ≥ 3/4` (so `tsign τ = 1`), the
contour point at distance `≥ η` from both orbit points `τ - 1` and `1 - τ⁻¹`. -/
private def farSetPlus (η : ℝ) : Set (ℍ × ℍ) :=
  {p | p.1 ∈ ctWin ∧ p.2 ∈ clBox ∧ (3 / 4 : ℝ) ≤ p.2.re ∧
    η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) - 1)‖ ∧ η ≤ ‖(p.1 : ℂ) - (1 - ((p.2 : ℂ))⁻¹)‖}

/-- The `-`-branch of the far set: `τ` on the bad line `Re τ ≤ -3/4` (so `tsign τ = -1`), the
contour point at distance `≥ η` from both orbit points `τ + 1` and `-1 - τ⁻¹`. -/
private def farSetMinus (η : ℝ) : Set (ℍ × ℍ) :=
  {p | p.1 ∈ ctWin ∧ p.2 ∈ clBox ∧ p.2.re ≤ -(3 / 4 : ℝ) ∧
    η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) + 1)‖ ∧ η ≤ ‖(p.1 : ℂ) - (-1 - ((p.2 : ℂ))⁻¹)‖}

private def farSet (η : ℝ) : Set (ℍ × ℍ) := farSetPlus η ∪ farSetMinus η

private lemma continuous_coe_fst :
    Continuous (fun p : ℍ × ℍ => ((p.1 : ℍ) : ℂ)) :=
  UpperHalfPlane.continuous_coe.comp continuous_fst

private lemma continuous_coe_snd :
    Continuous (fun p : ℍ × ℍ => ((p.2 : ℍ) : ℂ)) :=
  UpperHalfPlane.continuous_coe.comp continuous_snd

private lemma continuous_coe_snd_inv :
    Continuous (fun p : ℍ × ℍ => (((p.2 : ℍ) : ℂ))⁻¹) := by
  refine continuous_coe_snd.inv₀ (fun p hz => ?_)
  have h : ((p.2 : ℍ) : ℂ).im = 0 := by rw [hz]; simp
  rw [UpperHalfPlane.coe_im] at h
  exact (ne_of_gt p.2.im_pos) h

private lemma isClosed_farSetPlus (η : ℝ) : IsClosed (farSetPlus η) := by
  have h1 : IsClosed {p : ℍ × ℍ | p.1 ∈ ctWin} := isClosed_ctWin.preimage continuous_fst
  have h2 : IsClosed {p : ℍ × ℍ | p.2 ∈ clBox} := isClosed_clBox.preimage continuous_snd
  have h3 : IsClosed {p : ℍ × ℍ | (3 / 4 : ℝ) ≤ p.2.re} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_re.comp continuous_snd)
  have h4 : IsClosed {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) - 1)‖} :=
    isClosed_le continuous_const (continuous_coe_fst.sub (continuous_coe_snd.sub
      continuous_const)).norm
  have h5 : IsClosed {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - (1 - ((p.2 : ℂ))⁻¹)‖} :=
    isClosed_le continuous_const (continuous_coe_fst.sub
      (continuous_const.sub continuous_coe_snd_inv)).norm
  have he : farSetPlus η = {p : ℍ × ℍ | p.1 ∈ ctWin} ∩ {p : ℍ × ℍ | p.2 ∈ clBox} ∩
      {p : ℍ × ℍ | (3 / 4 : ℝ) ≤ p.2.re} ∩
      {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) - 1)‖} ∩
      {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - (1 - ((p.2 : ℂ))⁻¹)‖} := by
    ext p; simp only [farSetPlus, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [he]
  exact (((h1.inter h2).inter h3).inter h4).inter h5

private lemma isClosed_farSetMinus (η : ℝ) : IsClosed (farSetMinus η) := by
  have h1 : IsClosed {p : ℍ × ℍ | p.1 ∈ ctWin} := isClosed_ctWin.preimage continuous_fst
  have h2 : IsClosed {p : ℍ × ℍ | p.2 ∈ clBox} := isClosed_clBox.preimage continuous_snd
  have h3 : IsClosed {p : ℍ × ℍ | p.2.re ≤ -(3 / 4 : ℝ)} :=
    isClosed_le (UpperHalfPlane.continuous_re.comp continuous_snd) continuous_const
  have h4 : IsClosed {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) + 1)‖} :=
    isClosed_le continuous_const (continuous_coe_fst.sub (continuous_coe_snd.add
      continuous_const)).norm
  have h5 : IsClosed {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - (-1 - ((p.2 : ℂ))⁻¹)‖} :=
    isClosed_le continuous_const (continuous_coe_fst.sub
      (continuous_const.sub continuous_coe_snd_inv)).norm
  have he : farSetMinus η = {p : ℍ × ℍ | p.1 ∈ ctWin} ∩ {p : ℍ × ℍ | p.2 ∈ clBox} ∩
      {p : ℍ × ℍ | p.2.re ≤ -(3 / 4 : ℝ)} ∩
      {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - ((p.2 : ℂ) + 1)‖} ∩
      {p : ℍ × ℍ | η ≤ ‖(p.1 : ℂ) - (-1 - ((p.2 : ℂ))⁻¹)‖} := by
    ext p; simp only [farSetMinus, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [he]
  exact (((h1.inter h2).inter h3).inter h4).inter h5

private lemma isClosed_farSet (η : ℝ) : IsClosed (farSet η) :=
  (isClosed_farSetPlus η).union (isClosed_farSetMinus η)

private lemma farSet_subset (η : ℝ) : farSet η ⊆ ctWin ×ˢ clBox := by
  intro p hp
  rcases hp with hp | hp
  · exact Set.mk_mem_prod hp.1 hp.2.1
  · exact Set.mk_mem_prod hp.1 hp.2.1

/-! ## `j` never agrees on the far set -/

private lemma imagAxis_eq_self_of_mem_ctWin {z : ℍ} (hz : z ∈ ctWin) :
    z = imagAxis z.im z.im_pos :=
  Work.Asymptotics.KaxisMid.eq_imagAxis_of_re_eq_zero
    (by rw [UpperHalfPlane.coe_re]; exact hz.1)

private lemma farSetPlus_j_ne {η : ℝ} (hη : 0 < η) {p : ℍ × ℍ} (hp : p ∈ farSetPlus η) :
    jInvariantFun p.1 ≠ jInvariantFun p.2 := by
  intro hjeq
  obtain ⟨hw, hτ, hre, hfar1, hfar2⟩ := hp
  have hw_eq : p.1 = imagAxis p.1.im p.1.im_pos := imagAxis_eq_self_of_mem_ctWin hw
  have hcoin : jInvariantFun p.2 = jInvariantFun (imagAxis p.1.im p.1.im_pos) := by
    rw [← hw_eq]; exact hjeq.symm
  have hts : tsign p.2 = 1 := (tsign_eq_one_iff p.2).mpr (by linarith)
  rcases coincidence_classification hτ p.1.im_pos hw.2.1 hw.2.2 hcoin with h | h
  · have hcoe : ((zpole p.2 : ℍ) : ℂ) = (p.2 : ℂ) - 1 := by
      rw [zpole_coe, hts]; norm_num
    have hp1 : (p.1 : ℂ) = (p.2 : ℂ) - 1 := by rw [hw_eq.trans h, hcoe]
    rw [hp1, sub_self, norm_zero] at hfar1
    linarith
  · have hcoe : ((crossedPt p.2 : ℍ) : ℂ) = 1 - ((p.2 : ℂ))⁻¹ := by
      rw [crossedPt_coe, hts]; norm_num
    have hp1 : (p.1 : ℂ) = 1 - ((p.2 : ℂ))⁻¹ := by rw [hw_eq.trans h, hcoe]
    rw [hp1, sub_self, norm_zero] at hfar2
    linarith

private lemma farSetMinus_j_ne {η : ℝ} (hη : 0 < η) {p : ℍ × ℍ} (hp : p ∈ farSetMinus η) :
    jInvariantFun p.1 ≠ jInvariantFun p.2 := by
  intro hjeq
  obtain ⟨hw, hτ, hre, hfar1, hfar2⟩ := hp
  have hw_eq : p.1 = imagAxis p.1.im p.1.im_pos := imagAxis_eq_self_of_mem_ctWin hw
  have hcoin : jInvariantFun p.2 = jInvariantFun (imagAxis p.1.im p.1.im_pos) := by
    rw [← hw_eq]; exact hjeq.symm
  have hts : tsign p.2 = -1 := (tsign_eq_neg_one_iff p.2).mpr (by linarith)
  rcases coincidence_classification hτ p.1.im_pos hw.2.1 hw.2.2 hcoin with h | h
  · have hcoe : ((zpole p.2 : ℍ) : ℂ) = (p.2 : ℂ) + 1 := by
      rw [zpole_coe, hts]; norm_num
    have hp1 : (p.1 : ℂ) = (p.2 : ℂ) + 1 := by rw [hw_eq.trans h, hcoe]
    rw [hp1, sub_self, norm_zero] at hfar1
    linarith
  · have hcoe : ((crossedPt p.2 : ℍ) : ℂ) = -1 - ((p.2 : ℂ))⁻¹ := by
      rw [crossedPt_coe, hts]; norm_num
    have hp1 : (p.1 : ℂ) = -1 - ((p.2 : ℂ))⁻¹ := by rw [hw_eq.trans h, hcoe]
    rw [hp1, sub_self, norm_zero] at hfar2
    linarith

private lemma farSet_j_ne (η : ℝ) (hη : 0 < η) {p : ℍ × ℍ} (hp : p ∈ farSet η) :
    jInvariantFun p.1 ≠ jInvariantFun p.2 := by
  rcases hp with hp | hp
  · exact farSetPlus_j_ne hη hp
  · exact farSetMinus_j_ne hη hp

/-! ## The main statement -/

theorem blWinBox_far_lower (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      τ ∈ Work.HFN.BlLow.clBox → (11 : ℝ) / 40 ≤ t → t ≤ 5 / 8 →
      η ≤ ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) - ((Work.Asymptotics.HalfFunnel.zpole τ : UpperHalfPlane) : ℂ)‖ →
      η ≤ ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) - ((Work.HFN.BlLow.crossedPt τ : UpperHalfPlane) : ℂ)‖ →
      δ ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)‖ := by
  obtain ⟨c, hcpos, hc⟩ := exists_lower_j_prod isCompact_ctWin isCompact_clBox (farSet η)
    (isClosed_farSet η) (farSet_subset η) (fun p hp => farSet_j_ne η hη hp)
  refine ⟨c, hcpos, ?_⟩
  intro τ t ht hτ h1 h2 hfar1 hfar2
  have hw_ct : imagAxis t ht ∈ ctWin := imagAxis_mem_ctWin t ht h1 h2
  have hp : (imagAxis t ht, τ) ∈ farSet η := by
    rcases le_abs.mp hτ.1 with hpos | hneg
    · left
      have hts : tsign τ = 1 := (tsign_eq_one_iff τ).mpr (by linarith)
      have hz : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - 1 := by rw [zpole_coe, hts]; norm_num
      have hc : ((crossedPt τ : ℍ) : ℂ) = 1 - ((τ : ℂ))⁻¹ := by
        rw [crossedPt_coe, hts]; norm_num
      exact ⟨hw_ct, hτ, hpos, by rw [hz] at hfar1; exact hfar1,
        by rw [hc] at hfar2; exact hfar2⟩
    · right
      have hts : tsign τ = -1 := (tsign_eq_neg_one_iff τ).mpr (by linarith)
      have hz : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by rw [zpole_coe, hts]; norm_num
      have hc : ((crossedPt τ : ℍ) : ℂ) = -1 - ((τ : ℂ))⁻¹ := by
        rw [crossedPt_coe, hts]; norm_num
      exact ⟨hw_ct, hτ, by linarith, by rw [hz] at hfar1; exact hfar1,
        by rw [hc] at hfar2; exact hfar2⟩
  have h := hc (imagAxis t ht, τ) hp
  rw [zpole_jInvariantFun τ]
  exact h

end Work.HFN.BlLow
