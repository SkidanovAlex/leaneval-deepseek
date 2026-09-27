import Mathlib
import Submission.Work.Drive.Surf.Model
import Submission.Work.Drive.ncard_zeros_mod_four_eq_two
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.finite_of_isCompact_of_isolated
import Submission.Work.Surf.ncard_chordMeet_straightChord

/-!
# The straight case of the chord-crossing parity

If the second chord is the straight chord through a unit vector `w` and the pair satisfies the
"no crossings on the boundary of the square" (`hint`) and transversality (`htrans`) hypotheses, then
the number of crossing parameter pairs is odd.  The crossing set is in bijection with the zero set of
`s ↦ det2 (a s) w` (`Work.Surf.ncard_chordMeet_straightChord`), which takes opposite signs at the two
endpoints and has only sign-changing zeros (`htrans`), so has an odd number of them.
-/

namespace Work.Surf

open Set Filter
open scoped Topology

noncomputable section

open Work.Drive

/-- `deriv (straightChord w) t = -π sin (π t) • w`. -/
lemma deriv_straightChord (w : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    deriv (straightChord w) t = (-(Real.pi * Real.sin (Real.pi * t))) • w := by
  have hm : HasDerivAt (fun s : ℝ => Real.pi * s) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have hc : HasDerivAt (fun s : ℝ => Real.cos s) (-(Real.sin (Real.pi * t))) (Real.pi * t) :=
    Real.hasDerivAt_cos (Real.pi * t)
  have h1 : HasDerivAt (fun s : ℝ => Real.cos (Real.pi * s))
      (-(Real.sin (Real.pi * t)) * Real.pi) t := hc.comp t hm
  have h1' : HasDerivAt (fun s : ℝ => Real.cos (Real.pi * s))
      (-(Real.pi * Real.sin (Real.pi * t))) t := by
    convert h1 using 2
    ring
  have hfun : straightChord w = fun s : ℝ => Real.cos (Real.pi * s) • w := rfl
  rw [hfun]
  exact (h1'.smul_const w).deriv

/-- Two vectors with vanishing `det2`, the second nonzero, are proportional. -/
lemma det2_eq_zero_imp_smul {u w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) (h : det2 u w = 0) :
    ∃ lam : ℝ, u = lam • w := by
  have key : u 0 * w 1 = u 1 * w 0 := by
    have h' := h
    simp only [det2] at h'
    linarith
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 / w 1, ?_⟩
    ext i
    fin_cases i
    · simp only [smul_apply', Fin.zero_eta]
      rw [h0, mul_zero]
      have hk : u 0 * w 1 = 0 := by rw [key, h0, mul_zero]
      exact (mul_eq_zero.mp hk).resolve_right h1
    · simp only [smul_apply', Fin.mk_one]
      rw [div_mul_cancel₀ (u 1) h1]
  · refine ⟨u 0 / w 0, ?_⟩
    ext i
    fin_cases i
    · simp only [smul_apply', Fin.zero_eta]
      rw [div_mul_cancel₀ (u 0) h0]
    · simp only [smul_apply', Fin.mk_one]
      have h : u 0 / w 0 * w 1 = u 1 := by
        field_simp
        linarith [key]
      rw [h]

/-- For `|λ| < 1` there is `t ∈ (0,1)` with `cos (π t) = λ`. -/
lemma exists_cos_pi_mul_eq' {lam : ℝ} (h1 : -1 < lam) (h2 : lam < 1) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ Real.cos (Real.pi * t) = lam := by
  have hapos : 0 < Real.arccos lam := (Real.arccos_pos).mpr h2
  refine ⟨Real.arccos lam / Real.pi, ⟨div_pos hapos Real.pi_pos, ?_⟩, ?_⟩
  · rw [div_lt_one Real.pi_pos]
    exact (Real.arccos_lt_pi).mpr h1
  · rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.cos_arccos h1.le h2.le]

/-- `s ↦ det2 (a s) w` has derivative `det2 (deriv a s) w`. -/
lemma hasDerivAt_det2_comp {a : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (w : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    HasDerivAt (fun r => det2 (a r) w) (det2 (deriv a s) w) s := by
  have had : DifferentiableAt ℝ a s := (ha.differentiable (by norm_num)).differentiableAt
  have hd : HasDerivAt a (deriv a s) s := had.hasDerivAt
  have h0 : HasDerivAt (fun r => (a r) 0) ((deriv a s) 0) s := by
    show HasDerivAt ((fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 0) ∘ a) ((deriv a s).ofLp 0) s
    exact (EuclideanSpace.proj (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt s hd
  have h1 : HasDerivAt (fun r => (a r) 1) ((deriv a s) 1) s := by
    show HasDerivAt ((fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 1) ∘ a) ((deriv a s).ofLp 1) s
    exact (EuclideanSpace.proj (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt s hd
  have hcomb : HasDerivAt (fun r => (a r) 0 * w 1 - (a r) 1 * w 0)
      ((deriv a s) 0 * w 1 - (deriv a s) 1 * w 0) s :=
    (h0.mul_const (w 1)).sub (h1.mul_const (w 0))
  have hfun : (fun r => det2 (a r) w) = fun r => (a r) 0 * w 1 - (a r) 1 * w 0 := by
    funext r; simp only [det2]
  rw [hfun]
  convert hcomb using 2
  simp only [det2]

/-- A differentiable function with nonzero derivative at a zero changes sign there. -/
lemma signChangeAt_of_deriv_ne_zero {f : ℝ → ℝ} {x c : ℝ} (h : HasDerivAt f c x) (hc : c ≠ 0)
    (hx : f x = 0) : SignChangeAt f x := by
  have h' : HasDerivAt f c (x + 0) := by simpa using h
  have hm : HasDerivAt (fun t : ℝ => x + t) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add x
  have hg : HasDerivAt (fun t : ℝ => f (x + t)) c 0 := by
    have hcomp := h'.comp 0 hm
    simpa [Function.comp_def] using hcomp
  have hxs : ∀ s : ℝ, x + (s - x) = s := fun s => by ring
  rcases lt_or_gt_of_ne hc with hc' | hc'
  · obtain ⟨δ, hδ, hP1, hP2, -⟩ := scalar_neg hg hc'
    refine Or.inr ⟨δ, hδ, ?_, ?_⟩
    · intro s hs1 hs2
      have ht : s - x ∈ Ioo (-δ) 0 := ⟨by linarith, by linarith⟩
      have h2 := hP2 (s - x) ht
      rw [hxs s, add_zero, hx] at h2
      exact h2
    · intro s hs1 hs2
      have ht : s - x ∈ Ioo (0:ℝ) δ := ⟨by linarith, by linarith⟩
      have h1 := hP1 (s - x) ht
      rw [hxs s, add_zero, hx] at h1
      exact h1
  · obtain ⟨δ, hδ, hP1, hP2, -⟩ := scalar_pos hg hc'
    refine Or.inl ⟨δ, hδ, ?_, ?_⟩
    · intro s hs1 hs2
      have ht : s - x ∈ Ioo (-δ) 0 := ⟨by linarith, by linarith⟩
      have h2 := hP2 (s - x) ht
      rw [hxs s, add_zero, hx] at h2
      exact h2
    · intro s hs1 hs2
      have ht : s - x ∈ Ioo (0:ℝ) δ := ⟨by linarith, by linarith⟩
      have h1 := hP1 (s - x) ht
      rw [hxs s, add_zero, hx] at h1
      exact h1

/-- A sign-changing zero is isolated among the zeros. -/
lemma exists_ne_zero_nhdsNE_of_signChangeAt {f : ℝ → ℝ} {t : ℝ} (h : SignChangeAt f t) :
    ∃ ε > 0, ∀ s, t - ε < s → s < t + ε → s ≠ t → f s ≠ 0 := by
  rcases h with ⟨ε, hε, h1, h2⟩ | ⟨ε, hε, h1, h2⟩
  · refine ⟨ε, hε, ?_⟩
    intro s hs1 hs2 hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ne_of_lt (h1 s hs1 hlt)
    · exact ne_of_gt (h2 s hgt hs2)
  · refine ⟨ε, hε, ?_⟩
    intro s hs1 hs2 hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ne_of_gt (h1 s hs1 hlt)
    · exact ne_of_lt (h2 s hgt hs2)

/-- `f s = det2 (a s) w` is continuous. -/
lemma continuous_det2_comp {a : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : Continuous a)
    (w : EuclideanSpace ℝ (Fin 2)) : Continuous (fun s => det2 (a s) w) := by
  have h0 : Continuous fun s : ℝ => (a s) 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous.comp ha
  have h1 : Continuous fun s : ℝ => (a s) 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.comp ha
  have hfun : (fun s => det2 (a s) w) = fun s => (a s) 0 * w 1 - (a s) 1 * w 0 := by
    funext s; simp only [det2]
  rw [hfun]
  exact (h0.mul continuous_const).sub (h1.mul continuous_const)

/-- **The straight case: a chord against a straight chord crosses an odd number of times.** -/
theorem chordMeet_straight_odd {a : ℝ → EuclideanSpace ℝ (Fin 2)}
    {w : EuclideanSpace ℝ (Fin 2)} (ha : IsChord a) (hw : w ∈ unitCircle)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      a s = straightChord w t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1)
    (htrans : ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 →
      a s = straightChord w t →
      det2 (deriv a s) (deriv (straightChord w) t) ≠ 0) :
    Odd (chordMeet a (straightChord w)).ncard := by
  have hw1 : ‖w‖ = 1 := hw
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  have hne_w : ∀ s ∈ Set.Icc (0 : ℝ) 1, a s ≠ w := by
    intro s hs h
    have h' : a s = straightChord w 0 := by rw [h, straightChord_zero]
    obtain ⟨-, ht, -⟩ := hint s 0 hs (by norm_num) h'
    exact absurd ht.1 (by norm_num)
  have hne_nw : ∀ s ∈ Set.Icc (0 : ℝ) 1, a s ≠ -w := by
    intro s hs h
    have h' : a s = straightChord w 1 := by rw [h, straightChord_one]
    obtain ⟨-, ht, -⟩ := hint s 1 hs (by norm_num) h'
    exact absurd ht.2 (by norm_num)
  have hC := ncard_chordMeet_straightChord ha hw hne_w hne_nw
  set f : ℝ → ℝ := fun r => det2 (a r) w with hf
  have hCf : (chordMeet a (straightChord w)).ncard
      = ({s ∈ Set.Icc (0 : ℝ) 1 | f s = 0} : Set ℝ).ncard := by
    rw [hC]
  rw [hCf]
  have hfcont : Continuous f := by
    rw [hf]; exact continuous_det2_comp ha.continuous w
  have hfderiv : ∀ s : ℝ, HasDerivAt f (det2 (deriv a s) w) s := by
    intro s
    rw [hf]
    exact hasDerivAt_det2_comp ha.contDiff w s
  have hf0 : f 0 ≠ 0 := by
    intro h0
    have h0' : det2 (a 0) w = 0 := h0
    obtain ⟨lam, hlam⟩ := det2_eq_zero_imp_smul hw0 h0'
    have hnorm : |lam| = 1 := by
      have h2 : ‖a 0‖ = 1 := ha.start
      rw [hlam, norm_smul, Real.norm_eq_abs, hw1, mul_one] at h2
      exact h2
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with h1 | h1
    · exact hne_w 0 ⟨le_refl 0, zero_le_one⟩ (by rw [hlam, h1, one_smul])
    · exact hne_nw 0 ⟨le_refl 0, zero_le_one⟩ (by rw [hlam, h1, neg_one_smul])
  have hf1 : f 1 = -f 0 := by
    have h1 : a 1 = -a 0 := by simpa using ha.periodic 0
    rw [hf]
    show det2 (a 1) w = -det2 (a 0) w
    rw [h1]
    simp only [Work.Drive.det2, WithLp.ofLp_neg, Pi.neg_apply]
    ring
  -- the derivative of `f` never vanishes at a zero of `f` in the interval
  have hderiv_ne : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s = 0 → det2 (deriv a s) w ≠ 0 := by
    intro s hs hsz
    have hsz' : det2 (a s) w = 0 := hsz
    have hsint : s ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩
      · intro h; exact hf0 (h ▸ hsz)
      · intro h
        have h1 : f 1 = 0 := h ▸ hsz
        refine hf0 ?_
        have h2 := h1
        rw [hf1] at h2
        simpa using h2
    obtain ⟨lam, hlam⟩ := det2_eq_zero_imp_smul hw0 hsz'
    have hlt : ‖a s‖ < 1 := by
      have hle : ‖a s‖ ≤ 1 := by
        have := ha.mem_disk s hs
        simpa [unitDisk, Set.mem_ofPred_eq] using this
      have hnorm : ‖a s‖ = |lam| := by
        rw [hlam, norm_smul, Real.norm_eq_abs, hw1, mul_one]
      have hlam_le : |lam| ≤ 1 := by rw [← hnorm]; exact hle
      have hne1 : |lam| ≠ 1 := by
        intro hcon
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hcon with h1 | h1
        · exact hne_w s hs (by rw [hlam, h1, one_smul])
        · exact hne_nw s hs (by rw [hlam, h1, neg_one_smul])
      rw [hnorm]
      exact lt_of_le_of_ne hlam_le hne1
    have hlam_lt : |lam| < 1 := by
      have hnorm : ‖a s‖ = |lam| := by
        rw [hlam, norm_smul, Real.norm_eq_abs, hw1, mul_one]
      rw [← hnorm]; exact hlt
    obtain ⟨t, htIoo, htcos⟩ := exists_cos_pi_mul_eq' (abs_lt.mp hlam_lt).1 (abs_lt.mp hlam_lt).2
    have hcross : a s = straightChord w t := by
      rw [hlam, straightChord]
      simp only [htcos]
    have htr := htrans s t hsint htIoo hcross
    rw [deriv_straightChord, det2_smul_right] at htr
    have hsin : Real.pi * Real.sin (Real.pi * t) ≠ 0 := by
      have : Real.sin (Real.pi * t) ≠ 0 := by
        intro h
        have h1 : Real.pi * t ∈ Set.Ioo (0:ℝ) Real.pi :=
          ⟨mul_pos Real.pi_pos htIoo.1, by nlinarith [htIoo.2, Real.pi_pos]⟩
        exact (Real.sin_pos_of_mem_Ioo h1).ne' h
      exact mul_ne_zero Real.pi_ne_zero this
    intro hzero
    exact htr (by rw [hzero, mul_zero])
  have hsc : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 → SignChangeAt f t := by
    intro t ht htz
    exact signChangeAt_of_deriv_ne_zero (hfderiv t) (hderiv_ne t ht htz) htz
  -- the zero set is finite
  have hfin : ({t ∈ Set.Icc (0 : ℝ) 1 | f t = 0} : Set ℝ).Finite := by
    refine finite_of_isCompact_of_isolated ?_ ?_
    · refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun x hx => hx.1)
      exact (isClosed_Icc.preimage continuous_id).inter (isClosed_singleton.preimage hfcont)
    · intro t ht
      obtain ⟨ε, hε, hne⟩ := exists_ne_zero_nhdsNE_of_signChangeAt (hsc t ht.1 ht.2)
      refine ⟨Ioo (t - ε) (t + ε), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
      rintro s ⟨hs, hsZ⟩
      by_contra hcon
      exact hne s hs.1 hs.2 hcon hsZ.2
  refine odd_ncard_zeros_of_opposite_signs (by norm_num) hfcont.continuousOn hfin hsc hf0 ?_ ?_
  · rw [hf1]; exact neg_ne_zero.mpr hf0
  · rcases lt_or_gt_of_ne hf0 with h | h
    · exact Or.inl ⟨h, by rw [hf1]; linarith⟩
    · exact Or.inr ⟨by rw [hf1]; linarith, h⟩

end

end Work.Surf
