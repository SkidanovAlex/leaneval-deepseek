import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornSC.Toolkit
import Submission.Work.HornSC.joinedIn_componentIn_strip
import Submission.Work.HornSC.path_between_strip_sides
import Submission.Work.HornSC.wall_blocks_path

namespace Work.HornSC

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! The three planar-topology ingredients of this area live in their own modules:

* `Submission.Work.HornSC.path_between_strip_sides`,
* `Submission.Work.HornSC.wall_blocks_path`,
* `Submission.Work.HornSC.joinedIn_componentIn_strip`. -/

/-- For `A` invariant under translation by `1`, membership is invariant under every integer shift. -/
theorem aux_mem_add_int {A : Set ℂ} (hAT : MandelDim.IsTInvariant A) (k : ℤ) (w : ℂ) :
    w ∈ A ↔ w + (k : ℂ) ∈ A := by
  have hnat : ∀ n : ℕ, ∀ w : ℂ, w ∈ A ↔ w + (n : ℂ) ∈ A := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ m ih =>
        intro w
        have h1 : w + ((m + 1 : ℕ) : ℂ) = (w + (m : ℂ)) + 1 := by push_cast; ring
        rw [h1, ← hAT (w + (m : ℂ))]
        exact ih w
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · subst hn; exact hnat n w
  · subst hn
    have h := hnat n (w + (-(n : ℂ)))
    have h2 : w + (-(n : ℂ)) + (n : ℂ) = w := by ring
    rw [h2] at h
    simpa using h.symm

theorem separates_strip_tinvariant (η : ℝ) (A : Set ℂ) (hAcl : IsClosed A)
    (hAT : MandelDim.IsTInvariant A) (hAsub : A ⊆ {w : ℂ | |w.im| ≤ η})
    (hC : ∃ z ∈ A, ¬ Bornology.IsBounded (connectedComponentIn A z)) :
    ∀ y ∈ {w : ℂ | η < w.im}, ∀ z ∈ {w : ℂ | w.im < -η},
      connectedComponentIn Aᶜ y ≠ connectedComponentIn Aᶜ z := by
  intro y hy z hz h_eq
  have hyim : η < y.im := hy
  have hzim : z.im < -η := hz
  obtain ⟨z₀, hz₀A, hz₀unb⟩ := hC
  have hz₀sub := hAsub hz₀A
  have hz₀im : |z₀.im| ≤ η := hz₀sub
  have hη0 : 0 ≤ η := le_trans (abs_nonneg z₀.im) hz₀im
  have hAc : IsOpen Aᶜ := hAcl.isOpen_compl
  have hyAc : y ∈ Aᶜ := by
    intro hyA
    have h1 : |y.im| ≤ η := hAsub hyA
    have h2 : y.im ≤ η := (abs_le.mp h1).2
    linarith
  have hzAc : z ∈ Aᶜ := by
    intro hzA
    have h1 : |z.im| ≤ η := hAsub hzA
    have h2 : -η ≤ z.im := (abs_le.mp h1).1
    linarith
  -- the component of `Aᶜ` containing `y` and `z` is path connected
  have hYpc : IsPathConnected (connectedComponentIn Aᶜ y) := by
    refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
      ⟨⟨y, mem_connectedComponentIn hyAc⟩, isPreconnected_connectedComponentIn⟩ ?_
    intro u hu
    have huo : IsOpen (connectedComponentIn Aᶜ y) := hAc.connectedComponentIn
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp huo u hu
    exact ⟨Metric.ball u δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos,
      Metric.isPathConnected_ball hδpos, hδsub⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Path y z, Set.range Γ ⊆ Aᶜ := by
    obtain ⟨x₀, hx₀, hjoin⟩ := hYpc
    have hy' : y ∈ connectedComponentIn Aᶜ y := mem_connectedComponentIn hyAc
    have hz' : z ∈ connectedComponentIn Aᶜ y := by
      rw [h_eq]; exact mem_connectedComponentIn hzAc
    obtain ⟨Γ, hΓs⟩ := (hjoin hy').symm.trans (hjoin hz')
    exact ⟨Γ, fun w hw => connectedComponentIn_subset Aᶜ y (by
      obtain ⟨t, rfl⟩ := hw; exact hΓs t)⟩
  -- extract the wall path
  have hy_im : η < (Γ.toContinuousMap 0).im := by
    show η < (Γ 0).im
    rw [Γ.source]; exact hyim
  have hz_im : (Γ.toContinuousMap 1).im < -η := by
    show (Γ 1).im < -η
    rw [Γ.target]; exact hzim
  obtain ⟨V, M, hM0, hVm, hVp, hVbox, hVrange⟩ :=
    path_between_strip_sides hη0 hy_im hz_im
  -- the box for the wall
  set a : ℝ := -M - 1 with ha
  set b : ℝ := M + 1 with hb
  have hab : a < b := by rw [ha, hb]; linarith
  have hVbox' : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (V t).re ∈ Set.Icc a b ∧ (V t).im ∈ Set.Icc (-η) η := by
    intro t ht
    obtain ⟨him, hre⟩ := hVbox t ht
    have hre' : -M ≤ (V t).re ∧ (V t).re ≤ M := abs_le.mp hre
    have him' : -η ≤ (V t).im ∧ (V t).im ≤ η := abs_le.mp him
    exact ⟨⟨by rw [ha]; linarith [hre'.1], by rw [hb]; linarith [hre'.2]⟩, him'⟩
  -- the wall set and the free region
  set K : Set ℂ := V '' Set.Icc (-1:ℝ) 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.image V.continuous
  set W : Set ℂ := {w : ℂ | ∃ k : ℤ, ∃ u ∈ K, w = u + (k : ℂ)} with hWdef
  set Ω : Set ℂ := {w : ℂ | |w.im| ≤ η} \ W with hΩdef
  have hΩS : Ω ⊆ {z : ℂ | |z.im| ≤ η} := fun w hw => hw.1
  have hVrangeA : Set.range V ⊆ Aᶜ := hVrange.trans hΓ
  have hAΩ : A ⊆ Ω := by
    intro w hwA
    refine ⟨hAsub hwA, ?_⟩
    rintro ⟨k, u, huK, hwu⟩
    obtain ⟨s, hs, rfl⟩ := huK
    have hVsAc : V s ∈ Aᶜ := hVrangeA (Set.mem_range_self s)
    have hVsA : V s ∈ A := by
      have h := (aux_mem_add_int hAT (-k) w).mp hwA
      have h2 : w + ((-k : ℤ) : ℂ) = V s := by rw [hwu]; push_cast; ring
      rwa [h2] at h
    exact hVsAc hVsA
  -- `W` is closed
  have hWclosed : IsClosed W := by
    have hcont : Continuous (fun w : ℂ => Complex.exp (2 * Real.pi * I * w)) := by fun_prop
    have hKeq : W = (fun w : ℂ => Complex.exp (2 * Real.pi * I * w)) ⁻¹'
        ((fun w : ℂ => Complex.exp (2 * Real.pi * I * w)) '' K) := by
      ext w
      constructor
      · rintro ⟨k, u, huK, rfl⟩
        refine Set.mem_preimage.mpr ⟨u, huK, ?_⟩
        have h1 : (2 * Real.pi * I : ℂ) * (u + (k : ℂ)) =
            2 * Real.pi * I * u + (k : ℂ) * (2 * Real.pi * I) := by ring_nf
        rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · intro hw
        obtain ⟨u, huK, heq⟩ := Set.mem_preimage.mp hw
        rw [Complex.exp_eq_exp_iff_exists_int] at heq
        obtain ⟨n, hn⟩ := heq
        have h3 : (2 * Real.pi * I : ℂ) * (w - u + (n : ℂ)) = 0 := by
          have h7 : (2 * Real.pi * I : ℂ) * (w - u + (n : ℂ))
              = (2 * Real.pi * I * w - 2 * Real.pi * I * u)
                + (2 * Real.pi * I) * (n : ℂ) := by ring
          rw [h7, hn]; ring
        have h4 : (2 * Real.pi * I : ℂ) ≠ 0 := by
          have hπ : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
            simp [Real.pi_ne_zero]
          exact mul_ne_zero hπ Complex.I_ne_zero
        have h5 : w - u + (n : ℂ) = 0 := by
          rcases mul_eq_zero.mp h3 with h | h
          · exact absurd h h4
          · exact h
        have h6 : w = u - (n : ℂ) := by linear_combination h5
        exact ⟨-n, u, huK, by push_cast; exact h6⟩
    rw [hKeq]
    exact (hKc.image hcont).isClosed.preimage hcont
  have hΩopen : ∀ u ∈ Ω, ∃ δ : ℝ, 0 < δ ∧ Metric.ball u δ ∩ {z : ℂ | |z.im| ≤ η} ⊆ Ω := by
    intro u hu
    have huW : u ∉ W := hu.2
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hWclosed.isOpen_compl u huW
    exact ⟨δ, hδpos, fun w hw => ⟨hw.2, fun hwW => hδsub hw.1 hwW⟩⟩
  -- the component of the free region containing `C`
  have hCX : connectedComponentIn A z₀ ⊆ connectedComponentIn Ω z₀ :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hz₀A)
      (fun w hw => hAΩ (connectedComponentIn_subset A z₀ hw))
  have hXjoin : ∀ w ∈ connectedComponentIn Ω z₀, JoinedIn Ω z₀ w :=
    fun w hw => joinedIn_componentIn_strip hΩS hΩopen hw
  -- a point of the unbounded component with large real part
  have hUnb : ∀ R : ℝ, ∃ w ∈ connectedComponentIn A z₀, R < ‖w‖ := by
    intro R
    by_contra hcon
    push Not at hcon
    exact hz₀unb (isBounded_iff_forall_norm_le.mpr ⟨R, fun x hx => hcon x hx⟩)
  obtain ⟨w, hwC, hwbig⟩ := hUnb (|z₀.re| + (b - a) + 3 + |η|)
  have hwX : w ∈ connectedComponentIn Ω z₀ := hCX hwC
  have hwre : |z₀.re| + (b - a) + 2 < |w.re| := by
    have hImw : |w.im| ≤ |η| := by
      have h1 : |w.im| ≤ η := by
        have := hAsub (connectedComponentIn_subset A z₀ hwC)
        simpa using this
      exact le_trans h1 (le_abs_self η)
    have hnorm : ‖w‖ ≤ |w.re| + |w.im| := by
      have h3 : ‖w‖ ^ 2 ≤ (|w.re| + |w.im|) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [sq_abs w.re, sq_abs w.im, abs_nonneg w.re, abs_nonneg w.im]
      rw [sq_le_sq] at h3
      rwa [abs_of_nonneg (norm_nonneg w),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |w.re| + |w.im|)] at h3
    linarith
  -- pick the integer shift
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, min w.re z₀.re < a + (k : ℝ) ∧ b + (k : ℝ) < max w.re z₀.re := by
    have hgap : (max w.re z₀.re - b) - (min w.re z₀.re - a) > 1 := by
      have hmm : max w.re z₀.re - min w.re z₀.re = |w.re - z₀.re| := by
        rw [max_sub_min_eq_abs, abs_sub_comm]
      have htri : |w.re| ≤ |w.re - z₀.re| + |z₀.re| := by
        have h := abs_add_le (w.re - z₀.re) z₀.re
        have h2 : w.re - z₀.re + z₀.re = w.re := by ring
        rwa [h2] at h
      linarith
    refine ⟨⌊min w.re z₀.re - a⌋ + 1, ?_, ?_⟩
    · have h1 : min w.re z₀.re - a < ((⌊min w.re z₀.re - a⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      push_cast
      linarith
    · have h1 : ((⌊min w.re z₀.re - a⌋ : ℤ) : ℝ) ≤ min w.re z₀.re - a := Int.floor_le _
      push_cast
      linarith
  -- the path from the low point to the high point
  set lo : ℂ := if w.re ≤ z₀.re then w else z₀ with hLodef
  set hi : ℂ := if w.re ≤ z₀.re then z₀ else w with hHidef
  have hlore : lo.re = min w.re z₀.re := by
    rw [hLodef]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_lt (not_le.mp h))).symm
  have hhire : hi.re = max w.re z₀.re := by
    rw [hHidef]
    split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (le_of_lt (not_le.mp h))).symm
  have hloX : lo ∈ connectedComponentIn Ω z₀ := by
    rw [hLodef]
    split_ifs with h
    · exact hwX
    · exact mem_connectedComponentIn (hAΩ hz₀A)
  have hhiX : hi ∈ connectedComponentIn Ω z₀ := by
    rw [hHidef]
    split_ifs with h
    · exact mem_connectedComponentIn (hAΩ hz₀A)
    · exact hwX
  obtain ⟨γ2, hγ2⟩ : ∃ γ2 : Path lo hi, ∀ t, γ2 t ∈ Ω :=
    (hXjoin lo hloX).symm.trans (hXjoin hi hhiX)
  -- shift so that the wall sits at the origin
  let ρE : C(ℝ, ℂ) := γ2.extend - ContinuousMap.const ℝ (k : ℂ)
  have hρE_im : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → |(ρE t).im| ≤ η := by
    intro t ht
    have h1 : γ2.extend t ∈ Ω := by
      rw [Path.extend_apply γ2 ht]; exact hγ2 ⟨t, ht⟩
    have h2 : (γ2.extend t).im = (ρE t).im := by
      simp [ρE, Complex.sub_im]
    rw [← h2]; exact h1.1
  have hρE0 : (ρE 0).re < a := by
    have h1 : γ2.extend 0 = lo := Path.extend_zero γ2
    have h2 : (ρE 0).re = lo.re - (k : ℝ) := by simp [ρE, h1, Complex.sub_re]
    rw [h2, hlore]; linarith
  have hρE1 : b < (ρE 1).re := by
    have h1 : γ2.extend 1 = hi := Path.extend_one γ2
    have h2 : (ρE 1).re = hi.re - (k : ℝ) := by simp [ρE, h1, Complex.sub_re]
    rw [h2, hhire]; linarith
  obtain ⟨t, ht, s, hs, hts⟩ :=
    wall_blocks_path (η := η) (X := a) (Y := b) hab hVbox' hVm hVp hρE_im hρE0 hρE1
  -- contradiction
  have hmemΩ : γ2.extend t ∈ Ω := by
    rw [Path.extend_apply γ2 ht]; exact hγ2 ⟨t, ht⟩
  have hmemW : γ2.extend t ∈ W := by
    refine ⟨k, V s, ⟨s, hs, rfl⟩, ?_⟩
    have h3 : ρE t = V s := hts
    simp only [ρE, ContinuousMap.sub_apply, ContinuousMap.const_apply] at h3
    linear_combination h3
  exact hmemΩ.2 hmemW

end

end Work.HornSC
