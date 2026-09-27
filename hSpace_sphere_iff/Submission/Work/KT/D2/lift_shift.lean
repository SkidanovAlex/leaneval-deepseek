import Mathlib
import Submission.Work.KT.D2.CircleDegreeDefs

namespace Work.KT.D2

/-!
# Lifts of a loop through the exponential covering differ by an integral multiple of `W`

Let `f : C(S¹, ℂˣ)` be a loop in the units of `ℂ` and let `canLift f : C(I, ℂ)` be the canonical
lift of `t ↦ f (stdLoop t)` through the exponential covering, based at `base f` (`CircleDegreeDefs`).
If `G : C(I, ℂ)` is any other lift of the same loop, i.e. `exp (G t) = f (stdLoop t)` for all `t`,
then `G` and `canLift f` differ by a *constant* integral multiple of the period `W = 2πi`.

The proof is the standard discreteness argument: the difference `H = G - canLift f` is continuous
with `exp (H t) = 1`, hence `H t / W` is a real integer for every `t`.  The continuous `ℝ`-valued
map `t ↦ (H t / W).re` therefore has preconnected image contained in `ℤ ⊂ ℝ`, and a preconnected
subset of `ℤ` is a single point; so `t ↦ (H t / W).re` is constant, and since `(H t / W).im = 0`
for all `t`, the whole difference `H` is constant.
-/

noncomputable section

/-- An element of `ℂ` whose exponential is `1` is an integral multiple of the period `W = 2πi`. -/
lemma exp_eq_one_iff_exists_mul_W {u : ℂ} (hu : Complex.exp u = 1) :
    ∃ n : ℤ, u = n * W := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hu
  exact ⟨n, by rw [hn]; simp [W]⟩

/-- If `exp u = 1` then `u / W` is an integer (viewed as a real number). -/
lemma exp_one_div_W_isInt {u : ℂ} (hu : Complex.exp u = 1) :
    ∃ n : ℤ, u / W = ((n : ℝ) : ℂ) := by
  obtain ⟨n, hn⟩ := exp_eq_one_iff_exists_mul_W hu
  refine ⟨n, ?_⟩
  rw [hn, mul_comm ((n : ℤ) : ℂ) W, mul_div_cancel_left₀ ((n : ℤ) : ℂ) W_ne_zero]
  push_cast
  ring

/-- If `exp u = 1` then `u / W` is real, i.e. its imaginary part vanishes. -/
lemma exp_one_div_W_im_zero {u : ℂ} (hu : Complex.exp u = 1) : (u / W).im = 0 := by
  obtain ⟨n, hn⟩ := exp_one_div_W_isInt hu
  rw [hn, Complex.ofReal_im]

/-- A preconnected subset of `ℤ ⊂ ℝ` is a subsingleton: it cannot contain two distinct integers,
since it would then contain the non-integer midpoint `k + 1/2`. -/
lemma isPreconnected_subsingleton_of_subset_intRange {s : Set ℝ} (hs : IsPreconnected s)
    (h : ∀ x ∈ s, ∃ k : ℤ, (k : ℝ) = x) : s.Subsingleton := by
  intro a ha b hb
  obtain ⟨ka, hka⟩ := h a ha
  obtain ⟨kb, hkb⟩ := h b hb
  subst hka; subst hkb
  by_contra hne
  have key : ∀ (k l : ℤ), (k : ℝ) ∈ s → (l : ℝ) ∈ s → (k : ℝ) < (l : ℝ) → False := by
    intro k l hk hl hkl
    have hklt : k < l := Int.cast_lt.mp hkl
    have hk1 : k + 1 ≤ l := by omega
    have hle : (k : ℝ) + 1/2 ∈ Set.Icc (k : ℝ) (l : ℝ) := by
      refine ⟨by linarith, ?_⟩
      have hcast : ((k + 1 : ℤ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hk1
      calc (k : ℝ) + 1/2 ≤ (k : ℝ) + 1 := by norm_num
        _ = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
        _ ≤ (l : ℝ) := hcast
    have hmem : (k : ℝ) + 1/2 ∈ s := hs.Icc_subset hk hl hle
    obtain ⟨j, hj⟩ := h ((k : ℝ) + 1/2) hmem
    have hj2 : ((j - k : ℤ) : ℝ) = 1/2 := by
      have : ((j - k : ℤ) : ℝ) = (j : ℝ) - (k : ℝ) := by push_cast; ring
      rw [this]; linarith
    have hb0 : ((0 : ℤ) : ℝ) < ((j - k : ℤ) : ℝ) := by rw [hj2]; norm_num
    have hb1 : ((j - k : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by rw [hj2]; norm_num
    have h0 : (0 : ℤ) < j - k := Int.cast_lt.mp hb0
    have h1 : j - k < 1 := Int.cast_lt.mp hb1
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key ka kb ha hb hlt
  · exact key kb ka hb ha hlt

/-- A continuous real-valued function on `unitInterval` taking values in the integers is constant. -/
lemma continuous_intValued_const (g : C(unitInterval, ℝ))
    (hg : ∀ t, g t ∈ Set.range fun k : ℤ => (k : ℝ)) : ∀ s t, g s = g t := by
  have hpre : IsPreconnected (Set.range g) := by
    have h := isPreconnected_univ.image (g : unitInterval → ℝ) g.continuous.continuousOn
    rwa [Set.image_univ] at h
  have hss : (Set.range g).Subsingleton :=
    isPreconnected_subsingleton_of_subset_intRange hpre
      (by rintro y ⟨t, rfl⟩; exact hg t)
  exact fun s t => hss (Set.mem_range_self s) (Set.mem_range_self t)

/-- Two lifts of the loop `t ↦ f (stdLoop t)` through the exponential covering differ by a constant
integral multiple of the period `W = 2πi`. -/
theorem lift_shift (f : C(Work.KT.D2.S1, ℂˣ)) (G : C(unitInterval, ℂ))
    (hG : ∀ t, Complex.exp (G t) = (f (Work.KT.D2.stdLoop t) : ℂ)) :
    ∃ m : ℤ, ∀ t, G t = Work.KT.D2.canLift f t + m * Work.KT.D2.W := by
  -- The difference of the two lifts.
  let H : C(unitInterval, ℂ) := G - canLift f
  have hHval : ∀ t, H t = G t - canLift f t :=
    fun t => ContinuousMap.sub_apply G (canLift f) t
  -- Both are lifts of the same loop, so `exp` of the difference is `1`.
  have hExp : ∀ t, Complex.exp (H t) = 1 := by
    intro t
    have h2 : Complex.exp (canLift f t) = (f (stdLoop t) : ℂ) := by
      have h := congrArg (fun x : nzC => (x : ℂ)) (canLift_spec f t)
      simpa [expSub_coe, loopOf_apply] using h
    rw [hHval t, Complex.exp_sub, hG t, h2]
    exact div_self (Units.ne_zero (f (stdLoop t)))
  -- The normalized real part of the difference is a continuous integer-valued function.
  let g : C(unitInterval, ℝ) := ⟨fun t => (H t / W).re, by
    exact Complex.continuous_re.comp (H.continuous.div_const W)⟩
  have hg_int : ∀ t, g t ∈ Set.range fun k : ℤ => (k : ℝ) := by
    intro t
    obtain ⟨n, hn⟩ := exp_one_div_W_isInt (hExp t)
    refine ⟨n, ?_⟩
    show (n : ℝ) = (H t / W).re
    rw [hn, Complex.ofReal_re]
  have hconst : ∀ s t, g s = g t := continuous_intValued_const g hg_int
  -- Hence the difference itself is constant.
  have hHconst : ∀ t, H t = H 0 := by
    intro t
    have hreal_t : H t / W = ((g t : ℝ) : ℂ) := by
      apply Complex.ext
      · show (H t / W).re = (((g t : ℝ) : ℂ)).re
        rw [Complex.ofReal_re]; rfl
      · rw [exp_one_div_W_im_zero (hExp t), Complex.ofReal_im]
    have hreal_0 : H 0 / W = ((g 0 : ℝ) : ℂ) := by
      apply Complex.ext
      · show (H 0 / W).re = (((g 0 : ℝ) : ℂ)).re
        rw [Complex.ofReal_re]; rfl
      · rw [exp_one_div_W_im_zero (hExp 0), Complex.ofReal_im]
    have heq : H t / W = H 0 / W := by rw [hreal_t, hreal_0, hconst t 0]
    have h := congrArg (fun z => z * W) heq
    rwa [div_mul_cancel₀ _ W_ne_zero, div_mul_cancel₀ _ W_ne_zero] at h
  obtain ⟨m, hm⟩ := exp_eq_one_iff_exists_mul_W (hExp 0)
  refine ⟨m, fun t => ?_⟩
  have hsub : G t - canLift f t = (m : ℂ) * W := by rw [← hHval t, hHconst t, hm]
  have h2 : G t = canLift f t + (m : ℂ) * W := by rw [← hsub]; ring
  exact h2

end

end Work.KT.D2
