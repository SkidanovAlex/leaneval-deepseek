import Submission.Work.TMC14Core.RatRot
import Submission.Work.TMC14Core.rotLift_eq_rotQ
import Submission.Work.TMC14Core.rotQ_continuous
import Submission.Work.TMC14Core.rotQ_antitone
import Submission.Work.TMC14Core.disc_zero_abs
import Submission.Work.TMC14Core.discRe_strictMonoOn_or_strictAntiOn
import Submission.Work.TMC14Core.hyps_reduce
import Submission.Work.TMC14Core.rotQ_int_iff_trace
import Submission.Work.TMC14Core.abs_trAq_eq_trace_iterR
import Submission.Work.TMC14Core.drop_le_two_of_union
import Submission.Work.TMC14Core.preimage_Ioo_inter_eq_Ioo
import Submission.Work.TMC14Core.exists_coprime_reduce
import Submission.Work.TMC14Core.strictMonoOn_or_strictAntiOn_of_deriv_ne_zero
import Submission.Work.TMC14Core.disc_im_eq_zero
import Submission.Work.TMC14Core.chamCoef_norm

/-!
# TMC14Core: 14c — the variation of `N_{p/q}` inside the union spectrum

The variation of the integrated density of states of the rational approximant `p/q` over an
interval contained in the union spectrum is at most `2/q'` (`q' = q / gcd(p,q)` the reduced
denominator).

The proof has three layers.

* **Reduction to a reduced fraction.**  `(p/q) = (p'/q')` with `q' = q/gcd`, and `trAq`, `ids`,
  `ratSpec` depend on `p, q` only through the real frequency `p/q`, so it suffices to treat
  coprime `p, q`.

* **The fibre point of view.**  For coprime `p, q` the `q`-step Prüfer map
  `qMap p q lam E x` is the monodromy of the cocycle, and
  `rotLift (p/q) lam E = (1/q) ∫₀¹ rotQ p q lam E x dx`, where `rotQ` is the rotation number
  of that monodromy.  On the union spectrum the fibre rotation number is *not* integral
  (`rotQ ∉ ℤ ⟺ |tr A_q| < 2`), so that on each interval where the discriminant `Δ = disc p q lam`
  is strictly monotone — i.e. throughout a band — the drop of `x ↦ rotQ p q lam · x` across the
  interval is at most `1`, and at most `2` in general (the two central bands touch at `0` for
  even `q`, and `Δ' ≠ 0` on `{‖Δ‖ ≤ 2 + 2λ^q}` except at `0`).

* **Assembly.**  Hence `N(b) - N(a) = rotLift a - rotLift b ≤ 2/q`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## Statements delegated to the fleet (imported once proved) -/

theorem pruferStep_bridge_local : @Work.TMC14Core.pruferStep = @Work.TMContract.pruferStep := rfl

/-- The two copies of `pruferIter` agree. -/
theorem pruferIter_bridge_local (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    Work.TMC14Core.pruferIter α lam E n x t = Work.TMContract.pruferIter α lam E n x t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [Work.TMC14Core.pruferIter, Work.TMContract.pruferIter]
    rw [ih]
    exact congrFun (congrFun pruferStep_bridge_local _) _

/-- `rotLift` is the same in the two copies of the vocabulary. -/
theorem rotLift_bridge' (α lam E : ℝ) :
    Work.TMC14Core.rotLift α lam E = Work.TMContract.rotLift α lam E := by
  unfold Work.TMC14Core.rotLift Work.TMContract.rotLift
  congr 1
  funext n
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact pruferIter_bridge_local α lam E n x 0

/-- `ids` is the same in the two copies of the vocabulary. -/
theorem ids_bridge' (α lam E : ℝ) :
    Work.TMC14Core.ids α lam E = Work.TMContract.ids α lam E := by
  simp only [Work.TMC14Core.ids, Work.TMContract.ids, rotLift_bridge']

/-- `chamCoef p q lam` is a real number. -/
theorem chamCoef_im (p : ℤ) (q : ℕ) (lam : ℝ) : (chamCoef p q lam).im = 0 := by
  have h : chamCoef p q lam = (((2 * (-lam) ^ q * (-1) ^ (p * ((q : ℤ) - 1)) : ℝ)) : ℂ) := by
    simp only [chamCoef]
    push_cast
    ring
  rw [h, Complex.ofReal_im]

/-- The fibre rotation number fails to be integral exactly where the trace of the `q`-step
transfer matrix is `< 2`; in terms of the (real) discriminant this reads
`|Δ.re + chamCoef.re * cos (2πqx)| < 2`. -/
theorem rotQ_norm_lt_iff (p : ℤ) (q : ℕ) (lam x E : ℝ) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) :
    (rotQ p q lam E x ∉ Set.range (fun k : ℤ => (k : ℝ)) ↔
      |((disc p q lam).eval (E : ℂ)).re
        + (chamCoef p q lam).re * Real.cos (2 * Real.pi * (q : ℝ) * x)| < 2) := by
  have h1 : (∃ k : ℤ, rotQ p q lam E x = (k : ℝ)) ↔
      2 ≤ |(Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q x).trace| :=
    rotQ_int_iff_trace p q lam E x hq
  rw [← abs_trAq_eq_trace_iterR p q lam E x] at h1
  have hch := chambers p q lam (E : ℂ) hpq hq x
  have him := disc_im_eq_zero p q lam E
  have hcim := chamCoef_im p q lam
  have htr : trAq p q lam (E : ℂ) x
      = ((((disc p q lam).eval (E : ℂ)).re
          + (chamCoef p q lam).re * Real.cos (2 * Real.pi * (q : ℝ) * x) : ℝ) : ℂ) := by
    have h1' : (disc p q lam).eval (E : ℂ) = ((((disc p q lam).eval (E : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simp [him])
    have h2' : chamCoef p q lam = ((((chamCoef p q lam).re : ℝ)) : ℂ) :=
      Complex.ext rfl (by simp [hcim])
    rw [hch, h1', h2']
    push_cast
    simp only [Complex.ofReal_re, Complex.ofReal_cos]
  have hnorm : ‖trAq p q lam (E : ℂ) x‖
      = |((disc p q lam).eval (E : ℂ)).re
          + (chamCoef p q lam).re * Real.cos (2 * Real.pi * (q : ℝ) * x)| := by
    rw [htr, Complex.norm_real, Real.norm_eq_abs]
  have hrange : (rotQ p q lam E x ∉ Set.range (fun k : ℤ => (k : ℝ)))
      ↔ ¬ (∃ k : ℤ, rotQ p q lam E x = (k : ℝ)) := by
    rw [Set.mem_range]
    constructor
    · intro h ⟨k, hk⟩; exact h ⟨k, hk.symm⟩
    · intro h ⟨k, hk⟩; exact h ⟨k, hk.symm⟩
  have h2 : (rotQ p q lam E x ∉ Set.range (fun k : ℤ => (k : ℝ)))
      ↔ ¬ (2 ≤ ‖trAq p q lam (E : ℂ) x‖) := by
    rw [hrange]
    constructor
    · intro h h3; exact h (h1.mpr h3)
    · intro h h3; exact h (h1.mp h3)
  rw [h2, hnorm]
  constructor
  · intro h; exact not_le.mp h
  · intro h; exact not_le.mpr h

/-- **The band structure at a fixed phase.**  Inside the union spectrum the set where the
fibre rotation number fails to be integral is a union of at most two intervals: at most one
interval per monotone piece of the discriminant, and there are at most two of those (the
discriminant is strictly monotone off the single critical point `0`, which occurs only for
even `q`). -/
theorem rotQ_nonInt_twoIntervals (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (a b : ℝ) (hab : a ≤ b)
    (hkey : ∀ E ∈ Set.Ioo a b, ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q)
    (x : ℝ) :
    ∃ u v w z : ℝ, ∀ E : ℝ, E ∈ Set.Ioo a b →
      (rotQ p q lam E x ∉ Set.range (fun k : ℤ => (k : ℝ)) ↔
        (E ∈ Set.Ioo u v ∨ E ∈ Set.Ioo w z)) := by
  set Δr : ℝ → ℝ := fun E => ((disc p q lam).eval (E : ℂ)).re with hΔr
  set cc : ℝ := (chamCoef p q lam).re * Real.cos (2 * Real.pi * (q : ℝ) * x) with hcc
  have hcont : Continuous Δr := by
    rw [hΔr]
    exact Complex.continuous_re.comp
      ((Polynomial.continuous (disc p q lam)).comp Complex.continuous_ofReal)
  have hiff : ∀ E ∈ Set.Ioo a b,
      (rotQ p q lam E x ∉ Set.range (fun k : ℤ => (k : ℝ)) ↔
        Δr E ∈ Set.Ioo (-2 - cc) (2 - cc)) := by
    intro E hE
    rw [rotQ_norm_lt_iff p q lam x E hq hpq]
    rw [hΔr, hcc]
    constructor
    · intro h; rw [abs_lt] at h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h; rw [abs_lt]; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have piece : ∀ s t : ℝ, (StrictMonoOn Δr (Set.Ioo s t) ∨ StrictAntiOn Δr (Set.Ioo s t)) →
      ∃ u v : ℝ, {E : ℝ | E ∈ Set.Ioo s t ∧ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc)}
        = Set.Ioo u v := by
    intro s t hm
    rcases hm with hm | hm
    · exact preimage_Ioo_inter_eq_Ioo Δr hcont s t (-2 - cc) (2 - cc) hm
    · have hmono' : StrictMonoOn (fun E : ℝ => -Δr E) (Set.Ioo s t) := by
        intro E hE E' hE' hlt
        simp only [neg_lt_neg_iff]
        exact hm hE hE' hlt
      obtain ⟨u, v, huv⟩ := preimage_Ioo_inter_eq_Ioo (fun E : ℝ => -(Δr E)) hcont.neg s t
        (-(2 - cc)) (-(-2 - cc)) hmono'
      refine ⟨u, v, ?_⟩
      have hset : {E : ℝ | E ∈ Set.Ioo s t ∧ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc)}
          = {E : ℝ | E ∈ Set.Ioo s t ∧ -(Δr E) ∈ Set.Ioo (-(2 - cc)) (-(-2 - cc))} := by
        ext E
        constructor
        · intro h
          simp only [Set.mem_setOf_eq] at h ⊢
          refine ⟨h.1, ?_⟩
          rw [Set.mem_Ioo] at h ⊢
          exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩
        · intro h
          simp only [Set.mem_setOf_eq] at h ⊢
          refine ⟨h.1, ?_⟩
          rw [Set.mem_Ioo] at h ⊢
          exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩
      rw [hset, huv]
  by_cases hsplit : Even q ∧ (0 : ℝ) ∈ Set.Ioo a b
  · obtain ⟨hEven, h0⟩ := hsplit
    obtain ⟨m, hm⟩ : ∃ m : ℕ, q = 2 * m + 2 := by
      obtain ⟨k, hk⟩ := hEven
      exact ⟨k - 1, by omega⟩
    have hm1 := discRe_strictMonoOn_or_strictAntiOn p q lam hlam hq hpq a 0
      (fun _ _ hE => ne_of_lt hE.2)
      (fun E hE => hkey E ⟨hE.1, lt_trans hE.2 h0.2⟩)
    have hm2 := discRe_strictMonoOn_or_strictAntiOn p q lam hlam hq hpq 0 b
      (fun _ _ hE => ne_of_gt hE.1)
      (fun E hE => hkey E ⟨lt_trans h0.1 hE.1, hE.2⟩)
    obtain ⟨u1, v1, hv1⟩ := piece a 0 hm1
    obtain ⟨u2, v2, hv2⟩ := piece 0 b hm2
    have hsub1 : Set.Ioo u1 v1 ⊆ Set.Ioo a 0 := by
      intro E hE; rw [← hv1] at hE; exact hE.1
    have hsub2 : Set.Ioo u2 v2 ⊆ Set.Ioo 0 b := by
      intro E hE; rw [← hv2] at hE; exact hE.1
    refine ⟨u1, v1, u2, v2, ?_⟩
    intro E hE
    rw [hiff E hE]
    rcases lt_trichotomy E 0 with hlt | heq | hgt
    · have hE1 : E ∈ Set.Ioo a 0 := ⟨hE.1, hlt⟩
      have hnot2 : E ∉ Set.Ioo u2 v2 := fun h => absurd (hsub2 h).1 (not_lt.mpr (le_of_lt hlt))
      have key : (E ∈ Set.Ioo u1 v1) ↔ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc) := by
        rw [← hv1]
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨hE1, h⟩⟩
      simp only [key, hnot2, or_false]
    · subst heq
      have hR : ¬ ((0 : ℝ) ∈ Set.Ioo u1 v1 ∨ (0 : ℝ) ∈ Set.Ioo u2 v2) := by
        rintro (h | h)
        · exact absurd (hsub1 h).2 (lt_irrefl 0)
        · exact absurd (hsub2 h).1 (lt_irrefl 0)
      have hP : ¬ (Δr 0 ∈ Set.Ioo (-2 - cc) (2 - cc)) := by
        intro hcon
        have hd0 : |Δr 0| = 2 + 2 * lam ^ q := by
          have him : ((disc p q lam).eval ((0 : ℝ) : ℂ)).im = 0 := disc_im_eq_zero p q lam 0
          have hz : (disc p q lam).eval ((0 : ℝ) : ℂ)
              = ((((disc p q lam).eval ((0 : ℝ) : ℂ)).re : ℝ) : ℂ) :=
            Complex.ext rfl (by simpa using him)
          have h0c : (0 : ℂ) = ((0 : ℝ) : ℂ) := by simp
          have h2' := disc_zero_abs p q m lam hm hpq hlam
          rw [h0c, hz, Complex.norm_real, Real.norm_eq_abs] at h2'
          simpa [hΔr] using h2'
        have hcc' : |cc| ≤ 2 * lam ^ q := by
          rw [hcc]
          have h1' : |(chamCoef p q lam).re * Real.cos (2 * Real.pi * (q : ℝ) * x)|
              ≤ |(chamCoef p q lam).re| := by
            rw [abs_mul]
            calc |(chamCoef p q lam).re| * |Real.cos (2 * Real.pi * (q : ℝ) * x)|
                ≤ |(chamCoef p q lam).re| * 1 :=
                  mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
              _ = |(chamCoef p q lam).re| := mul_one _
          have h2'' : |(chamCoef p q lam).re| ≤ ‖chamCoef p q lam‖ := Complex.abs_re_le_norm _
          rw [chamCoef_norm p q lam hlam] at h2''
          linarith
        have htri : |Δr 0| - |cc| ≤ |Δr 0 + cc| := by
          have h2' : |Δr 0| ≤ |Δr 0 + cc| + |cc| := by
            calc |Δr 0| = |(Δr 0 + cc) - cc| := by ring_nf
              _ ≤ |Δr 0 + cc| + |cc| := abs_sub _ _
          linarith
        have hge : 2 ≤ |Δr 0 + cc| := by
          rw [hd0] at htri
          linarith
        have h4 : |Δr 0 + cc| < 2 := by
          rw [Set.mem_Ioo] at hcon
          rw [abs_lt]
          exact ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
        linarith [h4, hge]
      simp only [hR, hP]
    · have hE1 : E ∈ Set.Ioo 0 b := ⟨hgt, hE.2⟩
      have hnot1 : E ∉ Set.Ioo u1 v1 := fun h => absurd (hsub1 h).2 (not_lt.mpr (le_of_lt hgt))
      have key : (E ∈ Set.Ioo u2 v2) ↔ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc) := by
        rw [← hv2]
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨hE1, h⟩⟩
      simp only [hnot1, false_or, key]
  · have hsingle : ∃ u v : ℝ, {E : ℝ | E ∈ Set.Ioo a b ∧ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc)}
        = Set.Ioo u v := by
      refine piece a b ?_
      refine discRe_strictMonoOn_or_strictAntiOn p q lam hlam hq hpq a b ?_ hkey
      intro hEven E hE
      by_contra hE0
      exact hsplit ⟨hEven, by simpa [hE0] using hE⟩
    obtain ⟨u, v, huv⟩ := hsingle
    refine ⟨u, v, u, v, ?_⟩
    intro E hE
    rw [hiff E hE]
    have key : (E ∈ Set.Ioo u v) ↔ Δr E ∈ Set.Ioo (-2 - cc) (2 - cc) := by
      rw [← huv]
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨hE, h⟩⟩
    simp only [key, or_self]

/-! ## Assembly -/

/-- **The band set.**  If every point of `(a,b)` belongs to the union spectrum of the
rational approximant, then `|Δ| ≤ 2 + 2λ^q` there. -/
theorem disc_bound_of_trace (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (a b : ℝ)
    (H : ∀ E ∈ Ioo a b, ∃ θ : ℝ, ‖trAq p q lam (E : ℂ) θ‖ ≤ 2) :
    ∀ E ∈ Ioo a b, ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q := by
  intro E hE
  obtain ⟨θ, hθ⟩ := H E hE
  have hch := chambers p q lam (E : ℂ) hpq hq θ
  have hcn := chamCoef_norm p q lam hlam
  have hcos : ‖((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hsub : ‖(disc p q lam).eval (E : ℂ)‖
      ≤ ‖trAq p q lam (E : ℂ) θ‖
        + ‖chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖ := by
    have h1 : (disc p q lam).eval (E : ℂ)
        = trAq p q lam (E : ℂ) θ
          - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ) := by
      rw [hch]; ring
    rw [h1]
    exact norm_sub_le (trAq p q lam (E : ℂ) θ)
      (chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ))
  calc ‖(disc p q lam).eval (E : ℂ)‖
      ≤ ‖trAq p q lam (E : ℂ) θ‖
        + ‖chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖ := hsub
    _ = ‖trAq p q lam (E : ℂ) θ‖ + ‖chamCoef p q lam‖
          * ‖((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)‖ := by rw [norm_mul]
    _ ≤ 2 + 2 * lam ^ q := by
        have := mul_le_mul hcn.le hcos (norm_nonneg _) (by positivity)
        linarith

/-- **The pointwise drop bound.**  For each phase `x` the `q`-step rotation number drops by
at most `2` across an interval contained in the union spectrum. -/
theorem rotQ_drop_le_two (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (a b : ℝ) (hab : a ≤ b)
    (hkey : ∀ E ∈ Ioo a b, ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q) (x : ℝ) :
    rotQ p q lam a x - rotQ p q lam b x ≤ 2 := by
  obtain ⟨u, v, w, z, huvwz⟩ := rotQ_nonInt_twoIntervals p q lam hlam hq hpq a b hab hkey x
  exact drop_le_two_of_union (fun E => rotQ p q lam E x) (rotQ_continuous p q lam x hq)
    (rotQ_antitone p q lam x hq) a b u v w z hab huvwz

/-- **14c for a reduced fraction.** -/
theorem ratIdsVariation_coprime (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (a b : ℝ) (hab : a ≤ b)
    (H : ∀ E ∈ Ioo a b, ∃ θ : ℝ, ‖trAq p q lam (E : ℂ) θ‖ ≤ 2) :
    ids ((p : ℝ) / (q : ℝ)) lam b - ids ((p : ℝ) / (q : ℝ)) lam a ≤ 2 / ((q : ℕ) : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hkey := disc_bound_of_trace p q lam hlam hq hpq a b H
  have hdrop : ∀ x : ℝ, rotQ p q lam a x - rotQ p q lam b x ≤ 2 :=
    fun x => rotQ_drop_le_two p q lam hlam hq hpq a b hab hkey x
  have hint_a : IntervalIntegrable (fun x : ℝ => rotQ p q lam a x) volume 0 1 :=
    (rotQ_continuous_x p q lam a hq).intervalIntegrable 0 1
  have hint_b : IntervalIntegrable (fun x : ℝ => rotQ p q lam b x) volume 0 1 :=
    (rotQ_continuous_x p q lam b hq).intervalIntegrable 0 1
  have hInt : (∫ x in (0 : ℝ)..1, rotQ p q lam a x)
      - (∫ x in (0 : ℝ)..1, rotQ p q lam b x) ≤ 2 := by
    rw [← intervalIntegral.integral_sub hint_a hint_b]
    have h1 : (∫ x in (0 : ℝ)..1, (rotQ p q lam a x - rotQ p q lam b x))
        ≤ ∫ x in (0 : ℝ)..1, (2 : ℝ) :=
      intervalIntegral.integral_mono_on (by norm_num) (hint_a.sub hint_b)
        intervalIntegrable_const (fun x _ => hdrop x)
    simpa using h1
  have hids : ids ((p : ℝ) / (q : ℝ)) lam b - ids ((p : ℝ) / (q : ℝ)) lam a
      = (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1, rotQ p q lam a x)
        - (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1, rotQ p q lam b x) := by
    simp only [ids]
    rw [rotLift_bridge', rotLift_bridge',
      rotLift_eq_rotQ p q lam a hq, rotLift_eq_rotQ p q lam b hq]
    ring
  rw [hids]
  have hstep : (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1, rotQ p q lam a x)
      - (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1, rotQ p q lam b x)
      = (1 / (q : ℝ)) * ((∫ x in (0 : ℝ)..1, rotQ p q lam a x)
        - (∫ x in (0 : ℝ)..1, rotQ p q lam b x)) := by ring
  rw [hstep]
  have := mul_le_mul_of_nonneg_left hInt (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))
  have h2 : (1 / (q : ℝ)) * 2 = 2 / (q : ℝ) := by ring
  linarith [this, h2]

/-- **14c**: `RatIdsVariation`. -/
theorem ratIdsVariation : Work.TMC14Core.RatIdsVariation := by
  intro p q lam hlam hq a b hab H
  obtain ⟨p', q', hq'1, hcop, hq'eq, hfreq, H'⟩ := hyps_reduce p q lam hlam hq a b H
  have hmain := ratIdsVariation_coprime p' q' lam hlam hq'1 hcop a b hab H'
  have hfreq2 : (p' : ℝ) / (q' : ℝ) = (p : ℝ) / (q : ℝ) := hfreq
  rw [hfreq2] at hmain
  have hq'eq' : (2 : ℝ) / ((q' : ℕ) : ℝ) = 2 / ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) := by
    rw [hq'eq]
  rw [hq'eq'] at hmain
  exact hmain

end Work.TMC14Core
