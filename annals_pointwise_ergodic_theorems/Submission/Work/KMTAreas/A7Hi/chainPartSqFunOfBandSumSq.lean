import Mathlib
import Submission.Work.KMTAreas.A7Hi.bandSumSqRep
import Submission.Work.KMTAreas.A7Hi.eLpNorm_chainPart_le_uniform
import Submission.Work.KMTAreas.A7.fiberOpCum_lp_goodArcs
import Submission.Work.KMTPlan.A6.FkrStep
import Submission.Work.KMTPlan.A6.fkrW_zero_varPart
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary reductions -/

/-- **Telescoping**: the partial sum of the increments over the initial segment `[0,K)` is the
difference `T_K - T_0` of the two ends of the walk. -/
theorem partSum_range (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (K : ℕ) :
    partSum ρ l m₀ (Finset.range K) f
      = fun x : ℤ => lpf ρ l m₀ K f x - lpf ρ l m₀ 0 f x := by
  funext x
  rw [partSum]
  simp only [dInc]
  exact Finset.sum_range_sub (fun i : ℕ => lpf ρ l m₀ i f x) K

/-- The restricted square function `partSq` of a finite set of scales is dominated by the full band
square function `sqFun`. -/
theorem partSq_le_sqFun (ρ : ℝ) (l m₀ : ℕ) (I : Finset ℕ) (f : ℤ → ℂ) (x : ℤ) :
    partSq ρ l m₀ I f x ≤ sqFun ρ l m₀ f x := by
  rw [sqFun_eq_tsum_dInc, partSq]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  exact ENNReal.sum_le_tsum (f := fun i => ‖dInc ρ l m₀ i f x‖ₑ ^ (2 : ℝ)) I

/-- A summable family of nonnegative terms dominates each of its terms. -/
theorem norm_le_of_summable {q : ℝ} (hq : 0 < q) {f : ℤ → ℂ}
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ q)) (y : ℤ) :
    ‖f y‖ ≤ (∑' n : ℤ, ‖f n‖ ^ q) ^ (1 / q) := by
  have h1 : ‖f y‖ ^ q ≤ ∑' n : ℤ, ‖f n‖ ^ q :=
    hf.le_tsum y (fun j _ => by positivity)
  have h2 : ((‖f y‖ ^ q) ^ (1 / q)) = ‖f y‖ := by
    rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hq.ne']
  rw [← h2]
  exact Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-! ## The defect comparison of chain parts -/

/-- A vector with at most one nonzero entry, each of modulus `≤ α`, has `ℓ^r`-norm `≤ α`
(`1 ≤ r`). -/
private lemma ofReal_norm_toLp_le_of_support {r : NNReal} (hr : 1 ≤ r) {J : ℕ} {d : Fin J → ℂ}
    {α : ℝ≥0∞} (hcard : (Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card ≤ 1)
    (hbound : ∀ i : Fin J, ‖d i‖ₑ ≤ α) :
    ENNReal.ofReal ‖WithLp.toLp r d‖ ≤ α := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr d]
  set c : ℝ≥0∞ := (((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) : ℝ≥0∞) with hc
  have hsum : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ)) ≤ c * α ^ (r : ℝ) := by
    have hsplit : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))
        = ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : d i ≠ 0
      · rw [if_pos hi]
      · rw [if_neg hi]
        rw [show d i = 0 from by simpa using hi]
        simp [ENNReal.zero_rpow_of_pos hr0]
    rw [hsplit, hc]
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ)
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), α ^ (r : ℝ) :=
          Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (hbound i) hr0.le)
      _ = ((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) * α ^ (r : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc1 : c ≤ 1 := by
    rw [hc]
    exact_mod_cast hcard
  calc (((∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))) ^ (1 / (r : ℝ)))
      ≤ (c * α ^ (r : ℝ)) ^ (1 / (r : ℝ)) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = c ^ (1 / (r : ℝ)) * (α ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = c ^ (1 / (r : ℝ)) * α := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hr0.ne', ENNReal.rpow_one]
    _ ≤ 1 ^ (1 / (r : ℝ)) * α :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hc1 (by positivity)) bot_le
    _ = α := by rw [ENNReal.one_rpow, one_mul]

/-- **The defect comparison.**  If two sequences agree from index `1` on, their chain parts differ
by at most the modulus of the difference of the initial terms. -/
theorem chainPart_le_chainPart_add_defect {r : NNReal} (hr : 1 ≤ r) (u v : ℕ → ℂ)
    (hv : ∀ m : ℕ, 1 ≤ m → u m = v m) :
    chainPart r u ≤ chainPart r v + ‖u 0 - v 0‖ₑ := by
  classical
  set w : ℂ := u 0 - v 0 with hw
  have hwapply : ∀ m : ℕ, (u - v) m = if m = 0 then w else 0 := by
    intro m
    rcases eq_or_ne m 0 with h | h
    · subst h; simp [hw]
    · rw [if_neg h, Pi.sub_apply, hv m (by omega), sub_self]
  unfold chainPart
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  set vj : Fin J → ℂ := fun i => v (N (i + 1)) - v (N i) with hvj
  set dj : Fin J → ℂ := fun i => (u - v) (N (i + 1)) - (u - v) (N i) with hdj
  have hkey : ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => u (N (i + 1)) - u (N i))‖
      ≤ ENNReal.ofReal ‖WithLp.toLp r vj‖ + ‖w‖ₑ := by
    have hdecomp : (fun i : Fin J => u (N (i + 1)) - u (N i)) = vj + dj := by
      funext i
      simp only [hvj, hdj, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hdecomp]
    haveI : Fact (1 ≤ (r : ENNReal)) := ⟨by exact_mod_cast hr⟩
    have hadd : ENNReal.ofReal ‖WithLp.toLp r (vj + dj)‖
        ≤ ENNReal.ofReal ‖WithLp.toLp r vj‖ + ENNReal.ofReal ‖WithLp.toLp r dj‖ := by
      have h1 : WithLp.toLp r (vj + dj) = WithLp.toLp r vj + WithLp.toLp r dj := rfl
      calc ENNReal.ofReal ‖WithLp.toLp r (vj + dj)‖
          = ENNReal.ofReal ‖WithLp.toLp r vj + WithLp.toLp r dj‖ := by rw [h1]
        _ ≤ ENNReal.ofReal (‖WithLp.toLp r vj‖ + ‖WithLp.toLp r dj‖) :=
            ENNReal.ofReal_le_ofReal (norm_add_le _ _)
        _ = ENNReal.ofReal ‖WithLp.toLp r vj‖ + ENNReal.ofReal ‖WithLp.toLp r dj‖ :=
            ENNReal.ofReal_add (norm_nonneg (WithLp.toLp r vj)) (norm_nonneg (WithLp.toLp r dj))
    have hbound : ∀ i : Fin J, ‖dj i‖ₑ ≤ ‖w‖ₑ := by
      intro i
      have h1 : (u - v) (N (i + 1)) = if N (i + 1) = 0 then w else 0 := hwapply _
      have h2 : (u - v) (N i) = if N i = 0 then w else 0 := hwapply _
      simp only [hdj, h1, h2]
      split_ifs <;> simp
    have huniq : ∀ i j : Fin J, dj i ≠ 0 → dj j ≠ 0 → i = j := by
      intro i j hi hj
      by_contra hij
      rcases eq_or_ne w 0 with hw0 | hw0
      · exfalso
        have hz : dj i = 0 := by rw [hdj]; simp [hwapply, hw0]
        exact hi hz
      have key : ∀ k : Fin J, dj k ≠ 0 → N k = 0 ∧ N (k + 1) ≠ 0 := by
        intro k hk
        have h1 : (u - v) (N (k + 1)) = if N (k + 1) = 0 then w else 0 := hwapply _
        have h2 : (u - v) (N k) = if N k = 0 then w else 0 := hwapply _
        rw [hdj] at hk
        simp only [h1, h2] at hk
        by_cases hk0 : N k = 0
        · refine ⟨hk0, ?_⟩
          intro hk1
          rw [if_pos hk1, if_pos hk0, sub_self] at hk
          exact hk rfl
        · exfalso
          have hk1 : N (k + 1) = 0 := by
            by_contra h
            rw [if_neg h, if_neg hk0, sub_zero] at hk
            exact hk rfl
          have hmono : N k ≤ N (k + 1) := hN (by omega)
          omega
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have h1 := (key i hi).2
        have h2 := (key j hj).1
        have h3 : N (i + 1) ≤ N j := hN (by omega)
        omega
      · have h1 := (key j hj).2
        have h2 := (key i hi).1
        have h3 : N (j + 1) ≤ N i := hN (by omega)
        omega
    have hcard : (Finset.univ.filter (fun i : Fin J => dj i ≠ 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact huniq a b (by simpa using ha) (by simpa using hb)
    exact hadd.trans (add_le_add le_rfl (ofReal_norm_toLp_le_of_support hr hcard hbound))
  refine hkey.trans (add_le_add ?_ le_rfl)
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))


/-! ## The uniform `ℓ¹`-kernel bound and the uniform `ℓᵖ` bound of the low-pass operators -/

/-- `eLpNorm` on the counting measure of `ℤ` is invariant under translations. -/
theorem eLpNorm_comp_addRight {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (G : ℤ → ℝ≥0∞) (c : ℤ) :
    MeasureTheory.eLpNorm (fun x : ℤ => G (x + c)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm G p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop]
  congr 1
  rw [← tsum_eq_lintegral_count (fun x : ℤ => ‖G (x + c)‖ₑ ^ p.toReal),
    ← tsum_eq_lintegral_count (fun x : ℤ => ‖G x‖ₑ ^ p.toReal)]
  exact Equiv.tsum_eq (Equiv.addRight c) (fun y : ℤ => ‖G y‖ₑ ^ p.toReal)

/-- **The tail of a summable `ℝ≥0∞`-valued family on `ℤ`** tends to zero. -/
theorem tendsto_tsum_sub_sum_Icc {u : ℤ → ℝ≥0∞} (hu : (∑' n : ℤ, u n) < ⊤) :
    Filter.Tendsto (fun N : ℕ => (∑' n : ℤ, u n)
        - ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i) Filter.atTop (nhds 0) := by
  have hmono : Monotone (fun N : ℕ => ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i) := by
    intro N N' hNN'
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => bot_le)
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have hsup : (⨆ N : ℕ, ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i)
      = ∑' n : ℤ, u n := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_antisymm (iSup_le fun N => ?_) (iSup_le fun s => ?_)
    · exact le_iSup (fun s : Finset ℤ => ∑ i ∈ s, u i) (Finset.Icc (-(((N : ℕ)) : ℤ)) ((N : ℕ) : ℤ))
    · obtain ⟨N, hN⟩ := exists_nat_ge (s.sup (fun i => i.natAbs))
      refine le_iSup_of_le N (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => bot_le))
      intro i hi
      simp only [Finset.mem_Icc]
      have hi' : ((i.natAbs : ℕ) : ℤ) ≤ ((s.sup (fun i => i.natAbs) : ℕ) : ℤ) := by
        exact_mod_cast (Finset.le_sup (f := fun i => i.natAbs) hi)
      have h3 : |(i : ℤ)| ≤ (((N : ℕ)) : ℤ) := by
        rw [show |(i : ℤ)| = ((i.natAbs : ℕ) : ℤ) by simp]
        exact hi'.trans (by exact_mod_cast hN)
      rw [abs_le] at h3
      omega
  have h1 : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i)
      Filter.atTop (nhds (∑' n : ℤ, u n)) := by
    rw [← hsup]
    exact tendsto_atTop_iSup hmono
  have h2 : Filter.Tendsto (fun N : ℕ => (∑' n : ℤ, u n)
      - ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i) Filter.atTop
      (nhds ((∑' n : ℤ, u n) - (∑' n : ℤ, u n))) :=
    ENNReal.Tendsto.sub (f := Filter.atTop)
      (ma := fun _ : ℕ => (∑' n : ℤ, u n))
      (mb := fun N : ℕ => ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), u i)
      (a := ∑' n : ℤ, u n) (b := ∑' n : ℤ, u n) tendsto_const_nhds h1 (Or.inl hu.ne)
  simpa using h2

/-- **The `ℓᵖ` norm of the tail of `f` on the complement of an interval is a tail of the `ℓᵖ`
sum** (for a finite total mass). -/
theorem eLpNorm_Icc_compl_eq {p : ENNReal} (hp : 1 ≤ p) (hptop : p < ⊤) (f : ℤ → ℂ)
    (htot : (∑' n : ℤ, ‖f n‖ₑ ^ p.toReal) < ⊤) (N : ℕ) :
    MeasureTheory.eLpNorm (fun n : ℤ => if n ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ)
        then (0 : ℂ) else f n) p MeasureTheory.Measure.count
      = ((∑' n : ℤ, ‖f n‖ₑ ^ p.toReal)
          - ∑ i ∈ Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ), ‖f i‖ₑ ^ p.toReal)
        ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hp)
  have hq : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 (ne_of_lt hptop)
  set s : Finset ℤ := Finset.Icc (-(((N : ℕ)) : ℤ)) (((N : ℕ)) : ℤ) with hs
  set u : ℤ → ℝ≥0∞ := fun n => ‖f n‖ₑ ^ p.toReal with hu
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 (ne_of_lt hptop)]
  have hpt : ∀ n : ℤ, ‖(if n ∈ s then (0 : ℂ) else f n)‖ₑ ^ p.toReal
      = (if n ∈ s then 0 else u n) := by
    intro n
    by_cases hn : n ∈ s
    · rw [if_pos hn, if_pos hn]; simp [ENNReal.zero_rpow_of_pos hq]
    · rw [if_neg hn, if_neg hn, hu]
  rw [lintegral_congr hpt, ← tsum_eq_lintegral_count (fun n : ℤ => if n ∈ s then 0 else u n)]
  have hind : (∑' n : ℤ, (if n ∈ s then 0 else u n))
      = ∑' n : ℤ, ((s : Set ℤ)ᶜ).indicator u n := by
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ (s : Set ℤ)
    · rw [Set.indicator_of_notMem (by simpa using hn), if_pos (by simpa using hn)]
    · rw [Set.indicator_of_mem (by simpa using hn), if_neg (by simpa using hn)]
  rw [hind, ← tsum_subtype ((s : Set ℤ)ᶜ) u]
  have hfin : (∑ i ∈ s, u i) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ne_of_lt htot) ?_
    rw [hu]
    exact ENNReal.sum_le_tsum s
  rw [← ENNReal.sum_add_tsum_compl s u, ENNReal.add_sub_cancel_left hfin]

/-- Finiteness of the `ℝ≥0∞`-sum of the values of an `ℓᵖ` function. -/
theorem tsum_enorm_rpow_lt_top_of_eLpNorm_lt_top {p : ENNReal} {f : ℤ → ℂ} (hp0 : p ≠ 0) (hptop : p < ⊤)
    (hf : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count < ⊤) :
    (∑' n : ℤ, ‖f n‖ₑ ^ p.toReal) < ⊤ := by
  have h1 : (∫⁻ n : ℤ, ‖f n‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count) < ⊤ :=
    (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) hp0 (ne_of_lt hptop)).mp hf
  rwa [← Work.KMTAreas.A7Hi.tsum_eq_lintegral_count
    (u := fun n : ℤ => ‖f n‖ₑ ^ p.toReal)] at h1

/-- `ℓᵖ` summability of the values, from a finite `eLpNorm`. -/
theorem summable_of_eLpNorm_ne_top {p : ENNReal} {u : ℤ → ℂ} (hp0 : p ≠ 0) (hptop : p < ⊤)
    (hu : MeasureTheory.eLpNorm u p MeasureTheory.Measure.count < ⊤) :
    Summable (fun n : ℤ => ‖u n‖ ^ p.toReal) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_of_lt hptop)
  have hT : (∑' n : ℤ, ‖u n‖ₑ ^ p.toReal) < ⊤ := tsum_enorm_rpow_lt_top_of_eLpNorm_lt_top hp0 hptop hu
  have h3 : (∑' n : ℤ, ENNReal.ofReal (‖u n‖ ^ p.toReal)) < ⊤ :=
    (tsum_congr (fun n => (Work.KMTAreas.A7Hi2.enorm_rpow_eq_ofReal (u n) p.toReal hq.le).symm)).trans_lt hT
  have h4 : (∑' n : ℤ, ((Real.toNNReal (‖u n‖ ^ p.toReal) : ℝ≥0) : ℝ≥0∞)) < ⊤ := by
    simpa only [ENNReal.ofReal] using h3
  have h5 : Summable (fun n : ℤ => Real.toNNReal (‖u n‖ ^ p.toReal)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h4.ne
  have h6 : Summable (fun n : ℤ => (((Real.toNNReal (‖u n‖ ^ p.toReal)) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h5
  have h7 : (fun n : ℤ => (((Real.toNNReal (‖u n‖ ^ p.toReal)) : ℝ≥0) : ℝ))
      = fun n : ℤ => ‖u n‖ ^ p.toReal := by
    funext n
    exact Real.coe_toNNReal _ (by positivity)
  rwa [h7] at h6

/-- A finite bound on the values of an `ℓᵖ` function. -/
theorem exists_norm_bound_of_memLp {p : ENNReal} {f : ℤ → ℂ} (hp0 : p ≠ 0) (hptop : p < ⊤)
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℤ, ‖f x‖ ≤ B := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_of_lt hptop)
  set T : ENNReal := ∑' n : ℤ, ‖f n‖ₑ ^ p.toReal with hTdef
  have hT : T < ⊤ := tsum_enorm_rpow_lt_top_of_eLpNorm_lt_top hp0 hptop hf.eLpNorm_lt_top
  refine ⟨T.toReal ^ (1 / p.toReal) + 1, by positivity, fun x => ?_⟩
  have h1 : ENNReal.ofReal (‖f x‖ ^ p.toReal) ≤ T := by
    rw [← Work.KMTAreas.A7Hi2.enorm_rpow_eq_ofReal (f x) p.toReal hq.le]
    exact ENNReal.le_tsum (f := fun n : ℤ => ‖f n‖ₑ ^ p.toReal) x
  have h2 : ‖f x‖ ^ p.toReal ≤ T.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hT)).mp h1
  have h3 : ‖f x‖ = (‖f x‖ ^ p.toReal) ^ (1 / p.toReal) := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hq.ne', Real.rpow_one]
  rw [h3]
  exact (Real.rpow_le_rpow (by positivity) h2 (by positivity)).trans
    (le_add_of_nonneg_right zero_le_one)

end

end Work.KMTAreas.A7Hi
