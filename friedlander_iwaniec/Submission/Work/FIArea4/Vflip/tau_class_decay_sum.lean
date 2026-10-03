import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip

open Finset

noncomputable section

/-! ## Reindexing a residue class as an arithmetic progression -/

/-- The integers congruent to `n` modulo `q` are exactly `n + m * q`, `m : ℤ`. -/
private def residueEquivZ (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ℤ ≃ {k : ℤ // (k : ZMod q) = (n : ZMod q)} where
  toFun m := ⟨n + m * (q : ℤ), by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero]⟩
  invFun k := (k.1 - n) / (q : ℤ)
  left_inv m := by
    have hq0 : (q : ℤ) ≠ 0 := by omega
    show (n + m * (q : ℤ) - n) / (q : ℤ) = m
    rw [add_sub_cancel_left]
    exact Int.mul_ediv_cancel m hq0
  right_inv k := by
    apply Subtype.ext
    show n + (k.1 - n) / (q : ℤ) * (q : ℤ) = k.1
    have hdvd : (q : ℤ) ∣ k.1 - n := by
      have h : (((k.1 - n) : ℤ) : ZMod q) = 0 := by
        rw [Int.cast_sub, k.2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h
    rw [Int.ediv_mul_cancel hdvd, add_sub_cancel]

private lemma tsum_class_eq_progression (q : ℕ) (hq : 1 ≤ q) (n : ℤ) (g : ℤ → ℝ) :
    (∑' k : ℤ, (if (k : ZMod q) = (n : ZMod q) then g k else 0))
      = ∑' m : ℤ, g (n + m * (q : ℤ)) := by
  have hfun : ∀ k : ℤ, (if (k : ZMod q) = (n : ZMod q) then g k else 0)
      = Set.indicator {k : ℤ | (k : ZMod q) = (n : ZMod q)} g k := by
    intro k
    by_cases hk : (k : ZMod q) = (n : ZMod q)
    · rw [if_pos hk, Set.indicator_of_mem (show k ∈ {k : ℤ | (k:ZMod q) = (n:ZMod q)} from hk)]
    · rw [if_neg hk, Set.indicator_of_notMem (show k ∉ {k : ℤ | (k:ZMod q) = (n:ZMod q)} from hk)]
  rw [tsum_congr hfun, ← _root_.tsum_subtype]
  exact (Equiv.tsum_eq (residueEquivZ q hq n)
    (fun k : {k : ℤ // (k : ZMod q) = (n : ZMod q)} => g k.1)).symm

/-! ## Elementary `rpow` estimates -/

private lemma natAbs_cast_abs (k : ℤ) : (k.natAbs : ℝ) = |(k:ℝ)| := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp

/-- A form of Bernoulli's inequality for a negative exponent. -/
private lemma one_sub_rpow_neg_ge (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : 1 + β * u ≤ (1 - u) ^ (-β) := by
  have h1u : 0 ≤ 1 - u := by linarith
  have hposu : 0 < 1 - u := by linarith
  have hpos : 0 < (1 - u) ^ β := Real.rpow_pos_of_pos hposu β
  have hbern : (1 - u) ^ β ≤ 1 - β * u := by
    have := rpow_one_add_le_one_add_mul_self (show (-1:ℝ) ≤ -(u) by linarith) hβ0.le hβ1
    simpa [sub_eq_add_neg, mul_neg] using this
  have hmul : (1 - u) ^ β * (1 + β*u) ≤ 1 := by
    calc (1-u)^β * (1+β*u) ≤ (1 - β*u) * (1+β*u) := by
          apply mul_le_mul_of_nonneg_right hbern (by nlinarith [hβ0, hu0])
      _ = 1 - (β*u)^2 := by ring
      _ ≤ 1 := by nlinarith [sq_nonneg (β*u)]
  rw [Real.rpow_neg h1u, inv_eq_one_div, le_div_iff₀ hpos]
  linarith [hmul]

/-- Telescoping step: `(a+(i+1)q)^{-p}` is bounded by the drop of `t ↦ t^{1-p}`. -/
private lemma rpow_telescope (a q p : ℝ) (ha : 0 < a) (hq : 0 < q) (hp1 : 1 < p) (hp2 : p ≤ 2) (i : ℕ) :
    (a + ((i:ℝ)+1)*q)^(-p) ≤ ((a+(i:ℝ)*q)^(1-p) - (a+((i:ℝ)+1)*q)^(1-p))/(q*(p-1)) := by
  set x : ℝ := a + (i:ℝ)*q with hxdef
  set y : ℝ := a + ((i:ℝ)+1)*q with hydef
  have hx : 0 < x := by rw [hxdef]; positivity
  have hy : 0 < y := by rw [hydef]; positivity
  have hxy : x ≤ y := by rw [hxdef, hydef]; nlinarith [show (0:ℝ) ≤ (i:ℝ) by positivity, hq]
  have hyx : y - x = q := by rw [hxdef, hydef]; ring
  have hβ0 : 0 < p - 1 := by linarith
  have hβ1 : p - 1 ≤ 1 := by linarith
  set r : ℝ := x/y with hrdef
  have hr0 : 0 < r := div_pos hx hy
  have hr1 : r ≤ 1 := by rw [hrdef]; exact (div_le_one hy).mpr hxy
  have hu0 : 0 ≤ 1 - r := by linarith
  have hu1 : 1 - r < 1 := by linarith
  have hbern := one_sub_rpow_neg_ge (1 - r) hu0 hu1 hβ0 hβ1
  have hbern' : 1 + (p-1)*(1-r) ≤ r^(1-p) := by
    have h1 : (1 - (1 - r)) = r := by ring
    have h2 : (-(p-1)) = 1-p := by ring
    rw [h1, h2] at hbern
    linarith [hbern]
  have hxry : x = r * y := by rw [hrdef]; field_simp
  have hx1p : x^(1-p) = r^(1-p) * y^(1-p) := by
    rw [hxry, Real.mul_rpow hr0.le hy.le]
  have hy1p : y^(1-p) = y * y^(-p) := by
    rw [show (1:ℝ) - p = 1 + (-p) by ring, Real.rpow_add hy, Real.rpow_one]
  have hrq : 1 - r = q/y := by rw [hrdef]; field_simp; linarith [hyx]
  have h2 : x^(1-p) - y^(1-p) = (r^(1-p) - 1) * y^(1-p) := by rw [hx1p]; ring
  have h4 : (p-1)*(1-r)*y^(1-p) = y^(-p) * (q*(p-1)) := by
    rw [hrq, hy1p]; field_simp
  rw [le_div_iff₀ (mul_pos hq hβ0), h2, ← h4]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
  linarith [hbern']

/-- Sum of a tail of an arithmetic progression against a power. -/
private lemma rpow_range_sum_le (a q p : ℝ) (ha : 0 < a) (hq : 0 < q) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (N : ℕ) :
    ∑ j ∈ Finset.range N, (a + (j : ℝ) * q) ^ (-p) ≤ a ^ (-p) + a ^ (1 - p) / (q * (p - 1)) := by
  have hβ0 : 0 < p - 1 := by linarith
  have hqp : 0 < q*(p-1) := mul_pos hq hβ0
  have htel : ∀ M, ∑ i ∈ Finset.range M, ((a+(i:ℝ)*q)^(1-p) - (a+((i:ℝ)+1)*q)^(1-p))
      = a^(1-p) - (a+(M:ℝ)*q)^(1-p) := by
    intro M
    induction M with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [Nat.cast_add, Nat.cast_one]; ring
  have key : ∀ M : ℕ, ∑ i ∈ Finset.range M, (a + ((i:ℝ)+1)*q)^(-p) ≤ a^(1-p)/(q*(p-1)) := by
    intro M
    calc ∑ i ∈ Finset.range M, (a + ((i:ℝ)+1)*q)^(-p)
        ≤ ∑ i ∈ Finset.range M, ((a+(i:ℝ)*q)^(1-p) - (a+((i:ℝ)+1)*q)^(1-p))/(q*(p-1)) :=
          Finset.sum_le_sum (fun i _ => rpow_telescope a q p ha hq hp1 hp2 i)
      _ = (∑ i ∈ Finset.range M, ((a+(i:ℝ)*q)^(1-p) - (a+((i:ℝ)+1)*q)^(1-p)))/(q*(p-1)) := by
          rw [Finset.sum_div]
      _ = (a^(1-p) - (a+(M:ℝ)*q)^(1-p))/(q*(p-1)) := by rw [htel]
      _ ≤ a^(1-p)/(q*(p-1)) := by
          have hM : 0 ≤ (a+(M:ℝ)*q)^(1-p) := Real.rpow_nonneg (by positivity) _
          have hM2 : 0 ≤ (a+(M:ℝ)*q)^(1-p)/(q*(p-1)) := div_nonneg hM hqp.le
          rw [sub_div]; linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; positivity
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
    linarith [key M]

/-- The same, summed over an arbitrary finite set of natural numbers. -/
private lemma finset_rpow_tail_sum_le (a q p μ : ℝ) (hμ : 0 < μ) (ha : μ < a) (hq : 0 < q)
    (hp1 : 1 < p) (hp2 : p ≤ 2) (s : Finset ℕ) :
    ∑ j ∈ s, (a + (j:ℝ)*q)^(-p) ≤ μ^(-p) + μ^(1-p)/(q*(p-1)) := by
  have hapos : 0 < a := lt_trans hμ ha
  have hβ0 : 0 < p-1 := by linarith
  have hqp : 0 < q*(p-1) := mul_pos hq hβ0
  rcases s.eq_empty_or_nonempty with h | hne
  · subst h; simp; positivity
  · have hsub : s ⊆ Finset.range (s.max' hne + 1) := by
      intro j hj
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_max' s j hj)
    have hmono : ∑ j ∈ s, (a+(j:ℝ)*q)^(-p)
        ≤ ∑ j ∈ Finset.range (s.max' hne + 1), (a+(j:ℝ)*q)^(-p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.rpow_nonneg (by positivity) _)
    have h2 := rpow_range_sum_le a q p hapos hq hp1 hp2 (s.max' hne + 1)
    have hμp : a^(-p) ≤ μ^(-p) := Real.rpow_le_rpow_of_nonpos hμ ha.le (by linarith)
    have hμ1p : a^(1-p) ≤ μ^(1-p) := Real.rpow_le_rpow_of_nonpos hμ ha.le (by linarith)
    have hdiv : a^(1-p)/(q*(p-1)) ≤ μ^(1-p)/(q*(p-1)) := div_le_div_of_nonneg_right hμ1p hqp.le
    linarith [hmono, h2, hμp, hdiv]

/-- Counting lattice points of an arithmetic progression in an interval. -/
private lemma finset_class_card_le (n q μ : ℝ) (hq : 0 < q) (hμ : 0 < μ) (s : Finset ℤ)
    (hs : ∀ m ∈ s, |n + (m:ℝ)*q| ≤ μ) : (s.card : ℝ) ≤ 2*μ/q + 1 := by
  rcases s.eq_empty_or_nonempty with h | hne
  · subst h; simp; positivity
  · have hmem0 : s.min' hne ∈ s := Finset.min'_mem s hne
    have hmem1 : s.max' hne ∈ s := Finset.max'_mem s hne
    have h01 : s.min' hne ≤ s.max' hne := Finset.min'_le s (s.max' hne) hmem1
    have hb0 := hs (s.min' hne) hmem0
    have hb1 := hs (s.max' hne) hmem1
    have hdiff : (((s.max' hne) - (s.min' hne) : ℤ) : ℝ) * q ≤ 2*μ := by
      have e1 := abs_le.mp hb1
      have e0 := abs_le.mp hb0
      have h2 : ((s.max' hne : ℝ)*q) - ((s.min' hne : ℝ)*q) ≤ 2*μ := by linarith [e1.1, e0.2]
      rw [Int.cast_sub]; linarith
    have hcard : (s.card : ℝ) ≤ ((s.max' hne - s.min' hne : ℤ) : ℝ) + 1 := by
      have hcc : s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card :=
        Finset.card_le_card (fun x hx =>
          Finset.mem_Icc.mpr ⟨Finset.min'_le s x hx, Finset.le_max' s x hx⟩)
      have hIcc : ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℤ)
          = (s.max' hne) + 1 - (s.min' hne) := Int.card_Icc_of_le _ _ (by linarith [h01])
      have hIcc' : ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ)
          = (((s.max' hne) + 1 - (s.min' hne) : ℤ) : ℝ) := by exact_mod_cast hIcc
      have h3 : ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ)
          = ((s.max' hne - s.min' hne : ℤ) : ℝ) + 1 := by
        rw [hIcc']; push_cast; ring
      have h4 : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ) := by
        exact_mod_cast hcc
      linarith
    have hqinv : ((s.max' hne - s.min' hne : ℤ) : ℝ) ≤ 2*μ/q := by
      rw [le_div_iff₀ hq]; linarith [hdiff]
    linarith [hcard, hqinv]

/-! ## The weight function -/

private def tauWeight (δ μ : ℝ) (k : ℤ) : ℝ :=
  (k.natAbs : ℝ)^δ * (1 + |(k:ℝ)|/μ)^(-(2:ℝ))

private def progZ (n q : ℤ) (m : ℤ) : ℤ := n + m * q

private lemma tauWeight_nonneg (δ μ : ℝ) (hμ : 0 < μ) (k : ℤ) : 0 ≤ tauWeight δ μ k := by
  rw [tauWeight]
  apply mul_nonneg
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (by positivity) _

private lemma tauWeight_mid (δ μ : ℝ) (hδ0 : 0 < δ) (hμ : 0 < μ) (k : ℤ)
    (hk : |(k:ℝ)| ≤ μ) : tauWeight δ μ k ≤ μ^δ := by
  rw [tauWeight]
  rw [natAbs_cast_abs]
  have h1 : |(k:ℝ)|^δ ≤ μ^δ := Real.rpow_le_rpow (abs_nonneg _) hk hδ0.le
  have h2 : (1 + |(k:ℝ)|/μ)^(-(2:ℝ)) ≤ 1 := by
    have hle : (1:ℝ) ≤ 1 + |(k:ℝ)|/μ := by
      have : 0 ≤ |(k:ℝ)|/μ := div_nonneg (abs_nonneg _) hμ.le
      linarith
    have := Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 1 by norm_num) hle (by norm_num : (-(2:ℝ)) ≤ 0)
    simpa using this
  calc |(k:ℝ)|^δ * (1 + |(k:ℝ)|/μ)^(-(2:ℝ)) ≤ μ^δ * 1 :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hμ.le _)
    _ = μ^δ := by ring

private lemma tauWeight_large (δ μ p : ℝ) (hμ : 0 < μ) (hp : p = 2 - δ) (k : ℤ)
    (hk : μ < |(k:ℝ)|) : tauWeight δ μ k ≤ μ^2 * |(k:ℝ)|^(-p) := by
  rw [tauWeight, natAbs_cast_abs]
  have hy : 0 < |(k:ℝ)| := lt_trans hμ hk
  have h1 : (1 + |(k:ℝ)|/μ)^(-(2:ℝ)) ≤ (|(k:ℝ)|/μ)^(-(2:ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
    linarith [abs_nonneg (k:ℝ), hμ]
  have h2 : (|(k:ℝ)|/μ)^(-(2:ℝ)) = μ^2 * |(k:ℝ)|^(-(2:ℝ)) := by
    rw [Real.div_rpow (abs_nonneg _) hμ.le, Real.rpow_neg hμ.le, div_inv_eq_mul, Real.rpow_ofNat]
    ring
  have hmain : (1 + |(k:ℝ)|/μ)^(-(2:ℝ)) ≤ μ^2 * |(k:ℝ)|^(-(2:ℝ)) := h1.trans h2.le
  calc |(k:ℝ)|^δ * (1 + |(k:ℝ)|/μ)^(-(2:ℝ))
      ≤ |(k:ℝ)|^δ * (μ^2 * |(k:ℝ)|^(-(2:ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg (abs_nonneg _) _)
    _ = μ^2 * (|(k:ℝ)|^δ * |(k:ℝ)|^(-(2:ℝ))) := by ring
    _ = μ^2 * |(k:ℝ)|^(-p) := by
        congr 1
        rw [← Real.rpow_add hy δ (-(2:ℝ)), hp]
        congr 1
        ring

/-! ## The main estimate -/

private lemma tauWeight_finset_sum_le (δ μ p : ℝ) (hδ0 : 0 < δ) (hμ : 0 < μ) (hp : p = 2 - δ)
    (hp1 : 1 < p) (hp2 : p ≤ 2) (q : ℕ) (hqR : (0:ℝ) < (q:ℝ)) (n : ℤ) (s : Finset ℤ) :
    ∑ m ∈ s, tauWeight δ μ (progZ n (q:ℤ) m)
      ≤ (3 + 2/(1-δ)) * (μ^(1+δ)/(q:ℝ) + μ^δ) := by
  classical
  have hδ1' : 0 < 1 - δ := by rw [hp] at hp1; linarith
  set P : ℤ → Prop := fun m => |((progZ n (q:ℤ) m : ℤ) : ℝ)| ≤ μ with hP
  set Q : ℤ → Prop := fun m => μ < ((progZ n (q:ℤ) m : ℤ) : ℝ) with hQ
  -- middle
  have hA : ∑ m ∈ s.filter P, tauWeight δ μ (progZ n (q:ℤ) m)
      ≤ (2*μ/(q:ℝ) + 1) * μ^δ := by
    have hle : ∑ m ∈ s.filter P, tauWeight δ μ (progZ n (q:ℤ) m)
        ≤ ((s.filter P).card : ℝ) * μ^δ := by
      calc ∑ m ∈ s.filter P, tauWeight δ μ (progZ n (q:ℤ) m)
          ≤ ∑ _m ∈ s.filter P, μ^δ := by
            apply Finset.sum_le_sum
            intro m hm
            refine tauWeight_mid δ μ hδ0 hμ _ ?_
            have := (Finset.mem_filter.mp hm).2
            rwa [hP] at this
        _ = ((s.filter P).card : ℝ) * μ^δ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := finset_class_card_le (n:ℝ) (q:ℝ) μ hqR hμ (s.filter P) (fun m hm => by
      have h1 : |((progZ n (q:ℤ) m : ℤ) : ℝ)| ≤ μ := by
        have := (Finset.mem_filter.mp hm).2; rwa [hP] at this
      rw [progZ] at h1
      push_cast at h1 ⊢
      exact h1)
    calc ∑ m ∈ s.filter P, tauWeight δ μ (progZ n (q:ℤ) m)
        ≤ ((s.filter P).card : ℝ) * μ^δ := hle
      _ ≤ (2*μ/(q:ℝ) + 1) * μ^δ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hμ.le _)
  -- positive tail
  have hB : ∑ m ∈ (s.filter (fun m => ¬ P m)).filter Q, tauWeight δ μ (progZ n (q:ℤ) m)
      ≤ μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)) := by
    set t : Finset ℤ := (s.filter (fun m => ¬ P m)).filter Q with ht
    rcases t.eq_empty_or_nonempty with h | hne
    · rw [h]; simp; positivity
    · have hmem0 : t.min' hne ∈ t := Finset.min'_mem t hne
      have hQ0 : μ < ((progZ n (q:ℤ) (t.min' hne) : ℤ) : ℝ) := by
        have := (Finset.mem_filter.mp hmem0).2; rwa [hQ] at this
      have hnum0 : ¬ P (t.min' hne) := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem0).1).2
      have habs0 : μ < |((progZ n (q:ℤ) (t.min' hne) : ℤ) : ℝ)| :=
        not_le.mp (by rwa [hP] at hnum0)
      set a : ℝ := ((progZ n (q:ℤ) (t.min' hne) : ℤ) : ℝ) with ha
      have ha_gt : μ < a := by
        rw [ha]; rwa [abs_of_pos (lt_trans hμ hQ0)] at habs0
      have hle : ∑ m ∈ t, tauWeight δ μ (progZ n (q:ℤ) m)
          ≤ μ^2 * ∑ m ∈ t, (((progZ n (q:ℤ) m : ℤ) : ℝ))^(-p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro m hm
        have hmQ : μ < ((progZ n (q:ℤ) m : ℤ) : ℝ) := by
          have := (Finset.mem_filter.mp hm).2; rwa [hQ] at this
        have hmnP : ¬ P m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
        have hmabs : μ < |((progZ n (q:ℤ) m : ℤ) : ℝ)| := not_le.mp (by rwa [hP] at hmnP)
        have hlarge := tauWeight_large δ μ p hμ hp _ hmabs
        rwa [abs_of_pos (lt_trans hμ hmQ)] at hlarge
      have htail : ∑ m ∈ t, (((progZ n (q:ℤ) m : ℤ) : ℝ))^(-p)
          ≤ μ^(-p) + μ^(1-p)/((q:ℝ)*(p-1)) := by
        have hinj : Set.InjOn (fun m : ℤ => (m - t.min' hne).toNat) (↑t : Set ℤ) := by
          intro m1 hm1 m2 hm2 heq
          have h1 : t.min' hne ≤ m1 := Finset.min'_le t m1 hm1
          have h2 : t.min' hne ≤ m2 := Finset.min'_le t m2 hm2
          have e1 : ((m1 - t.min' hne).toNat : ℤ) = m1 - t.min' hne :=
            Int.toNat_of_nonneg (by omega)
          have e2 : ((m2 - t.min' hne).toNat : ℤ) = m2 - t.min' hne :=
            Int.toNat_of_nonneg (by omega)
          have heq' : (m1 - t.min' hne).toNat = (m2 - t.min' hne).toNat := heq
          have : m1 - t.min' hne = m2 - t.min' hne := by rw [← e1, ← e2, heq']
          omega
        have hsum : ∑ m ∈ t, (((progZ n (q:ℤ) m : ℤ) : ℝ))^(-p)
            = ∑ j ∈ t.image (fun m : ℤ => (m - t.min' hne).toNat),
                (a + (j:ℝ)*(q:ℝ))^(-p) := by
          rw [Finset.sum_image hinj]
          apply Finset.sum_congr rfl
          intro m hm
          have hm0le : t.min' hne ≤ m := Finset.min'_le t m hm
          have h1 : (((m - t.min' hne).toNat : ℕ) : ℝ) = (m:ℝ) - ((t.min' hne : ℤ) : ℝ) := by
            have hh : ((m - t.min' hne).toNat : ℤ) = m - t.min' hne :=
              Int.toNat_of_nonneg (by omega)
            have h2 : (((m - t.min' hne).toNat : ℕ) : ℝ)
                = (((m - t.min' hne).toNat : ℤ) : ℝ) := by push_cast; ring
            rw [h2, hh]; exact Int.cast_sub m (t.min' hne)
          have heq : ((progZ n (q:ℤ) m : ℤ) : ℝ)
              = a + (((m - t.min' hne).toNat : ℕ) : ℝ) * (q:ℝ) := by
            rw [ha, h1]
            simp only [progZ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
            ring
          rw [heq]
        rw [hsum]
        exact finset_rpow_tail_sum_le a (q:ℝ) p μ hμ ha_gt hqR hp1 hp2 _
      calc ∑ m ∈ t, tauWeight δ μ (progZ n (q:ℤ) m)
          ≤ μ^2 * ∑ m ∈ t, (((progZ n (q:ℤ) m : ℤ) : ℝ))^(-p) := hle
        _ ≤ μ^2 * (μ^(-p) + μ^(1-p)/((q:ℝ)*(p-1))) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)) := by
            have e1 : μ^2 * μ^(-p) = μ^δ := by
              rw [← Real.rpow_ofNat μ 2, ← Real.rpow_add hμ, hp]; congr 1; ring
            have e2 : μ^2 * (μ^(1-p)/((q:ℝ)*(p-1))) = μ^(1+δ)/((q:ℝ)*(1-δ)) := by
              rw [← mul_div_assoc]
              congr 1
              · rw [← Real.rpow_ofNat μ 2, ← Real.rpow_add hμ, hp]; congr 1; ring
              · rw [hp]; ring
            rw [mul_add, e1, e2]
  -- negative tail
  have hC : ∑ m ∈ (s.filter (fun m => ¬ P m)).filter (fun m => ¬ Q m),
        tauWeight δ μ (progZ n (q:ℤ) m)
      ≤ μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)) := by
    set t : Finset ℤ := (s.filter (fun m => ¬ P m)).filter (fun m => ¬ Q m) with ht
    rcases t.eq_empty_or_nonempty with h | hne
    · rw [h]; simp; positivity
    · have hmem1 : t.max' hne ∈ t := Finset.max'_mem t hne
      have hnQ1 : ¬ Q (t.max' hne) := (Finset.mem_filter.mp hmem1).2
      have hx1 : ¬ (μ < ((progZ n (q:ℤ) (t.max' hne) : ℤ) : ℝ)) := by rwa [hQ] at hnQ1
      have hnum1 : ¬ P (t.max' hne) := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem1).1).2
      have habs1 : μ < |((progZ n (q:ℤ) (t.max' hne) : ℤ) : ℝ)| :=
        not_le.mp (by rwa [hP] at hnum1)
      have hneg1 : ((progZ n (q:ℤ) (t.max' hne) : ℤ) : ℝ) < 0 := by
        rcases lt_or_ge (((progZ n (q:ℤ) (t.max' hne) : ℤ) : ℝ)) 0 with h' | h'
        · exact h'
        · exfalso
          rw [abs_of_nonneg h'] at habs1
          exact absurd habs1 (not_lt.mpr (not_lt.mp hx1))
      set b : ℝ := -((progZ n (q:ℤ) (t.max' hne) : ℤ) : ℝ) with hb
      have hb_gt : μ < b := by rw [hb]; rw [abs_of_neg hneg1] at habs1; linarith
      have hle : ∑ m ∈ t, tauWeight δ μ (progZ n (q:ℤ) m)
          ≤ μ^2 * ∑ m ∈ t, ((-((progZ n (q:ℤ) m : ℤ) : ℝ)))^(-p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro m hm
        have hmQ : ¬ Q m := (Finset.mem_filter.mp hm).2
        have hmx : ¬ (μ < ((progZ n (q:ℤ) m : ℤ) : ℝ)) := by rwa [hQ] at hmQ
        have hmnP : ¬ P m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
        have hmabs : μ < |((progZ n (q:ℤ) m : ℤ) : ℝ)| := not_le.mp (by rwa [hP] at hmnP)
        have hmneg : ((progZ n (q:ℤ) m : ℤ) : ℝ) < 0 := by
          rcases lt_or_ge (((progZ n (q:ℤ) m : ℤ) : ℝ)) 0 with h' | h'
          · exact h'
          · exfalso
            rw [abs_of_nonneg h'] at hmabs
            exact absurd hmabs (not_lt.mpr (not_lt.mp hmx))
        have hlarge := tauWeight_large δ μ p hμ hp _ hmabs
        rwa [abs_of_neg hmneg] at hlarge
      have htail : ∑ m ∈ t, ((-((progZ n (q:ℤ) m : ℤ) : ℝ)))^(-p)
          ≤ μ^(-p) + μ^(1-p)/((q:ℝ)*(p-1)) := by
        have hinj : Set.InjOn (fun m : ℤ => (t.max' hne - m).toNat) (↑t : Set ℤ) := by
          intro m1 hm1 m2 hm2 heq
          have h1 : m1 ≤ t.max' hne := Finset.le_max' t m1 hm1
          have h2 : m2 ≤ t.max' hne := Finset.le_max' t m2 hm2
          have e1 : ((t.max' hne - m1).toNat : ℤ) = t.max' hne - m1 :=
            Int.toNat_of_nonneg (by omega)
          have e2 : ((t.max' hne - m2).toNat : ℤ) = t.max' hne - m2 :=
            Int.toNat_of_nonneg (by omega)
          have heq' : (t.max' hne - m1).toNat = (t.max' hne - m2).toNat := heq
          have : t.max' hne - m1 = t.max' hne - m2 := by rw [← e1, ← e2, heq']
          omega
        have hsum : ∑ m ∈ t, ((-((progZ n (q:ℤ) m : ℤ) : ℝ)))^(-p)
            = ∑ j ∈ t.image (fun m : ℤ => (t.max' hne - m).toNat),
                (b + (j:ℝ)*(q:ℝ))^(-p) := by
          rw [Finset.sum_image hinj]
          apply Finset.sum_congr rfl
          intro m hm
          have hmle : m ≤ t.max' hne := Finset.le_max' t m hm
          have h1 : (((t.max' hne - m).toNat : ℕ) : ℝ) = ((t.max' hne : ℤ) : ℝ) - (m:ℝ) := by
            have hh : ((t.max' hne - m).toNat : ℤ) = t.max' hne - m :=
              Int.toNat_of_nonneg (by omega)
            have h2 : (((t.max' hne - m).toNat : ℕ) : ℝ)
                = (((t.max' hne - m).toNat : ℤ) : ℝ) := by push_cast; ring
            rw [h2, hh]; exact Int.cast_sub _ _
          have heq : -(((progZ n (q:ℤ) m : ℤ) : ℝ))
              = b + (((t.max' hne - m).toNat : ℕ) : ℝ) * (q:ℝ) := by
            rw [hb, h1]
            simp only [progZ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
            ring
          rw [heq]
        rw [hsum]
        exact finset_rpow_tail_sum_le b (q:ℝ) p μ hμ hb_gt hqR hp1 hp2 _
      calc ∑ m ∈ t, tauWeight δ μ (progZ n (q:ℤ) m)
          ≤ μ^2 * ∑ m ∈ t, ((-((progZ n (q:ℤ) m : ℤ) : ℝ)))^(-p) := hle
        _ ≤ μ^2 * (μ^(-p) + μ^(1-p)/((q:ℝ)*(p-1))) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)) := by
            have e1 : μ^2 * μ^(-p) = μ^δ := by
              rw [← Real.rpow_ofNat μ 2, ← Real.rpow_add hμ, hp]; congr 1; ring
            have e2 : μ^2 * (μ^(1-p)/((q:ℝ)*(p-1))) = μ^(1+δ)/((q:ℝ)*(1-δ)) := by
              rw [← mul_div_assoc]
              congr 1
              · rw [← Real.rpow_ofNat μ 2, ← Real.rpow_add hμ, hp]; congr 1; ring
              · rw [hp]; ring
            rw [mul_add, e1, e2]
  -- arithmetic
  have harith : (2*μ/(q:ℝ)+1)*μ^δ + (μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)))
      + (μ^δ + μ^(1+δ)/((q:ℝ)*(1-δ)))
      ≤ (3 + 2/(1-δ)) * (μ^(1+δ)/(q:ℝ) + μ^δ) := by
    have hA0 : 0 ≤ μ^(1+δ)/(q:ℝ) := div_nonneg (Real.rpow_nonneg hμ.le _) hqR.le
    have hB0 : 0 ≤ μ^δ := Real.rpow_nonneg hμ.le _
    have hD0 : 0 ≤ μ^δ/(1-δ) := div_nonneg hB0 hδ1'.le
    have hstep : (2*μ/(q:ℝ)+1)*μ^δ = 2*(μ^(1+δ)/(q:ℝ)) + μ^δ := by
      rw [add_mul, one_mul]
      congr 1
      rw [show (2*μ/(q:ℝ))*μ^δ = 2*(μ*μ^δ)/(q:ℝ) by ring,
        show μ * μ^δ = μ^(1+δ) by rw [Real.rpow_add hμ 1 δ, Real.rpow_one]]
      ring
    have hCeq : μ^(1+δ)/((q:ℝ)*(1-δ)) = (μ^(1+δ)/(q:ℝ))/(1-δ) := by
      field_simp
    have hexp : (3 + 2/(1-δ)) * (μ^(1+δ)/(q:ℝ) + μ^δ)
        = 3*(μ^(1+δ)/(q:ℝ)) + 3*μ^δ + 2*((μ^(1+δ)/(q:ℝ))/(1-δ)) + 2*(μ^δ/(1-δ)) := by
      ring
    rw [hstep, hCeq, hexp]
    have h2 : (0:ℝ) ≤ 2*(μ^δ/(1-δ)) := mul_nonneg (by norm_num) hD0
    nlinarith [hA0, h2]
  rw [← Finset.sum_filter_add_sum_filter_not s P]
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun m => ¬ P m)) Q]
  linarith [hA, hB, hC, harith]

theorem tau_class_decay_sum : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ (μ : ℝ), 0 < μ → ∀ (q : ℕ), 1 ≤ q → ∀ (n : ℤ),
      (∑' k : ℤ, (if (k : ZMod q) = (n : ZMod q) then (k.natAbs : ℝ) ^ δ * (1 + |(k:ℝ)| / μ) ^ (-(2:ℝ)) else 0))
        ≤ C * (μ ^ (1 + δ) / q + μ ^ δ) := by
  intro δ hδ0 hδ1
  refine ⟨3 + 2/(1-δ), by positivity, ?_⟩
  intro μ hμ q hq n
  set p : ℝ := 2 - δ with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hp2 : p ≤ 2 := by rw [hp]; linarith
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show (0:ℕ) < q by omega)
  change (∑' k : ℤ, (if (k : ZMod q) = (n : ZMod q) then tauWeight δ μ k else 0))
      ≤ (3 + 2/(1-δ)) * (μ^(1+δ)/(q:ℝ) + μ^δ)
  rw [tsum_class_eq_progression q hq n (tauWeight δ μ)]
  change (∑' m : ℤ, tauWeight δ μ (progZ n (q:ℤ) m))
      ≤ (3 + 2/(1-δ)) * (μ^(1+δ)/(q:ℝ) + μ^δ)
  apply Real.tsum_le_of_sum_le
  · exact fun m => tauWeight_nonneg δ μ hμ _
  · intro s
    exact tauWeight_finset_sum_le δ μ p hδ0 hμ hp hp1 hp2 q hqR n s

end

end Work.FIArea4.Vflip
