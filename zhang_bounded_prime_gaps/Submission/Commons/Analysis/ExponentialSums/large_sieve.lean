import Mathlib
import Submission.Commons.Analysis.ExponentialSums.norm_geom_sum_le
import Submission.Commons.Analysis.Trig.cosec_fejer_limit
import Submission.Commons.Analysis.Fin.count_fin_sub
import Submission.Commons.Analysis.ExponentialSums.hilbert_separated

namespace Commons.Analysis.ExponentialSums


private lemma star_negone (n : ℤ) : star ((-1 : ℂ) ^ n) = (-1 : ℂ) ^ n := by
  rw [Complex.star_def, map_zpow₀]; norm_num

private lemma negone_add (m n : ℤ) : (-1 : ℂ) ^ (m + n) = (-1 : ℂ) ^ (m - n) := by
  have h : (-1 : ℂ) ^ (2 * n) = 1 := by rw [zpow_mul]; norm_num
  rw [show m + n = (m - n) + 2 * n by ring, zpow_add₀, h, mul_one]; norm_num

private lemma negone_mul (a b : ℤ) : (-1 : ℂ) ^ a * (-1 : ℂ) ^ b = (-1 : ℂ) ^ (a - b) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), negone_add]

private lemma aug_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (z : ι → ℂ) (K : ℕ) :
    (∑ p : ι × Fin K, ∑ q ∈ (Finset.univ : Finset (ι × Fin K)).erase p,
        (z p.1 * (-1:ℂ)^(p.2.val:ℤ)) * star (z q.1 * (-1:ℂ)^(q.2.val:ℤ)) /
          (((α p.1 + p.2.val) - (α q.1 + q.2.val) : ℝ) : ℂ))
      = ∑ r, ∑ s, z r * star (z s) *
          (∑ m : Fin K, ∑ n : Fin K,
            (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ)) / (((α r - α s) + ((m.val : ℝ) - (n.val : ℝ)) : ℝ) : ℂ)) := by
  set F : (ι × Fin K) → (ι × Fin K) → ℂ := fun p q =>
    (z p.1 * (-1:ℂ)^(p.2.val:ℤ)) * star (z q.1 * (-1:ℂ)^(q.2.val:ℤ)) /
      (((α p.1 + p.2.val) - (α q.1 + q.2.val) : ℝ) : ℂ) with hF
  have hF0 : ∀ p : ι × Fin K, F p p = 0 := by
    intro p; simp only [hF, sub_self, Complex.ofReal_zero, div_zero]
  have h1 : (∑ p : ι × Fin K, ∑ q ∈ (Finset.univ : Finset (ι × Fin K)).erase p, F p q)
      = ∑ p : ι × Fin K, ∑ q : ι × Fin K, F p q := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact Finset.sum_erase _ (hF0 p)
  rw [h1]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hpow : (-1:ℂ)^((m.val:ℤ)) * (-1:ℂ)^((n.val:ℤ)) = (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ)) :=
    negone_mul _ _
  simp only [hF, star_mul, star_negone]
  have key : z x * (-1:ℂ)^((m.val:ℤ)) * ((-1:ℂ)^((n.val:ℤ)) * star (z s))
      = z x * star (z s) * (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ)) := by
    rw [← hpow]; ring
  rw [key]
  have hden : (↑(α x + ↑↑m - (α s + ↑↑n)) : ℂ) = ↑(α x - α s + (↑↑m - ↑↑n)) := by
    congr 1; push_cast; ring
  rw [hden, div_eq_mul_inv, div_eq_mul_inv]
  ring


-- Fejer/cosec kernel (matching the requested limit lemma)
noncomputable def fejerK (K : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
    ((1 - (|k| : ℝ) / K : ℝ) : ℂ) * (-1 : ℂ) ^ k / ((θ + k : ℝ) : ℂ)

private theorem count_fin_sub (K : ℕ) (f : ℤ → ℂ) :
    (∑ m : Fin K, ∑ n : Fin K, f ((m.val : ℤ) - (n.val : ℤ)))
      = ∑ k ∈ Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1),
          ((((K:ℝ) - |((k:ℝ))|) : ℝ) : ℂ) * f k :=
  Commons.Analysis.Fin.count_fin_sub K f

private theorem cosec_fejer_limit (u : ℝ) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ k : ℤ, δ ≤ |u - k|) :
    Filter.Tendsto (fun K : ℕ => fejerK K u)
      Filter.atTop (nhds ((Real.pi : ℂ) / ((Real.sin (Real.pi * u) : ℝ) : ℂ))) := by
  simpa only [fejerK] using Commons.Analysis.Trig.cosec_fejer_limit u hδ hsep


-- apply count_fin_sub with f(d) = (-1)^d/(theta+d)
private lemma D_eq (K : ℕ) (θ : ℝ) :
    (∑ m : Fin K, ∑ n : Fin K, (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ))
        / ((θ + ((m.val : ℝ) - (n.val : ℝ)) : ℝ) : ℂ))
      = ∑ k ∈ Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1),
          ((((K:ℝ) - |((k:ℝ))|) : ℝ) : ℂ) * ((-1:ℂ)^k / ((θ + ((k:ℝ))):ℂ)) := by
  have hcong : (∑ m : Fin K, ∑ n : Fin K, (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ))
        / ((θ + ((m.val : ℝ) - (n.val : ℝ)) : ℝ) : ℂ))
      = (∑ m : Fin K, ∑ n : Fin K,
          (fun d : ℤ => (-1:ℂ)^d / ((θ + (d:ℝ)):ℂ)) ((m.val:ℤ)-(n.val:ℤ))) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    congr 2
    push_cast
    ring
  rw [hcong]
  exact count_fin_sub K (fun d : ℤ => (-1:ℂ)^d / ((θ + (d:ℝ)):ℂ))

private lemma pow_neg_one_neg (k : ℤ) : (-1:ℂ)^(-k) = (-1:ℂ)^k := by
  rw [zpow_neg]
  have h : (-1:ℂ)^k * (-1:ℂ)^k = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), show k + k = 2*k by ring, zpow_mul]
    norm_num
  exact inv_eq_of_mul_eq_one_right h

private lemma sum_antisym_Icc {K : ℤ} {g : ℤ → ℂ} (hg : ∀ k : ℤ, g (-k) = - g k) :
    (∑ k ∈ Finset.Icc (-K) K, g k) = 0 := by
  have h : (∑ k ∈ Finset.Icc (-K) K, g k) = - (∑ k ∈ Finset.Icc (-K) K, g k) := by
    calc (∑ k ∈ Finset.Icc (-K) K, g k)
        = ∑ k ∈ Finset.Icc (-K) K, g (-k) := by
          refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a ha; simp
          · intro a ha; simp
          · intro a ha; simp
      _ = ∑ k ∈ Finset.Icc (-K) K, - g k := by simp_rw [hg]
      _ = - ∑ k ∈ Finset.Icc (-K) K, g k := by rw [Finset.sum_neg_distrib]
  have h3 : (∑ k ∈ Finset.Icc (-K) K, g k) + (∑ k ∈ Finset.Icc (-K) K, g k) = 0 := by
    nth_rewrite 2 [h]; ring
  exact add_self_eq_zero.mp h3

private lemma fejerK_zero (K : ℕ) : fejerK K 0 = 0 := by
  rw [fejerK]
  refine sum_antisym_Icc (K := (K:ℤ)) (fun k => ?_)
  rw [show ((((-k:ℤ)):ℝ)) = -(k:ℝ) by push_cast; ring]
  rw [show (|(-(k:ℝ))|:ℝ) = |(k:ℝ)| by rw [abs_neg]]
  rw [pow_neg_one_neg]
  rw [show (((0:ℝ) + (-(k:ℝ)) : ℝ) : ℂ) = -(((0:ℝ) + (k:ℝ) : ℝ) : ℂ) by push_cast; ring, div_neg]

-- shrink the range of fejerK (extra terms vanish for K ≥ 1)
private lemma fejerK_shift (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) :
    fejerK K θ = ∑ k ∈ Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1),
        ((1 - (|k|:ℝ)/K:ℝ):ℂ) * (-1:ℂ)^k / ((θ + (k:ℝ) : ℝ) : ℂ) := by
  rw [show Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1) = Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1) by
        congr 1; ring]
  rw [fejerK]
  refine (Finset.sum_subset (s₁ := Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1))
      (s₂ := Finset.Icc (-(K:ℤ)) (K:ℤ)) ?_ ?_).symm
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hxnot
    simp only [Finset.mem_Icc] at hx hxnot
    push Not at hxnot
    have hxK : x = (K:ℤ) ∨ x = -(K:ℤ) := by omega
    have hc : ∀ y : ℤ, y = (K:ℤ) ∨ y = -(K:ℤ) →
        (1 - (|(y:ℝ)|:ℝ)/(K:ℝ) : ℝ) = 0 := by
      intro y hy
      rcases hy with h | h <;> subst h
      · rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (((K:ℤ)):ℝ))]; push_cast
        rw [div_self (by positivity : (K:ℝ) ≠ 0)]; ring
      · push_cast
        rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (K:ℝ))]
        rw [div_self (by positivity : (K:ℝ) ≠ 0)]; ring
    rw [show (((1 - (|(x:ℝ)|:ℝ)/(K:ℝ) : ℝ)):ℂ) = 0 by rw [hc x hxK]; simp]
    simp

private lemma coef_eq (K : ℕ) (hK : 1 ≤ K) (k : ℤ) :
    (K:ℂ)⁻¹ * (((K:ℝ) - |(k:ℝ)|:ℝ):ℂ) = ((1 - (|k|:ℝ)/K:ℝ):ℂ) := by
  have hKc : (K:ℝ) ≠ 0 := by positivity
  rw [show (K:ℂ) = ((K:ℝ):ℂ) by push_cast; ring]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  field_simp

private lemma inv_mul_Ddouble_eq (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) :
    (K:ℂ)⁻¹ * (∑ m : Fin K, ∑ n : Fin K, (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ))
        / ((θ + ((m.val:ℝ)-(n.val:ℝ)) : ℝ) : ℂ)) = fejerK K θ := by
  rw [D_eq, Finset.mul_sum, fejerK_shift K hK θ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← coef_eq K hK k]
  push_cast
  ring

private lemma norm_negone_zpow (n : ℤ) : ‖(-1:ℂ)^n‖ = 1 := by
  rw [norm_zpow]; simp

private lemma sum_norm_wt {ι : Type*} [Fintype ι] (z : ι → ℂ) (K : ℕ) :
    (∑ p : ι × Fin K, ‖z p.1 * (-1:ℂ)^(p.2.val:ℤ)‖ ^ 2) = (K:ℝ) * ∑ r, ‖z r‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [norm_mul, norm_negone_zpow, mul_one]
  rw [show (∑ i : ι, ∑ j : Fin K, ‖z i‖ ^ 2) = ∑ i : ι, (K:ℝ) * ‖z i‖ ^ 2 by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  rw [← Finset.mul_sum]

theorem cosec_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : ι, r ≠ s → ∀ k : ℤ, δ ≤ |α r - α s - k|) (z : ι → ℂ) :
    ‖∑ r, ∑ s, z r * star (z s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)‖
      ≤ (1/δ) * ∑ r, ‖z r‖ ^ 2 := by
  by_cases hcard : Fintype.card ι ≤ 1
  · have hsub : ∀ a b : ι, a = b := Fintype.card_le_one_iff.mp hcard
    have hzero : (∑ r, ∑ s, z r * star (z s)
        / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro s _
      rw [hsub r s]; simp
    rw [hzero, norm_zero]; positivity
  · have hne : ∃ r s : ι, r ≠ s := by
      by_contra h; push Not at h
      exact hcard (Fintype.card_le_one_iff.mpr h)
    obtain ⟨r0, s0, hrs0⟩ := hne
    have hδ2 : δ ≤ 1/2 := by
      have h1 := hsep r0 s0 hrs0 (round (α r0 - α s0))
      have h2 := abs_sub_round (α r0 - α s0)
      linarith
    set U : ℂ := ∑ r, ∑ s, z r * star (z s) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ) with hU
    set T : ℂ := ∑ r, ∑ s, z r * star (z s) *
        ((Real.pi : ℂ) / ((Real.sin (Real.pi * (α r - α s)) : ℝ) : ℂ)) with hT
    have hTU : T = (Real.pi : ℂ) * U := by
      rw [hT, hU, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have hbound : ‖T‖ ≤ Real.pi / δ * ∑ r, ‖z r‖ ^ 2 := by
      set S : ℕ → ℂ := fun K => ∑ p : ι × Fin K, ∑ q ∈ (Finset.univ : Finset (ι × Fin K)).erase p,
          (z p.1 * (-1:ℂ)^(p.2.val:ℤ)) * star (z q.1 * (-1:ℂ)^(q.2.val:ℤ)) /
            (((α p.1 + p.2.val) - (α q.1 + q.2.val) : ℝ) : ℂ) with hS
      set A : ℕ → ℂ := fun K => (K:ℂ)⁻¹ * S K with hA
      set B : ℕ → ℂ := fun K => ∑ r, ∑ s, z r * star (z s) * fejerK K (α r - α s) with hB
      have hsepK : ∀ K (p q : ι × Fin K), p ≠ q →
          δ ≤ |(α p.1 + (p.2.val:ℝ)) - (α q.1 + (q.2.val:ℝ))| := by
        intro K p q hpq
        rcases p with ⟨r, m⟩; rcases q with ⟨s, n⟩
        by_cases hrs : r = s
        · subst hrs
          have hmn : m ≠ n := fun h => hpq (by simp [h])
          have hval : m.val ≠ n.val := fun h => hmn (Fin.ext h)
          have h2 : (1:ℝ) ≤ |(m.val:ℝ) - (n.val:ℝ)| := by
            have h3 : (1:ℤ) ≤ |(m.val:ℤ) - (n.val:ℤ)| :=
              Int.one_le_abs (sub_ne_zero.mpr (by omega))
            have h4 : (((|(m.val:ℤ) - (n.val:ℤ)| : ℤ)) : ℝ) = |(m.val:ℝ) - (n.val:ℝ)| := by
              rw [Int.cast_abs, Int.cast_sub]; push_cast; ring_nf
            rw [← h4]; exact_mod_cast h3
          have hthis : (α r + (m.val:ℝ)) - (α r + (n.val:ℝ)) = (m.val:ℝ) - (n.val:ℝ) := by ring
          rw [hthis]; linarith [h2, hδ2]
        · have hthis := hsep r s hrs ((n.val:ℤ) - (m.val:ℤ))
          have harg : (α r + (m.val:ℝ)) - (α s + (n.val:ℝ))
              = (α r - α s) - (((n.val:ℤ) - (m.val:ℤ) : ℤ) : ℝ) := by push_cast; ring
          rw [harg]; exact hthis
      have hHilb : ∀ K, ‖S K‖ ≤ Real.pi / δ * ((K:ℝ) * ∑ r, ‖z r‖ ^ 2) := by
        intro K
        simp only [hS]
        have h := hilbert_separated (fun p : ι × Fin K => α p.1 + (p.2.val:ℝ)) hδ (hsepK K)
          (fun p => z p.1 * (-1:ℂ)^(p.2.val:ℤ))
        rw [sum_norm_wt] at h
        exact h
      have hAB : ∀ K, 1 ≤ K → A K = B K := by
        intro K hK
        simp only [hA, hS, hB]
        rw [aug_decomp]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [show (K:ℂ)⁻¹ * (z r * star (z s) * (∑ m : Fin K, ∑ n : Fin K,
              (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ)) / (((α r - α s) + ((m.val:ℝ)-(n.val:ℝ)) : ℝ) : ℂ)))
            = z r * star (z s) * ((K:ℂ)⁻¹ * (∑ m : Fin K, ∑ n : Fin K,
              (-1:ℂ)^((m.val:ℤ)-(n.val:ℤ)) / (((α r - α s) + ((m.val:ℝ)-(n.val:ℝ)) : ℝ) : ℂ))) by ring]
        rw [inv_mul_Ddouble_eq K hK]
      have hA_bound : ∀ K, 1 ≤ K → ‖A K‖ ≤ Real.pi / δ * ∑ r, ‖z r‖ ^ 2 := by
        intro K hK
        rw [hA, norm_mul]
        rw [show ‖(K:ℂ)⁻¹‖ = ((K:ℝ))⁻¹ by rw [norm_inv, Complex.norm_natCast]]
        have h1 := hHilb K
        have h2 : ((K:ℝ))⁻¹ * ‖S K‖ ≤ ((K:ℝ))⁻¹ * (Real.pi / δ * ((K:ℝ) * ∑ r, ‖z r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        refine h2.trans_eq ?_
        field_simp
      have hlimB : Filter.Tendsto B Filter.atTop (nhds T) := by
        simp only [hB, hT]
        refine tendsto_finset_sum _ (fun r _ => tendsto_finset_sum _ (fun s _ => ?_))
        by_cases hrs : r = s
        · subst hrs
          have h0 : ∀ K, fejerK K (α r - α r) = 0 := by
            intro K; rw [sub_self]; exact fejerK_zero K
          rw [show (fun K => z r * star (z r) * fejerK K (α r - α r)) = (fun _ => (0:ℂ)) by
                funext K; rw [h0 K, mul_zero]]
          rw [show (z r * star (z r) * ((Real.pi : ℂ)
                / ((Real.sin (Real.pi * (α r - α r)) : ℝ) : ℂ))) = 0 by
                rw [sub_self]; simp]
          exact tendsto_const_nhds
        · exact (cosec_fejer_limit (α r - α s) hδ (fun k => hsep r s hrs k)).const_mul _
      have hlimA : Filter.Tendsto A Filter.atTop (nhds T) :=
        hlimB.congr' (by
          filter_upwards [Filter.eventually_ge_atTop 1] with K hK
          exact (hAB K hK).symm)
      have hnorm : Filter.Tendsto (fun K => ‖A K‖) Filter.atTop (nhds ‖T‖) := hlimA.norm
      exact le_of_tendsto hnorm (by
        filter_upwards [Filter.eventually_ge_atTop 1] with K hK
        exact hA_bound K hK)
    rw [hTU, norm_mul] at hbound
    rw [show ‖(Real.pi : ℂ)‖ = Real.pi by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]] at hbound
    rw [hU]
    rw [show Real.pi / δ * ∑ r, ‖z r‖ ^ 2 = Real.pi * ((1/δ) * ∑ r, ‖z r‖ ^ 2) by ring] at hbound
    exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mp hbound

private lemma ch_add' (x y : ℝ) : ch x * ch y = ch (x + y) := by
  unfold ch; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma star_ch' (x : ℝ) : star (ch x) = ch (-x) := by
  unfold ch; rw [Complex.star_def, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

private lemma ch_mul_star (x y : ℝ) : ch x * star (ch y) = ch (x - y) := by
  rw [star_ch', ch_add', sub_eq_add_neg]

private lemma ofReal_sin_eq (t : ℝ) :
    ((Real.sin t : ℝ) : ℂ) =
      (Complex.exp (((t : ℂ) * Complex.I)) - Complex.exp (-((t : ℂ) * Complex.I))) / (2 * Complex.I) := by
  rw [show (-((t:ℂ)*Complex.I)) = (((-t:ℝ)):ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp
  ring


private lemma ch_sub (x y : ℝ) :
    ch x - ch y = 2 * Complex.I * ch ((x+y)/2) * ((Real.sin (Real.pi*(x-y)):ℝ):ℂ) := by
  rw [ofReal_sin_eq]
  unfold ch
  set a : ℂ := (((2*Real.pi*x:ℝ)):ℂ) * Complex.I / 2 with ha
  set b : ℂ := (((2*Real.pi*y:ℝ)):ℂ) * Complex.I / 2 with hb
  have h2x : (((2*Real.pi*x:ℝ)):ℂ) * Complex.I = 2*a := by rw [ha]; ring
  have h2y : (((2*Real.pi*y:ℝ)):ℂ) * Complex.I = 2*b := by rw [hb]; ring
  have hC : (((2*Real.pi*((x+y)/2):ℝ)):ℂ) * Complex.I = a + b := by rw [ha, hb]; push_cast; ring
  have hD : (((Real.pi*(x-y):ℝ)):ℂ) * Complex.I = a - b := by rw [ha, hb]; push_cast; ring
  have hD' : -((((Real.pi*(x-y):ℝ)):ℂ) * Complex.I) = b - a := by rw [ha, hb]; push_cast; ring
  rw [h2x, h2y, hC, hD', hD]
  rw [show (2:ℂ)*a = a + a by ring, show (2:ℂ)*b = b + b by ring]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_sub, Complex.exp_sub]
  rw [show a + b = a + b from rfl, Complex.exp_add]
  field_simp

private lemma ch_zero' : ch 0 = 1 := by unfold ch; simp

private lemma one_sub_ch_ne (θ : ℝ) (hθ : Real.sin (Real.pi*θ) ≠ 0) : (1 - ch θ) ≠ 0 := by
  intro h
  apply hθ
  have hzero : ch θ = 1 := (sub_eq_zero.mp h).symm
  have key := ch_sub θ 0
  rw [ch_zero', sub_zero, hzero, sub_self] at key
  rw [show (θ+0)/2 = θ/2 by ring] at key
  have hsin0 : ((Real.sin (Real.pi*θ):ℝ):ℂ) = 0 := by
    have h2 : (2:ℂ)*Complex.I*ch (θ/2) = (2*Complex.I)*(ch (θ/2)) := by ring
    rw [h2] at key
    rcases mul_eq_zero.mp key.symm with h1 | h1
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · exact absurd h3 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      · exact absurd h3 (by unfold ch; exact Complex.exp_ne_zero _)
    · exact h1
  exact Complex.ofReal_eq_zero.mp hsin0

private lemma geom_ch2 (θ : ℝ) (N : ℕ) (hθ : Real.sin (Real.pi*θ) ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ)*θ))
      = (ch (((N:ℝ)+1/2)*θ) - ch (θ/2)) / (2*Complex.I*((Real.sin (Real.pi*θ):ℝ):ℂ)) := by
  have hz := one_sub_ch_ne θ hθ
  have hsin : ((Real.sin (Real.pi*θ):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have hgeom := geom_sum_Icc_mul (ch θ) N
  have hS : (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ)*θ)) = ∑ n ∈ Finset.Icc 1 N, (ch θ)^n := by
    refine Finset.sum_congr rfl (fun n _ => ?_); rw [ch_nat_mul]
  rw [hS]
  have hpow : (ch θ)^(N+1) = ch (((N:ℝ)+1)*θ) := by
    rw [← ch_nat_mul]; congr 1; push_cast; ring
  have h1 : ch θ - ch (((N:ℝ)+1)*θ)
      = -2*Complex.I*ch (((N:ℝ)+2)*θ/2)*((Real.sin (Real.pi*((N:ℝ)*θ)):ℝ):ℂ) := by
    rw [ch_sub]
    rw [show (θ + ((N:ℝ)+1)*θ)/2 = (((N:ℝ)+2)*θ/2) by ring,
        show (θ - ((N:ℝ)+1)*θ) = -((N:ℝ)*θ) by ring,
        show Real.pi * -((N:ℝ)*θ) = -(Real.pi * ((N:ℝ)*θ)) by ring, Real.sin_neg, Complex.ofReal_neg]
    ring
  have h2 : 1 - ch θ = -2*Complex.I*ch (θ/2)*((Real.sin (Real.pi*θ):ℝ):ℂ) := by
    rw [show (1:ℂ) = ch 0 from ch_zero'.symm, ch_sub]
    rw [show ((0:ℝ)+θ)/2 = θ/2 by ring, show ((0:ℝ)-θ) = -θ by ring,
        show Real.pi * -θ = -(Real.pi * θ) by ring, Real.sin_neg, Complex.ofReal_neg]
    ring
  have h3 : ch (((N:ℝ)+1/2)*θ) - ch (θ/2)
      = 2*Complex.I*ch (((N:ℝ)+1)*θ/2)*((Real.sin (Real.pi*((N:ℝ)*θ)):ℝ):ℂ) := by
    rw [ch_sub]
    rw [show ((((N:ℝ)+1/2)*θ) + θ/2)/2 = ((N:ℝ)+1)*θ/2 by ring,
        show ((((N:ℝ)+1/2)*θ) - θ/2) = (N:ℝ)*θ by ring]
  rw [eq_div_iff (mul_ne_zero (by norm_num) hsin)]
  refine mul_left_cancel₀ hz ?_
  rw [← mul_assoc, hgeom, hpow]
  rw [h1, h2, h3]
  have hqr : ch (((N:ℝ)+1)*θ/2) * ch (θ/2) = ch (((N:ℝ)+2)*θ/2) := by
    rw [ch_add']; congr 1; ring
  rw [show ((-2:ℂ) * Complex.I * ch (((N:ℝ)+2)*θ/2) * ((Real.sin (Real.pi*((N:ℝ)*θ)):ℝ):ℂ)) * (2 * Complex.I * ((Real.sin (Real.pi*θ):ℝ):ℂ))
        = (-2 * Complex.I * (((Real.sin (Real.pi*((N:ℝ)*θ)):ℝ):ℂ)) * (2*Complex.I*((Real.sin (Real.pi*θ):ℝ):ℂ))) * ch (((N:ℝ)+2)*θ/2) by ring]
  rw [← hqr]
  ring

private lemma sin_ne_zero_of_sep {x δ : ℝ} (hδ : 0 < δ) (hsep : ∀ k : ℤ, δ ≤ |x - k|) :
    Real.sin (Real.pi * x) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  have hxk : x = (k:ℝ) := by
    rw [show (k:ℝ)*Real.pi = Real.pi * (k:ℝ) by ring] at hk
    exact (mul_left_cancel₀ Real.pi_ne_zero hk).symm
  have hh := hsep k
  rw [hxk, sub_self, abs_zero] at hh
  linarith

private lemma norm_mul_ch_eq {ι : Type*} [Fintype ι] (z : ι → ℂ) (c : ι → ℝ) :
    (∑ r, ‖z r * ch (c r)‖ ^ 2) = ∑ r, ‖z r‖ ^ 2 := by
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [norm_mul, norm_ch_eq_one, mul_one]

private lemma wch_mul (zr zs : ℂ) (x y : ℝ) :
    (zr * ch x) * star (zs * ch y) = zr * star zs * ch (x - y) := by
  rw [star_mul]
  rw [show (zr * ch x) * (star (ch y) * star zs) = zr * (ch x * star (ch y)) * star zs by ring]
  rw [ch_mul_star]
  ring

private lemma offdiag_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : ι, r ≠ s → ∀ k : ℤ, δ ≤ |α r - α s - k|) (z : ι → ℂ) (N : ℕ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, z r * star (z s) *
        (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s)))‖ ≤ (1/δ) * ∑ r, ‖z r‖ ^ 2 := by
  set w1 : ι → ℂ := fun r => z r * ch (((N:ℝ)+1/2) * α r) with hw1
  set w2 : ι → ℂ := fun r => z r * ch (α r / 2) with hw2
  set A : ℂ := ∑ r, ∑ s, w1 r * star (w1 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ) with hA
  set B : ℂ := ∑ r, ∑ s, w2 r * star (w2 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ) with hB
  have hU1 : ‖A‖ ≤ (1/δ) * ∑ r, ‖z r‖ ^ 2 := by
    rw [hA]
    have h := cosec_bound α hδ hsep w1
    rw [norm_mul_ch_eq z (fun r => ((N:ℝ)+1/2)*α r)] at h
    exact h
  have hU2 : ‖B‖ ≤ (1/δ) * ∑ r, ‖z r‖ ^ 2 := by
    rw [hB]
    have h := cosec_bound α hδ hsep w2
    rw [norm_mul_ch_eq z (fun r => α r / 2)] at h
    exact h
  have hkey : ∀ r s : ι, r ≠ s →
      z r * star (z s) * (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s)))
        = (1/(2*Complex.I)) * (w1 r * star (w1 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)
            - w2 r * star (w2 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)) := by
    intro r s hrs
    rw [geom_ch2 (α r - α s) N (sin_ne_zero_of_sep hδ (hsep r s hrs))]
    have e1 : (z r * ch (((N:ℝ)+1/2) * α r)) * star (z s * ch (((N:ℝ)+1/2) * α s))
        = z r * star (z s) * ch (((N:ℝ)+1/2) * (α r - α s)) := by
      rw [wch_mul, show ((N:ℝ)+1/2)*α r - ((N:ℝ)+1/2)*α s = ((N:ℝ)+1/2)*(α r - α s) by ring]
    have e2 : (z r * ch (α r / 2)) * star (z s * ch (α s / 2))
        = z r * star (z s) * ch ((α r - α s)/2) := by
      rw [wch_mul, show α r/2 - α s/2 = (α r - α s)/2 by ring]
    rw [hw1, hw2, e1, e2]
    field_simp
  have hAe : A = ∑ r, ∑ s ∈ Finset.univ.erase r,
      w1 r * star (w1 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ) := by
    rw [hA]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ r),
        show (w1 r * star (w1 r) / (((Real.sin (Real.pi*(α r - α r))):ℝ):ℂ)) = 0 by
          rw [sub_self, mul_zero, Real.sin_zero, Complex.ofReal_zero, div_zero], sub_zero]
  have hBe : B = ∑ r, ∑ s ∈ Finset.univ.erase r,
      w2 r * star (w2 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ) := by
    rw [hB]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ r),
        show (w2 r * star (w2 r) / (((Real.sin (Real.pi*(α r - α r))):ℝ):ℂ)) = 0 by
          rw [sub_self, mul_zero, Real.sin_zero, Complex.ofReal_zero, div_zero], sub_zero]
  have hOff1 : (∑ r, ∑ s ∈ Finset.univ.erase r, z r * star (z s) *
        (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s))))
      = ∑ r, ∑ s ∈ Finset.univ.erase r,
          (1/(2*Complex.I)) * (w1 r * star (w1 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)
            - w2 r * star (w2 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)) := by
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s hs => ?_))
    rw [Finset.mem_erase] at hs
    exact hkey r s hs.1.symm
  have hOff2 : (1/(2*Complex.I)) * (A - B) = ∑ r, ∑ s ∈ Finset.univ.erase r,
          (1/(2*Complex.I)) * (w1 r * star (w1 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)
            - w2 r * star (w2 s) / (((Real.sin (Real.pi*(α r - α s))):ℝ):ℂ)) := by
    rw [hAe, hBe, mul_sub]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [hOff1, ← hOff2, norm_mul]
  have hnormC : ‖(1/(2*Complex.I) : ℂ)‖ = 1/2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  rw [hnormC]
  calc (1/2 : ℝ) * ‖A - B‖ ≤ (1/2) * (‖A‖ + ‖B‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le A B) (by norm_num)
    _ ≤ (1/2) * ((1/δ) * ∑ r, ‖z r‖ ^ 2 + (1/δ) * ∑ r, ‖z r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hU1 hU2) (by norm_num)
    _ = (1/δ) * ∑ r, ‖z r‖ ^ 2 := by ring

private lemma normSq_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]
  rfl

theorem large_sieve {ι : Type*} [Fintype ι] (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s : ι, r ≠ s → ∀ k : ℤ, δ ≤ |α r - α s - k|)
    (N : ℕ) (a : ℕ → ℂ) :
    (∑ r : ι, ‖∑ n ∈ Finset.Icc 1 N, a n * ch (n * α r)‖ ^ 2)
      ≤ (N + 1 / δ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
  classical
  have hdual : ∀ z : ι → ℂ,
      (∑ n ∈ Finset.Icc 1 N, ‖∑ r, z r * ch ((n:ℝ) * α r)‖ ^ 2)
        ≤ (N + 1/δ) * ∑ r, ‖z r‖ ^ 2 := by
    intro z
    have hexp : (((∑ n ∈ Finset.Icc 1 N, ‖∑ r, z r * ch ((n:ℝ) * α r)‖ ^ 2) : ℝ) : ℂ)
        = ∑ r, ∑ s, z r * star (z s) *
            (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s))) := by
      rw [Complex.ofReal_sum]
      calc (∑ n ∈ Finset.Icc 1 N, (((‖∑ r, z r * ch ((n:ℝ) * α r)‖ ^ 2 : ℝ)) : ℂ))
          = ∑ n ∈ Finset.Icc 1 N, ∑ r, ∑ s,
              z r * star (z s) * ch ((n:ℝ) * (α r - α s)) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [normSq_cast, star_sum, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
            rw [wch_mul, show (n:ℝ)*α r - (n:ℝ)*α s = (n:ℝ)*(α r - α s) by ring]
        _ = ∑ r, ∑ s, z r * star (z s) *
            (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s))) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun r _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [Finset.mul_sum]
    have hnorm : (∑ n ∈ Finset.Icc 1 N, ‖∑ r, z r * ch ((n:ℝ) * α r)‖ ^ 2)
        = ‖∑ r, ∑ s, z r * star (z s) *
            (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s)))‖ := by
      have h := congrArg norm hexp
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
      exact h
    rw [hnorm]
    have hdiag : ∀ r : ι, z r * star (z r) * (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α r)))
        = ((N:ℕ) : ℂ) * ((‖z r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      rw [sub_self, show (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * 0)) = ((N:ℕ):ℂ) by
            simp [mul_zero, ch_zero']]
      rw [normSq_cast]; ring
    have hsplit : (∑ r, ∑ s, z r * star (z s) * (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s))))
        = (∑ r, ((N:ℕ):ℂ) * ((‖z r‖^2 : ℝ):ℂ))
          + ∑ r, ∑ s ∈ Finset.univ.erase r, z r * star (z s) * (∑ n ∈ Finset.Icc 1 N, ch ((n:ℝ) * (α r - α s))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      congr 1
      exact hdiag r
    rw [hsplit]
    have hDnorm : ‖∑ r, ((N:ℕ):ℂ) * ((‖z r‖^2 : ℝ):ℂ)‖ = (N:ℝ) * ∑ r, ‖z r‖^2 := by
      rw [show (∑ r, ((N:ℕ):ℂ) * ((‖z r‖^2 : ℝ):ℂ)) = ((N:ℕ):ℂ) * ((∑ r, ‖z r‖^2 : ℝ):ℂ) by
            rw [Complex.ofReal_sum, Finset.mul_sum]]
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
    refine (norm_add_le _ _).trans ?_
    rw [hDnorm]
    have hoff := offdiag_bound α hδ hsep z N
    linarith [hoff]
  -- duality
  set S : ι → ℂ := fun r => ∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * α r) with hS
  set c : ℕ → ℂ := fun n => ∑ r, star (S r) * ch ((n:ℝ) * α r) with hc
  have hPc : ((∑ r, ‖S r‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ Finset.Icc 1 N, a n * c n := by
    simp only [hc]
    rw [Complex.ofReal_sum]
    rw [show (∑ n ∈ Finset.Icc 1 N, a n * ∑ r, star (S r) * ch ((n:ℝ) * α r))
        = ∑ n ∈ Finset.Icc 1 N, ∑ r, a n * (star (S r) * ch ((n:ℝ) * α r)) by
          refine Finset.sum_congr rfl (fun n _ => ?_); rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [normSq_cast, hS, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  have hP : (∑ r, ‖S r‖ ^ 2) = ‖∑ n ∈ Finset.Icc 1 N, a n * c n‖ := by
    have h := congrArg norm hPc
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h
  have hcbound : (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2) ≤ (N + 1/δ) * ∑ r, ‖S r‖ ^ 2 := by
    simp only [hc]
    have h := hdual (fun r => star (S r))
    rw [show (∑ r, ‖star (S r)‖ ^ 2) = ∑ r, ‖S r‖ ^ 2 by simp] at h
    exact h
  have hgoal : (∑ r, ‖S r‖ ^ 2) ≤ (N + 1/δ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
    have hPnn : (0:ℝ) ≤ ∑ r, ‖S r‖ ^ 2 := by positivity
    by_cases hP0 : (∑ r, ‖S r‖ ^ 2) = 0
    · rw [hP0]; positivity
    · have hPpos : 0 < ∑ r, ‖S r‖ ^ 2 := lt_of_le_of_ne hPnn (Ne.symm hP0)
      have hsq : (∑ r, ‖S r‖ ^ 2) ^ 2 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2) := by
        have h1 : ‖∑ n ∈ Finset.Icc 1 N, a n * c n‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * ‖c n‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum (fun n _ => by rw [norm_mul])
        have h2 : (∑ n ∈ Finset.Icc 1 N, ‖a n‖ * ‖c n‖) ^ 2 ≤
            (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        rw [hP]
        exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
      have hfin : (∑ r, ‖S r‖ ^ 2) ^ 2 ≤
          ((N + 1/δ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) * (∑ r, ‖S r‖ ^ 2) := by
        refine hsq.trans ?_
        calc (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * (∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2)
            ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * ((N + 1/δ) * ∑ r, ‖S r‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hcbound (by positivity)
          _ = ((N + 1/δ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) * (∑ r, ‖S r‖ ^ 2) := by ring
      rw [sq] at hfin
      exact le_of_mul_le_mul_right hfin hPpos
  rw [hS] at hgoal
  exact hgoal

end Commons.Analysis.ExponentialSums
