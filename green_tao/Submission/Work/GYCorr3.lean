import Submission.Work.GYCorr2
import Submission.Work.GYFactor8

/-!
# Green–Tao §9 (Proposition GY2) for the degenerate system: the §10 machinery

This file transplants the §10 Euler-product/contour-integral analysis (`GYFactor6`–`GYFactor8`)
to the *correlation* system `θ_i(x) = W(x + h_i) + 1` of Green–Tao's Proposition GY2.  The only
inputs that change are the majorant (`e1pMajorCorr` instead of `e1pMajor`) and the fact that the
`LocHyp` bundle is unavailable (the linear parts are proportional); everything else is copied with
`LocHyp`-hypotheses replaced by the explicit `1 ≤ m`, `0 < W`, `Delta h ≠ 0`.

The main result is `mainSum_eq_logR_corr`: the box-average main term of
`∏_{i} Λ_R(W(x+h_i)+1)²` equals `G'₁(0,0)G'₂(0,0)(log R)^a` up to Green–Tao's error, where the
arithmetic factor `∏_{p | Δ}(1 + O_m(p^{-1/2}))` is built into `G'₁(0,0)`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {m : ℕ}

/-! ## 1. `G₂` -/

lemma multipliable_E2p_corr {W : ℕ} (hW0 : 0 < W) (z z' : Fin m → ℂ) :
    Multipliable (fun n : ℕ => E2p W z z' n) := by
  have h : ∀ᶠ n : ℕ in Filter.atTop, ‖(E2p W z z' n - 1 : ℂ)‖ ≤ (0 : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨W + 1, fun n hn => ?_⟩
    have hnd : ¬ n ∣ W := fun hd => by
      have := Nat.le_of_dvd hW0 hd
      omega
    rw [E2p, if_neg (fun hc => hnd hc.2), sub_self, norm_zero]
  exact (multipliable_one_add_of_summable
    (Summable.of_norm_bounded_eventually_nat (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
      h).norm).congr (fun n => by ring)

lemma G2u_eq_prod_corr {W : ℕ} (hW0 : 0 < W) (z z' : Fin m → ℂ) :
    G2u W z z' = ∏ n ∈ W.divisors, E2p W z z' n := by
  rw [G2u]
  refine tprod_eq_prod (s := W.divisors) (fun n hn => ?_)
  have hnd : ¬ n ∣ W := by
    intro hd
    exact hn (Nat.mem_divisors.mpr ⟨hd, ne_of_gt hW0⟩)
  rw [E2p, if_neg (fun hc => hnd hc.2)]

lemma norm_E2p_le_corr {W : ℕ} (hm : 1 ≤ m) (n : ℕ) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E2p W z z' n‖ ≤ (32 : ℝ) ^ m := by
  by_cases hc : n.Prime ∧ n ∣ W
  · rw [E2p, if_pos hc, norm_prod]
    have hperj : ∀ j : Fin m, ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖ ≤ 32 := by
      intro j
      rw [norm_mul, norm_mul]
      have hA := norm_inv_one_sub_cpow_le (n := n) hc.1 (w := z j) (le_neg_half_of hm hz)
      have hB := norm_inv_one_sub_cpow_le (n := n) hc.1 (w := z' j) (le_neg_half_of hm hz')
      have hC : ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))‖ ≤ 2 := by
        have h := norm_one_sub_cpow_le (n := n) hc.1 (w := z j + z' j)
          (le_neg_half_add hm hz hz')
        rwa [show (-(1 + (z j + z' j)) : ℂ) = -(1 + z j + z' j) by ring] at h
      calc ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹‖
            * ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹‖
            * ‖(1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))‖
          ≤ 4 * 4 * 2 :=
            mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by norm_num)) hC (norm_nonneg _)
              (by norm_num)
        _ ≤ 32 := by norm_num
    have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun j : Fin m => ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
        * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))‖)
      (g := fun _ : Fin m => (32 : ℝ)) (fun j _ => norm_nonneg _) (fun j _ => hperj j)
    simpa [Finset.prod_const, Finset.card_univ] using h
  · rw [E2p, if_neg hc, norm_one]
    exact one_le_pow₀ (by norm_num)

lemma continuousOn_E2p_pair_corr {W : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E2p W x.1 x.2 n)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  by_cases hn : n.Prime
  · exact continuousOn_E2p_comp hn (fun i => continuousOn_fst_coord _ i)
      (fun i => continuousOn_snd_coord _ i) (fun x hx i => goodRegion_half hm hx i)
  · rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E2p W x.1 x.2 n) = fun _ => (1 : ℂ) by
      funext x; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
    exact continuousOn_const

lemma continuousOn_G2c {W : ℕ} (hm : 1 ≤ m) (hW0 : 0 < W) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G2u W x.1 x.2)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G2u W x.1 x.2)
      = fun x => ∏ n ∈ W.divisors, E2p W x.1 x.2 n by
    funext x; exact G2u_eq_prod_corr hW0 x.1 x.2]
  exact continuousOn_finsetProd' _ fun n _ => continuousOn_E2p_pair_corr hm n

lemma differentiableAt_G2c_curve₁ {W : ℕ} (hm : 1 ≤ m) (hW0 : 0 < W)
    {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G2u W (Function.update z j u) z') (z j) := by
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun u : ℂ => G2u W (Function.update z j u) z')
      {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := by
    rw [show (fun u : ℂ => G2u W (Function.update z j u) z')
        = fun u => ∏ n ∈ W.divisors, E2p W (Function.update z j u) z' n by
      funext u; exact G2u_eq_prod_corr hW0 _ _]
    refine differentiableOn_finsetProd' _ fun n _ => ?_
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z j i).mono (Set.subset_univ _)
      have h2 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z' i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z' i)
      refine differentiableOn_E2p_comp (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn
        h1 h2 ?_
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six hm) (update_re_gt hz hu i),
        lt_trans (neg_half_lt_neg_inv_six hm) (hz' i)⟩
    · rw [show (fun u : ℂ => E2p W (Function.update z j u) z' n) = fun _ : ℂ => (1 : ℂ) by
        funext u; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
      exact (differentiableOn_const (c := (1 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
  exact hd.differentiableAt (hs.mem_nhds (hz j))

lemma differentiableAt_G2c_curve₂ {W : ℕ} (hm : 1 ≤ m) (hW0 : 0 < W)
    {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G2u W z (Function.update z' j u)) (z' j) := by
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun u : ℂ => G2u W z (Function.update z' j u))
      {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} := by
    rw [show (fun u : ℂ => G2u W z (Function.update z' j u))
        = fun u => ∏ n ∈ W.divisors, E2p W z (Function.update z' j u) n by
      funext u; exact G2u_eq_prod_corr hW0 _ _]
    refine differentiableOn_finsetProd' _ fun n _ => ?_
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z i)
      have h2 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z' j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _)
      refine differentiableOn_E2p_comp (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn
        h1 h2 ?_
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six hm) (hz i),
        lt_trans (neg_half_lt_neg_inv_six hm) (update_re_gt hz' hu i)⟩
    · rw [show (fun u : ℂ => E2p W z (Function.update z' j u) n) = fun _ : ℂ => (1 : ℂ) by
        funext u; rw [E2p, if_neg (fun hc : n.Prime ∧ n ∣ W => hn hc.1)]]
      exact (differentiableOn_const (c := (1 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
  exact hd.differentiableAt (hs.mem_nhds (hz' j))

lemma norm_G2c_le {W : ℕ} (hm : 1 ≤ m) (hW0 : 0 < W) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖G2u W z z'‖ ≤ (32 : ℝ) ^ (m * W.divisors.card) := by
  rw [G2u_eq_prod_corr hW0 z z', norm_prod]
  have h := Finset.prod_le_prod (s := W.divisors) (f := fun n => ‖E2p W z z' n‖)
    (g := fun _ => (32 : ℝ) ^ m) (fun n _ => norm_nonneg _)
    (fun n _ => norm_E2p_le_corr hm n hz hz')
  calc ∏ n ∈ W.divisors, ‖E2p W z z' n‖ ≤ ∏ _n ∈ W.divisors, (32 : ℝ) ^ m := h
    _ = ((32 : ℝ) ^ m) ^ W.divisors.card := by rw [Finset.prod_const]
    _ = (32 : ℝ) ^ (m * W.divisors.card) := by rw [← pow_mul]

/-! ## 2. `G₁` -/

lemma summable_E1p_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) < (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) < (z' j).re) :
    Summable (fun n : ℕ => ‖E1p W (Ac m) h z z' n - 1‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_e1pMajorCorr hm hΔ0)
  exact E1p_sub_one_le_major_corr hm hW0 hΔ0 n (fun j => le_of_lt (hz j))
    (fun j => le_of_lt (hz' j))

lemma multipliable_E1p_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) < (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) < (z' j).re) :
    Multipliable (fun n : ℕ => E1p W (Ac m) h z z' n) :=
  (multipliable_one_add_of_summable (summable_E1p_corr hm hW0 hΔ0 hz hz')).congr
    (fun n => by ring)

/-- **Green–Tao (10.8) + (10.9) for the degenerate system.** -/
theorem tprod_eulerFactor_eq_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ} (hz : ∀ j, 1 < (z j).re)
    (hz' : ∀ j, 1 < (z' j).re) :
    (∏' p : ℕ, eulerFactor m (BoxAvg.vSys W (Ac m) h) z z' p)
      = G1u W (Ac m) h z z' * G2u W z z' * G3R z z' := by
  have hpt : ∀ p : ℕ, eulerFactor m (BoxAvg.vSys W (Ac m) h) z z' p
      = E1p W (Ac m) h z z' p * E2p W z z' p * E3p z z' p := fun p =>
    eulerFactor_eq_E1p_mul_E2p_mul_E3p_corr (σ₀ := 1 / 4) (by norm_num)
      (z := z) (z' := z') (fun j => by linarith [hz j]) (fun j => by linarith [hz' j]) p
  have hpos := sixth_pos hm
  have hM1 : Multipliable (fun p : ℕ => E1p W (Ac m) h z z' p) :=
    multipliable_E1p_corr hm hW0 hΔ0 (fun j => by linarith [hz j, hpos])
      (fun j => by linarith [hz' j, hpos])
  have hM2 : Multipliable (fun p : ℕ => E2p W z z' p) := multipliable_E2p_corr hW0 z z'
  have h3 := Commons.NumberTheory.Zeta.hasProd_E3_eq_zeta_ratio m z z'
    (fun j => by linarith [hz j]) (fun j => by linarith [hz' j])
  have hres : HasProd (fun p : ℕ => E1p W (Ac m) h z z' p * E2p W z z' p * E3p z z' p)
      (G1u W (Ac m) h z z' * G2u W z z' * G3R z z') :=
    (hM1.hasProd.mul hM2.hasProd).mul h3
  exact (hres.congr_fun (fun p => (hpt p))).tprod_eq

lemma continuousOn_E1p_pair_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (n : ℕ) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E1p W (Ac m) h x.1 x.2 n)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  by_cases hn : n.Prime
  · exact continuousOn_E1p_comp (W := W) (A := Ac m) (b := h) hn
      (fun i => continuousOn_fst_coord _ i) (fun i => continuousOn_snd_coord _ i)
      (fun x hx i => goodRegion_half hm hx i)
  · rw [show (fun x : (Fin m → ℂ) × (Fin m → ℂ) => E1p W (Ac m) h x.1 x.2 n)
        = fun _ => (1 : ℂ) by
      funext x; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1)]]
    exact continuousOn_const

lemma continuousOn_G1c {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G1u W (Ac m) h x.1 x.2)
      (goodRegion m (-(1 / (6 * (m : ℝ))))) := by
  have hfun : (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G1u W (Ac m) h x.1 x.2)
      = fun x => ∏' n : ℕ, (1 + (E1p W (Ac m) h x.1 x.2 n - 1)) := by
    funext x; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  refine Commons.Analysis.Complex.continuousOn_tprod_one_add_nat (isOpen_goodRegion m _)
    (summable_e1pMajorCorr hm hΔ0) ?_ ?_
  · exact Filter.Eventually.of_forall fun n x hx =>
      E1p_sub_one_le_major_corr hm hW0 hΔ0 n (fun i => le_of_lt (hx.1 i))
        (fun i => le_of_lt (hx.2 i))
  · intro n
    exact (continuousOn_E1p_pair_corr hm n).sub continuousOn_const

lemma differentiableAt_G1c_curve₁ {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G1u W (Ac m) h (Function.update z j u) z') (z j) := by
  have hfun : (fun u : ℂ => G1u W (Ac m) h (Function.update z j u) z')
      = fun u => ∏' n : ℕ, (1 + (E1p W (Ac m) h (Function.update z j u) z' n - 1)) := by
    funext u; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := Commons.Analysis.Complex.differentiableOn_tprod_one_add_nat
    (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
    (f := fun n u => E1p W (Ac m) h (Function.update z j u) z' n - 1)
    hs (summable_e1pMajorCorr hm hΔ0) ?_ ?_
  · exact hd.differentiableAt (hs.mem_nhds (hz j))
  · exact Filter.Eventually.of_forall fun n u hu =>
      E1p_sub_one_le_major_corr hm hW0 hΔ0 n (fun i => le_of_lt (update_re_gt hz hu i))
        (fun i => le_of_lt (hz' i))
  · intro n
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z j i).mono (Set.subset_univ _)
      have h2 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z' i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z' i)
      refine (differentiableOn_E1p_comp (W := W) (A := Ac m) (b := h)
        (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn h1 h2 ?_).sub
        (differentiableOn_const (c := (1 : ℂ)))
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six hm) (update_re_gt hz hu i),
        lt_trans (neg_half_lt_neg_inv_six hm) (hz' i)⟩
    · rw [show (fun u : ℂ => E1p W (Ac m) h (Function.update z j u) z' n - 1)
          = fun _ : ℂ => (0 : ℂ) by
        funext u; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self]]
      exact (differentiableOn_const (c := (0 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})

lemma differentiableAt_G1c_curve₂ {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re)
    (hz' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re) :
    DifferentiableAt ℂ (fun u : ℂ => G1u W (Ac m) h z (Function.update z' j u)) (z' j) := by
  have hfun : (fun u : ℂ => G1u W (Ac m) h z (Function.update z' j u))
      = fun u => ∏' n : ℕ, (1 + (E1p W (Ac m) h z (Function.update z' j u) n - 1)) := by
    funext u; rw [G1u]; exact tprod_congr (fun n => by ring)
  rw [hfun]
  have hs : IsOpen {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := Commons.Analysis.Complex.differentiableOn_tprod_one_add_nat
    (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})
    (f := fun n u => E1p W (Ac m) h z (Function.update z' j u) n - 1)
    hs (summable_e1pMajorCorr hm hΔ0) ?_ ?_
  · exact hd.differentiableAt (hs.mem_nhds (hz' j))
  · exact Filter.Eventually.of_forall fun n u hu =>
      E1p_sub_one_le_major_corr hm hW0 hΔ0 n (fun i => le_of_lt (hz i))
        (fun i => le_of_lt (update_re_gt hz' hu i))
  · intro n
    by_cases hn : n.Prime
    · have h1 : ∀ i, DifferentiableOn ℂ (fun _ : ℂ => z i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => differentiableOn_const (c := z i)
      have h2 : ∀ i, DifferentiableOn ℂ (fun u : ℂ => Function.update z' j u i)
          {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re} :=
        fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _)
      refine (differentiableOn_E1p_comp (W := W) (A := Ac m) (b := h)
        (s := {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re}) hn h1 h2 ?_).sub
        (differentiableOn_const (c := (1 : ℂ)))
      intro u hu i
      exact ⟨lt_trans (neg_half_lt_neg_inv_six hm) (hz i),
        lt_trans (neg_half_lt_neg_inv_six hm) (update_re_gt hz' hu i)⟩
    · rw [show (fun u : ℂ => E1p W (Ac m) h z (Function.update z' j u) n - 1)
          = fun _ : ℂ => (0 : ℂ) by
        funext u; rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self]]
      exact (differentiableOn_const (c := (0 : ℂ)) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u : ℂ | -(1 / (6 * (m : ℝ))) < u.re})

lemma norm_G1c_le {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖G1u W (Ac m) h z z'‖ ≤ Real.exp (∑' n : ℕ, e1pMajorCorr (Delta h) m n) := by
  have hsum : Summable (fun n : ℕ => ‖E1p W (Ac m) h z z' n - 1‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_e1pMajorCorr hm hΔ0)
    exact E1p_sub_one_le_major_corr hm hW0 hΔ0 n hz hz'
  rw [show G1u W (Ac m) h z z' = ∏' n : ℕ, (1 + (E1p W (Ac m) h z z' n - 1)) by
    rw [G1u]; exact tprod_congr (fun n => by ring)]
  refine le_trans (Commons.Analysis.Complex.norm_tprod_one_add_le_exp _ hsum) ?_
  refine Real.exp_le_exp.mpr ?_
  exact hsum.tsum_le_tsum (fun n => E1p_sub_one_le_major_corr hm hW0 hΔ0 n hz hz')
    (summable_e1pMajorCorr hm hΔ0)

/-- The uniform bound `B` of Green–Tao Lemma 10.4 for the correlation system. -/
noncomputable def stripBoundCorr (D W m : ℕ) : ℝ :=
  Real.exp (∑' n : ℕ, e1pMajorCorr D m n) * (32 : ℝ) ^ (m * W.divisors.card)

/-! ## 3. Green–Tao Lemma 10.4 for `F = G'₁G₂` -/

/-- **Green–Tao Lemma 10.4 for the correlation system.** -/
theorem zetaBound_G1G2_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ R : ℝ, 3 ≤ R →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
        (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
          (G1u W (Ac m) h (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
          * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
              + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m)
        - (G1u W (Ac m) h 0 0 * G2u (m := m) W 0 0) * (Real.log R) ^ m‖
      ≤ C ^ m * stripBoundCorr (Delta h) W m * (1 + (Real.log R) ^ (m - 1))
        + C ^ m * stripBoundCorr (Delta h) W m * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨δ, C, hδ, hC, Hmain⟩ := Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm
  refine ⟨δ, C, hδ, hC, fun R hR => ?_⟩
  refine Hmain R hR (fun z z' => G1u W (Ac m) h z z' * G2u W z z')
    (stripBoundCorr (Delta h) W m) ?_ ?_ ?_ ?_ ?_
  · unfold stripBoundCorr; positivity
  · exact ((continuousOn_G1c hm hW0 hΔ0).mul (continuousOn_G2c hm hW0)).mono
      (fun x hx => ⟨fun i => (hx.1 i).1, fun i => (hx.2 i).1⟩)
  · intro j z z' hz hz'
    exact (differentiableAt_G1c_curve₁ hm hW0 hΔ0 (fun i => (hz i).1)
        (fun i => (hz' i).1)).mul
      (differentiableAt_G2c_curve₁ hm hW0 (fun i => (hz i).1) (fun i => (hz' i).1))
  · intro j z z' hz hz'
    exact (differentiableAt_G1c_curve₂ hm hW0 hΔ0 (fun i => (hz i).1)
        (fun i => (hz' i).1)).mul
      (differentiableAt_G2c_curve₂ hm hW0 (fun i => (hz i).1) (fun i => (hz' i).1))
  · intro z z' hz hz'
    rw [norm_mul]
    exact mul_le_mul (norm_G1c_le hm hW0 hΔ0 (fun i => le_of_lt (hz i).1)
        (fun i => le_of_lt (hz' i).1))
      (norm_G2c_le hm hW0 (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
      (norm_nonneg _) (Real.exp_nonneg _)

end Corr
end GYMaj
