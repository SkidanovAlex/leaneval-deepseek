import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixR.LatGreen.HeatIntegral
import Submission.Work.BoseFixR.LatGreen.PoissonGauss1D
import Submission.Work.BoseFixR.LatGreen.SmallTMajorant
import Submission.Work.BoseFixR.LatGreen.TailMajorant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.MadelungBound` — the Madelung bound for the `ℤ³` lattice Green's
function with a neutralising background

The target is the inequality

`h(u) = G(u) − 1/(4π‖u‖) ≤ 1/(2π‖u‖)`   (`u ≠ 0`, `∀ i, |u i| ≤ 1/2`),

where `G = latGreen` is the `ℤ³`-lattice Coulomb Green's function with the neutralising
background, defined through its absolutely convergent theta (heat kernel) representation

`G(u) = ∫_0^∞ (Σ_{n∈ℤ³} p_t(u − n) − 1) dt`,  `p_t(x) = (4πt)^{-3/2} e^{−‖x‖²/(4t)}`.

## The Ewald splitting

The proof splits the `t`-integral at `η = etaZ = 1/32` (`md_smallT_pointwise`, `md_tail_pointwise`):

* **short times** `t ≤ η`: the lattice sum is dominated by the *direct Gaussian* bound
  `heatPeriod t u − heatK3 t u ≤ (4πt)^{-3/2} ((1 + tauZ t)³ − 1)`, obtained from the factorisation
  of the periodised heat kernel into three one-dimensional periodised kernels
  (`md_heatPeriod_eq_prod`) together with the elementary bound `md_heatK1_tsum_le`; its integral
  over `(0, η]` is at most `1/12` (`SmallTMajorant`).  The heat kernel itself contributes exactly
  `∫_0^∞ p_t(x) dt = 1/(4π‖x‖)` (`HeatIntegral`), which cancels against the singular part of `h`.
* **long times** `t ≥ η`: Poisson/Jacobi summation in one dimension (`PoissonGauss1D`) turns the
  periodised kernel into its Fourier series, whose tail is bounded two-sidedly by
  `rhoZ t = 2 Σ_{j≥1} e^{−4π²tj²}`; the resulting majorant has integral at most `1/14`
  (`TailMajorant`).

The ledger is therefore (`η = 1/32`)

`latGreen u ≤ 1/12 + 1/14 + 1/(4π‖u‖) − η`,   hence
`latGreenSmooth u ≤ 13/84 − 1/32 ≤ 1/(2π‖u‖)`,

the last inequality using `‖u‖ ≤ √3/2` (from the half-cell hypothesis) and `π < 3.15`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma md_summable_heatK1 {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun m : ℤ => heatK1 t (y - m)) := by
  have hc : (0 : ℝ) < 1 / (8 * t) := by positivity
  refine Summable.of_nonneg_of_le (fun m => heatK1_nonneg ht _) (fun m => ?_)
    (Summable.mul_left ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (y ^ 2 / (4 * t)))
      (summable_exp_neg_mul_sq_int hc))
  rw [heatK1]
  have h1 : -((y - (m : ℝ)) ^ 2) / (4 * t) ≤ y ^ 2 / (4 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2 := by
    have hpos : 0 < 4 * t := by positivity
    rw [div_le_iff₀ hpos]
    have h4 : (y ^ 2 / (4 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2) * (4 * t)
        = y ^ 2 - (m : ℝ) ^ 2 / 2 := by
      field_simp
      ring
    rw [h4]
    nlinarith [sq_nonneg ((m : ℝ) - 2 * y)]
  calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((y - (m : ℝ)) ^ 2) / (4 * t))
      ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
          * Real.exp (y ^ 2 / (4 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (Real.rpow_nonneg (by positivity) _)
    _ = ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (y ^ 2 / (4 * t)))
          * Real.exp (-(1 / (8 * t)) * (m : ℝ) ^ 2) := by
        have he : Real.exp (y ^ 2 / (4 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2)
            = Real.exp (y ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * (m : ℝ) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [he]; ring

lemma md_summable_gauss {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun m : ℤ => Real.exp (-((y - (m : ℝ)) ^ 2) / (4 * t))) := by
  have h := Summable.mul_left ((4 * Real.pi * t) ^ (1 / 2 : ℝ)) (md_summable_heatK1 ht y)
  refine h.congr fun m => ?_
  simp only [heatK1]
  rw [← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi * t)]
  norm_num

lemma md_sq_tail {t : ℝ} (_ht : 0 < t) {x : ℝ} (hx : |x| ≤ 1 / 2) {m : ℤ} (hm : m ≠ 0) :
    (|((m : ℤ) : ℝ)| - 1 / 2) ^ 2 ≤ (x - (m : ℝ)) ^ 2 := by
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have habs : |((m : ℤ) : ℝ)| - 1 / 2 ≤ |x - (m : ℝ)| := by
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have hm1 : ((m : ℤ) : ℝ) ≤ -1 := by
        have : m ≤ -1 := by omega
        exact_mod_cast this
      have h1 : |((m : ℤ) : ℝ)| = -((m : ℤ) : ℝ) := abs_of_neg (by linarith)
      rw [h1]
      have h2 : 0 ≤ x - (m : ℝ) := by linarith
      rw [abs_of_nonneg h2]
      linarith
    · have hm1 : (1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ m := by omega
        exact_mod_cast this
      have h1 : |((m : ℤ) : ℝ)| = ((m : ℤ) : ℝ) := abs_of_pos (by linarith)
      rw [h1]
      have h2 : x - (m : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos h2]
      linarith
  have h0 : 0 ≤ |((m : ℤ) : ℝ)| - 1 / 2 := by
    have hm1 : (1 : ℝ) ≤ |((m : ℤ) : ℝ)| := by
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have h3 : ((m : ℤ) : ℝ) ≤ -1 := by
          have : m ≤ -1 := by omega
          exact_mod_cast this
        rw [abs_of_neg (by linarith)]; linarith
      · have h3 : (1 : ℝ) ≤ ((m : ℤ) : ℝ) := by
          have : (1 : ℤ) ≤ m := by omega
          exact_mod_cast this
        rw [abs_of_pos (by linarith)]; linarith
    linarith
  have hs := mul_self_le_mul_self h0 habs
  simpa only [pow_two, ← sq_abs (x - (m : ℝ))] using hs

lemma md_gauss_tail_le {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (∑' m : ℤ, if m = 0 then 0 else Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t))) ≤ tauZ t := by
  have hpt : ∀ m : ℤ,
      (if m = 0 then 0 else Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t))) ≤ WZ t m := by
    intro m
    rcases eq_or_ne m 0 with hm | hm
    · rw [hm, if_pos rfl, WZ_zero]
    · rw [if_neg hm, WZ_apply_of_ne hm]
      refine Real.exp_le_exp.mpr ?_
      have hpos : 0 < 4 * t := by positivity
      exact div_le_div_of_nonneg_right (neg_le_neg (md_sq_tail ht hx hm)) (le_of_lt hpos)
  have hsum : Summable (fun m : ℤ =>
      if m = 0 then 0 else Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t))) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) hpt (summable_WZ ht)
    rcases eq_or_ne m 0 with hm | hm
    · rw [hm, if_pos rfl]
    · rw [if_neg hm]; exact Real.exp_nonneg _
  rw [← tsum_WZ ht]
  exact Summable.tsum_le_tsum hpt hsum (summable_WZ ht)

lemma md_heatK1_tsum_le {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (∑' m : ℤ, heatK1 t (x - m)) ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (1 + tauZ t) := by
  have hsumg := md_summable_gauss ht x
  have hsplit := Summable.tsum_eq_add_tsum_ite hsumg 0
  have hfact : (∑' m : ℤ, heatK1 t (x - m))
      = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * ∑' m : ℤ, Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [heatK1]
  rw [hfact, hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  have h0 : Real.exp (-((x - ((0 : ℤ) : ℝ)) ^ 2) / (4 * t)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    rw [show -((x - ((0 : ℤ) : ℝ)) ^ 2) / (4 * t) = -(x ^ 2 / (4 * t)) by ring]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg x) (by positivity))
  have htail := md_gauss_tail_le ht hx
  linarith

/-! ## The product decomposition of the periodised heat kernel -/

lemma md_tsum_fin3_mul (F0 F1 F2 : ℤ → ℝ)
    (h0n : ∀ a, 0 ≤ F0 a) (h1n : ∀ a, 0 ≤ F1 a) (h2n : ∀ a, 0 ≤ F2 a)
    (h0 : Summable F0) (h1 : Summable F1) (h2 : Summable F2) :
    (∑' n : Fin 3 → ℤ, F0 (n 0) * F1 (n 1) * F2 (n 2))
      = (∑' a, F0 a) * (∑' b, F1 b) * (∑' c, F2 c) := by
  have h12 : Summable (fun p : ℤ × ℤ => F1 p.1 * F2 p.2) := by
    refine (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => F1 p.1 * F2 p.2)
      (fun p => mul_nonneg (h1n _) (h2n _))).mpr ⟨fun a => ?_, ?_⟩
    · exact Summable.mul_left (F1 a) h2
    · have hcongr : (fun x : ℤ => ∑' y : ℤ, F1 x * F2 y)
          = fun x : ℤ => F1 x * (∑' y : ℤ, F2 y) := by
        funext x
        exact tsum_mul_left
      rw [hcongr]
      exact Summable.mul_right (∑' y : ℤ, F2 y) h1
  have h012 : Summable (fun p : ℤ × (ℤ × ℤ) => F0 p.1 * (F1 p.2.1 * F2 p.2.2)) := by
    refine (summable_prod_of_nonneg (f := fun p : ℤ × (ℤ × ℤ) =>
      F0 p.1 * (F1 p.2.1 * F2 p.2.2))
      (fun p => mul_nonneg (h0n _) (mul_nonneg (h1n _) (h2n _)))).mpr ⟨fun a => ?_, ?_⟩
    · exact Summable.mul_left (F0 a) h12
    · have hcongr : (fun x : ℤ => ∑' q : ℤ × ℤ, F0 x * (F1 q.1 * F2 q.2))
          = fun x : ℤ => F0 x * (∑' q : ℤ × ℤ, F1 q.1 * F2 q.2) := by
        funext x
        exact tsum_mul_left
      rw [hcongr]
      exact Summable.mul_right (∑' q : ℤ × ℤ, F1 q.1 * F2 q.2) h0
  calc (∑' n : Fin 3 → ℤ, F0 (n 0) * F1 (n 1) * F2 (n 2))
      = ∑' n : Fin 3 → ℤ, F0 (n 0) * (F1 (n 1) * F2 (n 2)) :=
        tsum_congr fun n => by ring
    _ = ∑' p : ℤ × (ℤ × ℤ), F0 p.1 * (F1 p.2.1 * F2 p.2.2) :=
        Equiv.tsum_eq piFinThreeEquiv (fun p : ℤ × (ℤ × ℤ) => F0 p.1 * (F1 p.2.1 * F2 p.2.2))
    _ = ∑' a : ℤ, ∑' q : ℤ × ℤ, F0 a * (F1 q.1 * F2 q.2) :=
        Summable.tsum_prod h012
    _ = ∑' a : ℤ, F0 a * ((∑' b, F1 b) * (∑' c, F2 c)) := by
        refine tsum_congr fun a => ?_
        rw [tsum_mul_left, ← Summable.tsum_mul_tsum h1 h2 h12]
    _ = (∑' a, F0 a) * ((∑' b, F1 b) * (∑' c, F2 c)) := tsum_mul_right
    _ = (∑' a, F0 a) * (∑' b, F1 b) * (∑' c, F2 c) := by ring

lemma md_heatPeriod_eq_prod {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u = ∏ i, ∑' m : ℤ, heatK1 t (u i - m) := by
  have hsum : ∀ i : Fin 3, Summable (fun m : ℤ => heatK1 t (u i - m)) :=
    fun i => md_summable_heatK1 ht (u i)
  have hnn : ∀ i : Fin 3, ∀ m : ℤ, 0 ≤ heatK1 t (u i - m) := fun i m => heatK1_nonneg ht _
  calc heatPeriod t u
      = ∑' n : Fin 3 → ℤ, heatK1 t ((u - latVec n) 0) * heatK1 t ((u - latVec n) 1)
          * heatK1 t ((u - latVec n) 2) :=
        tsum_congr fun n => heatK3_eq_prod_heatK1 ht (u - latVec n)
    _ = ∑' n : Fin 3 → ℤ, heatK1 t (u 0 - (n 0 : ℝ)) * heatK1 t (u 1 - (n 1 : ℝ))
          * heatK1 t (u 2 - (n 2 : ℝ)) := by
        refine tsum_congr fun n => ?_
        rw [show (u - latVec n) 0 = u 0 - (n 0 : ℝ) by simp [latVec],
          show (u - latVec n) 1 = u 1 - (n 1 : ℝ) by simp [latVec],
          show (u - latVec n) 2 = u 2 - (n 2 : ℝ) by simp [latVec]]
    _ = (∑' a : ℤ, heatK1 t (u 0 - (a : ℝ))) * (∑' b : ℤ, heatK1 t (u 1 - (b : ℝ)))
          * (∑' c : ℤ, heatK1 t (u 2 - (c : ℝ))) :=
        md_tsum_fin3_mul _ _ _ (hnn 0) (hnn 1) (hnn 2) (hsum 0) (hsum 1) (hsum 2)
    _ = ∏ i, ∑' m : ℤ, heatK1 t (u i - m) := by rw [Fin.prod_univ_three]

/-! ## The short-time pointwise bound -/

lemma md_three_le (a1 a2 a3 s1 s2 s3 τ : ℝ)
    (_ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1)
    (ha3 : 0 ≤ a3) (ha3' : a3 ≤ 1)
    (_hs1 : 0 ≤ s1) (hs1' : s1 ≤ τ) (hs2 : 0 ≤ s2) (hs2' : s2 ≤ τ)
    (hs3 : 0 ≤ s3) (hs3' : s3 ≤ τ) (hτ : 0 ≤ τ) :
    (a1 + s1) * (a2 + s2) * (a3 + s3) - a1 * a2 * a3 ≤ τ ^ 3 + 3 * τ ^ 2 + 3 * τ := by
  have h2 : a2 + s2 ≤ 1 + τ := by linarith
  have h3 : a3 + s3 ≤ 1 + τ := by linarith
  have h2n : 0 ≤ a2 + s2 := by linarith
  have h3n : 0 ≤ a3 + s3 := by linarith
  have e1 : s1 * (a2 + s2) * (a3 + s3) ≤ τ * (1 + τ) * (1 + τ) := by
    have hA : s1 * (a2 + s2) ≤ τ * (1 + τ) := mul_le_mul hs1' h2 h2n hτ
    exact mul_le_mul hA h3 h3n (by positivity)
  have e2 : a1 * (s2 * (a3 + s3) + a2 * s3) ≤ 1 * (τ * (1 + τ) + 1 * τ) := by
    have hc : s2 * (a3 + s3) ≤ τ * (1 + τ) := mul_le_mul hs2' h3 h3n hτ
    have hd : a2 * s3 ≤ 1 * τ := mul_le_mul ha2' hs3' hs3 (by norm_num)
    have hsum : s2 * (a3 + s3) + a2 * s3 ≤ τ * (1 + τ) + 1 * τ := add_le_add hc hd
    exact mul_le_mul ha1' hsum (by positivity) (by positivity)
  have hid : (a1 + s1) * (a2 + s2) * (a3 + s3) - a1 * a2 * a3
      = s1 * (a2 + s2) * (a3 + s3) + a1 * (s2 * (a3 + s3) + a2 * s3) := by ring
  nlinarith [e1, e2, hid]

lemma md_smallT_pointwise {t : ℝ} (ht : 0 < t) (u : ℝ³) (hcell : ∀ i, |u i| ≤ 1 / 2) :
    heatPeriod t u - heatK3 t u
      ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * ((1 + tauZ t) ^ 3 - 1) := by
  have hcp : (0 : ℝ) < 4 * Real.pi * t := by positivity
  set c : ℝ := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) with hc
  have hc3 : c ^ 3 = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
    rw [hc]
    rw [(Real.rpow_natCast (x := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) (n := 3)).symm,
      ← Real.rpow_mul (le_of_lt hcp)]
    norm_num
  set A : Fin 3 → ℝ := fun i => Real.exp (-((u i) ^ 2) / (4 * t)) with hA
  set S : Fin 3 → ℝ := fun i =>
    ∑' m : ℤ, if m = 0 then 0 else Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t)) with hS
  set Q : Fin 3 → ℝ := fun i =>
    ∑' m : ℤ, Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t)) with hQ
  have hA0 : ∀ i, 0 ≤ A i := fun i => Real.exp_nonneg _
  have hA1 : ∀ i, A i ≤ 1 := by
    intro i
    refine Real.exp_le_one_iff.mpr ?_
    rw [show -((u i) ^ 2) / (4 * t) = -(u i ^ 2 / (4 * t)) by ring]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hS0 : ∀ i, 0 ≤ S i := by
    intro i
    refine tsum_nonneg fun m => ?_
    rcases eq_or_ne m 0 with hm | hm
    · rw [hm, if_pos rfl]
    · rw [if_neg hm]; exact Real.exp_nonneg _
  have hStau : ∀ i, S i ≤ tauZ t := fun i => md_gauss_tail_le ht (hcell i)
  have hQS : ∀ i, Q i = A i + S i := by
    intro i
    have hsum := md_summable_gauss ht (u i)
    have hsplit := Summable.tsum_eq_add_tsum_ite hsum 0
    simp only [hQ, hS, hA]
    rw [hsplit, show u i - ((0 : ℤ) : ℝ) = u i by simp]
  have hq : ∀ i : Fin 3, (∑' m : ℤ, heatK1 t (u i - m)) = c * Q i := by
    intro i
    rw [hQ, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [heatK1, hc]
  have hHP : heatPeriod t u = c ^ 3 * ∏ i, Q i := by
    rw [md_heatPeriod_eq_prod ht u]
    rw [show (∏ i : Fin 3, ∑' m : ℤ, heatK1 t (u i - m)) = ∏ i : Fin 3, c * Q i from
      Finset.prod_congr rfl fun i _ => hq i]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hK3 : heatK3 t u = c ^ 3 * ∏ i, A i := by
    rw [heatK3_eq_prod_heatK1 ht u, Fin.prod_univ_three]
    have h1 : heatK1 t (u 0) = c * A 0 := by rw [heatK1, hc, hA]
    have h2 : heatK1 t (u 1) = c * A 1 := by rw [heatK1, hc, hA]
    have h3 : heatK1 t (u 2) = c * A 2 := by rw [heatK1, hc, hA]
    rw [h1, h2, h3]
    ring
  have hdiff : ∏ i, Q i - ∏ i, A i ≤ (1 + tauZ t) ^ 3 - 1 := by
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    have htau0 : 0 ≤ tauZ t := by
      have h1 := hS0 0
      have h2 := hStau 0
      linarith
    have hthree := md_three_le (A 0) (A 1) (A 2) (S 0) (S 1) (S 2) (tauZ t)
      (hA0 0) (hA1 0) (hA0 1) (hA1 1) (hA0 2) (hA1 2)
      (hS0 0) (hStau 0) (hS0 1) (hStau 1) (hS0 2) (hStau 2) htau0
    rw [hQS 0, hQS 1, hQS 2]
    have hring : (1 + tauZ t) ^ 3 - 1 = (tauZ t) ^ 3 + 3 * (tauZ t) ^ 2 + 3 * (tauZ t) := by
      ring
    rw [hring]
    exact hthree
  calc heatPeriod t u - heatK3 t u
      = c ^ 3 * (∏ i, Q i - ∏ i, A i) := by rw [hHP, hK3]; ring
    _ ≤ c ^ 3 * ((1 + tauZ t) ^ 3 - 1) := mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * ((1 + tauZ t) ^ 3 - 1) := by rw [hc3]


/-! ## Continuity of the heat kernels in `t`, and basic integrability -/

lemma md_continuousOn_gauss (a c : ℝ) :
    ContinuousOn (fun t : ℝ => (4 * Real.pi * t) ^ (-a) * Real.exp (-c / (4 * t))) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.rpow_const (continuousOn_const.mul continuousOn_id) ?_
    intro t ht
    left
    exact ne_of_gt (mul_pos (by positivity) ht)
  · refine Real.continuous_exp.comp_continuousOn ?_
    rw [show (fun t : ℝ => -c / (4 * t)) = fun t => (-c / 4) / t by funext t; ring]
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)

lemma md_continuousOn_heatK3 (u : ℝ³) : ContinuousOn (fun t : ℝ => heatK3 t u) (Ioi 0) := by
  simpa only [heatK3] using md_continuousOn_gauss (3 / 2) (‖u‖ ^ 2)


/-! ## Measurability of the periodised heat kernel -/

lemma md_tsum_eq_iSup_sum {ι : Type*} [Countable ι] (f : ι → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hs : Summable f) : (∑' i, f i) = ⨆ s : Finset ι, ∑ i ∈ s, f i := by
  refine le_antisymm ?_ ?_
  · refine Real.tsum_le_of_sum_le hnn (fun u => ?_)
    exact le_ciSup ⟨∑' i, f i, by rintro _ ⟨s, rfl⟩; exact hs.sum_le_tsum s (fun i _ => hnn i)⟩ u
  · exact ciSup_le fun s => hs.sum_le_tsum s (fun i _ => hnn i)

lemma md_aemeasurable_Q1 (x : ℝ) :
    AEMeasurable (fun t : ℝ => Q1 t x) (volume.restrict (Ioi 0)) := by
  have hmain : AEMeasurable (fun t : ℝ => ⨆ s : Finset ℤ, ∑ m ∈ s, heatK1 t (x - m))
      (volume.restrict (Ioi 0)) := by
    refine AEMeasurable.iSup fun s => ?_
    have hcont : ContinuousOn (fun t : ℝ => ∑ m ∈ s, heatK1 t (x - m)) (Ioi 0) :=
      continuousOn_finsetSum s (fun m _ => by
        simpa only [heatK1] using md_continuousOn_gauss (1 / 2) ((x - m) ^ 2))
    exact hcont.aemeasurable measurableSet_Ioi
  refine hmain.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact (md_tsum_eq_iSup_sum (fun m : ℤ => heatK1 t (x - m)) (fun m => heatK1_nonneg ht _)
    (md_summable_heatK1 ht x)).symm

lemma md_aemeasurable_heatPeriod (u : ℝ³) :
    AEMeasurable (fun t : ℝ => heatPeriod t u) (volume.restrict (Ioi 0)) := by
  have hmain : AEMeasurable (fun t : ℝ => Q1 t (u 0) * Q1 t (u 1) * Q1 t (u 2))
      (volume.restrict (Ioi 0)) :=
    ((md_aemeasurable_Q1 (u 0)).mul (md_aemeasurable_Q1 (u 1))).mul
      (md_aemeasurable_Q1 (u 2))
  rw [show (fun t : ℝ => Q1 t (u 0) * Q1 t (u 1) * Q1 t (u 2))
      = fun t => ∏ i : Fin 3, Q1 t (u i) from by
    funext t; rw [Fin.prod_univ_three]] at hmain
  refine hmain.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact (md_heatPeriod_eq_prod ht u).symm

lemma md_aestronglyMeasurable_f (u : ℝ³) :
    AEStronglyMeasurable (fun t : ℝ => heatPeriod t u - 1) (volume.restrict (Ioi 0)) :=
  ((md_aemeasurable_heatPeriod u).sub aemeasurable_const).aestronglyMeasurable

/-! ## The three-factor numeric bound -/

lemma md_abs_prod_le (y1 y2 y3 ρ : ℝ) (h1 : |y1| ≤ ρ) (h2 : |y2| ≤ ρ) (h3 : |y3| ≤ ρ) :
    |(y1 + 1) * (y2 + 1) * (y3 + 1) - 1| ≤ 3 * ρ + 3 * ρ ^ 2 + ρ ^ 3 := by
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg y1) h1
  have hy1 : 0 ≤ |y1| := abs_nonneg _
  have hy2 : 0 ≤ |y2| := abs_nonneg _
  have hy3 : 0 ≤ |y3| := abs_nonneg _
  have hexp : (y1 + 1) * (y2 + 1) * (y3 + 1) - 1
      = (y1 + y2 + y3) + (y1 * y2 + y1 * y3 + y2 * y3) + y1 * y2 * y3 := by ring
  rw [hexp]
  have e1 : |y1 + y2 + y3| ≤ |y1| + |y2| + |y3| := abs_add_three y1 y2 y3
  have e2 : |y1 * y2 + y1 * y3 + y2 * y3| ≤ |y1| * |y2| + |y1| * |y3| + |y2| * |y3| := by
    simpa only [abs_mul] using abs_add_three (y1 * y2) (y1 * y3) (y2 * y3)
  have e3 : |y1 * y2 * y3| = |y1| * |y2| * |y3| := by rw [abs_mul, abs_mul]
  have hsum : |(y1 + y2 + y3) + (y1 * y2 + y1 * y3 + y2 * y3) + y1 * y2 * y3|
      ≤ (|y1| + |y2| + |y3|) + (|y1| * |y2| + |y1| * |y3| + |y2| * |y3|)
        + |y1| * |y2| * |y3| := by
    have h4 := abs_add_three (y1 + y2 + y3) (y1 * y2 + y1 * y3 + y2 * y3) (y1 * y2 * y3)
    rw [e3] at h4
    exact le_trans h4 (add_le_add (add_le_add e1 e2) le_rfl)
  refine le_trans hsum ?_
  have p12 : |y1| * |y2| ≤ ρ * ρ := mul_le_mul h1 h2 hy2 hρ0
  have p13 : |y1| * |y3| ≤ ρ * ρ := mul_le_mul h1 h3 hy3 hρ0
  have p23 : |y2| * |y3| ≤ ρ * ρ := mul_le_mul h2 h3 hy3 hρ0
  have p123 : |y1| * |y2| * |y3| ≤ ρ * ρ * ρ :=
    mul_le_mul (mul_le_mul h1 h2 hy2 hρ0) h3 hy3 (by positivity)
  nlinarith [h1, h2, h3, hy1, hy2, hy3, hρ0, p12, p13, p23, p123]

lemma md_heatPeriod_ge_heatK3 {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    heatK3 t u ≤ heatPeriod t u := by
  rw [md_heatPeriod_eq_prod ht u, heatK3_eq_prod_heatK1 ht u, Fin.prod_univ_three]
  have h0 : heatK1 t (u 0) ≤ Q1 t (u 0) := by
    rw [Q1]
    simpa using (md_summable_heatK1 ht (u 0)).le_tsum 0 (fun j _ => heatK1_nonneg ht _)
  have h1 : heatK1 t (u 1) ≤ Q1 t (u 1) := by
    rw [Q1]
    simpa using (md_summable_heatK1 ht (u 1)).le_tsum 0 (fun j _ => heatK1_nonneg ht _)
  have h2 : heatK1 t (u 2) ≤ Q1 t (u 2) := by
    rw [Q1]
    simpa using (md_summable_heatK1 ht (u 2)).le_tsum 0 (fun j _ => heatK1_nonneg ht _)
  have n0 : 0 ≤ heatK1 t (u 0) := heatK1_nonneg ht _
  have n1 : 0 ≤ heatK1 t (u 1) := heatK1_nonneg ht _
  have n2 : 0 ≤ heatK1 t (u 2) := heatK1_nonneg ht _
  have m0 : 0 ≤ Q1 t (u 0) := le_trans n0 h0
  have m1 : 0 ≤ Q1 t (u 1) := le_trans n1 h1
  have m2 : 0 ≤ Q1 t (u 2) := le_trans n2 h2
  exact mul_le_mul (mul_le_mul h0 h1 n1 m0) h2 n2 (mul_nonneg m0 m1)

lemma md_integrableOn_heatK3_Ioi (u : ℝ³) (hu : u ≠ 0) :
    IntegrableOn (fun t : ℝ => heatK3 t u) (Ioi 0) := by
  by_contra h
  have h0 : (∫ t in Ioi (0 : ℝ), heatK3 t u) = 0 := integral_undef h
  rw [HeatIntegral hu] at h0
  have hp : 0 < 1 / (4 * Real.pi * ‖u‖) := by
    have := norm_pos_iff.mpr hu
    positivity
  linarith

lemma md_integrableOn_smallT (u : ℝ³) (hcell : ∀ i, |u i| ≤ 1 / 2) :
    IntegrableOn (fun t : ℝ => heatPeriod t u - heatK3 t u) (Ioc 0 etaZ) := by
  refine Integrable.mono' SmallTMajorant.1 ?_ ?_
  · have h1 : AEStronglyMeasurable (fun t : ℝ => heatPeriod t u)
        (volume.restrict (Ioc 0 etaZ)) :=
      ((md_aemeasurable_heatPeriod u).mono_measure
        (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ => heatK3 t u)
        (volume.restrict (Ioc 0 etaZ)) :=
      (((md_continuousOn_heatK3 u).aestronglyMeasurable (μ := volume) measurableSet_Ioi).mono_measure
        (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
    exact h1.sub h2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (md_heatPeriod_ge_heatK3 ht0 u))]
    exact md_smallT_pointwise ht0 u hcell

lemma md_integrableOn_f_Ioc (u : ℝ³) (hu : u ≠ 0) (hcell : ∀ i, |u i| ≤ 1 / 2) :
    IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioc 0 etaZ) := by
  have hA := md_integrableOn_smallT u hcell
  have hK : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioc 0 etaZ) :=
    (md_integrableOn_heatK3_Ioi u hu).mono_set Ioc_subset_Ioi_self
  have hB : IntegrableOn (fun t : ℝ => heatK3 t u - 1) (Ioc 0 etaZ) :=
    hK.sub (integrableOn_const (by rw [Real.volume_Ioc]; simp))
  refine (hA.add hB).congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp only [Pi.add_apply]
  ring



/-! ## The long-time (Fourier) bound and the final assembly -/

lemma md_tail_pointwise {t : ℝ} (ht : etaZ ≤ t) (u : ℝ³) :
    |heatPeriod t u - 1| ≤ 3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [etaZ]) ht
  have hQ : ∀ i : Fin 3, |Q1 t (u i) - 1| ≤ rhoZ t := by
    intro i
    have h := (PoissonGauss1D ht0 (u i)).2
    simpa only [Q1, rhoZ, SZ] using h
  have hprod : heatPeriod t u = Q1 t (u 0) * Q1 t (u 1) * Q1 t (u 2) := by
    rw [md_heatPeriod_eq_prod ht0 u]
    exact Fin.prod_univ_three _
  rw [hprod]
  have h := md_abs_prod_le (Q1 t (u 0) - 1) (Q1 t (u 1) - 1) (Q1 t (u 2) - 1) (rhoZ t)
    (hQ 0) (hQ 1) (hQ 2)
  simpa only [Q1, sub_add_cancel] using h

lemma md_integrableOn_tail (u : ℝ³) :
    IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi etaZ) := by
  refine Integrable.mono' TailMajorant.2.1 ?_ ?_
  · exact (((md_aemeasurable_heatPeriod u).mono_measure
      (Measure.restrict_mono (Set.Ioi_subset_Ioi (by norm_num [etaZ] : (0 : ℝ) ≤ etaZ)) le_rfl)).sub
      aemeasurable_const).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using md_tail_pointwise ht.le u

lemma md_integrableOn_f (u : ℝ³) (hu : u ≠ 0) (hcell : ∀ i, |u i| ≤ 1 / 2) :
    IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi 0) := by
  have hA := md_integrableOn_f_Ioc u hu hcell
  have hB := md_integrableOn_tail u
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num [etaZ] : (0 : ℝ) ≤ etaZ)]
  exact hA.union hB


theorem MadelungBound {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ≠ 0) (hcell : ∀ i, |u i| ≤ 1 / 2) :
    Work.BoseFixR.LatGreen.latGreenSmooth u ≤ 1 / (2 * Real.pi * ‖u‖) := by
  have hη : (0 : ℝ) < etaZ := by norm_num [etaZ]
  have hInt := md_integrableOn_f u hu hcell
  have hsmall_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioc 0 etaZ) :=
    hInt.mono_set Ioc_subset_Ioi_self
  have htail_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi etaZ) :=
    hInt.mono_set (Set.Ioi_subset_Ioi hη.le)
  have hsplit : latGreen u
      = (∫ t in Ioc 0 etaZ, (heatPeriod t u - 1)) + ∫ t in Ioi etaZ, (heatPeriod t u - 1) := by
    rw [latGreen, ← Set.Ioc_union_Ioi_eq_Ioi hη.le]
    rw [setIntegral_union (disjoint_left.mpr fun x hx => by
      simp only [Set.mem_Ioi, not_lt]
      exact hx.2) measurableSet_Ioi hsmall_int htail_int]
  have hK : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioc 0 etaZ) :=
    (md_integrableOn_heatK3_Ioi u hu).mono_set Ioc_subset_Ioi_self
  have hHP_int : IntegrableOn (fun t : ℝ => heatPeriod t u) (Ioc 0 etaZ) := by
    refine ((md_integrableOn_smallT u hcell).add hK).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [Pi.add_apply]
    ring
  have hA1 : (∫ t in Ioc 0 etaZ, (heatPeriod t u - heatK3 t u)) ≤ 1 / 12 := by
    have h := integral_mono_ae (md_integrableOn_smallT u hcell) SmallTMajorant.1 ?_
    · linarith [h, SmallTMajorant.2]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact md_smallT_pointwise ht.1 u hcell
  have hA2 : (∫ t in Ioc 0 etaZ, heatK3 t u) ≤ 1 / (4 * Real.pi * ‖u‖) := by
    have h1 : (∫ t in Ioc 0 etaZ, heatK3 t u) ≤ ∫ t in Ioi (0 : ℝ), heatK3 t u := by
      refine setIntegral_mono_set (md_integrableOn_heatK3_Ioi u hu) ?_
        (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact heatK3_nonneg ht _
    rw [HeatIntegral hu] at h1
    exact h1
  have hone : (∫ t in Ioc (0 : ℝ) etaZ, (1 : ℝ)) = etaZ := by
    rw [← intervalIntegral.integral_of_le (by norm_num [etaZ] : (0 : ℝ) ≤ etaZ),
      intervalIntegral.integral_const]
    simp
  have hsmall : (∫ t in Ioc 0 etaZ, (heatPeriod t u - 1))
      ≤ 1 / 12 + 1 / (4 * Real.pi * ‖u‖) - etaZ := by
    have h1 : (∫ t in Ioc 0 etaZ, (heatPeriod t u - 1))
        = (∫ t in Ioc 0 etaZ, heatPeriod t u) - etaZ := by
      rw [integral_sub hHP_int (integrableOn_const (by rw [Real.volume_Ioc]; simp)), hone]
    have h2 : (∫ t in Ioc 0 etaZ, heatPeriod t u)
        = (∫ t in Ioc 0 etaZ, (heatPeriod t u - heatK3 t u))
          + ∫ t in Ioc 0 etaZ, heatK3 t u := by
      rw [← integral_add (md_integrableOn_smallT u hcell) hK]
      congr 1 with t
      ring
    rw [h1, h2]
    linarith [hA1, hA2]
  have htail : (∫ t in Ioi etaZ, (heatPeriod t u - 1)) ≤ 1 / 14 := by
    have h := integral_mono_ae (md_integrableOn_tail u) TailMajorant.2.1 ?_
    · linarith [h, TailMajorant.2.2]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact le_trans (le_abs_self _) (md_tail_pointwise ht.le u)
  have hfin : latGreen u ≤ 1 / 12 + 1 / 14 + 1 / (4 * Real.pi * ‖u‖) - etaZ := by
    rw [hsplit]
    linarith [hsmall, htail]
  rw [latGreenSmooth]
  have hnorm_le : ‖u‖ ≤ Real.sqrt 3 / 2 := by
    have hsq : ‖u‖ ^ 2 ≤ 3 / 4 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (u i) ^ 2 ≤ ∑ _i : Fin 3, (1 / 4 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            obtain ⟨hl, hr⟩ := abs_le.mp (hcell i)
            nlinarith [hl, hr, sq_abs (u i)]
        _ = 3 / 4 := by norm_num
    calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
      _ ≤ Real.sqrt (3 / 4) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 3 / 2 := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
  have hsqrt3 : Real.sqrt 3 < 2 := by
    have h : Real.sqrt 3 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) < 4)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hden_pos : 0 < 2 * Real.pi * ‖u‖ := by
    have := norm_pos_iff.mpr hu
    positivity
  have hden : 2 * Real.pi * ‖u‖ ≤ 3.15 * 2 := by
    nlinarith [Real.pi_lt_d2, hnorm_le, hsqrt3, norm_nonneg u]
  have hinv : 1 / (3.15 * 2) ≤ 1 / (2 * Real.pi * ‖u‖) := one_div_le_one_div_of_le hden_pos hden
  have hnum : (13 : ℝ) / 84 - 1 / 32 ≤ 1 / (3.15 * 2) := by norm_num
  have heta : etaZ = (1 / 32 : ℝ) := rfl
  linarith [hfin, hinv, hnum, heta]

end Work.BoseFixR.LatGreen
