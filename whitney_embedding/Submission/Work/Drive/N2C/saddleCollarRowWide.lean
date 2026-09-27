import Mathlib
import Submission.Work.Drive.N2C.wideCollar
import Submission.Work.Drive.N2.saddleCollarRow
import Submission.Work.Drive.N2.windowDatum

set_option maxHeartbeats 1600000

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

theorem saddleCollarRowWide {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs Z : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hlev : ∀ y ∈ φ'.source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hηb : ηb < 1 / 10) (hηle : η ≤ ηb)
    {x : M} (hxsrc : x ∈ φ'.source) (hcol : Z x ∈ Work.Drive.N2C.saddleCollarWide ηb δ) :
    D.Φ (f p - lam0 ^ 2 * η - f x, x) ∈ φ'.source ∧
    f (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = f p - lam0 ^ 2 * η ∧
    Z (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = Work.Drive.N2.saddlePsi η δ (Z x) := by
  classical
  -- ## 0. elementary bookkeeping and the collar bounds
  have hρ : 0 < D.ρ D.j := D.hρ D.j
  have hlam0pos : 0 < lam0 := by rw [hlam0]; positivity
  have hlam0ne : lam0 ≠ 0 := ne_of_gt hlam0pos
  have hlam0C : (lam0 : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; exact hlam0ne
  have hsat : |((Z x) ^ 2).re| ≤ ηb ∧ 2 - 2 * δ ≤ |((Z x) ^ 2).im| ∧
      |((Z x) ^ 2).im| ≤ 2 := by
    simpa only [saddleCollarWide, Set.mem_setOf_eq] using hcol
  obtain ⟨hZre, hZimlo, hZimhi⟩ := hsat
  have hη2δ : 0 < 2 - 2 * δ := by linarith
  have hηb0 : 0 ≤ ηb := le_trans (abs_nonneg _) hZre
  have hηb2 : ηb ^ 2 < 1 / 100 := by
    have h1 : ηb * ηb ≤ ηb * (1 / 10) := mul_le_mul_of_nonneg_left hηb.le hηb0
    nlinarith
  have hlam4 : (0 : ℝ) < lam0 ^ 4 := by positivity
  -- the transport time
  set t : ℝ := f p - lam0 ^ 2 * η - f x with ht_def
  have hfx : f x = f p + lam0 ^ 2 * ((Z x) ^ 2).re := by
    have h := hlev x hxsrc
    rw [hZrel x, saddleCollar_aux_re_sq_smul] at h
    exact h
  have ht_eq : t = -(lam0 ^ 2 * (((Z x) ^ 2).re + η)) := by
    rw [ht_def, hfx]; ring
  -- ## 1. norm data of the collar point
  have hZs_norm (y : M) : ‖Zs y‖ = ‖φ' y‖ := by
    rw [hZs y]; exact saddleCollar_aux_norm_chart φ' y
  have hZs_re (y : M) : ((Zs y) ^ 2).re = lam0 ^ 2 * ((Z y) ^ 2).re := by
    have h := saddleCollar_aux_re_sq_smul lam0 (Z y)
    rw [← hZrel y] at h
    exact h
  have hZs_im (y : M) : ((Zs y) ^ 2).im = lam0 ^ 2 * ((Z y) ^ 2).im := by
    have h := saddleCollar_aux_im_sq_smul lam0 (Z y)
    rw [← hZrel y] at h
    exact h
  have hZx_lt : ‖Z x‖ < 2 := by
    have h4 : ‖Z x‖ ^ 4 = ((Z x) ^ 2).re ^ 2 + ((Z x) ^ 2).im ^ 2 :=
      saddleCollar_aux_norm_four _
    have hre2 : ((Z x) ^ 2).re ^ 2 ≤ ηb ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hηb0]
      exact hZre
    have him2 : ((Z x) ^ 2).im ^ 2 ≤ 4 := by
      nlinarith [abs_le.mp hZimhi, sq_abs ((Z x) ^ 2).im]
    have hlt : ‖Z x‖ ^ 4 < (2 : ℝ) ^ 4 := by
      rw [h4]; norm_num
      nlinarith [hre2, him2, hηb2]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (4 : ℕ) ≠ 0)).mp hlt
  have hx_norm : ‖φ' x‖ < 2 * lam0 := by
    rw [← hZs_norm x]
    have h : ‖Zs x‖ = lam0 * ‖Z x‖ := by
      rw [hZrel x, Complex.norm_mul, saddleCollar_aux_norm_ofReal_of_pos hlam0pos]
    rw [h]; nlinarith [hZx_lt, hlam0pos]
  have hρeq : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
  have hxC : x ∈ D.C D.j := by
    refine D.hCop D.j ⟨?_, ?_⟩
    · rw [← hsrc]; exact hxsrc
    · rw [← saddleCollar_aux_norm_chart_eq hsrc hball hxsrc]
      rw [hρeq]; nlinarith [hx_norm]
  -- ## 2. the orbit invariants along a confined trace (both time directions)
  have hnormLow : ∀ τ : ℝ, (∀ s ∈ Set.uIcc 0 τ, D.Φ (s, x) ∈ D.C D.j) →
      lam0 ^ 2 ≤ ‖φ' (D.Φ (τ, x))‖ ^ 2 := by
    intro τ hconf
    have himτ := him x τ (by simpa only [Set.uIcc] using hconf)
    have h1 : |((Zs (D.Φ (τ, x))) ^ 2).im| ≤ ‖Zs (D.Φ (τ, x))‖ ^ 2 :=
      saddleCollar_aux_abs_im_sq_le _
    have h2 : |((Zs (D.Φ (τ, x))) ^ 2).im| = lam0 ^ 2 * |((Z x) ^ 2).im| := by
      rw [himτ, hZs_im x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
    have h3 : lam0 ^ 2 ≤ |((Zs (D.Φ (τ, x))) ^ 2).im| := by
      rw [h2]
      have h4 : lam0 ^ 2 * (2 - 2 * δ) ≤ lam0 ^ 2 * |((Z x) ^ 2).im| :=
        mul_le_mul_of_nonneg_left hZimlo (sq_nonneg lam0)
      nlinarith [h4, hlam0pos, hη2δ]
    calc lam0 ^ 2 ≤ ‖Zs (D.Φ (τ, x))‖ ^ 2 := le_trans h3 h1
      _ = ‖φ' (D.Φ (τ, x))‖ ^ 2 := by rw [hZs_norm]
  have hderivRate : ∀ τ : ℝ, (∀ s ∈ Set.uIcc 0 τ, D.Φ (s, x) ∈ D.C D.j) →
      HasDerivAt (fun s : ℝ => ((Zs (D.Φ (s, x))) ^ 2).re) 1 τ := by
    intro τ hconf
    obtain ⟨hd0, hd1⟩ := hODE x τ (by simpa only [Set.uIcc] using hconf)
    have hre_eq : ∀ s : ℝ, (Zs (D.Φ (s, x))).re = φ' (D.Φ (s, x)) 0 := by
      intro s; rw [hZs (D.Φ (s, x))]; exact saddleCollar_aux_re_chart φ' _
    have him_eq : ∀ s : ℝ, (Zs (D.Φ (s, x))).im = φ' (D.Φ (s, x)) 1 := by
      intro s; rw [hZs (D.Φ (s, x))]; exact saddleCollar_aux_im_chart φ' _
    have hu : HasDerivAt (fun s : ℝ => (Zs (D.Φ (s, x))).re)
        (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re) τ := by
      refine hd0.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.EventuallyEq.of_eq (funext fun s => hre_eq s)
      · rw [hre_eq τ, one_mul]
    have hv : HasDerivAt (fun s : ℝ => (Zs (D.Φ (s, x))).im)
        (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im)) τ := by
      refine hd1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.EventuallyEq.of_eq (funext fun s => him_eq s)
      · rw [him_eq τ]; ring
    have hsq := (hu.pow 2).sub (hv.pow 2)
    have hnormeq : (Zs (D.Φ (τ, x))).re ^ 2 + (Zs (D.Φ (τ, x))).im ^ 2
        = ‖φ' (D.Φ (τ, x))‖ ^ 2 := by
      have h := norm_uVec (φ' (D.Φ (τ, x)))
      rw [← h]
      rw [hZs (D.Φ (τ, x))]; simp
    have hval : (2 : ℝ) * (Zs (D.Φ (τ, x))).re ^ (2 - 1)
          * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re)
        - 2 * (Zs (D.Φ (τ, x))).im ^ (2 - 1)
          * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im)) = 1 := by
      have hone : 2 * ‖φ' (D.Φ (τ, x))‖ ^ 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2)
          = 1 := chartMult_mul hlam0pos (hnormLow τ hconf)
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_one]
      have h3 : 2 * (Zs (D.Φ (τ, x))).re
            * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (Zs (D.Φ (τ, x))).re)
          - 2 * (Zs (D.Φ (τ, x))).im
            * (chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * (-(Zs (D.Φ (τ, x))).im))
          = 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2)
            * ((Zs (D.Φ (τ, x))).re ^ 2 + (Zs (D.Φ (τ, x))).im ^ 2) := by ring
      rw [h3, hnormeq,
        show 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) * ‖φ' (D.Φ (τ, x))‖ ^ 2
          = 2 * ‖φ' (D.Φ (τ, x))‖ ^ 2 * chartMult lam0 (‖φ' (D.Φ (τ, x))‖ ^ 2) from by ring]
      exact hone
    refine hsq.congr_of_eventuallyEq ?_ |>.congr_deriv hval
    exact Filter.EventuallyEq.of_eq (funext fun s => saddleCollar_aux_sq_re (Zs (D.Φ (s, x))))
  have hrateOf : ∀ u : ℝ, (∀ s ∈ Set.uIcc 0 u, D.Φ (s, x) ∈ D.C D.j) →
      ((Zs (D.Φ (u, x))) ^ 2).re = ((Zs x) ^ 2).re + u := by
    intro u hconf
    have hsub : ∀ s ∈ Set.uIcc 0 u, Set.uIcc 0 s ⊆ Set.uIcc 0 u := fun s hs =>
      Set.uIcc_subset_uIcc_iff_mem.mpr ⟨Set.left_mem_uIcc, hs⟩
    have hder : ∀ s ∈ Set.uIcc 0 u,
        HasDerivAt (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) 0 s := by
      intro s hs
      have hd := hderivRate s (fun r hr => hconf r (hsub s hs hr))
      have hsub2 : HasDerivAt (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) (1 - 1) s :=
        hd.sub (hasDerivAt_id s)
      simpa using hsub2
    have hdiff : ∀ s ∈ Set.uIcc 0 u,
        DifferentiableAt ℝ (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) s :=
      fun s hs => (hder s hs).differentiableAt
    have hbnd : ∀ s ∈ Set.uIcc 0 u,
        ‖deriv (fun r : ℝ => ((Zs (D.Φ (r, x))) ^ 2).re - r) s‖ ≤ 0 := by
      intro s hs
      rw [(hder s hs).deriv, norm_zero]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hdiff hbnd
      (convex_uIcc 0 u) (Set.right_mem_uIcc) (Set.left_mem_uIcc)
    rw [zero_mul, norm_le_zero_iff] at h
    simp only [D.hΦ0 x] at h
    linarith
  -- ## 3. the norm bound along the whole trace
  have hnormBd : ∀ u : ℝ, |u| ≤ |t| → (∀ s ∈ Set.uIcc 0 u, D.Φ (s, x) ∈ D.C D.j) →
      ‖φ' (D.Φ (u, x))‖ < 2 * lam0 := by
    intro u huabs hconf
    have hrate := hrateOf u hconf
    have hre : |((Zs (D.Φ (u, x))) ^ 2).re| ≤ 3 * lam0 ^ 2 * ηb := by
      rw [hrate]
      have h1 : |((Zs x) ^ 2).re| ≤ lam0 ^ 2 * ηb := by
        rw [hZs_re x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        exact mul_le_mul_of_nonneg_left hZre (sq_nonneg lam0)
      have h2 : |u| ≤ lam0 ^ 2 * (ηb + η) := by
        calc |u| ≤ |t| := huabs
          _ = lam0 ^ 2 * |((Z x) ^ 2).re + η| := by
              rw [ht_eq, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
          _ ≤ lam0 ^ 2 * (ηb + η) := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lam0)
              calc |((Z x) ^ 2).re + η| ≤ |((Z x) ^ 2).re| + |η| := abs_add_le _ _
                _ = |((Z x) ^ 2).re| + η := by rw [abs_of_pos hη]
                _ ≤ ηb + η := by linarith
      have h3 : lam0 ^ 2 * (ηb + η) ≤ 2 * lam0 ^ 2 * ηb := by nlinarith [hηle, sq_nonneg lam0]
      calc |((Zs x) ^ 2).re + u| ≤ |((Zs x) ^ 2).re| + |u| := abs_add_le _ _
        _ ≤ lam0 ^ 2 * ηb + 2 * lam0 ^ 2 * ηb := add_le_add h1 (le_trans h2 h3)
        _ = 3 * lam0 ^ 2 * ηb := by ring
    have him2 : |((Zs (D.Φ (u, x))) ^ 2).im| ≤ 2 * lam0 ^ 2 := by
      have h := him x u (by simpa only [Set.uIcc] using hconf)
      have h' : |((Zs (D.Φ (u, x))) ^ 2).im| ≤ lam0 ^ 2 * 2 := by
        rw [h, hZs_im x, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        exact mul_le_mul_of_nonneg_left hZimhi (sq_nonneg lam0)
      linarith
    have hlt : ‖Zs (D.Φ (u, x))‖ ^ 4 < (2 * lam0) ^ 4 := by
      rw [saddleCollar_aux_norm_four]
      have hre2 : ((Zs (D.Φ (u, x))) ^ 2).re ^ 2 ≤ (3 * lam0 ^ 2 * ηb) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * lam0 ^ 2 * ηb)]
        exact hre
      have him2' : ((Zs (D.Φ (u, x))) ^ 2).im ^ 2 ≤ (2 * lam0 ^ 2) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * lam0 ^ 2)]
        exact him2
      have hA : (3 * lam0 ^ 2 * ηb) ^ 2 + (2 * lam0 ^ 2) ^ 2 < (2 * lam0) ^ 4 := by
        have h1 : (3 * lam0 ^ 2 * ηb) ^ 2 = 9 * lam0 ^ 4 * ηb ^ 2 := by ring
        have h2 : (2 * lam0 ^ 2) ^ 2 = 4 * lam0 ^ 4 := by ring
        have h3 : (2 * lam0) ^ 4 = 16 * lam0 ^ 4 := by ring
        rw [h1, h2, h3]
        nlinarith [hηb2, hlam4]
      linarith [hre2, him2', hA]
    rw [← hZs_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * lam0)
      (by norm_num : (4 : ℕ) ≠ 0)).mp hlt
  -- ## 4. the confinement of the journey to the anchor level
  have hconf : ∀ s ∈ Set.uIcc 0 t, D.Φ (s, x) ∈ D.C D.j := by
    rcases le_total t 0 with ht0 | ht0
    · -- ### backwards in time
      rw [Set.uIcc_of_ge ht0]
      set T : Set ℝ := {σ : ℝ | t ≤ σ ∧ σ ≤ 0 ∧
        ∀ u ∈ Set.Icc σ 0, D.Φ (u, x) ∈ D.C D.j} with hTdef
      have hTmem : ∀ σ : ℝ, σ ∈ T ↔ (t ≤ σ ∧ σ ≤ 0 ∧
          ∀ u ∈ Set.Icc σ 0, D.Φ (u, x) ∈ D.C D.j) := by
        intro σ; simp only [hTdef, Set.mem_setOf_eq]
      have h0T : (0 : ℝ) ∈ T := (hTmem 0).mpr ⟨ht0, le_rfl, by
        intro u hu
        rw [Set.Icc_self] at hu
        rw [hu, D.hΦ0 x]
        exact hxC⟩
      have hTne : T.Nonempty := ⟨0, h0T⟩
      have hTbdd : BddBelow T := ⟨t, fun b hb => ((hTmem b).mp hb).1⟩
      set β : ℝ := sInf T with hβdef
      have hβge : t ≤ β := le_csInf hTne (fun b hb => ((hTmem b).mp hb).1)
      have hβle : β ≤ 0 := csInf_le hTbdd h0T
      have hgtβ : ∀ u ∈ Set.Ioc β 0, D.Φ (u, x) ∈ D.C D.j := by
        intro u hu
        obtain ⟨v, hvT, hvu⟩ := (csInf_lt_iff hTbdd hTne).mp hu.1
        exact ((hTmem v).mp hvT).2.2 u ⟨le_of_lt hvu, hu.2⟩
      have hnormUpper : ∀ u ∈ Set.Ioc β 0, ‖φ' (D.Φ (u, x))‖ < 2 * lam0 := by
        intro u hu
        refine hnormBd u ?_ ?_
        · rw [abs_of_nonpos hu.2, abs_of_nonpos ht0]
          linarith [hβge, hu.1]
        · intro s hs
          rw [Set.uIcc_of_ge hu.2, Set.mem_Icc] at hs
          exact hgtβ s ⟨lt_of_lt_of_le hu.1 hs.1, hs.2⟩
      have hΦcont : Continuous fun u : ℝ => D.Φ (u, x) := by
        have hp : Continuous fun u : ℝ => (u, x) := continuous_id.prodMk continuous_const
        exact D.hΦsm.continuous.comp hp
      have hβcl : D.Φ (β, x) ∈ closure (D.C D.j) := by
        rcases eq_or_lt_of_le hβle with hβ0 | hβlt
        · rw [hβ0, D.hΦ0 x]; exact subset_closure hxC
        · have h1 : β ∈ closure (Set.Ioc β 0) := by
            rw [closure_Ioc (ne_of_lt hβlt)]; exact ⟨le_rfl, hβle⟩
          have h2 : closure (Set.Ioc β 0) ⊆
              closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) :=
            closure_mono fun u hu => hgtβ u hu
          have h3 : closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) ⊆
              (fun u : ℝ => D.Φ (u, x)) ⁻¹' closure (D.C D.j) :=
            hΦcont.closure_preimage_subset _
          exact h3 (h2 h1)
      have hβsrc : D.Φ (β, x) ∈ φ'.source := by
        rw [hsrc]
        exact (D.hCcl D.j).2 hβcl
      have hβnorm : ‖φ' (D.Φ (β, x))‖ ≤ 2 * lam0 := by
        rcases eq_or_lt_of_le hβle with hβ0 | hβlt
        · rw [hβ0, D.hΦ0 x]; exact le_of_lt hx_norm
        · have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (β, x)) :=
            φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hβsrc)
          have horbT : Tendsto (fun u : ℝ => D.Φ (u, x)) (𝓝[>] β) (𝓝 (D.Φ (β, x))) :=
            hΦcont.continuousAt.mono_left nhdsWithin_le_nhds
          have htend : Tendsto (fun u : ℝ => ‖φ' (D.Φ (u, x))‖) (𝓝[>] β)
              (𝓝 ‖φ' (D.Φ (β, x))‖) :=
            (hφc.norm.tendsto).comp horbT
          refine le_of_tendsto htend ?_
          refine Filter.mem_of_superset (Ioc_mem_nhdsGT hβlt) ?_
          intro u hu
          exact (hnormUpper u hu).le
      have hβC : D.Φ (β, x) ∈ D.C D.j := by
        refine D.hCop D.j ⟨by rw [← hsrc]; exact hβsrc, ?_⟩
        rw [← saddleCollar_aux_norm_chart_eq hsrc hball hβsrc]
        rw [hρeq]; nlinarith [hβnorm, hlam0pos]
      have hβT : β ∈ T := (hTmem β).mpr ⟨hβge, hβle, fun u hu => by
        rcases eq_or_lt_of_le hu.1 with h | h
        · rw [← h]; exact hβC
        · exact hgtβ u ⟨h, hu.2⟩⟩
      have hβeq : β = t := by
        by_contra hne
        have hlt : t < β := lt_of_le_of_ne hβge (Ne.symm hne)
        have hnhdC : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ⊆ D.C D.j := by
          intro y hy
          refine D.hCop D.j ⟨by rw [← hsrc]; exact hy.1, ?_⟩
          rw [← saddleCollar_aux_norm_chart_eq hsrc hball hy.1]
          exact hy.2
        have hnhd : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ∈ 𝓝 (D.Φ (β, x)) := by
          have hltn : ‖φ' (D.Φ (β, x))‖ < D.ρ D.j := by
            rw [hρeq]; nlinarith [hβnorm, hlam0pos]
          have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (β, x)) :=
            φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hβsrc)
          exact Filter.inter_mem (IsOpen.mem_nhds φ'.open_source hβsrc)
            (hφc.norm.preimage_mem_nhds (isOpen_Iio.mem_nhds hltn))
        obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΦcont.continuousAt.preimage_mem_nhds hnhd)
        set d : ℝ := min (ε / 2) ((β - t) / 2) with hδdef
        have hδpos : 0 < d := lt_min (by linarith) (by linarith)
        have hδ1 : d ≤ ε / 2 := min_le_left _ _
        have hδ2 : d ≤ (β - t) / 2 := min_le_right _ _
        have hmem : β - d ∈ T := (hTmem _).mpr ⟨by linarith, by linarith, fun u hu => by
          rcases le_or_gt β u with h | h
          · exact ((hTmem β).mp hβT).2.2 u ⟨h, hu.2⟩
          · refine hnhdC (hε ?_)
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith [hu.1], by linarith [hu.1]⟩⟩
        have hle : β ≤ β - d := csInf_le hTbdd hmem
        linarith
      intro s hs
      exact ((hTmem β).mp hβT).2.2 s (by rw [hβeq]; exact hs)
    · -- ### forwards in time
      rw [Set.uIcc_of_le ht0]
      set T : Set ℝ := {σ : ℝ | 0 ≤ σ ∧ σ ≤ t ∧
        ∀ u ∈ Set.Icc 0 σ, D.Φ (u, x) ∈ D.C D.j} with hTdef
      have hTmem : ∀ σ : ℝ, σ ∈ T ↔ (0 ≤ σ ∧ σ ≤ t ∧
          ∀ u ∈ Set.Icc 0 σ, D.Φ (u, x) ∈ D.C D.j) := by
        intro σ; simp only [hTdef, Set.mem_setOf_eq]
      have h0T : (0 : ℝ) ∈ T := (hTmem 0).mpr ⟨le_rfl, ht0, by
        intro u hu
        rw [Set.Icc_self] at hu
        rw [hu, D.hΦ0 x]
        exact hxC⟩
      have hTne : T.Nonempty := ⟨0, h0T⟩
      have hTbdd : BddAbove T := ⟨t, fun b hb => ((hTmem b).mp hb).2.1⟩
      set γ : ℝ := sSup T with hγdef
      have hγge : 0 ≤ γ := le_csSup hTbdd h0T
      have hγle : γ ≤ t := csSup_le hTne (fun b hb => ((hTmem b).mp hb).2.1)
      have hltγ : ∀ u ∈ Set.Ico 0 γ, D.Φ (u, x) ∈ D.C D.j := by
        intro u hu
        obtain ⟨v, hvT, huv⟩ := (lt_csSup_iff hTbdd hTne).mp hu.2
        exact ((hTmem v).mp hvT).2.2 u ⟨hu.1, le_of_lt huv⟩
      have hnormUpper : ∀ u ∈ Set.Ico 0 γ, ‖φ' (D.Φ (u, x))‖ < 2 * lam0 := by
        intro u hu
        refine hnormBd u ?_ ?_
        · rw [abs_of_nonneg hu.1, abs_of_nonneg ht0]
          linarith [hγle, hu.2]
        · intro s hs
          rw [Set.uIcc_of_le hu.1, Set.mem_Icc] at hs
          exact hltγ s ⟨hs.1, lt_of_le_of_lt hs.2 hu.2⟩
      have hΦcont : Continuous fun u : ℝ => D.Φ (u, x) := by
        have hp : Continuous fun u : ℝ => (u, x) := continuous_id.prodMk continuous_const
        exact D.hΦsm.continuous.comp hp
      have hγcl : D.Φ (γ, x) ∈ closure (D.C D.j) := by
        rcases lt_or_eq_of_le hγge with hγlt | hγ0
        · have h1 : γ ∈ closure (Set.Ioo 0 γ) := by
            rw [closure_Ioo (ne_of_lt hγlt)]; exact ⟨le_of_lt hγlt, le_rfl⟩
          have h2 : closure (Set.Ioo 0 γ) ⊆
              closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) :=
            closure_mono fun u hu => hltγ u ⟨le_of_lt hu.1, hu.2⟩
          have h3 : closure ((fun u : ℝ => D.Φ (u, x)) ⁻¹' D.C D.j) ⊆
              (fun u : ℝ => D.Φ (u, x)) ⁻¹' closure (D.C D.j) :=
            hΦcont.closure_preimage_subset _
          exact h3 (h2 h1)
        · rw [← hγ0, D.hΦ0 x]; exact subset_closure hxC
      have hγsrc : D.Φ (γ, x) ∈ φ'.source := by
        rw [hsrc]
        exact (D.hCcl D.j).2 hγcl
      have hγnorm : ‖φ' (D.Φ (γ, x))‖ ≤ 2 * lam0 := by
        rcases lt_or_eq_of_le hγge with hγlt | hγ0
        · have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (γ, x)) :=
            φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hγsrc)
          have horbT : Tendsto (fun u : ℝ => D.Φ (u, x)) (𝓝[<] γ) (𝓝 (D.Φ (γ, x))) :=
            hΦcont.continuousAt.mono_left nhdsWithin_le_nhds
          have htend : Tendsto (fun u : ℝ => ‖φ' (D.Φ (u, x))‖) (𝓝[<] γ)
              (𝓝 ‖φ' (D.Φ (γ, x))‖) :=
            (hφc.norm.tendsto).comp horbT
          refine le_of_tendsto htend ?_
          refine Filter.mem_of_superset (Ico_mem_nhdsLT hγlt) ?_
          intro u hu
          exact (hnormUpper u hu).le
        · rw [← hγ0, D.hΦ0 x]; exact le_of_lt hx_norm
      have hγC : D.Φ (γ, x) ∈ D.C D.j := by
        refine D.hCop D.j ⟨by rw [← hsrc]; exact hγsrc, ?_⟩
        rw [← saddleCollar_aux_norm_chart_eq hsrc hball hγsrc]
        rw [hρeq]; nlinarith [hγnorm, hlam0pos]
      have hγT : γ ∈ T := (hTmem γ).mpr ⟨hγge, hγle, fun u hu => by
        rcases eq_or_lt_of_le hu.2 with h | h
        · exact h ▸ hγC
        · exact hltγ u ⟨hu.1, h⟩⟩
      have hγeq : γ = t := by
        by_contra hne
        have hlt : γ < t := lt_of_le_of_ne hγle hne
        have hnhdC : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ⊆ D.C D.j := by
          intro y hy
          refine D.hCop D.j ⟨by rw [← hsrc]; exact hy.1, ?_⟩
          rw [← saddleCollar_aux_norm_chart_eq hsrc hball hy.1]
          exact hy.2
        have hnhd : {y : M | y ∈ φ'.source ∧ ‖φ' y‖ < D.ρ D.j} ∈ 𝓝 (D.Φ (γ, x)) := by
          have hltn : ‖φ' (D.Φ (γ, x))‖ < D.ρ D.j := by
            rw [hρeq]; nlinarith [hγnorm, hlam0pos]
          have hφc : ContinuousAt (fun y : M => φ' y) (D.Φ (γ, x)) :=
            φ'.continuousOn_toFun.continuousAt (φ'.open_source.mem_nhds hγsrc)
          exact Filter.inter_mem (IsOpen.mem_nhds φ'.open_source hγsrc)
            (hφc.norm.preimage_mem_nhds (isOpen_Iio.mem_nhds hltn))
        obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΦcont.continuousAt.preimage_mem_nhds hnhd)
        set d : ℝ := min (ε / 2) ((t - γ) / 2) with hδdef
        have hδpos : 0 < d := lt_min (by linarith) (by linarith)
        have hδ1 : d ≤ ε / 2 := min_le_left _ _
        have hδ2 : d ≤ (t - γ) / 2 := min_le_right _ _
        have hmem : γ + d ∈ T := (hTmem _).mpr ⟨by linarith, by linarith, fun u hu => by
          rcases le_or_gt u γ with h | h
          · exact ((hTmem γ).mp hγT).2.2 u ⟨hu.1, h⟩
          · refine hnhdC (hε ?_)
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith [hu.2], by linarith [hu.2]⟩⟩
        have hle : γ + d ≤ γ := le_csSup hTbdd hmem
        linarith
      intro s hs
      exact ((hTmem γ).mp hγT).2.2 s (by rw [hγeq]; exact hs)
  -- ## 5. the orbit facts at the anchor time
  have hrateT : ((Zs (D.Φ (t, x))) ^ 2).re = ((Zs x) ^ 2).re + t := hrateOf t hconf
  have himT : ((Zs (D.Φ (t, x))) ^ 2).im = ((Zs x) ^ 2).im :=
    him x t (by simpa only [Set.uIcc] using hconf)
  have hsrcT : D.Φ (t, x) ∈ φ'.source :=
    hsrc ▸ D.hCsub D.j (hconf t (Set.right_mem_uIcc))
  have hZreT : ((Z (D.Φ (t, x))) ^ 2).re = -η := by
    have hkey : lam0 ^ 2 * ((Z (D.Φ (t, x))) ^ 2).re = lam0 ^ 2 * ((Z x) ^ 2).re + t := by
      rw [← hZs_re (D.Φ (t, x)), hrateT, hZs_re x]
    have h2 : lam0 ^ 2 * ((Z (D.Φ (t, x))) ^ 2).re = lam0 ^ 2 * (-η) := by
      rw [hkey, ht_def, hfx]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h2
  -- ## 6. the path `s ↦ Z (Φ (s t, x))` and the model constancy
  have hst_mem : ∀ s ∈ Set.Icc (0 : ℝ) 1, s * t ∈ Set.uIcc 0 t := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Set.mem_uIcc]
    rcases le_total t 0 with ht | ht
    · exact Or.inr ⟨by nlinarith, by nlinarith⟩
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
  have hchart : ContinuousOn (fun y : M => ((φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I))
      φ'.source := by
    have h0 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => ((u 0 : ℝ) : ℂ) := by fun_prop
    have h1 : Continuous fun u : EuclideanSpace ℝ (Fin 2) => ((u 1 : ℝ) : ℂ) := by fun_prop
    exact (h0.add (h1.mul continuous_const)).comp_continuousOn φ'.continuousOn_toFun
  have hZcont : ContinuousOn (fun y : M => Z y) φ'.source := by
    have hEq : (fun y : M => Z y) = fun y : M => (lam0 : ℂ)⁻¹ *
        ((φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) := by
      funext y
      have h : Z y = (lam0 : ℂ)⁻¹ * Zs y := by
        rw [hZrel y, ← mul_assoc, inv_mul_cancel₀ hlam0C, one_mul]
      rw [h, hZs y]
    rw [hEq]
    exact hchart.const_mul _
  set γp : ℝ → ℂ := fun s => Z (D.Φ (s * t, x)) with hγpdef
  have hmemγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, D.Φ (s * t, x) ∈ φ'.source := by
    intro s hs
    exact hsrc ▸ D.hCsub D.j (hconf (s * t) (hst_mem s hs))
  have hγpcont : ContinuousOn γp (Set.Icc (0 : ℝ) 1) := by
    have horb : Continuous fun s : ℝ => D.Φ (s * t, x) := by
      have hp : Continuous fun s : ℝ => (s * t, x) :=
        (continuous_id.mul continuous_const).prodMk continuous_const
      exact D.hΦsm.continuous.comp hp
    have hEq : γp = fun s : ℝ => (lam0 : ℂ)⁻¹ *
        ((φ' (D.Φ (s * t, x)) 0 : ℂ) + (φ' (D.Φ (s * t, x)) 1 : ℂ) * Complex.I) := by
      funext s
      show Z (D.Φ (s * t, x)) = (lam0 : ℂ)⁻¹ *
        ((φ' (D.Φ (s * t, x)) 0 : ℂ) + (φ' (D.Φ (s * t, x)) 1 : ℂ) * Complex.I)
      have h : Z (D.Φ (s * t, x)) = (lam0 : ℂ)⁻¹ * Zs (D.Φ (s * t, x)) := by
        rw [hZrel (D.Φ (s * t, x)), ← mul_assoc, inv_mul_cancel₀ hlam0C, one_mul]
      rw [h, hZs (D.Φ (s * t, x))]
    rw [hEq]
    exact (hchart.comp horb.continuousOn hmemγ).const_mul _
  have hγpC : ∀ s ∈ Set.Icc (0 : ℝ) 1, γp s ∈ saddleCollarWide ηb δ := by
    intro s hs
    have hst := hst_mem s hs
    have hconf' : ∀ u ∈ Set.uIcc 0 (s * t), D.Φ (u, x) ∈ D.C D.j := fun u hu =>
      hconf u (Set.uIcc_subset_uIcc_iff_mem.mpr ⟨Set.left_mem_uIcc, hst⟩ hu)
    have hrate := hrateOf (s * t) hconf'
    have hims := him x (s * t) (by simpa only [Set.uIcc] using hconf')
    set A : ℝ := lam0 ^ 2 * ((Z x) ^ 2).re with hA_def
    have hkeyA : lam0 ^ 2 * ((Z (D.Φ (s * t, x))) ^ 2).re = A + s * t := by
      rw [hA_def, ← hZs_re (D.Φ (s * t, x)), hrate, hZs_re x]
    have hat : A + t = -(lam0 ^ 2 * η) := by rw [hA_def, ht_def, hfx]; ring
    have hAabs : |A| ≤ lam0 ^ 2 * ηb := by
      rw [hA_def, abs_mul, abs_of_nonneg (sq_nonneg lam0)]
      exact mul_le_mul_of_nonneg_left hZre (sq_nonneg lam0)
    have hBabs : |A + t| ≤ lam0 ^ 2 * ηb := by
      rw [hat, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam0 ^ 2 * η)]
      nlinarith [hηle, sq_nonneg lam0]
    have hAnal := abs_le.mp hAabs
    have hBanal := abs_le.mp hBabs
    have hfin : |A + s * t| ≤ lam0 ^ 2 * ηb := by
      rw [abs_le]
      rcases Set.mem_uIcc.mp hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [hAnal.1, h1], by linarith [hBanal.2, h2]⟩
      · exact ⟨by linarith [hBanal.1, h1], by linarith [hAnal.2, h2]⟩
    have hreabs : |((Z (D.Φ (s * t, x))) ^ 2).re| ≤ ηb := by
      have h2 : |lam0 ^ 2 * ((Z (D.Φ (s * t, x))) ^ 2).re| ≤ lam0 ^ 2 * ηb := by
        rw [hkeyA]; exact hfin
      rw [abs_mul, abs_of_nonneg (sq_nonneg lam0)] at h2
      exact le_of_mul_le_mul_left h2 (by positivity)
    have himabs : 2 - 2 * δ ≤ |((Z (D.Φ (s * t, x))) ^ 2).im| ∧
        |((Z (D.Φ (s * t, x))) ^ 2).im| ≤ 2 := by
      have h2 : ((Z (D.Φ (s * t, x))) ^ 2).im = ((Z x) ^ 2).im := by
        have h := hims
        rw [hZs_im, hZs_im] at h
        exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h
      rw [h2]; exact ⟨hZimlo, hZimhi⟩
    rw [hγpdef]
    simpa only [saddleCollarWide, Set.mem_setOf_eq] using ⟨hreabs, himabs.1, himabs.2⟩
  have him0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((γp s) ^ 2).im = ((γp 0) ^ 2).im := by
    intro s hs
    have hst := hst_mem s hs
    have hconf' : ∀ u ∈ Set.uIcc 0 (s * t), D.Φ (u, x) ∈ D.C D.j := fun u hu =>
      hconf u (Set.uIcc_subset_uIcc_iff_mem.mpr ⟨Set.left_mem_uIcc, hst⟩ hu)
    have h0 : γp 0 = Z x := by simp only [hγpdef]; simp [D.hΦ0 x]
    rw [h0]
    have h1 : ((Z (D.Φ (s * t, x))) ^ 2).im = ((Z x) ^ 2).im := by
      have h := him x (s * t) (by simpa only [Set.uIcc] using hconf')
      rw [hZs_im, hZs_im] at h
      exact mul_left_cancel₀ (pow_ne_zero 2 hlam0ne) h
    rw [hγpdef]
    exact h1
  have hΨconst : saddlePsi η δ (Z (D.Φ (t, x))) = saddlePsi η δ (Z x) := by
    have h := saddlePsi_collarEqWide hη hη' hδ hδ' hηb hγpcont hγpC him0
    have h1 : γp 1 = Z (D.Φ (t, x)) := by simp only [hγpdef]; simp
    have h0 : γp 0 = Z x := by simp only [hγpdef]; simp [D.hΦ0 x]
    rwa [h1, h0] at h
  have hself := saddleCollar_aux_saddlePsi_eq_self_of_re_sq_neg_eta hη hδ
    (by linarith : δ < 1 / 2) hZreT
  exact ⟨hsrcT,
    by
      calc f (D.Φ (t, x)) = f p + ((Zs (D.Φ (t, x))) ^ 2).re := hlev _ hsrcT
        _ = f p + (((Zs x) ^ 2).re + t) := by rw [hrateT]
        _ = f p - lam0 ^ 2 * η := by
          rw [hZs_re x, ht_def, hfx]; ring,
    by
      rw [← hself]
      exact hΨconst⟩

end Work.Drive.N2C
