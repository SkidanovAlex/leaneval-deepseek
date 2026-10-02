import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.mem_escapeRegion_iterate
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.norm_le_norm_iterate
import Submission.Work.Escape.green_comp
import Submission.Work.Escape.green_nonneg
import Submission.Work.Escape.green_eq_zero_iff
import Submission.Work.Escape.exists_differentiableOn_ball_clog

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Harmonicity of the Green function

The Green function `G_f` of a monic-growth map `f` of degree `d ≥ 2` is harmonic on the
complement of the filled Julia set, i.e. on the open set `{G_f > 0}`.

The proof is the classical Böttcher-coordinate argument: on a small ball around a point `z₀`
with `G z₀ > 0` one writes `G` as the real part of a holomorphic function.  Concretely, if `N` is
chosen with `f^[N] z₀` in the escaping region and `M ≥ N` is large enough that the orbit of every
point of the ball has norm `≥ ρ` from time `M` on, then

`G(w) = d^{-M} log ‖f^[M] w‖ + ∑_{k≥0} d^{-(M+k+1)} (log ‖f^{M+k+1} w‖ - d log ‖f^{M+k} w‖)`,

and the `k`-th summand is the real part of `log (g_{M+k+1}(w) / g_{M+k}(w)^d)`, where `g_k` is a
holomorphic *shadow* of `f^[k]` (a holomorphic function with `‖g_k w‖ = ‖f^[k] w‖`).  By the
ratio hypothesis the argument of the logarithm stays in the unit ball around `1`, so the
principal logarithm is holomorphic, the series converges locally uniformly, and the sum is
holomorphic.  For the unicritical families `z ↦ z^d + c` (holomorphic) and `z ↦ z̄^d + c`
(antiholomorphic) explicit shadows are constructed in `Shadow.lean`.
-/

open Filter Function Metric Set InnerProductSpace
open scoped Topology

noncomputable section

namespace Work.Escape

/-- A family of *holomorphic shadows* of the iterates of `f`: `shadow k` is holomorphic with the
same modulus as `f^[k]`, and the "Böttcher ratios" `shadow (k+1) z / (shadow k z)^d` tend to `1`
along large orbits, uniformly in the iterate.  Both holomorphic and antiholomorphic unicritical
families admit such a family. -/
structure ShadowSeq (f : ℂ → ℂ) (d : ℕ) where
  shadow : ℕ → ℂ → ℂ
  differentiable : ∀ k : ℕ, Differentiable ℂ (shadow k)
  norm_eq : ∀ (k : ℕ) (z : ℂ), ‖shadow k z‖ = ‖(f^[k]) z‖
  ratio : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, ∀ (k : ℕ) (z : ℂ),
    ρ ≤ ‖(f^[k]) z‖ → ‖shadow (k + 1) z / (shadow k z) ^ d - 1‖ ≤ ε

/-- If `‖w - 1‖ ≤ 1/2` then `w` lies in the slit plane `ℂ ∖ (-∞, 0]`. -/
theorem mem_slitPlane_of_norm_sub_one_le {w : ℂ} (hw : ‖w - 1‖ ≤ (2 : ℝ)⁻¹) :
    w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  rw [abs_le] at h1
  have h2 : w.re = (w - 1).re + 1 := by simp
  have h3 : ‖w - 1‖ ≤ (1 : ℝ) / 2 := by linarith
  linarith [h1.1, h1.2]

/-- If `‖w - 1‖ ≤ 1/2` then `‖log w‖ ≤ log 2 + π`. -/
theorem norm_log_le_of_norm_sub_one_le {w : ℂ} (hw : ‖w - 1‖ ≤ (2 : ℝ)⁻¹) :
    ‖Complex.log w‖ ≤ Real.log 2 + Real.pi := by
  have hlow : (1 : ℝ) / 2 ≤ ‖w‖ := by
    have h := abs_norm_sub_norm_le w 1
    rw [norm_one, abs_le] at h
    have : ‖w - 1‖ ≤ (1 : ℝ) / 2 := by linarith
    linarith [h.1]
  have hhigh : ‖w‖ ≤ 3 / 2 := by
    have h := abs_norm_sub_norm_le w 1
    rw [norm_one, abs_le] at h
    have : ‖w - 1‖ ≤ (1 : ℝ) / 2 := by linarith
    linarith [h.2]
  have hlog : |Real.log ‖w‖| ≤ Real.log 2 := by
    have h1 : 0 < ‖w‖ := by linarith
    have h2 : Real.log ‖w‖ ≤ Real.log 2 := Real.log_le_log h1 (by linarith)
    have h3 : -Real.log 2 ≤ Real.log ‖w‖ := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2⁻¹) (show (2 : ℝ)⁻¹ ≤ ‖w‖ by linarith)
      rw [Real.log_inv] at this
      linarith
    rw [abs_le]
    exact ⟨h3, h2⟩
  have harg : |w.arg| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg w), Complex.arg_le_pi w⟩
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |w.arg| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ Real.log 2 + Real.pi := by linarith

/-- The Green function of a map with monic growth of degree `d ≥ 2` is harmonic at every point
where it is positive. -/
theorem harmonicAt_green_of_pos (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    (G : ShadowSeq f d) {z₀ : ℂ} (hz₀ : 0 < green f d z₀) :
    InnerProductSpace.HarmonicAt (green f d) z₀ := by
  classical
  have hzK : z₀ ∉ filledJulia f := fun hmem =>
    absurd ((green_eq_zero_iff f d A h hd z₀).mpr hmem) (ne_of_gt hz₀)
  -- ## Step 1: some iterate of `z₀` lies in the escaping region
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (f^[N]) z₀ ∈ escapeRegion A := by
    by_contra hcon
    push_neg at hcon
    exact hzK (mem_filledJulia_of_norm_le fun n => le_of_not_gt (hcon n))
  -- ## Step 2: a ball around `z₀` on which `f^[N]` stays in the escaping region
  set u₀ : ℂ := (f^[N]) z₀ with hu₀def
  have hu₀ : max 2 A < ‖u₀‖ := hN
  set c : ℝ := (‖u₀‖ + max 2 A) / 2 with hcdef
  have hcA : max 2 A < c := by rw [hcdef]; linarith
  have hcu : c < ‖u₀‖ := by rw [hcdef]; linarith
  have hc2 : 2 < c := lt_of_le_of_lt (le_max_left 2 A) hcA
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z₀ < δ → c < ‖(f^[N]) w‖ := by
    have hopen : IsOpen {w : ℂ | c < ‖(f^[N]) w‖} :=
      isOpen_lt continuous_const (h.continuous_iterate N).norm
    have hmem : z₀ ∈ {w : ℂ | c < ‖(f^[N]) w‖} := by
      show c < ‖(f^[N]) z₀‖
      rw [← hu₀def]; exact hcu
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen z₀ hmem
    exact ⟨ε, hε, fun w hw => hsub hw⟩
  have hball : ∀ w : ℂ, w ∈ ball z₀ δ → c < ‖(f^[N]) w‖ :=
    fun w hw => hδ w (mem_ball.mp hw)
  -- ## Step 3: growth on the ball, and the choice of `M`
  have hgeom : ∀ w : ℂ, w ∈ ball z₀ δ → ∀ m : ℕ, 2 * (c / 2) ^ d ^ m ≤ ‖(f^[N + m]) w‖ := by
    intro w hw m
    have hwE : (f^[N]) w ∈ escapeRegion A := by
      show max 2 A < ‖(f^[N]) w‖
      exact lt_trans hcA (hball w hw)
    have hcle : c ≤ ‖(f^[N]) w‖ := le_of_lt (hball w hw)
    have hkey := geom_le_norm_iterate f d A h hd hwE m
    have hgoal : ‖(f^[N + m]) w‖ = ‖(f^[m]) ((f^[N]) w)‖ := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [hgoal]
    refine le_trans ?_ hkey
    have hle : c / 2 ≤ ‖(f^[N]) w‖ / 2 := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hle (d ^ m)) (by norm_num)
  obtain ⟨ρ, hρ⟩ := G.ratio (2 : ℝ)⁻¹ (by norm_num)
  set ρ' : ℝ := max ρ 1 with hρ'def
  have hρ'1 : 1 ≤ ρ' := le_max_right _ _
  have hbase : 1 < c / 2 := by linarith
  have hd1 : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have htendnatpow : Tendsto (fun k : ℕ => d ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < d by omega)
  have htendgeom : Tendsto (fun j : ℕ => 2 * (c / 2) ^ j) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num)).mpr
      (tendsto_pow_atTop_atTop_of_one_lt hbase)
  have htendall : Tendsto (fun k : ℕ => 2 * (c / 2) ^ (d ^ k)) atTop atTop :=
    htendgeom.comp htendnatpow
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ρ' ≤ 2 * (c / 2) ^ d ^ K := by
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (htendall.eventually (eventually_ge_atTop ρ'))
    exact ⟨K, hK K le_rfl⟩
  set M : ℕ := N + K with hMdef
  have hNM : N ≤ M := Nat.le_add_right N K
  have hMnorm : ∀ w : ℂ, w ∈ ball z₀ δ → ∀ k : ℕ, M ≤ k → ρ' ≤ ‖(f^[k]) w‖ := by
    intro w hw k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    have hmK : K ≤ m := by omega
    have hm := hgeom w hw m
    have hmono : 2 * (c / 2) ^ d ^ K ≤ 2 * (c / 2) ^ d ^ m := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_right₀ (le_of_lt hbase)
      exact Nat.pow_le_pow_right (by omega) hmK
    linarith [hK]
  -- ## Step 4: the holomorphic logarithm of the shadow of `f^[M]`
  obtain ⟨L, hLdiff, _hLexp, hLre⟩ :=
    exists_differentiableOn_ball_clog (g := G.shadow M) (c := z₀) (r := δ)
      ((G.differentiable M).differentiableOn)
      (fun w hw hzero => by
        have h1 : 1 ≤ ‖(f^[M]) w‖ := le_trans hρ'1 (hMnorm w hw M le_rfl)
        have h2 : ‖G.shadow M w‖ = 0 := by rw [hzero, norm_zero]
        rw [G.norm_eq M w] at h2
        linarith)
  -- ## Step 5: the series terms
  set S : ℕ → ℂ → ℂ := fun k w => G.shadow (k + 1) w / (G.shadow k w) ^ d with hSdef
  have hSnear : ∀ k : ℕ, M ≤ k → ∀ w : ℂ, w ∈ ball z₀ δ → ‖S k w - 1‖ ≤ (2 : ℝ)⁻¹ := by
    intro k hk w hw
    exact hρ k w (le_trans (le_max_left ρ 1) (hMnorm w hw k hk))
  have hSslit : ∀ k : ℕ, M ≤ k → ∀ w : ℂ, w ∈ ball z₀ δ → S k w ∈ Complex.slitPlane :=
    fun k hk w hw => mem_slitPlane_of_norm_sub_one_le (hSnear k hk w hw)
  have hSdiff : ∀ k : ℕ, M ≤ k → DifferentiableOn ℂ (S k) (ball z₀ δ) := by
    intro k hk
    refine DifferentiableOn.div ((G.differentiable (k + 1)).differentiableOn)
      ((G.differentiable k).differentiableOn.pow d) ?_
    intro w hw hzero
    have h1 : 1 ≤ ‖(f^[k]) w‖ := le_trans hρ'1 (hMnorm w hw k hk)
    have h2 : ‖(G.shadow k w) ^ d‖ = 0 := by rw [hzero, norm_zero]
    rw [norm_pow, G.norm_eq k w] at h2
    have : (0 : ℝ) < ‖(f^[k]) w‖ ^ d := by positivity
    linarith
  set H : ℕ → ℂ → ℂ := fun k w => Complex.log (S k w) with hHdef
  have hHdiff : ∀ k : ℕ, M ≤ k → DifferentiableOn ℂ (H k) (ball z₀ δ) :=
    fun k hk => (hSdiff k hk).clog (hSslit k hk)
  have hHbound : ∀ k : ℕ, M ≤ k → ∀ w : ℂ, w ∈ ball z₀ δ →
      ‖H k w‖ ≤ Real.log 2 + Real.pi :=
    fun k hk w hw => norm_log_le_of_norm_sub_one_le (hSnear k hk w hw)
  -- the summability bound
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv1 : ‖((d : ℝ))⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ((d : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hd2
    linarith
  have hgeomsum : Summable (fun k : ℕ => ((d : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_norm_lt_one hinv1
  have hsummableR : Summable (fun k : ℕ => ((d : ℝ) ^ (M + k + 1))⁻¹ * (Real.log 2 + Real.pi)) := by
    have h1 : (fun k : ℕ => ((d : ℝ) ^ (M + k + 1))⁻¹ * (Real.log 2 + Real.pi)) =
        fun k : ℕ => ((d : ℝ)⁻¹) ^ k * (((d : ℝ) ^ (M + 1))⁻¹ * (Real.log 2 + Real.pi)) := by
      funext k
      have h2 : (M + k + 1 : ℕ) = (M + 1) + k := by ring
      rw [h2, pow_add, mul_inv, ← inv_pow]
      ring
    rw [h1]
    exact hgeomsum.mul_right _
  -- ## Step 6: the holomorphic function `F` with `Re F = G` on the ball
  -- the real constants `d^{-n}`, viewed as complex numbers
  let cd : ℕ → ℂ := fun n => Complex.ofReal (((d : ℝ) ^ n)⁻¹)
  have hcd_unfold : ∀ n : ℕ, cd n = Complex.ofReal (((d : ℝ) ^ n)⁻¹) := fun _ => rfl
  have hcd_re : ∀ n : ℕ, (cd n).re = ((d : ℝ) ^ n)⁻¹ := fun n => by
    rw [hcd_unfold n, Complex.ofReal_re]
  have hcd_im : ∀ n : ℕ, (cd n).im = 0 := fun n => by
    rw [hcd_unfold n, Complex.ofReal_im]
  have hcd_norm : ∀ n : ℕ, ‖cd n‖ = ((d : ℝ) ^ n)⁻¹ := fun n => by
    have h1 : ‖Complex.ofReal (((d : ℝ) ^ n)⁻¹)‖ = |(((d : ℝ) ^ n)⁻¹)| := by simp
    rw [hcd_unfold n, h1, abs_of_nonneg (by positivity)]
  set F : ℂ → ℂ := fun w => cd M • L w + ∑' k : ℕ, cd (M + k + 1) • H (M + k) w with hFdef
  have hFdiff : DifferentiableOn ℂ F (ball z₀ δ) := by
    have hterm : ∀ k : ℕ, DifferentiableOn ℂ
        (fun w : ℂ => cd (M + k + 1) • H (M + k) w) (ball z₀ δ) :=
      fun k => (hHdiff (M + k) (Nat.le_add_right M k)).const_smul (cd (M + k + 1))
    have hle : ∀ k : ℕ, ∀ w : ℂ, w ∈ ball z₀ δ →
        ‖cd (M + k + 1) • H (M + k) w‖ ≤ ((d : ℝ) ^ (M + k + 1))⁻¹ * (Real.log 2 + Real.pi) := by
      intro k w hw
      rw [norm_smul, hcd_norm (M + k + 1)]
      exact mul_le_mul_of_nonneg_left (hHbound (M + k) (Nat.le_add_right M k) w hw)
        (by positivity)
    have htsum := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun k (w : ℂ) => cd (M + k + 1) • H (M + k) w) hsummableR hterm isOpen_ball hle
    exact ((differentiableOn_const (cd M)).mul hLdiff).add htsum
  -- ## Step 7: `Re F = G` on the ball
  have hsummable : ∀ w : ℂ, w ∈ ball z₀ δ →
      Summable (fun k : ℕ => cd (M + k + 1) • H (M + k) w) := by
    intro w hw
    refine Summable.of_norm_bounded hsummableR fun k => ?_
    rw [norm_smul, hcd_norm (M + k + 1)]
    exact mul_le_mul_of_nonneg_left (hHbound (M + k) (Nat.le_add_right M k) w hw) (by positivity)
  have hRe_term : ∀ (k : ℕ) (w : ℂ), w ∈ ball z₀ δ →
      Complex.reCLM (cd (M + k + 1) • H (M + k) w) =
        ((d : ℝ) ^ (M + k + 1))⁻¹ *
          (Real.log ‖(f^[M + k + 1]) w‖ - (d : ℝ) * Real.log ‖(f^[M + k]) w‖) := by
    intro k w hw
    have hpos : (0 : ℝ) < ‖(f^[M + k]) w‖ := by
      have h1 : 1 ≤ ‖(f^[M + k]) w‖ :=
        le_trans hρ'1 (hMnorm w hw (M + k) (Nat.le_add_right M k))
      linarith
    have hspos : (0 : ℝ) < ‖(f^[M + k + 1]) w‖ := by
      have h1 : 1 ≤ ‖(f^[M + k + 1]) w‖ :=
        le_trans hρ'1 (hMnorm w hw (M + k + 1) (by omega))
      linarith
    have hnorm : ‖S (M + k) w‖ = ‖(f^[M + k + 1]) w‖ / ‖(f^[M + k]) w‖ ^ d := by
      rw [hSdef]
      simp only
      rw [norm_div, norm_pow, G.norm_eq (M + k + 1) w, G.norm_eq (M + k) w]
    have hHre : (H (M + k) w).re =
        Real.log ‖(f^[M + k + 1]) w‖ - (d : ℝ) * Real.log ‖(f^[M + k]) w‖ := by
      rw [hHdef]
      simp only
      rw [Complex.log_re, hnorm]
      rw [Real.log_div (x := ‖(f^[M + k + 1]) w‖) (y := ‖(f^[M + k]) w‖ ^ d)
        (ne_of_gt hspos) (by positivity), Real.log_pow]
    rw [Complex.reCLM_apply, smul_eq_mul, Complex.mul_re, hcd_re, hcd_im, zero_mul, sub_zero, hHre]
  have hReF : ∀ w : ℂ, w ∈ ball z₀ δ → (F w).re = green f d w := by
    intro w hw
    have htel : ∀ n : ℕ,
        (∑ k ∈ Finset.range n, ((d : ℝ) ^ (M + k + 1))⁻¹ *
            (Real.log ‖(f^[M + k + 1]) w‖ - (d : ℝ) * Real.log ‖(f^[M + k]) w‖)) =
          greenIter f d w (M + n) - ((d : ℝ) ^ M)⁻¹ * Real.log ‖(f^[M]) w‖ := by
      intro n
      have hstep : ∀ k : ℕ,
          ((d : ℝ) ^ (M + k + 1))⁻¹ *
              (Real.log ‖(f^[M + k + 1]) w‖ - (d : ℝ) * Real.log ‖(f^[M + k]) w‖) =
            ((d : ℝ) ^ (M + (k + 1)))⁻¹ * Real.log ‖(f^[M + (k + 1)]) w‖ -
              ((d : ℝ) ^ (M + k))⁻¹ * Real.log ‖(f^[M + k]) w‖ := by
        intro k
        have h1 : ((d : ℝ) ^ (M + k + 1))⁻¹ * ((d : ℝ) * Real.log ‖(f^[M + k]) w‖) =
            ((d : ℝ) ^ (M + k))⁻¹ * Real.log ‖(f^[M + k]) w‖ := by
          have hdne : (d : ℝ) ≠ 0 := by positivity
          rw [pow_succ, mul_inv]
          field_simp
        have h2 : (M + (k + 1) : ℕ) = M + k + 1 := by ring
        rw [h2, mul_sub, h1]
      rw [Finset.sum_congr rfl fun k _ => hstep k]
      rw [Finset.sum_range_sub (fun i => ((d : ℝ) ^ (M + i))⁻¹ * Real.log ‖(f^[M + i]) w‖)]
      have h1 : 1 ≤ ‖(f^[M + n]) w‖ :=
        le_trans hρ'1 (hMnorm w hw (M + n) (Nat.le_add_right M n))
      rw [greenIter_eq_of_one_le h1]
      norm_num
    have hlim1 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        Complex.reCLM (cd (M + k + 1) • H (M + k) w)) atTop
        (𝓝 (Complex.reCLM (∑' k : ℕ, cd (M + k + 1) • H (M + k) w))) :=
      (HasSum.map ((hsummable w hw).hasSum) Complex.reCLM Complex.reCLM.continuous).tendsto_sum_nat
    have hlim2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        Complex.reCLM (cd (M + k + 1) • H (M + k) w)) atTop
        (𝓝 (green f d w - ((d : ℝ) ^ M)⁻¹ * Real.log ‖(f^[M]) w‖)) := by
      have hfun : (fun n : ℕ => ∑ k ∈ Finset.range n,
          Complex.reCLM (cd (M + k + 1) • H (M + k) w)) =
          fun n : ℕ => greenIter f d w (M + n) - ((d : ℝ) ^ M)⁻¹ * Real.log ‖(f^[M]) w‖ := by
        funext n
        rw [← htel n]
        exact Finset.sum_congr rfl fun k _ => hRe_term k w hw
      rw [hfun]
      have h1 : Tendsto (fun n : ℕ => greenIter f d w (n + M)) atTop (𝓝 (green f d w)) :=
        (tendsto_greenIter f d A h hd w).comp (tendsto_add_atTop_nat M)
      have h2 : Tendsto (fun n : ℕ => greenIter f d w (M + n)) atTop (𝓝 (green f d w)) := by
        simpa [Nat.add_comm] using h1
      exact h2.sub_const _
    have hmain : Complex.reCLM (∑' k : ℕ, cd (M + k + 1) • H (M + k) w) =
        green f d w - ((d : ℝ) ^ M)⁻¹ * Real.log ‖(f^[M]) w‖ :=
      tendsto_nhds_unique hlim1 hlim2
    have hL : (L w).re = Real.log ‖(f^[M]) w‖ := by
      rw [hLre w hw, G.norm_eq M w]
    have hmain' : (∑' k : ℕ, cd (M + k + 1) • H (M + k) w).re =
        green f d w - ((d : ℝ) ^ M)⁻¹ * Real.log ‖(f^[M]) w‖ := by
      rw [← Complex.reCLM_apply]
      exact hmain
    rw [hFdef]
    simp only
    rw [Complex.add_re, smul_eq_mul, Complex.mul_re, hcd_re M, hcd_im M, zero_mul, sub_zero, hL,
      hmain']
    ring
  -- ## Step 8: conclude
  have hballmem : ball z₀ δ ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hδpos)
  have hharm : HarmonicAt (fun w : ℂ => (F w).re) z₀ :=
    (hFdiff.analyticAt hballmem).harmonicAt_re
  refine (harmonicAt_congr_nhds ?_).mp hharm
  filter_upwards [hballmem] with w hw
  exact hReF w hw

/-- The Green function is harmonic off the filled Julia set. -/
theorem harmonicOnNhd_green (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    (G : ShadowSeq f d) :
    InnerProductSpace.HarmonicOnNhd (green f d) {z : ℂ | 0 < green f d z} := by
  intro z hz
  exact harmonicAt_green_of_pos f d A h hd G hz

/-- The Green function is harmonic on the complement of the filled Julia set. -/
theorem harmonicOnNhd_green_compl (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (G : ShadowSeq f d) :
    InnerProductSpace.HarmonicOnNhd (green f d) (filledJulia f)ᶜ := by
  intro z hz
  have hz' : 0 < green f d z := by
    rcases (green_nonneg f d A h hd z).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      exact hz ((green_eq_zero_iff f d A h hd z).mp heq.symm)
  exact harmonicAt_green_of_pos f d A h hd G hz'

end Work.Escape
