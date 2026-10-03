import Mathlib
import Submission.Work.Param.Basic

/-!
# Koenigs' linearisation of the attracting fixed point

`Q l x = l * x + x ^ 2` with `0 < ‖l‖ < 1` has an attracting fixed point at `0`.  The classical
Koenigs coordinate
`φ w = w + ∑' n, (l ^ (n + 1))⁻¹ * ((Q l)^[n] w) ^ 2 = lim n, (Q l)^[n] w / l ^ n`
linearises `Q l` near `0`: it is holomorphic on a ball around `0`, fixes `0`, has `deriv φ 0 = 1`
and satisfies `φ (Q l z) = l * φ z`.  Its local inverse `ψ` (which exists by the analytic inverse
function theorem, since `deriv φ 0 = 1 ≠ 0`) is the Koenigs linearisation of the target statement:
`Q l (ψ w) = ψ (l * w)` near `0`, with `ψ 0 = 0` and `deriv ψ 0 = 1`.
-/

namespace Work.Param

open Filter Topology Metric

noncomputable section


lemma norm_iterate_Q_le {l : ℂ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (_hlamγ : ‖l‖ ≤ γ) (n : ℕ)
    {w : ℂ} (hw : ‖w‖ ≤ γ - ‖l‖) : ‖(Q l)^[n] w‖ ≤ γ ^ n * ‖w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hx2 : ‖(Q l)^[n] w‖ ≤ γ - ‖l‖ := by
        have hpow : γ ^ n ≤ 1 := pow_le_one₀ hγ0 hγ1
        nlinarith [norm_nonneg w]
      have hstep1 : ‖l‖ * ‖(Q l)^[n] w‖ + ‖(Q l)^[n] w‖ ^ 2 ≤ γ * ‖(Q l)^[n] w‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hx2 (norm_nonneg ((Q l)^[n] w))]
      have hstep2 : γ * (γ ^ n * ‖w‖) = γ ^ (n + 1) * ‖w‖ := by rw [pow_succ]; ring
      have hstep3 : ‖l‖ * ‖(Q l)^[n] w‖ + ‖(Q l)^[n] w‖ ^ 2 ≤ γ * (γ ^ n * ‖w‖) :=
        le_trans hstep1 (mul_le_mul_of_nonneg_left ih hγ0)
      calc ‖Q l ((Q l)^[n] w)‖ = ‖l * ((Q l)^[n] w) + ((Q l)^[n] w) ^ 2‖ := rfl
        _ ≤ ‖l * ((Q l)^[n] w)‖ + ‖((Q l)^[n] w) ^ 2‖ := norm_add_le _ _
        _ = ‖l‖ * ‖(Q l)^[n] w‖ + ‖(Q l)^[n] w‖ ^ 2 := by rw [norm_mul, norm_pow]
        _ ≤ γ ^ (n + 1) * ‖w‖ := by rw [← hstep2]; exact hstep3

lemma geom_identity (a g r q : ℝ) (ha : 0 < a) (hq : q = g ^ 2 / a) (n : ℕ) :
    (a ^ (n + 1))⁻¹ * (g ^ n * r) ^ 2 = (r ^ 2 / a) * q ^ n := by
  rw [hq, div_pow]
  field_simp
  ring

theorem exists_linearizing_map (l : ℂ) (hl : ‖l‖ < 1) (hl0 : l ≠ 0) :
    ∃ (ρ : ℝ) (φ : ℂ → ℂ), 0 < ρ ∧ DifferentiableOn ℂ φ (Metric.ball 0 ρ) ∧ φ 0 = 0 ∧
      deriv φ 0 = 1 ∧ (∀ z ∈ Metric.ball 0 ρ, φ (Q l z) = l * φ z) := by
  have hlam0 : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  set s : ℝ := Real.sqrt ‖l‖ with hs
  have hs2 : s ^ 2 = ‖l‖ := Real.sq_sqrt hlam0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hlam0
  have hs1 : s < 1 := by nlinarith [hs2, hs0, hl]
  have hls : ‖l‖ < s := by nlinarith [hs2, hs0, hs1]
  set γ : ℝ := (‖l‖ + s) / 2 with hγdef
  have hγlt : ‖l‖ < γ := by rw [hγdef]; linarith
  have hγs : γ < s := by rw [hγdef]; linarith
  have hγ0 : 0 < γ := lt_trans hlam0 hγlt
  have hγ1 : γ < 1 := lt_trans hγs hs1
  have hq_lt : γ ^ 2 < ‖l‖ := by nlinarith [hγ0, hγs, hs2]
  set q : ℝ := γ ^ 2 / ‖l‖ with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hlam0]; exact hq_lt
  set ρ : ℝ := γ - ‖l‖ with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  set t : ℕ → ℂ → ℂ := fun n w => (l ^ (n + 1))⁻¹ * ((Q l)^[n] w) ^ 2 with ht
  set Ψ : ℂ → ℂ := fun w => ∑' n, t n w with hΨ
  set φ : ℂ → ℂ := fun w => w + Ψ w with hφ
  have hQd : Differentiable ℂ (Q l) := by unfold Q; fun_prop
  have hu : Summable (fun n : ℕ => (ρ ^ 2 / ‖l‖) * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hbound : ∀ n (w : ℂ), ‖w‖ ≤ ρ → ‖t n w‖ ≤ (ρ ^ 2 / ‖l‖) * q ^ n := by
    intro n w hw
    have hγn : (0 : ℝ) ≤ γ ^ n := pow_nonneg hγ0.le n
    have hiter : ‖(Q l)^[n] w‖ ≤ γ ^ n * ‖w‖ :=
      norm_iterate_Q_le hγ0.le hγ1.le hγlt.le n hw
    have hiter' : ‖(Q l)^[n] w‖ ≤ γ ^ n * ρ := by nlinarith [norm_nonneg w]
    have h1 : (‖l‖ ^ (n + 1))⁻¹ * ‖(Q l)^[n] w‖ ^ 2 ≤
        (‖l‖ ^ (n + 1))⁻¹ * (γ ^ n * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hiter' 2) (by positivity)
    have h2 : ‖t n w‖ = (‖l‖ ^ (n + 1))⁻¹ * ‖(Q l)^[n] w‖ ^ 2 := by
      simp only [ht, norm_mul, norm_inv, norm_pow]
    have h3 : (‖l‖ ^ (n + 1))⁻¹ * (γ ^ n * ρ) ^ 2 = (ρ ^ 2 / ‖l‖) * q ^ n :=
      geom_identity ‖l‖ γ ρ q hlam0 hqdef n
    rw [h2]
    exact h1.trans_eq h3
  have hsummable : ∀ w : ℂ, ‖w‖ ≤ ρ → Summable (fun n => t n w) :=
    fun w hw => Summable.of_norm_bounded hu (fun n => hbound n w hw)
  have ht_diff : ∀ n, DifferentiableOn ℂ (t n) (Metric.ball 0 ρ) := by
    intro n
    have hQn : DifferentiableOn ℂ ((Q l)^[n]) (Metric.ball 0 ρ) := (hQd.iterate n).differentiableOn
    exact (hQn.pow 2).const_mul ((l ^ (n + 1))⁻¹)
  have hΨdiff : DifferentiableOn ℂ Ψ (Metric.ball 0 ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm (U := Metric.ball 0 ρ) (F := t)
      hu ht_diff Metric.isOpen_ball (fun n w hw => hbound n w (mem_ball_zero_iff.mp hw).le)
  have hφdiff : DifferentiableOn ℂ φ (Metric.ball 0 ρ) :=
    differentiableOn_id.add hΨdiff
  have hQn0 : ∀ n, (Q l)^[n] (0 : ℂ) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp only [Q]; ring
  have hΨ0 : Ψ 0 = 0 := by
    have hterm : (fun n => t n (0 : ℂ)) = fun _ => (0 : ℂ) := by
      funext n
      simp only [ht, hQn0 n, pow_two, mul_zero]
    show (∑' n, t n (0 : ℂ)) = 0
    rw [hterm, tsum_zero]
  have hφ0 : φ 0 = 0 := by
    show (0 : ℂ) + Ψ 0 = 0
    rw [hΨ0, add_zero]
  have hΨderiv : deriv Ψ 0 = 0 := by
    have hsum := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball 0 ρ) (z := (0 : ℂ))
      (F := t) hu ht_diff Metric.isOpen_ball
      (fun n w hw => hbound n w (mem_ball_zero_iff.mp hw).le) (Metric.mem_ball_self hρ0)
    have hzero : ∀ n, deriv (t n) 0 = 0 := by
      intro n
      have hdF : HasDerivAt ((Q l)^[n]) (deriv ((Q l)^[n]) 0) 0 :=
        ((hQd.iterate n).differentiableAt).hasDerivAt
      have hval : deriv (fun w : ℂ => (l ^ (n + 1))⁻¹ * ((Q l)^[n] w) ^ 2) 0
          = (l ^ (n + 1))⁻¹ * ((2 : ℂ) * ((Q l)^[n] (0 : ℂ)) ^ (2 - 1)
              * deriv ((Q l)^[n]) 0) :=
        ((hdF.pow 2).const_mul ((l ^ (n + 1))⁻¹)).deriv
      have hsame : deriv (t n) 0 = deriv (fun w : ℂ => (l ^ (n + 1))⁻¹ * ((Q l)^[n] w) ^ 2) 0 :=
        rfl
      rw [hsame, hval, hQn0 n]
      ring
    have hfun : (fun n => deriv (t n) 0) = fun _ => (0 : ℂ) := funext hzero
    rw [hfun] at hsum
    exact HasSum.unique hsum hasSum_zero
  have hderivφ : deriv φ 0 = 1 := by
    have h2 : DifferentiableAt ℂ Ψ 0 := hΨdiff.differentiableAt (Metric.ball_mem_nhds 0 hρ0)
    have h := deriv_add (𝕜 := ℂ) differentiableAt_id h2
    have h3 : ((id : ℂ → ℂ) + Ψ) = φ := by funext w; simp only [Pi.add_apply, id_eq, hφ]
    rw [h3, deriv_id, hΨderiv] at h
    rw [h]
    norm_num
  set Φ : ℕ → ℂ → ℂ := fun N w => w + ∑ n ∈ Finset.range N, t n w with hΦ
  have hAlgebra : ∀ (N : ℕ) (z : ℂ), Φ N (Q l z) = l * Φ (N + 1) z := by
    intro N z
    induction N with
    | zero =>
        show (Q l z + ∑ n ∈ Finset.range 0, t n (Q l z)) = l * (z + ∑ n ∈ Finset.range 1, t n z)
        rw [Finset.range_zero, Finset.range_one, Finset.sum_empty, Finset.sum_singleton, add_zero]
        have ht0 : t 0 z = l⁻¹ * z ^ 2 := by
          simp only [ht, Function.iterate_zero_apply]
          norm_num
        rw [ht0, show Q l z = l * z + z ^ 2 from rfl]
        field_simp
    | succ N ih =>
        have hiter : (Q l)^[N] (Q l z) = (Q l)^[N + 1] z :=
          (Function.iterate_succ_apply (Q l) N z).symm
        have hstep : t N (Q l z) = l * t (N + 1) z := by
          simp only [ht, hiter]
          field_simp
          ring
        have ih' : Q l z + ∑ n ∈ Finset.range N, t n (Q l z)
            = l * (z + (∑ n ∈ Finset.range N, t n z + t N z)) := by
          have h := ih
          simp only [hΦ, Finset.sum_range_succ] at h
          exact h
        show (Q l z + ∑ n ∈ Finset.range (N + 1), t n (Q l z))
            = l * (z + ∑ n ∈ Finset.range (N + 1 + 1), t n z)
        simp only [Finset.sum_range_succ, hstep]
        linear_combination ih'
  have hfe : ∀ z ∈ Metric.ball 0 ρ, φ (Q l z) = l * φ z := by
    intro z hz
    have hzlt : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
    have hQz : ‖Q l z‖ ≤ ρ := by
      have h1 : ‖Q l z‖ ≤ ‖z‖ * (‖l‖ + ‖z‖) := by
        rw [show Q l z = l * z + z ^ 2 from rfl]
        calc ‖l * z + z ^ 2‖ ≤ ‖l‖ * ‖z‖ + ‖z‖ ^ 2 :=
              (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_pow])
          _ = ‖z‖ * (‖l‖ + ‖z‖) := by ring
      have h2 : ‖l‖ + ‖z‖ < γ := by
        have hg : γ = ‖l‖ + ρ := by linarith [hρdef]
        rw [hg]; linarith
      have h3 : (0 : ℝ) < ‖l‖ + ‖z‖ := by linarith [hlam0.le, norm_nonneg z]
      have h4 : ‖z‖ * (‖l‖ + ‖z‖) < ρ * γ :=
        calc ‖z‖ * (‖l‖ + ‖z‖) < ρ * (‖l‖ + ‖z‖) := mul_lt_mul_of_pos_right hzlt h3
          _ < ρ * γ := mul_lt_mul_of_pos_left h2 hρ0
      have h5 : ρ * γ ≤ ρ := by nlinarith [hγ1.le, hρ0.le]
      linarith [h1, h4.le, h5]
    have htendz : Tendsto (fun N => Φ N z) atTop (𝓝 (φ z)) :=
      (hsummable z hzlt.le).hasSum.tendsto_sum_nat.const_add z
    have htendQ : Tendsto (fun N => Φ N (Q l z)) atTop (𝓝 (φ (Q l z))) :=
      (hsummable (Q l z) hQz).hasSum.tendsto_sum_nat.const_add (Q l z)
    have htendl : Tendsto (fun N => Φ N (Q l z)) atTop (𝓝 (l * φ z)) := by
      have hshift : Tendsto (fun N => Φ (N + 1) z) atTop (𝓝 (φ z)) :=
        (tendsto_add_atTop_iff_nat 1).mpr htendz
      refine (hshift.const_mul l).congr' ?_
      filter_upwards with N
      exact (hAlgebra N z).symm
    exact tendsto_nhds_unique htendQ htendl
  exact ⟨ρ, φ, hρ0, hφdiff, hφ0, hderivφ, hfe⟩

/-- **Local-inverse step of Koenigs' linearisation.**  If `φ` is holomorphic on `Metric.ball 0 ρ`
(`0 < ρ`), fixes `0`, has `deriv φ 0 = 1` and linearises `Q l` there (`φ (Q l z) = l * φ z`), then
its local inverse `ψ` at `0` (analytic inverse function theorem) satisfies the Koenigs equation
`Q l (ψ w) = ψ (l * w)` near `0`, with `ψ 0 = 0` and `deriv ψ 0 = 1`. -/
theorem inverse_step_local {l : ℂ} (hl : ‖l‖ < 1) {ρ : ℝ} (hρ : 0 < ρ) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 ρ)) (hφ0 : φ 0 = 0) (hdφ : deriv φ 0 = 1)
    (hfe : ∀ z ∈ Metric.ball 0 ρ, φ (Q l z) = l * φ z) :
    ∃ R : ℝ, 0 < R ∧ ∃ ψ : ℂ → ℂ,
      DifferentiableOn ℂ ψ (Metric.ball 0 R) ∧ ψ 0 = 0 ∧ deriv ψ 0 = 1 ∧
      (∀ w ∈ Metric.ball 0 R, Q l (ψ w) = ψ (l * w)) := by
  have hana : AnalyticAt ℂ φ 0 := hφ.analyticAt (Metric.ball_mem_nhds 0 hρ)
  have hfd : deriv φ 0 ≠ 0 := by rw [hdφ]; exact one_ne_zero
  have hf : HasStrictDerivAt φ (deriv φ 0) 0 := hana.hasStrictDerivAt
  let ψ : ℂ → ℂ := HasStrictDerivAt.localInverse φ (deriv φ 0) 0 hf hfd
  have hψ_ana : AnalyticAt ℂ ψ 0 := by
    simpa only [hφ0] using hana.analyticAt_localInverse hfd
  have hψ_cont : ContinuousAt ψ 0 := hψ_ana.continuousAt
  have hψ0 : ψ 0 = 0 := by
    simpa only [hφ0] using (HasStrictDerivAt.eventually_left_inverse (f := φ) (f' := deriv φ 0)
      (a := 0) hf hfd).self_of_nhds
  have hψ_deriv : deriv ψ 0 = 1 := by
    have h := HasDerivAt.deriv (HasStrictDerivAt.hasDerivAt (hf.to_localInverse hfd))
    have h2 : (deriv φ 0)⁻¹ = 1 := by rw [hdφ]; norm_num
    rw [h2] at h
    simpa only [hφ0] using h
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (φ z) = z :=
    HasStrictDerivAt.eventually_left_inverse (f := φ) (f' := deriv φ 0) (a := 0) hf hfd
  have hright : ∀ᶠ z in 𝓝 (0 : ℂ), φ (ψ z) = z := by
    simpa only [hφ0] using
      (HasStrictDerivAt.eventually_right_inverse (f := φ) (f' := deriv φ 0) (a := 0) hf hfd)
  obtain ⟨rA, hrA, hA⟩ := Metric.mem_nhds_iff.mp hleft
  obtain ⟨rB, hrB, hB⟩ := Metric.mem_nhds_iff.mp hright
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    hψ_ana.eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp hev
  set S : ℝ := min (min rA rB) (min ρ ((1 - ‖l‖) / 2)) with hSdef
  have hS0 : 0 < S := by
    rw [hSdef]
    exact lt_min (lt_min hrA hrB) (lt_min hρ (by linarith))
  have hSrA : S ≤ rA := (min_le_left _ _).trans (min_le_left _ _)
  have hSrB : S ≤ rB := (min_le_left _ _).trans (min_le_right _ _)
  have hSρ : S ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hSlam : S ≤ (1 - ‖l‖) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rc, hrc, hc⟩ := Metric.mem_nhds_iff.mp
    (hψ_cont.preimage_mem_nhds (by rw [hψ0]; exact Metric.ball_mem_nhds 0 hS0))
  refine ⟨min S (min rc d), lt_min hS0 (lt_min hrc hd), ψ, ?_, hψ0, hψ_deriv, ?_⟩
  · exact fun y hy =>
      (hdsub (Metric.ball_subset_ball ((min_le_right S (min rc d)).trans
        (min_le_right rc d)) hy)).differentiableWithinAt
  · intro w hw
    have hwR : ‖w‖ < min S (min rc d) := mem_ball_zero_iff.mp hw
    have hRmS : min S (min rc d) ≤ S := min_le_left _ _
    have hRmrc : min S (min rc d) ≤ rc := (min_le_right _ _).trans (min_le_left _ _)
    have hwrc : ‖w‖ < rc := lt_of_lt_of_le hwR hRmrc
    have hψwS : ψ w ∈ Metric.ball 0 S := hc (mem_ball_zero_iff.mpr hwrc)
    have hψwρ : ψ w ∈ Metric.ball 0 ρ := Metric.ball_subset_ball hSρ hψwS
    have hwS : ‖w‖ < S := lt_of_lt_of_le hwR hRmS
    have hwSrB : w ∈ Metric.ball 0 rB := Metric.ball_subset_ball hSrB (mem_ball_zero_iff.mpr hwS)
    have hlw_lt : ‖l * w‖ < min S (min rc d) := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg w) hl.le) hwR
    have hlw_rc : ‖l * w‖ < rc := lt_of_lt_of_le hlw_lt hRmrc
    have hψlwS : ψ (l * w) ∈ Metric.ball 0 S := hc (mem_ball_zero_iff.mpr hlw_rc)
    have hQmem : Q l (ψ w) ∈ Metric.ball 0 S := by
      have hzn : ‖ψ w‖ < S := mem_ball_zero_iff.mp hψwS
      have h1 : ‖Q l (ψ w)‖ ≤ ‖ψ w‖ * (‖l‖ + ‖ψ w‖) := by
        rw [show Q l (ψ w) = l * ψ w + (ψ w) ^ 2 from rfl]
        calc ‖l * ψ w + (ψ w) ^ 2‖ ≤ ‖l‖ * ‖ψ w‖ + ‖ψ w‖ ^ 2 :=
              (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_pow])
          _ = ‖ψ w‖ * (‖l‖ + ‖ψ w‖) := by ring
      have h2 : ‖l‖ + ‖ψ w‖ < 1 := by
        have h3 : ‖l‖ + S ≤ ‖l‖ + (1 - ‖l‖) / 2 := by linarith
        nlinarith [hzn, h3, hS0, hl]
      have h4 : ‖ψ w‖ * (‖l‖ + ‖ψ w‖) < S * 1 := by
        have h4a : ‖ψ w‖ * (‖l‖ + ‖ψ w‖) ≤ ‖ψ w‖ * 1 :=
          mul_le_mul_of_nonneg_left h2.le (norm_nonneg _)
        have h4b : ‖ψ w‖ * 1 < S * 1 := by rw [mul_one, mul_one]; exact hzn
        linarith
      rw [mem_ball_zero_iff]
      linarith
    have heq1 : φ (Q l (ψ w)) = l * w := by rw [hfe (ψ w) hψwρ, hB hwSrB]
    have heq2 : φ (ψ (l * w)) = l * w :=
      hB (Metric.ball_subset_ball hSrB (mem_ball_zero_iff.mpr (lt_of_lt_of_le hlw_lt hRmS)))
    have hkey : φ (Q l (ψ w)) = φ (ψ (l * w)) := by rw [heq1, heq2]
    have h1 : ψ (φ (Q l (ψ w))) = Q l (ψ w) := hA (Metric.ball_subset_ball hSrA hQmem)
    have h2 : ψ (φ (ψ (l * w))) = ψ (l * w) := hA (Metric.ball_subset_ball hSrA hψlwS)
    rw [hkey, h2] at h1
    exact h1.symm

/-- **Koenigs' linearisation of the attracting fixed point.**  Let `Q l x = l * x + x ^ 2`
(`Work.Param.Q`) and suppose `0 < ‖l‖ < 1`.  Then `Q l` is linearisable near the attracting
fixed point `0`: there is `R > 0` and a holomorphic `ψ` on `Metric.ball 0 R` with `ψ 0 = 0`,
`deriv ψ 0 = 1` and `Q l (ψ w) = ψ (l * w)` for `w` in that ball.  (The hypothesis `l ≠ 0` is
necessary: for `l = 0` the equation forces `ψ ≡ 0` on a neighbourhood of `0` and then
`deriv ψ 0 = 0`.) -/
theorem koenigs (l : ℂ) (hl : ‖l‖ < 1) (hl0 : l ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ ψ : ℂ → ℂ,
      DifferentiableOn ℂ ψ (Metric.ball 0 R) ∧ ψ 0 = 0 ∧ deriv ψ 0 = 1 ∧
      (∀ w ∈ Metric.ball 0 R, Q l (ψ w) = ψ (l * w)) := by
  obtain ⟨ρ, φ, hρ, hφdiff, hφ0, hdφ, hfe⟩ := exists_linearizing_map l hl hl0
  exact inverse_step_local hl hρ hφdiff hφ0 hdφ hfe

end

end Work.Param
