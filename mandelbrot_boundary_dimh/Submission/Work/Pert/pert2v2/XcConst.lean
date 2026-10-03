import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.pert2v2.XcV2_deep_legit
import Submission.Work.Pert.pert2v2.XcV2_deriv_bound
import Submission.Work.Pert.pert2v2.Psi_Xc_constant_v2
import Submission.Work.Pert.pert2v2.Xc_ray_mem
import Submission.Work.Parab.Setup

/-!
# `Work.Pert.pert2v2.XcConst`

**The model coherence on the left.**  For a §4.1 datum `d` and a Fatou coordinate `Ψ` of the limit
dynamics `F0f = τ₀ ∘ f₀ ∘ τ₀` on the left cone `Q := Qreg none (some (-Ξ'))`, the periodic function

  `hfun u = Ψ (Xc d u) − u`,   `Xc d u = τ₀ (φ₀ u)`

is **constant on a left half plane**.  The proof uses only already-proved lemmas:

* `pert2v2.Xc_domain_left` — a left half plane lies in the four-fold membership region of the
  curve (`u ∈ Dφ`, `u+1 ∈ Dφ`, `Xc d u ∈ Q`, `Xc d (u+1) ∈ Q`), hence `hfun` is differentiable
  there and `hfun (u+1) = hfun u` (`pert2v2.h_periodic`);
* `pert2v2.XcV2_deriv_bound` — the derivative of `Ψ ∘ Xc d` tends to `1` at the deep left end:
  `‖deriv (Ψ ∘ Xc d) v − 1‖ ≤ C / (−v.re)`.

Hence `deriv hfun` is `1`-periodic and tends to `0` at the left end, so it vanishes identically on
the half plane (for `n` large, `deriv hfun u = deriv hfun (u − n) → 0`), and `hfun` is constant there
by `IsOpen.exists_is_const_of_deriv_eq_zero`.

This is the missing input `(COHER)` of `NOTES_pert2v2_session34.md` §1: it is *not* obtained from
`FatouUnique` on a `Qreg` region (impossible — no `Qreg`-wedge sits inside `QLeft ξ₀`, and `d.φ` is
injective only on `QLeft ξ₀`), but from the derivative bound, which is insensitive to both problems.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set Metric Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- `Qreg none (some (-Ξ')) = {z | z.re + Ξ' < |z.im|}` does not contain `0` when `Ξ' > 0`. -/
theorem zero_notMem_qreg_left {Ξ' : ℝ} (hΞ' : 0 < Ξ') :
    (0 : ℂ) ∉ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
  intro h
  have h' := h.2 (-(Ξ' : ℂ)) (Option.mem_def.mpr rfl)
  simp only [sub_neg_eq_add, zero_add, Complex.ofReal_re, Complex.ofReal_im, abs_zero] at h'
  linarith

/-- **The left half plane is inside the four-fold membership region of the curve.** -/
theorem Xc_domain_left {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' : ℝ}
    (hΞ' : 0 < Ξ') :
    ∃ K : ℝ, ∀ u : ℂ, u.re < -K →
      u ∈ d.Dφ ∧ u + 1 ∈ d.Dφ ∧
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ∧
      Work.Pert.Xc d (u + 1) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
  obtain ⟨N, hN⟩ := XcV2_deep_legit d hΞ'
  refine ⟨max (max N (d.ξ₀ + 1)) 1 + 2, fun u hu => ?_⟩
  have hNM : N ≤ max (max N (d.ξ₀ + 1)) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hξM : d.ξ₀ + 1 ≤ max (max N (d.ξ₀ + 1)) 1 :=
    le_trans (le_max_right N (d.ξ₀ + 1)) (le_max_left _ _)
  have huN : u.re < -N := by linarith
  have huξ : u.re < -d.ξ₀ := by linarith
  have huQ : u ∈ MandelDim.QLeft d.ξ₀ := Work.Parab.halfplane_subset_QLeft d.ξ₀ huξ
  have h1 : u ∈ d.Dφ := d.Q_sub huQ
  have h2 : d.φ u ∈ D₀ := d.Q_maps huQ
  have h3 : u + 1 ∈ d.Dφ := (d.succ_iff u h1).mpr h2
  have hu1 : (u + 1).re < -N := by
    have hre : (u + 1).re = u.re + 1 := by simp
    rw [hre]; linarith
  exact ⟨h1, h3, hN u huN, hN (u + 1) hu1⟩

/-- **The model coherence on the left.**  `hfun u = Ψ (Xc d u) − u` is constant on a left half
plane. -/
theorem Xc_h_const {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) {Ξ' : ℝ} (hΞ' : 0 < Ξ') {Ψ : ℂ → ℂ}
    (hΨ : MandelDim.IsFatouCoordOn
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ
      (MandelDim.Qreg none (some (-(Ξ' : ℂ))))) :
    ∃ K : ℝ, ∃ c : ℂ, ∀ u : ℂ, u.re < -K →
      Ψ (Work.Pert.Xc d u) - u = c := by
  obtain ⟨Nleg, hleg⟩ := XcV2_deep_legit d hΞ'
  obtain ⟨N₀, C, hCpos, hder₀⟩ := XcV2_deriv_bound d hF hΨ hleg
  obtain ⟨K₀, hK₀⟩ := Xc_domain_left d hΞ'
  -- make the left half plane strictly negative, so `u.re < 0` is available
  set K₁ : ℝ := max K₀ 1 with hK₁def
  have hK₀₁ : K₀ ≤ K₁ := le_max_left _ _
  have hK₁₁ : (1 : ℝ) ≤ K₁ := le_max_right _ _
  have hK : ∀ u : ℂ, u.re < -K₁ →
      u ∈ d.Dφ ∧ u + 1 ∈ d.Dφ ∧
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ∧
      Work.Pert.Xc d (u + 1) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
    intro u hu
    exact hK₀ u (by linarith)
  -- normalise the derivative threshold to be `≥ 1`
  set N : ℝ := max N₀ 1 with hNdef
  have hN₁ : (1 : ℝ) ≤ N := le_max_right _ _
  have hder : ∀ v : ℂ, v.re ≤ -N →
      ‖deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) v - 1‖ ≤ C / (-v.re) := by
    intro v hv
    exact hder₀ v (by have := le_max_left N₀ (1 : ℝ); linarith)
  have hQopen : IsOpen (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := isOpen_Qreg_left Ξ'
  set hfun : ℂ → ℂ := fun u => Ψ (Work.Pert.Xc d u) - u with hfun_def
  have hdiff : ∀ u : ℂ, u.re < -K₁ → DifferentiableAt ℂ hfun u := by
    intro u hu
    obtain ⟨h1, -, h3, -⟩ := hK u hu
    have hφne : d.φ u ≠ 0 := by
      intro h0
      have hz : Work.Pert.Xc d u = 0 := by
        simp only [Work.Pert.Xc, h0, MandelDim.tau0, div_zero]
      rw [hz] at h3
      exact zero_notMem_qreg_left hΞ' h3
    rw [hfun_def]
    exact ((hΨ.1.differentiableAt (hQopen.mem_nhds h3)).comp u
      (differentiableAt_Xc d h1 hφne)).sub differentiableAt_id
  have hper : ∀ v : ℂ, v.re < -K₁ → hfun (v + 1) = hfun v := by
    intro v hv
    obtain ⟨h1, h2, h3, h4⟩ := hK v hv
    have hF0 : (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) (Work.Pert.Xc d v)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
      change Work.Pert.F0f f₀ (Work.Pert.Xc d v) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))
      rw [← Xc_add_one' d h1 h2]; exact h4
    have h := h_periodic d hΨ h1 h2 h3 hF0
    show Ψ (Work.Pert.Xc d (v + 1)) - (v + 1) = Ψ (Work.Pert.Xc d v) - v
    exact h
  have hstep : ∀ v : ℂ, v.re < -K₁ - 1 → deriv hfun (v + 1) = deriv hfun v := by
    intro v hv
    have hv1 : v.re < -K₁ := by linarith
    have hv2 : (v + 1).re < -K₁ := by
      have hre : (v + 1).re = v.re + 1 := by simp
      rw [hre]; linarith
    have hopen : IsOpen {w : ℂ | w.re < -K₁} := isOpen_lt continuous_re continuous_const
    have hev : (fun w : ℂ => hfun (w + 1)) =ᶠ[𝓝 v] hfun := by
      filter_upwards [hopen.mem_nhds hv1] with w hw
      exact hper w hw
    have h2 : deriv (fun w : ℂ => hfun (w + 1)) v = deriv hfun (v + 1) := by
      have hcomp := deriv_comp (x := v) (h₂ := hfun) (h := fun w : ℂ => w + 1)
        (hdiff (v + 1) hv2) (differentiableAt_id.add_const (1 : ℂ))
      have hd1 : deriv (fun w : ℂ => w + 1) v = 1 := by
        rw [deriv_add_const (f := fun y : ℂ => y) (c := (1 : ℂ)) (x := v)]
        exact congr_fun (deriv_id'' (𝕜 := ℂ)) v
      rw [hd1, mul_one] at hcomp
      exact hcomp
    exact h2.symm.trans hev.deriv_eq
  have hchain : ∀ n : ℕ, ∀ u : ℂ, u.re < -K₁ - 1 → deriv hfun u = deriv hfun (u - (n : ℂ)) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ k ih =>
      intro u hu
      have hk := ih u hu
      have hrec : (u - ((k : ℕ) : ℂ) - 1).re < -K₁ - 1 := by
        have h1 : (u - ((k : ℕ) : ℂ) - 1).re = u.re - (k : ℝ) - 1 := by
          simp [Complex.sub_re, Complex.one_re]
        rw [h1]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith [hu, hk0]
      have hs := hstep (u - ((k : ℕ) : ℂ) - 1) hrec
      have hkeq : (u - ((k : ℕ) : ℂ) - 1) + 1 = u - ((k : ℕ) : ℂ) := by ring
      rw [hkeq] at hs
      have hsucc : u - (((k + 1 : ℕ)) : ℂ) = u - ((k : ℕ) : ℂ) - 1 := by push_cast; ring
      rw [hsucc, hk]
      exact hs
  have hzero : ∀ u : ℂ, u.re < -K₁ - 1 → deriv hfun u = 0 := by
    intro u hu
    have hule0 : u.re < 0 := by linarith
    refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
    refine le_of_forall_pos_le_add fun ε hε => ?_
    -- find `n` with `N - u.re ≤ n` and `C / (n - u.re) < ε`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, N - u.re ≤ (n : ℝ) ∧ C / ((n : ℝ) - u.re) < ε := by
      obtain ⟨n, hn⟩ := exists_nat_gt (max (N - u.re) (C / ε))
      have h1 : N - u.re ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
      have h2 : C / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have h3 : 0 < (n : ℝ) - u.re := by nlinarith [hN₁, h1]
      have h4 : C < (n : ℝ) * ε := by
        rw [div_lt_iff₀ hε] at h2; linarith
      refine ⟨n, h1, ?_⟩
      rw [div_lt_iff₀ h3]
      nlinarith [h4, hule0]
    have hb : ‖deriv hfun u‖ ≤ C / ((n : ℝ) - u.re) := by
      have hle : (u - (n : ℂ)).re ≤ -N := by
        have h1 : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
        rw [h1]; linarith
      have hle' : (u - (n : ℂ)).re < -K₁ := by
        have h1 : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
        rw [h1]
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      obtain ⟨hd1, -, hd3, -⟩ := hK (u - (n : ℂ)) hle'
      have hφne : d.φ (u - (n : ℂ)) ≠ 0 := by
        intro h0
        have hz : Work.Pert.Xc d (u - (n : ℂ)) = 0 := by
          simp only [Work.Pert.Xc, h0, MandelDim.tau0, div_zero]
        rw [hz] at hd3
        exact zero_notMem_qreg_left hΞ' hd3
      have hsub : deriv hfun (u - (n : ℂ))
          = deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) (u - (n : ℂ)) - 1 := by
        have hfd : DifferentiableAt ℂ (fun w : ℂ => Ψ (Work.Pert.Xc d w)) (u - (n : ℂ)) :=
          (hΨ.1.differentiableAt (hQopen.mem_nhds hd3)).comp (u - (n : ℂ))
            (differentiableAt_Xc d hd1 hφne)
        have hsplit : hfun = (fun w : ℂ => Ψ (Work.Pert.Xc d w)) - id := by
          rw [hfun_def]; rfl
        rw [hsplit, deriv_sub hfd differentiableAt_id, deriv_id]
      have hre : -(u - (n : ℂ)).re = (n : ℝ) - u.re := by
        have h1 : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
        rw [h1]; ring
      rw [hchain n u hu, hsub]
      simpa only [hre] using hder (u - (n : ℂ)) hle
    simpa using le_trans hb (le_of_lt hn.2)
  -- constancy
  have hconst : ∃ c : ℂ, ∀ u : ℂ, u.re < -K₁ - 1 → hfun u = c := by
    have hopen : IsOpen {u : ℂ | u.re < -K₁ - 1} := isOpen_lt continuous_re continuous_const
    have hpc : IsPreconnected {u : ℂ | u.re < -K₁ - 1} := by
      have hlin : IsLinearMap ℝ (fun u : ℂ => u.re) :=
        ⟨fun x y => by simp, fun c x => by simp⟩
      have hc := convex_halfSpace_lt hlin (-K₁ - 1)
      have hset : {u : ℂ | u.re < -K₁ - 1} = {w : ℂ | w.re < -K₁ - 1} := rfl
      rw [hset]
      exact hc.isPreconnected
    have hdo : DifferentiableOn ℂ hfun {u : ℂ | u.re < -K₁ - 1} := by
      intro u hu
      have hu' : u.re < -K₁ - 1 := hu
      exact (hdiff u (by linarith)).differentiableWithinAt
    have hz : Set.EqOn (deriv hfun) 0 {u : ℂ | u.re < -K₁ - 1} := by
      intro u hu
      have hu' : u.re < -K₁ - 1 := hu
      exact hzero u hu'
    obtain ⟨c, hc⟩ := hopen.exists_is_const_of_deriv_eq_zero hpc hdo hz
    exact ⟨c, fun u hu => hc u hu⟩
  obtain ⟨c, hc⟩ := hconst
  refine ⟨K₁ + 1, c, fun u hu => ?_⟩
  have hu' : u.re < -K₁ - 1 := by linarith
  simpa only [hfun_def] using hc u hu'

/-- **Extension of the coherence off the left half plane along a horizontal ray.**  If the
four-fold membership region contains the whole ray `{t + i·w.im | t ≤ w.re}`, and the periodic
function `hfun` is constant on the deep left half plane, then it is constant at `w` too. -/
theorem Xc_h_eq_of_ray {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' : ℝ} {Ψ : ℂ → ℂ}
    (hΨ : MandelDim.IsFatouCoordOn
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))))
    {K : ℝ} {c : ℂ} (hc : ∀ u : ℂ, u.re < -K → Ψ (Work.Pert.Xc d u) - u = c)
    {w : ℂ}
    (hray : ∀ t : ℝ, t ≤ w.re →
      ((t : ℂ) + (w.im : ℂ) * Complex.I ∈ d.Dφ) ∧
      (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1 ∈ d.Dφ) ∧
      (Work.Pert.Xc d ((t : ℂ) + (w.im : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) ∧
      (Work.Pert.Xc d (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))))
    {n : ℕ} (hn : (w - (n : ℂ)).re < -K) :
    Ψ (Work.Pert.Xc d w) - w = c := by
  -- the points `w - j` lie on the ray
  have hpt : ∀ j : ℕ, (w - ((j : ℕ) : ℂ))
      = ((w.re - (j : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    intro j
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.natCast_re, Complex.natCast_im]
  have hray' : ∀ j : ℕ,
      ((w - ((j : ℕ) : ℂ)) ∈ d.Dφ) ∧
      ((w - ((j : ℕ) : ℂ)) + 1 ∈ d.Dφ) ∧
      (Work.Pert.Xc d (w - ((j : ℕ) : ℂ)) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) ∧
      (Work.Pert.Xc d ((w - ((j : ℕ) : ℂ)) + 1) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := by
    intro j
    have hp := hray (w.re - (j : ℝ)) (by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith)
    rwa [← hpt j] at hp
  have hper_step : ∀ j : ℕ, (w - (((j + 1 : ℕ)) : ℂ)) + 1 = w - ((j : ℕ) : ℂ) := by
    intro j; push_cast; ring
  -- the chain `hfun w = hfun (w - j)` for `j ≤ n`
  have hchain : ∀ j : ℕ, j ≤ n →
      (Ψ (Work.Pert.Xc d w) - w) = (Ψ (Work.Pert.Xc d (w - ((j : ℕ) : ℂ)))
        - (w - ((j : ℕ) : ℂ))) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have hrec := ih hk'
      obtain ⟨ha, hb, hc', hd'⟩ := hray' (k + 1)
      have hF0 : (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
          (Work.Pert.Xc d (w - (((k + 1 : ℕ)) : ℂ)))
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
        change Work.Pert.F0f f₀ (Work.Pert.Xc d (w - (((k + 1 : ℕ)) : ℂ)))
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))
        rw [← Xc_add_one' d ha hb]; exact hd'
      have hper := h_periodic d hΨ ha hb hc' hF0
      rw [hper_step k] at hper
      rw [hrec]
      exact hper
  have hfin := hchain n le_rfl
  rw [hfin]
  exact hc (w - (n : ℂ)) hn


/-- **The model coherence at a point of the horizontal ray.**  Combining the half-plane coherence
`Xc_h_const` with the ray membership `Xc_ray_mem` and the chain `Xc_h_eq_of_ray` gives
`Ψ (Xc d w) − w = c` at every `w = x + i y₀` with `x ∈ [0,1)` and `y₀` past the datum threshold. -/
theorem Xc_coher_of_ray {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' → ∃ Y : ℝ, 0 < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ →
      ∀ Ψ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ
        (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
      ∃ c : ℂ, ∀ x : ℝ, 0 ≤ x → x < 1 →
        Ψ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
          - ((x : ℂ) + (y₀ : ℂ) * Complex.I) = c := by
  obtain ⟨Ξ₀, hΞ₀pos, hray⟩ := Xc_ray_mem d
  refine ⟨Ξ₀, hΞ₀pos, fun Ξ' hΞ' => ?_⟩
  obtain ⟨Y, hY⟩ := hray Ξ' hΞ'
  refine ⟨max Y 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun y₀ hy₀ Ψ hΨ => ?_⟩
  obtain ⟨K₀, c, hc₀⟩ := Xc_h_const d hF (lt_of_lt_of_le hΞ₀pos hΞ') hΨ
  -- make `K` positive so that `⌈x + K⌉.toNat` behaves
  set K : ℝ := max K₀ 1 with hKdef
  have hKle : K₀ ≤ K := by simp only [hKdef]; exact le_max_left _ _
  have h1K : (1 : ℝ) ≤ K := by simp only [hKdef]; exact le_max_right _ _
  have hc : ∀ u : ℂ, u.re < -K → Ψ (Work.Pert.Xc d u) - u = c := by
    intro u hu
    exact hc₀ u (by linarith)
  refine ⟨c, fun x hx0 hx1 => ?_⟩
  set w : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hwdef
  have hwim : w.im = y₀ := by simp [hwdef]
  have hwre : w.re = x := by simp [hwdef]
  have hy₀Y : Y ≤ y₀ := le_trans (le_max_left Y 1) hy₀
  -- the ray membership, in the `w.im` form required by `Xc_h_eq_of_ray`
  have hrayw : ∀ t : ℝ, t ≤ w.re →
      ((t : ℂ) + (w.im : ℂ) * Complex.I ∈ d.Dφ) ∧
      (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1 ∈ d.Dφ) ∧
      (Work.Pert.Xc d ((t : ℂ) + (w.im : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) ∧
      (Work.Pert.Xc d (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := by
    intro t ht
    have ht' : t ≤ x := by rw [hwre] at ht; exact ht
    have h := hY y₀ hy₀Y x t hx0 hx1 ht'
    rwa [hwim]
  -- a large `n` with `(w - n).re < -K`
  have hunbdd : ∃ n : ℕ, (w - (n : ℂ)).re < -K := by
    refine ⟨⌈w.re + K⌉.toNat + 1, ?_⟩
    have hce : w.re + K ≤ (⌈w.re + K⌉ : ℝ) := Int.le_ceil _
    have h0 : (0 : ℤ) ≤ ⌈w.re + K⌉ := Int.ceil_nonneg (by
      have : (0 : ℝ) ≤ w.re := by rw [hwre]; exact hx0
      linarith [h1K])
    have hcast : ((⌈w.re + K⌉.toNat : ℕ) : ℝ) = ((⌈w.re + K⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    have hre : (w - ((⌈w.re + K⌉.toNat + 1 : ℕ) : ℂ)).re
        = w.re - (((⌈w.re + K⌉.toNat + 1 : ℕ)) : ℝ) := by simp
    rw [hre]
    have hc1 : (((⌈w.re + K⌉.toNat + 1 : ℕ)) : ℝ) = ((⌈w.re + K⌉ : ℤ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, hcast]
    rw [hc1]
    linarith [hce]
  obtain ⟨n, hn⟩ := hunbdd
  exact Xc_h_eq_of_ray d hΨ hc hrayw hn

/-- **The model coherence at the two points `(RIG)` needs, with the same constant.**  For `Ξ'` and
`y₀` past the datum thresholds there is a constant `c` with `Ψ (Xc d u) − u = c` both at the anchor
`u = −M` (`M ≥ M₀`) and at every segment point `u = x + i y₀`, `x ∈ [0,1)`. -/
theorem Xc_coher_pin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' → ∃ Y : ℝ, 0 < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ →
      ∀ Ψ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ
        (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
      ∃ c : ℂ, ∃ M₀ : ℝ,
        (∀ M : ℝ, M₀ ≤ M → Ψ (Work.Pert.Xc d (-M)) - (-M) = c) ∧
        (∀ x : ℝ, 0 ≤ x → x < 1 →
          Ψ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
            - ((x : ℂ) + (y₀ : ℂ) * Complex.I) = c) := by
  obtain ⟨Ξ₀, hΞ₀pos, hray⟩ := Xc_ray_mem d
  refine ⟨Ξ₀, hΞ₀pos, fun Ξ' hΞ' => ?_⟩
  obtain ⟨Y, hY⟩ := hray Ξ' hΞ'
  refine ⟨max Y 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun y₀ hy₀ Ψ hΨ => ?_⟩
  obtain ⟨K₀, c, hc₀⟩ := Xc_h_const d hF (lt_of_lt_of_le hΞ₀pos hΞ') hΨ
  set K : ℝ := max K₀ 1 with hKdef
  have hKle : K₀ ≤ K := by simp only [hKdef]; exact le_max_left _ _
  have h1K : (1 : ℝ) ≤ K := by simp only [hKdef]; exact le_max_right _ _
  have hc : ∀ u : ℂ, u.re < -K → Ψ (Work.Pert.Xc d u) - u = c := by
    intro u hu
    exact hc₀ u (by linarith)
  have hy₀Y : Y ≤ y₀ := le_trans (le_max_left Y 1) hy₀
  refine ⟨c, max K 1 + 1, ?_, ?_⟩
  · intro M hM
    refine hc (-M) ?_
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith [le_max_left K (1 : ℝ)]
  · intro x hx0 hx1
    set w : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hwdef
    have hwim : w.im = y₀ := by simp [hwdef]
    have hwre : w.re = x := by simp [hwdef]
    have hrayw : ∀ t : ℝ, t ≤ w.re →
        ((t : ℂ) + (w.im : ℂ) * Complex.I ∈ d.Dφ) ∧
        (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1 ∈ d.Dφ) ∧
        (Work.Pert.Xc d ((t : ℂ) + (w.im : ℂ) * Complex.I)
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) ∧
        (Work.Pert.Xc d (((t : ℂ) + (w.im : ℂ) * Complex.I) + 1)
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := by
      intro t ht
      have ht' : t ≤ x := by rw [hwre] at ht; exact ht
      have h := hY y₀ hy₀Y x t hx0 hx1 ht'
      rwa [hwim]
    have hunbdd : ∃ n : ℕ, (w - (n : ℂ)).re < -K := by
      refine ⟨⌈w.re + K⌉.toNat + 1, ?_⟩
      have hce : w.re + K ≤ (⌈w.re + K⌉ : ℝ) := Int.le_ceil _
      have h0 : (0 : ℤ) ≤ ⌈w.re + K⌉ := Int.ceil_nonneg (by
        have : (0 : ℝ) ≤ w.re := by rw [hwre]; exact hx0
        linarith [h1K])
      have hcast : ((⌈w.re + K⌉.toNat : ℕ) : ℝ) = ((⌈w.re + K⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h0
      have hre : (w - ((⌈w.re + K⌉.toNat + 1 : ℕ) : ℂ)).re
          = w.re - (((⌈w.re + K⌉.toNat + 1 : ℕ)) : ℝ) := by simp
      rw [hre]
      have hc1 : (((⌈w.re + K⌉.toNat + 1 : ℕ)) : ℝ) = ((⌈w.re + K⌉ : ℤ) : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one, hcast]
      rw [hc1]
      linarith [hce]
    obtain ⟨n, hn⟩ := hunbdd
    exact Xc_h_eq_of_ray d hΨ hc hrayw hn

end

end Work.Pert.pert2v2
