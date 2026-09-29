import Mathlib
import Submission.Work.C17.logPw_setup
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.defs
import Submission.Work.C17I.stadium_facts
import Submission.Work.C17I.xs_facts
import Submission.Work.C17I.sw_p0_lt
import Submission.Work.C17I.q4x_roots
import Submission.Work.C17I.phi_chain_rule
import Submission.Work.C17I.pullback_identity
import Submission.Work.C17I.linear_ode_unique
import Submission.Work.C17I.ode_coeff_diff
import Submission.Work.C17I.logPCoeffQ_diff
import Submission.Work.C17I.logP_series_diverges
import Submission.Work.C17I.lens_eq_ball
import Submission.Work.C17.Pfun_hasSum
import Submission.Work.C17f.Pfun_solves_M
import Submission.Work.C17g.linear_ode_convex

namespace Work.C17I

open scoped BigOperators

noncomputable section

/-! ## A small auxiliary estimate -/

lemma sixth_le_norm_sw {z : ℂ} (hzre : (1 / 5 : ℝ) ≤ z.re) (hz1 : z ≠ 1) :
    (1 / 6 : ℝ) ≤ ‖Work.C17I.sw z‖ := by
  have hz5 : (1 / 5 : ℝ) ≤ ‖z‖ := le_trans hzre (Complex.re_le_norm z)
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have h6 : ‖z - 1‖ ≤ 6 * ‖z‖ := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
      _ = ‖z‖ + 1 := by simp
      _ ≤ ‖z‖ + 5 * ‖z‖ := by linarith
      _ = 6 * ‖z‖ := by ring
  have hz1pos : (0 : ℝ) < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hz1
  rw [Work.C17I.sw, norm_div]
  have hkey : ‖z‖ / (6 * ‖z‖) ≤ ‖z‖ / ‖z - 1‖ :=
    div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) h6
  have heq : ‖z‖ / (6 * ‖z‖) = 1 / 6 := by
    field_simp
  rwa [heq] at hkey

/-! ## The main assembly -/

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# Continuation of `P ∘ φ` to a convex stadium

`P = logP a b ra rb rab r0` is the "unlikely" series of Theorem C of arXiv:2408.15403
(`a = 2m+1`, `b = 2n+1`), `x_s = xsOf m n` is its Taylor radius, `φ(z) = z/(z-1)`.
The claim continues the *composition* `P ∘ φ` from the region where the series converges
(`‖φ z‖ < x_s`, where it equals `Pfun (φ z)`) to a convex open set `S` containing a ball around
the cusp `x_s` and a ball around the "safe harbour" point `p₀ = 1/4 + i/5 = Work.C17.p0C`.

Availability / route (all ingredients are already in the workspace):
* `Work.C17.logPw_setup` defines `QtilC, pi2C, pi1C, pi0C, rhoTil, odeP, odeQ, odeR`, the data of
  the *pulled back* equation `u'' + odeP·u' + odeQ·u = odeR` (equivalently, the cleared form
  `π₂(z-1)² u'' + (2π₂-π₁)(z-1) u' + π₀ u = ρ̃(z-1)`), which `u = Pfun ∘ φ` satisfies wherever the
  series converges.  This follows from `Work.C17f.Pfun_solves_M` (function-level `M(Pfun) = rhoMx`)
  by the chain rule (`PowerSeries.derivative_subst` and `PowerSeries.subst_mul` over `ℚ⟦x⟧`).
* `Work.C17g.linear_ode_convex` (proved): a linear system `Y' = A z · Y + b z` with holomorphic
  `A, b` on a *convex* open set `S` has a global holomorphic solution on `S` with prescribed
  initial data; use `k = 2` and the vector `Y = (u, u')`.
* The singular points of the pulled-back equation are `0`, `1/2`, `1` and the four cusp images
  `φ(x_{±±})`; the two positive/inverted ones satisfy `|φ(x_{±±})| > 1`, and the two remaining
  ones are negative reals, hence outside a convex `S` whose real parts are `≥ 1/5`.
  (`Work.CLoc` contains the corresponding estimates for the four cusp values in the admissible
  range; adapt or redo them for `φ`.)
* `x_s ≥ 1/2` (indeed `x_s ≥ 1 - 10⁻⁵`) follows from the gap hypothesis; then
  `‖p₀/(p₀-1)‖ < x_s`, so the series `Pfun (z/(z-1))` converges on a neighbourhood of `p₀` and the
  solution of the ODE may be matched with it at `p₀`.
* `S := Work.C17.stadiumSet (xsOf m n) ((1 - xsOf m n)/2) (1/20)` (or the convex hull of the two
  open balls) satisfies the set-theoretic requirements, including `S ⊆ ball 0 1` and `0 ∉ S`.

We only need the *existence* of `S` and `Ψ` (the specific shape of `S` is not used downstream).

Helper auxiliary results may be added above the claim; do not change the claim. -/
theorem pw_continuation (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ) :
    ∃ S : Set ℂ, Convex ℝ S ∧ IsOpen S ∧
      Metric.ball ((Work.C17.xsOf m n : ℂ)) ((1 - Work.C17.xsOf m n) / 2) ⊆ S ∧
      Metric.ball Work.C17.p0C (1 / 20) ⊆ S ∧ (0 : ℂ) ∉ S ∧
      S ⊆ Metric.ball (0 : ℂ) 1 ∧
      ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ S ∧
        ∀ z ∈ S, ‖z / (z - 1)‖ < Work.C17.xsOf m n →
          Ψ z = Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 (z / (z - 1)) := by
  obtain ⟨hx0, hx2, hx1⟩ := xs_facts m n hm hlt hgap
  have hxlt : Work.C17.xsOf m n < 1 := Work.C17.xsOf_lt_one m n hm hlt
  obtain ⟨hSconv, hSopen, hball1, hball2, h0S, hSball, hSre, hhalfS⟩ :=
    stadium_facts m n hx0 hx1 hx2
  obtain ⟨hroots, hP2⟩ := q4x_roots m n hm hlt hSball hSre hhalfS
  have hp0mem : Work.C17.p0C ∈ Sset m n := hball2 (Metric.mem_ball_self (by norm_num))
  have hne1 : ∀ z ∈ Sset m n, z ≠ 1 := by
    intro z hz hz1
    have h := hSball hz
    rw [Metric.mem_ball, dist_zero_right, hz1] at h
    simp at h
  -- the lens is a disc (off `1`); since `S` avoids `1`, `S ∩ lens` is convex and open
  have hS'lens : Sset m n ∩ lens (Work.C17.xsOf m n) =
      Sset m n ∩ Metric.ball ((-((Work.C17.xsOf m n) ^ 2) / (1 - (Work.C17.xsOf m n) ^ 2) : ℝ) : ℂ)
        ((Work.C17.xsOf m n) / (1 - (Work.C17.xsOf m n) ^ 2)) := by
    rw [← lens_eq_ball (Work.C17.xsOf m n) hx0 hxlt]
    ext z; constructor
    · rintro ⟨hzS, hzl⟩; exact ⟨hzS, hzl, hne1 z hzS⟩
    · rintro ⟨hzS, hzl, -⟩; exact ⟨hzS, hzl⟩
  have hS'conv : Convex ℝ (Sset m n ∩ lens (Work.C17.xsOf m n)) := by
    rw [hS'lens]; exact hSconv.inter (convex_ball _ _)
  have hS'open : IsOpen (Sset m n ∩ lens (Work.C17.xsOf m n)) := by
    rw [hS'lens]; exact hSopen.inter Metric.isOpen_ball
  have hp0lens : Work.C17.p0C ∈ lens (Work.C17.xsOf m n) := sw_p0_lt m n hx1
  have ha3 : (3 : ℚ) ≤ Work.C17.aOf m := by
    unfold Work.C17.aOf
    have : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    linarith
  have hb3 : (3 : ℚ) ≤ Work.C17.aOf n := by
    unfold Work.C17.aOf
    have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hab : Work.C17.aOf m < Work.C17.aOf n := by
    unfold Work.C17.aOf
    have : (m : ℚ) < (n : ℚ) := by exact_mod_cast hlt
    linarith
  by_cases hA : (ra : ℝ) * Submission.CDT.beukersEta ((Work.C17.aOf m : ℚ) : ℝ)
      + (rb : ℝ) * Submission.CDT.beukersEta ((Work.C17.aOf n : ℚ) : ℝ)
      + (rab : ℝ) * (Submission.CDT.beukersEta ((Work.C17.aOf m : ℚ) : ℝ)
          * Submission.CDT.beukersEta ((Work.C17.aOf n : ℚ) : ℝ)) = (r0 : ℝ)
  · -- #### Case A = 0: the unlikely case; the series converges on the lens
    have hconv := Work.C17.Pfun_hasSum (Work.C17.aOf m) (Work.C17.aOf n) ha3 hb3 hab ra rb rab r0 hA
    have hdiff := ode_coeff_diff m n ra rb rab hSopen hne1 hP2
    obtain ⟨Ψv, hΨvd, hΨv0, hΨvode⟩ :=
      Work.C17g.linear_ode_convex hSconv hSopen (A2 (Work.C17.aOf m) (Work.C17.aOf n))
        (B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab) hdiff.1 hdiff.2 (Work.C17.p0C) hp0mem
        (PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 (Work.C17.p0C))
    refine ⟨Sset m n, hSconv, hSopen, hball1, hball2, h0S, hSball, (fun z => Ψv z 0), ?_, ?_⟩
    · exact (differentiableOn_pi.mp hΨvd) 0
    · intro z hz hzlens
      have hz' : z ∈ Sset m n ∩ lens (Work.C17.xsOf m n) := ⟨hz, hzlens⟩
      -- ΦVec solves the system on `S ∩ lens`
      have hΦode : ∀ w ∈ Sset m n ∩ lens (Work.C17.xsOf m n),
          HasDerivAt (PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)
            (fun i => ∑ j, A2 (Work.C17.aOf m) (Work.C17.aOf n) w i j
                * PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w i) w := by
        intro w hw
        obtain ⟨hwS, hwlens⟩ := hw
        have hw1 : w ≠ 1 := hne1 w hwS
        have hwp2 : pp2 (Work.C17.aOf m) (Work.C17.aOf n) w ≠ 0 := hP2 w hwS
        have hwlens' : ‖sw w‖ < Work.C17.xs (Work.C17.aOf m) (Work.C17.aOf n) := by
          rw [Work.C17.xsOf_eq_xs]; exact hwlens
        obtain ⟨hΦd, hΦd1, hΦdd, hΦd2⟩ :=
          phi_chain_rule (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 hconv w hw1 hwlens'
        have hM := Work.C17f.Pfun_solves_M (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0
          hconv (sw w) hwlens'
        have hident := pullback_identity (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w hw1 hwp2
          hΦd1 hΦd2 hM
        have hf0 : (fun x => PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 x 0)
            = PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 := by
          funext x; simp [PhiVec]
        have hf1 : (fun x => PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 x 1)
            = deriv (PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) := by
          funext x; simp [PhiVec]
        have hv0 : (∑ j : Fin 2, A2 (Work.C17.aOf m) (Work.C17.aOf n) w 0 j
              * PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w 0)
            = deriv (PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) w := by
          simp [A2, B2, PhiVec, Fin.sum_univ_two]
        have hv1 : (∑ j : Fin 2, A2 (Work.C17.aOf m) (Work.C17.aOf n) w 1 j
              * PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w 1)
            = deriv (deriv (PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)) w := by
          have h2 : deriv (deriv (PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)) w
              = -odQ (Work.C17.aOf m) (Work.C17.aOf n) w
                  * PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w
                - odP (Work.C17.aOf m) (Work.C17.aOf n) w
                  * deriv (PhiC (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) w
                + odR (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w := by
            rw [← hident]; ring
          rw [h2]; simp [A2, B2, PhiVec, Fin.sum_univ_two]; ring
        rw [hasDerivAt_pi]
        intro i
        fin_cases i
        · show HasDerivAt (fun x => PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 x 0)
            (∑ j : Fin 2, A2 (Work.C17.aOf m) (Work.C17.aOf n) w 0 j
              * PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w 0) w
          rw [hf0, hv0]; exact hΦd.hasDerivAt
        · show HasDerivAt (fun x => PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 x 1)
            (∑ j : Fin 2, A2 (Work.C17.aOf m) (Work.C17.aOf n) w 1 j
              * PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w 1) w
          rw [hf1, hv1]; exact hΦdd.hasDerivAt
      have hΨode' : ∀ w ∈ Sset m n ∩ lens (Work.C17.xsOf m n),
          HasDerivAt Ψv (fun i => ∑ j, A2 (Work.C17.aOf m) (Work.C17.aOf n) w i j * Ψv w j
              + B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab w i) w :=
        fun w hw => hΨvode w hw.1
      have heq := linear_ode_unique hS'conv hS'open (A2 (Work.C17.aOf m) (Work.C17.aOf n))
        (B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab)
        (hdiff.1.continuousOn.mono Set.inter_subset_left) Ψv
        (PhiVec (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) hΨode' hΦode
        ⟨hp0mem, hp0lens⟩ hΨv0
      have hcomp := congrFun (heq z hz') 0
      simpa [PhiVec, PhiC, sw] using hcomp
  · -- #### Case A ≠ 0: the series never converges on `S`, so `Ψ = 0` works
    refine ⟨Sset m n, hSconv, hSopen, hball1, hball2, h0S, hSball, (fun _ => 0),
      differentiableOn_const 0, ?_⟩
    intro z hz hzlens
    have hns := logP_series_diverges (Work.C17.aOf m) (Work.C17.aOf n) ha3 hb3 ra rb rab r0 hA
      (sw z) (sixth_le_norm_sw (hSre z hz) (hne1 z hz))
    have hzero : Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 (z / (z - 1)) = 0 := by
      simpa [Work.C17.Pfun, sw] using tsum_eq_zero_of_not_summable hns
    rw [hzero]



end

end Work.C17I
