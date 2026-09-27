import Mathlib
import Submission.Work.Drive.trunc_sqrt_contDiff
import Submission.Work.Drive.flat_jets_bound
import Submission.Work.Drive.contDiff_iteratedDeriv_fst
import Submission.Work.Drive.iteratedDeriv_comp_sq
import Submission.Work.Drive.contDiffOn_even_comp_sqrt

/-!
# Seeley's half-space extension: the shared definitions

This file fixes the objects used by the proof of `Work.Drive.seeley_halfspace_extension`
(seeley's extension construction, Hanusch's infinite-dimensional version).

Given a function `F : X × ℝ → E` which is `C^∞` and even in its second variable (the
"descent" picture, obtained from a function on a half space by composing with `t ↦ t²`),
we want a globally `C^∞` function agreeing with `s ↦ F (x, √s)` on `s ≥ 0`.

Write `c n x = ∂_t^{2n} F (x,0) / (2n)!`,  `T N (x,s) = Σ_{n ≤ N} s^n c n x` and
`S N (x,t) = F (x,t) - T N (x, t²)`.  Then `S N` is flat to order `2N+2` at `t = 0`, so

* `R N := sqrtDesc (S N)` (the descent of `S N`) is `C^N` and
* the answer is `G = T N + R N + (correction)`, where the correction vanishes on `s ≥ 0`
  and is given on `s < 0` by the Seeley series `Σ_j a_j ρ (b_j s) · (…)` for a moment
  sequence `(a,b)`.

-/

open scoped ContDiff Topology
open Filter

namespace Work.Drive

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bump underlying `seeleyRho`. -/
noncomputable def seeleyBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fixed smooth cutoff used by the construction: `1` on `[-1/2, 1/2]`, `0` outside
`(-1, 1)`, with values in `[0,1]`. -/
noncomputable def seeleyRho : ℝ → ℝ := seeleyBump

@[simp] lemma seeleyRho_apply (t : ℝ) : seeleyRho t = seeleyBump t := rfl

lemma seeleyRho_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) seeleyRho :=
  ContDiffBump.contDiff seeleyBump

lemma seeleyRho_eq_one {t : ℝ} (ht : |t| ≤ 1 / 2) : seeleyRho t = 1 := by
  rw [seeleyRho_apply]
  exact ContDiffBump.one_of_mem_closedBall (f := seeleyBump) (c := (0 : ℝ)) (x := t) (by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    simpa [seeleyBump] using ht)

lemma seeleyRho_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : seeleyRho t = 0 := by
  rw [seeleyRho_apply]
  exact ContDiffBump.zero_of_le_dist (f := seeleyBump) (c := (0 : ℝ)) (x := t) (by
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
    simpa [seeleyBump] using ht)

lemma seeleyRho_le_one (t : ℝ) : seeleyRho t ≤ 1 := by
  rw [seeleyRho_apply]; exact ContDiffBump.le_one seeleyBump

/-- The derivatives of `seeleyRho` vanish at `0` (it is locally constant there). -/
lemma seeleyRho_iteratedDeriv_zero (i : ℕ) (hi : 1 ≤ i) :
    iteratedDeriv i seeleyRho 0 = 0 := by
  have hev : seeleyRho =ᶠ[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0:ℝ) < 1 / 4)] with t ht
    refine seeleyRho_eq_one ?_
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] at ht
    have : |t| ≤ 1 / 2 := by linarith [abs_nonneg t]
    exact this
  have h2 := (Filter.EventuallyEq.iteratedDeriv hev i).eq_of_nhds
  have h3 : iteratedDeriv i (fun _ : ℝ => (1 : ℝ)) 0 = 0 := by
    rw [iteratedDeriv_const]
    rcases i with _ | i
    · omega
    · simp
  rw [h2, h3]

/-- The Seeley series: `Σ_j a_j ρ (b_j s) R (x, -b_j s)`.  It is designed to be used for
`s < 0`, where `-b_j s > 0` and the terms are finitely supported. -/
noncomputable def seeleySum (a b : ℕ → ℝ) (R : X × ℝ → E) : X × ℝ → E :=
  fun p => ∑' j, a j • (seeleyRho (b j * p.2) • R (p.1, -(b j * p.2)))

/-- The `n`-th coefficient of the (descent) Taylor series of `F` at `s = 0`:
`∂_t^{2n} F (x,0) / (2n)!`. -/
noncomputable def seeleyCoeff (F : X × ℝ → E) (n : ℕ) (x : X) : E :=
  ((Nat.factorial (2 * n) : ℝ))⁻¹ • iteratedDeriv (2 * n) (fun t : ℝ => F (x, t)) 0

/-- The (descent) Taylor polynomial of order `N`: `Σ_{n ≤ N} s^n c n x`. -/
noncomputable def seeleyTaylor (F : X × ℝ → E) (N : ℕ) : X × ℝ → E :=
  fun p => ∑ n ∈ Finset.range (N + 1), p.2 ^ n • seeleyCoeff F n p.1

/-- `S N (x,t) = F (x,t) - T N (x, t²)`: the Taylor remainder in the `t`-variable, a globally
smooth even function, flat to order `2N+2` at `t = 0`. -/
noncomputable def seeleyRemainder (F : X × ℝ → E) (N : ℕ) : X × ℝ → E :=
  fun p => F p - seeleyTaylor F N (p.1, p.2 ^ 2)

/-- The descent of the remainder: `sqrtDesc (S N)`, a `C^N` function agreeing with
`s ↦ F (x,√s) - T N (x,s)` on `s > 0` and vanishing on `s ≤ 0`. -/
noncomputable def seeleyDescent (F : X × ℝ → E) (N : ℕ) : X × ℝ → E :=
  sqrtDesc (seeleyRemainder F N)

/-- The correction term of the extension: it vanishes on `s ≥ 0` and is given on `s < 0`
by the Seeley series applied to the Taylor polynomial and to the descent of the remainder. -/
noncomputable def seeleyCorr (a b : ℕ → ℝ) (F : X × ℝ → E) (N : ℕ) : X × ℝ → E :=
  fun p => if p.2 < 0 then
      (seeleySum a b (seeleyTaylor F N) p - seeleyTaylor F N p)
        + seeleySum a b (seeleyDescent F N) p
    else 0

/-- The candidate extension: `T N + R N + correction`. -/
noncomputable def seeleyExt (a b : ℕ → ℝ) (F : X × ℝ → E) (N : ℕ) : X × ℝ → E :=
  fun p => seeleyTaylor F N p + seeleyDescent F N p + seeleyCorr a b F N p

/-! ## The Taylor data of a smooth even function -/

lemma seeleyCoeff_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyCoeff F n) :=
  (contDiff_iteratedDeriv_fst hF (2 * n)).const_smul _

lemma seeleyTaylor_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyTaylor F N) := by
  unfold seeleyTaylor
  refine ContDiff.sum (s := Finset.range (N + 1))
    (f := fun n (p : X × ℝ) => p.2 ^ n • seeleyCoeff F n p.1) ?_
  intro n _
  exact (contDiff_snd.pow n).smul ((seeleyCoeff_contDiff hF n).comp contDiff_fst)

lemma seeleyRemainder_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (N : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyRemainder F N) := by
  unfold seeleyRemainder
  exact hF.sub ((seeleyTaylor_contDiff hF N).comp (contDiff_fst.prodMk (contDiff_snd.pow 2)))

lemma seeleyRemainder_even {F : X × ℝ → E} (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t))
    (N : ℕ) (x : X) (t : ℝ) : seeleyRemainder F N (x, -t) = seeleyRemainder F N (x, t) := by
  unfold seeleyRemainder seeleyTaylor
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq, heven x t]

/-- The jets of the descent Taylor polynomial. -/
lemma seeleyTaylor_iteratedDeriv {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (N n : ℕ) (hn : n ≤ N) (x : X) :
    iteratedDeriv n (fun s : ℝ => seeleyTaylor F N (x, s)) 0
      = ((Nat.factorial n : ℕ) : ℝ) • seeleyCoeff F n x := by
  have hfun : (fun s : ℝ => seeleyTaylor F N (x, s))
      = ∑ m ∈ Finset.range (N + 1), (fun s : ℝ => s ^ m • seeleyCoeff F m x) := by
    ext s
    rw [Finset.sum_apply]
    rfl
  rw [hfun]
  rw [iteratedDeriv_sum (fun m _ => (by fun_prop :
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun s : ℝ => s ^ m • seeleyCoeff F m x) 0))]
  trans ∑ m ∈ Finset.range (N + 1), ((if n = m then (Nat.factorial m : ℕ) else 0 : ℝ)) •
      seeleyCoeff F m x
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [iteratedDeriv_smul_const (f := fun s : ℝ => s ^ m) (by fun_prop)
      (seeleyCoeff F m x), iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp
  · rw [Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      rw [if_neg (Ne.symm hmn), zero_smul]
    · intro hn'
      exact absurd (Finset.mem_range.mpr (by omega)) hn'

/-- `S N` is flat to order `2N+2` at `t = 0`. -/
lemma seeleyRemainder_flat {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) (N : ℕ) :
    ∀ i < 2 * N + 2, ∀ x : X,
      iteratedDeriv i (fun t : ℝ => seeleyRemainder F N (x, t)) 0 = 0 := by
  intro i hi x
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => F (x, t)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => seeleyTaylor F N (x, s)) :=
    (seeleyTaylor_contDiff hF N).comp (contDiff_const.prodMk contDiff_id)
  have hP2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => seeleyTaylor F N (x, t ^ 2)) :=
    hP.comp (contDiff_id.pow 2)
  have key : iteratedDeriv i (fun t : ℝ => F (x, t) - seeleyTaylor F N (x, t ^ 2)) 0 = 0 := by
    rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj, ← Nat.two_mul]
      change iteratedDeriv (2 * j) ((fun t : ℝ => F (x, t))
        - (fun t : ℝ => seeleyTaylor F N (x, t ^ 2))) 0 = 0
      rw [iteratedDeriv_sub (f := fun t : ℝ => F (x, t))
          (g := fun t : ℝ => seeleyTaylor F N (x, t ^ 2))
          (hF'.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hP2.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
      have hjN : j ≤ N := by omega
      rw [iteratedDeriv_comp_sq (φ := fun s : ℝ => seeleyTaylor F N (x, s)) hP j,
        seeleyTaylor_iteratedDeriv hF N j hjN x]
      have hL : iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0
          = ((Nat.factorial (2 * j) : ℕ) : ℝ) • seeleyCoeff F j x := by
        rw [show seeleyCoeff F j x = (((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹ •
              iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0 from rfl,
          smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      have hR : (((Nat.factorial (2 * j) : ℕ) : ℝ) / ((Nat.factorial j : ℕ) : ℝ)) •
            (((Nat.factorial j : ℕ) : ℝ) • seeleyCoeff F j x)
          = ((Nat.factorial (2 * j) : ℕ) : ℝ) • seeleyCoeff F j x := by
        rw [smul_smul,
          show (((Nat.factorial (2 * j) : ℕ) : ℝ) / ((Nat.factorial j : ℕ) : ℝ)) *
              ((Nat.factorial j : ℕ) : ℝ) = ((Nat.factorial (2 * j) : ℕ) : ℝ) from by
            rw [div_mul_cancel₀ _ (by positivity)]]
      rw [hL, hR, sub_self]
    · rw [hj]
      change iteratedDeriv (2 * j + 1) ((fun t : ℝ => F (x, t))
        - (fun t : ℝ => seeleyTaylor F N (x, t ^ 2))) 0 = 0
      rw [iteratedDeriv_sub (f := fun t : ℝ => F (x, t))
          (g := fun t : ℝ => seeleyTaylor F N (x, t ^ 2))
          (hF'.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hP2.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_odd_eq_zero_of_even (g := fun t : ℝ => F (x, t)) (fun t => heven x t) j,
        iteratedDeriv_odd_eq_zero_of_even
          (g := fun t : ℝ => seeleyTaylor F N (x, t ^ 2)) (fun t => by rw [neg_sq]) j,
        sub_zero]
  simpa only [seeleyRemainder] using key

/-- The jet bounds for `S N` coming from its flatness at `t = 0`. -/
lemma seeleyRemainder_bounds {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) (N : ℕ) :
    ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ 2 * N + 2 →
        ‖iteratedFDeriv ℝ j (seeleyRemainder F N) (x, t)‖ ≤ C * t ^ (2 * N + 2 - j) :=
  flat_jets_bound (seeleyRemainder_contDiff hF N) (seeleyRemainder_flat hF heven N)

/-- The descent `R N` is `C^N`. -/
lemma seeleyDescent_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) (N : ℕ) :
    ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (seeleyDescent F N) :=
  trunc_sqrt_contDiff (K := 2 * N + 2) (m := N) (by omega)
    (fun z _ => (seeleyRemainder_contDiff hF N).contDiffAt)
    (seeleyRemainder_bounds hF heven N)

/-- On the open upper half plane the descent is the expected value. -/
lemma seeleyDescent_eq {F : X × ℝ → E} {N : ℕ} {x : X} {σ : ℝ} (hσ : 0 < σ) :
    seeleyDescent F N (x, σ) = seeleyRemainder F N (x, Real.sqrt σ) := by
  simp [seeleyDescent, sqrtDesc, hσ]

/-- On the closed lower half plane the descent vanishes. -/
lemma seeleyDescent_eq_zero {F : X × ℝ → E} {N : ℕ} {x : X} {σ : ℝ} (hσ : σ ≤ 0) :
    seeleyDescent F N (x, σ) = 0 := by
  simp [seeleyDescent, sqrtDesc, not_lt.mpr hσ]

/-- The descent is smooth on the open upper half plane. -/
lemma seeleyDescent_contDiffAt {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {N : ℕ} {z : X × ℝ} (hz : 0 < z.2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyDescent F N) z :=
  contDiffAt_sqrtDesc_of_pos (fun w _ => (seeleyRemainder_contDiff hF N).contDiffAt) z hz

end Work.Drive
