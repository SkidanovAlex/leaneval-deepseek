import Mathlib
import Submission.Work.Drive.seeleyDefs
import Submission.Work.Drive.momentSequences
import Submission.Work.Drive.seeleyEps_flat
import Submission.Work.Drive.seeleyDescent_bounds
import Submission.Work.Drive.seeleySum_bounds
import Submission.Work.Drive.seeleySum_bounds_local
import Submission.Work.Drive.seeleySum_taylor_eq
import Submission.Work.Drive.seeleySum_taylor_flat
import Submission.Work.Drive.contDiffAt_of_flat_halfspace_bounds

/-!
# Extension of the even `√`-descent (Seeley's construction)

`Work.Drive.seeleyDescent_ext`: if `F : X × ℝ → E` is `C^∞` and even in its second variable, then
`s ↦ F (x, √s)` on `s ≥ 0` extends to a globally `C^∞` function.

Route (Seeley, see Hanusch arXiv:2002.05125): with a moment sequence `(a,b)`
(`∑_j a_j b_j^q = (-1)^q`, `∑_j |a_j| b_j^q < ∞`) one defines the extension on the lower half plane
by the series `G (x,s) = ∑_j a_j ρ (b_j s) F (x, √(-(b_j s)))` (`ρ` a cutoff which is `1` near `0`
and vanishes for `|t| ≥ 1`).  Only finitely many summands are non-zero near any point with `s ≠ 0`,
so `G` is smooth off the axis; near the axis, for each `n` one writes
`G - T n - R n = (seeleySum a b (seeleyTaylor F n) - seeleyTaylor F n) + seeleySum a b (seeleyDescent F n)`
on the lower half plane, where the two summands are flat of order `n+1`
(`Work.Drive.seeleySum_taylor_flat` and `Work.Drive.seeleySum_bounds_local` plus
`Work.Drive.seeleyDescent_bounds`), so `G` is `C^n` at the axis by the flat gluing lemma
`Work.Drive.contDiffAt_of_flat_halfspace_bounds`.
-/

open scoped ContDiff Topology
open Filter Set

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The moment sequence -/

/-- A packaged form of `Work.Drive.momentSequences`, with the absolute-moment summability. -/
theorem momentSeqExists :
    ∃ a b : ℕ → ℝ, (∀ j : ℕ, 0 < b j) ∧ Filter.Tendsto b Filter.atTop Filter.atTop ∧
      (∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) ∧
      (∀ q : ℕ, ∑' j : ℕ, a j * (b j) ^ q = (-1 : ℝ) ^ q) := by
  obtain ⟨a, b, hb, _hmono, hbtend, hsum, hmom⟩ := momentSequences
  refine ⟨a, b, hb, hbtend, fun q => ?_, hmom⟩
  have h := (hsum q).abs
  refine h.congr (fun j => ?_)
  rw [abs_mul, abs_of_pos (pow_pos (hb j) q)]

/-! ## Finite support of the Seeley series on the lower half plane -/

/-- For `s < 0` the cutoff argument `b j * s` eventually drops below any prescribed negative
level. -/
theorem seeleyRho_mul_le_of_pos {b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) {s : ℝ} (hs : s < 0) {c : ℝ}
    (hc : 0 < c) : ∃ J : ℕ, ∀ j ≥ J, b j * s ≤ -c := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
    (hbtend.eventually (Filter.eventually_ge_atTop (c / (-s))))
  refine ⟨J, fun j hj => ?_⟩
  have h1 : c / (-s) ≤ b j := hJ j hj
  have hsne : s ≠ 0 := ne_of_lt hs
  have h3 : (c / (-s)) * s = -c := by
    field_simp
  have h4 : b j * s ≤ (c / (-s)) * s := mul_le_mul_of_nonpos_right h1 hs.le
  linarith

/-- For `s < 0` the cutoff `ρ (b j s)` vanishes for all large `j`. -/
theorem seeleyRho_mul_pos_eventually_zero {b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) {s : ℝ} (hs : s < 0) :
    ∃ J : ℕ, ∀ j ≥ J, seeleyRho (b j * s) = 0 := by
  obtain ⟨J, hJ⟩ := seeleyRho_mul_le_of_pos hb hbtend hs (c := 1) one_pos
  refine ⟨J, fun j hj => ?_⟩
  refine seeleyRho_eq_zero ?_
  rw [abs_of_neg (mul_neg_of_pos_of_neg (hb j) hs)]
  linarith [hJ j hj]

/-- On the lower half plane the Seeley series is a finite sum. -/
theorem seeleySum_eq_sum_of_forall_zero {a b : ℕ → ℝ} (R : X × ℝ → E) {J : ℕ} {x : X} {s : ℝ}
    (hJ : ∀ j ≥ J, seeleyRho (b j * s) = 0) :
    seeleySum a b R (x, s)
      = ∑ j ∈ Finset.range J, a j • (seeleyRho (b j * s) • R (x, -(b j * s))) := by
  change (∑' j : ℕ, a j • (seeleyRho (b j * s) • R (x, -(b j * s))))
    = ∑ j ∈ Finset.range J, a j • (seeleyRho (b j * s) • R (x, -(b j * s)))
  refine tsum_eq_sum (fun j hj => ?_)
  have hjJ : J ≤ j := by
    by_contra h
    exact hj (Finset.mem_range.mpr (by omega))
  rw [hJ j hjJ, zero_smul, smul_zero]

/-- On the lower half plane the Seeley series is a finite sum (existential form). -/
theorem seeleySum_eq_sum_of_neg {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) (R : X × ℝ → E) {x : X} {s : ℝ}
    (hs : s < 0) :
    ∃ J : ℕ, seeleySum a b R (x, s)
      = ∑ j ∈ Finset.range J, a j • (seeleyRho (b j * s) • R (x, -(b j * s))) :=
  let ⟨J, hJ⟩ := seeleyRho_mul_pos_eventually_zero hb hbtend hs
  ⟨J, seeleySum_eq_sum_of_forall_zero R hJ⟩

/-- **Additivity of the Seeley series on the lower half plane**, from a pointwise identity which is
only required where the series is evaluated (i.e. on the open upper half plane). -/
theorem seeleySum_add_of_neg {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) {R₁ R₂ R₃ : X × ℝ → E}
    (hadd : ∀ p : X × ℝ, 0 < p.2 → R₃ p = R₁ p + R₂ p) {x : X} {s : ℝ} (hs : s < 0) :
    seeleySum a b R₃ (x, s) = seeleySum a b R₁ (x, s) + seeleySum a b R₂ (x, s) := by
  obtain ⟨J, hJ⟩ := seeleyRho_mul_pos_eventually_zero hb hbtend hs
  rw [seeleySum_eq_sum_of_forall_zero (a := a) (b := b) R₃ hJ,
    seeleySum_eq_sum_of_forall_zero (a := a) (b := b) R₁ hJ,
    seeleySum_eq_sum_of_forall_zero (a := a) (b := b) R₂ hJ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjpos : 0 < -(b j * s) := by
    have := hb j
    nlinarith [hs, this]
  rw [hadd (x, -(b j * s)) hjpos, smul_add, smul_add]

/-! ## Smoothness of the Seeley series off the axis -/

/-- The Seeley series is smooth at every point of the open lower half plane, provided `R` is smooth
on the open upper half plane. -/
theorem contDiffAt_seeleySum_of_neg {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) {R : X × ℝ → E}
    (hR : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    {z : X × ℝ} (hz : z.2 < 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleySum a b R) z := by
  obtain ⟨J, hJ⟩ := seeleyRho_mul_le_of_pos hb hbtend hz (c := 2) (by norm_num)
  have hfin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : X × ℝ => ∑ j ∈ Finset.range J,
        a j • (seeleyRho (b j * y.2) • R (y.1, -(b j * y.2)))) z := by
    refine ContDiffAt.sum (fun j _ => ?_)
    have hz2 : (0 : ℝ) < -(b j * z.2) := by
      have := hb j; nlinarith
    have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : X × ℝ => (y.1, -(b j * y.2))) z := by
      refine contDiffAt_fst.prodMk ?_
      simpa only [neg_mul] using
        (contDiffAt_const (c := -(b j)) (x := z)).mul (contDiffAt_snd (p := z))
    have hρ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : X × ℝ => seeleyRho (b j * y.2)) z :=
      seeleyRho_contDiff.contDiffAt.comp z
        ((contDiffAt_const (c := b j) (x := z)).mul (contDiffAt_snd (p := z)))
    exact (ContDiffAt.const_smul (a j)) (hρ.smul ((hR _ hz2).comp z hmap))
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds
    (by linarith : z.2 < z.2 / 2)] with y hy
  refine seeleySum_eq_sum_of_forall_zero R (fun j hj => ?_)
  refine seeleyRho_eq_zero ?_
  have hy2 : y.2 < 0 := by linarith
  have h1 : b j * y.2 < b j * (z.2 / 2) := mul_lt_mul_of_pos_left hy (hb j)
  have h2 : b j * (z.2 / 2) = (b j * z.2) / 2 := by ring
  have h3 : (b j * z.2) / 2 ≤ -1 := by linarith [hJ j hj]
  have h4 : b j * y.2 ≤ -1 := by linarith
  rw [abs_of_neg (mul_neg_of_pos_of_neg (hb j) hy2)]
  linarith


/-! ## The gluing lemma for functions vanishing above the axis -/

/-- The reflection `(x, s) ↦ (x, -s)`, as a continuous linear map. -/
noncomputable def reflCLM : (X × ℝ) →L[ℝ] (X × ℝ) :=
  (ContinuousLinearMap.fst ℝ X ℝ).prod ((-1 : ℝ) • ContinuousLinearMap.snd ℝ X ℝ)

lemma reflCLM_apply (p : X × ℝ) : reflCLM (X := X) p = (p.1, -p.2) := by
  simp [reflCLM]

lemma reflCLM_norm (p : X × ℝ) : ‖reflCLM (X := X) p‖ = ‖p‖ := by
  rw [reflCLM_apply, Prod.norm_def, Prod.norm_def]
  simp

lemma reflCLM_norm_le : ‖reflCLM (X := X)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => ?_)
  rw [reflCLM_norm, one_mul]

/-- **Gluing at the axis.**  A function which vanishes on the closed upper half plane, is `C^∞`
on the lower half plane and whose derivatives of order `k ≤ n` there are bounded by
`C |z.2| ^ (n + 1 - k)` is `C^n` at `(x₀, 0)`. -/
theorem contDiffAt_of_flat_upper_bounds {Φ : X × ℝ → E} {x₀ : X} {n : ℕ} {R : ℝ}
    (hR : 0 < R)
    (hz : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < R → 0 ≤ z.2 → Φ z = 0)
    (hC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
      (Metric.ball (x₀, 0) R ∩ {z : X × ℝ | z.2 < 0}))
    (hb : ∀ k ≤ n, ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < R → z.2 < 0 →
      ‖iteratedFDeriv ℝ k Φ z‖ ≤ C * |z.2| ^ (n + 1 - k)) :
    ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) Φ (x₀, 0) := by
  set U : Set (X × ℝ) := Metric.ball (x₀, 0) R ∩ {z : X × ℝ | z.2 < 0} with hU
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_snd continuous_const)
  have hmemU : ∀ p : X × ℝ, ‖p - (x₀, 0)‖ < R → p.2 < 0 → p ∈ U := by
    intro p h1 h2
    exact ⟨Metric.mem_ball.mpr (by rwa [dist_eq_norm]), h2⟩
  have hdist : ∀ p : X × ℝ, ‖reflCLM (X := X) p - (x₀, 0)‖ = ‖p - (x₀, 0)‖ := by
    intro p
    rw [reflCLM_apply, Prod.norm_def, Prod.norm_def]
    simp
  set f : X × ℝ → E := fun p => Φ (p.1, -p.2) with hf
  have hfeq : f = Φ ∘ reflCLM (X := X) := by funext p; simp [hf, reflCLM_apply]
  have hflat : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) f (x₀, 0) := by
    refine contDiffAt_of_flat_halfspace_bounds (f := f) hR ?_ ?_ ?_
    · intro z hz1 hz2
      have h2 : ‖(z.1, -z.2) - (x₀, 0)‖ = ‖z - (x₀, 0)‖ := by
        rw [← reflCLM_apply (X := X) z]; exact hdist z
      exact hz (z.1, -z.2) (by rw [h2]; exact hz1) (by linarith)
    · intro p hp
      have hpR : ‖p - (x₀, 0)‖ < R := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hp.1
      have hp2 : 0 < p.2 := hp.2
      have h2 : ‖reflCLM (X := X) p - (x₀, 0)‖ < R := by rw [hdist p]; exact hpR
      have h3 : (reflCLM (X := X) p).2 < 0 := by
        rw [reflCLM_apply]; simpa using hp2
      have hmem := hmemU _ h2 h3
      have hΦ : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) Φ (reflCLM (X := X) p) :=
        ((hC.contDiffWithinAt hmem).contDiffAt (hUopen.mem_nhds hmem)).of_le
          (WithTop.coe_le_coe.mpr le_top)
      rw [hfeq]
      exact (hΦ.comp p ((reflCLM (X := X)).contDiff.contDiffAt)).contDiffWithinAt
    · intro k hk
      obtain ⟨C, hCb⟩ := hb k hk
      refine ⟨C, fun p hp hp2 => ?_⟩
      have h2 : ‖reflCLM (X := X) p - (x₀, 0)‖ < R := by rw [hdist p]; exact hp
      have h3 : (reflCLM (X := X) p).2 < 0 := by
        rw [reflCLM_apply]; simpa using hp2
      have hmem := hmemU _ h2 h3
      have hcomp := norm_iteratedFDeriv_comp_clm_le (L := reflCLM (X := X)) (f := Φ)
        (U := U) hUopen hC hmem k
      have hb2 := hCb (reflCLM (X := X) p) h2 h3
      have hnorm : ‖reflCLM (X := X)‖ ^ k ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) reflCLM_norm_le
      calc ‖iteratedFDeriv ℝ k f p‖
          = ‖iteratedFDeriv ℝ k (Φ ∘ reflCLM (X := X)) p‖ := by rw [hfeq]
        _ ≤ ‖iteratedFDeriv ℝ k Φ (reflCLM (X := X) p)‖ * ‖reflCLM (X := X)‖ ^ k := hcomp
        _ ≤ ‖iteratedFDeriv ℝ k Φ (reflCLM (X := X) p)‖ * 1 :=
              mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ ≤ (C * |(reflCLM (X := X) p).2| ^ (n + 1 - k)) * 1 :=
              mul_le_mul_of_nonneg_right hb2 (by norm_num)
        _ = C * p.2 ^ (n + 1 - k) := by
              have h2 : (reflCLM (X := X) p).2 = -p.2 := by rw [reflCLM_apply]
              rw [mul_one, h2, abs_neg, abs_of_pos hp2]
  have hL0 : reflCLM (X := X) (x₀, 0) = (x₀, 0) := by simp [reflCLM_apply]
  have hflat' : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) f (reflCLM (X := X) (x₀, 0)) := by
    rwa [hL0]
  have hconv := hflat'.comp (x₀, 0) ((reflCLM (X := X)).contDiff.contDiffAt)
  simpa [Function.comp_def, hf, reflCLM_apply] using hconv

/-- Two functions which agree on an open set have the same iterated derivatives at every point of
that set. -/
theorem iteratedFDeriv_congr_of_isOpen {s : Set (X × ℝ)} (hs : IsOpen s) {f g : X × ℝ → E}
    (h : Set.EqOn f g s) {z : X × ℝ} (hz : z ∈ s) (k : ℕ) :
    iteratedFDeriv ℝ k f z = iteratedFDeriv ℝ k g z := by
  rw [← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) k hs) hz,
    ← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) k hs) hz,
    iteratedFDerivWithin_congr h hz k]

/-! ## Coordinate estimates in a product -/

theorem norm_fst_sub_le {c : X} (w : X × ℝ) : ‖w.1 - c‖ ≤ ‖w - (c, 0)‖ := by
  have h1 : dist w.1 c ≤ dist w (c, 0) := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  rwa [dist_eq_norm, dist_eq_norm] at h1

theorem abs_snd_le {c : X} (w : X × ℝ) : |w.2| ≤ ‖w - (c, 0)‖ := by
  have h1 : dist w.2 0 ≤ dist w (c, 0) := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  rwa [Real.dist_eq, sub_zero, dist_eq_norm] at h1

/-! ## The main theorem -/

/-- Extension of the *descent* of a globally smooth even function: if `F : X × ℝ → E` is `C^∞` and even in the second variable, then `s ↦ F (x, √s)` on `s ≥ 0` extends to a globally `C^∞` function (Seeley's construction, see Hanusch arXiv:2002.05125; `X`, `E` arbitrary normed spaces). -/
theorem seeleyDescent_ext {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) :
    ∃ G : X × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      ∀ (x : X) (s : ℝ), 0 ≤ s → G (x, s) = F (x, Real.sqrt s) := by
  obtain ⟨a, b, hb, hbtend, hsum, hmom⟩ := momentSeqExists
  set Rf : X × ℝ → E := fun p => F (p.1, Real.sqrt p.2) with hRf
  set G : X × ℝ → E := fun p => if 0 ≤ p.2 then Rf p else seeleySum a b Rf p with hG
  have hG_apply : ∀ p : X × ℝ, G p = if 0 ≤ p.2 then Rf p else seeleySum a b Rf p := fun p => rfl
  have hRf_smooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Rf z := by
    intro z hz
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : X × ℝ => (p.1, Real.sqrt p.2)) z :=
      (contDiffAt_fst (p := z)).prodMk
        ((Real.contDiffAt_sqrt (ne_of_gt hz)).comp z (contDiffAt_snd (p := z)))
    exact hF.contDiffAt.comp z h1
  have hdescent : ∀ (n : ℕ) (x : X) (s : ℝ), 0 < s →
      Rf (x, s) = seeleyTaylor F n (x, s) + seeleyDescent F n (x, s) := by
    intro n x s hs
    have h1 : Rf (x, s) = F (x, Real.sqrt s) := rfl
    have h2 : seeleyDescent F n (x, s) = seeleyRemainder F n (x, Real.sqrt s) :=
      seeleyDescent_eq hs
    have h3 : seeleyRemainder F n (x, Real.sqrt s)
        = F (x, Real.sqrt s) - seeleyTaylor F n (x, s) := by
      simp only [seeleyRemainder, Real.sq_sqrt hs.le]
    rw [h1, h2, h3]; abel
  have htzero : ∀ (n : ℕ) (x : X), seeleyTaylor F n (x, 0) = F (x, 0) := by
    intro n x
    have h1 : seeleyTaylor F n (x, 0) = seeleyCoeff F 0 x := by
      simp only [seeleyTaylor]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro m _ hne; rw [zero_pow hne, zero_smul]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
    rw [h1, seeleyCoeff]
    simp
  have hG_off : ∀ z : X × ℝ, z.2 ≠ 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G z := by
    intro z hz
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · have hev : G =ᶠ[𝓝 z] seeleySum a b Rf := by
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hzneg] with y hy
        rw [hG_apply]
        exact if_neg (not_le.mpr hy)
      exact (contDiffAt_seeleySum_of_neg hb hbtend hRf_smooth hzneg).congr_of_eventuallyEq hev
    · have hev : G =ᶠ[𝓝 z] Rf := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hzpos] with y hy
        rw [hG_apply]
        exact if_pos hy.le
      exact (hRf_smooth z hzpos).congr_of_eventuallyEq hev
  refine ⟨G, ?_, ?_⟩
  · rw [contDiff_infty]
    intro n
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz0 : z.2 = 0
    · have hz_eq : z = (z.1, 0) := by ext <;> simp [hz0]
      rw [hz_eq]
      set Φ₁ : X × ℝ → E := fun p => seeleySum a b (seeleyTaylor F n) p - seeleyTaylor F n p
        with hΦ₁
      set Φ₂ : X × ℝ → E := fun p => seeleySum a b (seeleyDescent F n) p with hΦ₂
      set e₁ : X × ℝ → E := fun p => if 0 ≤ p.2 then 0 else Φ₁ p with he₁
      set e₂ : X × ℝ → E := fun p => if 0 ≤ p.2 then 0 else Φ₂ p with he₂
      have h_open_neg : IsOpen {p : X × ℝ | p.2 < 0} :=
        isOpen_lt continuous_snd continuous_const
      have hΦ₁_smooth : ∀ w : X × ℝ, w.2 < 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₁ w := by
        intro w hw
        refine (contDiffAt_seeleySum_of_neg hb hbtend
          (fun u _ => (seeleyTaylor_contDiff hF n).contDiffAt) hw).sub ?_
        exact (seeleyTaylor_contDiff hF n).contDiffAt
      have hΦ₂_smooth : ∀ w : X × ℝ, w.2 < 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₂ w :=
        fun w hw => contDiffAt_seeleySum_of_neg hb hbtend
          (fun u _ => seeleyDescent_contDiffAt hF (by assumption)) hw
      obtain ⟨C₁, r₁, hr₁, _hr₁1, hb₁⟩ :=
        seeleySum_taylor_flat hb hbtend hmom hsum hF n z.1 (n + 1)
      obtain ⟨Cd, rd, hrd, _hrd1, hD⟩ := seeleyDescent_bounds hF heven n z.1
      have hD' : ∀ x σ, ‖x - z.1‖ < rd → 0 < σ → σ < 1 → ∀ k ≤ n,
          ‖iteratedFDeriv ℝ k (seeleyDescent F n) (x, σ)‖ ≤ max Cd 0 * σ ^ (n + 1 - k) := by
        intro x σ hx hσ1 hσ2 k hk
        refine le_trans (hD x σ hx hσ1 hσ2 k hk) ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ1.le _)
      obtain ⟨C₂, r₂, hr₂, _hr₂1, _hr₂r, hb₂⟩ :=
        seeleySum_bounds_local hb hbtend hsum (fun w hw => seeleyDescent_contDiffAt hF hw)
          (C := max Cd 0) (le_max_right _ _) z.1 hrd hD'
      -- the two flat pieces are `C^n` at the axis
      have hE₁ : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) e₁ (z.1, 0) := by
        refine contDiffAt_of_flat_upper_bounds (Φ := e₁) (x₀ := z.1) (R := min r₁ 1)
          (lt_min hr₁ one_pos) ?_ ?_ ?_
        · intro w _ hw2
          rw [he₁]
          exact if_pos hw2
        · intro w hw
          have hw2 : w.2 < 0 := hw.2
          have heq : e₁ =ᶠ[𝓝 w] Φ₁ := by
            filter_upwards [h_open_neg.mem_nhds hw2] with y hy
            rw [he₁]
            exact if_neg (not_le.mpr hy)
          exact (hΦ₁_smooth w hw2).congr_of_eventuallyEq heq |>.contDiffWithinAt
        · intro k hk
          refine ⟨max C₁ 0, fun w hw hw2 => ?_⟩
          have hwr : ‖w.1 - z.1‖ < r₁ := by
            have h1 : ‖w.1 - z.1‖ ≤ ‖w - (z.1, 0)‖ := norm_fst_sub_le w
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_left _ _))
          have hws : -r₁ < w.2 := by
            have h1 : |w.2| ≤ ‖w - (z.1, 0)‖ := abs_snd_le w
            have h2 : |w.2| < r₁ := lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_left _ _))
            rw [abs_of_neg hw2] at h2
            linarith
          have hbound := hb₁ w.1 w.2 hwr hw2 hws k (by omega)
          have htransfer : iteratedFDeriv ℝ k e₁ w = iteratedFDeriv ℝ k Φ₁ w :=
            iteratedFDeriv_congr_of_isOpen h_open_neg (fun y hy => by
              rw [he₁]; exact if_neg (not_le.mpr hy)) hw2 k
          rw [htransfer]
          have hwabs : |w.2| ≤ 1 := by
            have h1 : |w.2| ≤ ‖w - (z.1, 0)‖ := abs_snd_le w
            exact le_trans h1 (le_of_lt (lt_of_lt_of_le hw (min_le_right _ _)))
          have hpow : |w.2| ^ (n + 1) ≤ |w.2| ^ (n + 1 - k) :=
            pow_le_pow_of_le_one (abs_nonneg _) hwabs (by omega)
          calc ‖iteratedFDeriv ℝ k Φ₁ w‖ ≤ C₁ * |w.2| ^ (n + 1) := hbound
            _ ≤ (max C₁ 0) * |w.2| ^ (n + 1) :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) _)
            _ ≤ (max C₁ 0) * |w.2| ^ (n + 1 - k) :=
                  mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      have hE₂ : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) e₂ (z.1, 0) := by
        refine contDiffAt_of_flat_upper_bounds (Φ := e₂) (x₀ := z.1) (R := min r₂ 1)
          (lt_min hr₂ one_pos) ?_ ?_ ?_
        · intro w _ hw2
          rw [he₂]
          exact if_pos hw2
        · intro w hw
          have hw2 : w.2 < 0 := hw.2
          have heq : e₂ =ᶠ[𝓝 w] Φ₂ := by
            filter_upwards [h_open_neg.mem_nhds hw2] with y hy
            rw [he₂]
            exact if_neg (not_le.mpr hy)
          exact (hΦ₂_smooth w hw2).congr_of_eventuallyEq heq |>.contDiffWithinAt
        · intro k hk
          refine ⟨max C₂ 0, fun w hw hw2 => ?_⟩
          have hwr : ‖w.1 - z.1‖ < r₂ := by
            have h1 : ‖w.1 - z.1‖ ≤ ‖w - (z.1, 0)‖ := norm_fst_sub_le w
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_left _ _))
          have hws : -r₂ < w.2 := by
            have h1 : |w.2| ≤ ‖w - (z.1, 0)‖ := abs_snd_le w
            have h2 : |w.2| < r₂ := lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_left _ _))
            rw [abs_of_neg hw2] at h2
            linarith
          have hbound := hb₂ w.1 w.2 hwr hw2 hws k hk
          have htransfer : iteratedFDeriv ℝ k e₂ w = iteratedFDeriv ℝ k Φ₂ w :=
            iteratedFDeriv_congr_of_isOpen h_open_neg (fun y hy => by
              rw [he₂]; exact if_neg (not_le.mpr hy)) hw2 k
          rw [htransfer]
          exact le_trans hbound (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (pow_nonneg (abs_nonneg _) _))
      -- the decomposition `G = T n + R n + (e₁ + e₂)`
      have hdecomp : ∀ p : X × ℝ,
          G p = seeleyTaylor F n p + seeleyDescent F n p + (e₁ p + e₂ p) := by
        intro p
        rcases lt_trichotomy p.2 0 with hp | hp | hp
        · -- p.2 < 0
          have hadd : ∀ q : X × ℝ, 0 < q.2 →
              Rf q = seeleyTaylor F n q + seeleyDescent F n q := fun q hq => hdescent n q.1 q.2 hq
          have hsum_eq : seeleySum a b Rf p
              = seeleySum a b (seeleyTaylor F n) p + seeleySum a b (seeleyDescent F n) p := by
            have := seeleySum_add_of_neg (a := a) (b := b) (x := p.1) (s := p.2) hb hbtend
              (R₁ := seeleyTaylor F n) (R₂ := seeleyDescent F n) (R₃ := Rf) hadd hp
            simpa using this
          have hRnp : seeleyDescent F n p = 0 := seeleyDescent_eq_zero hp.le
          have h1 : e₁ p = Φ₁ p := by simp only [he₁]; exact if_neg (not_le.mpr hp)
          have h2 : e₂ p = Φ₂ p := by simp only [he₂]; exact if_neg (not_le.mpr hp)
          rw [hG_apply, if_neg (not_le.mpr hp), hsum_eq, hRnp, h1, h2, hΦ₁, hΦ₂]
          simp only [neg_one_smul]
          abel
        · -- p.2 = 0
          have hp0 : p = (p.1, 0) := by ext <;> simp [hp]
          have h1 : Rf p = seeleyTaylor F n p + seeleyDescent F n p := by
            rw [hp0, show Rf (p.1, 0) = F (p.1, 0) from by simp [Rf],
              htzero n p.1, seeleyDescent_eq_zero (le_refl (0 : ℝ))]
            abel
          have h2 : e₁ p = 0 := by
            change (if 0 ≤ p.2 then (0 : E) else Φ₁ p) = 0
            rw [hp]
            exact if_pos le_rfl
          have h3 : e₂ p = 0 := by
            change (if 0 ≤ p.2 then (0 : E) else Φ₂ p) = 0
            rw [hp]
            exact if_pos le_rfl
          rw [hG_apply, if_pos (le_of_eq hp.symm), h1, h2, h3]
          abel
        · -- 0 < p.2
          have hval : Rf p = seeleyTaylor F n p + seeleyDescent F n p := hdescent n p.1 p.2 hp
          have h1 : e₁ p = 0 := by simp only [he₁]; exact if_pos hp.le
          have h2 : e₂ p = 0 := by simp only [he₂]; exact if_pos hp.le
          rw [hG_apply, if_pos hp.le, hval, h1, h2]
          abel
      have hsumcd : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (fun p => e₁ p + e₂ p) (z.1, 0) :=
        hE₁.add hE₂
      have hH : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞)
          (fun p : X × ℝ => seeleyTaylor F n p + seeleyDescent F n p + (e₁ p + e₂ p))
          (z.1, 0) :=
        (((seeleyTaylor_contDiff hF n).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr le_top)).add
          ((seeleyDescent_contDiff hF heven n).contDiffAt)).add hsumcd
      exact hH.congr_of_eventuallyEq (Filter.Eventually.of_forall hdecomp)
    · exact (hG_off z hz0).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro x s hs
    rw [hG_apply]; exact if_pos hs

end Work.Drive
