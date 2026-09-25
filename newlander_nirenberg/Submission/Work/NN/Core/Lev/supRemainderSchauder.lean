import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.NN.Core.perturbed_lossless
import Submission.Work.NN.Core.Lev.prelim
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz

set_option maxHeartbeats 16000000

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

variable {n : ℕ}

/-! ## Elementary interpolation for the `C^{0,α}` seminorm -/

/-- Two-case interpolation: a function bounded by `Z` on a set `S` and with derivative bounded by
`M` on a convex set `T ⊇ S` has Hölder seminorm at most `2Z/d^α + d^{1-α}M` on `S`, for every
free split `d > 0`. -/
lemma hSN_zero_le_interp {α Z M d : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hd : 0 < d) (hZ : 0 ≤ Z)
    (hM : 0 ≤ M)
    {S T : Set (Cn n)} (hST : S ⊆ T) (hconv : Convex ℝ T)
    {u : Cn n → ℂ} (hdiff : ∀ z ∈ T, DifferentiableAt ℝ u z)
    (hbound : ∀ z ∈ T, ‖fderiv ℝ u z‖ ≤ M)
    (hsup : ∀ z ∈ S, ‖u z‖ ≤ Z) :
    Work.CR.Flat.Holder.hSN 0 α u S
      ≤ ENNReal.ofReal (2 * Z / d ^ α + d ^ (1 - α) * M) := by
  rw [Work.CR.Flat.Holder.hSN_zero_deriv]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hdα : 0 < d ^ α := Real.rpow_pos_of_pos hd α
  have hxy0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hxyα0 : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hxy0.le α
  have hd1α : 0 ≤ d ^ (1 - α) := Real.rpow_nonneg hd.le _
  by_cases hle : ‖x - y‖ ≤ d
  · have hmvt : ‖u x - u y‖ ≤ M * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (f := u)
        (fun z hz => hdiff z hz) (fun z hz => hbound z hz) hconv (hST hy) (hST hx)
    calc ‖u x - u y‖ / ‖x - y‖ ^ α
        ≤ M * ‖x - y‖ / ‖x - y‖ ^ α := div_le_div_of_nonneg_right hmvt hxyα0
      _ = M * ‖x - y‖ ^ (1 - α) := by
            rw [mul_div_assoc, Real.rpow_sub hxy0 (1:ℝ) α, Real.rpow_one]
      _ ≤ M * d ^ (1 - α) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxy0.le hle (by linarith)) hM
      _ ≤ 2 * Z / d ^ α + d ^ (1 - α) * M := by
            rw [mul_comm M]
            have : 0 ≤ 2 * Z / d ^ α := div_nonneg (by linarith) hdα.le
            linarith
  · have hlt : d < ‖x - y‖ := not_le.mp hle
    have h2 : ‖u x - u y‖ ≤ 2 * Z := by
      have h1 := hsup x hx
      have h2 := hsup y hy
      calc ‖u x - u y‖ ≤ ‖u x‖ + ‖u y‖ := norm_sub_le _ _
        _ ≤ 2 * Z := by linarith
    calc ‖u x - u y‖ / ‖x - y‖ ^ α
        ≤ 2 * Z / ‖x - y‖ ^ α := div_le_div_of_nonneg_right h2 hxyα0
      _ ≤ 2 * Z / d ^ α :=
            div_le_div_of_nonneg_left (by linarith) hdα (Real.rpow_le_rpow hd.le hlt.le (by linarith))
      _ ≤ 2 * Z / d ^ α + d ^ (1 - α) * M :=
            le_add_of_nonneg_right (mul_nonneg hd1α hM)

/-! ## Finiteness of the sup of the derivative on a strictly smaller polydisc -/

/-- On a polydisc strictly inside the region where `u` is `C¹`, the supremum of `‖fderiv ℝ u‖` is
finite. -/
lemma iSup_ofReal_norm_fderiv_lt_top (hn : 0 < n) {ρ ρ₀ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hρ₀ρ : ∀ j, ρ₀ j < ρ j)
    {u : Cn n → ℂ} (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) :
    (⨆ z ∈ Work.CR.Flat.polydisc 0 ρ₀, ENNReal.ofReal ‖fderiv ℝ u z‖) < ⊤ := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set ρ₁ : Fin n → ℝ := fun j => (max (ρ₀ j) 0 + ρ j) / 2 with hρ₁def
  have hmaxlt : ∀ j, max (ρ₀ j) 0 < ρ j := fun j => max_lt (hρ₀ρ j) (hρ j)
  have hρ₁pos : ∀ j, 0 < ρ₁ j := fun j => by
    simp only [hρ₁def]
    have h1 := le_max_left (ρ₀ j) (0:ℝ)
    have h2 := le_max_right (ρ₀ j) (0:ℝ)
    linarith [hρ j]
  have hρ₁lt : ∀ j, ρ₁ j < ρ j := fun j => by
    simp only [hρ₁def]; linarith [hmaxlt j]
  have hρ₀ρ₁ : ∀ j, ρ₀ j ≤ ρ₁ j := fun j => by
    simp only [hρ₁def]
    have := le_max_left (ρ₀ j) (0:ℝ)
    linarith [hmaxlt j]
  have hsub : Work.CR.Flat.polydisc (0 : Cn n) ρ₀ ⊆ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz j => lt_of_le_of_lt (le_trans (le_of_lt (hz j)) (hρ₀ρ₁ j)) (hρ₁lt j)
  set K : Set (Cn n) := {z | ∀ j, ‖z j‖ ≤ ρ₁ j} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef, show {z : Cn n | ∀ j, ‖z j‖ ≤ ρ₁ j} = ⋂ j, {z : Cn n | ‖z j‖ ≤ ρ₁ j} from by
      ext z; simp]
    exact isClosed_iInter fun j =>
      isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
  set R : ℝ := ∑ j : Fin n, ρ₁ j with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact Finset.sum_pos (fun j _ => hρ₁pos j) Finset.univ_nonempty
  have hKsub : K ⊆ Metric.closedBall (0 : Cn n) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [pi_norm_le_iff_of_nonneg hRpos.le]
    intro j
    refine le_trans (hz j) ?_
    rw [hRdef]
    exact Finset.single_le_sum (fun k _ => (hρ₁pos k).le) (Finset.mem_univ j)
  have hKbdd : Bornology.IsBounded K :=
    (Metric.isBounded_closedBall (x := (0 : Cn n)) (r := R)).subset hKsub
  have hKcomp : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbdd⟩
  have hΩ : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hcontW : ContinuousOn (fderivWithin ℝ u (Work.CR.Flat.polydisc (0 : Cn n) ρ))
      (Work.CR.Flat.polydisc (0 : Cn n) ρ) :=
    hu.continuousOn_fderivWithin hΩ.uniqueDiffOn (by norm_num)
  have hKsubρ : K ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ :=
    fun z hz j => by simpa using lt_of_le_of_lt (hz j) (hρ₁lt j)
  have hcont : ContinuousOn (fun z => fderiv ℝ u z) K :=
    (hcontW.mono hKsubρ).congr (fun z hz => (fderivWithin_of_isOpen hΩ (hKsubρ hz)).symm)
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn hcont
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := max C 0))
  refine iSup₂_le fun z hz => ?_
  have hzK : z ∈ K := fun j => le_of_lt (lt_of_lt_of_le (by simpa using hz j) (hρ₀ρ₁ j))
  exact ENNReal.ofReal_le_ofReal (le_trans (hC z hzK) (le_max_left C 0))

/-! ## `holderNorm` congruence and convexity of the closed polydisc -/

/-- `holderNorm` depends only on the values on the set. -/
lemma holderNorm_congr {k : ℕ} {α : ℝ} {Ω : Set (Cn n)} {f g : Cn n → ℂ}
    (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  simp only [Work.CR.Flat.holderNorm]
  exact Finset.sum_congr rfl fun i _ => by
    have h1 : Work.CR.Flat.iterDerivNorm i f Ω = Work.CR.Flat.iterDerivNorm i g Ω :=
      Work.CR.Flat.Holder.iDN_congr (i := i) h
    have h2 : Work.CR.Flat.holderSeminorm i α f Ω = Work.CR.Flat.holderSeminorm i α g Ω :=
      Work.CR.Flat.Holder.hSN_congr (i := i) h
    rw [h1, h2]

/-- The closed polydisc `{z | ∀ j, ‖z j‖ ≤ r j}` is convex. -/
lemma convex_polydiscClosed {r : Fin n → ℝ} :
    Convex ℝ {z : Cn n | ∀ j, ‖z j‖ ≤ r j} := by
  intro x hx y hy a b ha hb hab j
  have h1 : (a • x + b • y) j = a • x j + b • y j := rfl
  rw [h1]
  calc ‖a • x j + b • y j‖ ≤ ‖a • x j‖ + ‖b • y j‖ := norm_add_le _ _
    _ = a * ‖x j‖ + b * ‖y j‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * r j + b * r j :=
        add_le_add (mul_le_mul_of_nonneg_left (hx j) ha) (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = r j := by rw [← add_mul, hab, one_mul]

/-! ## ENNReal form of the interpolation -/

/-- ENNReal version of the two-case interpolation. -/
lemma hSN_zero_le_interp_enn {α d : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hd : 0 < d)
    {S T : Set (Cn n)} (hST : S ⊆ T) (hconv : Convex ℝ T)
    {u : Cn n → ℂ} (hdiff : ∀ z ∈ T, DifferentiableAt ℝ u z)
    {M : ℝ≥0∞} (hMlt : M < ⊤) (hbound : ∀ z ∈ T, ENNReal.ofReal ‖fderiv ℝ u z‖ ≤ M)
    {Z : ℝ≥0∞} (hZ : ∀ z ∈ S, ENNReal.ofReal ‖u z‖ ≤ Z) :
    Work.CR.Flat.Holder.hSN 0 α u S
      ≤ ENNReal.ofReal (2 / d ^ α) * Z + ENNReal.ofReal (d ^ (1 - α)) * M := by
  rcases eq_or_ne Z ⊤ with hZtop | hZne
  · have htop : ENNReal.ofReal (2 / d ^ α) * Z + ENNReal.ofReal (d ^ (1 - α)) * M = ⊤ := by
      rw [hZtop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity), top_add]
    rw [htop]
    exact le_top
  · have hZcoe : ENNReal.ofReal Z.toReal = Z := ENNReal.ofReal_toReal hZne
    have hMcoe : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal (ne_of_lt hMlt)
    have hzr0 : 0 ≤ Z.toReal := ENNReal.toReal_nonneg
    have hm0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    have hsup : ∀ z ∈ S, ‖u z‖ ≤ Z.toReal := fun z hz => by
      have h := hZ z hz
      rw [← hZcoe] at h
      exact (ENNReal.ofReal_le_ofReal_iff hzr0).mp h
    have hbnd : ∀ z ∈ T, ‖fderiv ℝ u z‖ ≤ M.toReal := fun z hz => by
      have h := hbound z hz
      rw [← hMcoe] at h
      exact (ENNReal.ofReal_le_ofReal_iff hm0).mp h
    have e1 : ENNReal.ofReal (2 / d ^ α * Z.toReal) = ENNReal.ofReal (2 / d ^ α) * Z := by
      conv_rhs => rw [← hZcoe]
      rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 / d ^ α by positivity)]
    have e2 : ENNReal.ofReal (d ^ (1 - α) * M.toReal) = ENNReal.ofReal (d ^ (1 - α)) * M := by
      conv_rhs => rw [← hMcoe]
      rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ d ^ (1 - α) by positivity)]
    refine (hSN_zero_le_interp (n := n) hα0 hα1 hd hzr0 hm0 hST hconv hdiff hbnd hsup).trans ?_
    refine le_of_eq ?_
    rw [← e1, ← e2,
      ← ENNReal.ofReal_add (show (0:ℝ) ≤ 2 / d ^ α * Z.toReal by positivity)
        (show (0:ℝ) ≤ d ^ (1 - α) * M.toReal by positivity)]
    congr 1
    ring

/-! ## Vanishing of the cutoff datum -/

/-- Where the cutoff vanishes identically in a neighbourhood, its `(0,1)`-datum vanishes. -/
lemma dbarCn_cutoff_vanish {A : Cn n → Cn n →L[ℝ] Cn n} {R : Fin n → ℝ} {e : ℝ}
    {χ : Cn n → ℝ} (hχ0 : ∀ z, (∃ j, R j + e ≤ ‖z j‖) → χ z = 0)
    {z : Cn n} (hz : ∃ j : Fin n, R j + e < ‖z j‖) (j : Fin n) :
    dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1) = 0 := by
  obtain ⟨k, hk⟩ := hz
  have hδ : 0 < ‖z k‖ - (R k + e) := by linarith
  have hev : ∀ᶠ w in 𝓝 z, χ w = 0 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨‖z k‖ - (R k + e), hδ, fun w hw => ?_⟩
    apply hχ0
    refine ⟨k, ?_⟩
    have h2 : ‖z k - w k‖ ≤ ‖z - w‖ := norm_le_pi_norm (z - w) k
    have h3 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
    have h4 : ‖z k‖ ≤ ‖w k‖ + ‖z k - w k‖ := by
      calc ‖z k‖ = ‖w k + (z k - w k)‖ := by rw [show w k + (z k - w k) = z k from by ring]
        _ ≤ ‖w k‖ + ‖z k - w k‖ := norm_add_le _ _
    rw [dist_eq_norm] at hw
    linarith
  have hevC : (fun w : Cn n => (χ w : ℂ)) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hev] with w hw
    show ((χ w : ℝ) : ℂ) = (0 : ℂ)
    rw [hw]
    rfl
  have hfd : fderiv ℝ (fun w : Cn n => (χ w : ℂ)) z = 0 := by
    rw [hevC.fderiv_eq]
    simp
  have hzero : dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z = 0 := by
    ext v
    rw [show dbarCn (JstdCn n + A) (fun w : Cn n => (χ w : ℂ)) z v
        = (1 / 2 : ℂ) * (fderiv ℝ (fun w : Cn n => (χ w : ℂ)) z v
            + Complex.I * fderiv ℝ (fun w : Cn n => (χ w : ℂ)) z (((JstdCn n + A) z) v))
        from dbarCn_apply _ _ _ _]
    rw [hfd]
    simp
  rw [hzero]
  simp

/-! ## The one-step perturbed Schauder estimate with a sup remainder -/

/-- **The one-step perturbed Schauder estimate with a sup remainder.** -/
theorem onestepSup {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ'' : Fin n → ℝ} (hρ''0 : ∀ j, 0 < ρ'' j) (hρ''ρ : ∀ j, ρ'' j < ρ j)
    {A : Cn n → Cn n →L[ℝ] Cn n}
    {C Kd L1 L2 d : ℝ} (hC : 0 < C) (hKd : 0 < Kd) (hL1 : 0 < L1) (hL2 : 0 < L2) (hd : 0 < d)
    (hlossless : ∀ v : Cn n → ℂ, (∀ z, (∃ i, ρ'' i ≤ ‖z i‖) → v z = 0) →
        ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ) →
        Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc 0 ρ'')
          ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ''))
    {R : Fin n → ℝ} {e : ℝ} (he : 0 < e) (hRe : ∀ j, R j + e ≤ ρ'' j)
    {χ : Cn n → ℝ} (hχsm : ∀ m : ℕ, ContDiff ℝ m χ)
    (hχ1 : ∀ z, (∀ j, ‖z j‖ ≤ R j) → χ z = 1)
    (hχ0 : ∀ z, (∃ j, R j + e ≤ ‖z j‖) → χ z = 0)
    (hχC : Work.CR.Flat.Holder.iDN 0 (fun z => (χ z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        + Work.CR.Flat.Holder.hSN 0 α (fun z => (χ z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
          ≤ ENNReal.ofReal L1)
    (hχN : Work.CR.Flat.holderNorm 1 α (fun z => (χ z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
          ≤ ENNReal.ofReal L2)
    (hdata : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => dbarCn (JstdCn n + A) (fun z => (χ z : ℂ)) z (Pi.single j 1))
        (Work.CR.Flat.polydisc 0 ρ'') ≤ ENNReal.ofReal Kd * Work.CR.Flat.holderNorm 1 α
          (fun z => (χ z : ℂ)) (Work.CR.Flat.polydisc 0 ρ''))
    {u : Cn n → ℂ} (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) :
    Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 R)
      ≤ ENNReal.ofReal (C * L1) * (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ))
        + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * (1 + 2 * Real.rpow d (-α)))
            * (⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ENNReal.ofReal ‖u z‖)
        + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * Real.rpow d (1 - α))
            * (⨆ z ∈ Work.CR.Flat.polydisc 0 (fun j => R j + (e + d)),
                ENNReal.ofReal ‖fderiv ℝ u z‖) := by
  classical
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set X : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ) with hXdef
  set Z : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ, ENNReal.ofReal ‖u z‖ with hZdef
  set Me : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) (fun j => R j + (e + d)),
      ENNReal.ofReal ‖fderiv ℝ u z‖ with hMedef
  by_cases hMetop : Me = ⊤
  · have hcoef : ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * Real.rpow d (1 - α)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact mul_pos (mul_pos hC (mul_pos (mul_pos hKd hnR) hL2)) (Real.rpow_pos_of_pos hd _)
    have htop : ENNReal.ofReal (C * L1) * X
        + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * (1 + 2 * Real.rpow d (-α))) * Z
        + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * Real.rpow d (1 - α)) * Me = ⊤ := by
      rw [hMetop, ENNReal.mul_top hcoef, add_top]
    rw [htop]
    exact le_top
  · have hMlt : Me < ⊤ := lt_top_iff_ne_top.mpr hMetop
    have hΩ'' : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := Work.CR.Flat.isOpen_polydisc 0 ρ''
    have hΩ : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
    have hsub : Work.CR.Flat.polydisc (0 : Cn n) ρ'' ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ :=
      fun z hz j => lt_trans (hz j) (hρ''ρ j)
    have hRlt : ∀ j, R j < ρ'' j := fun j => by linarith [he, hRe j]
    have hRsub : Work.CR.Flat.polydisc (0 : Cn n) R ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ'' :=
      fun z hz j => lt_trans (hz j) (hRlt j)
    -- the function `v := χ · u`, supported in `polydisc 0 ρ''`
    set v : Cn n → ℂ := fun z => (χ z : ℂ) * u z with hvdef
    have hvsm : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc (0 : Cn n) ρ) := by
      have h1 : ContDiffOn ℝ 1 (fun z : Cn n => (χ z : ℂ)) (Work.CR.Flat.polydisc (0 : Cn n) ρ) :=
        ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm 1)).contDiffOn
      rw [hvdef]
      exact h1.mul hu
    have hv0 : ∀ z, (∃ i, ρ'' i ≤ ‖z i‖) → v z = 0 := by
      intro z hz
      obtain ⟨i, hi⟩ := hz
      have hz' : R i + e ≤ ‖z i‖ := le_trans (hRe i) hi
      rw [hvdef]
      show (χ z : ℂ) * u z = 0
      rw [hχ0 z ⟨i, hz'⟩]
      simp
    have hloss := hlossless v hv0 hvsm
    have hcmp : Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc (0 : Cn n) R)
        ≤ Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := by
      have heq : Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc (0 : Cn n) R)
          = Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc (0 : Cn n) R) :=
        holderNorm_congr (k := 1) (α := α) fun z hz => by
          rw [hvdef]
          show u z = (χ z : ℂ) * u z
          rw [hχ1 z (fun j => le_of_lt (by simpa using hz j))]
          simp
      rw [heq]
      exact Work.CR.Flat.holderNorm_mono_set hΩ'' (Work.CR.Flat.isOpen_polydisc 0 R) hRsub 1 α v
    -- Leibniz
    have hleib : ∀ j : Fin n, Set.EqOn (fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1))
        ((fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
          + (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1)))
        (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := by
      intro j z hz
      have hzρ : z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ := hsub hz
      have hχd : DifferentiableAt ℝ (fun w : Cn n => (χ w : ℂ)) z := by
        have hdiff : Differentiable ℝ (fun w : Cn n => (χ w : ℂ)) :=
          ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm 1)).differentiable
            (by norm_num)
        exact hdiff.differentiableAt
      have hud : DifferentiableAt ℝ u z :=
        (hu.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hzρ)
      show dbarCn (JstdCn n + A) v z (Pi.single j 1)
          = (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1)
            + u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1)
      rw [hvdef]
      exact dbarCn_mul_leibniz hχd hud j
    -- split the sum
    have hsplit : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1))
          (Work.CR.Flat.polydisc (0 : Cn n) ρ''))
        ≤ (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ''))
          + (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'')) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have heq := holderNorm_congr (k := 0) (α := α) (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
        (f := fun z => dbarCn (JstdCn n + A) v z (Pi.single j 1))
        (g := (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
              + (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1)))
        (hleib j)
      rw [heq]
      exact Work.NN.Core.Lev.holderNorm_zero_add_le
    -- term A
    have htermA : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
          (Work.CR.Flat.polydisc (0 : Cn n) ρ'')) ≤ X * ENNReal.ofReal L1 := by
      have hper : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
          (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
          ≤ Work.CR.Flat.holderNorm 0 α
              (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'') * ENNReal.ofReal L1 := by
        intro j
        have hprod := holderNorm_zero_mul_le_support (α := α)
          (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'') (S := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
          (u := fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (g := fun z => (χ z : ℂ))
          (fun z hz _ => hz)
        have hcon : Work.CR.Flat.holderNorm 0 α
              (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
            = Work.CR.Flat.holderNorm 0 α
              (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1) * (χ z : ℂ))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'') :=
          holderNorm_congr (k := 0) (α := α) fun z _ => mul_comm _ _
        rw [hcon]
        refine hprod.trans ?_
        rw [← Work.NN.Core.Lev.holderNorm_zero_le_self]
        exact mul_le_mul le_rfl hχC bot_le bot_le
      calc (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => (χ z : ℂ) * dbarCn (JstdCn n + A) u z (Pi.single j 1))
            (Work.CR.Flat.polydisc (0 : Cn n) ρ''))
          ≤ ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'') * ENNReal.ofReal L1 :=
            Finset.sum_le_sum fun j _ => hper j
        _ = (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'')) * ENNReal.ofReal L1 :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ X * ENNReal.ofReal L1 := by
            rw [hXdef]
            exact mul_le_mul (Finset.sum_le_sum fun j _ =>
              Work.CR.Flat.holderNorm_mono_set hΩ hΩ'' hsub 0 α
                (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1))) le_rfl bot_le bot_le
    -- term B
    have htermB : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
          (Work.CR.Flat.polydisc (0 : Cn n) ρ''))
        ≤ ENNReal.ofReal (Kd * (n : ℝ) * L2)
            * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) := by
      set S : Set (Cn n) := {z | ∀ j : Fin n, ‖z j‖ ≤ R j + e} with hSdef
      have hconvS : Convex ℝ S := by rw [hSdef]; exact convex_polydiscClosed
      have hSsubρ : S ⊆ Work.CR.Flat.polydisc (0 : Cn n) ρ := by
        intro z hz
        rw [Work.CR.Flat.mem_polydisc]
        intro j
        have h2 : R j + e < ρ j := lt_of_le_of_lt (hRe j) (hρ''ρ j)
        have h3 : ‖z j‖ < ρ j := lt_of_le_of_lt (hz j) h2
        simpa using h3
      have hdiffS : ∀ z ∈ S, DifferentiableAt ℝ u z := fun z hz =>
        (hu.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds (hSsubρ hz))
      have hbndS : ∀ z ∈ S, ENNReal.ofReal ‖fderiv ℝ u z‖ ≤ Me := by
        intro z hz
        rw [hMedef]
        refine le_iSup₂_of_le z ?_ le_rfl
        rw [Work.CR.Flat.mem_polydisc]
        intro j
        have h2 : R j + e < R j + (e + d) := by linarith
        have h3 : ‖z j‖ < R j + (e + d) := lt_of_le_of_lt (hz j) h2
        simpa using h3
      have hsupS : ∀ z ∈ S, ENNReal.ofReal ‖u z‖ ≤ Z := fun z hz => by
        rw [hZdef]
        exact le_iSup₂_of_le z (hSsubρ hz) le_rfl
      have hinterp := hSN_zero_le_interp_enn (n := n) (α := α) (d := d) hα0 hα1 hd
        (S := S) (T := S) (subset_refl S) hconvS hdiffS hMlt hbndS hsupS
      have hUbound : Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S
          ≤ ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
            + ENNReal.ofReal (Real.rpow d (1 - α)) * Me := by
        have hidn : Work.CR.Flat.Holder.iDN 0 u S ≤ Z := by
          rw [hZdef]
          exact Work.NN.Core.Lev.iDN_zero_le_sup hSsubρ
        have heq1 : (1 : ℝ≥0∞) + ENNReal.ofReal (2 / d ^ α)
            = ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) := by
          have h2 : 2 * Real.rpow d (-α) = (2:ℝ) / d ^ α := by
            have h : Real.rpow d (-α) = (d ^ α)⁻¹ := Real.rpow_neg hd.le α
            rw [h, div_eq_mul_inv]
          rw [ENNReal.ofReal_add (p := 1) (q := 2 * Real.rpow d (-α)) (by norm_num : (0:ℝ) ≤ 1)
                (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_pos_of_pos hd (-α)).le),
              ← ENNReal.ofReal_one, h2]
        calc Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S
            ≤ Z + (ENNReal.ofReal (2 / d ^ α) * Z
                + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) := add_le_add hidn hinterp
          _ = ((1 : ℝ≥0∞) + ENNReal.ofReal (2 / d ^ α)) * Z
                + ENNReal.ofReal (Real.rpow d (1 - α)) * Me := by ring
          _ = ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                + ENNReal.ofReal (Real.rpow d (1 - α)) * Me := by rw [heq1]
      have hN : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
            (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
          ≤ ENNReal.ofReal Kd * ENNReal.ofReal L2 := fun j =>
            (hdata j).trans (mul_le_mul le_rfl hχN bot_le bot_le)
      have hper : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
            (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
          ≤ (ENNReal.ofReal Kd * ENNReal.ofReal L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) := by
        intro j
        have hsupp : ∀ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'',
            dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1) ≠ 0 → z ∈ S := by
          intro z hz hne
          by_contra hzS
          rw [hSdef] at hzS
          simp only [Set.mem_setOf_eq, not_forall, not_le] at hzS
          exact hne (dbarCn_cutoff_vanish (A := A) (R := R) (e := e) (χ := χ) hχ0 hzS j)
        have hprod := holderNorm_zero_mul_le_support (α := α)
          (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'') (S := S) (u := u)
          (g := fun z => dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1)) hsupp
        calc Work.CR.Flat.holderNorm 0 α
              (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
              (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
            ≤ (Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S)
                * (Work.CR.Flat.Holder.iDN 0
                    (fun z => dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
                    (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
                  + Work.CR.Flat.Holder.hSN 0 α
                    (fun z => dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
                    (Work.CR.Flat.polydisc (0 : Cn n) ρ'')) := hprod
          _ = (Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S)
                * Work.CR.Flat.holderNorm 0 α
                  (fun z => dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
                  (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := by
                rw [Work.NN.Core.Lev.holderNorm_zero_le_self]
          _ ≤ (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me)
                * (ENNReal.ofReal Kd * ENNReal.ofReal L2) :=
                mul_le_mul hUbound (hN j) bot_le bot_le
          _ = (ENNReal.ofReal Kd * ENNReal.ofReal L2)
                * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                    + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) := by ring
      calc (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => u z * dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1))
            (Work.CR.Flat.polydisc (0 : Cn n) ρ''))
          ≤ ∑ _j : Fin n, (ENNReal.ofReal Kd * ENNReal.ofReal L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) :=
            Finset.sum_le_sum fun j _ => hper j
        _ = ENNReal.ofReal ((n : ℝ)) * ((ENNReal.ofReal Kd * ENNReal.ofReal L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast n]
        _ = ENNReal.ofReal (Kd * (n : ℝ) * L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me) := by
            have step : ENNReal.ofReal (Kd * (n : ℝ) * L2)
                = ENNReal.ofReal ((n:ℝ)) * (ENNReal.ofReal Kd * ENNReal.ofReal L2) := by
              rw [← ENNReal.ofReal_mul (p := Kd) (q := L2) hKd.le,
                ← ENNReal.ofReal_mul (p := (n:ℝ)) (q := Kd * L2) (Nat.cast_nonneg n)]
              congr 1
              ring
            rw [← mul_assoc, ← step]
    -- final assembly
    have h1 : Work.CR.Flat.holderNorm 1 α v (Work.CR.Flat.polydisc (0 : Cn n) ρ'')
        ≤ ENNReal.ofReal C * (X * ENNReal.ofReal L1
            + ENNReal.ofReal (Kd * (n : ℝ) * L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me)) := by
      refine hloss.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      exact hsplit.trans (add_le_add htermA htermB)
    have hfinal : ENNReal.ofReal C * (X * ENNReal.ofReal L1
          + ENNReal.ofReal (Kd * (n : ℝ) * L2)
              * (ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) * Z
                  + ENNReal.ofReal (Real.rpow d (1 - α)) * Me))
        = ENNReal.ofReal (C * L1) * X
          + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * (1 + 2 * Real.rpow d (-α))) * Z
          + ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * Real.rpow d (1 - α)) * Me := by
      have hKnn : (0:ℝ) ≤ Kd * (n : ℝ) * L2 := (mul_pos (mul_pos hKd hnR) hL2).le
      rw [show ENNReal.ofReal (C * L1) = ENNReal.ofReal C * ENNReal.ofReal L1 from
            ENNReal.ofReal_mul hC.le,
          show ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * (1 + 2 * Real.rpow d (-α)))
              = ENNReal.ofReal (C * (Kd * (n : ℝ) * L2))
                * ENNReal.ofReal (1 + 2 * Real.rpow d (-α)) from
            ENNReal.ofReal_mul (mul_nonneg hC.le hKnn),
          show ENNReal.ofReal (C * (Kd * (n : ℝ) * L2) * Real.rpow d (1 - α))
              = ENNReal.ofReal (C * (Kd * (n : ℝ) * L2))
                * ENNReal.ofReal (Real.rpow d (1 - α)) from
            ENNReal.ofReal_mul (mul_nonneg hC.le hKnn),
          show ENNReal.ofReal (C * (Kd * (n : ℝ) * L2))
              = ENNReal.ofReal C * ENNReal.ofReal (Kd * (n : ℝ) * L2) from
            ENNReal.ofReal_mul hC.le,
          show ENNReal.ofReal (Kd * (n : ℝ) * L2)
              = ENNReal.ofReal Kd * ENNReal.ofReal (n : ℝ) * ENNReal.ofReal L2 from by
            rw [ENNReal.ofReal_mul (p := Kd * (n:ℝ)) (q := L2) (mul_pos hKd hnR).le,
              ENNReal.ofReal_mul (p := Kd) (q := (n:ℝ)) hKd.le],
          show ENNReal.ofReal (1 + 2 * Real.rpow d (-α))
              = ENNReal.ofReal 1 + ENNReal.ofReal 2 * ENNReal.ofReal (Real.rpow d (-α)) from by
            rw [ENNReal.ofReal_add (p := 1) (q := 2 * Real.rpow d (-α)) (by norm_num)
                  (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_pos_of_pos hd (-α)).le),
              ENNReal.ofReal_mul (p := 2) (q := Real.rpow d (-α)) (by norm_num)]]
      ring
    exact hcmp.trans (h1.trans (le_of_eq hfinal))


/-! ## Auxiliary: the telescoping chain -/

/-- The geometric sum `∑_{i<N} 2^{-i} ≤ 2`. -/
lemma sum_range_half_pow_le (N : ℕ) : (∑ i ∈ Finset.range N, ((1/2:ℝ))^i) ≤ 2 := by
  have h : ∀ N : ℕ, (∑ i ∈ Finset.range N, ((1/2:ℝ))^i) = 2 - 2 * ((1/2:ℝ))^N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h N]
  have : 0 ≤ 2 * ((1/2:ℝ))^N := by positivity
  linarith

/-- Products of a termwise smaller nonnegative family. -/
lemma prod_range_le_of_nonneg {f g : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (hle : ∀ k, f k ≤ g k) :
    ∀ N, ∏ k ∈ Finset.range N, f k ≤ ∏ k ∈ Finset.range N, g k := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact mul_le_mul ih (hle N) (hf N) (Finset.prod_nonneg fun k _ => hg k)

/-- `∏_{k<N} (1/2)^k ≤ 1`. -/
lemma prod_range_half_le_one (N : ℕ) : ∏ k ∈ Finset.range N, ((1/2:ℝ))^k ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ]
      have h1 : (0:ℝ) ≤ ((1/2:ℝ))^N := pow_nonneg (by norm_num) N
      have h2 : ((1/2:ℝ))^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith

/-- `2 ^ (-i) = (1/2)^i`. -/
lemma rpow_two_neg_nat (i : ℕ) : Real.rpow 2 (-(i:ℝ)) = ((1/2:ℝ))^i := by
  rw [show Real.rpow 2 (-(i:ℝ)) = (Real.rpow 2 (i:ℝ))⁻¹ from Real.rpow_neg (by norm_num) (i:ℝ),
    show Real.rpow 2 (i:ℝ) = (2:ℝ)^i from Real.rpow_natCast 2 i, ← inv_pow]
  norm_num

/-- **Telescoping bound.** -/
lemma chain_telescope {V : ℕ → ℝ≥0∞} {X Z : ℝ≥0∞} {ar br lr : ℕ → ℝ} (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hPsucc : ∀ i, P (i+1) = P i * lr i)
    (har : ∀ i, 0 ≤ ar i) (hbr : ∀ i, 0 ≤ br i) (hlr : ∀ i, 0 ≤ lr i)
    (hstep : ∀ i, V i ≤ ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z
        + ENNReal.ofReal (lr i) * V (i+1)) :
    ∀ N, V 0 ≤ (∑ i ∈ Finset.range N, ENNReal.ofReal (P i) *
          (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z))
        + ENNReal.ofReal (P N) * V N := by
  have hPnn : ∀ i, 0 ≤ P i := by
    intro i
    induction i with
    | zero => rw [hP0]; norm_num
    | succ i ih => rw [hPsucc i]; exact mul_nonneg ih (hlr i)
  intro N
  induction N with
  | zero => rw [hP0, ENNReal.ofReal_one, one_mul, Finset.range_zero, Finset.sum_empty, zero_add]
  | succ N ih =>
    have hPN : ENNReal.ofReal (P (N+1)) = ENNReal.ofReal (P N) * ENNReal.ofReal (lr N) := by
      rw [hPsucc N, ENNReal.ofReal_mul (hPnn N)]
    rw [hPN]
    refine ih.trans ?_
    have h2 : ENNReal.ofReal (P N) * V N
        ≤ ENNReal.ofReal (P N) * (ENNReal.ofReal (ar N) * X + ENNReal.ofReal (br N) * Z
            + ENNReal.ofReal (lr N) * V (N+1)) :=
      mul_le_mul le_rfl (hstep N) bot_le bot_le
    refine (add_le_add le_rfl h2).trans (le_of_eq ?_)
    rw [Finset.sum_range_succ, mul_add, mul_add, mul_assoc]
    ring

/-! ## Power and geometric helpers for the graded chain -/

/-- `(2^{-1})^i` raised to the power `-q`. -/
lemma rpow_half_pow_neg (i : ℕ) (q : ℝ) :
    Real.rpow (((1/2:ℝ))^i) (-q) = (Real.rpow 2 q)^i := by
  rw [show Real.rpow (((1/2:ℝ))^i) (-q) = Real.rpow (Real.rpow 2 (-(i:ℝ))) (-q) from by
    rw [rpow_two_neg_nat i]]
  change ((2:ℝ) ^ (-(i:ℝ))) ^ (-q) = ((2:ℝ) ^ q)^i
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(i:ℝ)) (-q),
      show (-(i:ℝ)) * (-q) = q * (i:ℝ) from by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) q (i:ℝ),
      Real.rpow_natCast ((2:ℝ) ^ q) i]

/-- `(2^{-1})^i` raised to the power `q`. -/
lemma rpow_half_pow (i : ℕ) (q : ℝ) :
    Real.rpow (((1/2:ℝ))^i) q = (Real.rpow (1/2) q)^i := by
  rw [show Real.rpow (((1/2:ℝ))^i) q = Real.rpow (Real.rpow 2 (-(i:ℝ))) q from by
    rw [rpow_two_neg_nat i]]
  change ((2:ℝ) ^ (-(i:ℝ))) ^ q = (((1/2:ℝ)) ^ q)^i
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(i:ℝ)) q,
      show (-(i:ℝ)) * q = (-q) * (i:ℝ) from by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-q) (i:ℝ),
      Real.rpow_natCast ((2:ℝ) ^ (-q)) i,
      show (2:ℝ) ^ (-q) = ((1/2:ℝ)) ^ q from by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2) q]
        norm_num]

/-- `(1/2)^q = 2^{-q}`. -/
lemma rpow_half_eq (q : ℝ) : Real.rpow (1/2) q = Real.rpow 2 (-q) := by
  change (((1/2:ℝ))^q) = ((2:ℝ)^(-q))
  rw [show ((1/2:ℝ)) = ((2:ℝ))⁻¹ from by norm_num,
    Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2) q, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) q]

/-- `(1/2)^{mk} ≤ (1/2)^k`. -/
lemma half_pow_mul_le {m k : ℕ} (hm : 1 ≤ m) : ((1/2:ℝ))^(m*k) ≤ ((1/2:ℝ))^k := by
  have h : k ≤ m * k := by nlinarith [Nat.mul_le_mul_right k hm]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- `Real.one_le_rpow`. -/
lemma one_le_rpow_two {q : ℝ} (hq : 0 ≤ q) : 1 ≤ Real.rpow 2 q := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq
  simpa using h

/-! ## Some cast helpers -/

/-- `∑_{k<N} k` cast to `ℝ`. -/
lemma cast_range_sum_id (i : ℕ) :
    ((∑ k ∈ Finset.range i, k : ℕ) : ℝ) = (i:ℝ)*((i:ℝ)-1)/2 := by
  have h := Finset.sum_range_id_mul_two i
  have h2 : ((∑ k ∈ Finset.range i, k : ℕ) : ℝ) * 2 = ((i*(i-1) : ℕ) : ℝ) := by
    exact_mod_cast h
  have h3 : ((i*(i-1) : ℕ) : ℝ) = (i:ℝ)*((i:ℝ)-1) := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; norm_num
    · rw [Nat.cast_mul, Nat.cast_sub hpos]; norm_num
  linarith

/-- `(2^q)^i = 2^{qi}`. -/
lemma rpow_two_mul_nat (i : ℕ) (q : ℝ) :
    (Real.rpow 2 q)^i = Real.rpow 2 (q * (i:ℝ)) := by
  change ((2:ℝ)^q)^i = ((2:ℝ)^(q * (i:ℝ)))
  rw [← Real.rpow_natCast ((2:ℝ)^q) i,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) q (i:ℝ)]

/-- `‖D^1 f z‖ = ‖df_z‖`. -/
lemma norm_iteratedFDeriv_one_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℂ) (z : X) : ‖iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f z‖ := by
  have key : continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDeriv ℝ 1 f z) = fderiv ℝ f z := by
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  rw [← key, LinearIsometryEquiv.norm_map]

/-- `‖D^1 f x - D^1 f y‖ = ‖df_x - df_y‖`. -/
lemma norm_iteratedFDeriv_one_sub_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℂ) (x y : X) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  have kx : continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  have ky : continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDeriv ℝ 1 f y) = fderiv ℝ f y := by
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  rw [← kx, ← ky, ← map_sub, LinearIsometryEquiv.norm_map]

/-- `‖D^1 f z‖ = ‖df_z‖` on an open set. -/
lemma norm_iteratedFDerivWithin_one_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} (hs : IsOpen s) (f : X → ℂ) {z : X} (hz : z ∈ s) :
    ‖iteratedFDerivWithin ℝ 1 f s z‖ = ‖fderiv ℝ f z‖ := by
  rw [iteratedFDerivWithin_of_isOpen 1 hs hz]
  exact norm_iteratedFDeriv_one_eq f z

/-- `‖D^1 f x - D^1 f y‖ = ‖df_x - df_y‖` on an open set. -/
lemma norm_iteratedFDerivWithin_one_sub_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} (hs : IsOpen s) (f : X → ℂ) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ 1 f s x - iteratedFDerivWithin ℝ 1 f s y‖
      = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  rw [iteratedFDerivWithin_of_isOpen 1 hs hx, iteratedFDerivWithin_of_isOpen 1 hs hy]
  exact norm_iteratedFDeriv_one_sub_eq f x y

/-- `(1/2)^N = 2^{-N}`. -/
lemma rpow_two_neg_nat' (i : ℕ) : Real.rpow 2 (-(i:ℝ)) = ((1/2:ℝ))^i := rpow_two_neg_nat i

/-- **The perturbed interior Schauder estimate with a sup (`C^0`) remainder.** -/
theorem supRemainderSchauder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α
            (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ u : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
          Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ')
            ≤ ENNReal.ofReal C * ((∑ j : Fin n,
                  Work.CR.Flat.holderNorm 0 α
                    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
                    (Work.CR.Flat.polydisc 0 ρ))
                + ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ENNReal.ofReal ‖u z‖) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- ## The geometry
  set s : Fin n → ℝ := fun j => ρ j - ρ' j with hsdef
  have hs : ∀ j, 0 < s j := fun j => by simp only [hsdef]; linarith [hρ' j]
  set smin : ℝ := Finset.univ.inf' Finset.univ_nonempty s with hsmindef
  have hsmin0 : 0 < smin := by
    rw [hsmindef]; exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hs j)
  have hsminle : ∀ j, smin ≤ s j := fun j => by
    rw [hsmindef]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set ρ'' : Fin n → ℝ := fun j => ρ' j + s j / 2 with hρ''def
  have hρ''0 : ∀ j, 0 < ρ'' j := fun j => by simp only [hρ''def]; linarith [hs j, hρ'0 j]
  have hρ''ρ : ∀ j, ρ'' j < ρ j := fun j => by
    simp only [hρ''def, hsdef]; linarith [hs j]
  -- ## the lossless estimate
  obtain ⟨εL, hεLpos, CL, hCLpos, hloss⟩ :=
    perturbed_lossless (n := n) hn hα0 hα1 hρ0 hρ''0 hρ''ρ 0
  -- ## cutoff constants
  set Rmin : ℝ := Finset.univ.inf' Finset.univ_nonempty ρ' with hRmindef
  have hRmin0 : 0 < Rmin := by
    rw [hRmindef]; exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hρ'0 j)
  have hRminle : ∀ j, Rmin ≤ ρ' j := fun j => by
    rw [hRmindef]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ'' with hRmaxdef
  have hRmax0 : 0 < Rmax := by
    rw [hRmaxdef]
    exact lt_of_lt_of_le (hρ''0 ⟨0, hn⟩) (Finset.le_sup' _ (Finset.mem_univ _))
  have hρ''leRmax : ∀ j, ρ'' j ≤ Rmax := fun j => by
    rw [hRmaxdef]; exact Finset.le_sup' _ (Finset.mem_univ j)
  obtain ⟨K, hKpos, p, hppos, hcut⟩ :=
    exists_polydisc_cutoff_lipschitz (n := n) hn hα0 hα1 hRmin0 hRmax0
  -- ## the datum constant
  obtain ⟨Cd, hCdpos, hdatac⟩ :=
    dbarCn_data_le (n := n) hα0 (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
      (Work.CR.Flat.isOpen_polydisc 0 ρ'')
  -- ## the exponent for the interpolation splits
  have h1a : 0 < 1 - α := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 < (m:ℝ) * (1 - α) := by
    obtain ⟨m, hm⟩ := exists_nat_ge ((p + 1) / (1 - α) + 1)
    refine ⟨m, ?_⟩
    have h2 := mul_le_mul_of_nonneg_right hm h1a.le
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h1a), one_mul] at h2
    linarith
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0] at hm
      simp only [Nat.cast_zero, zero_mul] at hm
      linarith [hppos]
    · exact hpos
  -- ## the smallness and thickness constants
  set eps0 : ℝ := min εL 1 with heps0def
  have heps0pos : 0 < eps0 := lt_min hεLpos one_pos
  set Kd : ℝ := Cd * (1 + eps0) with hKddef
  have hKdpos : 0 < Kd := mul_pos hCdpos (by linarith)
  set e0 : ℝ := smin / 100 with he0def
  have he0pos : 0 < e0 := by rw [he0def]; linarith
  have he0le : e0 ≤ smin / 100 := by rw [he0def]
  have he0rpow : (0:ℝ) < Real.rpow e0 (-p) := Real.rpow_pos_of_pos he0pos (-p)
  set CA : ℝ := (3 + K) * (1 + Real.rpow e0 (-p)) with hCAdef
  have hCAnn : 0 ≤ CA := by rw [hCAdef]; exact mul_nonneg (by linarith) (by linarith)
  have hCApos : 0 < CA := by rw [hCAdef]; exact mul_pos (by linarith) (by linarith)
  set CB : ℝ := (3 + 4 * K) * (1 + Real.rpow e0 (-p)) with hCBdef
  have hCBnn : 0 ≤ CB := by rw [hCBdef]; exact mul_nonneg (by linarith) (by linarith)
  have hCBpos : 0 < CB := by rw [hCBdef]; exact mul_pos (by linarith) (by linarith)
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set Cst0 : ℝ := CL * Kd * (n : ℝ) * CB with hCst0def
  have hCst0pos : 0 < Cst0 := by
    rw [hCst0def]
    exact mul_pos (mul_pos (mul_pos hCLpos hKdpos) hnR) hCBpos
  set d0 : ℝ := min (smin / 100) (Real.rpow (1 / Cst0) (1 / (1 - α))) with hd0def
  have hd0pos : 0 < d0 := by
    rw [hd0def]
    exact lt_min (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
  have hd0le : d0 ≤ smin / 100 := min_le_left _ _
  have hd0rpow : Real.rpow d0 (1 - α) ≤ 1 / Cst0 := by
    have hCpos : (0:ℝ) < 1 / Cst0 := by positivity
    have h1 : d0 ≤ Real.rpow (1 / Cst0) (1 / (1 - α)) := min_le_right _ _
    have h2 : Real.rpow d0 (1 - α) ≤ Real.rpow (Real.rpow (1 / Cst0) (1 / (1 - α))) (1 - α) :=
      Real.rpow_le_rpow hd0pos.le h1 (by linarith)
    have h3 : Real.rpow (Real.rpow (1 / Cst0) (1 / (1 - α))) (1 - α)
        = Real.rpow (1 / Cst0) ((1 / (1 - α)) * (1 - α)) :=
      (Real.rpow_mul (le_of_lt hCpos) (1 / (1 - α)) (1 - α)).symm
    have h4 : Real.rpow (1 / Cst0) ((1 / (1 - α)) * (1 - α)) = 1 / Cst0 := by
      rw [show (1 / (1 - α)) * (1 - α) = 1 from by field_simp]
      exact Real.rpow_one _
    linarith [h2, h3, h4]
  -- ## the bases of the growth
  set Bp : ℝ := Real.rpow 2 p with hBpdef
  have hBp1 : 1 ≤ Bp := by rw [hBpdef]; exact one_le_rpow_two hppos.le
  set Bal : ℝ := Real.rpow 2 α with hBaldef
  have hBal1 : 1 ≤ Bal := by rw [hBaldef]; exact one_le_rpow_two hα0.le
  have hBalnn : (0:ℝ) ≤ Bal := by rw [hBaldef]; exact Real.rpow_nonneg (by norm_num) α
  set Bq : ℝ := Real.rpow 2 (p + (m:ℝ) * α) with hBqdef
  have hBq1 : 1 ≤ Bq := by rw [hBqdef]; exact one_le_rpow_two (by positivity)
  set B1 : ℝ := Real.rpow 2 (-(1 - α)) with hB1def
  have hB1nn : (0:ℝ) ≤ B1 := by rw [hB1def]; exact Real.rpow_nonneg (by norm_num) (-(1 - α))
  have hB1eq : B1 = Real.rpow (1/2) (1 - α) := by
    rw [hB1def]; exact (rpow_half_eq (1 - α)).symm
  set beta : ℝ := (m:ℝ) * (1 - α) - p with hbetadef
  have hbeta1 : 1 < beta := by rw [hbetadef]; linarith
  have hB1m : Bp * B1 ^ m = Real.rpow 2 (-beta) := by
    have hstep : B1 ^ m = Real.rpow 2 ((m:ℝ) * (-(1 - α))) := by
      rw [hB1def]
      change ((2:ℝ)^(-(1-α)))^m = ((2:ℝ)^((m:ℝ)*(-(1-α))))
      rw [← Real.rpow_natCast ((2:ℝ)^(-(1-α))) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(1-α)) (m:ℝ)]
      congr 1
      ring
    have hstep2 : Bp * Real.rpow 2 ((m:ℝ) * (-(1 - α))) = Real.rpow 2 (-beta) := by
      rw [hBpdef]
      change ((2:ℝ)^p) * ((2:ℝ)^((m:ℝ)*(-(1-α)))) = ((2:ℝ)^(-beta))
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), hbetadef]
      congr 1
      ring
    rw [hstep, hstep2]
  have hB1le : Real.rpow 2 (-beta) ≤ 1/2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show -beta ≤ -1 from by linarith)
    have h2 : Real.rpow 2 (-1) = (1/2:ℝ) := by
      change ((2:ℝ)^((-1:ℝ))) = (1/2:ℝ)
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) 1]
      norm_num
    rw [← h2]
    exact h
  set CstL : ℝ := CL * Kd * (n : ℝ) * CB * Real.rpow d0 (1 - α) with hCstLdef
  have hCstLle : CstL ≤ 1 := by
    rw [hCstLdef]
    have hbase : (0:ℝ) ≤ CL * Kd * (n:ℝ) * CB :=
      mul_nonneg (mul_nonneg (mul_nonneg hCLpos.le hKdpos.le) hnR.le) hCBnn
    calc CL * Kd * (n:ℝ) * CB * Real.rpow d0 (1 - α)
        ≤ CL * Kd * (n:ℝ) * CB * (1/Cst0) := mul_le_mul_of_nonneg_left hd0rpow hbase
      _ = 1 := by
          rw [hCst0def]
          field_simp
  set A2 : ℝ := CL * CA with hA2def
  have hA2nn : 0 ≤ A2 := by rw [hA2def]; positivity
  set B2 : ℝ := CL * Kd * (n : ℝ) * CB * (1 + 2 * Real.rpow d0 (-α)) with hB2def
  have hB2nn : 0 ≤ B2 := by
    rw [hB2def]
    have hr : (0:ℝ) ≤ Real.rpow d0 (-α) := (Real.rpow_pos_of_pos hd0pos (-α)).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCLpos.le hKdpos.le) hnR.le) hCBnn)
      (by linarith)
  obtain ⟨I0A, hI0A⟩ : ∃ I0A : ℕ, 2 * p + 3 ≤ (I0A:ℝ) := exists_nat_ge (2*p+3)
  obtain ⟨I0B, hI0B⟩ : ∃ I0B : ℕ, 2 * (p + (m:ℝ)*α) + 3 ≤ (I0B:ℝ) :=
    exists_nat_ge (2*(p + (m:ℝ)*α) + 3)
  set DA : ℝ := A2 * Bp ^ I0A * (2:ℝ) ^ I0A with hDAdef
  set DB : ℝ := B2 * Bq ^ I0B * (2:ℝ) ^ I0B with hDBdef
  set Cfin : ℝ := 1 + 2 * DA + 2 * DB with hCfindef
  have hBp0 : (0:ℝ) < Bp := lt_of_lt_of_le one_pos hBp1
  have hBq0 : (0:ℝ) < Bq := lt_of_lt_of_le one_pos hBq1
  have hDA0 : 0 ≤ DA := by
    rw [hDAdef]
    exact mul_nonneg (mul_nonneg hA2nn (pow_nonneg hBp0.le _)) (pow_nonneg (by norm_num) _)
  have hDB0 : 0 ≤ DB := by
    rw [hDBdef]
    exact mul_nonneg (mul_nonneg hB2nn (pow_nonneg hBq0.le _)) (pow_nonneg (by norm_num) _)
  have hCfinpos : 0 < Cfin := by rw [hCfindef]; linarith
  refine ⟨eps0, heps0pos, Cfin, hCfinpos, ?_⟩
  intro A hAsm ε hε hsmall hJ u hu
  -- ## the datum and the norm quantities
  set X : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ) with hXdef
  set Z : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ, ENNReal.ofReal ‖u z‖ with hZdef
  set Me : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'', ENNReal.ofReal ‖fderiv ℝ u z‖
    with hMedef
  have hMelt : Me < ⊤ := by
    rw [hMedef]
    exact iSup_ofReal_norm_fderiv_lt_top hn hρ0 hρ''ρ hu
  by_cases hXtop : X = ⊤
  · rw [hXtop, top_add, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCfinpos)]
    exact le_top
  by_cases hZtop : Z = ⊤
  · rw [hZtop, add_top, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCfinpos)]
    exact le_top
  -- ## the sequences of radii
  set Efun : ℕ → ℝ := fun i => e0 * ((1/2:ℝ))^i with hEfundef
  set Dfun : ℕ → ℝ := fun i => d0 * ((1/2:ℝ))^(m*i) with hDfundef
  have hEv : ∀ i, Efun i = e0 * ((1/2:ℝ))^i := fun i => by simp only [hEfundef]
  have hDv : ∀ i, Dfun i = d0 * ((1/2:ℝ))^(m*i) := fun i => by simp only [hDfundef]
  set Rfun : ℕ → Fin n → ℝ :=
    fun i j => ρ' j + ∑ k ∈ Finset.range i, (Efun k + Dfun k) with hRfundef
  have hEpos : ∀ i, 0 < Efun i := fun i => by rw [hEfundef]; positivity
  have hDpos : ∀ i, 0 < Dfun i := fun i => by rw [hDfundef]; positivity
  have hEsum : ∀ i, (∑ k ∈ Finset.range i, Efun k) ≤ 2 * e0 := by
    intro i
    have h : ∀ k, Efun k = e0 * ((1/2:ℝ))^k := fun k => by rw [hEfundef]
    simp only [h, ← Finset.mul_sum]
    have h2 := sum_range_half_pow_le i
    nlinarith [he0pos.le]
  have hDsum : ∀ i, (∑ k ∈ Finset.range i, Dfun k) ≤ 2 * d0 := by
    intro i
    have h : ∀ k, Dfun k = d0 * ((1/2:ℝ))^(m*k) := fun k => by rw [hDfundef]
    simp only [h, ← Finset.mul_sum]
    have hle : (∑ k ∈ Finset.range i, ((1/2:ℝ))^(m*k)) ≤ ∑ k ∈ Finset.range i, ((1/2:ℝ))^k :=
      Finset.sum_le_sum fun k _ => half_pow_mul_le hm1
    have h2 := sum_range_half_pow_le i
    nlinarith [hd0pos.le]
  have hRd : ∀ i j, Rfun i j + (Efun i + Dfun i) ≤ ρ'' j := by
    intro i j
    have hsum1 : (∑ k ∈ Finset.range i, (Efun k + Dfun k)) ≤ 2*e0 + 2*d0 := by
      rw [Finset.sum_add_distrib]; linarith [hEsum i, hDsum i]
    have hED : Efun i + Dfun i ≤ e0 + d0 := by
      rw [hEfundef, hDfundef]
      have h1 : ((1/2:ℝ))^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : ((1/2:ℝ))^(m*i) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [he0pos.le, hd0pos.le]
    have hkey : 3*e0 + 3*d0 ≤ s j / 2 := by
      have h1 : e0 = smin/100 := he0def
      have h3 : smin ≤ s j := hsminle j
      linarith [hd0le]
    simp only [hRfundef, hρ''def]
    linarith
  have hRe : ∀ i j, Rfun i j + Efun i ≤ ρ'' j := by
    intro i j
    have hsum1 : (∑ k ∈ Finset.range i, (Efun k + Dfun k)) ≤ 2*e0 + 2*d0 := by
      rw [Finset.sum_add_distrib]; linarith [hEsum i, hDsum i]
    have h2 : Efun i ≤ e0 := by
      rw [hEfundef]
      have h1 : ((1/2:ℝ))^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [he0pos.le]
    have hkey : 2*e0 + 2*d0 + e0 ≤ s j / 2 := by
      have h1 : e0 = smin/100 := he0def
      have h3 : smin ≤ s j := hsminle j
      linarith [hd0le]
    simp only [hRfundef, hρ''def]
    linarith
  have hRsub : ∀ i j, Rfun i j ≤ ρ'' j := fun i j => by
    have h1 := hRe i j; linarith [hEpos i]
  have hRltρ : ∀ i j, Rfun i j < ρ j := fun i j => lt_of_le_of_lt (hRsub i j) (hρ''ρ j)
  have hRmin : ∀ i j, Rmin ≤ Rfun i j := by
    intro i j
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.range i, (Efun k + Dfun k) :=
      Finset.sum_nonneg fun k _ => by linarith [hEpos k, hDpos k]
    simp only [hRfundef]
    linarith [hRminle j]
  have hRmax : ∀ i j, Rfun i j ≤ Rmax := fun i j =>
    le_trans (hRsub i j) (hρ''leRmax j)
  have hRsucc : ∀ i, (fun j => Rfun i j + (Efun i + Dfun i)) = Rfun (i+1) := by
    intro i
    funext j
    simp only [hRfundef, Finset.sum_range_succ]
    ring
  -- ## the cutoffs
  choose χf hχf using fun i =>
    hcut (Rfun i) (Efun i) (fun j => hRmin i j) (fun j => hRmax i j) (hEpos i)
  have hχsm : ∀ i (m' : ℕ), ContDiff ℝ (m' : WithTop ℕ∞) (χf i) := fun i => (hχf i).1
  have hχnn : ∀ i z, 0 ≤ χf i z := fun i z => ((hχf i).2.1 z).1
  have hχle1 : ∀ i z, χf i z ≤ 1 := fun i z => ((hχf i).2.1 z).2
  have hχ1 : ∀ i z, (∀ j, ‖z j‖ ≤ Rfun i j) → χf i z = 1 := fun i => (hχf i).2.2.1
  have hχ0 : ∀ i z, (∃ j, Rfun i j + Efun i ≤ ‖z j‖) → χf i z = 0 := fun i => (hχf i).2.2.2.1
  have hχg : ∀ i x, ‖fderiv ℝ (fun z => (χf i z : ℂ)) x‖
      ≤ K * (1 + Real.rpow (Efun i) (-p)) := fun i => (hχf i).2.2.2.2.1
  have hχL : ∀ i x y, ‖fderiv ℝ (fun z => (χf i z : ℂ)) x
        - fderiv ℝ (fun z => (χf i z : ℂ)) y‖
      ≤ K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖ := fun i => (hχf i).2.2.2.2.2
  -- ## the level-`1` bounds for the cutoff
  set L1f : ℕ → ℝ := fun i => 3 + K * (1 + Real.rpow (Efun i) (-p)) with hL1fdef
  set L2f : ℕ → ℝ := fun i => 3 + 4 * (K * (1 + Real.rpow (Efun i) (-p))) with hL2fdef
  have hL1fv : ∀ i, L1f i = 3 + K * (1 + Real.rpow (Efun i) (-p)) := fun i => by simp only [hL1fdef]
  have hL2fv : ∀ i, L2f i = 3 + 4 * (K * (1 + Real.rpow (Efun i) (-p))) :=
    fun i => by simp only [hL2fdef]
  have hrpowE : ∀ i, (0:ℝ) < Real.rpow (Efun i) (-p) :=
    fun i => Real.rpow_pos_of_pos (hEpos i) (-p)
  have hL1fpos : ∀ i, 0 < L1f i := fun i => by
    simp only [hL1fdef]; have := hrpowE i; nlinarith [hKpos]
  have hL2fpos : ∀ i, 0 < L2f i := fun i => by
    simp only [hL2fdef]; have := hrpowE i; nlinarith [hKpos]
  have hL1fnn : ∀ i, 0 ≤ L1f i := fun i => by
    simp only [hL1fdef]; have := hrpowE i; nlinarith [hKpos.le]
  have hL2fnn : ∀ i, 0 ≤ L2f i := fun i => by
    simp only [hL2fdef]; have := hrpowE i; nlinarith [hKpos.le]
  have hL1 : ∀ i, Work.CR.Flat.Holder.iDN 0 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      + Work.CR.Flat.Holder.hSN 0 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal (L1f i) := by
    intro i
    have hMnn : 0 ≤ K * (1 + Real.rpow (Efun i) (-p)) := by
      have := hrpowE i; nlinarith [hKpos.le]
    have hχdiff : ∀ z, DifferentiableAt ℝ (fun z : Cn n => (χf i z : ℂ)) z := fun z => by
      have hd : Differentiable ℝ (fun z : Cn n => (χf i z : ℂ)) :=
        ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm i 1)).differentiable
          (by norm_num)
      exact hd.differentiableAt
    have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal 1 := by
      rw [Work.CR.Flat.Holder.iDN_zero_deriv]
      refine iSup₂_le fun z _ => ?_
      rw [show ‖(χf i z : ℂ)‖ = χf i z from by
        rw [show ‖(χf i z : ℂ)‖ = |χf i z| from RCLike.norm_ofReal (χf i z),
          abs_of_nonneg (hχnn i z)]]
      exact ENNReal.ofReal_le_ofReal (hχle1 i z)
    have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (max 2 (K * (1 + Real.rpow (Efun i) (-p)))) := by
      have h2' := hSN_zero_le_of_deriv_bound (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
        (χ := fun z : Cn n => (χf i z : ℂ))
        (M := K * (1 + Real.rpow (Efun i) (-p))) (Z := 1)
        hα0 hα1.le hMnn (by norm_num)
        hχdiff (fun x => hχg i x) (fun x => by
          rw [show ‖(χf i x : ℂ)‖ = χf i x from by
            rw [show ‖(χf i x : ℂ)‖ = |χf i x| from RCLike.norm_ofReal (χf i x),
              abs_of_nonneg (hχnn i x)]]
          exact hχle1 i x)
      refine h2'.trans_eq ?_
      congr 1
      rw [mul_one]
    have h3 : ENNReal.ofReal 1 + ENNReal.ofReal (max 2 (K * (1 + Real.rpow (Efun i) (-p))))
        ≤ ENNReal.ofReal (L1f i) := by
      rw [hL1fv i, ← ENNReal.ofReal_add (by norm_num)
        (le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_left _ _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : max (2:ℝ) (K * (1 + Real.rpow (Efun i) (-p)))
          ≤ 2 + K * (1 + Real.rpow (Efun i) (-p)) :=
        max_le (by linarith) (by linarith)
      linarith
    exact (add_le_add h1 h2).trans h3
  have hL2 : ∀ i, Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal (L2f i) := by
    intro i
    have hMnn : 0 ≤ K * (1 + Real.rpow (Efun i) (-p)) := by
      have := hrpowE i; nlinarith [hKpos.le]
    have hΩ'' : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := Work.CR.Flat.isOpen_polydisc 0 ρ''
    have h3 : Work.CR.Flat.iterDerivNorm 1 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (K * (1 + Real.rpow (Efun i) (-p))) := by
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun z hz => ?_
      rw [norm_iteratedFDerivWithin_one_eq hΩ'' (fun z : Cn n => (χf i z : ℂ)) hz]
      exact ENNReal.ofReal_le_ofReal (hχg i z)
    have h4 : Work.CR.Flat.holderSeminorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (2 * (K * (1 + Real.rpow (Efun i) (-p)))) := by
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      have hx' : x ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'' := hx
      have hy' : y ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'' := hy
      rw [norm_iteratedFDerivWithin_one_sub_eq hΩ'' (fun z : Cn n => (χf i z : ℂ)) hx' hy']
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hxyα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hxy0 α
      by_cases hle : ‖x - y‖ ≤ 1
      · have hpow : ‖x - y‖ ^ (1 - α) ≤ 1 := Real.rpow_le_one hxy0.le hle (by linarith)
        have hsub : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
          rw [Real.rpow_sub hxy0 (1:ℝ) α, Real.rpow_one]
        calc ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
              - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖ / ‖x - y‖ ^ α
            ≤ (K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right (hχL i x y) hxyα.le
          _ = K * (1 + Real.rpow (Efun i) (-p)) * (‖x - y‖ / ‖x - y‖ ^ α) := by ring
          _ = K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖ ^ (1 - α) := by rw [hsub]
          _ ≤ K * (1 + Real.rpow (Efun i) (-p)) * 1 := mul_le_mul_of_nonneg_left hpow hMnn
          _ ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) := by linarith
      · have h2b : ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
            - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖
            ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) := by
          have hxa := hχg i x
          have hya := hχg i y
          have := norm_sub_le (fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x)
            (fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y)
          linarith
        have hα1' : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (not_le.mp hle).le hα0.le
        calc ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
              - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖ / ‖x - y‖ ^ α
            ≤ (2 * (K * (1 + Real.rpow (Efun i) (-p)))) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right h2b hxyα.le
          _ ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) :=
              div_le_self (by have := hrpowE i; nlinarith [hKpos.le]) hα1'
    have h5 := hL1 i
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_one]
    have hsum : ENNReal.ofReal (L1f i) + (ENNReal.ofReal (K * (1 + Real.rpow (Efun i) (-p)))
        + ENNReal.ofReal (2 * (K * (1 + Real.rpow (Efun i) (-p))))) = ENNReal.ofReal (L2f i) := by
      rw [hL1fv i, hL2fv i,
        ← ENNReal.ofReal_add (p := K * (1 + Real.rpow (Efun i) (-p)))
          (q := 2 * (K * (1 + Real.rpow (Efun i) (-p)))) hMnn (by linarith),
        ← ENNReal.ofReal_add (p := 3 + K * (1 + Real.rpow (Efun i) (-p)))
          (q := K * (1 + Real.rpow (Efun i) (-p)) + 2 * (K * (1 + Real.rpow (Efun i) (-p))))
          (by linarith) (by linarith)]
      congr 1
      ring
    exact (add_le_add h5 (add_le_add h3 h4)).trans (le_of_eq hsum)
  -- ## the datum bound for the cutoff
  have hdatai : ∀ (i : ℕ) (j : Fin n), Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) (fun z => (χf i z : ℂ)) z (Pi.single j 1))
      (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal Kd * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ))
          (Work.CR.Flat.polydisc 0 ρ'') := by
    intro i j
    have hε' : 0 ≤ max ε 0 := le_max_right _ _
    have hε'le : max ε 0 ≤ eps0 := max_le hε (le_of_lt heps0pos)
    have hBsm : ∀ i' l : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i' 1) l)
        (Work.CR.Flat.polydisc 0 ρ'') ≤ ENNReal.ofReal (max ε 0) := by
      intro i' l
      refine (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ)
        (Work.CR.Flat.isOpen_polydisc 0 ρ'') ?_ 0 α (fun z => A z (Pi.single i' 1) l)).trans ?_
      · exact fun z hz j => lt_trans (hz j) (hρ''ρ j)
      · exact ((Work.CR.Flat.holderNorm_mono_k (k := 0) (k' := 1) (by norm_num) α
            (fun z => A z (Pi.single i' 1) l) (Work.CR.Flat.polydisc 0 ρ)).trans
          (hsmall i' l)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hBc : ∀ i' l : Fin n, ContDiffOn ℝ 0 (fun z => A z (Pi.single i' 1) l)
        (Work.CR.Flat.polydisc 0 ρ'') := by
      intro i' l
      rw [contDiffOn_zero]
      have hAcont : Continuous A := contDiff_zero.mp (hAsm 0)
      have h1 : Continuous (fun z : Cn n => A z (Pi.single i' 1)) :=
        hAcont.clm_apply continuous_const
      exact ((continuous_apply l).comp h1).continuousOn
    have hχi : ContDiffOn ℝ 1 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'') :=
      ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm i 1)).contDiffOn
    have hres := hdatac hχi hε' hBsm hBc j
    refine hres.trans ?_
    have hCdnn : (0:ℝ) ≤ Cd := hCdpos.le
    have h1m : 1 + max ε 0 ≤ 1 + eps0 := by linarith
    have hcoef : ENNReal.ofReal Cd * ENNReal.ofReal (1 + max ε 0) ≤ ENNReal.ofReal Kd := by
      rw [hKddef, ← ENNReal.ofReal_mul hCdnn]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1m hCdpos.le)
    calc ENNReal.ofReal Cd * (ENNReal.ofReal (1 + max ε 0)
          * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ''))
        = (ENNReal.ofReal Cd * ENNReal.ofReal (1 + max ε 0))
          * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'') :=
          by rw [mul_assoc]
      _ ≤ ENNReal.ofReal Kd * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ))
            (Work.CR.Flat.polydisc 0 ρ'') := mul_le_mul hcoef le_rfl bot_le bot_le
  -- ## the coefficient sequences
  set ar : ℕ → ℝ := fun i => CL * L1f i with hardef
  set br : ℕ → ℝ := fun i => CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * Real.rpow (Dfun i) (-α))
    with hbrdef
  set lr : ℕ → ℝ := fun i => CL * (Kd * (n:ℝ) * L2f i) * Real.rpow (Dfun i) (1 - α) with hlrdef
  set P : ℕ → ℝ := fun i => ∏ k ∈ Finset.range i, lr k with hPdef
  have harv : ∀ i, ar i = CL * L1f i := fun i => by simp only [hardef]
  have hbrv : ∀ i, br i = CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * Real.rpow (Dfun i) (-α)) :=
    fun i => by simp only [hbrdef]
  have hlrv : ∀ i, lr i = CL * (Kd * (n:ℝ) * L2f i) * Real.rpow (Dfun i) (1-α) :=
    fun i => by simp only [hlrdef]
  have hPv : ∀ i, P i = ∏ k ∈ Finset.range i, lr k := fun i => by simp only [hPdef]
  have hP0 : P 0 = 1 := by simp [hPdef]
  have hPsucc : ∀ i, P (i+1) = P i * lr i := fun i => by
    simp only [hPdef, Finset.prod_range_succ]
  -- ## the growth of `Real.rpow (Efun i) (-p)` etc.
  have hEpow : ∀ i, Real.rpow (Efun i) (-p) = Real.rpow e0 (-p) * Bp ^ i := by
    intro i
    rw [hEv i]
    have key : Real.rpow (e0 * ((1/2:ℝ))^i) (-p)
        = Real.rpow e0 (-p) * Real.rpow ((1/2:ℝ)^i) (-p) :=
      Real.mul_rpow (x := e0) (y := ((1/2:ℝ))^i) (z := -p) he0pos.le (by positivity)
    rw [key, hBpdef, rpow_half_pow_neg i p]
  have hDpow1 : ∀ i, Real.rpow (Dfun i) (1-α) = Real.rpow d0 (1-α) * B1 ^ (m*i) := by
    intro i
    rw [hDv i]
    have key : Real.rpow (d0 * ((1/2:ℝ))^(m*i)) (1-α)
        = Real.rpow d0 (1-α) * Real.rpow ((1/2:ℝ)^(m*i)) (1-α) :=
      Real.mul_rpow (x := d0) (y := ((1/2:ℝ))^(m*i)) (z := 1-α) hd0pos.le (by positivity)
    rw [key, rpow_half_pow (m*i) (1-α), ← hB1eq]
  have hDpowα : ∀ i, Real.rpow (Dfun i) (-α) = Real.rpow d0 (-α) * Bal ^ (m*i) := by
    intro i
    rw [hDv i]
    have key : Real.rpow (d0 * ((1/2:ℝ))^(m*i)) (-α)
        = Real.rpow d0 (-α) * Real.rpow ((1/2:ℝ)^(m*i)) (-α) :=
      Real.mul_rpow (x := d0) (y := ((1/2:ℝ))^(m*i)) (z := -α) hd0pos.le (by positivity)
    rw [key, hBaldef, rpow_half_pow_neg (m*i) α]
  -- ## the bounds on the coefficients
  have hL1b : ∀ i, L1f i ≤ CA * Bp ^ i := by
    intro i
    rw [hL1fv i, hEpow i, hCAdef]
    have h1 : (1:ℝ) ≤ Bp ^ i := one_le_pow₀ hBp1
    have h2 := Real.rpow_pos_of_pos he0pos (-p)
    nlinarith [h1, h2, hKpos.le, hBp1]
  have hL2b : ∀ i, L2f i ≤ CB * Bp ^ i := by
    intro i
    rw [hL2fv i, hEpow i, hCBdef]
    have h1 : (1:ℝ) ≤ Bp ^ i := one_le_pow₀ hBp1
    have h2 := Real.rpow_pos_of_pos he0pos (-p)
    nlinarith [h1, h2, hKpos.le, hBp1]
  have harb : ∀ i, ar i ≤ A2 * Bp ^ i := by
    intro i
    rw [harv i, hA2def]
    calc CL * L1f i ≤ CL * (CA * Bp ^ i) := mul_le_mul_of_nonneg_left (hL1b i) hCLpos.le
      _ = CL * CA * Bp ^ i := by ring
  have hlrb : ∀ i, lr i ≤ ((1/2:ℝ))^i := by
    intro i
    have hkey : lr i ≤ CstL * (Bp * B1 ^ m) ^ i := by
      rw [hlrv i, hCstLdef, hDpow1 i]
      have h1 : CL * (Kd * (n:ℝ) * L2f i) ≤ CL * Kd * (n:ℝ) * CB * Bp ^ i := by
        have h2 : Kd * (n:ℝ) * L2f i ≤ Kd * (n:ℝ) * (CB * Bp ^ i) :=
          mul_le_mul_of_nonneg_left (hL2b i) (by positivity)
        calc CL * (Kd * (n:ℝ) * L2f i) ≤ CL * (Kd * (n:ℝ) * (CB * Bp ^ i)) :=
              mul_le_mul_of_nonneg_left h2 hCLpos.le
          _ = CL * Kd * (n:ℝ) * CB * Bp ^ i := by ring
      calc CL * (Kd * (n:ℝ) * L2f i) * (Real.rpow d0 (1-α) * B1^(m*i))
          ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * (Real.rpow d0 (1-α) * B1^(m*i)) :=
            mul_le_mul_of_nonneg_right h1
              (mul_nonneg (Real.rpow_nonneg hd0pos.le (1-α)) (pow_nonneg hB1nn _))
        _ = CstL * (Bp ^ i * B1^(m*i)) := by rw [hCstLdef]; ring
        _ = CstL * (Bp * B1 ^ m) ^ i := by rw [pow_mul B1 m i, ← mul_pow Bp (B1^m) i]
    calc lr i ≤ CstL * (Bp * B1 ^ m) ^ i := hkey
      _ ≤ 1 * (Real.rpow 2 (-beta))^i := by
          rw [hB1m]
          exact mul_le_mul_of_nonneg_right hCstLle
            (pow_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) i)
      _ ≤ 1 * ((1/2:ℝ))^i := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-beta))
            (le_trans hB1le (by norm_num)) i
      _ = ((1/2:ℝ))^i := one_mul _
  have hbrb : ∀ i, br i ≤ B2 * Bq ^ i := by
    intro i
    have hkey : br i ≤ B2 * ((Bp * Bal ^ m) ^ i) := by
      rw [hbrv i, hB2def, hDpowα i]
      have h1 : CL * (Kd * (n:ℝ) * L2f i)
          ≤ CL * Kd * (n:ℝ) * CB * Bp ^ i := by
        have h2 : Kd * (n:ℝ) * L2f i ≤ Kd * (n:ℝ) * (CB * Bp ^ i) :=
          mul_le_mul_of_nonneg_left (hL2b i) (by positivity)
        calc CL * (Kd * (n:ℝ) * L2f i) ≤ CL * (Kd * (n:ℝ) * (CB * Bp ^ i)) :=
              mul_le_mul_of_nonneg_left h2 hCLpos.le
          _ = CL * Kd * (n:ℝ) * CB * Bp ^ i := by ring
      have h2 : (1:ℝ) + 2 * (Real.rpow d0 (-α) * Bal^(m*i))
          ≤ (1 + 2 * Real.rpow d0 (-α)) * Bal^(m*i) := by
        have hb1 : (1:ℝ) ≤ Bal^(m*i) := one_le_pow₀ hBal1
        have hb2 : (0:ℝ) ≤ Real.rpow d0 (-α) :=
          (Real.rpow_pos_of_pos hd0pos (-α)).le
        nlinarith
      calc CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * (Real.rpow d0 (-α) * Bal^(m*i)))
          ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * (1 + 2 * (Real.rpow d0 (-α) * Bal^(m*i))) :=
            mul_le_mul_of_nonneg_right h1 (by
              have hb2 : (0:ℝ) ≤ Real.rpow d0 (-α) :=
                (Real.rpow_pos_of_pos hd0pos (-α)).le
              have hb1 : (1:ℝ) ≤ Bal ^ (m*i) := one_le_pow₀ hBal1
              nlinarith)
        _ ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * ((1 + 2 * Real.rpow d0 (-α)) * Bal^(m*i)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = B2 * (Bp ^ i * Bal^(m*i)) := by rw [hB2def]; ring
        _ = B2 * (Bp * Bal ^ m) ^ i := by rw [pow_mul Bal m i, ← mul_pow Bp (Bal^m) i]
    calc br i ≤ B2 * ((Bp * Bal ^ m) ^ i) := hkey
      _ = B2 * Bq ^ i := by
          congr 1
          rw [hBqdef]
          congr 1
          rw [hBpdef, hBaldef]
          change ((2:ℝ)^p) * (((2:ℝ)^α)^m) = ((2:ℝ)^(p + (m:ℝ)*α))
          rw [← Real.rpow_natCast ((2:ℝ)^α) m,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) α (m:ℝ),
            ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
  -- ## the bounds on the products
  have harnn : ∀ i, 0 ≤ ar i := fun i => by rw [harv i]; exact mul_nonneg hCLpos.le (hL1fnn i)
  have hDpowαnn : ∀ i, (0:ℝ) ≤ Real.rpow (Dfun i) (-α) :=
    fun i => (Real.rpow_pos_of_pos (hDpos i) (-α)).le
  have hDpow1nn : ∀ i, (0:ℝ) ≤ Real.rpow (Dfun i) (1-α) :=
    fun i => (Real.rpow_pos_of_pos (hDpos i) (1-α)).le
  have hbrnn : ∀ i, 0 ≤ br i := fun i => by
    rw [hbrv i]
    have h1 : (0:ℝ) ≤ CL := hCLpos.le
    have h2 : (0:ℝ) ≤ Kd := hKdpos.le
    have h3 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h4 : (0:ℝ) ≤ L2f i := hL2fnn i
    have h5 : (0:ℝ) ≤ Real.rpow (Dfun i) (-α) := hDpowαnn i
    positivity
  have hlrnn : ∀ i, 0 ≤ lr i := fun i => by
    rw [hlrv i]
    have h1 : (0:ℝ) ≤ CL := hCLpos.le
    have h2 : (0:ℝ) ≤ Kd := hKdpos.le
    have h3 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h4 : (0:ℝ) ≤ L2f i := hL2fnn i
    have h5 : (0:ℝ) ≤ Real.rpow (Dfun i) (1-α) := hDpow1nn i
    positivity
  have hPnn' : ∀ i, 0 ≤ P i := fun i => by
    rw [hPv i]; exact Finset.prod_nonneg fun k _ => hlrnn k
  have hPbound : ∀ i, P i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) := by
    intro i
    have h1 : P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := by
      rw [hPv i]
      exact prod_range_le_of_nonneg (fun k => hlrnn k) (fun k => pow_nonneg (by norm_num) k)
        (fun k => hlrb k) i
    have h2 : (∏ k ∈ Finset.range i, ((1/2:ℝ))^k)
        = ((1/2:ℝ))^(∑ k ∈ Finset.range i, k) := Finset.prod_pow_eq_pow_sum _ _ _
    have h3 : ((1/2:ℝ))^(∑ k ∈ Finset.range i, k)
        = Real.rpow 2 (-((∑ k ∈ Finset.range i, k : ℕ):ℝ)) :=
      (rpow_two_neg_nat _).symm
    have h4 : ((∑ k ∈ Finset.range i, k : ℕ):ℝ) = (i:ℝ)*((i:ℝ)-1)/2 := cast_range_sum_id i
    calc P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := h1
      _ = ((1/2:ℝ))^(∑ k ∈ Finset.range i, k) := h2
      _ = Real.rpow 2 (-((∑ k ∈ Finset.range i, k : ℕ):ℝ)) := h3
      _ = Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) := by rw [h4]
  have hP1 : ∀ i, P i ≤ 1 := by
    intro i
    calc P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := by
          rw [hPv i]
          exact prod_range_le_of_nonneg (fun k => hlrnn k) (fun k => pow_nonneg (by norm_num) k)
            (fun k => hlrb k) i
      _ ≤ 1 := prod_range_half_le_one i
  have hPar : ∀ i, P i * ar i ≤ DA * ((1/2:ℝ))^i := by
    intro i
    by_cases hi : i ≤ I0A
    · have h3 : Bp ^ i ≤ Bp ^ I0A := pow_le_pow_right₀ hBp1 hi
      have h4 : (1:ℝ) ≤ (2:ℝ)^I0A * ((1/2:ℝ))^i := by
        have h5 : ((1/2:ℝ))^I0A ≤ ((1/2:ℝ))^i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
        have h6 : ((1/2:ℝ))^I0A * (2:ℝ)^I0A = 1 := by rw [← mul_pow]; norm_num
        have h7 : (0:ℝ) < (2:ℝ)^I0A := by positivity
        nlinarith [h5, h6, h7]
      calc P i * ar i ≤ 1 * (A2 * Bp ^ i) :=
            mul_le_mul (hP1 i) (harb i) (harnn i) (by norm_num)
        _ = A2 * Bp ^ i := one_mul _
        _ ≤ A2 * Bp ^ I0A := mul_le_mul_of_nonneg_left h3 hA2nn
        _ ≤ A2 * Bp ^ I0A * ((2:ℝ)^I0A * ((1/2:ℝ))^i) :=
            le_mul_of_one_le_right (mul_nonneg hA2nn (pow_nonneg (le_of_lt hBp0) I0A)) h4
        _ = DA * ((1/2:ℝ))^i := by rw [hDAdef]; ring
    · have hiI : (I0A:ℝ) < (i:ℝ) := by exact_mod_cast (not_le.mp hi)
      have h5 : p * (i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2 ≤ -(i:ℝ) := by
        have hi2 : (2*p+3 : ℝ) ≤ (i:ℝ) := le_trans hI0A hiI.le
        have hpos : (0:ℝ) < (i:ℝ) := by linarith
        nlinarith
      have h6 : Bp ^ i = Real.rpow 2 (p * (i:ℝ)) := by rw [hBpdef]; exact rpow_two_mul_nat i p
      have h7 : Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 (p * (i:ℝ))
          = Real.rpow 2 (p*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by
        rw [show Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 (p * (i:ℝ))
            = ((2:ℝ) ^ (-((i:ℝ)*((i:ℝ)-1)/2))) * ((2:ℝ) ^ (p * (i:ℝ))) from rfl,
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc P i * ar i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * (A2 * Bp ^ i) :=
            mul_le_mul (hPbound i) (harb i) (harnn i) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        _ = A2 * (Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Bp ^ i) := by ring
        _ = A2 * Real.rpow 2 (p*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by rw [h6, h7]
        _ ≤ A2 * Real.rpow 2 (-(i:ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA2nn
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        _ = A2 * ((1/2:ℝ))^i := by rw [rpow_two_neg_nat i]
        _ ≤ DA * ((1/2:ℝ))^i := by
            rw [hDAdef]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h8 : (1:ℝ) ≤ Bp ^ I0A := one_le_pow₀ hBp1
            have h9 : (1:ℝ) ≤ (2:ℝ)^I0A := one_le_pow₀ (by norm_num)
            calc A2 ≤ A2 * Bp ^ I0A := le_mul_of_one_le_right hA2nn h8
              _ ≤ A2 * Bp ^ I0A * (2:ℝ)^I0A :=
                  le_mul_of_one_le_right (mul_nonneg hA2nn (pow_nonneg hBp0.le I0A)) h9
  have hPbr : ∀ i, P i * br i ≤ DB * ((1/2:ℝ))^i := by
    intro i
    by_cases hi : i ≤ I0B
    · have h3 : Bq ^ i ≤ Bq ^ I0B := pow_le_pow_right₀ hBq1 hi
      have h4 : (1:ℝ) ≤ (2:ℝ)^I0B * ((1/2:ℝ))^i := by
        have h5 : ((1/2:ℝ))^I0B ≤ ((1/2:ℝ))^i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
        have h6 : ((1/2:ℝ))^I0B * (2:ℝ)^I0B = 1 := by rw [← mul_pow]; norm_num
        have h7 : (0:ℝ) < (2:ℝ)^I0B := by positivity
        nlinarith [h5, h6, h7]
      calc P i * br i ≤ 1 * (B2 * Bq ^ i) :=
            mul_le_mul (hP1 i) (hbrb i) (hbrnn i) (by norm_num)
        _ = B2 * Bq ^ i := one_mul _
        _ ≤ B2 * Bq ^ I0B := mul_le_mul_of_nonneg_left h3 hB2nn
        _ ≤ B2 * Bq ^ I0B * ((2:ℝ)^I0B * ((1/2:ℝ))^i) :=
            le_mul_of_one_le_right (mul_nonneg hB2nn (pow_nonneg (le_of_lt hBq0) I0B)) h4
        _ = DB * ((1/2:ℝ))^i := by rw [hDBdef]; ring
    · have hiI : (I0B:ℝ) < (i:ℝ) := by exact_mod_cast (not_le.mp hi)
      have h5 : (p + (m:ℝ)*α) * (i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2 ≤ -(i:ℝ) := by
        have hi2 : (2*(p + (m:ℝ)*α)+3 : ℝ) ≤ (i:ℝ) := le_trans hI0B hiI.le
        have hpos : (0:ℝ) < (i:ℝ) := by linarith
        nlinarith
      have h6 : Bq ^ i = Real.rpow 2 ((p + (m:ℝ)*α) * (i:ℝ)) := by
        rw [hBqdef]; exact rpow_two_mul_nat i _
      have h7 : Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 ((p+(m:ℝ)*α) * (i:ℝ))
          = Real.rpow 2 ((p+(m:ℝ)*α)*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by
        rw [show Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 ((p+(m:ℝ)*α) * (i:ℝ))
            = ((2:ℝ) ^ (-((i:ℝ)*((i:ℝ)-1)/2))) * ((2:ℝ) ^ ((p+(m:ℝ)*α) * (i:ℝ))) from rfl,
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc P i * br i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * (B2 * Bq ^ i) :=
            mul_le_mul (hPbound i) (hbrb i) (hbrnn i) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        _ = B2 * (Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Bq ^ i) := by ring
        _ = B2 * Real.rpow 2 ((p+(m:ℝ)*α)*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by rw [h6, h7]
        _ ≤ B2 * Real.rpow 2 (-(i:ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hB2nn
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        _ = B2 * ((1/2:ℝ))^i := by rw [rpow_two_neg_nat i]
        _ ≤ DB * ((1/2:ℝ))^i := by
            rw [hDBdef]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h8 : (1:ℝ) ≤ Bq ^ I0B := one_le_pow₀ hBq1
            have h9 : (1:ℝ) ≤ (2:ℝ)^I0B := one_le_pow₀ (by norm_num)
            calc B2 ≤ B2 * Bq ^ I0B := le_mul_of_one_le_right hB2nn h8
              _ ≤ B2 * Bq ^ I0B * (2:ℝ)^I0B :=
                  le_mul_of_one_le_right (mul_nonneg hB2nn (pow_nonneg hBq0.le I0B)) h9
  -- ## the chain
  set V : ℕ → ℝ≥0∞ := fun i => Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 (Rfun i))
    with hVdef
  set Mes : ℕ → ℝ≥0∞ := fun i =>
    ⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (Rfun i), ENNReal.ofReal ‖fderiv ℝ u z‖ with hMesdef
  have hMesV : ∀ i, Mes i ≤ V i := by
    intro i
    have hΩr : IsOpen (Work.CR.Flat.polydisc (0:Cn n) (Rfun i)) := Work.CR.Flat.isOpen_polydisc 0 _
    rw [hMesdef]
    refine le_trans ?_ (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α u
      (Work.CR.Flat.polydisc 0 (Rfun i)) (le_refl 1))
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    refine le_iSup₂_of_le z hz ?_
    rw [norm_iteratedFDerivWithin_one_eq hΩr u hz]
  have hMesM : ∀ i, Mes i ≤ Me := by
    intro i
    rw [hMesdef, hMedef]
    refine iSup₂_le fun z hz => ?_
    exact le_iSup₂_of_le z (fun j => lt_of_lt_of_le (hz j) (hRsub i j)) le_rfl
  have hstep : ∀ i, V i ≤ ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z
      + ENNReal.ofReal (lr i) * V (i+1) := by
    intro i
    have h := onestepSup (A := A) hn hα0 hα1 hρ''0 hρ''ρ hCLpos hKdpos (hL1fpos i)
      (hL2fpos i) (hDpos i) (fun v hv hvc => hloss hAsm (le_trans hε (min_le_left εL 1)) hsmall hJ v hv hvc)
      (hEpos i) (fun j : Fin n => hRe i j) (hχsm i) (hχ1 i) (hχ0 i) (hL1 i) (hL2 i) (hdatai i) hu
    refine h.trans ?_
    have hm : (⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (fun j => Rfun i j + (Efun i + Dfun i)),
        ENNReal.ofReal ‖fderiv ℝ u z‖) ≤ V (i+1) := by
      rw [hRsucc i]
      exact hMesV (i+1)
    exact add_le_add (add_le_add (by rw [hardef, hXdef]) (by rw [hbrdef, hZdef]))
      (by rw [hlrdef]; exact mul_le_mul le_rfl hm bot_le bot_le)
  have hteles := chain_telescope (V := V) (X := X) (Z := Z) (ar := ar) (br := br) (lr := lr)
    P hP0 hPsucc harnn hbrnn hlrnn hstep
  -- ## the infinite sum
  set Ssum : ℝ≥0∞ := (∑' i, ENNReal.ofReal (P i * ar i)) * X
    + (∑' i, ENNReal.ofReal (P i * br i)) * Z with hSsumdef
  have hgeom1 : (∑' i : ℕ, ENNReal.ofReal (DA * ((1/2:ℝ))^i)) = ENNReal.ofReal (2 * DA) := by
    have hsumm : Summable (fun i : ℕ => DA * ((1/2:ℝ))^i) :=
      Summable.mul_left DA (summable_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsumm, tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1)]
    congr 1
    ring
  have hgeom2 : (∑' i : ℕ, ENNReal.ofReal (DB * ((1/2:ℝ))^i)) = ENNReal.ofReal (2 * DB) := by
    have hsumm : Summable (fun i : ℕ => DB * ((1/2:ℝ))^i) :=
      Summable.mul_left DB (summable_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsumm, tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1)]
    congr 1
    ring
  have hSA : (∑' i, ENNReal.ofReal (P i * ar i)) ≤ ENNReal.ofReal (2 * DA) := by
    refine (ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hPar i)).trans (le_of_eq hgeom1)
  have hSB : (∑' i, ENNReal.ofReal (P i * br i)) ≤ ENNReal.ofReal (2 * DB) := by
    refine (ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hPbr i)).trans (le_of_eq hgeom2)
  have hSsumle : Ssum ≤ ENNReal.ofReal (2 * DA) * X + ENNReal.ofReal (2 * DB) * Z := by
    rw [hSsumdef]
    exact add_le_add (mul_le_mul hSA le_rfl bot_le bot_le) (mul_le_mul hSB le_rfl bot_le bot_le)
  -- ## the limit
  have hV0 : V 0 ≤ Ssum := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδpos : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
    set xv : ℝ := X.toReal with hxv
    set zv : ℝ := Z.toReal with hzv
    set mv : ℝ := Me.toReal with hmv
    have hxcoe : ENNReal.ofReal xv = X := ENNReal.ofReal_toReal hXtop
    have hzcoe : ENNReal.ofReal zv = Z := ENNReal.ofReal_toReal hZtop
    have hmcoe : ENNReal.ofReal mv = Me := ENNReal.ofReal_toReal (ne_of_lt hMelt)
    have hxv0 : 0 ≤ xv := ENNReal.toReal_nonneg
    have hzv0 : 0 ≤ zv := ENNReal.toReal_nonneg
    have hmv0 : 0 ≤ mv := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N ≤ (δ:ℝ) := by
      have ht : Filter.Tendsto (fun N : ℕ => (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N)
          Filter.atTop (𝓝 0) := by
        have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (1/2:ℝ) < 1)).const_mul (2*DA*xv + 2*DB*zv + mv)
        simpa using h0
      have hlt := (tendsto_order.1 ht).2 (δ:ℝ) hδpos
      rw [Filter.eventually_atTop] at hlt
      obtain ⟨N, hN⟩ := hlt
      exact ⟨N, le_of_lt (hN N le_rfl)⟩
    have hPNV : ENNReal.ofReal (P N) * V N ≤ ENNReal.ofReal (δ:ℝ) := by
      have hlast : V N ≤ ENNReal.ofReal (ar N) * X + ENNReal.ofReal (br N) * Z
          + ENNReal.ofReal (lr N) * Me := by
        have h := onestepSup (A := A) hn hα0 hα1 hρ''0 hρ''ρ hCLpos hKdpos (hL1fpos N)
          (hL2fpos N) (hDpos N) (fun v hv hvc => hloss hAsm (le_trans hε (min_le_left εL 1)) hsmall hJ v hv hvc)
          (hEpos N) (fun j : Fin n => hRe N j) (hχsm N) (hχ1 N) (hχ0 N) (hL1 N) (hL2 N) (hdatai N) hu
        refine h.trans ?_
        have hm : (⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (fun j => Rfun N j + (Efun N + Dfun N)),
            ENNReal.ofReal ‖fderiv ℝ u z‖) ≤ Me := by
          rw [hRsucc N]
          exact hMesM (N+1)
        exact add_le_add (add_le_add (by rw [hardef, hXdef]) (by rw [hbrdef, hZdef]))
          (by rw [hlrdef]; exact mul_le_mul le_rfl hm bot_le bot_le)
      have hPnn' : 0 ≤ P N := by
        have h : P N ≤ 1 := hP1 N
        have h0 : (0:ℝ) ≤ P N := by
          rw [hPdef]
          exact Finset.prod_nonneg fun k _ => hlrnn k
        exact h0
      refine (mul_le_mul le_rfl hlast bot_le bot_le).trans ?_
      rw [mul_add, mul_add]
      have e1 : ENNReal.ofReal (P N) * ENNReal.ofReal (ar N) = ENNReal.ofReal (P N * ar N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have e2 : ENNReal.ofReal (P N) * ENNReal.ofReal (br N) = ENNReal.ofReal (P N * br N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have e3 : ENNReal.ofReal (P N) * ENNReal.ofReal (lr N) = ENNReal.ofReal (P N * lr N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have hassoc : ENNReal.ofReal (P N) * (ENNReal.ofReal (ar N) * X)
            + ENNReal.ofReal (P N) * (ENNReal.ofReal (br N) * Z)
            + ENNReal.ofReal (P N) * (ENNReal.ofReal (lr N) * Me)
          = (ENNReal.ofReal (P N) * ENNReal.ofReal (ar N)) * X
            + (ENNReal.ofReal (P N) * ENNReal.ofReal (br N)) * Z
            + (ENNReal.ofReal (P N) * ENNReal.ofReal (lr N)) * Me := by ring
      rw [hassoc, e1, e2, e3]
      have hxr : ENNReal.ofReal (P N * ar N) * X ≤ ENNReal.ofReal (DA * ((1/2:ℝ))^N) * X :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hPar N)) bot_le
      have hzr : ENNReal.ofReal (P N * br N) * Z ≤ ENNReal.ofReal (DB * ((1/2:ℝ))^N) * Z :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hPbr N)) bot_le
      have hmr : ENNReal.ofReal (P N * lr N) * Me ≤ ENNReal.ofReal (((1/2:ℝ))^N) * Me := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        calc P N * lr N ≤ 1 * ((1/2:ℝ))^N :=
              mul_le_mul (hP1 N) (hlrb N) (hlrnn N) (by norm_num)
          _ = ((1/2:ℝ))^N := one_mul _
      refine (add_le_add (add_le_add hxr hzr) hmr).trans ?_
      -- rewrite in terms of xv, zv, mv
      rw [← hxcoe, ← hzcoe, ← hmcoe]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ DA * ((1/2:ℝ))^N),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ DB * ((1/2:ℝ))^N),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((1/2:ℝ))^N),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h8 : DA * ((1/2:ℝ))^N * xv + DB * ((1/2:ℝ))^N * zv + ((1/2:ℝ))^N * mv
          ≤ (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N := by
        have hNn : (0:ℝ) ≤ ((1/2:ℝ))^N := by positivity
        have h1 : DA * ((1/2:ℝ))^N * xv ≤ (2*DA*xv) * ((1/2:ℝ))^N := by
          have h0 : (0:ℝ) ≤ DA * xv * ((1/2:ℝ))^N := mul_nonneg (mul_nonneg hDA0 hxv0) hNn
          have e1 : DA * ((1/2:ℝ))^N * xv = DA * xv * ((1/2:ℝ))^N := by ring
          have e2 : (2*DA*xv) * ((1/2:ℝ))^N = 2 * (DA * xv * ((1/2:ℝ))^N) := by ring
          linarith
        have h2 : DB * ((1/2:ℝ))^N * zv ≤ (2*DB*zv) * ((1/2:ℝ))^N := by
          have h0 : (0:ℝ) ≤ DB * zv * ((1/2:ℝ))^N := mul_nonneg (mul_nonneg hDB0 hzv0) hNn
          have e1 : DB * ((1/2:ℝ))^N * zv = DB * zv * ((1/2:ℝ))^N := by ring
          have e2 : (2*DB*zv) * ((1/2:ℝ))^N = 2 * (DB * zv * ((1/2:ℝ))^N) := by ring
          linarith
        have h3 : ((1/2:ℝ))^N * mv ≤ mv * ((1/2:ℝ))^N := le_of_eq (mul_comm _ _)
        linarith [h1, h2, h3]
      linarith [hN, h8]
    have hpart : (∑ i ∈ Finset.range N, ENNReal.ofReal (P i) *
        (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z)) ≤ Ssum := by
      rw [hSsumdef]
      have hsplit : (∑ i ∈ Finset.range N, ENNReal.ofReal (P i) *
          (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z))
          = (∑ i ∈ Finset.range N, ENNReal.ofReal (P i * ar i)) * X
            + (∑ i ∈ Finset.range N, ENNReal.ofReal (P i * br i)) * Z := by
        have h1 : ∀ i, ENNReal.ofReal (P i) *
            (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z)
            = ENNReal.ofReal (P i * ar i) * X + ENNReal.ofReal (P i * br i) * Z := by
          intro i
          rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (hPnn' i),
            ← ENNReal.ofReal_mul (hPnn' i)]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsplit]
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact (ENNReal.sum_le_tsum _).trans le_rfl
      · refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact (ENNReal.sum_le_tsum _).trans le_rfl
    refine (hteles N).trans (add_le_add hpart ?_)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hPNV
  -- ## conclusion
  have hV0eq : V 0 = Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ') := by
    have hR0 : Rfun 0 = ρ' := by
      funext j
      simp only [hRfundef, Finset.range_zero, Finset.sum_empty, add_zero]
    simp only [hVdef]
    rw [hR0]
  have hfin : ENNReal.ofReal (2*DA) * X + ENNReal.ofReal (2*DB) * Z
      ≤ ENNReal.ofReal Cfin * (X + Z) := by
    have h1 : ENNReal.ofReal (2*DA) ≤ ENNReal.ofReal Cfin := by
      rw [hCfindef]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have h2 : ENNReal.ofReal (2*DB) ≤ ENNReal.ofReal Cfin := by
      rw [hCfindef]; exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal (2*DA) * X + ENNReal.ofReal (2*DB) * Z
        ≤ ENNReal.ofReal Cfin * X + ENNReal.ofReal Cfin * Z :=
          add_le_add (mul_le_mul h1 le_rfl bot_le bot_le) (mul_le_mul h2 le_rfl bot_le bot_le)
      _ = ENNReal.ofReal Cfin * (X + Z) := by rw [mul_add]
  exact hV0eq ▸ (hV0.trans (hSsumle.trans hfin))

end

end Work.NN.Core.Lev
