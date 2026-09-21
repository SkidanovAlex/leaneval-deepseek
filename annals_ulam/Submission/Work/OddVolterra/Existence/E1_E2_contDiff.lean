import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Smooth.Slice
import Submission.Work.OddVolterra.Smooth.ParametricIntegral

namespace Work.OddVolterra.Existence

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam

noncomputable section

/-! ## The polynomial model of the radicand, and the positivity region -/

/-- The polynomial model `1 - t ^ 2 - (s * t + h s) ^ 2` of the radicand `psi`. -/
def psiPoly (h : ℝ → ℝ) (s t : ℝ) : ℝ := 1 - t ^ 2 - (s * t + h s) ^ 2

lemma psiPoly_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => psiPoly h p.1 p.2) := by
  unfold psiPoly
  fun_prop

/-- The open set of parameters on which the radicand `psi h semicircle` is positive. -/
def psiPos (h : ℝ → ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < psi h semicircle p.1 p.2}

lemma isOpen_psiPos {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) : IsOpen (psiPos h) := by
  have hcont : Continuous fun p : ℝ × ℝ => psi h semicircle p.1 p.2 := by
    unfold psi Work.OddVolterra.line Commons.Geometry.Ulam.semicircle
    fun_prop
  exact isOpen_lt continuous_const hcont

/-- If `psi` is positive at `(u, t)`, then `|t| < 1`. -/
lemma abs_lt_one_of_psi_pos {h : ℝ → ℝ} {u t : ℝ} (hpos : 0 < psi h semicircle u t) :
    |t| < 1 := by
  have hpsi : psi h semicircle u t =
      (Real.sqrt (1 - t ^ 2)) ^ 2 - (u * t + h u) ^ 2 := by
    unfold psi Work.OddVolterra.line Commons.Geometry.Ulam.semicircle
    ring
  rw [hpsi] at hpos
  have h1 : 0 < (Real.sqrt (1 - t ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (u * t + h u)]
  have h2 : 0 < 1 - t ^ 2 := by
    by_contra hc
    have hz : Real.sqrt (1 - t ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [hz] at h1
    norm_num at h1
  have : t ^ 2 < 1 := by linarith
  exact (sq_lt_one_iff_abs_lt_one t).mp this

/-- Where `psi h semicircle` is positive it agrees with the polynomial model `psiPoly`. -/
lemma psi_eq_psiPoly_of_pos {h : ℝ → ℝ} {u t : ℝ} (hpos : 0 < psi h semicircle u t) :
    psi h semicircle u t = psiPoly h u t := by
  have ht : |t| < 1 := abs_lt_one_of_psi_pos hpos
  have h1 : 0 ≤ 1 - t ^ 2 := by
    have : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).mpr ht
    linarith
  unfold psi psiPoly Work.OddVolterra.line Commons.Geometry.Ulam.semicircle
  rw [Real.sq_sqrt h1]

/-! ## Smoothness on the positivity region -/

lemma contDiffOn_psi_semicircle {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => psi h semicircle p.1 p.2) (psiPos h) := by
  have hpoly : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => psiPoly h p.1 p.2) (psiPos h) :=
    (psiPoly_contDiff hh).contDiffOn.mono (subset_univ _)
  exact hpoly.congr (fun p _ => psi_eq_psiPoly_of_pos ‹0 < psi h semicircle p.1 p.2›)

lemma contDiffOn_pow_sqrt (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ n * Real.sqrt x) (Ioi 0) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ n) (Ioi 0) := by fun_prop
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) Real.sqrt (Ioi 0) := by
    simpa using (contDiffOn_id.sqrt (s := Ioi 0) (fun x hx => ne_of_gt hx))
  exact h1.mul h2

/-- The `n`-th power of the radicand times its square root, as a function of the plane. -/
def PhiF (n : ℕ) (h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => psi h semicircle p.1 p.2 ^ n * Real.sqrt (psi h semicircle p.1 p.2)

/-- The second moment integrand of the plane, as a function of the plane. -/
def PhiH (n : ℕ) (h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => psi h semicircle p.1 p.2 ^ (n - 1) * Real.sqrt (psi h semicircle p.1 p.2)
    * Work.OddVolterra.lineSlope h p.1 p.2

lemma contDiffOn_PhiF {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (PhiF n h) (psiPos h) := by
  have hcomp := (contDiffOn_pow_sqrt n).comp (contDiffOn_psi_semicircle hh)
    (fun p hp => hp)
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p : ℝ × ℝ => psi h semicircle p.1 p.2 ^ n * Real.sqrt (psi h semicircle p.1 p.2))
    (psiPos h)
  exact hcomp

lemma contDiff_lineSlope {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.lineSlope h p.1 p.2) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    rw [← contDiffOn_univ]
    exact hh.contDiffOn.deriv_of_isOpen isOpen_univ
      Work.OddVolterra.Smooth.top_coe_add_one_le
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => deriv h p.1) := by
    simpa [Function.comp_def] using hd.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => p.2 + deriv h p.1) := h2.add h1
  simpa [Work.OddVolterra.lineSlope] using h3

lemma contDiffOn_PhiH {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (PhiH n h) (psiPos h) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => psi h semicircle p.1 p.2 ^ (n - 1)
        * Real.sqrt (psi h semicircle p.1 p.2)) (psiPos h) := by
    have hcomp := (contDiffOn_pow_sqrt (n - 1)).comp (contDiffOn_psi_semicircle hh)
      (fun p hp => hp)
    simpa [Function.comp_def] using hcomp
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.lineSlope h p.1 p.2)
      (psiPos h) := (contDiff_lineSlope hh).contDiffOn.mono (subset_univ _)
  have h3 := h1.mul h2
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p : ℝ × ℝ => psi h semicircle p.1 p.2 ^ (n - 1) * Real.sqrt (psi h semicircle p.1 p.2)
      * Work.OddVolterra.lineSlope h p.1 p.2) (psiPos h)
  exact h3

/-! ## Parametric integrals of iterated slice derivatives -/

/-- The parametric interval integral of the `k`-th iterated derivative of the slices of a
`C^∞` function is `C^∞` at `s₀`, as long as the vertical segment sits in the domain. -/
lemma contDiffAt_integral_iteratedDeriv {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) {c d s₀ : ℝ} (k : ℕ)
    (hseg : ∀ t ∈ Set.uIcc c d, (s₀, t) ∈ W) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s => ∫ t in c..d, iteratedDeriv k (fun u : ℝ => F (u, t)) s) s₀ := by
  have hK : IsCompact ({s₀} ×ˢ Set.uIcc c d : Set (ℝ × ℝ)) :=
    isCompact_singleton.prod isCompact_uIcc
  have hKW : ({s₀} ×ˢ Set.uIcc c d : Set (ℝ × ℝ)) ⊆ W := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hseg t ht
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hW hKW
  have tube : ∀ s : ℝ, |s - s₀| < δ → ∀ t ∈ Set.uIcc c d, (s, t) ∈ W := by
    intro s hs t ht
    refine hδ (Metric.thickening_subset_cthickening δ _ ?_)
    rw [Metric.mem_thickening_iff]
    refine ⟨(s₀, t), ⟨by simp, ht⟩, ?_⟩
    have hdist : dist (s, t) (s₀, t) = |s - s₀| := by
      rw [Prod.dist_eq]
      dsimp only
      rw [dist_self, max_eq_left dist_nonneg, Real.dist_eq]
    rw [hdist]
    exact hs
  have hmain := Work.OddVolterra.Smooth.Alt.contDiffAt_integral_of_contDiffOn hW
    (Work.OddVolterra.Smooth.contDiffOn_pderiv1Iter hW hF k) hseg
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds s₀ hδpos] with s hs
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  exact Work.OddVolterra.Smooth.iteratedDeriv_eq_pderiv1Iter hW hF
    (tube s (by simpa [Real.dist_eq] using hs) t ht) k

/-! ## The two inhomogeneities are `C^∞` on `(0, 1)` -/

theorem E1_E2_contDiff (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hpsi : ∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle u t) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Work.OddVolterra.E1 n h s) (Set.Ioo (0:ℝ) 1) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Work.OddVolterra.E2 n h s) (Set.Ioo (0:ℝ) 1) := by
  have hle : -(Commons.Geometry.Ulam.profileX 1) ≤ Commons.Geometry.Ulam.profileX 1 := by
    have := Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
    linarith
  have hseg : ∀ s₀ ∈ Set.Ioo (0:ℝ) 1,
      ∀ t ∈ Set.uIcc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
        (s₀, t) ∈ psiPos h := by
    intro s₀ hs₀ t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hpsi s₀ hs₀ t ht
  constructor
  · intro s₀ hs₀
    have := contDiffAt_integral_iteratedDeriv (isOpen_psiPos hh) (contDiffOn_PhiF hh n)
      (n + 1) (hseg s₀ hs₀)
    exact this.contDiffWithinAt
  · intro s₀ hs₀
    have := contDiffAt_integral_iteratedDeriv (isOpen_psiPos hh) (contDiffOn_PhiH hh n)
      n (hseg s₀ hs₀)
    exact this.contDiffWithinAt

end

end Work.OddVolterra.Existence
