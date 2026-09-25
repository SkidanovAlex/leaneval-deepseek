import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmRhs_tendsto_eps
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmPotential_holderNorm_le
import Submission.Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- A compactly supported function vanishes off a ball (in the sup-norm). -/
lemma exists_radius_sup {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0 := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max r 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hx0
  have hmem : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hx0)
  have h1 : ‖x‖ ≤ r := by
    have h := hr hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have h2 : r ≤ max r 0 := le_max_left _ _
  linarith

/-- **Decay of the Bochner–Martinelli potential.**  If the data `h j` are continuous with compact
support (vanishing off the sup-norm ball of radius `R`), then outside the ball of radius `2R` the
potential is bounded by `C ‖z‖^{1-2n}`. -/
lemma norm_bmPot_le_of_large {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hc : ∀ j, Continuous (h j)) (hcs : ∀ j, HasCompactSupport (h j))
    (hsupp : ∀ j, ∀ x : Fin n → ℂ, R ≤ ‖x‖ → h j x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin n → ℂ, 2 * R ≤ ‖z‖ →
      ‖bmPot h z‖ ≤ C * ‖z‖ ^ (1 - 2 * (n : ℝ)) := by
  have hint : ∀ j, Integrable (h j) volume := fun j =>
    (hc j).integrable_of_hasCompactSupport (hcs j)
  set A : ℝ := ∑ j, ∫ x, ‖h j x‖ with hA
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  refine ⟨A * 2 ^ (2 * (n : ℝ) - 1), by positivity, fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := by linarith
  have hz2 : 0 < ‖z‖ - R := by linarith
  have hexp : (1 : ℝ) - 2 * (n : ℝ) < 0 := by
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  -- pointwise bound on the kernel on the support of the translate
  have hker : ∀ j x, h j (z + x) ≠ 0 → ‖bmKernel j x‖ ≤ (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) := by
    intro j x hx
    have h1 : ‖z + x‖ < R := by
      by_contra hcon
      exact hx (hsupp j (z + x) (not_lt.mp hcon))
    have h2 : ‖z‖ - R ≤ ‖x‖ := by
      have hle : ‖z‖ ≤ ‖z + x‖ + ‖x‖ := by
        have := norm_add_le (z + x) (-x)
        simpa using this
      linarith
    refine le_trans (norm_bmKernel_le j x) ?_
    exact Real.rpow_le_rpow_of_nonpos hz2 h2 (le_of_lt hexp)
  have hbd : ∀ j, ‖∫ x, bmKernel j x * h j (z + x)‖ ≤
      (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * ∫ x, ‖h j x‖ := by
    intro j
    have hshift : ∫ x, ‖h j (z + x)‖ = ∫ x, ‖h j x‖ := by
      have h := MeasureTheory.integral_add_right_eq_self (μ := volume)
        (fun x : Fin n → ℂ => ‖h j x‖) z
      simpa [Function.comp_def, add_comm] using h
    have hInt : Integrable (fun x : Fin n → ℂ => ‖h j (z + x)‖) volume :=
      (((hc j).comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
        ((hcs j).comp_homeomorph (Homeomorph.addLeft z))).norm
    calc ‖∫ x, bmKernel j x * h j (z + x)‖
        ≤ ∫ x, ‖bmKernel j x * h j (z + x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖bmKernel j x‖ * ‖h j (z + x)‖ := by simp_rw [norm_mul]
      _ ≤ ∫ x, (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * ‖h j (z + x)‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            (hInt.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : h j (z + x) = 0
          · simp [hx]
          · exact mul_le_mul_of_nonneg_right (hker j x hx) (norm_nonneg _)
      _ = (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * ∫ x, ‖h j x‖ := by
          rw [MeasureTheory.integral_const_mul, hshift]
  have hsum : ‖bmPot h z‖ ≤ (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * A := by
    rw [bmPot, hA]
    calc ‖∑ j, ∫ x, bmKernel j x * h j (z + x)‖
        ≤ ∑ j, ‖∫ x, bmKernel j x * h j (z + x)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * ∫ x, ‖h j x‖ :=
          Finset.sum_le_sum fun j _ => hbd j
      _ = (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * ∑ j, ∫ x, ‖h j x‖ := by rw [Finset.mul_sum]
  refine le_trans hsum ?_
  have h3 : (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) ≤
      2 ^ (2 * (n : ℝ) - 1) * ‖z‖ ^ (1 - 2 * (n : ℝ)) := by
    have hhalf : ‖z‖ / 2 ≤ ‖z‖ - R := by linarith
    have h1 : (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) ≤ (‖z‖ / 2) ^ (1 - 2 * (n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (le_of_lt hexp)
    have h4 : (‖z‖ / 2) ^ (1 - 2 * (n : ℝ)) =
        2 ^ (2 * (n : ℝ) - 1) * ‖z‖ ^ (1 - 2 * (n : ℝ)) := by
      rw [Real.div_rpow (le_of_lt hzpos) (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [h4] at h1
    exact h1
  calc (‖z‖ - R) ^ (1 - 2 * (n : ℝ)) * A
      ≤ (2 ^ (2 * (n : ℝ) - 1) * ‖z‖ ^ (1 - 2 * (n : ℝ))) * A :=
        mul_le_mul_of_nonneg_right h3 hAnn
    _ = A * 2 ^ (2 * (n : ℝ) - 1) * ‖z‖ ^ (1 - 2 * (n : ℝ)) := by ring


/-- The `∂̄`-derivative of a function with compact support has compact support. -/
lemma hasCompactSupport_dbarCoordAux {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hc : HasCompactSupport f)
    (k : Fin n) : HasCompactSupport (fun y => Work.CR.Flat.dbarCoord k f y) := by
  have h1 : (fun y => fderiv ℝ f y (Pi.single k (1 : ℂ)))
      = (fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k (1 : ℂ))) ∘ (fderiv ℝ f) := rfl
  have h2 : (fun y => fderiv ℝ f y (Pi.single k Complex.I))
      = (fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k Complex.I)) ∘ (fderiv ℝ f) := rfl
  have hc1 : HasCompactSupport (fun y => fderiv ℝ f y (Pi.single k (1 : ℂ))) := by
    rw [h1]; exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)
  have hc2 : HasCompactSupport (fun y => fderiv ℝ f y (Pi.single k Complex.I)) := by
    rw [h2]; exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)
  have h3 : (fun y => Work.CR.Flat.dbarCoord k f y)
      = fun y => (1 / 2 : ℂ) * ((fun y => fderiv ℝ f y (Pi.single k (1 : ℂ))) y
          + Complex.I * (fun y => fderiv ℝ f y (Pi.single k Complex.I)) y) := by
    funext y; rfl
  rw [h3]
  exact (hc1.add (hc2.mul_left (f := fun _ : Fin n → ℂ => Complex.I))).mul_left
    (f := fun _ : Fin n → ℂ => (1 / 2 : ℂ))

/-- `flatLap` is invariant under translations. -/
lemma flatLap_comp_add' {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z x : Fin n → ℂ) :
    flatLap (fun y => f (z + y)) x = flatLap f (z + x) := by
  rw [flatLap_apply, flatLap_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (fun y => Work.CR.Flat.dbarCoord k (fun y => f (z + y)) y)
      = fun y => Work.CR.Flat.dbarCoord k f (z + y) :=
    Work.CR.Flat.Cauchy.dbarCoord_comp_add' k f z
  rw [h1]
  exact congrFun (Work.CR.Flat.Cauchy.dCoord_comp_add k (fun y => Work.CR.Flat.dbarCoord k f y) z) x

/-- The `∂̄`-derivative of a `C²` function is `C¹`. -/
lemma contDiff_one_dbarCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 2 g) (k : Fin n) :
    ContDiff ℝ 1 (fun y => Work.CR.Flat.dbarCoord k g y) := by
  have hfd : ContDiff ℝ 1 (fun y => fderiv ℝ g y) := hg.fderiv_right (m := 1) (by norm_num)
  have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single k (1 : ℂ))) :=
    ContDiff.clm_apply hfd contDiff_const
  have h2 : ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single k Complex.I)) :=
    ContDiff.clm_apply hfd contDiff_const
  have h3 : (fun y => Work.CR.Flat.dbarCoord k g y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ g y (Pi.single k (1 : ℂ))
          + Complex.I * fderiv ℝ g y (Pi.single k Complex.I)) := by
    funext y; rfl
  rw [h3]
  exact (h1.add (contDiff_const.mul h2)).const_smul (1 / 2 : ℂ)

/-- A function vanishing near a point has vanishing `∂̄`-derivative there. -/
lemma dbarCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (h : g =ᶠ[nhds x] 0) (k : Fin n) : Work.CR.Flat.dbarCoord k g x = 0 := by
  have hfd : fderiv ℝ g x = 0 := by rw [h.fderiv_eq]; simp
  rw [Work.CR.Flat.dbarCoord, hfd]
  simp

/-- The `∂`-derivative of a function with compact support has compact support. -/
lemma hasCompactSupport_dCoord {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hc : HasCompactSupport f)
    (k : Fin n) : HasCompactSupport (fun y => Work.CR.Flat.dCoord k f y) := by
  have h1 : (fun y => fderiv ℝ f y (Pi.single k (1 : ℂ)))
      = (fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k (1 : ℂ))) ∘ (fderiv ℝ f) := rfl
  have h2 : (fun y => fderiv ℝ f y (Pi.single k Complex.I))
      = (fun L : (Fin n → ℂ) →L[ℝ] ℂ => L (Pi.single k Complex.I)) ∘ (fderiv ℝ f) := rfl
  have hc1 : HasCompactSupport (fun y => fderiv ℝ f y (Pi.single k (1 : ℂ))) := by
    rw [h1]; exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)
  have hc2 : HasCompactSupport (fun y => fderiv ℝ f y (Pi.single k Complex.I)) := by
    rw [h2]; exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)
  have h3 : (fun y => Work.CR.Flat.dCoord k f y)
      = fun y => (1 / 2 : ℂ) * ((fun y => fderiv ℝ f y (Pi.single k (1 : ℂ))) y
          - Complex.I * (fun y => fderiv ℝ f y (Pi.single k Complex.I)) y) := by
    funext y; rfl
  rw [h3]
  exact (hc1.sub (hc2.mul_left (f := fun _ : Fin n → ℂ => Complex.I))).mul_left
    (f := fun _ : Fin n → ℂ => (1 / 2 : ℂ))

/-- The `∂`-derivative of a `C¹` function is continuous. -/
lemma continuous_dCoord_of_contDiff_one {n : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (k : Fin n) : Continuous (fun y => Work.CR.Flat.dCoord k g y) := by
  have hfd : Continuous (fun y => fderiv ℝ g y) := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun y => fderiv ℝ g y (Pi.single k (1 : ℂ))) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun y => fderiv ℝ g y (Pi.single k Complex.I)) :=
    hfd.clm_apply continuous_const
  have h3 : (fun y => Work.CR.Flat.dCoord k g y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ g y (Pi.single k (1 : ℂ))
          - Complex.I * fderiv ℝ g y (Pi.single k Complex.I)) := by
    funext y; rfl
  rw [h3]
  exact (h1.sub (continuous_const.mul h2)).const_mul (1 / 2 : ℂ)

/-- Integrability of `bmKernel j` against a translate of a continuous compactly supported
function. -/
lemma integrable_bmKernel_mul_comp {n : ℕ} (hn : 0 < n) (j : Fin n) {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : Fin n → ℂ) :
    Integrable (fun x : Fin n → ℂ => bmKernel j x * g (z + x)) :=
  Work.CR.Flat.Cauchy.integrable_bmKernel_mul hn j
    (hg.comp (continuous_const.add continuous_id))
    (hgc.comp_homeomorph (Homeomorph.addLeft z))

/-- **`Δ (bmPot h) = 4 γ div h`.**  For `C²` compactly supported data, the flat Laplacian of the
Bochner–Martinelli potential is `4 bmGamma n` times the divergence of the data.  The kernel
identity `hcrux` (the statement `Δ bmKernel j = 4 bmGamma n ∂_j δ`) is the only input. -/
lemma flatLap_bmPot_eq {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ j, ContDiff ℝ 2 (h j)) (hcs : ∀ j, HasCompactSupport (h j))
    (hcrux : ∀ (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ 2 ψ → HasCompactSupport ψ → ∀ j : Fin n,
      ∫ x, bmKernel j x * flatLap ψ x = 4 * bmGamma n * Work.CR.Flat.dCoord j ψ 0)
    (z : Fin n → ℂ) :
    flatLap (fun w => bmPot h w) z
      = 4 * bmGamma n * ∑ j : Fin n, Work.CR.Flat.dCoord j (h j) z := by
  choose Rj hRj using fun j => exists_radius_sup (hcs j)
  set R : ℝ := (∑ j : Fin n, Rj j) + 1 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have hsum : 0 < ∑ j : Fin n, Rj j :=
      Finset.sum_pos (fun j _ => (hRj j).1) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    linarith
  have hle : ∀ j : Fin n, Rj j ≤ R := by
    intro j
    have h := Finset.single_le_sum (fun i _ => le_of_lt (hRj i).1) (Finset.mem_univ j)
    rw [hRdef]; linarith
  have hR : ∀ j x, R ≤ ‖x‖ → h j x = 0 := fun j x hx => (hRj j).2 x (le_trans (hle j) hx)
  have hRder : ∀ j x, R ≤ ‖x‖ → ∀ k, Work.CR.Flat.dbarCoord k (h j) x = 0 := by
    intro j x hx k
    refine dbarCoord_eq_zero_of_eventuallyEq_zero ?_ k
    have hltR : Rj j < R := by
      have hle2 : Rj j ≤ ∑ i : Fin n, Rj i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hRj i).1) (Finset.mem_univ j)
      rw [hRdef]; linarith
    have hlt : Rj j < ‖x‖ := lt_of_lt_of_le hltR hx
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hlt] with y hy
    exact (hRj j).2 y (le_of_lt hy)
  -- Step 1: the `∂̄_k`-derivative of the potential is the potential of the `∂̄_k`-family
  have hdbar : ∀ k, (fun w => Work.CR.Flat.dbarCoord k (fun w => bmPot h w) w)
      = bmPot (fun j y => Work.CR.Flat.dbarCoord k (h j) y) := by
    intro k
    funext w
    have h1 := Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (fun j => (hh j).of_le (by norm_num))
      hRpos hR k w
    simp only [bmPot] at h1 ⊢
    exact h1
  -- Step 2: differentiate under the integral sign
  have hderiv : ∀ k, Work.CR.Flat.dCoord k
        (fun w => bmPot (fun j y => Work.CR.Flat.dbarCoord k (h j) y) w) z
      = ∑ j, ∫ x, bmKernel j x *
          Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x) := by
    intro k
    exact Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord hn (fun j => contDiff_one_dbarCoord (hh j) k)
      hRpos (fun j x hx => hRder j x hx k) k z
  -- Step 3: assemble
  have hmain : flatLap (fun w => bmPot h w) z
      = ∑ j : Fin n, ∫ x, bmKernel j x * flatLap (fun y => h j (z + y)) x := by
    rw [flatLap_apply]
    have h1 : ∀ k : Fin n, Work.CR.Flat.dCoord k
          (fun w => Work.CR.Flat.dbarCoord k (fun w => bmPot h w) w) z
        = ∑ j, ∫ x, bmKernel j x *
            Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x) := by
      intro k
      rw [hdbar k]
      exact hderiv k
    simp only [h1]
    -- pull the `k`-sum inside the integral, for each `j`
    have h2 : ∀ j : Fin n, (∑ k : Fin n, ∫ x, bmKernel j x *
          Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x))
        = ∫ x, bmKernel j x * (∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x)) := by
      intro j
      rw [← MeasureTheory.integral_finsetSum]
      · congr 1
        funext x
        rw [Finset.mul_sum]
      · intro k _
        exact integrable_bmKernel_mul_comp hn j
          (continuous_dCoord_of_contDiff_one (contDiff_one_dbarCoord (hh j) k) k)
            (hasCompactSupport_dCoord (hasCompactSupport_dbarCoordAux (hcs j) k) k) z
    have h3 : ∀ j : Fin n, ∫ x, bmKernel j x * (∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x))
        = (1 / 4) * ∫ x, bmKernel j x * flatLap (fun y => h j (z + y)) x := by
      intro j
      have hpt : ∀ x : Fin n → ℂ, (∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x))
          = (1 / 4) * flatLap (fun y => h j (z + y)) x := by
        intro x
        rw [flatLap_comp_add', flatLap_apply]
        ring
      rw [show (fun x : Fin n → ℂ => bmKernel j x * (∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x)))
          = fun x => (1 / 4) * (bmKernel j x * flatLap (fun y => h j (z + y)) x) from by
        funext x; rw [hpt x]; ring]
      rw [MeasureTheory.integral_const_mul]
    calc 4 * ∑ k : Fin n, ∑ j : Fin n, ∫ x, bmKernel j x *
            Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x)
        = 4 * ∑ j : Fin n, ∑ k : Fin n, ∫ x, bmKernel j x *
            Work.CR.Flat.dCoord k (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x) := by
          rw [Finset.sum_comm]
      _ = 4 * ∑ j : Fin n, ∫ x, bmKernel j x * (∑ k : Fin n, Work.CR.Flat.dCoord k
            (fun y => Work.CR.Flat.dbarCoord k (h j) y) (z + x)) := by
          rw [Finset.sum_congr rfl fun j _ => h2 j]
      _ = 4 * ∑ j : Fin n, (1 / 4) * ∫ x, bmKernel j x * flatLap (fun y => h j (z + y)) x := by
          rw [Finset.sum_congr rfl fun j _ => h3 j]
      _ = ∑ j : Fin n, ∫ x, bmKernel j x * flatLap (fun y => h j (z + y)) x := by
          rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => by ring)]
  -- Step 4: apply the kernel identity
  have hcrux' : ∀ j : Fin n, ∫ x, bmKernel j x * flatLap (fun y => h j (z + y)) x
      = 4 * bmGamma n * Work.CR.Flat.dCoord j (h j) z := by
    intro j
    have hcsj : HasCompactSupport (fun y => h j (z + y)) :=
      (hcs j).comp_homeomorph (Homeomorph.addLeft z)
    have hcj : ContDiff ℝ 2 (fun y => h j (z + y)) :=
      (hh j).comp (contDiff_const.add contDiff_id)
    have h0 := hcrux (fun y => h j (z + y)) hcj hcsj j
    have h0z : Work.CR.Flat.dCoord j (fun y => h j (z + y)) 0 = Work.CR.Flat.dCoord j (h j) z := by
      have := congrFun (Work.CR.Flat.Cauchy.dCoord_comp_add j (h j) z) 0
      simpa using this
    rw [h0z] at h0
    exact h0
  rw [hmain, Finset.sum_congr rfl fun j _ => hcrux' j, Finset.mul_sum]

end Work.NN.Core

