/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `∂̄χ · ζ` in the `C^{k,α}` scale

The Bochner–Martinelli step uses the defect `bmH χ ζ j k l = ∂̄_l χ · ζ_{jk} + ∂̄_j χ · ζ_{kl}
- ∂̄_k χ · ζ_{jl}`: an *algebraic* expression in the cut-off `χ` and the form `ζ`.  This file
establishes the `C^{k,α}` estimate for it that the Schauder iteration needs
(`Work.NN.Core.holderNorm_bmH_le`): for a smooth `χ` vanishing off the open polydisc
`polydisc 0 ρ` one has, for all `j m l`,

  `‖bmH χ ζ j m l‖_{C^{k,α}(ℂⁿ)} ≤ C · Σ_{i,l} ‖ζ_{il}‖_{C^{k,α}(polydisc 0 ρ)}`.

The only delicate point is that the norm on the left is taken over *all* of `ℂⁿ`, while `ζ` is
only controlled on the polydisc.  Since `∂̄χ` is `C^∞` and supported in the (closed) polydisc,
the product `∂̄χ · ζ` is `C^∞` *and flat* on the closed complement of the polydisc; the whole
estimate follows from that flatness together with the Leibniz rule on the polydisc.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.CnPert

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Filter
open Work.CR.Flat

namespace Work.NN.Core

variable {n : ℕ}

/-! ## The geometry of the closed exterior of a polydisc -/

/-- The closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc `polydisc 0 ρ` (for positive
radii) is the closure of the *open* exterior `{z | ∃ j, ρ j < ‖z j‖}`. -/
lemma closure_setOf_lt_norm_polydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    closure {z : Work.NN.Core.Cn n | ∃ j, ρ j < ‖z j‖}
      = {z : Work.NN.Core.Cn n | ∃ j, ρ j ≤ ‖z j‖} := by
  apply Subset.antisymm
  · refine closure_minimal ?_ ?_
    · rintro z ⟨j, hj⟩; exact ⟨j, le_of_lt hj⟩
    · rw [show {z : Work.NN.Core.Cn n | ∃ j, ρ j ≤ ‖z j‖}
            = ⋃ j, {z : Work.NN.Core.Cn n | ρ j ≤ ‖z j‖} from by ext z; simp]
      exact isClosed_iUnion_of_finite fun j =>
        isClosed_le continuous_const ((continuous_apply j).norm)
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := hz
    have hzj : 0 < ‖z j‖ := lt_of_lt_of_le (hρ j) hj
    have hδpos : 0 < ε / (‖z j‖ + 1) := div_pos hε (by positivity)
    refine ⟨Function.update z j ((1 + ε / (‖z j‖ + 1)) • z j), ⟨j, ?_⟩, ?_⟩
    · rw [Function.update_self, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < 1 + ε / (‖z j‖ + 1))]
      have h2 : 0 < (ε / (‖z j‖ + 1)) * ‖z j‖ := mul_pos hδpos hzj
      have h1 : (1 + ε / (‖z j‖ + 1)) * ‖z j‖ = ‖z j‖ + (ε / (‖z j‖ + 1)) * ‖z j‖ := by ring
      linarith [hρ j, hj, h2, h1]
    · rw [dist_eq_norm, show z - Function.update z j ((1 + ε / (‖z j‖ + 1)) • z j)
          = Pi.single j (z j - (1 + ε / (‖z j‖ + 1)) • z j) from by
        ext i
        by_cases hi : i = j
        · subst hi; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne hi, Function.update_of_ne hi],
        Pi.norm_single]
      have he : z j - (1 + ε / (‖z j‖ + 1)) • z j = -(ε / (‖z j‖ + 1)) • z j := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      have hlt : ‖z j‖ / (‖z j‖ + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      calc ε / (‖z j‖ + 1) * ‖z j‖ = ε * (‖z j‖ / (‖z j‖ + 1)) := by field_simp
        _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
        _ = ε := mul_one ε

/-- If `z` is not in the open polydisc `polydisc 0 ρ` then some coordinate of `z` is at least
the corresponding radius. -/
lemma not_mem_polydisc_exists {ρ : Fin n → ℝ} {z : Work.NN.Core.Cn n}
    (hz : z ∉ polydisc 0 ρ) : ∃ j, ρ j ≤ ‖z j‖ := by
  by_contra hcon
  simp only [not_exists] at hcon
  exact hz (by rw [mem_polydisc]; exact fun j => lt_of_not_ge (by simpa using hcon j))

/-! ## Flatness of a smooth function supported in a polydisc -/

/-- A smooth function vanishing on the closed exterior of the open polydisc `polydisc 0 ρ` is
*flat* there: all of its iterated derivatives vanish. -/
lemma iteratedFDeriv_eq_zero_of_vanishing_closedPolydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiff ℝ ⊤ u)
    (hu0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → u z = 0) (p : ℕ) :
    ∀ z, (∃ j, ρ j ≤ ‖z j‖) → iteratedFDeriv ℝ p u z = 0 := by
  have hzero : ∀ z, (∃ j, ρ j < ‖z j‖) → iteratedFDeriv ℝ p u z = 0 := by
    intro z hz
    obtain ⟨j, hj⟩ := hz
    have hopen : IsOpen {w : Work.NN.Core.Cn n | ρ j < ‖w j‖} :=
      isOpen_lt continuous_const ((continuous_apply j).norm)
    have h0 : u =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hj] with w hw
      exact hu0 w ⟨j, le_of_lt hw⟩
    have h1 : iteratedFDeriv ℝ p u =ᶠ[nhds z] iteratedFDeriv ℝ p (fun _ => (0 : ℂ)) :=
      h0.iteratedFDeriv ℝ p
    simpa using h1.eq_of_nhds
  intro z hz
  have hcont : Continuous (iteratedFDeriv ℝ p u) :=
    hu.continuous_iteratedFDeriv (m := p) le_top
  have hsub : {w : Work.NN.Core.Cn n | ∃ j, ρ j < ‖w j‖}
      ⊆ {w : Work.NN.Core.Cn n | iteratedFDeriv ℝ p u w = 0} := fun w hw => hzero w hw
  have hclosed : IsClosed {w : Work.NN.Core.Cn n | iteratedFDeriv ℝ p u w = 0} :=
    isClosed_eq hcont continuous_const
  have hmem : z ∈ closure {w : Work.NN.Core.Cn n | ∃ j, ρ j < ‖w j‖} := by
    rw [closure_setOf_lt_norm_polydisc hρ]; exact hz
  exact closure_minimal hsub hclosed hmem

/-- If `u` is smooth and vanishes on the closed exterior of `polydisc 0 ρ`, then every iterated
derivative of `u` is `o(‖z - y‖)` as `z → y`, for `y` in the closed exterior. -/
lemma isLittleO_iteratedFDeriv_of_vanishing_closedPolydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiff ℝ ⊤ u)
    (hu0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → u z = 0) (p : ℕ) {y : Work.NN.Core.Cn n}
    (hy : ∃ j, ρ j ≤ ‖y j‖) :
    (fun z => iteratedFDeriv ℝ p u z) =o[𝓝 y] (fun z => z - y) := by
  have hflat := iteratedFDeriv_eq_zero_of_vanishing_closedPolydisc hρ hu hu0
  have hft := ((hu.contDiffOn (s := Set.univ)).ftaylorSeriesWithin uniqueDiffOn_univ).fderivWithin
      p (by simp : (p : WithTop ℕ∞) < (⊤ : WithTop ℕ∞)) y (mem_univ y)
  have hderiv : HasFDerivAt (fun z => iteratedFDeriv ℝ p u z)
      ((iteratedFDeriv ℝ (p + 1) u y).curryLeft) y := by
    simp only [ftaylorSeriesWithin, iteratedFDerivWithin_univ] at hft
    rwa [hasFDerivWithinAt_univ] at hft
  have hzero' : iteratedFDeriv ℝ (p + 1) u y = 0 := hflat (p + 1) y hy
  have hcurry : (iteratedFDeriv ℝ (p + 1) u y).curryLeft
      = (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n [×p]→L[ℝ] ℂ) := by
    rw [hzero']
    ext x m
    simp [ContinuousMultilinearMap.curryLeft_apply]
  have hderiv0 : HasFDerivAt (fun z => iteratedFDeriv ℝ p u z)
      (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n [×p]→L[ℝ] ℂ) y := by
    simpa [hcurry] using hderiv
  have hpy : iteratedFDeriv ℝ p u y = 0 := hflat p y hy
  have := hderiv0.isLittleO
  simpa [hpy] using this

/-! ## The product of a flat `u` with a `C^{k+1}` function on a polydisc -/

/-- Squeezing an `IsLittleO` estimate: if `‖G x‖ ≤ h x` eventually and `h =o v` then `G =o v`. -/
private lemma isLittleO_of_norm_le {α : Type*} {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {l : Filter α} {G : α → E} {h : α → ℝ} {v : α → F}
    (hle : ∀ᶠ x in l, ‖G x‖ ≤ h x) (hh : h =o[l] v) : G =o[l] v := by
  rw [Asymptotics.isLittleO_iff] at hh ⊢
  intro c hc
  filter_upwards [hle, hh hc] with x hx1 hx2
  have hx0 : 0 ≤ h x := le_trans (norm_nonneg _) hx1
  rw [Real.norm_of_nonneg hx0] at hx2
  exact le_trans hx1 hx2

/-- **The key product estimate.**  Let `u` be smooth with compact support whose support lies in
the closed polydisc `polydisc 0 ρ`, and let `ζ` be `C^{k+1}` on the open polydisc `polydisc 0 ρ`
with finite `C^{k,α}`-norm there.  Then the product `u · ζ` is `C^{k,α}` on all of `ℂⁿ`, with

  `‖u · ζ‖_{C^{k,α}(ℂⁿ)} ≤ C · ‖ζ‖_{C^{k,α}(polydisc 0 ρ)}`.

The point is that `u` is flat on the closed exterior of the polydisc, so that `u · ζ` vanishes
to infinite order there (while `ζ` is only controlled inside). -/
theorem holderNorm_mul_le_of_flat_supported {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {k : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiff ℝ ⊤ u) (hus : HasCompactSupport u)
    (hu0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → u z = 0)
    {ζ : Work.NN.Core.Cn n → ℂ} (hζ : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) ζ (polydisc 0 ρ))
    (hζf : holderNorm k α ζ (polydisc 0 ρ) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ holderNorm k α (fun z => u z * ζ z) Set.univ
      ≤ ENNReal.ofReal C * holderNorm k α ζ (polydisc 0 ρ) := by
  set P : Set (Work.NN.Core.Cn n) := polydisc 0 ρ with hP
  have hPopen : IsOpen P := by rw [hP]; exact isOpen_polydisc 0 ρ
  have hPud : UniqueDiffOn ℝ P := hPopen.uniqueDiffOn
  set H : ℝ≥0∞ := holderNorm k α ζ P with hH
  have hHne : H ≠ ⊤ := hH ▸ hζf
  set M : ℝ := H.toReal with hM
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  have hHM : H = ENNReal.ofReal M := (ENNReal.ofReal_toReal hHne).symm
  -- bounds for the derivatives of `ζ` on the polydisc
  have hζbd : ∀ q ≤ k, ∀ x ∈ P, ‖iteratedFDeriv ℝ q ζ x‖ ≤ M := by
    intro q hq x hx
    have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ q ζ P x‖ ≤ H := by
      rw [hH]
      exact le_trans (le_iterDerivNorm q ζ P hx) (iterDerivNorm_le_holderNorm k α ζ P hq)
    rw [hHM] at h1
    have h2 : ‖iteratedFDerivWithin ℝ q ζ P x‖ ≤ M := (ENNReal.ofReal_le_ofReal_iff hMnn).mp h1
    rwa [iteratedFDerivWithin_of_isOpen q hPopen hx] at h2
  -- bounds for the derivatives of `u`
  have hbdd : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖iteratedFDeriv ℝ j u z‖ ≤ B := by
    intro j
    have hcont : Continuous (iteratedFDeriv ℝ j u) := hu.continuous_iteratedFDeriv (m := j) le_top
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hus.iteratedFDeriv j)
    exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩
  choose Bu hBunn hBu using hbdd
  -- Lipschitz bound for the derivatives of `u`
  have hulip : ∀ (i : ℕ) (x y' : Work.NN.Core.Cn n),
      ‖iteratedFDeriv ℝ i u x - iteratedFDeriv ℝ i u y'‖ ≤ Bu (i + 1) * ‖x - y'‖ := by
    intro i x y'
    have hdiff : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ i u) z := fun z =>
      ((hu.differentiable_iteratedFDeriv (m := i) (lt_top_iff_ne_top.mpr (by simp))).differentiableAt)
    have hbd : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ i u) z‖ ≤ Bu (i + 1) := fun z => by
      rw [norm_fderiv_iteratedFDeriv]; exact hBu (i + 1) z
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hbd z)
      convex_univ (mem_univ x) (mem_univ y')
  -- the pointwise Leibniz bound on the polydisc
  have hpoint : ∀ m ≤ k, ∀ z ∈ P,
      ‖iteratedFDeriv ℝ m (fun z => u z * ζ z) z‖
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M := by
    intro m hm z hz
    have h1 := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := P) (f := u) (g := ζ)
      (N := (((k + 1 : ℕ)) : ℕ∞))
      ((hu.of_le le_top).contDiffOn (s := P)) hζ hPud hz (n := m)
      (by exact_mod_cast (Nat.le_succ_of_le hm))
    rw [iteratedFDerivWithin_of_isOpen m hPopen hz] at h1
    refine h1.trans (Finset.sum_le_sum fun i hi => ?_)
    have him : m - i ≤ k := le_trans (Nat.sub_le m i) hm
    have h1i : ‖iteratedFDerivWithin ℝ i u P z‖ ≤ ‖iteratedFDeriv ℝ i u z‖ := by
      rw [iteratedFDerivWithin_of_isOpen i hPopen hz]
    have h2i : ‖iteratedFDerivWithin ℝ (m - i) ζ P z‖ ≤ M := by
      rw [iteratedFDerivWithin_of_isOpen (m - i) hPopen hz]; exact hζbd (m - i) him z hz
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1i (Nat.cast_nonneg _)) h2i (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  -- `u` has a priori bounds, used to dominate the constants
  set Bsum : ℝ := ∑ i ∈ Finset.range (k + 2), Bu i with hBsum
  set Dsum : ℝ := ∑ i ∈ Finset.range (k + 1), (Bu i + Bu (i + 1)) with hDsum
  have hBsum_nn : 0 ≤ Bsum := Finset.sum_nonneg fun i _ => hBunn i
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun i _ => add_nonneg (hBunn i) (hBunn (i + 1))
  -- flatness of the product on the closed exterior
  have hflat : ∀ m ≤ k, ∀ y, (∃ j, ρ j ≤ ‖y j‖) →
      iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ y = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ y hy
      have hz0 : u y * ζ y = 0 := by rw [hu0 y hy, zero_mul]
      rw [iteratedFDerivWithin_zero_eq_comp]
      simp only [Function.comp_apply, hz0]
      ext m
      simp [ContinuousMultilinearMap.uncurry0_apply]
    | succ m IH =>
      intro hmk y hy
      have hmk' : m ≤ k := le_trans (Nat.le_succ m) hmk
      have hGy : iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ y = 0 := IH hmk' y hy
      -- the `m`-th derivative of the product is `o(‖z - y‖)` near `y`
      have hG : (fun z => iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ z)
          =o[𝓝 y] (fun z => z - y) := by
        refine isLittleO_of_norm_le (E := Work.NN.Core.Cn n [×m]→L[ℝ] ℂ) (F := Work.NN.Core.Cn n)
          (l := 𝓝 y)
          (G := fun z => iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ z)
          (h := fun z => ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M)
          (v := fun z => z - y) ?_ ?_
        · refine Filter.Eventually.of_forall fun z => ?_
          by_cases hzP : z ∈ P
          · rw [iteratedFDerivWithin_univ]; exact hpoint m hmk' z hzP
          · have hzC : ∃ j, ρ j ≤ ‖z j‖ := by
              by_contra hcon
              simp only [not_exists] at hcon
              exact hzP (by rw [hP, mem_polydisc]; exact fun j => lt_of_not_ge (by simpa using hcon j))
            rw [IH hmk' z hzC]
            exact le_trans (by simp) (Finset.sum_nonneg fun i _ =>
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hMnn)
        · have hterm : ∀ i ∈ Finset.range (m + 1),
              (fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M)
                =o[𝓝 y] (fun z => z - y) := by
            intro i hi
            have hio : (fun z => iteratedFDeriv ℝ i u z) =o[𝓝 y] (fun z => z - y) :=
              isLittleO_iteratedFDeriv_of_vanishing_closedPolydisc hρ hu hu0 i hy
            have h1 : (fun z => ‖iteratedFDeriv ℝ i u z‖) =o[𝓝 y] (fun z => z - y) :=
              hio.norm_left
            have h2 := h1.const_mul_left ((m.choose i : ℝ) * M)
            rw [show (fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M)
                = (fun z => ((m.choose i : ℝ) * M) * ‖iteratedFDeriv ℝ i u z‖) from by
                  funext z; ring]
            exact h2
          rw [show (fun z => ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M)
              = (∑ i ∈ Finset.range (m + 1),
                  fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ * M) from by
                funext z; rw [Finset.sum_apply]]
          exact Asymptotics.IsLittleO.sum hterm
      have hderiv : HasFDerivAt
          (fun z => iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ z)
          (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n [×m]→L[ℝ] ℂ) y := by
        rw [hasFDerivAt_iff_isLittleO]
        simpa [hGy] using hG
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      simp only [Function.comp_apply]
      rw [fderivWithin_univ, hderiv.fderiv]
      ext m'
      simp
  -- ### the constants
  set Kmul : ℝ≥0∞ := ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) with hKmul
  have hKmul_ne : Kmul ≠ ⊤ := by
    rw [hKmul]
    exact ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩)
      (ENNReal.pow_ne_top (by norm_num))
  set Kmul' : ℝ := Kmul.toReal + 1 with hKmul'
  have hKmul'_pos : 0 < Kmul' := by rw [hKmul']; positivity
  have huPne : holderNorm k α u P ≠ ⊤ :=
    ne_top_of_le_ne_top
      (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
        (X := Work.NN.Core.Cn n) hα (le_of_lt hα1) (hu.of_le le_top) hus)
      (holderNorm_mono_set isOpen_univ hPopen (subset_univ P) k α u)
  set Bu0 : ℝ := (holderNorm k α u P).toReal with hBu0
  have hBu0nn : 0 ≤ Bu0 := ENNReal.toReal_nonneg
  have hBu0eq : holderNorm k α u P = ENNReal.ofReal Bu0 := (ENNReal.ofReal_toReal huPne).symm
  set Cbig : ℝ := 2 ^ k * (Bsum + Dsum) + Kmul' * (Bu0 + 1) + 1 with hCbig
  have hpowk : (0:ℝ) ≤ 2 ^ k := by positivity
  have hrest : 0 ≤ Kmul' * (Bu0 + 1) := mul_nonneg hKmul'_pos.le (by linarith)
  have hfirst : 0 ≤ 2 ^ k * (Bsum + Dsum) := mul_nonneg hpowk (add_nonneg hBsum_nn hDsum_nn)
  have hCbig_nn : 0 ≤ Cbig := by rw [hCbig]; linarith
  have hKmul'Bu0_le : Kmul' * Bu0 ≤ Cbig := by
    rw [hCbig]
    have h3 : Kmul' * Bu0 ≤ Kmul' * (Bu0 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hKmul'_pos.le
    linarith
  have hKmul_le : Kmul ≤ ENNReal.ofReal Kmul' := by
    rw [hKmul']
    exact le_trans (le_of_eq (ENNReal.ofReal_toReal hKmul_ne).symm)
      (ENNReal.ofReal_le_ofReal (by linarith))
  -- ### the product bound on the polydisc
  have hprod_raw : holderNorm k α (fun z => u z * ζ z) P
      ≤ Kmul * holderNorm k α u P * H :=
    Work.CR.Flat.Holder.holderNorm_mul_le (k := k) (α := α) (f := u) (g := ζ) (Ω := P)
      ((hu.of_le le_top).contDiffOn (s := P))
      (hζ.of_le (by exact_mod_cast Nat.le_succ k)) hPud huPne hζf
  have hprod : holderNorm k α (fun z => u z * ζ z) P ≤ ENNReal.ofReal Cbig * H := by
    refine hprod_raw.trans ?_
    have h1 : Kmul * holderNorm k α u P ≤ ENNReal.ofReal Kmul' * ENNReal.ofReal Bu0 := by
      rw [hBu0eq]
      exact mul_le_mul hKmul_le le_rfl (zero_le) (zero_le)
    calc Kmul * holderNorm k α u P * H
        ≤ ENNReal.ofReal Kmul' * ENNReal.ofReal Bu0 * H :=
          mul_le_mul_of_nonneg_right h1 (zero_le)
      _ = ENNReal.ofReal (Kmul' * Bu0) * H := by
          rw [← ENNReal.ofReal_mul hKmul'_pos.le]
      _ ≤ ENNReal.ofReal Cbig * H :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hKmul'Bu0_le) H
  -- ### combinatorial facts
  have hBu_le_Bsum : ∀ i, i ≤ k + 1 → Bu i ≤ Bsum := by
    intro i hi
    exact Finset.single_le_sum (f := Bu) (fun j _ => hBunn j)
      (Finset.mem_range.mpr (by omega))
  have hBu_le_Dsum : ∀ i, i ≤ k → Bu i + Bu (i + 1) ≤ Dsum := by
    intro i hi
    exact Finset.single_le_sum (f := fun j => Bu j + Bu (j + 1))
      (fun j _ => add_nonneg (hBunn j) (hBunn (j + 1))) (Finset.mem_range.mpr (by omega))
  have hchoose : ∀ m, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
    intro m
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hCbig_ge_Bsum : 2 ^ k * Bsum ≤ Cbig := by
    rw [hCbig]
    have h1 : 2 ^ k * Bsum ≤ 2 ^ k * (Bsum + Dsum) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDsum_nn) hpowk
    linarith
  have hCbig_ge_Dsum : 2 ^ k * Dsum ≤ Cbig := by
    rw [hCbig]
    have h1 : 2 ^ k * Dsum ≤ 2 ^ k * (Bsum + Dsum) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hBsum_nn) hpowk
    linarith
  have hA0 : ∀ m ≤ k, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) ≤ Cbig := by
    intro m hm
    have h1 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i)
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bsum :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (hBu_le_Bsum i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
    have h2 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bsum)
        = (2 : ℝ) ^ m * Bsum := by rw [← Finset.sum_mul, hchoose m]
    have h3 : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hm
    calc (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i)
        ≤ (2 : ℝ) ^ m * Bsum := h1.trans (le_of_eq h2)
      _ ≤ 2 ^ k * Bsum := mul_le_mul_of_nonneg_right h3 hBsum_nn
      _ ≤ Cbig := hCbig_ge_Bsum
  have hA1 : ∀ m ≤ k, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) ≤ Cbig := by
    intro m hm
    have h1 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1))
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Dsum :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (le_trans (by linarith [hBunn i]) (hBu_le_Dsum i (by have := Finset.mem_range.mp hi; omega)))
        (Nat.cast_nonneg _)
    have h2 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Dsum)
        = (2 : ℝ) ^ m * Dsum := by rw [← Finset.sum_mul, hchoose m]
    have h3 : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hm
    calc (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1))
        ≤ (2 : ℝ) ^ m * Dsum := h1.trans (le_of_eq h2)
      _ ≤ 2 ^ k * Dsum := mul_le_mul_of_nonneg_right h3 hDsum_nn
      _ ≤ Cbig := hCbig_ge_Dsum
  -- ### the two halves of the norm
  have hIDN : ∀ m ≤ k, iterDerivNorm m (fun z => u z * ζ z) Set.univ
      ≤ ENNReal.ofReal Cbig * H := by
    intro m hm
    refine iSup₂_le fun z _ => ?_
    by_cases hzP : z ∈ P
    · have h1 : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ z‖
          ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) * M := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm z hzP).trans ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun i hi => mul_le_mul
          (mul_le_mul_of_nonneg_left (hBu i z) (Nat.cast_nonneg _)) le_rfl hMnn
          (mul_nonneg (Nat.cast_nonneg _) (hBunn i))
      have hXnn : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hBunn i)
      refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
      rw [ENNReal.ofReal_mul hXnn, hHM]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hA0 m hm)) (zero_le)
    · have hzC : ∃ j, ρ j ≤ ‖z j‖ := not_mem_polydisc_exists hzP
      rw [hflat m hm z hzC]
      simp
  have hHSN : ∀ m ≤ k, holderSeminorm m α (fun z => u z * ζ z) Set.univ
      ≤ ENNReal.ofReal Cbig * H := by
    intro m hm
    have mixed : ∀ a b, a ≠ b → a ∈ P → (∃ j, ρ j ≤ ‖b j‖) →
        ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α)
          ≤ ENNReal.ofReal Cbig * H := by
      intro a b hab haP hbC
      have hdpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
      have hA0b : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖
          ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) * M := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm a haP).trans ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun i hi => mul_le_mul
          (mul_le_mul_of_nonneg_left (hBu i a) (Nat.cast_nonneg _)) le_rfl hMnn
          (mul_nonneg (Nat.cast_nonneg _) (hBunn i))
      have hA1b : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖
          ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M * ‖a - b‖ := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm a haP).trans ?_
        calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i u a‖ * M
            ≤ ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * (Bu (i + 1) * ‖a - b‖) * M := by
              refine Finset.sum_le_sum fun i hi => ?_
              have h1 : ‖iteratedFDeriv ℝ i u a‖ ≤ Bu (i + 1) * ‖a - b‖ := by
                have h2 : iteratedFDeriv ℝ i u b = 0 :=
                  iteratedFDeriv_eq_zero_of_vanishing_closedPolydisc hρ hu hu0 i b hbC
                rw [← sub_zero (iteratedFDeriv ℝ i u a), ← h2]
                exact hulip i a b
              exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) le_rfl hMnn
                (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hBunn (i+1)) (norm_nonneg _)))
          _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M * ‖a - b‖ := by
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i hi => ?_
              ring
      have hS1nn : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hBunn (i + 1))
      have hS0nn : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hBunn i)
      have hratio : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α
          ≤ Cbig * M := by
        by_cases hdle : ‖a - b‖ ≤ 1
        · have hpow : ‖a - b‖ ^ (1 - α) ≤ 1 :=
            Real.rpow_le_one (norm_nonneg _) hdle (by linarith)
          have hstep : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α
              ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M := by
            calc ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α
                ≤ ((∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M
                    * ‖a - b‖) / ‖a - b‖ ^ α :=
                  div_le_div_of_nonneg_right hA1b (Real.rpow_nonneg (norm_nonneg _) α)
              _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M
                    * (‖a - b‖ / ‖a - b‖ ^ α) := by ring
              _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M
                    * ‖a - b‖ ^ (1 - α) := by
                  rw [show ‖a - b‖ / ‖a - b‖ ^ α = ‖a - b‖ ^ (1 - α) from by
                    rw [Real.rpow_sub hdpos 1 α, Real.rpow_one]]
              _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M * 1 := by
                  gcongr
              _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu (i + 1)) * M := by ring
          exact hstep.trans (mul_le_mul_of_nonneg_right (hA1 m hm) hMnn)
        · have hdgt : 1 < ‖a - b‖ := not_le.mp hdle
          have hpow : 1 ≤ ‖a - b‖ ^ α := Real.one_le_rpow (le_of_lt hdgt) hα
          have hstep : ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α
              ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) * M := by
            calc ‖iteratedFDerivWithin ℝ m (fun z => u z * ζ z) Set.univ a‖ / ‖a - b‖ ^ α
                ≤ ((∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) * M)
                    / ‖a - b‖ ^ α :=
                  div_le_div_of_nonneg_right hA0b (Real.rpow_nonneg (norm_nonneg _) α)
              _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu i) * M :=
                  div_le_self (mul_nonneg hS0nn hMnn) hpow
          exact hstep.trans (mul_le_mul_of_nonneg_right (hA0 m hm) hMnn)
      refine le_trans (ENNReal.ofReal_le_ofReal hratio) ?_
      rw [ENNReal.ofReal_mul hCbig_nn, hHM]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    by_cases hxP : x ∈ P
    · by_cases hyP : y ∈ P
      · have h1 := le_holderSeminorm m α (fun z => u z * ζ z) P hxP hyP hxy
        rw [iteratedFDerivWithin_of_isOpen m hPopen hxP,
            iteratedFDerivWithin_of_isOpen m hPopen hyP] at h1
        rw [iteratedFDerivWithin_univ]
        exact h1.trans ((holderSeminorm_le_holderNorm k α (fun z => u z * ζ z) P hm).trans hprod)
      · rw [hflat m hm y (not_mem_polydisc_exists hyP), sub_zero]
        exact mixed x y hxy hxP (not_mem_polydisc_exists hyP)
    · by_cases hyP : y ∈ P
      · have hxC := not_mem_polydisc_exists hxP
        rw [hflat m hm x hxC, zero_sub, norm_neg, norm_sub_rev x y]
        exact mixed y x hxy.symm hyP hxC
      · rw [hflat m hm x (not_mem_polydisc_exists hxP),
            hflat m hm y (not_mem_polydisc_exists hyP), sub_self, norm_zero, zero_div]
        simp
  -- ### assembly
  refine ⟨((k + 1 : ℕ) : ℝ) * (2 * Cbig) + 1, by positivity, ?_⟩
  rw [show (fun z => u z * ζ z) = (fun z => u z * ζ z) from rfl]
  rw [holderNorm]
  calc ∑ m ∈ Finset.range (k + 1),
        (iterDerivNorm m (fun z => u z * ζ z) Set.univ
          + holderSeminorm m α (fun z => u z * ζ z) Set.univ)
      ≤ ∑ _m ∈ Finset.range (k + 1),
          (ENNReal.ofReal Cbig * H + ENNReal.ofReal Cbig * H) :=
        Finset.sum_le_sum fun m hm => add_le_add (hIDN m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
          (hHSN m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (2 * Cbig)) * H := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [show ENNReal.ofReal Cbig * H + ENNReal.ofReal Cbig * H
              = ENNReal.ofReal (2 * Cbig) * H from by
            rw [← add_mul, ← ENNReal.ofReal_add hCbig_nn hCbig_nn, show Cbig + Cbig = 2 * Cbig from by ring]]
        rw [← ENNReal.ofReal_natCast (k + 1)]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
    _ ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (2 * Cbig) + 1) * H :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) _

/-- Factoring a constant out of a double sum. -/
private lemma sum_univ_sum_range_mul {ι : Type*} [Fintype ι] (m : ℕ) (f : ι → ℕ → ℝ) (M : ℝ) :
    (∑ t, ∑ i ∈ Finset.range (m + 1), f t i * M)
      = (∑ t, ∑ i ∈ Finset.range (m + 1), f t i) * M := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => (Finset.sum_mul _ _ _).symm

/-- **The key product estimate, for a finite sum.**  If each `u t` is smooth with compact
support contained in the closed polydisc `polydisc 0 ρ` and each `v t` is `C^{k+1}` on the open
polydisc, then the sum of products is `C^{k,α}` on all of `ℂⁿ`, with

  `‖Σ t, u t · v t‖_{C^{k,α}(ℂⁿ)} ≤ C · Σ t, ‖v t‖_{C^{k,α}(polydisc 0 ρ)}`. -/
theorem holderNorm_sumMul_le_of_flat_supported {ι : Type*} [Fintype ι]
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {k : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (u : ι → Work.NN.Core.Cn n → ℂ) (hu : ∀ t, ContDiff ℝ ⊤ (u t))
    (hus : ∀ t, HasCompactSupport (u t))
    (hu0 : ∀ t z, (∃ j, ρ j ≤ ‖z j‖) → u t z = 0)
    (v : ι → Work.NN.Core.Cn n → ℂ)
    (hv : ∀ t, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (v t) (polydisc 0 ρ))
    (hvf : ∀ t, holderNorm k α (v t) (polydisc 0 ρ) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ holderNorm k α (fun z => ∑ t, u t z * v t z) Set.univ
      ≤ ENNReal.ofReal C * ∑ t, holderNorm k α (v t) (polydisc 0 ρ) := by
  classical
  set P : Set (Work.NN.Core.Cn n) := polydisc 0 ρ with hP
  have hPopen : IsOpen P := by rw [hP]; exact isOpen_polydisc 0 ρ
  have hPud : UniqueDiffOn ℝ P := hPopen.uniqueDiffOn
  set F : Work.NN.Core.Cn n → ℂ := fun z => ∑ t, u t z * v t z with hF
  have hvp : ∀ t, holderNorm k α (v t) P ≠ ⊤ := fun t => by rw [hP]; exact hvf t
  set H : ℝ≥0∞ := ∑ t, holderNorm k α (v t) P with hH
  have hHne : H ≠ ⊤ := by
    rw [hH]
    exact ENNReal.sum_ne_top.mpr fun t _ => hvp t
  set M : ℝ := H.toReal with hM
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  have hHM : H = ENNReal.ofReal M := (ENNReal.ofReal_toReal hHne).symm
  -- bounds for the derivatives of the `v t`
  have hvbd : ∀ t, ∀ q ≤ k, ∀ x ∈ P, ‖iteratedFDeriv ℝ q (v t) x‖ ≤ M := by
    intro t q hq x hx
    have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ q (v t) P x‖ ≤ H := by
      rw [hH]
      refine le_trans (le_iterDerivNorm q (v t) P hx) ?_
      refine le_trans (iterDerivNorm_le_holderNorm k α (v t) P hq) ?_
      exact Finset.single_le_sum (f := fun t => holderNorm k α (v t) P)
        (fun _ _ => bot_le) (Finset.mem_univ t)
    rw [hHM] at h1
    have h2 : ‖iteratedFDerivWithin ℝ q (v t) P x‖ ≤ M := (ENNReal.ofReal_le_ofReal_iff hMnn).mp h1
    rwa [iteratedFDerivWithin_of_isOpen q hPopen hx] at h2
  -- bounds for the derivatives of the `u t`
  have hbdd : ∀ t j, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖iteratedFDeriv ℝ j (u t) z‖ ≤ B := by
    intro t j
    have hcont : Continuous (iteratedFDeriv ℝ j (u t)) :=
      (hu t).continuous_iteratedFDeriv (m := j) le_top
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support ((hus t).iteratedFDeriv j)
    exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩
  choose Bu hBunn hBu using hbdd
  have hulip : ∀ (t : ι) (i : ℕ) (x y' : Work.NN.Core.Cn n),
      ‖iteratedFDeriv ℝ i (u t) x - iteratedFDeriv ℝ i (u t) y'‖ ≤ Bu t (i + 1) * ‖x - y'‖ := by
    intro t i x y'
    have hdiff : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ i (u t)) z := fun z =>
      ((hu t).differentiable_iteratedFDeriv (m := i) (lt_top_iff_ne_top.mpr (by simp))).differentiableAt
    have hbd : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ i (u t)) z‖ ≤ Bu t (i + 1) := fun z => by
      rw [norm_fderiv_iteratedFDeriv]; exact hBu t (i + 1) z
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hbd z)
      convex_univ (mem_univ x) (mem_univ y')
  -- the pointwise Leibniz bound on the polydisc
  have hpoint : ∀ m ≤ k, ∀ z ∈ P,
      ‖iteratedFDeriv ℝ m F z‖
        ≤ ∑ t, ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M := by
    intro m hm z hz
    have hmul_cont : ∀ t, ContDiffWithinAt ℝ (m : ℕ∞) (fun z => u t z * v t z) P z := by
      intro t
      have h1 : ContDiffOn ℝ (m : ℕ∞) (u t) P := ((hu t).of_le le_top).contDiffOn (s := P)
      have h2 : ContDiffOn ℝ (m : ℕ∞) (v t) P :=
        (hv t).of_le (by exact_mod_cast (show m ≤ k + 1 by omega))
      exact (h1.mul h2).contDiffWithinAt hz
    have hsum : iteratedFDerivWithin ℝ m F P z
        = ∑ t, iteratedFDerivWithin ℝ m (fun z => u t z * v t z) P z := by
      rw [hF]
      exact iteratedFDerivWithin_fun_sum_apply hPud hz (u := Finset.univ)
        (f := fun t z => u t z * v t z) (i := m) (fun t _ => hmul_cont t)
    rw [iteratedFDerivWithin_of_isOpen m hPopen hz] at hsum
    rw [hsum]
    refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := P) (f := u t) (g := v t)
      (N := (((k + 1 : ℕ)) : ℕ∞)) (((hu t).of_le le_top).contDiffOn (s := P)) (hv t) hPud hz
      (n := m) (by exact_mod_cast (Nat.le_succ_of_le hm))).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    have him : m - i ≤ k := le_trans (Nat.sub_le m i) hm
    have h1i : ‖iteratedFDerivWithin ℝ i (u t) P z‖ ≤ ‖iteratedFDeriv ℝ i (u t) z‖ := by
      rw [iteratedFDerivWithin_of_isOpen i hPopen hz]
    have h2i : ‖iteratedFDerivWithin ℝ (m - i) (v t) P z‖ ≤ M := by
      rw [iteratedFDerivWithin_of_isOpen (m - i) hPopen hz]
      exact hvbd t (m - i) him z hz
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1i (Nat.cast_nonneg _)) h2i (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  -- ### the constants
  set Kmul : ℝ≥0∞ := ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) with hKmul
  have hKmul_ne : Kmul ≠ ⊤ := by
    rw [hKmul]
    exact ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩)
      (ENNReal.pow_ne_top (by norm_num))
  set Kmul' : ℝ := Kmul.toReal + 1 with hKmul'
  have hKmul'_pos : 0 < Kmul' := by rw [hKmul']; positivity
  have huPne : ∀ t, holderNorm k α (u t) P ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top
      (Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport'
        (X := Work.NN.Core.Cn n) hα (le_of_lt hα1) ((hu t).of_le le_top) (hus t))
      (holderNorm_mono_set isOpen_univ hPopen (subset_univ P) k α (u t))
  have hUsum_terms : ∀ t, (holderNorm k α (u t) P).toReal ≤ ∑ t, (holderNorm k α (u t) P).toReal :=
    fun t => Finset.single_le_sum (f := fun t => (holderNorm k α (u t) P).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ t)
  set Usum : ℝ := ∑ t, (holderNorm k α (u t) P).toReal with hUsum
  have hUsum_nn : 0 ≤ Usum := Finset.sum_nonneg fun t _ => ENNReal.toReal_nonneg
  set Bs : ι → ℝ := fun t => ∑ i ∈ Finset.range (k + 2), Bu t i with hBs
  have hBs_nn : ∀ t, 0 ≤ Bs t := fun t => Finset.sum_nonneg fun i _ => hBunn t i
  set Ds : ι → ℝ := fun t => ∑ i ∈ Finset.range (k + 1), (Bu t i + Bu t (i + 1)) with hDs
  have hDs_nn : ∀ t, 0 ≤ Ds t := fun t =>
    Finset.sum_nonneg fun i _ => add_nonneg (hBunn t i) (hBunn t (i + 1))
  set Bsum : ℝ := ∑ t, Bs t with hBsum
  have hBsum_nn : 0 ≤ Bsum := Finset.sum_nonneg fun t _ => hBs_nn t
  set Dsum : ℝ := ∑ t, Ds t with hDsum
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun t _ => hDs_nn t
  have hBu_le_Bs : ∀ t i, i ≤ k + 1 → Bu t i ≤ Bs t := by
    intro t i hi
    exact Finset.single_le_sum (f := fun i => Bu t i) (fun i _ => hBunn t i)
      (Finset.mem_range.mpr (by omega))
  have hBu1_le_Ds : ∀ t i, i ≤ k → Bu t (i + 1) ≤ Ds t := by
    intro t i hi
    refine le_trans (le_add_of_nonneg_left (hBunn t i)) ?_
    exact Finset.single_le_sum (f := fun i => Bu t i + Bu t (i + 1))
      (fun i _ => add_nonneg (hBunn t i) (hBunn t (i + 1))) (Finset.mem_range.mpr (by omega))
  have hBs_le_Bsum : ∀ t, Bs t ≤ Bsum := fun t =>
    Finset.single_le_sum (f := fun t => Bs t) (fun t _ => hBs_nn t) (Finset.mem_univ t)
  have hDs_le_Dsum : ∀ t, Ds t ≤ Dsum := fun t =>
    Finset.single_le_sum (f := fun t => Ds t) (fun t _ => hDs_nn t) (Finset.mem_univ t)
  set Cbig : ℝ := ((Fintype.card ι : ℝ) + 1) * (Kmul' * Usum + 2 ^ k * (Bsum + Dsum) + 1) with hCbig
  have hcard_nn : 0 ≤ ((Fintype.card ι : ℝ)) := Nat.cast_nonneg _
  have hpowk : (0:ℝ) ≤ 2 ^ k := by positivity
  have hstuff : 0 ≤ Kmul' * Usum + 2 ^ k * (Bsum + Dsum) + 1 := by
    have h1 : 0 ≤ Kmul' * Usum := mul_nonneg hKmul'_pos.le hUsum_nn
    have h2 : 0 ≤ 2 ^ k * (Bsum + Dsum) := mul_nonneg hpowk (add_nonneg hBsum_nn hDsum_nn)
    linarith
  have hCbig_nn : 0 ≤ Cbig := by
    rw [hCbig]; exact mul_nonneg (by linarith [hcard_nn]) hstuff
  have hKmul'Usum_le : Kmul' * Usum ≤ Cbig := by
    rw [hCbig]
    nlinarith [hstuff, hcard_nn, mul_nonneg hKmul'_pos.le hUsum_nn]
  have hcard_le : (Fintype.card ι : ℝ) * (Kmul' * Usum) ≤ Cbig := by
    rw [hCbig]
    have h1 : 0 ≤ Kmul' * Usum := mul_nonneg hKmul'_pos.le hUsum_nn
    have h2 : Kmul' * Usum ≤ Kmul' * Usum + 2 ^ k * (Bsum + Dsum) + 1 := by
      have h3 : 0 ≤ 2 ^ k * (Bsum + Dsum) := mul_nonneg hpowk (add_nonneg hBsum_nn hDsum_nn)
      linarith
    nlinarith [h1, h2, hstuff, hcard_nn]
  have hKmul_le : Kmul ≤ ENNReal.ofReal Kmul' := by
    rw [hKmul']
    exact le_trans (le_of_eq (ENNReal.ofReal_toReal hKmul_ne).symm)
      (ENNReal.ofReal_le_ofReal (by linarith))
  -- ### the product bound on the polydisc
  have hprod_t : ∀ t, holderNorm k α (fun z => u t z * v t z) P
      ≤ ENNReal.ofReal (Kmul' * Usum) * H := by
    intro t
    have h1 := Work.CR.Flat.Holder.holderNorm_mul_le (k := k) (α := α) (f := u t) (g := v t)
      (Ω := P) (((hu t).of_le le_top).contDiffOn (s := P))
      ((hv t).of_le (by exact_mod_cast Nat.le_succ k)) hPud (huPne t) (hvp t)
    refine h1.trans ?_
    have h2 : Kmul * holderNorm k α (u t) P
        ≤ ENNReal.ofReal Kmul' * ENNReal.ofReal ((holderNorm k α (u t) P).toReal) := by
      rw [ENNReal.ofReal_toReal (huPne t)]
      exact mul_le_mul hKmul_le le_rfl (zero_le) (zero_le)
    have h3 : (holderNorm k α (u t) P).toReal ≤ Usum := by rw [hUsum]; exact hUsum_terms t
    have h4 : holderNorm k α (v t) P ≤ H := by
      rw [hH]
      exact Finset.single_le_sum (f := fun t => holderNorm k α (v t) P)
        (fun _ _ => bot_le) (Finset.mem_univ t)
    calc Kmul * holderNorm k α (u t) P * holderNorm k α (v t) P
        ≤ (ENNReal.ofReal Kmul' * ENNReal.ofReal ((holderNorm k α (u t) P).toReal)) * H :=
          mul_le_mul h2 h4 (zero_le) (zero_le)
      _ = ENNReal.ofReal (Kmul' * (holderNorm k α (u t) P).toReal) * H := by
          rw [← ENNReal.ofReal_mul hKmul'_pos.le]
      _ ≤ ENNReal.ofReal (Kmul' * Usum) * H :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h3 hKmul'_pos.le)) H
  have hprod : holderNorm k α F P ≤ ENNReal.ofReal Cbig * H := by
    rw [hF]
    refine le_trans (Work.CR.Flat.Holder.holderNorm_sum_le (s := Finset.univ) (k := k) (α := α)
      (g := fun t z => u t z * v t z) (Ω := P) ?_ hPud) ?_
    · intro t _
      exact ((hu t).of_le le_top).contDiffOn.mul ((hv t).of_le (by exact_mod_cast Nat.le_succ k))
    · calc ∑ t ∈ Finset.univ, holderNorm k α (fun z => u t z * v t z) P
          ≤ ∑ _t ∈ Finset.univ, ENNReal.ofReal (Kmul' * Usum) * H :=
            Finset.sum_le_sum fun t _ => hprod_t t
        _ = (Finset.univ.card : ℝ≥0∞) * (ENNReal.ofReal (Kmul' * Usum) * H) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (Kmul' * Usum)) * H := by
            rw [Finset.card_univ, ← ENNReal.ofReal_natCast (Fintype.card ι), ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (Fintype.card ι : ℝ))]
        _ ≤ ENNReal.ofReal Cbig * H :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hcard_le) H
  have hchoose : ∀ m, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
    intro m
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  -- ### bounds on the inner sums of the constants
  have hA0 : ∀ m ≤ k, (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i) ≤ Cbig := by
    intro m hm
    have h1 : ∀ t, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i)
        ≤ (2 : ℝ) ^ m * Bs t := by
      intro t
      have h2 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i)
          ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bs t :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (hBu_le_Bs t i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
      have h3 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bs t)
          = (2 : ℝ) ^ m * Bs t := by
        rw [(Finset.sum_mul _ _ _).symm, hchoose m]
      exact h2.trans (le_of_eq h3)
    calc (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i)
        ≤ ∑ t, (2 : ℝ) ^ m * Bs t := Finset.sum_le_sum fun t _ => h1 t
      _ = (2 : ℝ) ^ m * Bsum := by rw [← Finset.mul_sum]
      _ ≤ 2 ^ k * Bsum := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hm) hBsum_nn
      _ ≤ Cbig := by
          rw [hCbig]
          have h3 : 2 ^ k * Bsum ≤ Kmul' * Usum + 2 ^ k * (Bsum + Dsum) + 1 := by
            have h4 : 2 ^ k * Bsum ≤ 2 ^ k * (Bsum + Dsum) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hDsum_nn) hpowk
            have h6 : 0 ≤ Kmul' * Usum := mul_nonneg hKmul'_pos.le hUsum_nn
            linarith
          have h5 : (1:ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by linarith [hcard_nn]
          nlinarith [h3, hstuff, h5]
  have hA1 : ∀ m ≤ k, (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1)) ≤ Cbig := by
    intro m hm
    have h1 : ∀ t, (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1))
        ≤ (2 : ℝ) ^ m * Ds t := by
      intro t
      have h2 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1))
          ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Ds t :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (hBu1_le_Ds t i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
      have h3 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Ds t)
          = (2 : ℝ) ^ m * Ds t := by
        rw [(Finset.sum_mul _ _ _).symm, hchoose m]
      exact h2.trans (le_of_eq h3)
    calc (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1))
        ≤ ∑ t, (2 : ℝ) ^ m * Ds t := Finset.sum_le_sum fun t _ => h1 t
      _ = (2 : ℝ) ^ m * Dsum := by rw [← Finset.mul_sum]
      _ ≤ 2 ^ k * Dsum := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hm) hDsum_nn
      _ ≤ Cbig := by
          rw [hCbig]
          have h3 : 2 ^ k * Dsum ≤ Kmul' * Usum + 2 ^ k * (Bsum + Dsum) + 1 := by
            have h4 : 2 ^ k * Dsum ≤ 2 ^ k * (Bsum + Dsum) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hBsum_nn) hpowk
            have h6 : 0 ≤ Kmul' * Usum := mul_nonneg hKmul'_pos.le hUsum_nn
            linarith
          have h5 : (1:ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by linarith [hcard_nn]
          nlinarith [h3, hstuff, h5]
  -- ### flatness of the sum on the closed exterior
  have hflat : ∀ m ≤ k, ∀ y, (∃ j, ρ j ≤ ‖y j‖) →
      iteratedFDerivWithin ℝ m F Set.univ y = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ y hy
      have hz0 : F y = 0 := by
        rw [hF]
        exact Finset.sum_eq_zero fun t _ => by rw [hu0 t y hy, zero_mul]
      rw [iteratedFDerivWithin_zero_eq_comp]
      simp only [Function.comp_apply, hz0]
      ext m'
      simp [ContinuousMultilinearMap.uncurry0_apply]
    | succ m IH =>
      intro hmk y hy
      have hmk' : m ≤ k := le_trans (Nat.le_succ m) hmk
      have hGy : iteratedFDerivWithin ℝ m F Set.univ y = 0 := IH hmk' y hy
      have hG : (fun z => iteratedFDerivWithin ℝ m F Set.univ z) =o[𝓝 y] (fun z => z - y) := by
        refine isLittleO_of_norm_le (E := Work.NN.Core.Cn n [×m]→L[ℝ] ℂ) (F := Work.NN.Core.Cn n)
          (l := 𝓝 y) (G := fun z => iteratedFDerivWithin ℝ m F Set.univ z)
          (h := fun z => ∑ t, ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
          (v := fun z => z - y) ?_ ?_
        · refine Filter.Eventually.of_forall fun z => ?_
          by_cases hzP : z ∈ P
          · rw [iteratedFDerivWithin_univ]; exact hpoint m hmk' z hzP
          · have hzC := not_mem_polydisc_exists hzP
            rw [IH hmk' z hzC]
            exact le_trans (by simp) (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ =>
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hMnn)
        · have hterm : ∀ t, (fun z => ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
                =o[𝓝 y] (fun z => z - y) := by
            intro t
            have hterm' : ∀ i ∈ Finset.range (m + 1),
                (fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
                  =o[𝓝 y] (fun z => z - y) := by
              intro i hi
              have hio : (fun z => iteratedFDeriv ℝ i (u t) z) =o[𝓝 y] (fun z => z - y) :=
                isLittleO_iteratedFDeriv_of_vanishing_closedPolydisc hρ (hu t) (hu0 t) i hy
              have h1 : (fun z => ‖iteratedFDeriv ℝ i (u t) z‖) =o[𝓝 y] (fun z => z - y) :=
                hio.norm_left
              have h2 := h1.const_mul_left ((m.choose i : ℝ) * M)
              rw [show (fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
                  = (fun z => ((m.choose i : ℝ) * M) * ‖iteratedFDeriv ℝ i (u t) z‖) from by
                    funext z; ring]
              exact h2
            rw [show (fun z => ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
                = (∑ i ∈ Finset.range (m + 1),
                    fun z => (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M) from by
                  funext z; rw [Finset.sum_apply]]
            exact Asymptotics.IsLittleO.sum hterm'
          rw [show (fun z => ∑ t, ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M)
              = (∑ t, fun z => ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M) from by
                funext z; rw [Finset.sum_apply]]
          exact Asymptotics.IsLittleO.sum fun t _ => hterm t
      have hderiv : HasFDerivAt (fun z => iteratedFDerivWithin ℝ m F Set.univ z)
          (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n [×m]→L[ℝ] ℂ) y := by
        rw [hasFDerivAt_iff_isLittleO]
        simpa [hGy] using hG
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      simp only [Function.comp_apply]
      rw [fderivWithin_univ, hderiv.fderiv]
      ext m'
      simp
  -- ### the two halves of the norm
  have hIDN : ∀ m ≤ k, iterDerivNorm m F Set.univ ≤ ENNReal.ofReal Cbig * H := by
    intro m hm
    refine iSup₂_le fun z _ => ?_
    by_cases hzP : z ∈ P
    · have h1 : ‖iteratedFDerivWithin ℝ m F Set.univ z‖ ≤ Cbig * M := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm z hzP).trans ?_
        calc ∑ t, ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) z‖ * M
            ≤ ∑ t, ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * Bu t i * M := by
              refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i hi =>
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hBu t i z) (Nat.cast_nonneg _)) hMnn
          _ = (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i) * M :=
              sum_univ_sum_range_mul m (fun t i => (m.choose i : ℝ) * Bu t i) M
          _ ≤ Cbig * M := mul_le_mul_of_nonneg_right (hA0 m hm) hMnn
      refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
      rw [ENNReal.ofReal_mul hCbig_nn, hHM]
    · have hzC := not_mem_polydisc_exists hzP
      rw [hflat m hm z hzC]
      simp
  have hHSN : ∀ m ≤ k, holderSeminorm m α F Set.univ ≤ ENNReal.ofReal Cbig * H := by
    intro m hm
    have mixed : ∀ a b, a ≠ b → a ∈ P → (∃ j, ρ j ≤ ‖b j‖) →
        ENNReal.ofReal (‖iteratedFDerivWithin ℝ m F Set.univ a‖ / ‖a - b‖ ^ α)
          ≤ ENNReal.ofReal Cbig * H := by
      intro a b hab haP hbC
      have hdpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
      have hA0b : ‖iteratedFDerivWithin ℝ m F Set.univ a‖ ≤ Cbig * M := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm a haP).trans ?_
        calc ∑ t, ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) a‖ * M
            ≤ ∑ t, ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * Bu t i * M := by
              refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i hi =>
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hBu t i a) (Nat.cast_nonneg _)) hMnn
          _ = (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t i) * M :=
              sum_univ_sum_range_mul m (fun t i => (m.choose i : ℝ) * Bu t i) M
          _ ≤ Cbig * M := mul_le_mul_of_nonneg_right (hA0 m hm) hMnn
      have hA1b : ‖iteratedFDerivWithin ℝ m F Set.univ a‖ ≤ Cbig * M * ‖a - b‖ := by
        rw [iteratedFDerivWithin_univ]
        refine (hpoint m hm a haP).trans ?_
        calc ∑ t, ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u t) a‖ * M
            ≤ ∑ t, ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * (Bu t (i + 1) * ‖a - b‖) * M := by
              refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i hi => ?_
              have h1 : ‖iteratedFDeriv ℝ i (u t) a‖ ≤ Bu t (i + 1) * ‖a - b‖ := by
                have h2 : iteratedFDeriv ℝ i (u t) b = 0 :=
                  iteratedFDeriv_eq_zero_of_vanishing_closedPolydisc hρ (hu t) (hu0 t) i b hbC
                rw [← sub_zero (iteratedFDeriv ℝ i (u t) a), ← h2]
                exact hulip t i a b
              exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) le_rfl hMnn
                (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hBunn t (i + 1)) (norm_nonneg _)))
          _ = (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1)) * M
                * ‖a - b‖ := by
              rw [sum_univ_sum_range_mul m (fun t i => (m.choose i : ℝ) * (Bu t (i + 1) * ‖a - b‖)) M]
              rw [show (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (Bu t (i + 1) * ‖a - b‖))
                  = (∑ t, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bu t (i + 1)) * ‖a - b‖ from by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun i _ => by ring]
              ring
          _ ≤ Cbig * M * ‖a - b‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_right (hA1 m hm) hMnn
      have hratio : ‖iteratedFDerivWithin ℝ m F Set.univ a‖ / ‖a - b‖ ^ α ≤ Cbig * M := by
        by_cases hdle : ‖a - b‖ ≤ 1
        · have hpow : ‖a - b‖ ^ (1 - α) ≤ 1 :=
            Real.rpow_le_one (norm_nonneg _) hdle (by linarith)
          have hstep : ‖iteratedFDerivWithin ℝ m F Set.univ a‖ / ‖a - b‖ ^ α ≤ Cbig * M := by
            calc ‖iteratedFDerivWithin ℝ m F Set.univ a‖ / ‖a - b‖ ^ α
                ≤ (Cbig * M * ‖a - b‖) / ‖a - b‖ ^ α :=
                  div_le_div_of_nonneg_right hA1b (Real.rpow_nonneg (norm_nonneg _) α)
              _ = Cbig * M * (‖a - b‖ / ‖a - b‖ ^ α) := by ring
              _ = Cbig * M * ‖a - b‖ ^ (1 - α) := by
                  rw [show ‖a - b‖ / ‖a - b‖ ^ α = ‖a - b‖ ^ (1 - α) from by
                    rw [Real.rpow_sub hdpos 1 α, Real.rpow_one]]
              _ ≤ Cbig * M * 1 := by gcongr
              _ = Cbig * M := by ring
          exact hstep
        · have hdgt : 1 < ‖a - b‖ := not_le.mp hdle
          have hpow : 1 ≤ ‖a - b‖ ^ α := Real.one_le_rpow (le_of_lt hdgt) hα
          calc ‖iteratedFDerivWithin ℝ m F Set.univ a‖ / ‖a - b‖ ^ α
              ≤ (Cbig * M) / ‖a - b‖ ^ α :=
                div_le_div_of_nonneg_right hA0b (Real.rpow_nonneg (norm_nonneg _) α)
            _ ≤ Cbig * M := div_le_self (mul_nonneg hCbig_nn hMnn) hpow
      refine le_trans (ENNReal.ofReal_le_ofReal hratio) ?_
      rw [ENNReal.ofReal_mul hCbig_nn, hHM]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    by_cases hxP : x ∈ P
    · by_cases hyP : y ∈ P
      · have h1 := le_holderSeminorm m α F P hxP hyP hxy
        rw [iteratedFDerivWithin_of_isOpen m hPopen hxP,
            iteratedFDerivWithin_of_isOpen m hPopen hyP] at h1
        rw [iteratedFDerivWithin_univ]
        exact h1.trans ((holderSeminorm_le_holderNorm k α F P hm).trans hprod)
      · rw [hflat m hm y (not_mem_polydisc_exists hyP), sub_zero]
        exact mixed x y hxy hxP (not_mem_polydisc_exists hyP)
    · by_cases hyP : y ∈ P
      · have hxC := not_mem_polydisc_exists hxP
        rw [hflat m hm x hxC, zero_sub, norm_neg, norm_sub_rev x y]
        exact mixed y x hxy.symm hyP hxC
      · rw [hflat m hm x (not_mem_polydisc_exists hxP),
            hflat m hm y (not_mem_polydisc_exists hyP), sub_self, norm_zero, zero_div]
        simp
  -- ### assembly
  refine ⟨((k + 1 : ℕ) : ℝ) * (2 * Cbig) + 1, by positivity, ?_⟩
  calc holderNorm k α F Set.univ
      = ∑ m ∈ Finset.range (k + 1),
          (iterDerivNorm m F Set.univ + holderSeminorm m α F Set.univ) := rfl
    _ ≤ ∑ _m ∈ Finset.range (k + 1),
          (ENNReal.ofReal Cbig * H + ENNReal.ofReal Cbig * H) :=
        Finset.sum_le_sum fun m hm' => add_le_add (hIDN m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')))
          (hHSN m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')))
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (2 * Cbig)) * H := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show ENNReal.ofReal Cbig * H + ENNReal.ofReal Cbig * H
              = ENNReal.ofReal (2 * Cbig) * H from by
            rw [← add_mul, ← ENNReal.ofReal_add hCbig_nn hCbig_nn,
              show Cbig + Cbig = 2 * Cbig from by ring],
          ← ENNReal.ofReal_natCast (k + 1), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
    _ ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (2 * Cbig) + 1) * H :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) _

/-- `∂̄_t η` is smooth whenever `η` is. -/
private lemma contDiff_dbarCoord {n : ℕ} {η : Work.NN.Core.Cn n → ℂ} (hη : ContDiff ℝ ⊤ η)
    (j : Fin n) : ContDiff ℝ ⊤ (fun z => dbarCoord j η z) := by
  unfold dbarCoord
  fun_prop

/-- **The `C^{k,α}` estimate for the Bochner–Martinelli defect form `bmH`.**

For `0 < α < 1`, positive multi-radii `ρ`, a smooth `χ` vanishing off the open polydisc
`polydisc 0 ρ` and `ζ` of class `C^{k+1}` on that polydisc with finite `C^{k,α}`-norm, there is
`C > 0` with

  `‖bmH χ ζ j m l‖_{C^{k,α}(ℂⁿ)} ≤ C · Σ_{i,l} ‖ζ i l‖_{C^{k,α}(polydisc 0 ρ)}`

for all `j m l`. -/
theorem holderNorm_bmH_le {n : ℕ} (hn : 0 < n) {k : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ ⊤ χ)
    (hχsub : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ)
    (hζ : ∀ i l, ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ i l) (Work.CR.Flat.polydisc 0 ρ))
    (hζf : ∀ i l, Work.CR.Flat.holderNorm k α (ζ i l) (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ j m l,
      Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ ζ j m l) Set.univ
        ≤ ENNReal.ofReal C * ∑ i, ∑ l', Work.CR.Flat.holderNorm k α (ζ i l') (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  have hα0 : 0 ≤ α := le_of_lt hα
  have hα1' : α ≤ 1 := le_of_lt hα1
  -- each `∂̄_t χ` is smooth
  have hdχ_sm : ∀ t : Fin n, ContDiff ℝ ⊤ (fun z => dbarCoord t χ z) := fun t =>
    contDiff_dbarCoord hχ t
  -- each `∂̄_t χ` vanishes on the closed exterior
  have hdχ_van : ∀ t : Fin n, ∀ z, (∃ j, ρ j ≤ ‖z j‖) → dbarCoord t χ z = 0 := by
    intro t
    have hopen_eq : ∀ z, (∃ j, ρ j < ‖z j‖) → dbarCoord t χ z = 0 := by
      intro z hz
      obtain ⟨j, hj⟩ := hz
      have hopen : IsOpen {w : Work.NN.Core.Cn n | ρ j < ‖w j‖} :=
        isOpen_lt continuous_const ((continuous_apply j).norm)
      have h0 : χ =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
        filter_upwards [hopen.mem_nhds hj] with w hw
        exact hχsub w ⟨j, le_of_lt hw⟩
      have hfd : fderiv ℝ χ z = 0 := by
        rw [h0.fderiv_eq]
        simp
      simp [dbarCoord, hfd]
    intro z hz
    have hcont : Continuous (fun z => dbarCoord t χ z) := (hdχ_sm t).continuous
    have hclosed : IsClosed {w : Work.NN.Core.Cn n | dbarCoord t χ w = 0} :=
      isClosed_eq hcont continuous_const
    exact closure_minimal (fun w hw => hopen_eq w hw) hclosed
      ((closure_setOf_lt_norm_polydisc hρ).ge hz)
  -- each `∂̄_t χ` has compact support
  have hdχ_cs : ∀ t : Fin n, HasCompactSupport (fun z => dbarCoord t χ z) := by
    intro t
    have hsum_nn : 0 ≤ ∑ j, ρ j := Finset.sum_nonneg fun j _ => (hρ j).le
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall (0 : Work.NN.Core.Cn n) (∑ j, ρ j))
      (isCompact_closedBall _ _) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    rw [not_le] at hcon
    have hzC : ∃ j, ρ j ≤ ‖z j‖ := by
      by_contra hcon2
      simp only [not_exists] at hcon2
      have hle : ‖z‖ ≤ ∑ j, ρ j := by
        rw [pi_norm_le_iff_of_nonneg hsum_nn]
        intro j
        refine le_trans (le_of_lt (by simpa using hcon2 j)) ?_
        exact Finset.single_le_sum (f := ρ) (fun j _ => (hρ j).le) (Finset.mem_univ j)
      linarith
    exact hz (hdχ_van t z hzC)
  -- the estimate for each triple `(j,m,l)`
  have key : ∀ p : Fin n × Fin n × Fin n, ∃ C : ℝ, 0 < C ∧
      Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ ζ p.1 p.2.1 p.2.2) Set.univ
        ≤ ENNReal.ofReal C
          * ∑ i, ∑ l', Work.CR.Flat.holderNorm k α (ζ i l') (Work.CR.Flat.polydisc 0 ρ) := by
    rintro ⟨j, m, l⟩
    set uts : Fin 3 → Work.NN.Core.Cn n → ℂ :=
      ![fun z => dbarCoord l χ z, fun z => dbarCoord j χ z, -(fun z => dbarCoord m χ z)]
      with huts
    set vts : Fin 3 → Work.NN.Core.Cn n → ℂ := ![ζ j m, ζ m l, ζ j l] with hvts
    have hu : ∀ t, ContDiff ℝ ⊤ (uts t) := by
      intro t
      fin_cases t
      · show ContDiff ℝ ⊤ (fun z => dbarCoord l χ z)
        exact hdχ_sm l
      · show ContDiff ℝ ⊤ (fun z => dbarCoord j χ z)
        exact hdχ_sm j
      · show ContDiff ℝ ⊤ (-(fun z => dbarCoord m χ z))
        exact (hdχ_sm m).neg
    have hus : ∀ t, HasCompactSupport (uts t) := by
      intro t
      fin_cases t
      · show HasCompactSupport (fun z => dbarCoord l χ z)
        exact hdχ_cs l
      · show HasCompactSupport (fun z => dbarCoord j χ z)
        exact hdχ_cs j
      · show HasCompactSupport (-(fun z => dbarCoord m χ z))
        exact (hdχ_cs m).neg
    have hu0 : ∀ t z, (∃ j, ρ j ≤ ‖z j‖) → uts t z = 0 := by
      intro t z hz
      fin_cases t
      · show dbarCoord l χ z = 0
        exact hdχ_van l z hz
      · show dbarCoord j χ z = 0
        exact hdχ_van j z hz
      · show (-(fun z => dbarCoord m χ z)) z = 0
        rw [Pi.neg_apply, hdχ_van m z hz, neg_zero]
    have hv : ∀ t, ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (vts t) (polydisc 0 ρ) := by
      intro t
      fin_cases t
      · show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ j m) (polydisc 0 ρ)
        exact hζ j m
      · show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ m l) (polydisc 0 ρ)
        exact hζ m l
      · show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ j l) (polydisc 0 ρ)
        exact hζ j l
    have hvf : ∀ t, holderNorm k α (vts t) (polydisc 0 ρ) ≠ ⊤ := by
      intro t
      fin_cases t
      · show holderNorm k α (ζ j m) (polydisc 0 ρ) ≠ ⊤
        exact hζf j m
      · show holderNorm k α (ζ m l) (polydisc 0 ρ) ≠ ⊤
        exact hζf m l
      · show holderNorm k α (ζ j l) (polydisc 0 ρ) ≠ ⊤
        exact hζf j l
    obtain ⟨C, hCpos, hC⟩ := holderNorm_sumMul_le_of_flat_supported (ι := Fin 3) hρ hα0 hα1
      uts hu hus hu0 vts hv hvf
    have hfun : (fun z => ∑ t : Fin 3, uts t z * vts t z) = Work.NN.Core.bmH χ ζ j m l := by
      funext z
      rw [Fin.sum_univ_three]
      simp only [huts, hvts, Work.NN.Core.bmH, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.neg_apply, neg_mul]
      ring
    rw [hfun] at hC
    have hsing : ∀ a b : Fin n, holderNorm k α (ζ a b) (polydisc 0 ρ)
        ≤ ∑ i, ∑ l', holderNorm k α (ζ i l') (polydisc 0 ρ) := by
      intro a b
      refine le_trans (Finset.single_le_sum
        (f := fun l' => holderNorm k α (ζ a l') (polydisc 0 ρ))
        (fun l' _ => bot_le) (Finset.mem_univ b)) ?_
      exact Finset.single_le_sum
        (f := fun i => ∑ l', holderNorm k α (ζ i l') (polydisc 0 ρ))
        (fun i _ => Finset.sum_nonneg fun l' _ => bot_le) (Finset.mem_univ a)
    refine ⟨3 * C + 1, by positivity, ?_⟩
    calc Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ ζ j m l) Set.univ
        ≤ ENNReal.ofReal C * ∑ t : Fin 3, holderNorm k α (vts t) (polydisc 0 ρ) := hC
      _ ≤ ENNReal.ofReal C * (((3 : ℕ) : ℝ≥0∞)
            * ∑ i, ∑ l', Work.CR.Flat.holderNorm k α (ζ i l') (polydisc 0 ρ)) := by
          refine mul_le_mul_right ?_ _
          calc ∑ t : Fin 3, holderNorm k α (vts t) (polydisc 0 ρ)
              ≤ ∑ _t : Fin 3, ∑ i, ∑ l',
                  Work.CR.Flat.holderNorm k α (ζ i l') (polydisc 0 ρ) := by
                refine Finset.sum_le_sum fun t _ => ?_
                fin_cases t
                · show holderNorm k α (ζ j m) (polydisc 0 ρ) ≤ _
                  exact hsing j m
                · show holderNorm k α (ζ m l) (polydisc 0 ρ) ≤ _
                  exact hsing m l
                · show holderNorm k α (ζ j l) (polydisc 0 ρ) ≤ _
                  exact hsing j l
            _ = ((3 : ℕ) : ℝ≥0∞) * ∑ i, ∑ l',
                  Work.CR.Flat.holderNorm k α (ζ i l') (polydisc 0 ρ) := by
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal (C * 3) * ∑ i, ∑ l',
            Work.CR.Flat.holderNorm k α (ζ i l') (polydisc 0 ρ) := by
          rw [show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) from (ENNReal.ofReal_natCast 3).symm,
            ← mul_assoc, ← ENNReal.ofReal_mul (p := C) (q := 3) hCpos.le]
      _ ≤ ENNReal.ofReal (3 * C + 1) * ∑ i, ∑ l',
            Work.CR.Flat.holderNorm k α (ζ i l') (polydisc 0 ρ) := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          linarith
  choose C1 hC1pos hC1 using key
  refine ⟨1 + ∑ p : Fin n × Fin n × Fin n, C1 p, ?_, ?_⟩
  · have h : 0 ≤ ∑ p : Fin n × Fin n × Fin n, C1 p :=
      Finset.sum_nonneg fun p _ => (hC1pos p).le
    linarith
  · intro j m l
    have h1 := hC1 (j, m, l)
    have h2 : C1 (j, m, l) ≤ 1 + ∑ p : Fin n × Fin n × Fin n, C1 p := by
      have h3 : C1 (j, m, l) ≤ ∑ p : Fin n × Fin n × Fin n, C1 p :=
        Finset.single_le_sum (fun p _ => (hC1pos p).le) (Finset.mem_univ _)
      linarith
    exact h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal h2) _)

end Work.NN.Core
