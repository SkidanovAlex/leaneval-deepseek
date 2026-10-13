/-
# `Work.FTS_LocDatum3a.contDiffOn_Fstar_Jeps_sep`

The angular moment `F_*` of the log-coordinate mollification of a separable datum is `C^∞` on
`(0,∞)`.

## The statement

For an admissible smooth mollifier kernel `ρ` (`IsSmoothKernel ρ`), `ε > 0`, `0 < α` and a
radial factor `a` which is `C^∞` on `(0,∞)`, the angular moment

  `F_*(J_ε f)(z) = ∫_θ J_ε f (z,θ) · sin θ cos²θ dθ`,   `f z θ = a z · Γ(θ)`

is `C^m` on `(0,∞)` for every `m`.  This is the `fsm` clause of `Work.FTS.ClassC.ClassC` for the
separable datum `locR α L β(z)·Γ(θ)` of the localised-data chapter.

## The route

`J_ε` (the log-coordinate mollifier of `Submission/Work/FTS/StrongEps/Basic.lean`) is `C^∞` on
the *open* quadrant `Q0 = (0,∞) × (0,π/2)` (`SmoothOpen_Jeps`), but it is **not** smooth across
the boundary angles `θ = 0, π/2`: the datum behaves like `θ^{α/3}` there and `J_ε` is defined to
be `0` outside the open quadrant.  So the classical "differentiate under the `θ`-integral" route
cannot be run in the variable `z` directly (the domination hypotheses would fail at the
endpoints).  Instead we use the log coordinate `s = log z`:

* `D_z = z ∂_z` is `∂_s`, and `D_z^k (J_ε f) = J_ε (D_z^k f)` on the open quadrant
  (`DzIter_Jeps_of_smooth`), so the `D_z`-iterates of `J_ε f` are again *mollifications*, and
  they are uniformly bounded on `[s₀-1,s₀+1] × Iθ` by the bounds on the data
  (`abs_Jeps_le_sup`); at the boundary angles both sides vanish identically;
* `contDiffOn_integral_Iθ_univ` then shows, by induction on the order and differentiation under
  the `θ`-integral (DCT + `hasDerivAt_integral_of_dominated_loc_of_deriv_le`), that
  `s ↦ ∫_θ F (e^s) θ · sinθcos²θ dθ` is `C^∞` on all of `ℝ`;
* composing with `log` (smooth on `(0,∞)`) and using `e^{log z} = z` for `z > 0` gives the
  result.

The two local-uniform bounds on `D_z^k (J_ε f)` used along the way are
`FJS.radial_mul_Gam_DzIter_bound` (for the separable datum, on compact subintervals of `(0,∞)`)
and `FJS.DzIter_Jeps_bound` (transport through `J_ε`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace FJS

/-! ## Elementary facts about the angular interval `Iθ` -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact measurableSet_Icc

theorem isCompact_Iθ : IsCompact Work.Spaces.Iθ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact isCompact_Icc

theorem mem_Iθ_zero : (0 : ℝ) ∈ Work.Spaces.Iθ :=
  show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) from ⟨le_refl 0, by linarith [Real.pi_pos]⟩

theorem isFiniteMeasure_restrict_Iθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact lt_top_iff_ne_top.mpr isCompact_Iθ.measure_ne_top⟩

/-- `volume.restrict Iθ` may be replaced by `volume.restrict (0,π/2)`: the two endpoints form a
null set. -/
theorem volume_restrict_Iθ :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

/-- Almost-everywhere statements w.r.t. `volume.restrict Iθ` may be checked on the open
interval `(0,π/2)`. -/
theorem eventually_restrict_Iθ {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [volume_restrict_Iθ]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => h θ hθ)

/-- Almost-everywhere statements w.r.t. `volume.restrict Iθ` may be checked on all of `Iθ`. -/
theorem eventually_restrict_Iθ_of_Iθ {p : ℝ → Prop}
    (h : ∀ θ ∈ Work.Spaces.Iθ, p θ) : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl] at h ⊢
  exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => h θ hθ)

/-! ## The angular weights `sin θ cos²θ` and `Γ(θ)` -/

theorem continuousOn_sinCos2 : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
  (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn

theorem abs_sinCos2_le_one : ∀ θ ∈ Work.Spaces.Iθ, |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul (Real.sin_le_one θ) hc (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  rw [Work.Elliptic.sinCos2, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
  exact hle

/-- `|Γ(θ)| ≤ 1` on `Iθ` for `0 < α`. -/
theorem abs_Gam_le_one {α : ℝ} (hα : 0 < α) :
    ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ 1 := by
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have h0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul (Real.sin_le_one θ) hc (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  rw [Work.Spaces.Gam, abs_of_nonneg (Real.rpow_nonneg h0 _)]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) ≤ 1 ^ (α / 3) :=
        Real.rpow_le_rpow h0 hle (by linarith)
    _ = 1 := Real.one_rpow _

/-! ## The generic parametric-integral lemma -/

/-- `F` pulled back to the log coordinate `s = log z`. -/
def logPullZ (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun s θ => F (Real.exp s) θ

/-- `D_z^k F` pulled back to the log coordinate `s = log z`. -/
def logPullDz (F : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun s θ => Work.Spaces.DzIter k F (Real.exp s) θ

/-- **Smoothness of a parametric integral in the log variable.**

Let `Φ k` be the `k`-th `s`-derivative of `Φ 0` on `ℝ × (0,π/2)` (in the sense that the slices
have the stated derivatives), with every `Φ k` `C^∞` on `ℝ × (0,π/2)` and uniformly bounded on
`[s₀-1,s₀+1] × Iθ` for every `s₀`.  Then `s ↦ ∫_θ Φ 0 s θ · φ θ dθ` is `C^∞` on `ℝ`.

The proof is the textbook induction: the parametric integral of `Φ k` is `C^n`, its derivative is
the parametric integral of `Φ (k+1)` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the
constant bound on the slab `[s₀-1,s₀+1]`), and the base case is dominated convergence
(`tendsto_integral_filter_of_norm_le_const`); a.e. statements are checked on the open interval
`(0,π/2)`, which is enough because both endpoints are null. -/
theorem contDiffOn_integral_Iθ_univ {Φ : ℕ → ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ n (Function.uncurry (Φ k))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hderiv : ∀ (k : ℕ) (s θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      HasDerivAt (fun s' => Φ k s' θ) (Φ (k + 1) s θ) s)
    (hbdd : ∀ (k : ℕ) (s₀ : ℝ), ∃ C, ∀ s, |s - s₀| ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Φ k s θ| ≤ C)
    (hφ : ContinuousOn φ Work.Spaces.Iθ) (hφb : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ 1) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun s => ∫ θ in Work.Spaces.Iθ, Φ 0 s θ * φ θ) Set.univ := by
  -- continuity of the slices in the parameter
  have hslice : ∀ (k : ℕ) {θ : ℝ}, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      Continuous (fun s : ℝ => Φ k s θ) := by
    intro k θ hθ
    have hf : ContDiffOn ℝ 0 (fun s : ℝ => (s, θ)) (Set.univ : Set ℝ) :=
      (contDiffOn_zero (𝕜 := ℝ)).mpr (continuous_id.prodMk continuous_const).continuousOn
    have h : ContDiffOn ℝ 0 (fun s : ℝ => Φ k s θ) Set.univ :=
      (hsmooth k 0).comp hf (fun s _ => ⟨Set.mem_univ s, hθ⟩)
    exact continuousOn_univ.mp ((contDiffOn_zero (𝕜 := ℝ)).mp h)
  -- a.e. strong measurability of the slices
  have haesm : ∀ (k : ℕ) (s : ℝ),
      AEStronglyMeasurable (fun θ : ℝ => Φ k s θ * φ θ) (volume.restrict Work.Spaces.Iθ) := by
    intro k s
    have hc1 : ContinuousOn (fun θ : ℝ => Φ k s θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
      have hf : ContDiffOn ℝ 0 (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
        (contDiffOn_zero (𝕜 := ℝ)).mpr (continuous_const.prodMk continuous_id).continuousOn
      have h := (hsmooth k 0).comp hf (fun θ hθ => ⟨Set.mem_univ s, hθ⟩)
      exact (contDiffOn_zero (𝕜 := ℝ)).mp (by
        show ContDiffOn ℝ 0 (fun θ : ℝ => Φ k s θ) (Set.Ioo (0 : ℝ) (π / 2)); exact h)
    have hc2 : ContinuousOn φ (Set.Ioo (0 : ℝ) (π / 2)) :=
      hφ.mono fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Φ k s θ * φ θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      (hc1.mul hc2).aestronglyMeasurable measurableSet_Ioo
    rwa [volume_restrict_Iθ]
  -- the base case: continuity of every integral
  have hcont : ∀ k : ℕ, Continuous (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ) := by
    intro k
    rw [continuous_iff_continuousAt]
    intro s₀
    obtain ⟨C, hC⟩ := hbdd k s₀
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC s₀ (by simp) 0 mem_Iθ_zero)
    refine tendsto_integral_filter_of_norm_le_const
      (F := fun s θ => Φ k s θ * φ θ) (f := fun θ => Φ k s₀ θ * φ θ) (l := 𝓝 s₀) ?_ ?_ ?_
    · exact Eventually.of_forall fun s => haesm k s
    · refine ⟨C, ?_⟩
      filter_upwards [isOpen_Ioo.mem_nhds (show s₀ ∈ Set.Ioo (s₀ - 1) (s₀ + 1) from
        ⟨by linarith, by linarith⟩)] with s hs
      refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      have hs1 : |s - s₀| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul (hC s hs1 θ hθ) (hφb θ hθ) (abs_nonneg _) hCnn)
        (le_of_eq (mul_one C))
    · refine eventually_restrict_Iθ fun θ hθ => ?_
      exact ((hslice k hθ).continuousAt.mul continuousAt_const).tendsto
  -- differentiation under the integral sign
  have hkey : ∀ (k : ℕ) (s₀ : ℝ),
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Φ (k + 1) s₀ θ * φ θ) s₀ := by
    intro k s₀
    obtain ⟨C, hC⟩ := hbdd (k + 1) s₀
    obtain ⟨C₀, hC₀⟩ := hbdd k s₀
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC s₀ (by simp) 0 mem_Iθ_zero)
    have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ s₀ (by simp) 0 mem_Iθ_zero)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
      (bound := fun _ : ℝ => C)
      (F := fun s θ => Φ k s θ * φ θ) (F' := fun s θ => Φ (k + 1) s θ * φ θ)
      (x₀ := s₀) (s := Set.Ioo (s₀ - 1) (s₀ + 1))
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun s => haesm k s
    · refine MeasureTheory.Integrable.of_bound (haesm k s₀) C₀ ?_
      refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      have h1 : |Φ k s₀ θ| ≤ C₀ := hC₀ s₀ (by simp) θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul h1 (hφb θ hθ) (abs_nonneg _) hC₀nn) (le_of_eq (mul_one C₀))
    · exact haesm (k + 1) s₀
    · refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      intro s hs
      have hs1 : |s - s₀| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      show ‖Φ (k + 1) s θ * φ θ‖ ≤ C
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul (hC s hs1 θ hθ) (hφb θ hθ) (abs_nonneg _) hCnn)
        (le_of_eq (mul_one C))
    · exact integrable_const C
    · refine eventually_restrict_Iθ fun θ hθ => ?_
      intro s _
      exact (hderiv k s θ hθ).mul_const (φ θ)
  -- the induction on the order
  have hmain : ∀ (m : ℕ) (k : ℕ),
      ContDiffOn ℝ m (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ) Set.univ := by
    intro m
    induction m with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).mpr (hcont k).continuousOn
    | succ m ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ)
        (n := ((m : ℕ) : WithTop ℕ∞)) (s := Set.univ) isOpen_univ).2 ⟨?_, ?_, ?_⟩
      · exact fun s _ => (hkey k s).differentiableAt.differentiableWithinAt
      · intro h; exact absurd h (by simp)
      · refine (ih (k + 1)).congr fun s _ => ?_
        exact (hkey k s).deriv
  intro m
  simpa using hmain m 0

/-! ## From `C^∞` on the quadrant plus `D_z`-bounds to `F_*`-smoothness -/

/-- **`F_*` is `C^∞` on `(0,∞)`** for a datum `F` which is `C^∞` on the open quadrant and whose
`D_z`-iterates, pulled back to the log coordinate, are locally bounded on `Iθ`. -/
theorem contDiffOn_Fstar_of_dzBound {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hb : ∀ (k : ℕ) (s₀ : ℝ), ∃ C, ∀ s, |s - s₀| ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter k F (Real.exp s) θ| ≤ C) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  have hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ n (Function.uncurry (logPullDz F k))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    intro k n
    have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter k F))
        Work.FTS.EllipticEst.Q0 := (hF.DzIter k).forall n
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      ContDiffOn.prodMk
        ((((Real.contDiff_exp.comp contDiff_fst).contDiffOn).of_le le_top).mono
          (Set.subset_univ _))
        contDiffOn_snd
    have h3 := h1.comp h2 (fun p hp => ⟨Real.exp_pos _, hp.2⟩)
    show ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.DzIter k F (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
    exact h3
  have hderiv : ∀ (k : ℕ) (s θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      HasDerivAt (fun s' => logPullDz F k s' θ) (logPullDz F (k + 1) s θ) s := by
    intro k s θ hθ
    have h1 : HasDerivAt (fun z' => Work.Spaces.DzIter k F z' θ)
        (Work.Spaces.pz (Work.Spaces.DzIter k F) (Real.exp s) θ) (Real.exp s) :=
      hF.hasDerivAt_slice_DzIter k hθ (Real.exp_pos s)
    have h2 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have h3 := h1.comp s h2
    have h4 : Work.Spaces.pz (Work.Spaces.DzIter k F) (Real.exp s) θ * Real.exp s
        = Work.Spaces.DzIter (k + 1) F (Real.exp s) θ := by
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      ring
    rw [h4] at h3
    show HasDerivAt (fun s' : ℝ => Work.Spaces.DzIter k F (Real.exp s') θ)
      (Work.Spaces.DzIter (k + 1) F (Real.exp s) θ) s
    exact h3
  have hmain := contDiffOn_integral_Iθ_univ (Φ := logPullDz F) (φ := Work.Elliptic.sinCos2)
    hsmooth hderiv hb continuousOn_sinCos2 abs_sinCos2_le_one
  intro m
  have h1 : ContDiff ℝ m
      (fun s => ∫ θ in Work.Spaces.Iθ, logPullZ F s θ * Work.Elliptic.sinCos2 θ) :=
    contDiffOn_univ.mp (hmain m)
  have h2 : ContDiffOn ℝ m
      ((fun s => ∫ θ in Work.Spaces.Iθ, logPullZ F s θ * Work.Elliptic.sinCos2 θ) ∘ Real.log)
      (Set.Ioi 0) :=
    h1.comp_contDiffOn ((Real.contDiffOn_log (n := m)).mono fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)
  refine h2.congr fun z hz => ?_
  have hz' : Real.exp (Real.log z) = z := Real.exp_log hz
  simp only [Function.comp_def, logPullZ, hz', Work.Elliptic.Fstar]

/-! ## The separable datum `a(z)·Γ(θ)` -/

/-- The separable datum `(z,θ) ↦ a z · Γ(θ)`. -/
abbrev sepDatum (a : ℝ → ℝ) (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => a z * Work.Spaces.Gam α θ

theorem smoothOpen_sepDatum {α : ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (sepDatum a α) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have ha_n : ContDiffOn ℝ n a (Set.Ioi 0) := contDiffOn_iff_forall_nat_le.mp ha n le_top
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 := by
    have h := ha_n.comp (contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0))
      (fun p hp => hp.1)
    show ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0
    exact h
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      ((((Real.contDiff_sin.comp contDiff_snd).mul
        ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top).mono
        (Set.subset_univ _)
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
        (by linarith [h1', Real.pi_pos]) (by linarith [h2', Real.pi_pos])
      have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [h1', Real.pi_pos], h2'⟩
      positivity
    simpa only [Work.Spaces.Gam] using hbase.rpow_const_of_ne hne
  have h3 := h1.mul h2
  show ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1 * Work.Spaces.Gam α p.2)
    Work.FTS.EllipticEst.Q0
  exact h3

theorem exp_mul_exp_neg (x ε : ℝ) : Real.exp x * Real.exp (-ε) = Real.exp (x - ε) := by
  rw [← Real.exp_add, sub_eq_add_neg]

theorem exp_mul_exp_pos (x ε : ℝ) : Real.exp x * Real.exp ε = Real.exp (x + ε) := by
  rw [← Real.exp_add]

/-! ## Local uniform bounds for the `D_z`-iterates -/

/-- `D_z^k` of a separable datum `a(z)Γ(θ)` only differs in the radial factor. -/
theorem DzIter_sepDatum (α : ℝ) (a : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.DzIter k (sepDatum a α)
      = fun z θ => Work.Spaces.DzIter k (fun z _ => a z) z θ * Work.Spaces.Gam α θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_mul_const_field']
    ring

/-- The one-variable iterate `(z d/dz)^k a`. -/
def dzA (a : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => a
  | k + 1 => fun z => z * deriv (dzA a k) z

@[simp] theorem dzA_zero (a : ℝ → ℝ) : dzA a 0 = a := rfl

@[simp] theorem dzA_succ (a : ℝ → ℝ) (k : ℕ) :
    dzA a (k + 1) = fun z => z * deriv (dzA a k) z := rfl

/-- `D_z^k` of a radial datum is the one-variable iterate `(z d/dz)^k`. -/
theorem DzIter_radial_eq (a : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter k (fun z _ => a z) z θ = dzA a k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, dzA_succ]
    have hfun : (fun z' => Work.Spaces.DzIter k (fun z _ => a z) z' θ) = dzA a k :=
      funext fun z' => ih z'
    rw [hfun]

/-- `(z d/dz)^k a` is `C^n` on `(0,∞)` for every `n`, when `a` is `C^∞` there. -/
theorem contDiffOn_dzA {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    ∀ (k n : ℕ), ContDiffOn ℝ n (dzA a k) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero =>
    intro n
    simpa only [dzA_zero] using contDiffOn_iff_forall_nat_le.mp ha n le_top
  | succ k ih =>
    intro n
    have h1 : ContDiffOn ℝ (((n : ℕ) : WithTop ℕ∞) + 1) (dzA a k) (Set.Ioi 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ih (n + 1)
    have h2 : ContDiffOn ℝ n (deriv (dzA a k)) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))
        isOpen_Ioi).mp h1).2.2
    have h3 : ContDiffOn ℝ n (fun z => z * deriv (dzA a k) z) (Set.Ioi 0) :=
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))).mul h2
    simpa only [dzA_succ] using h3

/-- **The `D_z`-iterates of the separable datum are locally uniformly bounded on `Iθ`.** -/
theorem radial_mul_Gam_DzIter_bound {α : ℝ} (hα : 0 < α) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) (k : ℕ) {z₁ z₂ : ℝ}
    (hz₁ : 0 < z₁) :
    ∃ C, ∀ z, z₁ ≤ z → z ≤ z₂ → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k (fun z θ => a z * Work.Spaces.Gam α θ) z θ| ≤ C := by
  have hcont : ContinuousOn (dzA a k) (Set.Icc z₁ z₂) :=
    ((contDiffOn_dzA ha k 0).mono
      (fun z hz => lt_of_lt_of_le hz₁ hz.1)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|, fun z hz1 hz2 θ hθ => ?_⟩
  simp only [DzIter_sepDatum, DzIter_radial_eq, abs_mul]
  have h1 : |dzA a k z| ≤ |C| := by
    have h := hC z ⟨hz1, hz2⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self C)
  calc |dzA a k z| * |Work.Spaces.Gam α θ| ≤ |C| * 1 :=
        mul_le_mul h1 (abs_Gam_le_one hα θ hθ) (abs_nonneg _) (abs_nonneg _)
    _ = |C| := mul_one _

/-- A function vanishing on a whole `z`-line has vanishing `D_z`-iterates on that line. -/
theorem DzIter_eq_zero_of_slice_zero {g : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, g z θ = 0) :
    ∀ (k : ℕ) (z : ℝ), Work.Spaces.DzIter k g z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' => Work.Spaces.DzIter k g z' θ) = fun _ => 0 := funext ih
    rw [hfun, deriv_const, mul_zero]

/-- **`J_ε` preserves local uniform bounds on the `D_z`-iterates.**

If `|D_z^k f| ≤ M` on the slightly enlarged rectangle `[a e^{-ε}, b e^{ε}] × [0, π/2]`, then
`|D_z^k (J_ε f)| ≤ max M 0` on `[a, b] × [0, π/2]`.

On the open quadrant this is the commutation `D_z^k ∘ J_ε = J_ε ∘ D_z^k`
(`DzIter_Jeps_of_smooth`) followed by the elementary domination of the convolution by the
supremum over the shift region (`abs_Jeps_le_sup`): a shift `p` with `|p₁| ≤ ε` sends `z ∈ [a,b]`
into `zShift z p₁ = z e^{-p₁} ∈ [a e^{-ε}, b e^{ε}]`, and the angular shift `thShift θ p₂` stays
in the open quadrant.  On the boundary `θ = 0, π/2` both sides vanish identically in `z`. -/
theorem DzIter_Jeps_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) {a b M : ℝ}
    (ha : 0 < a)
    (hM : ∀ z, a * Real.exp (-ε) ≤ z → z ≤ b * Real.exp ε → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k f z θ| ≤ M) :
    ∃ C, ∀ z, a ≤ z → z ≤ b → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z θ| ≤ C := by
  refine ⟨max M 0, fun z hza hzb θ hθ => ?_⟩
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  · have hcomm : Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z θ :=
      Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε hf k
        (show (z, θ) ∈ Work.FTS.StrongEps.Quad from ⟨hzpos, hθo⟩)
    rw [hcomm]
    refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ hε hzpos hθo (fun p hp1 hp2 => ?_)
      (le_max_right _ _)
    obtain ⟨hp1, hp1'⟩ := abs_le.mp hp1
    have hbpos : 0 < b := lt_of_lt_of_le hzpos hzb
    have hzlo : a * Real.exp (-ε) ≤ Work.FTS.StrongEps.zShift z p.1 := by
      rw [Work.FTS.StrongEps.zShift]
      exact mul_le_mul hza (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (le_of_lt hzpos)
    have hzhi : Work.FTS.StrongEps.zShift z p.1 ≤ b * Real.exp ε := by
      rw [Work.FTS.StrongEps.zShift]
      exact mul_le_mul hzb (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (le_of_lt hbpos)
    have hθin : Work.FTS.StrongEps.thShift θ p.2 ∈ Work.Spaces.Iθ :=
      let h := Work.FTS.StrongEps.thShift_mem hθo
      ⟨le_of_lt h.1, le_of_lt h.2⟩
    exact le_trans (hM _ hzlo hzhi _ hθin) (le_max_left _ _)
  · have hzline : ∀ z' : ℝ, Work.FTS.StrongEps.Jeps ρ ε f z' θ = 0 :=
      fun z' => Work.FTS.StrongEps.Jeps_eq_zero_of_theta ρ ε f (fun hc => hθo hc)
    rw [DzIter_eq_zero_of_slice_zero hzline k z, abs_zero]
    exact le_max_right _ _

end FJS

open FJS

theorem contDiffOn_Fstar_Jeps_sep {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 0 < α)
    {a : ℝ → ℝ} (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => a z * Work.Spaces.Gam α θ)))
      (Set.Ioi 0) := by
  have hmoll : Work.FTS.StrongEps.IsMollKernel ρ := hρ.moll
  have hf : Work.FTS.EllipticEst.SmoothOpen (sepDatum a α) := smoothOpen_sepDatum ha
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε (sepDatum a α)) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
      Work.FTS.StrongEps.SmoothOpen_Jeps ρ hmoll hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (sepDatum a α)).mp hf) n
  refine contDiffOn_Fstar_of_dzBound (F := Work.FTS.StrongEps.Jeps ρ ε (sepDatum a α)) hF ?_
  intro k s₀
  obtain ⟨M, hM⟩ := radial_mul_Gam_DzIter_bound (α := α) hα ha k
    (z₁ := Real.exp (s₀ - 1 - ε)) (z₂ := Real.exp (s₀ + 1 + ε)) (Real.exp_pos _)
  have hMex : ∀ z, Real.exp (s₀ - 1) * Real.exp (-ε) ≤ z →
      z ≤ Real.exp (s₀ + 1) * Real.exp ε →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter k (sepDatum a α) z θ| ≤ M := by
    intro z hz1 hz2 θ hθ
    refine hM z ?_ ?_ θ hθ
    · rw [exp_mul_exp_neg] at hz1; exact hz1
    · rw [exp_mul_exp_pos] at hz2; exact hz2
  obtain ⟨C, hC⟩ := DzIter_Jeps_bound (f := sepDatum a α) hmoll hε hf k
    (a := Real.exp (s₀ - 1)) (b := Real.exp (s₀ + 1)) (Real.exp_pos _) hMex
  exact ⟨C, fun s hs θ hθ => hC (Real.exp s)
    (Real.exp_le_exp_of_le (by linarith [(abs_le.mp hs).1]))
    (Real.exp_le_exp_of_le (by linarith [(abs_le.mp hs).2])) θ hθ⟩

end Work.FTS_LocDatum3a
