import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.HkIntegrand_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The `H^k`-integrand of a difference of two families, one angular slice at a time

The target `perz_HkIntegrand_diff` says: if the two families `V` (depending on a parameter
`s ∈ [0,δ]`) and `W` are smooth on the open quadrant and `ℋ^k`-honest, and if on *each* angular
slice (i.e. for each fixed `z ∈ Iz`) the integrals `∫_θ HkIntegrand α k (V s) z θ` and
`∫_θ HkIntegrand α k W z θ` are bounded by constants `Cz` (uniform in `s`), then the same is true
of the family of differences `s ↦ V s - W`.

The proof is the triangle inequality for `H^k`, slice by slice and parameter by parameter:

* on the open quadrant `(0,∞) × (0,π/2)`, `D_z^j D_θ^i (V s - W) = D_z^j D_θ^i (V s)
  - D_z^j D_θ^i W` (`mixed_sub_of_contDiffOn_six`, from `C^6`-smoothness on the open quadrant),
  so *every* summand of `HkIntegrand α k (V s - W)` is a square of a difference of the
  corresponding summands of `V s` and `W` and hence `≤ 2·(·)² + 2·(·)²`; the `if`-guards depend
  only on the indices.  Summing gives the pointwise bound
  `HkIntegrand α k (V s - W) z θ ≤ 2 HkIntegrand α k (V s) z θ + 2 HkIntegrand α k W z θ`
  (`HkIntegrand_sub_le`, proved separately, plus `HkIntegrand_sub_le_open` here).
* The two endpoints `θ = 0, π/2` and the radial endpoint `z = 0` are irrelevant: the former are
  null for `volume.restrict Iθ` (`ae_le_restrict_Iθ_of_forall_Ioo`), while at `z = 0` the radial
  weight `w 0 = 0` kills the whole integrand (`HkIntegrand_zero_z`), so the bound is trivial.
* Finally the slice integrals are compared with `MeasureTheory.integral_mono_of_nonneg`, which
  needs only `0 ≤ᵐ f`, an integrable majorant `g` and `f ≤ᵐ g` —— in particular *no* measurability
  or integrability of the difference integrand itself, which is why the (unproved here) honesty of
  the difference family is not needed.  The majorant is integrable by the two `HkMem` hypotheses,
  and its integral splits by linearity into `2∫(V s) + 2∫W ≤ 2 CzV + 2 CzW`.
-/

/-! ## The pointwise triangle inequality on the open quadrant -/

/-- **The triangle inequality for `HkIntegrand` on the open quadrant.**  For two functions that
are `C^6` on the open quadrant (equivalently, `SmoothOpen`, which gives all finite orders) the
`H^k`-integrand of the difference is at most twice the sum of the two integrands, for `k ≤ 6`.

The `C^6`-hypothesis is exactly what `mixed_sub_of_contDiffOn_six` needs, in order to replace
`D_z^j D_θ^i (A - B)` by the difference of the two separate derivatives at every point of the open
quadrant; the rest is the algebraic `HkIntegrand_sub_le`. -/
private lemma HkIntegrand_sub_le_open {α : ℝ} {k : ℕ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hk : k ≤ 6) (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hB : Work.FTS.EllipticEst.SmoothOpen B) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α k (fun z θ => A z θ - B z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k A z θ + 2 * Work.Spaces.HkIntegrand α k B z θ :=
  HkIntegrand_sub_le (G := fun z θ => A z θ - B z θ) fun j i hji =>
    Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six
      (by omega) hz hθ ((Work.FTS.EllipticEst.smoothOpen_iff_forall A).mp hA 6)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall B).mp hB 6)

/-! ## The radial endpoint `z = 0` -/

/-- At `z = 0` the whole `H^k`-integrand vanishes: the radial weight `w 0 = 0` kills every
summand of the pure `D_z`-sum, and the angular weight `Wt α 0 θ = w 0 · (·)` kills every summand
of the double sum. -/
private lemma HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]

/-! ## Almost-everywhere bounds on `Iθ` from bounds on the open interval -/

/-- An inequality that holds on `(0, π/2)` holds almost everywhere for `volume.restrict Iθ`,
the two endpoints being null. -/
private lemma ae_le_restrict_Iθ_of_forall_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f θ ≤ g θ) :
    f ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] g := by
  have hset : Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  exact h θ hθ

theorem perz_HkIntegrand_diff {α : ℝ} {k : ℕ} {δ : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hle : k ≤ 6)
    (hsmV : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (V s))
    (hsmW : Work.FTS.EllipticEst.SmoothOpen W)
    (hmemV : ∀ s ∈ Set.Icc 0 δ, Work.Spaces.HkMem α k (V s))
    (hmemW : Work.Spaces.HkMem α k W)
    (hperzV : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ s ∈ Set.Icc 0 δ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (V s) z θ) ≤ Cz)
    (hperzW : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, 0 ≤ Cz ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k W z θ) ≤ Cz) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ s ∈ Set.Icc 0 δ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ) ≤ Cz := by
  intro z hz
  obtain ⟨CzV, hCzV0, hCzV⟩ := hperzV z hz
  obtain ⟨CzW, hCzW0, hCzW⟩ := hperzW z hz
  refine ⟨2 * CzV + 2 * CzW, by linarith, ?_⟩
  intro s hs
  have hzle : (0 : ℝ) ≤ z := hz
  rcases lt_or_eq_of_le hzle with hzpos | hz0
  · -- the generic case `z > 0`: compare the two slice integrands a.e. on `Iθ`
    have hIntA : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (V s) z θ)
        Work.Spaces.Iθ := (hmemV s hs).1 z hz
    have hIntB : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k W z θ)
        Work.Spaces.Iθ := hmemW.1 z hz
    have hIntF : MeasureTheory.IntegrableOn
        (fun θ => 2 * Work.Spaces.HkIntegrand α k (V s) z θ
          + 2 * Work.Spaces.HkIntegrand α k W z θ) Work.Spaces.Iθ :=
      (hIntA.const_mul 2).add (hIntB.const_mul 2)
    have hae : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => 2 * Work.Spaces.HkIntegrand α k (V s) z θ
          + 2 * Work.Spaces.HkIntegrand α k W z θ) :=
      ae_le_restrict_Iθ_of_forall_Ioo fun θ hθ => HkIntegrand_sub_le_open hle (hsmV s hs) hsmW hzpos hθ
    have hnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (0 : ℝ) ≤ Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ :=
      Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ
    have hmono : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ)
        ≤ (∫ θ in Work.Spaces.Iθ, 2 * Work.Spaces.HkIntegrand α k (V s) z θ
            + 2 * Work.Spaces.HkIntegrand α k W z θ) :=
      MeasureTheory.integral_mono_of_nonneg hnn hIntF hae
    have hsplit : (∫ θ in Work.Spaces.Iθ, 2 * Work.Spaces.HkIntegrand α k (V s) z θ
            + 2 * Work.Spaces.HkIntegrand α k W z θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (V s) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k W z θ) := by
      rw [MeasureTheory.integral_add (hIntA.const_mul 2) (hIntB.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ)
        ≤ (∫ θ in Work.Spaces.Iθ, 2 * Work.Spaces.HkIntegrand α k (V s) z θ
            + 2 * Work.Spaces.HkIntegrand α k W z θ) := hmono
      _ = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (V s) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k W z θ) := hsplit
      _ ≤ 2 * CzV + 2 * CzW := by linarith [hCzV s hs, hCzW]
  · -- the degenerate case `z = 0`: the integrand is identically zero
    rw [← hz0]
    have hzero : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) 0 θ) = 0 := by
      simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
    rw [hzero]
    linarith

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
