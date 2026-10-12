import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.AprioriPieces
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.rPsi_eq_zero_of_normB_eq_zero`

**The degenerate-state clause of the state-level remainder `R_Ψ` (FS step 2).**

`R_Ψ = RPsiB h M 1 μ ℓ d Φ` is the configuration integral over the interior set
`I₋ = interiorSet ℓ d μ` of `w1MassB u` times the box integral

`∫_{abox n ℓ} (Φ x)² · psiWeight c μ (nCountB M ℓ d u x / chiMass M ℓ d u)`.

If the *boxed* `L²`-norm square `normB v μ n Φ = ∫_{abox n ℓ} (Φ x)²` vanishes,
then `R_Ψ = 0`.  (`BoxState` carries no support condition, so a state may vanish
on the box and be non-zero outside it; the vanishing of the boxed norm is the
only information available.)

## Route

The mathematical content is the general statement
`RPsiB_eq_zero_of_sqNormB_eq_zero`, with *free* parameters `M, c, μ, ℓ, d` and an
arbitrary continuous state `Φ : X n → ℝ`: if `sqNormB n ℓ Φ = 0` then
`RPsiB h M c μ ℓ d Φ = 0`.  Writing `S := abox n ℓ` and
`w u x := psiWeight c μ (nCountB M ℓ d u x / chiMass M ℓ d u)`, it suffices to
show that the *inner* integral vanishes for every `u`, since then the outer
integrand `w1MassB h M ℓ d u * (inner u)` is identically zero.

* `n = 0`: the count `nCountB M ℓ d u x = Σ_{i : Fin 0} … = 0` is constant, so
  `w u x = w u 0` is independent of `x` and `MeasureTheory.integral_mul_const`
  gives `∫_S (Φ x)² * w u 0 = (∫_S (Φ x)²) * w u 0 = 0`.
* `n ≥ 1`, `ℓ ≤ 0`: the box is null.  Indeed `abox n ℓ ⊆ abox n 0` — for
  `ℓ ≤ 0` the interval `Icc (−ℓ/2) (ℓ/2)` forces each coordinate to be `0`, so
  `y ∈ acube ℓ → y ∈ acube 0` — and `volume (abox n 0) = ofReal ((0³)^n) = 0`
  by `abox_volume`.  Hence `MeasureTheory.setIntegral_measure_zero`.
* `n ≥ 1`, `0 < ℓ`: the boxed norm square is the integral of a nonnegative
  continuous function over the box, so
  `Sector.eq_zero_on_abox_of_sqNormB_eq_zero` makes `Φ` vanish *pointwise* on
  `abox n ℓ`, and each summand of the inner integral is `0² * w = 0`
  (`MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`).

The target then follows by specialising `M, c, μ, ℓ, d` to FS's parameters
`(paramsAt μ (a v)).M`, `1`, `μ`, `sideAt μ (a v)`, `(paramsAt μ (a v)).d`
(note that `RPsi` *is* `RPsiB` at those parameters, by definition).

The statement deliberately carries no positivity hypothesis on the scattering
length `a v` (only `0 < μ`): the `ℓ ≤ 0` clause above covers that case, and no
`ℓ > 0` is available from the hypotheses alone.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`R_Ψ` vanishes on states with vanishing boxed norm square** (general
parameters).  For an arbitrary continuous `Φ : X n → ℝ` with
`sqNormB n ℓ Φ = ∫_{abox n ℓ} Φ² = 0`, the state-level remainder `RPsiB` at any
parameters `M, c, μ, ℓ, d` vanishes. -/
lemma RPsiB_eq_zero_of_sqNormB_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {c μ ℓ d : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hnorm : Work.BoseKinLoc.sqNormB n ℓ Φ = 0) :
    Work.BoseFixB1.RPsiB h M c μ ℓ d Φ = 0 := by
  rw [Work.BoseFixB1.RPsiB]
  -- the inner integral vanishes for every `u`
  have hinner : ∀ u : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight c μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)) = 0 := by
    intro u
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: the density weight is constant in the configuration
      subst hn
      have hcount : ∀ x : Submission.BoseGases.X 0,
          Work.BoseFixB1.nCountB M ℓ d u x = 0 := by
        intro x
        simp [Work.BoseFixB1.nCountB]
      simp_rw [hcount]
      rw [MeasureTheory.integral_mul_const]
      rw [show (∫ x in Submission.BoseGases.abox 0 ℓ, (Φ x) ^ 2) = 0 from hnorm]
      ring
    · -- `n ≥ 1`
      rcases le_or_gt ℓ 0 with hle | hpos
      · -- `ℓ ≤ 0`: the box is a null set
        have hvol : (volume : Measure (Submission.BoseGases.X n))
            (Submission.BoseGases.abox n ℓ) = 0 := by
          -- the box sits inside the degenerate box `abox n 0`
          have hsub : Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n 0 := by
            intro x hx
            rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
            intro i
            rw [Submission.BoseGases.mem_acube_iff]
            intro m
            have h1 : x i ∈ Submission.BoseGases.acube ℓ := hx i
            rw [Submission.BoseGases.mem_acube_iff] at h1
            have h2 := h1 m
            rw [Set.mem_Icc] at h2 ⊢
            constructor <;> linarith [h2.1, h2.2, hle]
          -- and the degenerate box is null for `n ≥ 1`
          have h0 : (volume : Measure (Submission.BoseGases.X n))
              (Submission.BoseGases.abox n 0) = 0 := by
            rw [Submission.BoseGases.abox_volume n 0 le_rfl]
            simp [hn.ne']
          exact measure_mono_null hsub h0
        exact MeasureTheory.setIntegral_measure_zero _ hvol
      · -- `0 < ℓ`: the state vanishes pointwise on the box
        have hΦ0 : ∀ x ∈ Submission.BoseGases.abox n ℓ, Φ x = 0 :=
          Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hpos hΦc hnorm
        exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
          (fun x hx => by rw [hΦ0 x hx]; ring)
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    (fun u _ => by rw [hinner u, mul_zero])

theorem rPsi_eq_zero_of_normB_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hnorm : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0) :
    Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
  have hnorm' : Work.BoseKinLoc.sqNormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
    simpa [Work.BoseBoxFix.normB] using hnorm
  exact RPsiB_eq_zero_of_sqNormB_eq_zero Φ.contDiff.continuous hnorm'

end Work.BoseFixB1B
