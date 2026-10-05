import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.lagData_per

/-!
# B5: smoothness of the assembled family at `x = -√2` is invariant under `t ↦ t + 2πN`

The assembled family `ℓ τ (x,t) = lagPt D.W D.Γc D.Ac D.rho τ x t` is only *quasi*-periodic in
`t` (`lagData_per`): `ℓ τ x (t + 2π) = Tk 1 (ℓ τ x t)`, where `Tk k` is the shift of the angle
`q₂` by `2πk`.  Iterating, `ℓ τ x (t + 2πn) = Tk n (ℓ τ x t)` for every `n : ℕ`
(`lagData_quasiPer_nat` below).

Since `Tk k` is a smooth coordinate change, this means that `ContDiffWithinAt` of `ℓ` at
`(τ₀, (-√2, t₀))` is *equivalent* to `ContDiffWithinAt` at `(τ₀, (-√2, t₀ + 2πn))`, which is why
the junction lemma `lagData_smooth_at_negSqrt2` may be proved at an arbitrary (convenient)
representative of the `t`-orbit.

The proof is a two-step composition with the *global* identity
`ℓ = Tk (-n) ∘ ℓ ∘ (t ↦ t + 2πn)`:
* precomposing `ℓ` with the (smooth) shift `Φ (τ,x,t) = (τ, x, t + 2πn)` keeps the set
  `Icc 0 1 ×ˢ univ ×ˢ univ` invariant, so `ContDiffWithinAt` transfers from `Φ p₀` to `p₀`;
* postcomposing with `Tk (-n)`, which is smooth everywhere, restores `ℓ` pointwise.
-/

namespace Work.RPB.B5

open RectangularPegProblem
open Complex Real
open scoped ContDiff

-- the hypotheses `hτ₀` (and, in the two statements below, `τ₀ ∈ Icc 0 1`) are part of the
-- requested interface but are not needed: only the invariance of the `τ`-slab under the shift
-- `Φ` is used.
set_option linter.unusedVariables false

/-- `Tk k`, the shift `q₂ ↦ q₂ + 2πk` of the angle, is smooth (an affine coordinate change). -/
private theorem contDiff_Tk_shift (n : ℕ) (k : ℤ) : ContDiff ℝ n (Work.RPV.Tk k) := by
  unfold Work.RPV.Tk
  fun_prop

/-- Quasi-periodicity of `lagPt` in `t` for integer multiples of `2π`: shifting `t` by `2πn`
applies the angle shift `Tk n`.  This is the `n`-fold iterate of `lagData_per`. -/
theorem lagData_quasiPer_nat (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) (n : ℕ)
    (τ x t : ℝ) :
    Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x (t + 2 * Real.pi * (n : ℝ))
      = Work.RPV.Tk (n : ℤ) (Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t) := by
  induction n with
  | zero => simp [Work.RPV.Tk_zero]
  | succ k ih =>
    rw [Nat.cast_succ]
    rw [show t + 2 * Real.pi * ((k : ℝ) + 1)
          = (t + 2 * Real.pi * (k : ℝ)) + 2 * Real.pi by ring]
    rw [Work.RPB.B5.lagData_per CI a ha D τ x (t + 2 * Real.pi * (k : ℝ)), ih,
      Work.RPV.Tk_add]
    congr 1
    push_cast
    ring

theorem lagData_tShift (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) (t₀ : ℝ) (N : ℕ)
    (h : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (-Real.sqrt 2, t₀ + 2 * Real.pi * N))) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (-Real.sqrt 2, t₀)) := by
  -- the family and the two maps of the change of variables `ℓ = Tk (-N) ∘ ℓ ∘ Φ`
  set S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ with hS
  set p₀ : ℝ × (ℝ × ℝ) := (τ₀, (-Real.sqrt 2, t₀)) with hp₀
  set L : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun z => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2 with hL
  set Φ : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
    fun z => (z.1, z.2.1, z.2.2 + 2 * Real.pi * (N : ℝ)) with hΦ
  have hΦsm : ContDiff ℝ 8 Φ := by rw [hΦ]; fun_prop
  have hmap : Set.MapsTo Φ S S := by
    intro z hz
    rw [hS] at hz
    simp only [hΦ, hS]
    exact ⟨hz.1, trivial, trivial⟩
  have hLshift : ContDiffWithinAt ℝ 8 L S (Φ p₀) := by
    simpa only [hL, hΦ, hp₀, hS] using h
  have h1 : ContDiffWithinAt ℝ 8 (L ∘ Φ) S p₀ :=
    hLshift.comp p₀ hΦsm.contDiffWithinAt hmap
  -- `Tk (-N)` undoes the shift pointwise
  have h2 : ∀ z : ℝ × (ℝ × ℝ), Work.RPV.Tk (-(N : ℤ)) ((L ∘ Φ) z) = L z := by
    rintro ⟨τ, x, t⟩
    rw [Function.comp_apply, hL, hΦ]
    exact (congrArg (Work.RPV.Tk (-(N : ℤ))) (lagData_quasiPer_nat CI a ha D N τ x t)).trans
      (Work.RPV.Tk_neg (N : ℤ) _)
  have h3 : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPV.Tk (-(N : ℤ)) ((L ∘ Φ) z)) S p₀ := by
    have hc := (contDiff_Tk_shift 8 (-(N : ℤ))).contDiffWithinAt.comp p₀ h1
      (fun z _ => Set.mem_univ _)
    simpa [Function.comp_def] using hc
  exact h3.congr (fun z _ => (h2 z).symm) (h2 p₀).symm

end Work.RPB.B5
