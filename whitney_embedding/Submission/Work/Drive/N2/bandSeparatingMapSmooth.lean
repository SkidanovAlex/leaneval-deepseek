import Mathlib
import Submission.Work.Drive.N2.mfderiv_ne_zero_of_flow
import Submission.Work.Drive.N2.mfderiv_eq_zero_of_eqOn_band
import Submission.Work.Drive.N2.mfderiv_eq_of_eqOn_band
import Submission.Work.Drive.N2.mfderiv_flow_zero_snd

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-! Corrected `Work.Drive.N2.bandSeparatingMap`: the statement is the same, except that it now
assumes `hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f`.  Without it the requested statement is FALSE (see
`Submission/Work/Drive/N2/NOTES_bandSmooth_plan.md` for the counterexample: `M = ℝ²`, `a = 0`, `b = 1`,
`f (z₀,z₁) = z₀ + |z₁|`, `Φ (t,z) = z + (t,0)`, `A` the inclusion of `ℝ²` into `ℝ³`, `x = (1/2,0)`:
every hypothesis holds but `A (Φ (b - f z, z)) = (1 - |z₁|, z₁, 0)` is not smooth at `z₁ = 0`).
The consumer `Work.Drive.N2.levelSeparatingMap` has this smoothness in scope via `IsMorseDistinct`.

A complete route, including which on-disk bricks to use
(`Work.Drive.N2.mfderiv_ne_zero_of_flow`, `Work.Drive.N2.mfderiv_eq_zero_of_eqOn_band`,
`Work.Drive.N2.mfderiv_flow_zero_snd`), is written up in
`Submission/Work/Drive/N2/NOTES_bandSmooth_plan.md`.  In short: write `τ z := Φ (b - f z, z)`; the
map is `A ∘ τ`; smoothness is the chain rule; injectivity on level sets transports `τ x = τ y` back
along `Φ (c - b, ·)` using `hΦcomp`; for the immersion, the identities `f (τ z) = b` and
`σ (τ z) = σ z` hold on the whole band (for `σ z := Φ (c - f z, z)`, `c := f x`) and, differentiated
with `mfderiv_eq_zero_of_eqOn_band`, turn the hypothesis `mfderiv A (τ x) w = 0` (`w := mfderiv τ x v`)
into `w = 0` via `hAimm`, after which `mfderiv σ x v = v` (chain rule + `mfderiv_flow_zero_snd` and
`mfderiv f x v = 0`) gives `v = 0`.

The auxiliary computations below (the components of the derivative of the graph map
`z ↦ (k - f z, z)`) are the standard `mfderiv_fst`/`mfderiv_snd` bookkeeping for the `TangentSpace`
type synonyms; the same bookkeeping appears in the sibling file
`Submission/Work/Drive/N2/bandSeparatingMap_of_contMDiff.lean`. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-! ### The graph map `z ↦ (k - f z, z)` and its derivative -/

/-- Smoothness of the graph map `z ↦ (k - f z, z)`. -/
lemma bandGraph_contMDiff (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (k : ℝ) :
    ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ (fun z : M => (k - f z, z)) :=
  ((contDiff_const.sub contDiff_id).comp_contMDiff hf).prodMk contMDiff_id

/-- The derivative of `z ↦ k - f z` is minus the derivative of `f`. -/
lemma bandGraph_const_sub_apply (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (k : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => k - f z) x v
      = - mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v := by
  have h1 : (fun z : M => k - f z) = ((fun _ : M => k) - f) := rfl
  rw [h1, mfderiv_sub mdifferentiableAt_const (hf.mdifferentiableAt (by simp)), mfderiv_const]
  simp only [zero_sub]
  rfl

/-- The time component of the derivative of the graph map. -/
lemma bandGraph_mfderiv_fst (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (k : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v).1
      = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => k - f z) x v := by
  have hmd : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x :=
    (bandGraph_contMDiff f hf k).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ).prod (𝓡 2))) (I'' := 𝓘(ℝ, ℝ))
    (f := fun z : M => (k - f z, z)) (g := Prod.fst) (x := x) mdifferentiableAt_fst hmd v
  have h1 : (Prod.fst ∘ fun z : M => (k - f z, z)) = (fun z : M => k - f z) := rfl
  rw [h1] at hc
  have h2 : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) Prod.fst ((k - f x), x))
      = ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (k - f x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_fst
  rw [h2] at hc
  exact (show (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v).1
      = (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (k - f x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v) from rfl).trans
    hc.symm

/-- The space component of the derivative of the graph map is the vector itself. -/
lemma bandGraph_mfderiv_snd (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (k : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v).2 = v := by
  have hmd : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x :=
    (bandGraph_contMDiff f hf k).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ).prod (𝓡 2))) (I'' := (𝓡 2))
    (f := fun z : M => (k - f z, z)) (g := Prod.snd) (x := x) mdifferentiableAt_snd hmd v
  have h1 : (Prod.snd ∘ fun z : M => (k - f z, z)) = (fun z : M => z) := rfl
  rw [h1] at hc
  have h2 : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Prod.snd ((k - f x), x))
      = ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (k - f x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_snd
  rw [h2] at hc
  have h4 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => z) x v = v := by
    change mfderiv (𝓡 2) (𝓡 2) id x v = v
    rw [mfderiv_id]
    rfl
  rw [h4] at hc
  exact (show (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v).2
      = (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (k - f x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (k - f z, z)) x v) from rfl).trans
    hc.symm

/-- **The shift at the level of `f x` fixes the kernel directions.**  If `k = f x` and
`mfderiv f x v = 0`, then the derivative of `z ↦ Φ (k - f z, z)` at `x` sends `v` to `v`: for such
`v` the time argument `k - f z` has vanishing derivative at `x`, and the time-`0` slice of the flow
is the identity. -/
lemma mfderiv_bandShift_apply (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    {k : ℝ} {x : M} (hk : k = f x) (v : TangentSpace (𝓡 2) x)
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0) :
    mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (k - f z, z)) x v = v := by
  subst hk
  have hmdΨ : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (f x - f z, z)) x :=
    (bandGraph_contMDiff f hf (f x)).mdifferentiableAt (by simp)
  have hmdΦ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Φ ((f x - f x), x) :=
    hΦsm.mdifferentiableAt (by simp)
  have hchain : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v
      = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Φ ((f x - f x), x)
          (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (f x - f z, z)) x v) := by
    have h := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ).prod (𝓡 2))) (I'' := (𝓡 2))
      (f := fun z : M => (f x - f z, z)) (g := Φ) (x := x) hmdΦ hmdΨ v
    simpa only [Function.comp_def] using h
  rw [hchain]
  set w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) ((f x - f x), x) :=
    mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (f x - f z, z)) x v with hw
  have hsplit := mfderiv_prod_eq_add_apply (f := Φ) (p := ((f x - f x), x)) (v := w) hmdΦ
  rw [hsplit]
  have hw1 : w.1 = 0 := by
    rw [hw, bandGraph_mfderiv_fst f hf (f x) x v, bandGraph_const_sub_apply f hf (f x) x v, hv]
    simp
  have hw2 : w.2 = v := by rw [hw]; exact bandGraph_mfderiv_snd f hf (f x) x v
  rw [hw1, hw2]
  have hslice : (fun z : M => Φ (f x - f x, z)) = id := by
    funext z
    rw [sub_self]
    exact hΦ0 z
  rw [mfderiv_congr hslice, mfderiv_id]
  rw [map_zero, zero_add]
  rfl

/-! ### The band identities -/

/-- On the band, the shift map sends everything to the level `k`. -/
lemma bandGraph_eq_of_mem (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) {Φ : ℝ × M → M}
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    {k : ℝ} (hk : k ∈ Set.Icc a b) {z : M} (hz : f z ∈ Set.Icc a b) :
    f (Φ (k - f z, z)) = k := by
  have h := hΦf z (k - f z) hz (by rw [show f z + (k - f z) = k by ring]; exact hk)
  simpa using h

/-- On a band of a level flow the composite `z ↦ f (Φ (b - f z, z))` is constantly `b`, so its
derivative vanishes at every regular point of the band. -/
lemma mfderiv_tau_f_eq_zero (f : M → ℝ) {a b : ℝ} (hab : a < b) {Φ : ℝ × M → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    {x : M} (hx : f x ∈ Set.Icc a b)
    (hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x = 0 := by
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  have hτ : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - f z, z)) :=
    hΦsm.comp (bandGraph_contMDiff f hf b)
  have hR : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      ((fun z : M => f (Φ (b - f z, z))) - (fun _ : M => b)) :=
    (hf.comp hτ).sub contMDiff_const
  have hR0 : ∀ z : M, f z ∈ Set.Icc a b →
      ((fun z : M => f (Φ (b - f z, z))) - (fun _ : M => b)) z = 0 := by
    intro z hz
    show f (Φ (b - f z, z)) - b = 0
    rw [bandGraph_eq_of_mem f hab.le hΦf hb hz, sub_self]
  have hF : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x :=
    (hf.comp hτ).mdifferentiableAt (by simp)
  have h := mfderiv_eq_zero_of_eqOn_band f
    ((fun z : M => f (Φ (b - f z, z))) - (fun _ : M => b)) hab hf hR hx hreg hR0
  rwa [mfderiv_sub hF mdifferentiableAt_const, mfderiv_const, sub_zero] at h

/-! ### The target theorem -/

theorem bandSeparatingMapSmooth {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) {Φ : ℝ × M → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ x : M, ∀ s t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f x + t + s ∈ Set.Icc a b → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (A : M → EuclideanSpace ℝ (Fin 3)) (hA : ContMDiff (𝓡 2) (𝓡 3) ∞ A)
    (hAinj : ∀ x y : M, f x = b → f y = b → A x = A y → x = y)
    (hAimm : ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) A y v = 0 → v = 0) :
    (∀ x : M, f x ∈ Set.Icc a b →
      ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun z => A (Φ (b - f z, z))) x) ∧
    (∀ x : M, ∀ v : TangentSpace (𝓡 2) x, f x ∈ Set.Icc a b →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (fun z => A (Φ (b - f z, z))) x v = 0 → v = 0) ∧
    (∀ x y : M, f x ∈ Set.Icc a b → f y ∈ Set.Icc a b → f x = f y →
      A (Φ (b - f x, x)) = A (Φ (b - f y, y)) → x = y) := by
  classical
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hτsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - f z, z)) :=
    hΦsm.comp (bandGraph_contMDiff f hf b)
  refine ⟨?_, ?_, ?_⟩
  · -- 1. smoothness on the band
    intro x _
    exact (hA.contMDiffAt).comp x
      ((hΦsm.contMDiffAt).comp x (bandGraph_contMDiff f hf b).contMDiffAt)
  · -- 2. the immersion
    intro x v hx hfv hgv
    -- the chain rule for `A ∘ τ` at `x`
    have hAchain : mfderiv (𝓡 2) (𝓡 3) (fun z : M => A (Φ (b - f z, z))) x v
        = mfderiv (𝓡 2) (𝓡 3) A (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
      mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := fun z : M => Φ (b - f z, z)) (g := A) (x := x)
        (hA.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
    rw [hAchain] at hgv
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · -- the band is a single level set
      have hfxb : f x = b := by
        rw [hab_eq] at hx
        exact le_antisymm hx.2 hx.1
      have hτv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v = v :=
        mfderiv_bandShift_apply f hf hΦsm hΦ0 hfxb.symm v hfv
      have hτx : Φ (b - f x, x) = x := by rw [hfxb, sub_self]; exact hΦ0 x
      rw [hτv, hτx] at hgv
      exact hAimm x hfxb v hfv hgv
    · -- a genuine band
      have hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 :=
        mfderiv_ne_zero_of_flow f hab_lt hf hΦsm hΦ0 hΦf hx
      -- (a) the derivative of `f ∘ τ` vanishes
      have hfτ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x = 0 :=
        mfderiv_tau_f_eq_zero f hab_lt hf hΦsm hΦf hx hreg
      have hτxband : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f hab hΦf hb hx
      have hσsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (f x - f z, z)) :=
        hΦsm.comp (bandGraph_contMDiff f hf (f x))
      -- the first derivative condition holds at `τ x`
      have hdfτ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
        have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
          (f := fun z : M => Φ (b - f z, z)) (g := f) (x := x)
          (hf.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
        have hc' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x v
            = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (b - f x, x))
                (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := hc
        rw [← hc', hfτ]
        rfl
      have hτv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v = 0 :=
        hAimm (Φ (b - f x, x)) hτxband _ hdfτ hgv
      -- (b) `σ ∘ τ = σ` on the band, so their derivatives at `x` agree
      have hEq : mfderiv (𝓡 2) (𝓡 2)
            (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x
          = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x := by
        refine mfderiv_eq_of_eqOn_band f hab_lt hf _ _ (hσsm.comp hτsm) hσsm hx hreg ?_
        intro z hz
        rw [bandGraph_eq_of_mem f hab hΦf hb hz]
        have h := hΦcomp z (f x - b) (b - f z) hz (by simpa using hb)
          (by rw [show f z + (b - f z) + (f x - b) = f x by ring]; exact hx)
        simpa [show (f x - b) + (b - f z) = f x - f z by ring] using h
      have hchainσ : mfderiv (𝓡 2) (𝓡 2)
            (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v
          = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
        mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
          (f := fun z : M => Φ (b - f z, z)) (g := fun w : M => Φ (f x - f w, w)) (x := x)
          (hσsm.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
      have hσzero : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = 0 := by
        have h1 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v
            = mfderiv (𝓡 2) (𝓡 2)
                (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v :=
          (congrArg (fun (L : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) => L v)
            hEq).symm
        have h3 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
          rw [hτv]
          exact map_zero _
        exact h1.trans (hchainσ.trans h3)
      have hσv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = v :=
        mfderiv_bandShift_apply f hf hΦsm hΦ0 rfl v hfv
      calc v = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v := hσv.symm
        _ = 0 := hσzero
  · -- 3. injectivity on each level set
    intro x y hx hy hfxy hAxy
    have hfx : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f hab hΦf hb hx
    have hfy : f (Φ (b - f y, y)) = b := bandGraph_eq_of_mem f hab hΦf hb hy
    have hτ : Φ (b - f x, x) = Φ (b - f y, y) := hAinj _ _ hfx hfy hAxy
    -- flowing back from `τ z` recovers `z`
    have hback : ∀ z : M, f z ∈ Set.Icc a b → f z = f x →
        Φ (f x - b, Φ (b - f z, z)) = z := by
      intro z hz hzx
      have h := hΦcomp z (f x - b) (b - f z) hz (by simpa using hb)
        (by rw [show f z + (b - f z) + (f x - b) = f x by ring]; exact hx)
      have hst : (f x - b) + (b - f z) = f x - f z := by ring
      rw [hst] at h
      refine h.trans ?_
      rw [hzx, sub_self]
      exact hΦ0 z
    have h1 := hback x hx rfl
    have h2 := hback y hy hfxy.symm
    rw [hτ] at h1
    exact h1.symm.trans h2

end Work.Drive.N2
