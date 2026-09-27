import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.mfderiv_ne_zero_of_flow
import Submission.Work.Drive.N2.mfderiv_eq_zero_of_eqOn_band
import Submission.Work.Drive.N2.mfderiv_eq_of_eqOn_band
import Submission.Work.Drive.N2.mfderiv_flow_zero_snd

/-!
# The corrected band construction (the requested `bandSeparatingMap` needs `f` smooth)

`Work.Drive.N2.bandSeparatingMap` asks for the map `g z = A (Φ (b - f z, z))` to be smooth,
injective on level sets and to have `(dg, df)` injective on the band `f ⁻¹' [a,b]`, from the
hypotheses of a level flow `Φ` alone — but it never assumes that `f` is smooth, and it is FALSE
without that: with `M = ℝ²`, `a = 0`, `b = 1`, `f (z₀, z₁) = z₀ + |z₁|`, `Φ (t, z) = z + (t, 0)`,
`A` the inclusion `ℝ² ↪ ℝ³` and `x = (1/2, 0)`, every hypothesis holds while
`g z = (1 - |z₁|, z₁, 0)` is not smooth at `z₁ = 0`.

This file proves the corrected statement, whose only extra hypothesis is smoothness of `f`
(available in the intended application, where `f` is Morse: `IsMorseDistinct f` is a conjunction
whose first component is exactly `ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f`).

The work is split into the flow-independent computation `mfderiv_transport_self` (the transport to
the level of `f x` fixes tangent directions of the level set), the two vanishing statements on the
band (`mfderiv_eq_zero_of_eqOn_band`), and the regularity fact `mfderiv_ne_zero_of_flow`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- Smoothness of the graph map `z ↦ (d - f z, z)`. -/
lemma contMDiff_graph (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (d : ℝ) :
    ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ fun z : M => (d - f z, z) :=
  ((contDiff_const.sub contDiff_id).comp_contMDiff hf).prodMk contMDiff_id

lemma mdifferentiableAt_graph (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (d : ℝ) (x : M) :
    MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x :=
  (contMDiff_graph f hf d).mdifferentiableAt (by simp)

/-- The derivative of `z ↦ d - f z` is minus the derivative of `f`. -/
lemma mfderiv_const_sub_apply (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (d : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => d - f z) x v
      = - mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v := by
  have h1 : (fun z : M => d - f z) = ((fun _ : M => d) - f) := rfl
  rw [h1, mfderiv_sub mdifferentiableAt_const (hf.mdifferentiableAt (by simp)), mfderiv_const]
  simp only [zero_sub]
  rfl

/-- The *time* component of the derivative of the graph map `z ↦ (d - f z, z)`. -/
lemma mfderiv_graph_fst (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (d : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v).1
      = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => d - f z) x v := by
  have hmd := mdifferentiableAt_graph f hf d x
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ).prod (𝓡 2))) (I'' := 𝓘(ℝ, ℝ))
    (f := fun z : M => (d - f z, z)) (g := Prod.fst) (x := x) mdifferentiableAt_fst hmd v
  have h1 : (Prod.fst ∘ fun z : M => (d - f z, z)) = (fun z : M => d - f z) := rfl
  rw [h1] at hc
  have h2 : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) Prod.fst ((d - f x), x))
      = ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (d - f x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_fst
  rw [h2] at hc
  exact (show (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v).1
      = (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (d - f x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v) from rfl).trans
    hc.symm

/-- The *space* component of the derivative of the graph map `z ↦ (d - f z, z)`. -/
lemma mfderiv_graph_snd (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (d : ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v).2 = v := by
  have hmd := mdifferentiableAt_graph f hf d x
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ).prod (𝓡 2))) (I'' := (𝓡 2))
    (f := fun z : M => (d - f z, z)) (g := Prod.snd) (x := x) mdifferentiableAt_snd hmd v
  have h1 : (Prod.snd ∘ fun z : M => (d - f z, z)) = (fun z : M => z) := rfl
  rw [h1] at hc
  have h2 : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) Prod.snd ((d - f x), x))
      = ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (d - f x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_snd
  rw [h2] at hc
  have h4 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => z) x v = v := by
    change mfderiv (𝓡 2) (𝓡 2) id x v = v
    rw [mfderiv_id]
    rfl
  rw [h4] at hc
  exact (show (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v).2
      = (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (d - f x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) (fun z : M => (d - f z, z)) x v) from rfl).trans
    hc.symm

/-- The transport `z ↦ Φ (f x - f z, z)` (to the level of `f x`) fixes the tangent directions in
`ker (mfderiv f x)`. -/
lemma mfderiv_transport_self (Φ : ℝ × M → M)
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : TangentSpace (𝓡 2) x)
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0) :
    mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = v := by
  have hmdΨ := mdifferentiableAt_graph f hf (f x) x
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
    rw [hw, mfderiv_graph_fst f hf (f x) x v, mfderiv_const_sub_apply f hf (f x) x v, hv]
    simp
  have hw2 : w.2 = v := by rw [hw]; exact mfderiv_graph_snd f hf (f x) x v
  rw [hw1, hw2]
  have hslice : (fun z : M => Φ (f x - f x, z)) = id := by
    funext z
    rw [sub_self]
    exact hΦ0 z
  rw [mfderiv_congr hslice, mfderiv_id]
  rw [map_zero, zero_add]
  rfl

/-- **The corrected band construction.**  This is `Work.Drive.N2.bandSeparatingMap` with the
missing hypothesis that `f` is smooth (without it the statement is false). -/
theorem bandSeparatingMap_of_contMDiff
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
  have hband : ∀ z : M, f z ∈ Set.Icc a b → f (Φ (b - f z, z)) = b := by
    intro z hz
    have h := hΦf z (b - f z) hz (by simpa using hb)
    simpa using h
  have hgraph : ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ fun z : M => (b - f z, z) :=
    contMDiff_graph f hf b
  have hτsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - f z, z)) := hΦsm.comp hgraph
  refine ⟨?_, ?_, ?_⟩
  · -- 1. smoothness on the band
    intro x _
    have h := (hA.contMDiffAt).comp x ((hΦsm.contMDiffAt).comp x hgraph.contMDiffAt)
    simpa only [Function.comp_def] using h
  · -- 2. the immersion
    intro x v hx hfv hgv
    by_cases hAB : a = b
    · -- the band is a single level set
      have hfxb : f x = b := by
        rw [hAB] at hx
        exact le_antisymm hx.2 hx.1
      have hτx : Φ (b - f x, x) = x := by rw [hfxb, sub_self]; exact hΦ0 x
      have htransport : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v = v := by
        have hfun : (fun z : M => Φ (b - f z, z)) = (fun z : M => Φ (f x - f z, z)) := by
          funext z
          rw [hfxb]
        rw [hfun]
        exact mfderiv_transport_self Φ hΦsm hΦ0 f hf x v hfv
      have hchain : mfderiv (𝓡 2) (𝓡 3) (fun z : M => A (Φ (b - f z, z))) x v
          = mfderiv (𝓡 2) (𝓡 3) A (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := by
        have h := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓡 2)) (I'' := (𝓡 3))
          (f := fun z : M => Φ (b - f z, z)) (g := A) (x := x)
          (hA.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
        simpa only [Function.comp_def] using h
      rw [hchain, htransport, hτx] at hgv
      exact hAimm x hfxb v hfv hgv
    · -- a < b
      have hab' : a < b := lt_of_le_of_ne hab hAB
      have hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 :=
        mfderiv_ne_zero_of_flow f hab' hf hΦsm hΦ0 hΦf hx
      have hτfx : f (Φ (b - f x, x)) = b := hband x hx
      have hσsm' : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (f x - f z, z)) :=
        hΦsm.comp (contMDiff_graph f hf (f x))
      -- the two vanishing statements on the band
      have hR1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun z : M => f (Φ (b - f z, z)) - f (Φ (b - f x, x))) x = 0 := by
        refine mfderiv_eq_zero_of_eqOn_band f
          (fun z : M => f (Φ (b - f z, z)) - f (Φ (b - f x, x))) hab' hf ?_ hx hreg ?_
        · exact (hf.comp hτsm).sub contMDiff_const
        · intro z hz
          rw [hband z hz, hτfx, sub_self]
      have hfτ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x = 0 := by
        have hsub : (fun z : M => f (Φ (b - f z, z)) - f (Φ (b - f x, x)))
            = (fun z : M => f (Φ (b - f z, z))) - (fun _ : M => f (Φ (b - f x, x))) := rfl
        rw [hsub] at hR1
        rw [mfderiv_sub (f := fun z : M => f (Φ (b - f z, z)))
          (g := fun _ : M => f (Φ (b - f x, x)))
          ((hf.comp hτsm).mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const,
          sub_zero] at hR1
        exact hR1
      -- `σ ∘ τ = σ` on the band, hence `mfderiv σ x = mfderiv σ (τ x) ∘ mfderiv τ x`
      have hEq : mfderiv (𝓡 2) (𝓡 2)
            (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x
          = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x := by
        refine mfderiv_eq_of_eqOn_band f hab' hf _ _ (hσsm'.comp hτsm) hσsm' hx hreg ?_
        intro z hz
        rw [hband z hz]
        have h := hΦcomp z (f x - b) (b - f z) hz (by simpa using hb)
          (by rw [show f z + (b - f z) + (f x - b) = f x by ring]; exact hx)
        simpa [show (f x - b) + (b - f z) = f x - f z by ring] using h
      -- conclusion
      have hgchain : mfderiv (𝓡 2) (𝓡 3) (fun z : M => A (Φ (b - f z, z))) x v
          = mfderiv (𝓡 2) (𝓡 3) A (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := by
        have h := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓡 2)) (I'' := (𝓡 3))
          (f := fun z : M => Φ (b - f z, z)) (g := A) (x := x)
          (hA.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
        simpa only [Function.comp_def] using h
      have hw : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v = 0 := by
        refine hAimm (Φ (b - f x, x)) hτfx _ ?_ ?_
        · have h1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x v
              = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (b - f x, x))
                  (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
            mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓡 2)) (I'' := 𝓘(ℝ, ℝ))
              (f := fun z : M => Φ (b - f z, z)) (g := f) (x := x)
              (hf.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
          rw [← h1, hfτ]
          simp
        · rw [← hgchain]
          exact hgv
      have hσv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = v :=
        mfderiv_transport_self Φ hΦsm hΦ0 f hf x v hfv
      have h2 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = 0 := by
        have h1 : mfderiv (𝓡 2) (𝓡 2)
              (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v
            = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
                (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
          mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓡 2)) (I'' := (𝓡 2))
            (f := fun z : M => Φ (b - f z, z)) (g := fun w : M => Φ (f x - f w, w)) (x := x)
            (hσsm'.mdifferentiableAt (by simp)) (hτsm.mdifferentiableAt (by simp)) v
        have hEqapp : mfderiv (𝓡 2) (𝓡 2)
              (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v
            = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v :=
          congrArg (fun (L : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) => L v) hEq
        have h3 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
          rw [hw]
          exact map_zero _
        exact hEqapp.symm.trans (h1.trans h3)
      rw [← hσv]
      exact h2
  · -- 3. injectivity on each level set
    intro x y hx hy hfxy hAxy
    have hfx : f (Φ (b - f x, x)) = b := hband x hx
    have hfy : f (Φ (b - f y, y)) = b := hband y hy
    have hτ : Φ (b - f x, x) = Φ (b - f y, y) := hAinj _ _ hfx hfy hAxy
    have hinv : ∀ z : M, f z ∈ Set.Icc a b → f z = f x → Φ (f z - b, Φ (b - f z, z)) = z := by
      intro z hz _
      have h := hΦcomp z (f z - b) (b - f z) hz (by simpa using hb)
        (by rw [show f z + (b - f z) + (f z - b) = f z by ring]; exact hz)
      rw [show (f z - b) + (b - f z) = 0 by ring, hΦ0 z] at h
      exact h
    have h1 := hinv x hx rfl
    have h2 := hinv y hy hfxy.symm
    rw [hτ] at h1
    have hfx_eq : f x - b = f y - b := by rw [hfxy]
    rw [← hfx_eq] at h2
    exact h1.symm.trans h2

end Work.Drive.N2
