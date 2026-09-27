import Mathlib

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- **Derivative at an endpoint.**  Let `φ : ℝ → ℝ` be differentiable at `0` and suppose that on a
nondegenerate interval `[α, β]` (with `α < β` and `0 ∈ [α, β]`) it agrees with the affine function
`s ↦ φ 0 + s` of slope `1`.  Then `deriv φ 0 = 1`.

Only the one-sided information at the endpoint `0` is used; uniqueness of the derivative on a
convex set with nonempty interior containing `0` in its closure does the work. -/
lemma deriv_eq_one_of_eqOn_Icc {φ : ℝ → ℝ} {α β : ℝ} (hαβ : α < β)
    (h0 : (0 : ℝ) ∈ Set.Icc α β) (h : ∀ s ∈ Set.Icc α β, φ s = φ 0 + s)
    (hφ : DifferentiableAt ℝ φ 0) : deriv φ 0 = 1 := by
  have hS : UniqueDiffWithinAt ℝ (Set.Icc α β) 0 := (uniqueDiffOn_Icc hαβ) 0 h0
  rw [← hφ.derivWithin hS]
  rw [← derivWithin_congr (f₁ := fun s : ℝ => φ 0 + s) (fun s hs => (h s hs).symm) (by ring)]
  change derivWithin (((φ 0 : ℝ) + id ·)) (Set.Icc α β) 0 = 1
  rw [derivWithin_const_add (f := id) (φ 0), derivWithin_id 0 (Set.Icc α β) hS]

/-- **A band point of a smooth level flow is a regular point of the level function.**

Proof sketch: let `c = f x`.  The map `g : ℝ → ℝ`, `g s = f (Φ (s, x)) - f x - s`, is smooth
(`hf`, `hΦsm`, chain rule `mfderiv_comp`), and by `hΦf` it vanishes on the whole interval
`[a - c, b - c]`, which contains `0` and is non-trivial because `a < b`.  Hence `deriv g 0 = 0`
(if `0` is an interior point of the interval use a neighbourhood-constancy lemma; if `c = a` then
`g = 0` on `[0, b - a]`, use `HasDerivWithinAt` on `Set.Ici 0`/`Set.Ioi 0` together with
`UniqueDiffWithinAt`, and if `c = b` mirror `s ↦ -s`).  Finally the chain rule at `s = 0`, where
`Φ (0, x) = x`, gives `deriv g 0 = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x (X x) - 1` with
`X x = mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s ↦ Φ (s, x)) 0 1`, so `mfderiv f x (X x) = 1 ≠ 0`. -/
theorem mfderiv_ne_zero_of_flow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) {a b : ℝ} (hab : a < b) {Φ : ℝ × M → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    {x : M} (hx : f x ∈ Set.Icc a b) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 := by
  have hfx : f x ∈ Set.Icc a b := hx
  -- the flow line `s ↦ Φ (s, x)` and the function `φ s = f (Φ (s, x))` are smooth
  have hfst : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod (𝓡 2)) ∞ (fun s : ℝ => (s, x)) :=
    contMDiff_id.prodMk contMDiff_const
  have hγcd : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ (fun s : ℝ => Φ (s, x)) := hΦsm.comp hfst
  have hfmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℝ) f x := hf.contMDiffAt.mdifferentiableAt (by simp)
  have hγmd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => Φ (s, x)) 0 :=
    hγcd.contMDiffAt.mdifferentiableAt (by simp)
  -- chain rule at the base point
  have hchain : deriv (fun s : ℝ => f (Φ (s, x))) 0
      = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => Φ (s, x)) 0 (1 : ℝ)) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
    change (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ fun s : ℝ => Φ (s, x)) 0) (1 : ℝ)
        = (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x)
            ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => Φ (s, x)) 0) (1 : ℝ))
    rw [mfderiv_comp_apply_of_eq (0:ℝ) hfmd hγmd (hΦ0 x) (1:ℝ)]
  have hHcd : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => f (Φ (s, x))) := hf.comp hγcd
  have hφdiff : DifferentiableAt ℝ (fun s : ℝ => f (Φ (s, x))) 0 :=
    (hHcd.contMDiffAt.mdifferentiableAt (by simp)).differentiableAt
  -- on the nondegenerate interval of parameters that keep the value in `[a, b]`, `φ` is affine
  have hvan : ∀ s ∈ Set.Icc (a - f x) (b - f x), f (Φ (s, x)) = f (Φ (0, x)) + s := by
    intro s hs
    rw [hΦ0 x]
    exact hΦf x s hfx ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩
  have hder1 : deriv (fun s : ℝ => f (Φ (s, x))) 0 = 1 :=
    deriv_eq_one_of_eqOn_Icc (by linarith) ⟨by linarith [hx.1], by linarith [hx.2]⟩ hvan hφdiff
  -- so the derivative of `f` at `x` in the direction of the flow is `1`
  have hAY : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => Φ (s, x)) 0 (1 : ℝ)) = 1 :=
    hchain.symm.trans hder1
  intro hzero
  have h0 : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => Φ (s, x)) 0 (1 : ℝ)) = 0 := by
    rw [hzero]
    exact zero_apply _
  have hcontra : (1 : ℝ) = 0 := hAY.symm.trans h0
  norm_num at hcontra

end Work.Drive.N2
