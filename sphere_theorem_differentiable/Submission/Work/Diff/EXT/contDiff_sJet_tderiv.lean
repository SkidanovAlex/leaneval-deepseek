import Mathlib
import Submission.Work.Diff.EXT.pde_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped ContDiff

/-! ### Smoothness of the spatial `2`-jet and of the time derivative

The two building blocks are the partial derivatives in the spatial and in the time direction.
Both are instances of `ContDiff.fderiv`/`ContDiff.fderiv_apply`: the partial derivative
`∂_y h(z.1, y)` of a map `h : ℝ × ℝⁿ → W` at `y = z.2` is `fderiv ℝ (h x) (g x)` for the
curried map `f : (ℝ × ℝⁿ) → (ℝⁿ → W)`, `f x = (y ↦ h (x.1, y))` and the *smooth* base point
map `g x = x.2`; the hypothesis `Function.uncurry f` is `C^∞` holds because `uncurry f` is the
composite of `h` with the continuous linear map `(x, y) ↦ (x.1, y)`.  The time derivative is
the same construction with `ℝⁿ` replaced by `ℝ` postcomposed with the evaluation at `1`
(the two are definitionally equal by `fderiv_apply_one_eq_deriv`).
-/

/-- Partial differentiation in the spatial variables preserves smoothness: for a `C^∞` map
`h : ℝ × ℝⁿ → W`, the map `z ↦ ∂_y h(z.1, z.2)` is again `C^∞`. -/
lemma contDiff_fderiv_snd_shift {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {h : ℝ × (Fin n → ℝ) → W} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin n → ℝ) => fderiv ℝ (fun y : Fin n → ℝ => h (z.1, y)) z.2) := by
  refine ContDiff.fderiv (n := (⊤ : ℕ∞)) (m := (⊤ : ℕ∞)) ?_ contDiff_snd (by simp)
  show ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => h (p.1.1, p.2))
  let L : ((ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).comp
      (ContinuousLinearMap.fst ℝ (ℝ × (Fin n → ℝ)) (Fin n → ℝ))).prod
      (ContinuousLinearMap.snd ℝ (ℝ × (Fin n → ℝ)) (Fin n → ℝ))
  have hL : (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => h (p.1.1, p.2)) = h ∘ L := by
    funext p; rfl
  rw [hL]
  exact hh.comp L.contDiff

/-- The time derivative `tderiv g z = ∂ₜ g(z)` of a `C^∞` map `g : ℝ × ℝⁿ → ℝᵐ` is `C^∞`. -/
lemma contDiff_tderiv {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (tderiv g) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin n → ℝ) => fderiv ℝ (fun s : ℝ => g (s, z.2)) z.1 1) := by
    refine ContDiff.fderiv_apply (n := (⊤ : ℕ∞)) (m := (⊤ : ℕ∞)) ?_ contDiff_fst
      contDiff_const (by simp)
    show ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × (Fin n → ℝ)) × ℝ => g (p.2, p.1.2))
    let L : ((ℝ × (Fin n → ℝ)) × ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
      (ContinuousLinearMap.snd ℝ (ℝ × (Fin n → ℝ)) ℝ).prod
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp
          (ContinuousLinearMap.fst ℝ (ℝ × (Fin n → ℝ)) ℝ))
    have hL : (fun p : (ℝ × (Fin n → ℝ)) × ℝ => g (p.2, p.1.2)) = g ∘ L := by
      funext p; rfl
    rw [hL]
    exact hg.comp L.contDiff
  exact h1

/-- The spatial `2`-jet `sJet g` and the time derivative `tderiv g` of a `C^∞` function
`g : ℝ × ℝⁿ → ℝᵐ` are again `C^∞`.  (`sJet g z = (g z, ∂ₓg(z), ∂ₓ²g(z))` and
`tderiv g z = ∂ₜg(z)`, all derivatives being with the other variable held fixed.)

Proof: each component is a partial derivative of a smooth function, obtained by
`ContDiff.fderiv` (`ContDiff 𝕜 m (Function.uncurry f) → ContDiff 𝕜 n g → n + 1 ≤ m →
ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x)`), where the condition `n + 1 ≤ m` is trivial for
`m = n = ⊤`; assemble the components with `ContDiff.prodMk` and `contDiff_pi`.  (`tderiv g` is
`fderiv ℝ (fun s => g (s, z.2)) z.1` applied to `1`, i.e. the first partial derivative.) -/
theorem contDiff_sJet_tderiv {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (sJet g) ∧ ContDiff ℝ (⊤ : ℕ∞) (tderiv g) := by
  -- The second component of `sJet g` is the spatial derivative of `g`, the third component is
  -- the spatial derivative of that, so `contDiff_fderiv_snd_shift` applies twice.
  have h2 := contDiff_fderiv_snd_shift hg
  have h3 := contDiff_fderiv_snd_shift h2
  exact ⟨hg.prodMk (h2.prodMk h3), contDiff_tderiv g hg⟩

end Work.Diff.EXT
