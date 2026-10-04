import Mathlib
import Submission.Work.Diff.EXT.pde_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped ContDiff

/-!  ### Smoothness of the spatial jet, of the time derivative and of the recursion
### `Aseq` / `Seq` / `Psi`

These are the elementary inputs of the smoothness statement `contDiff_Aseq_Psi` below.  They are
proved directly from `ContDiff.fderiv` (the parametric version: if `x ↦ f x y` is smooth jointly in
`(x,y)` and `x ↦ g x` is smooth then so is `x ↦ fderiv 𝕜 (f x) (g x)`), which avoids having to
identify the partial derivative `fderiv ℝ (fun y => g (x, y)) y` with the full derivative composed
with `ContinuousLinearMap.inr`. -/

/-- The spatial derivative of a smooth function of `(t, x)` is smooth, as a function of the base
point.  More precisely: if `g` is `C^∞` then so is
`z ↦ fderiv ℝ (fun y ↦ g (φ z.1, y)) z.2`, for any smooth `φ` (only the first factor of `z` is used
in the time variable). -/
theorem contDiff_fderiv_snd_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ} {g : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E × (Fin n → ℝ) => fderiv ℝ (fun y : Fin n → ℝ => g (φ z.1, y)) z.2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun (z : E × (Fin n → ℝ)) (y : Fin n → ℝ) => g (φ z.1, y))) := by
    rw [show Function.uncurry (fun z (y : Fin n → ℝ) => g (φ z.1, y))
        = (fun p : (E × (Fin n → ℝ)) × (Fin n → ℝ) => g (φ p.1.1, p.2)) from rfl]
    exact hg.comp ((hφ.comp (contDiff_fst.fst)).prodMk contDiff_snd)
  exact ContDiff.fderiv h1 contDiff_snd (by simp)

/-- The spatial `2`-jet `sJet g` of a `C^∞` function is `C^∞`. -/
theorem contDiff_sJet_of_contDiff {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (sJet g) := by
  rw [show sJet g = fun z : ℝ × (Fin n → ℝ) =>
      (g z, fderiv ℝ (fun y : Fin n → ℝ => g (z.1, y)) z.2,
       fderiv ℝ (fun w : Fin n → ℝ => fderiv ℝ (fun y : Fin n → ℝ => g (z.1, y)) w) z.2)
      from rfl]
  refine hg.prodMk (?_ : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) =>
      (fderiv ℝ (fun y : Fin n → ℝ => g (z.1, y)) z.2,
       fderiv ℝ (fun w : Fin n → ℝ => fderiv ℝ (fun y : Fin n → ℝ => g (z.1, y)) w) z.2)))
  refine (contDiff_fderiv_snd_of_contDiff hg (E := ℝ) contDiff_id).prodMk ?_
  have hC : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        fderiv ℝ (fun y : Fin n → ℝ => g (p.1.1, y)) p.2) :=
    contDiff_fderiv_snd_of_contDiff hg (E := ℝ × (Fin n → ℝ)) contDiff_fst
  exact ContDiff.fderiv hC contDiff_snd (by simp)

/-- The time derivative `tderiv g` of a `C^∞` function is `C^∞`. -/
theorem contDiff_tderiv_of_contDiff {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (tderiv g) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun (z : ℝ × (Fin n → ℝ)) (s : ℝ) => g (s, z.2))) := by
    rw [show Function.uncurry (fun z (s : ℝ) => g (s, z.2))
        = (fun p : (ℝ × (Fin n → ℝ)) × ℝ => g (p.2, p.1.2)) from rfl]
    exact hg.comp (contDiff_snd.prodMk (contDiff_fst.snd))
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin n → ℝ) => (fderiv ℝ (fun s : ℝ => g (s, z.2)) z.1) 1) :=
    ContDiff.fderiv_apply h1 contDiff_fst contDiff_const (by simp)
  exact h2

/-- The functions produced by the recursion of `Submission/Work/Diff/EXT/pde_defs.lean` from a
`C^∞` `Φ` and a `C^∞` `a` are `C^∞`:  `Aseq Φ a j = ∂ₜ^j (Φ(·,Ja))`, `Seq Φ a 0 = a`,
`Seq Φ a (j+1) = Aseq Φ a j`, and `Psi Φ j` is the universal function expressing `∂ₜ^j(Φ(·,Ja))`
in terms of the spatial `2`-jets of `a, Aseq Φ a 0, …, Aseq Φ a (j-1)`.

Proof sketch: `Aseq Φ a 0 = Φ ∘ (fun z => (z.2, sJet a z))` with `sJet a` smooth when `a` is (see
`contDiff_sJet_tderiv`); `Aseq Φ a (j+1) = tderiv (Aseq Φ a j)` with `tderiv` preserving smoothness.
`Seq` is `a` or an `Aseq`.  For `Psi`: `Psi Φ 0 = Φ ∘ (fun p => (p.1, p.2 0))` is smooth, and the
recursion step is a finite sum of terms
`(fderiv ℝ (Psi Φ j) (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ))`, where
`p ↦ fderiv ℝ (Psi Φ j) (p.1, fun k => p.2 k.castSucc)` is smooth by `ContDiff.fderiv` (the
function `p ↦ (p.1, fun k => p.2 k.castSucc)` is smooth by `ContDiff.prodMk`/`contDiff_pi`),
`p ↦ (0, Pi.single i (p.2 i.succ))` is smooth, and applying a continuous linear map to a smooth
argument preserves smoothness (`ContDiff.clm_apply`); finish with `Finset.sum`. -/
theorem contDiff_Aseq_Psi {n m : ℕ} (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)) (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    (∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Aseq Φ a j)) ∧
      (∀ i : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Seq Φ a i)) ∧
      (∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Psi Φ j)) := by
  have haSJet : ContDiff ℝ (⊤ : ℕ∞) (sJet a) := contDiff_sJet_of_contDiff a ha
  have hA : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Aseq Φ a j) := by
    intro j
    induction j with
    | zero =>
      rw [Aseq.eq_1]
      exact hΦ.comp (contDiff_snd.prodMk haSJet)
    | succ j ih =>
      rw [Aseq.eq_2]
      exact contDiff_tderiv_of_contDiff _ ih
  refine ⟨hA, ?_, ?_⟩
  · intro i
    cases i with
    | zero => rw [Seq.eq_1]; exact ha
    | succ j => rw [Seq.eq_2]; exact hA j
  · intro j
    induction j with
    | zero =>
      rw [Psi.eq_1]
      exact hΦ.comp
        (contDiff_fst.prodMk ((contDiff_apply ℝ (SJet n m) (0 : Fin 1)).comp contDiff_snd))
    | succ j ih =>
      rw [Psi.eq_2]
      refine ContDiff.sum (fun i _ => ?_)
      -- the derivative of `Psi Φ j` as a smooth function of the base point
      have hfd : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : (Fin n → ℝ) × (Fin (j + 2) → SJet n m) =>
            fderiv ℝ (fun q : (Fin n → ℝ) × (Fin (j + 1) → SJet n m) => Psi Φ j q)
              (x.1, fun k : Fin (j + 1) => x.2 k.castSucc)) := by
        have hun : ContDiff ℝ (⊤ : ℕ∞)
            (Function.uncurry (fun (_ : (Fin n → ℝ) × (Fin (j + 2) → SJet n m))
                (q : (Fin n → ℝ) × (Fin (j + 1) → SJet n m)) => Psi Φ j q)) := by
          rw [show Function.uncurry (fun (_ : (Fin n → ℝ) × (Fin (j + 2) → SJet n m))
                (q : (Fin n → ℝ) × (Fin (j + 1) → SJet n m)) => Psi Φ j q)
                = (fun r : ((Fin n → ℝ) × (Fin (j + 2) → SJet n m)) ×
                    ((Fin n → ℝ) × (Fin (j + 1) → SJet n m)) => Psi Φ j r.2) from rfl]
          exact ih.comp contDiff_snd
        have hφ : ContDiff ℝ (⊤ : ℕ∞)
            (fun x : (Fin n → ℝ) × (Fin (j + 2) → SJet n m) =>
              ((x.1, fun k : Fin (j + 1) => x.2 k.castSucc) :
                (Fin n → ℝ) × (Fin (j + 1) → SJet n m))) :=
          contDiff_fst.prodMk
            (contDiff_pi.mpr
              (fun k => (contDiff_apply ℝ (SJet n m) k.castSucc).comp contDiff_snd))
        exact ContDiff.fderiv hun hφ (by simp)
      -- apply the above continuous linear map to the smooth shift `(0, eᵢ)`
      refine ContDiff.clm_apply hfd ?_
      refine contDiff_const.prodMk ?_
      exact (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.single ℝ (fun _ : Fin (j + 1) => SJet n m) i)).comp
          ((contDiff_apply ℝ (SJet n m) i.succ).comp contDiff_snd)

end Work.Diff.EXT
