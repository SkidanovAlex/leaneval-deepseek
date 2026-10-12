import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.window_a_pair_le`

**The double-annihilation pair bound on the `n₊`-window**: for a window state
`Ψ` (`T.NWindow M Ψ`, FS `eq:LocalizedAftercNumber`) and under the Bessel/number
hypothesis `Σ_k a_k†a_k ≤ Cn·n₊`,

  `|⟨a_k a_l Ψ, Ψ⟩| ≤ Cn (M+1) ‖Ψ‖²`.

## The argument

Everything is the `NWindow` bound `⟨n₊g,g⟩ ≤ M‖g‖²` (`Work.BoseB7A.NWindow_bp_N_le`)
applied to vectors that the number grading keeps inside the window, plus
Cauchy–Schwarz in the Fock form.  Write `u = a_l Ψ`.

1. `‖u‖² ≤ Cn·M‖Ψ‖²`: `‖a_lΨ‖² ≤ ⟨(Σ_ka_k†a_k)Ψ,Ψ⟩ ≤ Cn⟨n₊Ψ,Ψ⟩ ≤ Cn·M‖Ψ‖²`
   (`Σ_k‖a_kg‖² = ⟨(Σ_ka_k†a_k)g,g⟩`, singleton bound by the full sum, Bessel,
   window).
2. `a_lΨ` is again a window state (`Work.BoseB7A.TildeData.NWindow_a`: the grading
   `[n₊,a_l] = -a_l` *lowers* the window, whence `T.NWindow M (a_lΨ)`), so the same
   bound applies to `g = a_lΨ`: `‖a_ka_lΨ‖² ≤ Cn·M‖a_lΨ‖² ≤ (Cn·M)²‖Ψ‖²`.
3. Cauchy–Schwarz squared in the Fock form (`Work.BoseB7.bp_cauchy_sq`):
   `⟨a_ka_lΨ,Ψ⟩² ≤ ‖a_ka_lΨ‖²‖Ψ‖² ≤ ((Cn·M)‖Ψ‖²)²`, and `sq_le_sq` turns the
   squared bound into `|⟨a_ka_lΨ,Ψ⟩| ≤ Cn·M‖Ψ‖² ≤ Cn(M+1)‖Ψ‖²`.

No square roots are taken: the whole proof is polynomial arithmetic on the
nonnegative quantities `Cn`, `M`, `‖·‖²`.

The proof is complete (no unfinished obligations) and rests on
`propext, Classical.choice, Quot.sound`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB7

set_option autoImplicit false

/-! ## 1. The number form is the sum of the annihilation energies -/

/-- `⟨(Σ_k n_k)g, g⟩ = Σ_k ‖a_k g‖²`: the total number form is the sum of the
individual annihilation energies (`a_k†` is the adjoint of `a_k`). -/
private theorem window_pair_nOp_sum_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (g : F.H) :
    F.bp ((∑ k : Mode, F.nOp k) g) g = ∑ k : Mode, F.normSq (F.a k g) := by
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint, FockData.normSq]

/-! ## 2. The single-mode window bound `‖a_k g‖² ≤ Cn·M‖g‖²` -/

/-- **The per-mode annihilation bound on the window**: Bessel plus the window
bound on the same vector.  (`Σ_k‖a_kg‖² = ⟨(Σ_ka_k†a_k)g,g⟩ ≤ Cn⟨n₊g,g⟩ ≤ Cn·M‖g‖²`.) -/
private theorem window_pair_normSq_a_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode)
    (T : Work.BoseB7A.TildeData F) (Cn M : ℝ) (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (k : Mode) (g : F.H) (hg : T.NWindow M g) :
    F.normSq (F.a k g) ≤ Cn * M * F.normSq g := by
  have h1 : F.normSq (F.a k g) ≤ F.bp ((∑ j : Mode, F.nOp j) g) g := by
    rw [window_pair_nOp_sum_eq]
    exact Finset.single_le_sum (fun j _ => F.bp_nonneg (F.a j g)) (Finset.mem_univ k)
  have h2 : F.bp ((∑ j : Mode, F.nOp j) g) g ≤ Cn * F.bp (T.N g) g := hBessel g
  have h3 : F.bp (T.N g) g ≤ M * F.normSq g :=
    Work.BoseB7A.NWindow_bp_N_le F T hM hg
  calc F.normSq (F.a k g) ≤ Cn * F.bp (T.N g) g := le_trans h1 h2
    _ ≤ Cn * (M * F.normSq g) := mul_le_mul_of_nonneg_left h3 hCn0
    _ = Cn * M * F.normSq g := by ring

/-! ## 3. The pair bound -/

theorem window_a_pair_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {M : ℝ} (hM : 0 ≤ M) {Ψ : F.H} (hΨ : T.NWindow M Ψ) (k l : Mode) :
    |F.bp (F.a k (F.a l Ψ)) Ψ| ≤ Cn * (M + 1) * F.normSq Ψ := by
  -- `a_l Ψ` is again a window state (the grading lowers the window)
  have hwin : T.NWindow M (F.a l Ψ) := T.NWindow_a l hΨ
  -- the two single-mode bounds
  have h1 : F.normSq (F.a l Ψ) ≤ Cn * M * F.normSq Ψ :=
    window_pair_normSq_a_le F T Cn M hCn0 hM hBessel l Ψ hΨ
  have h2 : F.normSq (F.a k (F.a l Ψ)) ≤ Cn * M * F.normSq (F.a l Ψ) :=
    window_pair_normSq_a_le F T Cn M hCn0 hM hBessel k (F.a l Ψ) hwin
  have hV : 0 ≤ F.normSq Ψ := by
    rw [FockData.normSq]; exact F.bp_nonneg Ψ
  have hCM : 0 ≤ Cn * M := mul_nonneg hCn0 hM
  -- `‖a_k a_l Ψ‖² ≤ (Cn·M)²‖Ψ‖²`
  have hU : F.normSq (F.a k (F.a l Ψ)) ≤ (Cn * M) * ((Cn * M) * F.normSq Ψ) :=
    le_trans h2 (mul_le_mul_of_nonneg_left h1 hCM)
  have hUV : F.normSq (F.a k (F.a l Ψ)) * F.normSq Ψ
      ≤ ((Cn * M) * F.normSq Ψ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hU hV
    calc F.normSq (F.a k (F.a l Ψ)) * F.normSq Ψ
        ≤ ((Cn * M) * ((Cn * M) * F.normSq Ψ)) * F.normSq Ψ := h
      _ = ((Cn * M) * F.normSq Ψ) ^ 2 := by ring
  -- Cauchy–Schwarz (squared) in the Fock form
  have hcs : (F.bp (F.a k (F.a l Ψ)) Ψ) ^ 2
      ≤ F.normSq (F.a k (F.a l Ψ)) * F.normSq Ψ := by
    simpa only [FockData.normSq] using
      Work.BoseB7.bp_cauchy_sq F (F.a k (F.a l Ψ)) Ψ
  -- and `Cn·M ≤ Cn·(M+1)`
  have hsq : (F.bp (F.a k (F.a l Ψ)) Ψ) ^ 2 ≤ (Cn * (M + 1) * F.normSq Ψ) ^ 2 := by
    have hA : Cn * M ≤ Cn * (M + 1) := by nlinarith
    have h0 : 0 ≤ (Cn * M) * F.normSq Ψ := mul_nonneg hCM hV
    have h1' : (Cn * M) * F.normSq Ψ ≤ Cn * (M + 1) * F.normSq Ψ :=
      mul_le_mul_of_nonneg_right hA hV
    have h2' : ((Cn * M) * F.normSq Ψ) ^ 2 ≤ (Cn * (M + 1) * F.normSq Ψ) ^ 2 := by
      nlinarith [h0, h1']
    exact le_trans (le_trans hcs hUV) h2'
  have hfin : |F.bp (F.a k (F.a l Ψ)) Ψ| ≤ |Cn * (M + 1) * F.normSq Ψ| :=
    sq_le_sq.mp hsq
  have hnn : 0 ≤ Cn * (M + 1) * F.normSq Ψ :=
    mul_nonneg (mul_nonneg hCn0 (by linarith)) hV
  rwa [abs_of_nonneg hnn] at hfin

end Work.BoseBoxFock
