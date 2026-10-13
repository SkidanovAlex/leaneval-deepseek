/-
  WilE9G / Lagrange — **`degenH_fderiv_surjective`**.

  At a Lagrange point `p = (z, (ν,ν₀), c)` of the genericity step with `ν₀ ≠ 0` and `Φ(z) > 0`, the
  differential of the system

    `degenH S Phi = (h_a(z))_a , degenLam(z,ν,ν₀) , (degenPsi_l(z,ν,ν₀,c))_l`

  is surjective.  The reason is its block structure:

  * `h`-rows:  `v ↦ ∑_l ∂_l h_a(z) · vz_l` (rank `S.j` by `S.Good`, so surjective onto `ℝ^{S.j}`),
  * `λ`-row:   `v ↦ ∑_a 2 ν_a · vν_a` (surjective as `ν₀ ≠ 0`),
  * `ψ`-rows:  carry the diagonal block `ν₀ Φ(z) · δ_{ll'}` in the `c`-coordinates,

  so one can solve the three blocks successively: `vz` from `S.Good`, the `ν₀`-coordinate from the
  normalisation, and then the `c`-coordinates correct the Lagrange rows (`Φ(z) > 0` and `ν₀ ≠ 0`
  make the diagonal invertible).

  The differential itself is computed in `Submission.Work.WilE9G.Lagrange.DegenDiff`
  (`degenDCLM`, with rows `eaDRow`, `rowLam`, `rowPsi`); the three block computations are
  `hasFDerivAt_eaDRow`, `hasFDerivAt_rowLam`, `hasFDerivAt_rowPsi` and the surjectivity of the
  `h`-block is `surjective_hBlock`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE9G.Lagrange.DegenDiff
import Submission.Work.WilE9G.Lagrange.hasFDerivAt_rowPsi
import Submission.Work.WilE9G.Lagrange.hasFDerivAt_rowLam
import Submission.Work.WilE9G.Lagrange.surjective_hBlock
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## The differential of `degenH` -/

theorem hasFDerivAt_degenH_DCLM (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ) :
    HasFDerivAt (degenH S Phi) (degenDCLM S Phi p) p := by
  have hproj : ∀ r : Fin (S.j + (1 + (1 + m))),
      (ContinuousLinearMap.proj r) ∘SL (degenDCLM S Phi p) = degenRow S Phi p r := by
    intro r
    ext v
    exact degenDCLM_apply S Phi p v r
  rw [hasFDerivAt_pi']
  intro r
  rw [hproj r]
  refine Fin.addCases (motive := fun r => HasFDerivAt
    (fun x : Fin (degenDim n m S.j) → ℝ => degenH S Phi x r) (degenRow S Phi p r) p) ?_ ?_ r
  · intro a
    rw [show (fun x : Fin (degenDim n m S.j) → ℝ =>
          degenH S Phi x (Fin.castAdd (1 + (1 + m)) a))
        = fun x => eaEval S.X.c (S.h a) (degenZ x) from
          funext fun x => by simp only [degenH, Fin.append_left],
      show degenRow S Phi p (Fin.castAdd (1 + (1 + m)) a) = eaDRow S (S.h a) p from by
          simp only [degenRow, Fin.addCases_left]]
    exact hasFDerivAt_eaDRow S (S.h a) p
  · intro s
    refine Fin.addCases (motive := fun s => HasFDerivAt
      (fun x : Fin (degenDim n m S.j) → ℝ => degenH S Phi x (Fin.natAdd S.j s))
      (degenRow S Phi p (Fin.natAdd S.j s)) p) ?_ ?_ s
    · intro u
      rw [show (fun x : Fin (degenDim n m S.j) → ℝ =>
            degenH S Phi x (Fin.natAdd S.j (Fin.castAdd (1 + m) u)))
          = fun x => degenLam S x from
            funext fun x => by simp only [degenH, Fin.append_right, Fin.append_left],
        show degenRow S Phi p (Fin.natAdd S.j (Fin.castAdd (1 + m) u)) = rowLam S p from by
            simp only [degenRow, Fin.addCases_right, Fin.addCases_left]]
      exact hasFDerivAt_rowLam S p
    · intro l
      rw [show (fun x : Fin (degenDim n m S.j) → ℝ =>
            degenH S Phi x (Fin.natAdd S.j (Fin.natAdd 1 l)))
          = fun x => degenPsi S Phi x l from
            funext fun x => by simp only [degenH, Fin.append_right],
        show degenRow S Phi p (Fin.natAdd S.j (Fin.natAdd 1 l)) = rowPsi S Phi p l from by
            simp only [degenRow, Fin.addCases_right]]
      exact hasFDerivAt_rowPsi S Phi p l

theorem fderiv_degenH_DCLM (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ) :
    fderiv ℝ (degenH S Phi) p = degenDCLM S Phi p :=
  (hasFDerivAt_degenH_DCLM S Phi p).fderiv

/-! ## Surjectivity of the differential -/

theorem degenDCLM_surjective (S : AmbStratum (n + (1 + m))) (hS : S.Good)
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (hPhi : ∀ z ∈ S.X.set, 0 < eaEval S.X.c Phi z)
    (p : Fin (degenDim n m S.j) → ℝ) (hz : degenZ p ∈ S.X.set)
    (hν0 : degenNu p (Fin.last S.j) ≠ 0) :
    Function.Surjective (degenDCLM S Phi p) := by
  intro w
  have hΦ : 0 < eaEval S.X.c Phi (degenZ p) := hPhi (degenZ p) hz
  have hΦne : eaEval S.X.c Phi (degenZ p) ≠ 0 := ne_of_gt hΦ
  have hν0' : 2 * degenNu p (Fin.last S.j) ≠ 0 := by
    intro h
    exact hν0 (by linarith)
  have hne : degenNu p (Fin.last S.j) * eaEval S.X.c Phi (degenZ p) ≠ 0 :=
    mul_ne_zero hν0 hΦne
  -- the `h`-block: solve for the `z`-coordinates
  obtain ⟨vz, hvz⟩ := surjective_hBlock S hS (degenZ p) hz
    (fun a => w (Fin.castAdd (1 + (1 + m)) a))
  have hvz' : ∀ a : Fin S.j,
      ∑ l : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c l (S.h a)) (degenZ p) * vz l
        = w (Fin.castAdd (1 + (1 + m)) a) := fun a => congrFun hvz a
  -- the `ν₀`-coordinate: solve for the normalisation row
  set x₀ : ℝ := w (Fin.natAdd S.j (Fin.castAdd (1 + m) (0 : Fin 1)))
      / (2 * degenNu p (Fin.last S.j)) with hx₀
  set vν : Fin (S.j + 1) → ℝ := Pi.single (Fin.last S.j) x₀ with hvν
  set v₀ : Fin (degenDim n m S.j) → ℝ := degenPt vz vν (0 : Fin (1 + m) → ℝ) with hv₀
  -- the `c`-coordinates: solve for the Lagrange rows
  set vc : Fin (1 + m) → ℝ := fun l =>
      (w (Fin.natAdd S.j (Fin.natAdd 1 l))
        - degenDCLM S Phi p v₀ (Fin.natAdd S.j (Fin.natAdd 1 l)))
        / (degenNu p (Fin.last S.j) * eaEval S.X.c Phi (degenZ p)) with hvc
  have hvc' : ∀ l : Fin (1 + m), vc l
      = (w (Fin.natAdd S.j (Fin.natAdd 1 l))
        - degenDCLM S Phi p v₀ (Fin.natAdd S.j (Fin.natAdd 1 l)))
        / (degenNu p (Fin.last S.j) * eaEval S.X.c Phi (degenZ p)) :=
    fun l => by rw [hvc]
  refine ⟨v₀ + degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc, ?_⟩
  have hZ₀ : ∀ l : Fin (n + (1 + m)), degenZ v₀ l = vz l := by
    intro l
    simp only [degenZ_eq_apply, hv₀, degenPt_zIdx]
  have hZc : ∀ l : Fin (n + (1 + m)),
      degenZ (degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc) l = 0 := by
    intro l
    simp only [degenZ_eq_apply, degenPt_zIdx, Pi.zero_apply]
  have hNu₀ : ∀ a : Fin (S.j + 1), degenNu v₀ a = vν a := by
    intro a
    simp only [degenNu_eq_apply, hv₀, degenPt_nuIdx]
  have hNuc : ∀ a : Fin (S.j + 1),
      degenNu (degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc) a = 0 := by
    intro a
    simp only [degenNu_eq_apply, degenPt_nuIdx, Pi.zero_apply]
  funext r
  refine Fin.addCases (motive := fun r => degenDCLM S Phi p
    (v₀ + degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc) r = w r) ?_ ?_ r
  · intro a
    rw [map_add, Pi.add_apply, degenDCLM_apply, degenDCLM_apply,
      show degenRow S Phi p (Fin.castAdd (1 + (1 + m)) a) = eaDRow S (S.h a) p from by
        simp only [degenRow, Fin.addCases_left],
      eaDRow_apply, eaDRow_apply]
    simp only [hZ₀, hZc, mul_zero, Finset.sum_const_zero, add_zero]
    exact hvz' a
  · intro s
    refine Fin.addCases (motive := fun s => degenDCLM S Phi p
      (v₀ + degenPt (0 : Fin (n + (1 + m)) → ℝ) (0 : Fin (S.j + 1) → ℝ) vc)
      (Fin.natAdd S.j s) = w (Fin.natAdd S.j s)) ?_ ?_ s
    · intro u
      have hu : u = (0 : Fin 1) := Subsingleton.elim u 0
      rw [hu, map_add, Pi.add_apply, degenDCLM_apply, degenDCLM_apply,
        show degenRow S Phi p (Fin.natAdd S.j (Fin.castAdd (1 + m) (0 : Fin 1))) = rowLam S p
          from by simp only [degenRow, Fin.addCases_right, Fin.addCases_left],
        rowLam_apply, rowLam_apply]
      simp only [hNu₀, hNuc, mul_zero, Finset.sum_const_zero, add_zero]
      rw [hvν]
      rw [Finset.sum_eq_single (Fin.last S.j)]
      · rw [Pi.single_eq_same, hx₀]
        field_simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hb
        exact absurd (Finset.mem_univ (Fin.last S.j)) hb
    · intro l
      have hpsirow : degenRow S Phi p (Fin.natAdd S.j (Fin.natAdd 1 l)) = rowPsi S Phi p l := by
        simp only [degenRow, Fin.addCases_right]
      have hpsiv₀ : degenDCLM S Phi p v₀ (Fin.natAdd S.j (Fin.natAdd 1 l))
          = rowPsi S Phi p l v₀ := by
        rw [degenDCLM_apply, hpsirow]
      rw [map_add, Pi.add_apply, degenDCLM_apply, degenDCLM_apply, hpsirow,
        rowPsi_apply_degenPt, hvc' l, hpsiv₀]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
      ring

/-! ## The target -/

theorem degenH_fderiv_surjective {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (hPhi : ∀ z ∈ S.X.set, 0 < WilkiesDesign.E.eaEval S.X.c Phi z)
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ)
    (hz : Work.WilE9G.Lagrange.degenZ p ∈ S.X.set)
    (hν0 : Work.WilE9G.Lagrange.degenNu p (Fin.last S.j) ≠ 0) :
    Function.Surjective (fderiv ℝ (Work.WilE9G.Lagrange.degenH S Phi) p) := by
  rw [fderiv_degenH_DCLM]
  exact degenDCLM_surjective S hS Phi hPhi p hz hν0

end Work.WilE9G.Lagrange
