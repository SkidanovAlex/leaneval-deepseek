import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.flat.phi_bound
import Submission.Work.Diff.STE.flat.GalerkinSmooth
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.level_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the DeTurck nonlinearity along the jet of a Fourier series

`Work.Diff.STE.flat.continuousOn_phi_jet`: for a nonlinearity `Φ` of DeTurck shape and a
coefficient family `c` decaying faster than every polynomial in the weight `wt` (`hmom`), whose
real part is *symmetric* (`hsym`) and *uniformly elliptic* with constant `lam > 0` (`hell`), the
function

`x ↦ Φ (x, jetM (seriesFunM c) x)`

is continuous on the closed unit cube.

## Proof

Nothing here uses the equation.  Three facts are combined:

* `seriesFunM c` is `C^∞` (`contDiff_seriesFun`, entrywise in the coefficients `c k i j`), hence so
  are its first and second coordinate derivatives (`contDiff_pd_top`), hence the graph
  `x ↦ (x, jetM (seriesFunM c) x)` is continuous;
* symmetry plus the quadratic-form lower bound with `lam > 0` make `reMat (seriesFunM c x)`
  positive definite, so in particular `det (reMat (seriesFunM c x)) ≠ 0`
  (`reMat_det_ne_zero_of_elliptic`), i.e. the graph lands in the nondegeneracy locus
  `univ ×ˢ {w | (reMat w.1).det ≠ 0}`;
* `Φ` is `C^∞` — hence continuous — on that locus (`hshape`).

Composing gives the result, and `ContinuousOn` on the cube is a weakening of continuity.
-/
namespace Work.Diff.STE.flat

/-- The coordinate partial derivative of a smooth function `(Fin n → ℝ) → ℂ` is smooth.  (`pd d` is
`fderiv ℝ · (Pi.single d 1)`, and `fderiv` lowers the level by one while `⊤ : ℕ∞` is fixed by
`n ↦ n - 1`.)  (`private`: a sibling module declares the same name.) -/
private lemma contDiff_pd_top {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (d : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd d f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single d 1)) := h1.clm_apply contDiff_const
  rw [show Work.Diff.STE.pd d f
      = (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single d 1)) from rfl]
  exact h2

/-- A matrix-valued Fourier series with rapidly decaying coefficients is smooth. -/
lemma contDiff_seriesFunM {n : ℕ} (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hmom : ∀ (i j : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k i j‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.Flat.seriesFunM c) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j)
    (fun N => hmom i j N)
  simpa only [Work.Diff.STE.Flat.seriesFunM_apply] using h

/-- The spatial jet `x ↦ jetM (seriesFunM c) x` of a rapidly decaying Fourier series is
continuous. -/
lemma continuous_jetM_seriesFunM {n : ℕ} (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hmom : ∀ (i j : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k i j‖)) :
    Continuous (fun x : Fin n → ℝ =>
      Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) := by
  have hval : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c x i j) := by
    intro i j
    have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j)
      (fun N => hmom i j N)
    simpa only [Work.Diff.STE.Flat.seriesFunM_apply] using h
  have hpd1 : ∀ (c' i j : Fin n), ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ =>
        Work.Diff.STE.Flat.pdM c' (Work.Diff.STE.Flat.seriesFunM c) x i j) :=
    fun c' i j => contDiff_pd_top (hval i j) c'
  have hpd2 : ∀ (c' d i j : Fin n), ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => Work.Diff.STE.Flat.pdM c'
        (Work.Diff.STE.Flat.pdM d (Work.Diff.STE.Flat.seriesFunM c)) x i j) :=
    fun c' d i j => contDiff_pd_top (hpd1 d i j) c'
  have h0 : Continuous (fun x : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c x) :=
    continuous_pi (fun i => continuous_pi (fun j => (hval i j).continuous))
  have h1 : Continuous (fun x : Fin n → ℝ =>
      fun c' : Fin n => Work.Diff.STE.Flat.pdM c' (Work.Diff.STE.Flat.seriesFunM c) x) :=
    continuous_pi (fun c' => continuous_pi (fun i => continuous_pi (fun j =>
      (hpd1 c' i j).continuous)))
  have h2 : Continuous (fun x : Fin n → ℝ => fun c' d : Fin n => Work.Diff.STE.Flat.pdM c'
      (Work.Diff.STE.Flat.pdM d (Work.Diff.STE.Flat.seriesFunM c)) x) :=
    continuous_pi (fun c' => continuous_pi (fun d => continuous_pi (fun i =>
      continuous_pi (fun j => (hpd2 c' d i j).continuous))))
  have h3 := h0.prodMk (h1.prodMk h2)
  simpa only [Work.Diff.STE.Flat.jetM] using h3

theorem continuousOn_phi_jet {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam)
    (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hmom : ∀ (i j : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k i j‖))
    (hsym : ∀ (x : Fin n → ℝ) (i j : Fin n),
      Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j
        = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) j i)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * Finset.sum Finset.univ (fun i : Fin n => (v i) ^ 2) ≤
        Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j)))
    (i j : Fin n) :
    ContinuousOn (fun x : Fin n → ℝ =>
      Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨hΦ, -⟩ := hshape
  have hjet := continuous_jetM_seriesFunM c hmom
  have hJ : Continuous (fun x : Fin n → ℝ =>
      (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x)) :=
    continuous_id.prodMk hjet
  have hmem : ∀ x : Fin n → ℝ, (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x)
      ∈ Set.prod Set.univ
        {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} :=
    fun x => ⟨Set.mem_univ x,
      reMat_det_ne_zero_of_elliptic (Work.Diff.STE.Flat.seriesFunM c x) hlam (hsym x) (hell x)⟩
  have hcomp : Continuous (fun x : Fin n → ℝ =>
      Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x)) :=
    hΦ.continuousOn.comp_continuous hJ hmem
  have hcomp' : Continuous (fun x : Fin n → ℝ =>
      Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hcomp)
  exact hcomp'.continuousOn

end Work.Diff.STE.flat
