import Mathlib
import Submission.Work.NN.Assemble.DbarJSolver
import Submission.Work.NN.Final.flatOne
import Submission.Work.NN.Core.flat_projection_eq
import Submission.Work.CR.Flat.Holder

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Assemble

variable {n : ℕ} {α : ℝ}

/-! ## Elementary bridges between the form-level and coefficient-level language

The standard structure `JstdCn n` is multiplication by `i`, so a `Jstd`-antilinear form is
determined by its coefficients on the standard basis, and the `(0,2)`-projection of the exterior
derivative of `stdForm ψ` is the classical coefficient expression `∂̄_k ψ_l - ∂̄_l ψ_k` of
`Work.NN.Core.flat_projection_eq`.  These two facts are what transport `Work.NN.Final.flatOne`
(the `(0,1)`-level Poincaré lemma for the standard structure, stated in coefficients) to the
form-level interface `Work.NN.Assemble.DbarJSolver` at `A = 0`.
-/

/-- The `j`-th coefficient of a family of `(0,1)`-forms is as smooth as the family. -/
lemma contDiff_coeff {m : WithTop ℕ∞} {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hf : ContDiff ℝ m f) (j : Fin n) :
    ContDiff ℝ m (fun z : Work.NN.Core.Cn n => f z (Pi.single j (1 : ℂ))) := by
  have h := hf.clm_apply (contDiff_const (c := (Pi.single j (1 : ℂ) : Work.NN.Core.Cn n)))
  simpa using h

/-- **A `Jstd`-antilinear `(0,1)`-form is the standard form of its coefficients.** -/
lemma stdForm_coeff_eq {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hanti : ∀ z v, f z (Work.NN.Core.JstdCn n z v) = -Complex.I * f z v)
    (z : Work.NN.Core.Cn n) :
    Work.NN.Core.stdForm (fun j (z' : Work.NN.Core.Cn n) => f z' (Pi.single j (1 : ℂ))) z
      = f z := by
  refine Work.NN.Core.form_ext_basis (f := Work.NN.Core.stdForm _ z) (g := f z) ?_ ?_
  · intro j
    rw [Work.NN.Core.stdForm_single]
  · intro j
    rw [Work.NN.Core.stdForm_single_I, ← Work.NN.Core.smul_single_I j,
      ← Work.NN.Core.JstdCn_apply n z (Pi.single j (1 : ℂ))]
    rw [hanti z (Pi.single j (1 : ℂ))]

/-- **The `(0,2)`-projection of `d (stdForm ψ)` on the standard basis is the coefficient
closedness defect.** -/
lemma proj02_std_dOne_stdForm_single {ψ : Fin n → Work.NN.Core.Cn n → ℂ}
    (hψ : ∀ m, ContDiff ℝ 1 (ψ m)) (z : Work.NN.Core.Cn n) (k l : Fin n) :
    Work.NN.Final.proj02 (Work.NN.Core.JstdCn n)
        (fun z' => Work.NN.Final.dOne (Work.NN.Core.stdForm ψ) z') z
        (Pi.single k (1 : ℂ)) (Pi.single l (1 : ℂ))
      = Work.CR.Flat.dbarCoord k (ψ l) z - Work.CR.Flat.dbarCoord l (ψ k) z := by
  simp only [Work.NN.Final.proj02, Work.NN.Final.dOne, Work.NN.Core.JstdCn_apply,
    Work.NN.Core.smul_single_I]
  exact Work.NN.Core.flat_projection_eq hψ z k l

/-- **Form-level closedness of a `Jstd`-antilinear datum implies coefficient-level closedness.**
A `Jstd`-antilinear `(0,1)`-form `f` whose exterior derivative has vanishing `(0,2)`-projection is
`∂̄₀`-closed: its coefficient family `z ↦ f z (e_j)` satisfies `Clos1`. -/
lemma clos1_of_proj02 {ρ : Fin n → ℝ} {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hanti : ∀ z v, f z (Work.NN.Core.JstdCn n z v) = -Complex.I * f z v)
    (hf : ContDiff ℝ 1 f)
    (hcl : ∀ z ∈ Work.NN.Final.pd n ρ 4, ∀ V W : Work.NN.Core.Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n) (fun z' => Work.NN.Final.dOne f z') z V W
        = 0) :
    Work.NN.Final.Clos1 n ρ 4
      (fun j (z : Work.NN.Core.Cn n) => f z (Pi.single j (1 : ℂ))) := by
  let ψ : Fin n → Work.NN.Core.Cn n → ℂ := fun i z' => f z' (Pi.single i (1 : ℂ))
  have hcoe : f = fun w => Work.NN.Core.stdForm ψ w := by
    funext w
    exact (stdForm_coeff_eq hanti w).symm
  have hfun : (fun z' => Work.NN.Final.dOne f z')
      = (fun z' => Work.NN.Final.dOne (Work.NN.Core.stdForm ψ) z') := by
    rw [hcoe]
  have hψ : ∀ m : Fin n, ContDiff ℝ 1 (ψ m) := fun m => contDiff_coeff hf m
  intro j l z hz
  have h := hcl z hz (Pi.single j (1 : ℂ)) (Pi.single l (1 : ℂ))
  rw [hfun, proj02_std_dOne_stdForm_single hψ z j l] at h
  exact sub_eq_zero.mp h

/-- The zero perturbation of the standard structure is the standard structure itself. -/
lemma JstdCn_add_zero :
    (Work.NN.Core.JstdCn n + (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)))
      = Work.NN.Core.JstdCn n := by
  funext y
  simp

/-- `IsJAntilinear` for the zero perturbation is exactly `Jstd`-antilinearity. -/
lemma isJAntilinear_zero_apply {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hanti : IsJAntilinear (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)) f) :
    ∀ z v, f z (Work.NN.Core.JstdCn n z v) = -Complex.I * f z v :=
  fun z v => by simpa using hanti z v

/-- **`stdForm` reconstruction from the `DbarJSolver`-shaped antilinearity hypothesis.** -/
lemma stdForm_coeff_eq_of_isJAntilinear
    {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hanti : IsJAntilinear (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)) f)
    (z : Work.NN.Core.Cn n) :
    Work.NN.Core.stdForm (fun j (z' : Work.NN.Core.Cn n) => f z' (Pi.single j (1 : ℂ))) z
      = f z :=
  stdForm_coeff_eq (isJAntilinear_zero_apply hanti) z

/-- **The `DbarJSolver` closedness hypothesis at `A = 0` is coefficient-level closedness.**
This is `clos1_of_proj02` with its hypotheses exactly in the shape in which the fields of
`Work.NN.Assemble.DbarJSolver` provide them, so that the transport to `Work.NN.Final.flatOne`
becomes a one-liner. -/
lemma clos1_of_dbarJSolver_hyp {ρ : Fin n → ℝ}
    {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hanti : IsJAntilinear (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)) f)
    (hf : ContDiff ℝ 1 f)
    (hcl : ∀ z ∈ Work.NN.Final.pd n ρ 4, ∀ V W : Work.NN.Core.Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n
        + (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)))
        (fun z' => Work.NN.Final.dOne f z') z V W = 0) :
    Work.NN.Final.Clos1 n ρ 4
      (fun j (z : Work.NN.Core.Cn n) => f z (Pi.single j (1 : ℂ))) := by
  refine clos1_of_proj02 (isJAntilinear_zero_apply hanti) hf ?_
  intro z hz V W
  have h := hcl z hz V W
  rwa [JstdCn_add_zero] at h

/-- The `(0,1)`-data of the standard structure: `T1 ψ` solves `∂̄₀ v = stdForm ψ` on the smaller
polydisc as soon as `ψ` is `∂̄₀`-closed and `C¹` there. -/
lemma dbarCn_std_T1_eq {ρ : Fin n → ℝ} (F : Work.NN.Final.FlatOne n α ρ)
    {ψ : Fin n → Work.NN.Core.Cn n → ℂ}
    (hψ : ∀ j, ContDiffOn ℝ (1 : ℕ∞) (ψ j) (Work.NN.Final.pd n ρ 4))
    (hcl : Work.NN.Final.Clos1 n ρ 4 ψ) {z : Work.NN.Core.Cn n}
    (hz : z ∈ Work.NN.Final.pd n ρ 2) :
    Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n) (F.T1 ψ) z
      = Work.NN.Core.stdForm ψ z := by
  rw [Work.NN.Core.dbarCn_std_eq_stdForm]
  refine Work.NN.Core.stdForm_ext fun j => ?_
  exact F.T1_solves ψ hψ hcl j z hz

/-- **The unperturbed case of the `∂̄_J`-Poincaré input: `A = 0`.**  For the standard structure
`JstdCn n`, the interface `Work.NN.Assemble.DbarJSolver` is inhabited: solving `∂̄₀ v = f` for a
`∂̄₀`-closed `(0,1)`-form `f` on the nested polydiscs with the `C^{1,α}` gain and smoothness is the
content of `Work.NN.Final.FlatOne` (`flatOne`), transported through the bridges
`Work.NN.Core.stdForm` / `dbarCn_std_eq_stdForm` (a `Jstd`-antilinear form is `stdForm` of its
coefficients `f (·) (e_m)`, and the form-level closedness `proj02 Jstd (dOne f) = 0` is the
coefficient-level `Clos1` of those coefficients).

This is the base case of `NN/Assemble/nonempty_dbarJSolver_small` and is expected to be the
starting point of any perturbative proof of it (Neumann series / small-`A` argument). -/
theorem nonempty_dbarJSolver_std {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    Nonempty (Work.NN.Assemble.DbarJSolver (n := n) α ρ
      (fun _ => (0 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n))) := by
  obtain ⟨F⟩ := Work.NN.Final.flatOne (n := n) (α := α) (ρ := ρ) hρ hα0 hα1
  refine ⟨{ C := max (F.C1 0) 1
            hC := lt_max_of_lt_left (F.hC1 0)
            T := fun f => F.T1 (fun j (z : Work.NN.Core.Cn n) => f z (Pi.single j (1 : ℂ)))
            solves := ?_
            est := ?_
            smooth := ?_ }⟩
  · intro f hf hanti hcl z hz
    let ψ : Fin n → Work.NN.Core.Cn n → ℂ := fun i z' => f z' (Pi.single i (1 : ℂ))
    have hψ1 : ∀ j, ContDiffOn ℝ (1 : ℕ∞) (ψ j) (Work.NN.Final.pd n ρ 4) :=
      fun j => (contDiff_coeff (hf 1) j).contDiffOn
    have hcl1 : Work.NN.Final.Clos1 n ρ 4 ψ := clos1_of_dbarJSolver_hyp hanti (hf 1) hcl
    rw [JstdCn_add_zero]
    show Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n) (F.T1 ψ) z = f z
    rw [Work.NN.Core.dbarCn_std_eq_stdForm, ← stdForm_coeff_eq_of_isJAntilinear hanti z]
    refine Work.NN.Core.stdForm_ext (fun j => ?_)
    exact F.T1_solves ψ hψ1 hcl1 j z (Work.NN.Final.pd_one_subset_two hρ hz)
  · intro f hf hanti hcl
    let ψ : Fin n → Work.NN.Core.Cn n → ℂ := fun i z' => f z' (Pi.single i (1 : ℂ))
    have hψ1 : ∀ j, ContDiffOn ℝ (1 : ℕ∞) (ψ j) (Work.NN.Final.pd n ρ 4) :=
      fun j => (contDiff_coeff (hf 1) j).contDiffOn
    have hcl1 : Work.NN.Final.Clos1 n ρ 4 ψ := clos1_of_dbarJSolver_hyp hanti (hf 1) hcl
    show Work.CR.Flat.holderNorm 1 α (F.T1 ψ) (Work.NN.Final.pd n ρ 1)
      ≤ ENNReal.ofReal (max (F.C1 0) 1)
        * ∑ m : Fin n, Work.CR.Flat.holderNorm 0 α (ψ m) (Work.NN.Final.pd n ρ 4)
    calc Work.CR.Flat.holderNorm 1 α (F.T1 ψ) (Work.NN.Final.pd n ρ 1)
        ≤ Work.CR.Flat.holderNorm 1 α (F.T1 ψ) (Work.NN.Final.pd n ρ 2) :=
          Work.CR.Flat.holderNorm_mono_set (Work.NN.Final.isOpen_pd ρ 2)
            (Work.NN.Final.isOpen_pd ρ 1) (Work.NN.Final.pd_one_subset_two hρ) 1 α _
      _ ≤ ENNReal.ofReal (F.C1 0)
            * ∑ m : Fin n, Work.CR.Flat.holderNorm 0 α (ψ m) (Work.NN.Final.pd n ρ 4) :=
          F.T1_est 0 ψ hψ1 hcl1
      _ ≤ ENNReal.ofReal (max (F.C1 0) 1)
            * ∑ m : Fin n, Work.CR.Flat.holderNorm 0 α (ψ m) (Work.NN.Final.pd n ρ 4) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  · intro f hf hanti hcl m
    let ψ : Fin n → Work.NN.Core.Cn n → ℂ := fun i z' => f z' (Pi.single i (1 : ℂ))
    have hcl1 : Work.NN.Final.Clos1 n ρ 4 ψ := clos1_of_dbarJSolver_hyp hanti (hf 1) hcl
    have hf_top : ContDiff ℝ ∞ f :=
      (contDiff_iff_forall_nat_le (𝕜 := ℝ) (f := f) (n := (⊤ : ℕ∞))).2 (fun k _ => hf k)
    have hψ_top : ∀ j, ContDiffOn ℝ ∞ (ψ j) (Work.NN.Final.pd n ρ 4) :=
      fun j => (contDiff_coeff hf_top j).contDiffOn
    show ContDiffOn ℝ m (F.T1 ψ) (Work.NN.Final.pd n ρ 1)
    exact ((F.T1_smooth ψ hψ_top hcl1).of_le Work.NN.Final.coe_le_infty).mono
      (Work.NN.Final.pd_one_subset_two hρ)

end Work.NN.Assemble
