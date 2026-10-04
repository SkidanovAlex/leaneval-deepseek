import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.B3.norm_multilinear_le_of_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `iteratedFDeriv_le_of_pdVec`

`Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec`: a bound on the iterated Fréchet derivative
`iteratedFDeriv ℝ m f z` of a smooth function `f : (Fin n → ℝ) → ℝ` in terms of the
*partial-derivative vectors* `Work.Diff.STE.pdVec m β (fun y ↦ (f y : ℂ)) z`.

The mathematical content is the elementary identity

`pdVec m γ g z = iteratedFDeriv ℝ m g z (fun i ↦ Pi.single (γ i) 1)`

(evaluation of the iterated derivative on the tuple of standard basis vectors), together with
the fact that a continuous multilinear map on `(Fin n → ℝ)^m` is bounded by `n^m` times the
supremum of its values on the standard basis tuples
(`Work.Diff.STE.B3.norm_multilinear_le_of_basis`).

The identity above is `Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv` in the *global* case
(`ContDiff ℝ ⊤ g`).  Here only `ContDiffAt ℝ ⊤ f z` is assumed, so we prove the corresponding
*local* statement `pdVec_eq_iteratedFDeriv_at` first: the induction is run on an open
neighbourhood `V` of `z` on which `f` is `C^{k+1}` (which exists because `ContDiffAt ℝ ↑⊤` at
level `∞` means `C^m` at `z` for every finite `m`).  The only place where a neighbourhood is
needed is the step from level `j` to level `j+1`, where the identity of `fderiv`s requires the
two functions to agree *near* `z` (and the differentiability of `y ↦ iteratedFDeriv ℝ j f y`).
-/

namespace Work.Diff.STE.B3

/-- **Dictionary lemma (local form).**  For a function `f : (ι → ℝ) → ℂ` that is smooth at `z`,
the iterated partial derivative `pdVec k l f z` is the iterated Fréchet derivative
`iteratedFDeriv ℝ k f z` evaluated on the tuple of standard basis vectors
`(Pi.single (l 0) 1, …, Pi.single (l (k-1)) 1)`.

This is the pointwise/local version of `Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv` (which
assumes global smoothness `ContDiff ℝ ⊤ f`). -/
lemma pdVec_eq_iteratedFDeriv_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ} {z : ι → ℝ} (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z)
    (k : ℕ) (l : Fin k → ι) :
    Work.Diff.STE.pdVec k l f z = iteratedFDeriv ℝ k f z (fun j => Pi.single (l j) 1) := by
  -- `ContDiffAt ℝ ∞ f z` means `C^m` at `z` for every finite `m`.
  have hfin : ∀ m : ℕ, ContDiffAt ℝ (m : ℕ∞) f z := contDiffAt_infty.mp hf
  -- hence `f` is `C^{k+1}` on an open neighbourhood `V` of `z`.
  obtain ⟨V, hVopen, hzV, hVsmooth⟩ :=
    (hfin (k+1)).contDiffOn' le_rfl (by intro h; simp at h)
  have hVsmooth : ContDiffOn ℝ (k+1) f V := by simpa using hVsmooth
  -- the definitional recursion of `pdVec`, peeling the first index.
  have hpd : ∀ (j : ℕ) (l : Fin (j+1) → ι),
      Work.Diff.STE.pdVec (j+1) l f
        = Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec j (Fin.tail l) f) := by
    intro j l
    have h : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
      conv_lhs => rw [← Fin.cons_self_tail l]
      rw [List.ofFn_cons]
    simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [h, List.foldr_cons]
  -- the induction on `V`
  have key : ∀ (j : ℕ), j ≤ k → ∀ (l : Fin j → ι) (y : ι → ℝ), y ∈ V →
      Work.Diff.STE.pdVec j l f y = iteratedFDeriv ℝ j f y (fun i => Pi.single (l i) 1) := by
    intro j
    induction j with
    | zero =>
      intro _ l y _
      rw [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]
      exact (iteratedFDeriv_zero_apply (fun j => Pi.single (l j) 1)).symm
    | succ j ih =>
      intro hj1 l y hyV
      have hj : j ≤ k := by omega
      rw [hpd j l]
      simp only [Work.Diff.STE.pd]
      -- the two functions agree on the open set `V ∋ y`, hence have the same `fderiv` at `y`.
      have hev : (fun y' => Work.Diff.STE.pdVec j (Fin.tail l) f y') =ᶠ[nhds y]
          (fun y' => iteratedFDeriv ℝ j f y' (fun i => Pi.single ((Fin.tail l) i) 1)) := by
        filter_upwards [hVopen.mem_nhds hyV] with y' hy'
        rw [ih hj (Fin.tail l) y' hy']
      rw [Filter.EventuallyEq.fderiv_eq hev]
      -- differentiability of the `j`-th iterated derivative at `y`, from `V`-smoothness.
      have hAy : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) y := by
        have hy : ContDiffAt ℝ ((k+1 : ℕ) : ℕ∞) f y :=
          hVsmooth.contDiffAt (hVopen.mem_nhds hyV)
        have h2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (iteratedFDeriv ℝ j f) y :=
          hy.iteratedFDeriv_right (m := 1) (i := j) (by exact_mod_cast (by omega : 1 + j ≤ k + 1))
        exact h2.differentiableAt (by norm_num)
      -- pull the constant multilinear argument out of the `fderiv` …
      rw [fderiv_continuousMultilinear_apply_const_apply hAy
        (fun i => Pi.single ((Fin.tail l) i) 1) (Pi.single (l 0) 1)]
      -- … and read off the definition of `iteratedFDeriv` one step further.
      rw [iteratedFDeriv_succ_apply_left]
      rfl
  exact key k le_rfl l z hzV

/-- **Complexified partial derivatives.**  For a real-valued `f`, the partial-derivative vectors
of the complexification `y ↦ (f y : ℂ)` are the complexifications of the iterated derivative of
`f` evaluated on the standard basis tuple. -/
lemma pdVec_ofReal_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {z : ι → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (k : ℕ) (l : Fin k → ι) :
    Work.Diff.STE.pdVec k l (fun y => ((f y : ℝ) : ℂ)) z
      = ((iteratedFDeriv ℝ k f z (fun i => Pi.single (l i) 1) : ℝ) : ℂ) := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ((f y : ℝ) : ℂ)) z :=
    ContDiffAt.comp z Complex.ofRealCLM.contDiff.contDiffAt hf
  rw [pdVec_eq_iteratedFDeriv_at hg k l]
  rw [show (fun y => ((f y : ℝ) : ℂ)) = (⇑Complex.ofRealCLM ∘ f) from rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM hf
    (by simp : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))]
  rfl

theorem iteratedFDeriv_le_of_pdVec {n M : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (Kd : ℝ), 0 ≤ Kd →
        ContDiffAt ℝ (⊤ : ℕ∞) f z →
        (∀ m ≤ M, ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (fun y => ((f y : ℝ) : ℂ)) z‖ ≤ Kd) →
        ∀ m ≤ M, ‖iteratedFDeriv ℝ m f z‖ ≤ C * Kd := by
  refine ⟨((n : ℝ) + 1) ^ M, by positivity, ?_⟩
  intro f z Kd hKd hf hpd m hm
  -- the hypothesis bounds the iterated derivative on the standard basis tuples
  have hb : ∀ γ : Fin m → Fin n,
      ‖iteratedFDeriv ℝ m f z (fun i => Pi.single (γ i) 1)‖ ≤ Kd := by
    intro γ
    have h := hpd m hm γ
    rw [pdVec_ofReal_eq hf m γ] at h
    simpa using h
  -- a multilinear map is bounded by `n^m` times its values on the basis tuples
  have hnorm := norm_multilinear_le_of_basis (Φ := iteratedFDeriv ℝ m f z) hKd hb
  calc ‖iteratedFDeriv ℝ m f z‖ ≤ (n : ℝ) ^ m * Kd := hnorm
    _ ≤ ((n : ℝ) + 1) ^ m * Kd := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        refine mul_le_mul_of_nonneg_right ?_ hKd
        exact pow_le_pow_left₀ hn (by linarith) m
    _ ≤ ((n : ℝ) + 1) ^ M * Kd := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        refine mul_le_mul_of_nonneg_right ?_ hKd
        exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hm

end Work.Diff.STE.B3
