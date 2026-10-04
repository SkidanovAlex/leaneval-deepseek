import Mathlib
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.B3.J_finite_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: the chart data of a single spanning vector `jVec` of the Galerkin family

`Work.Diff.STE.B3.jFamily D ε` is the finite spanning family of the range of the Friedrichs
mollifier `J ρ ε`, with members

  `jVec D ε i a b q (p) =
      (ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹ · modeFun q (coord i p))
        • (eᵢa♭ ⊗ eᵢb♭)`

(`Work.Diff.STE.B3.jVec`).  The Galerkin scheme of Layer D lives in the span of this family
(`Work.Diff.STE.D.genMap`), and each *smooth* span element with a positive definite pairing is the
tensor of a global smooth metric (`Work.Diff.STE.D.smetOf`).  The smoothness of the span elements
is `Work.Diff.STE.D.ChartData_genMap`; the present file proves it for the spanning vectors
themselves, which is the basic case (and the one the `J_mem_span` bookkeeping reduces to).

**The reduction.**  Each `jVec D ε i a b q` is the reconstruction `D.Rstar i u` of the *single*
component function `u a' b' = δ_{a'a} δ_{b'b} · modeFun q`:  the defining formula
`Work.Diff.STE.B3.Rstar_apply` evaluates `Rstar i u` at `(X, Y)` as the coefficient

  `ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹`

times the double sum `Σ_{a'b'} u a' b' (coord i p) · ⟪X, eᵢa'⟫ · ⟪Y, eᵢb'⟫`, which for the delta
component collapses to `modeFun q (coord i p) · ⟪X, eᵢa⟫ · ⟪Y, eᵢb⟫` — exactly the value of
`jVec`.  This is `jVec_eq_Rstar` below (a double `Finset.sum_eq_single`).

The smoothness hypothesis `hu` of `Work.Diff.STE.D.ChartData_Rstar` is then the smoothness of the
Fourier mode `modeFun q` (`contDiff_modeFun`, from the smoothness of the character
`Work.Diff.STE.fourierExp`), and the conclusion follows.
-/

namespace Work.Diff.STE.D

/-- **The real Fourier mode `modeFun q` is `C^∞`.**  `modeFun q` is the real (resp. imaginary) part
of the character `Work.Diff.STE.fourierExp m`, which is the exponential of a real-linear (hence
smooth) function of the coordinates, and the real and imaginary parts of `ℂ` are continuous linear
functionals over `ℝ` (`Complex.reCLM`, `Complex.imCLM`). -/
lemma contDiff_modeFun (n : ℕ) (ε : ℝ) (q : Work.Diff.STE.B3.QIdx n ε) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.modeFun n q) := by
  obtain ⟨m, s⟩ := q
  -- The character is smooth: it is `exp` of a real-linear function of `z`.
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.fourierExp m.1) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Fin n → ℝ => ∑ i, (m.1 i : ℂ) * ((x i : ℝ) : ℂ)) := by
      refine ContDiff.sum (fun i _ => ?_)
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (by fun_prop))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ =>
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ∑ i, (m.1 i : ℂ) * ((x i : ℝ) : ℂ)) :=
      (contDiff_const (c := (2 : ℂ) * (Real.pi : ℂ) * Complex.I)).mul h1
    unfold Work.Diff.STE.fourierExp
    exact Complex.contDiff_exp.comp h2
  cases s
  · -- the real part
    show ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℝ => (Work.Diff.STE.fourierExp m.1 z).re)
    exact Complex.reCLM.contDiff.comp hexp
  · -- the imaginary part
    show ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℝ => (Work.Diff.STE.fourierExp m.1 z).im)
    exact Complex.imCLM.contDiff.comp hexp

/-- **The spanning vector `jVec` is the reconstruction of a single Fourier mode.**  With the
component function `u a' b' = δ_{a'a} δ_{b'b} · modeFun q`, the reconstruction `Rstar i u` has the
same value as `jVec D ε i a b q` at every point and on every pair of vectors: the double sum of
`Rstar_apply` collapses onto the single index pair `(a,b)`. -/
lemma jVec_eq_Rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε) :
    Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q
      = D.Rstar i (fun a' b' z =>
          if a' = a ∧ b' = b then Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q z else 0) := by
  classical
  funext p
  apply ContinuousLinearMap.ext; intro X
  apply ContinuousLinearMap.ext; intro Y
  rw [Work.Diff.STE.B3.Rstar_apply]
  -- The value of `jVec` at `(X, Y)`.
  have hjv : Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q p X Y
      = (D.ζ i p * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)))⁻¹
          * Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q
              (Work.Diff.STE.coord (I := I) (D.x₀ i) p))
        * ((((g₀.inner p) X) (D.e i a p)) * (((g₀.inner p) Y) (D.e i b p))) := by
    simp only [Work.Diff.STE.B3.jVec, Work.Diff.STE.B3.jWgt, Work.Diff.STE.B3.jForm,
      ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    rw [g₀.symm p (D.e i a p) X, g₀.symm p (D.e i b p) Y]
  rw [hjv]
  -- The double sum over the component indices collapses onto `(a, b)`.
  have hsum : (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
      (if a' = a ∧ b' = b then
        Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
        else 0)
        * (((g₀.inner p) X) (D.e i a' p)) * (((g₀.inner p) Y) (D.e i b' p)))
      = Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
        * (((g₀.inner p) X) (D.e i a p)) * (((g₀.inner p) Y) (D.e i b p)) := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hb'
        simp [hb']
      · intro hb
        simp at hb
    · intro a' _ ha'
      rw [Finset.sum_eq_zero]
      intro b' _
      simp [ha']
    · intro ha
      simp at ha
  rw [hsum]
  ring

theorem ChartData_jVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q) := by
  rw [jVec_eq_Rstar D ε i a b q]
  refine ChartData_Rstar D i _ (fun a' b' => ?_)
  by_cases h : a' = a ∧ b' = b
  · have hfun : (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        if a' = a ∧ b' = b then Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q z else 0)
        = Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q := by
      funext z
      rw [ite_eq_left h]
    rw [hfun]
    exact contDiff_modeFun _ _ q
  · have hfun : (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        if a' = a ∧ b' = b then Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q z else 0)
        = 0 := by
      funext z
      rw [ite_eq_right h]
      rfl
    rw [hfun]
    exact contDiff_const

end Work.Diff.STE.D
