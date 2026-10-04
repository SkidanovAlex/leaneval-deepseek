import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.cap_avoid
import Submission.Work.Diff.C.gram_along
import Submission.Work.Diff.C.osc_lower
import Submission.Work.Diff.C.ray_cover
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.rgrad_comp_eventuallyEq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Shared helpers for the pointwise Gram estimate

These three lemmas are used both by `Submission.Work.Diff.C.gram_pointwise2` (the target) and by
`Submission.Work.Diff.C.gram_along_pair` (which needs `init_gram` for the base value of the Gram
matrix).  They live here so that neither file has to import the other.

* `cmDiff_psi_comp` — conclusion (1) of the target: `psi ∘ f` is `C^∞` if `f` is smooth on
  `{f ≥ -1+c}` and `psi ≡ -1+c` below `-1+c`;
* `rgrad_psi_comp` — the chain rule for the gradient of `ψ ∘ f`;
* `init_gram` — the target statement at the base point `p` (`A_ij(p) = δ_ij` and `Σ Fᵢ(p)² = 1`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Smoothness of the cutoff of a function that is smooth above `-1+c`.**
If `f : M → ℝ` is continuous, is `C^∞` at every point of the closed region `{f ≥ -1+c}`, and `ψ`
is smooth with `ψ ≡ -1+c` on `(-∞,-1+c]`, then `ψ ∘ f` is `C^∞` on all of `M`. -/
theorem cmDiff_psi_comp {c : ℝ} {ψ : ℝ → ℝ} (hψd : ContDiff ℝ ∞ ψ)
    (hψc : ∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c)
    {f : M → ℝ} (hcont : Continuous f)
    (hreg : ∀ x : M, -1 + c ≤ f x → CMDiffAt ∞ f x) :
    CMDiff ∞ (fun x : M => ψ (f x)) := by
  intro x
  rcases le_or_gt (-1 + c) (f x) with h | h
  · have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ (f x) :=
      hψd.contMDiff.contMDiffAt
    have h2 : CMDiffAt ∞ f x := hreg x h
    simpa only [Function.comp_def] using h1.comp x h2
  · have hopen : {y : M | f y < -1 + c} ∈ 𝓝 x :=
      (isOpen_lt hcont continuous_const).mem_nhds h
    have hconst : (fun y : M => ψ (f y)) =ᶠ[𝓝 x] (fun _ => -1 + c) := by
      filter_upwards [hopen] with y hy
      exact hψc (f y) (le_of_lt hy)
    exact contMDiffAt_const.congr_of_eventuallyEq hconst

/-- **The gradient of `ψ ∘ f`.**  With `ψ` smooth and `f` smooth at `x`,
`∇(ψ ∘ f)(x) = ψ'(f x) • ∇f x`. -/
theorem rgrad_psi_comp {ψ : ℝ → ℝ} (hψd : ContDiff ℝ ∞ ψ) {f : M → ℝ} {x : M}
    (hf : CMDiffAt ∞ f x) :
    rgrad (I := I) (fun y : M => ψ (f y)) x = deriv ψ (f x) • rgrad (I := I) f x := by
  have h := rgrad_comp_eventuallyEq (I := I) (c := ψ) (F := f) (x := x)
    (hψd.contDiffAt) hf
  exact h.eq_of_nhds

end Helpers

section InitGram

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The base point.**  At `p` the family of cutoff functions is exactly orthonormal for the Gram
pairing, and its squared sum is `1`.  This is the `x = p` case of `gram_pointwise2`, and the
starting point of the integration along the rays. -/
theorem init_gram {n : ℕ} {p : M} {e : Fin n → TangentSpace I p}
    {c : ℝ} {ψ : ℝ → ℝ}
    (hmet : IsMetricCompatible cov) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hsmC : ∀ (q x : M), -1 + c ≤ fcos (I := I) (M := M) q x →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) x)
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ s : ℝ, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ 2) ∧
      (∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) ∧ (∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c)) :
    (∑ i : Fin (n + 1), (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i p)) ^ 2 = 1) ∧
    (∀ i j : Fin (n + 1),
      gp (I := I) (M := M)
          (fun x : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x))
          (fun x : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j x)) p
        = if i = j then 1 else 0) := by
  classical
  have hpsi := psi_estimates hc hψ
  obtain ⟨hψd, -, -, hψid, hψconst⟩ := hψ
  obtain ⟨-, -, -, -, -, hderiv1, -, -, -, -⟩ := hpsi
  have hc2 : -1 + 2 * c < (0 : ℝ) := by linarith
  have hc3 : -1 + 2 * c < (1 : ℝ) := by linarith
  have hc4 : -1 + 2 * c ≤ (0 : ℝ) := le_of_lt hc2
  have hc5 : -1 + 2 * c ≤ (1 : ℝ) := le_of_lt hc3
  obtain ⟨hf0p, hg0p, hfi⟩ := hinit
  have hqpt0 : qpt (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (n + 1)) = p := by
    show Submission.GlobalExp.GExp (cov := cov) hmet p ((Real.pi / 2) • dirv e 0) = p
    have hdv0 : dirv (I := I) (p := p) e (0 : Fin (n + 1)) = 0 := Fin.cases_zero
    rw [hdv0, smul_zero]
    exact Submission.GlobalExp.GExp_zero hmet p
  have hdv0 : dirv (I := I) (p := p) e (0 : Fin (n + 1)) = 0 := Fin.cases_zero
  have hdvsucc : ∀ k : Fin n, dirv (I := I) (p := p) e (Fin.succ k) = e k := fun k =>
    Fin.cases_succ k
  have hF0 : fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (n + 1)) =
      fcos (I := I) (M := M) p := by
    show fcos (qpt (I := I) (M := M) (cov := cov) hmet p e 0) = fcos p
    rw [hqpt0]
  have hgradf0 : rgrad (I := I) (M := M)
      (fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (n + 1))) p = 0 := by
    rw [hF0]; exact hg0p
  have hgradfi : ∀ k : Fin n,
      rgrad (I := I) (M := M)
        (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p = e k :=
    fun k => (hfi k).2
  have hvalf0 : fFam (I := I) (M := M) (cov := cov) hmet p e (0 : Fin (n + 1)) p = 1 := by
    rw [hF0]; exact hf0p
  have hvalfi : ∀ k : Fin n,
      fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) p = 0 :=
    fun k => (hfi k).1
  have hsm : ∀ i : Fin (n + 1),
      CMDiffAt ∞ (fFam (I := I) (M := M) (cov := cov) hmet p e i) p := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [hF0]
      exact hsmC p p (by rw [hf0p]; linarith)
    · exact hsmC _ p (by rw [(hfi k).1]; linarith)
  have hgradF : ∀ i : Fin (n + 1), rgrad (I := I) (M := M)
      (fun x : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x)) p =
        dirv (I := I) (p := p) e i := by
    intro i
    rw [rgrad_psi_comp (I := I) hψd (hsm i)]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [hvalf0, hderiv1 1 hc3, one_smul, hgradf0, hdv0]
    · rw [hvalfi k, hderiv1 0 hc2, one_smul, hgradfi k, hdvsucc k]
  have hvalF : ∀ i : Fin (n + 1),
      ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i p) =
        if i = 0 then (1 : ℝ) else 0 := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [hvalf0, hψid 1 hc5]; simp
    · rw [hvalfi k, hψid 0 hc4]; simp [Fin.succ_ne_zero]
  have hdirv_inner : ∀ i j : Fin (n + 1),
      Inner.inner ℝ (dirv (I := I) (p := p) e i) (dirv (I := I) (p := p) e j) =
        (if i = j then (1 : ℝ) else 0) -
          (if i = 0 then (1 : ℝ) else 0) * (if j = 0 then (1 : ℝ) else 0) := by
    intro i j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · rw [hdv0]
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
      · rw [hdv0]
        simp [Fin.succ_ne_zero]
      · rw [hdvsucc k, hdvsucc l, hON k l]
        simp [Fin.succ_inj, Fin.succ_ne_zero]
  constructor
  · rw [Fin.sum_univ_succ]
    have : ∀ k : Fin n, (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) p)) ^ 2
        = 0 := by
      intro k; rw [hvalF (Fin.succ k)]; simp [Fin.succ_ne_zero]
    rw [Finset.sum_eq_zero (fun k _ => this k), add_zero, hvalF 0]
    norm_num
  · intro i j
    rw [gp, hgradF i, hgradF j, hvalF i, hvalF j, hdirv_inner i j]
    ring

end InitGram

end Work.Diff.C
