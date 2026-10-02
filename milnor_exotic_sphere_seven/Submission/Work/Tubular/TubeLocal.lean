import Submission.Work.Tubular.Local

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The tubular map of a chart is a local diffeomorphism

In a chart of the manifold, with `f : ℝ^m → ℝ^{m+k}` the chart representative of the embedding and
`A : ℝ^k → ℝ^{m+k}` a linear parametrisation of the normal directions at the centre of the chart, the
**tubular map of the chart** is `(y,u) ↦ f y + A u`.  Its derivative at `(y,u)` is
`(δy, δu) ↦ Df(y)·δy + A δu`, a linear isomorphism exactly when `ℝ^{m+k}` is the direct sum of
`im Df(y)` and `im A`; at the base point of the chart this holds, and it stays true in a
neighbourhood.  Hence, by the inverse function theorem
(`Work.Tubular.exists_localInverse_of_hasFDerivAt`), the tubular map of a chart is a local
diffeomorphism at `(y₀, 0)`.

This is the analytic heart of the tubular neighbourhood theorem: the whole construction is the
assembly of these local models over a finite chart cover of the compact manifold.
-/

open scoped Manifold ContDiff Topology
open Filter

namespace Work.Tubular

noncomputable section

variable {m k : ℕ}

/-- **A bijective continuous linear map between finite-dimensional spaces is a continuous linear
equivalence** (the continuity is automatic on a finite-dimensional source). -/
theorem exists_continuousLinearEquiv_of_bijective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [T2Space E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (h : Function.Bijective L) :
    ∃ φ : E ≃L[ℝ] F, φ.toContinuousLinearMap = L :=
  ⟨(LinearEquiv.ofBijective L.toLinearMap h).toContinuousLinearEquiv, by
    ext p
    rfl⟩

/-- The **tubular map of a chart**: `(y,u) ↦ f y + A u`, where `f` is the chart representative of the
embedding and `A` parametrises the normal directions. -/
def tubeMapChart (f : Euc m → Euc (m + k)) (A : Euc k →L[ℝ] Euc (m + k)) :
    Euc m × Euc k → Euc (m + k) := fun p => f p.1 + A p.2

@[simp] theorem tubeMapChart_apply (f : Euc m → Euc (m + k)) (A : Euc k →L[ℝ] Euc (m + k))
    (p : Euc m × Euc k) : tubeMapChart f A p = f p.1 + A p.2 := rfl

/-- The tubular map of a chart is smooth. -/
theorem contDiff_tubeMapChart (f : Euc m → Euc (m + k)) (A : Euc k →L[ℝ] Euc (m + k))
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (tubeMapChart f A) :=
  (hf.comp contDiff_fst).add (A.contDiff.comp contDiff_snd)

/-- The derivative of the tubular map of a chart: at `(y,u)` it is
`(δy, δu) ↦ Df(y)·δy + A δu` (it does not depend on `u`). -/
def tubeDeriv (f : Euc m → Euc (m + k)) (A : Euc k →L[ℝ] Euc (m + k)) (y : Euc m) :
    (Euc m × Euc k) →L[ℝ] Euc (m + k) :=
  (fderiv ℝ f y).comp (ContinuousLinearMap.fst ℝ (Euc m) (Euc k)) +
    A.comp (ContinuousLinearMap.snd ℝ (Euc m) (Euc k))

@[simp] theorem tubeDeriv_apply (f : Euc m → Euc (m + k)) (A : Euc k →L[ℝ] Euc (m + k))
    (y : Euc m) (p : Euc m × Euc k) : tubeDeriv f A y p = fderiv ℝ f y p.1 + A p.2 := rfl

theorem hasFDerivAt_tubeMapChart (f : Euc m → Euc (m + k)) (hf : ContDiff ℝ 1 f)
    (A : Euc k →L[ℝ] Euc (m + k)) (y : Euc m) (u : Euc k) :
    HasFDerivAt (tubeMapChart f A) (tubeDeriv f A y) (y, u) := by
  have h1 : HasFDerivAt (fun p : Euc m × Euc k => f p.1)
      ((fderiv ℝ f y).comp (ContinuousLinearMap.fst ℝ (Euc m) (Euc k))) (y, u) :=
    ((hf.differentiable (by norm_num)) y).hasFDerivAt.comp (y, u) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : Euc m × Euc k => A p.2)
      (A.comp (ContinuousLinearMap.snd ℝ (Euc m) (Euc k))) (y, u) :=
    A.hasFDerivAt.comp (y, u) hasFDerivAt_snd
  exact h1.add h2

/-- **The tubular map of a chart is a local diffeomorphism at `(y₀, 0)`**, whenever the derivative
there is invertible and stays invertible nearby. -/
theorem exists_localInverse_tubeMap (f : Euc m → Euc (m + k))
    {y₀ : Euc m} (hf : ContDiff ℝ ∞ f) (A : Euc k →L[ℝ] Euc (m + k))
    (h₀ : Function.Bijective (tubeDeriv f A y₀))
    (h₁ : ∀ᶠ y in 𝓝 y₀, Function.Bijective (tubeDeriv f A y)) :
    ∃ (W : Set (Euc m × Euc k)) (U : Set (Euc (m + k))) (g : Euc (m + k) → Euc m × Euc k),
      IsOpen W ∧ (y₀, 0) ∈ W ∧ IsOpen U ∧ tubeMapChart f A '' W = U ∧
      Set.InjOn (tubeMapChart f A) W ∧
      (∀ z ∈ U, tubeMapChart f A (g z) = z) ∧
      (∀ p ∈ W, g (tubeMapChart f A p) = p) ∧
      ContinuousOn g U ∧ ContDiffOn ℝ ∞ g U := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨φ, hφcoe⟩ := exists_continuousLinearEquiv_of_bijective (tubeDeriv f A y₀) h₀
  have hderiv : HasFDerivAt (tubeMapChart f A) (φ : (Euc m × Euc k) →L[ℝ] Euc (m + k))
      (y₀, 0) := by
    rw [hφcoe]
    exact hasFDerivAt_tubeMapChart f hf1 A y₀ 0
  have hInv : ∃ W₀ : Set (Euc m × Euc k), IsOpen W₀ ∧ (y₀, 0) ∈ W₀ ∧
      ∀ x ∈ W₀, ∃ ψ : (Euc m × Euc k) ≃L[ℝ] Euc (m + k),
        HasFDerivAt (tubeMapChart f A) ψ.toContinuousLinearMap x := by
    obtain ⟨W₀, hW₀sub, hW₀open, hy₀W₀⟩ := mem_nhds_iff.mp h₁
    refine ⟨W₀ ×ˢ Set.univ, hW₀open.prod isOpen_univ, ⟨hy₀W₀, Set.mem_univ 0⟩, ?_⟩
    rintro ⟨y, u⟩ hyu
    obtain ⟨ψ, hψcoe⟩ := exists_continuousLinearEquiv_of_bijective (tubeDeriv f A y)
      (hW₀sub hyu.1)
    refine ⟨ψ, ?_⟩
    rw [hψcoe]
    exact hasFDerivAt_tubeMapChart f hf1 A y u
  obtain ⟨W, U, g, hW, haW, hU, himg, hinj, hright, hleft, hcont, hsmooth⟩ :=
    exists_localInverse_of_hasFDerivAt (tubeMapChart f A) φ
      (contDiff_tubeMapChart f A hf) hderiv hInv
  exact ⟨W, U, g, hW, haW, hU, himg, hinj, hright, hleft, hcont, hsmooth⟩

end

end Work.Tubular
