import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The moment-sum / counting identity for exponential sums on the torus

For a finite index type `ι` and a "moment map" `φ : ι → (Fin d → ℤ)` we prove that the `L²` norm
squared of the exponential sum `θ ↦ ∑ i, e(θ · φ i)` on the unit torus `𝕋^d = (ℝ/ℤ)^d` equals the
number of pairs `(i,j)` with `φ i = φ j`.

The measure on `𝕋^d` is the product of the normalised Haar (probability) measures on the factors.
Note that this is *not* literally the `volume` instance used by
`Mathlib.Analysis.Fourier.AddCircleMulti` (which declares a `local instance` for `UnitAddCircle`);
we therefore relate `volume` on `UnitAddTorus` to the product of `AddCircle.haarAddCircle` once and
for all in `volume_eq_pi`, and reduce the orthogonality of the monomials to the (explicitly
measure-parametrised) one-dimensional identity `fourier_integral_unitCircle`, obtained from the
orthonormality of `fourierLp` by Fubini (`integral_fintype_prod_eq_prod`).
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Work.BMF.recursion

noncomputable section

/-- **Orthogonality of the one-dimensional Fourier monomials** with respect to the normalised Haar
measure on the unit circle: `∫ e(n x) = 1` if `n = 0` and `0` otherwise. -/
lemma fourier_integral_unitCircle (n : ℤ) :
    (∫ x : UnitAddCircle, (fourier (T := 1) n) x ∂AddCircle.haarAddCircle)
      = if n = 0 then (1 : ℂ) else 0 := by
  have hO := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) (0 : ℤ) n
  have hinner : (∫ x : UnitAddCircle,
        (fourier (T := 1) n) x * starRingEnd ℂ ((fourier (T := 1) 0) x)
          ∂AddCircle.haarAddCircle) = if (0 : ℤ) = n then (1 : ℂ) else 0 := by
    rw [← hO]
    dsimp only [fourierLp]
    rw [ContinuousMap.inner_toLp (AddCircle.haarAddCircle)
      (fourier (T := 1) 0) (fourier (T := 1) n)]
  have h0val : ∀ x : UnitAddCircle, starRingEnd ℂ ((fourier (T := 1) 0) x) = (1 : ℂ) := by
    intro x
    rw [fourier_zero]
    simp
  calc (∫ x : UnitAddCircle, (fourier (T := 1) n) x ∂AddCircle.haarAddCircle)
      = ∫ x : UnitAddCircle,
          (fourier (T := 1) n) x * starRingEnd ℂ ((fourier (T := 1) 0) x)
            ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards with x
          rw [h0val x]
          simp
    _ = if (0 : ℤ) = n then (1 : ℂ) else 0 := hinner
    _ = if n = 0 then (1 : ℂ) else 0 := by
          by_cases hn : n = 0
          · simp [hn]
          · simp [hn]
            exact fun h0n => hn h0n.symm

/-- **Orthogonality of the torus monomials** with respect to the product of the normalised Haar
measures on the factors of `𝕋^d`. -/
lemma mFourier_integral_pi (d : ℕ) (n : Fin d → ℤ) :
    (∫ θ : UnitAddTorus (Fin d), UnitAddTorus.mFourier n θ
      ∂(Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)))
      = if n = 0 then (1 : ℂ) else 0 := by
  have hprod : (fun θ : UnitAddTorus (Fin d) => UnitAddTorus.mFourier n θ)
      = fun θ : UnitAddTorus (Fin d) => ∏ i : Fin d, (fourier (n i)) (θ i) := by
    funext θ
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [hprod]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (μ := fun _ : Fin d => AddCircle.haarAddCircle)
      (f := fun i (x : UnitAddCircle) => (fourier (n i)) x)]
  simp_rw [fourier_integral_unitCircle]
  by_cases hn : n = 0
  · simp [hn]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    rw [ite_eq_right hn, Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]

/-- The standard measure `volume` on `𝕋^d` is the product of the normalised Haar measures. -/
lemma volume_eq_pi (d : ℕ) :
    (volume : Measure (UnitAddTorus (Fin d)))
      = Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have h1 : (volume : Measure (UnitAddTorus (Fin d)))
      = Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) := rfl
  rw [h1]
  congr 1
  funext i
  exact hvol

/-- **Orthogonality of the torus monomials** for the standard `volume` on `𝕋^d`. -/
lemma mFourier_integral_global (d : ℕ) (n : Fin d → ℤ) :
    (∫ θ : UnitAddTorus (Fin d), UnitAddTorus.mFourier n θ)
      = if n = 0 then (1 : ℂ) else 0 := by
  rw [volume_eq_pi d]
  exact mFourier_integral_pi d n

/-- Product of two finite sums as a sum over the product index set. -/
lemma sum_mul_sum_pairs {α β : Type*} [Fintype α] [Fintype β] (a : α → ℂ) (b : β → ℂ) :
    (∑ x : α, a x) * (∑ y : β, b y) = ∑ p : α × β, a p.1 * b p.2 := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product', Finset.univ_product_univ]

/-- **The moment-sum / counting identity, in general form.**  For a finite index type `ι` and a
"moment map" `φ : ι → (Fin d → ℤ)`, the `L²` norm squared of the sum of the characters
`θ ↦ e(θ·φ i)` on the unit torus `𝕋^d` equals the number of pairs `(i,j)` with `φ i = φ j`.

This generalises `Submission.Vinogradov.vmvt_orthogonality_norm` (the case `ι = Tuple s X`,
`φ = powerSums k`, `d = k+1`), whose proof in `Submission/Vinogradov/Orthogonality.lean` can be
copied: expand `‖Σ_i χ_i‖² = Σ_{i,j} χ_i conj(χ_j)`, integrate term by term using orthogonality
(`UnitAddTorus.mFourier_integral_monomial`: `∫ mFourier n = if n = 0 then 1 else 0`), and count.
Repeat the local instances of that file if needed for `volume` on `UnitAddTorus (Fin d)`
(`UnitAddTorus (Fin d) = Fin d → UnitAddCircle`). -/
theorem integral_normSq_eq_card (d : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (φ : ι → Fin d → ℤ) :
    ∫ θ : UnitAddTorus (Fin d), ‖∑ i : ι, UnitAddTorus.mFourier (φ i) θ‖ ^ 2
      = ((Finset.univ.filter (fun q : ι × ι => φ q.1 = φ q.2)).card : ℝ) := by
  classical
  set F : UnitAddTorus (Fin d) → ℂ := fun θ => ∑ i : ι, UnitAddTorus.mFourier (φ i) θ with hF
  -- `F` is continuous, hence everything below is integrable
  have hFcont : Continuous F := by
    rw [hF]
    exact continuous_finsetSum Finset.univ fun i _ => (UnitAddTorus.mFourier (φ i)).continuous
  -- the pointwise expansion of `F · conj F` as a sum of characters
  have hpt : (fun θ : UnitAddTorus (Fin d) => F θ * conj (F θ))
      = fun θ => ∑ q : ι × ι, UnitAddTorus.mFourier (φ q.1 - φ q.2) θ := by
    funext θ
    rw [hF]
    have hconj : conj (∑ i : ι, UnitAddTorus.mFourier (φ i) θ)
        = ∑ i : ι, UnitAddTorus.mFourier (-(φ i)) θ := by
      rw [map_sum (starRingEnd ℂ)]
      exact Finset.sum_congr rfl fun i _ => (UnitAddTorus.mFourier_neg).symm
    rw [hconj, sum_mul_sum_pairs]
    exact Finset.sum_congr rfl fun q _ =>
      (UnitAddTorus.mFourier_add (m := φ q.1) (n := -(φ q.2)) (x := θ)).symm
  have hint : Integrable (fun θ : UnitAddTorus (Fin d) => F θ * conj (F θ)) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hFcont.mul (Complex.continuous_conj.comp hFcont)
    · unfold HasCompactSupport tsupport
      exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _)
  -- integrate term by term and count
  have hcomplex : (∫ θ : UnitAddTorus (Fin d), F θ * conj (F θ))
      = ((Finset.univ.filter (fun q : ι × ι => φ q.1 = φ q.2)).card : ℂ) := by
    rw [hpt]
    rw [integral_finsetSum Finset.univ]
    · simp_rw [mFourier_integral_global d]
      simp_rw [sub_eq_zero]
      rw [Finset.sum_boole]
    · intro q _
      exact (UnitAddTorus.mFourier (φ q.1 - φ q.2)).continuous.integrable_of_hasCompactSupport (by
        unfold HasCompactSupport tsupport
        exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _))
  have hreal : (∫ θ : UnitAddTorus (Fin d), ‖F θ‖ ^ 2) = (∫ θ, F θ * conj (F θ)).re := by
    have hpt2 : (fun θ : UnitAddTorus (Fin d) => ‖F θ‖ ^ 2)
        = fun θ => (F θ * conj (F θ)).re := by
      funext θ
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hpt2]
    exact integral_re hint
  calc ∫ θ : UnitAddTorus (Fin d), ‖∑ i : ι, UnitAddTorus.mFourier (φ i) θ‖ ^ 2
      = ∫ θ : UnitAddTorus (Fin d), ‖F θ‖ ^ 2 := by rw [hF]
    _ = (∫ θ : UnitAddTorus (Fin d), F θ * conj (F θ)).re := hreal
    _ = ((Finset.univ.filter (fun q : ι × ι => φ q.1 = φ q.2)).card : ℝ) := by
          rw [hcomplex]
          simp

end

end Work.BMF.recursion
