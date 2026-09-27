import Mathlib
import Submission.Work.KT.Dim2.idem_conj_of_contractible

namespace Work.KT.D2

open Matrix ContinuousMap Filter

open scoped Topology

noncomputable section

/-- **Trivialisation of an idempotent at a prescribed base point.**  Let `p : X → M_n(ℂ)` be a
continuous idempotent-valued function on a compact space `X`, let `y0 : X`, and suppose
`K : [0,1] × X → X` is a homotopy from the constant map at `y0` (`K (0, x) = y0`) to the identity
(`K (1, x) = x`).  Then `p` is trivialised by continuous families of units to the constant
idempotent `p y0`: there are `u, v : C(X, M_n(ℂ))` with `u x * v x = 1 = v x * u x` and
`u x * p x * v x = p y0` for all `x`.

Use `Work.KT.Dim2.conj_of_path_mat` on the path `t ↦ p ∘ K t` of idempotents of `M_n(C(X,ℂ))`,
whose norm-continuity follows from uniform continuity of the entries of `p` on the compact `X`;
then convert the resulting unit into pointwise families of matrices with
`Work.KT.Dim2.exists_eval_units`. -/
theorem idem_conj_target_boundary (X : Type) [TopologicalSpace X] [CompactSpace X]
    (y0 : X) (K : C(unitInterval × X, X)) (hK0 : ∀ x, K (0, x) = y0) (hK1 : ∀ x, K (1, x) = x)
    (n : ℕ) (p : C(X, Matrix (Fin n) (Fin n) ℂ)) (hp : ∀ x, p x * p x = p x) :
    ∃ u v : C(X, Matrix (Fin n) (Fin n) ℂ),
      (∀ x, u x * v x = 1 ∧ v x * u x = 1) ∧ (∀ x, u x * p x * v x = p y0) := by
  classical
  let P : C(unitInterval × X, Matrix (Fin n) (Fin n) ℂ) := p.comp K
  have hP : ∀ (t : unitInterval) (x : X), P (t, x) = p (K (t, x)) := by
    intro t x; rfl
  let entry : Fin n → Fin n → C(unitInterval, C(X, ℂ)) := fun i j =>
    ContinuousMap.curry ⟨fun q : unitInterval × X => P q i j,
      (P.continuous.matrix_elem i j)⟩
  have entry_apply : ∀ (i j : Fin n) (t : unitInterval) (x : X),
      entry i j t x = P (t, x) i j := by
    intro i j t x
    rw [show entry i j = ContinuousMap.curry ⟨fun q : unitInterval × X => P q i j,
        (P.continuous.matrix_elem i j)⟩ from rfl]
    rw [ContinuousMap.curry_apply]
    rfl
  let γ : unitInterval → Matrix (Fin n) (Fin n) C(X, ℂ) := fun t => Matrix.of (fun i j => entry i j t)
  have hγ_apply : ∀ (t : unitInterval) (i j : Fin n), γ t i j = entry i j t := by
    intro t i j; rfl
  have hidem : ∀ t, γ t * γ t = γ t := by
    intro t
    ext i j x
    simp only [Matrix.mul_apply, ContinuousMap.mul_apply, ContinuousMap.sum_apply]
    simp only [hγ_apply, entry_apply, hP]
    rw [← Matrix.mul_apply, hp (K (t, x))]
  have hγ : ∀ t : unitInterval, ∀ c : NNReal, 0 < c →
      ∀ᶠ s in 𝓝 t, homInvMatNorm (γ s - γ t) < c := by
    intro t0 c hc
    set e : NNReal := c / ((n : NNReal) + 1) with he
    have hepos : 0 < e := by rw [he]; exact div_pos hc (by positivity)
    have hE : ∀ᶠ s in 𝓝 t0, ∀ i j : Fin n, ‖(γ s - γ t0) i j‖₊ ≤ e := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      have hcont : ∀ᶠ s in 𝓝 t0, dist (entry i j s) (entry i j t0) < (e : ℝ) :=
        Metric.tendsto_nhds.mp ((entry i j).continuous.continuousAt (x := t0)) _
          (by exact_mod_cast hepos)
      filter_upwards [hcont] with s hs
      rw [dist_eq_norm] at hs
      rw [show (γ s - γ t0) i j = entry i j s - entry i j t0 by
            simp [γ, Matrix.of_apply]]
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact le_of_lt hs
    filter_upwards [hE] with s hs
    calc homInvMatNorm (γ s - γ t0)
        ≤ (n : NNReal) * e := homInvMatNorm_le_card_mul _ hs
      _ < c := by
          have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
          rw [← NNReal.coe_lt_coe]
          simp only [he, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div,
            NNReal.coe_add, NNReal.coe_one]
          rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith [hcR]
  obtain ⟨u, hu⟩ := Work.KT.Dim2.conj_of_path_mat γ hγ hidem
  obtain ⟨u', v', hu'e, hv'e, huv⟩ := Work.KT.Dim2.exists_eval_units n u
  have evalMat_apply : ∀ (x : X) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n),
      RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom M i j = M i j x := by
    intro x M i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact ContinuousMap.evalAlgHom_apply ℂ ℂ x (M i j)
  have hγ0 : ∀ x, RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom (γ 0) = p y0 := by
    intro x
    ext i j
    rw [evalMat_apply, show γ 0 i j = entry i j 0 from rfl]
    show ((entry i j) 0) x = p y0 i j
    rw [entry_apply]
    show P (0, x) i j = p y0 i j
    rw [hP, hK0 x]
  have hγ1 : ∀ x, RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom (γ 1) = p x := by
    intro x
    ext i j
    rw [evalMat_apply, show γ 1 i j = entry i j 1 from rfl]
    show ((entry i j) 1) x = p x i j
    rw [entry_apply]
    show P (1, x) i j = p x i j
    rw [hP, hK1 x]
  refine ⟨u', v', huv, fun x => ?_⟩
  have hconj_x : u' x * p x = p y0 * u' x := by
    have hmap := congrArg (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom) hu
    rw [map_mul, map_mul] at hmap
    rw [hγ1 x, hγ0 x, ← hu'e x] at hmap
    exact hmap
  calc u' x * p x * v' x = (u' x * p x) * v' x := rfl
    _ = (p y0 * u' x) * v' x := by rw [hconj_x]
    _ = p y0 * (u' x * v' x) := by rw [mul_assoc]
    _ = p y0 := by rw [(huv x).1, mul_one]

end

end Work.KT.D2
