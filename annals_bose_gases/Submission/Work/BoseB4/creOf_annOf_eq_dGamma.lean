import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.finset_sum_creOf_comp_annOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-! ## Supporting computations

The rank-one operator `|w⟩⟨v| : x ↦ (∑ l, v l * x l) • w` is written in the file's own
vocabulary as `(∑ l, v l • LinearMap.proj l).smulRight w`; its matrix element on the coordinate
basis `evec` is `w i * v j`. -/

/-- The diagonalisation of the rank-one form on the coordinate vector `evec m j`:
`(∑ l, v l • proj l) (evec m j) = v j` (only the `j`-th term survives). -/
private lemma sum_proj_evec {m : ℕ} (v : Fin m → ℝ) (j : Fin m) :
    (∑ l : Fin m, v l • (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ)) (evec m j) = v j := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, evec]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The matrix elements of the rank-one operator `|w⟩⟨v|` in the coordinate basis:
`(|w⟩⟨v| (evec m j)) i = w i * v j`. -/
private lemma smulRight_proj_apply_evec {m : ℕ} (w v : Fin m → ℝ) (i j : Fin m) :
    (((∑ l : Fin m, v l • (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ)).smulRight w :
        (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (evec m j)) i = w i * v j := by
  rw [LinearMap.smulRight_apply, sum_proj_evec, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **The rank-one bridge `creOf w ∘ annOf v = dGamma m (|w⟩⟨v|)`.**

`dGamma m T = Σ_{ij} (T (evec j))_i • (cre m i ∘ ann m j)` and
`creOf m w = Σ_i w_i • cre m i`, `annOf m v = Σ_j v_j • ann m j`; for the rank-one operator
`T = |w⟩⟨v|`, i.e. `T x = (Σ_l v_l x_l) • w` (`(∑ l, v l • LinearMap.proj l).smulRight w`), the
matrix element is `(T (evec j))_i = v_j * w_i`, so both sides are `Σ_{ij} w_i v_j • (cre_i ∘ ann_j)`.

This is the definitional bridge that turns a **ladder word** into a **`dGamma`** (hence, via
`Work.BoseDict.boxRealise_dGamma`, into the one-body slot sum `boxSlotSum e T` and the one-body
model assembly `Work.BoseBoxFock.exists_model_le_of_slotSum`).  It is what the one-body rows of
`Work.BoseBoxFock.H2ndF` (`Σ_k τ_k a_k†a_k`, the `NH` row — recall
`NH = (1/32) Σ_{k∈excited} etaH … • (creOf (f k) ∘ annOf (f k))` — and the `μ n₀` /
`(L₀+L₁)∘n₊` rows) need in order to be written as `dGamma m T`.  (A useful corollary to record in
the same file: with `w = v = evec m 0` this specialises to `n₀ = dGamma m (|e₀⟩⟨e₀|)`, cf. the
specialised `Work.BoseBoxFock.dGamma_coord_zero` already on disk.) -/
theorem creOf_annOf_eq_dGamma {m : ℕ} (w v : Fin m → ℝ) :
    (Work.BoseB4.creOf m w).comp (Work.BoseB4.annOf m v)
      = Work.BoseB4.dGamma m ((∑ l : Fin m, v l • LinearMap.proj l).smulRight w) := by
  rw [creOf, annOf, sum_smul_comp_sum_smul, dGamma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (smulRight_proj_apply_evec w v i j).symm

/-! ## The `n₀` specialisation

With `w = v = evec m 0` the bridge says that the mode-`0` number operator `n₀ = a₀†a₀` is the
second quantisation of the rank-one projector `|e₀⟩⟨e₀| : x ↦ (x 0) • e₀`. -/

/-- `creOf m (evec m 0) = cre m 0`: creating the superposition with coordinate vector `e₀`
is creating mode `0`. -/
private lemma creOf_evec_zero (m : ℕ) [NeZero m] : creOf m (evec m 0) = cre m 0 := by
  rw [creOf, Finset.sum_eq_single (0 : Fin m)]
  · rw [evec, Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [evec, Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- `annOf m (evec m 0) = ann m 0`: annihilating the superposition with coordinate vector `e₀`
is annihilating mode `0`. -/
private lemma annOf_evec_zero (m : ℕ) [NeZero m] : annOf m (evec m 0) = ann m 0 := by
  rw [annOf, Finset.sum_eq_single (0 : Fin m)]
  · rw [evec, Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [evec, Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- `∑ l, (evec m 0) l • proj l = proj 0`: the one-particle projection onto the mode `0`. -/
private lemma sum_evec_proj (m : ℕ) [NeZero m] :
    (∑ l : Fin m, (evec m 0) l • (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ))
      = LinearMap.proj (0 : Fin m) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, evec]
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [Pi.single_eq_same, smul_eq_mul, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- **The `n₀` corollary of `creOf_annOf_eq_dGamma`**: the number operator `n₀ = a₀†a₀` of the
mode `0` is the second quantisation of the rank-one projector `|e₀⟩⟨e₀|` (`x ↦ (x 0) • e₀`). -/
theorem modeNumOp_zero_eq_dGamma (m : ℕ) [NeZero m] :
    modeNumOp m 0 = dGamma m ((LinearMap.proj (0 : Fin m)).smulRight (evec m 0)) := by
  have h : (creOf m (evec m 0)).comp (annOf m (evec m 0))
      = dGamma m ((LinearMap.proj (0 : Fin m)).smulRight (evec m 0)) := by
    rw [creOf_annOf_eq_dGamma, sum_evec_proj]
  rw [creOf_evec_zero m, annOf_evec_zero m] at h
  rw [← h, modeNumOp]

end Work.BoseB4
