import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.starProjection_comp_of_mapsTo
import Submission.Work.ORP311.cosetShift_coset
import Submission.Work.ORP311.regBlk_adjoint

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- Exponent bookkeeping: `t ^ (j - 1) = t⁻¹ * t ^ j` (for the inverse shift). -/
private theorem zpow_sub_one_eq_inv_mul' (t : G) (j : ℤ) : t ^ (j - 1) = t⁻¹ * t ^ j := by
  rw [← zpow_neg_one t, ← zpow_add]
  congr 1
  ring

/-- **The inverse shift of a coset**: `t⁻¹ · (N t^j) = N t^{j-1}`, where the `N`-part is
conjugated by `t⁻¹` (which preserves `N` by `TwistData.conj_inv`).

Together with `Work.ORP311.cosetShift_coset` (`t · (N t^{j-1}) = N t^j`) this says that the left
regular operator `λ(t)` is a bijection from the block `ℓ²(N t^{j-1})` onto the block `ℓ²(N t^j)`,
which is the content of `Work.ORP311.blk_comp_regBlk`. -/
theorem cosetShift_inv_coset {N : Subgroup G} {t : G} (h : P311.TwistData N t) (j : ℤ) :
    cosetShift t⁻¹ (coset N t j) = coset N t (j - 1) := by
  ext x
  constructor
  · -- `x = t⁻¹ * (n * t^j) = (t⁻¹ n t) * t^{j-1}`
    rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨⟨t⁻¹ * (n : G) * t, h.conj_inv n n.2⟩,
      by rw [zpow_sub_one_eq_inv_mul']; group⟩
  · -- `x = n * t^{j-1} = t⁻¹ * ((t n t⁻¹) * t^j)`
    rintro ⟨n, rfl⟩
    refine ⟨((⟨t * (n : G) * t⁻¹, h.conj n n.2⟩ : N) : G) * t ^ j, ⟨_, rfl⟩, ?_⟩
    rw [zpow_sub_one_eq_inv_mul']
    group

/-- **`λ(t)` intertwines the block projections with a shift of the coset index.**

The blockwise left regular operator `regBlk n t` (the direct sum of `λ(t)` over the `n` summands)
maps the `N`-coset block `ℓ²(N t^{j-1})ⁿ` *onto* the block `ℓ²(N t^j)ⁿ`: it maps the first block
into the second (`regBlk_ell2Sub` + `cosetShift_coset`), and its adjoint `regBlk n t⁻¹`
(`regBlk_adjoint`) maps the second back into the first (`regBlk_ell2Sub` +
`cosetShift_inv_coset`).  Hence by `starProjection_comp_of_mapsTo` the projection onto the second
block intertwines with the operator:

  `blk n N t j ∘L regBlk n t = regBlk n t ∘L blk n N t (j - 1)`. -/
theorem blk_comp_regBlk {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : Work.ORP311.P311.TwistData N t) (n : ℕ) (j : ℤ) :
    Work.ORP311.P311.blk n N t j ∘L Work.ORP311.regBlk (G := G) n t =
      Work.ORP311.regBlk (G := G) n t ∘L Work.ORP311.P311.blk n N t (j - 1) := by
  -- `λ(t)` maps the block `ℓ²(N t^{j-1})` into the block `ℓ²(N t^j)`
  have hT : ∀ x ∈ ell2Sub (G := G) n (coset N t (j - 1)),
      regBlk (G := G) n t x ∈ ell2Sub (G := G) n (coset N t j) := by
    intro x hx
    exact ell2Sub_mono (cosetShift_coset h j).le
      (regBlk_ell2Sub (G := G) n t (coset N t (j - 1)) ⟨x, hx, rfl⟩)
  -- its adjoint `λ(t⁻¹)` maps the block `ℓ²(N t^j)` back into the block `ℓ²(N t^{j-1})`
  have hT' : ∀ y ∈ ell2Sub (G := G) n (coset N t j),
      (ContinuousLinearMap.adjoint (regBlk (G := G) n t)) y
        ∈ ell2Sub (G := G) n (coset N t (j - 1)) := by
    intro y hy
    rw [regBlk_adjoint (G := G) n t]
    exact ell2Sub_mono (cosetShift_inv_coset h j).le
      (regBlk_ell2Sub (G := G) n t⁻¹ (coset N t j) ⟨y, hy, rfl⟩)
  exact starProjection_comp_of_mapsTo (ell2Sub (G := G) n (coset N t (j - 1)))
    (ell2Sub (G := G) n (coset N t j)) (regBlk (G := G) n t) hT hT'

end Work.ORP311
