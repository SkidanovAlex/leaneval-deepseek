import Mathlib
import Submission.Work.Cohomology.pd_ab_enlarge
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.cap_d
import Submission.Work.Cohomology.pd_crux_weak

/-!
# The cap product of a coboundary with the "middle" chain is a boundary in `U ∩ V`

Let `X` be a topological space, `U V K L ⊆ X` subsets and, in degree `N = k + (mj + 1)`, chains
`α₁, α₂, α₃` supported respectively in `U ∖ L`, `U ∩ V`, `V ∖ K`, whose boundaries are supported in
`Lᶜ` (for `α₁`) and in `Kᶜ` (for `α₃`) and which sum to a cycle.  Let `θ` be a degree `k` cochain
vanishing on chains in `Kᶜ` *and* in `Lᶜ` (i.e. `θ` lies in the `A+B` complex of the pair
`(Kᶜ, Lᶜ)`).

Then the cap product of the coboundary `δθ` with the middle chain `α₂` is a boundary of a chain
supported in `U ∩ V`:

  `∃ γ, γ ∈ C_{mj+1}(U ∩ V)` and `d γ = (-1)^(k+1) • (α₂ ⌢ δθ)`.

This is the "well-definedness of the pairing with `α₂` on the `A+B` slot" used in the computation
of the crux square of Poincaré–Lefschetz duality.  The witness is the cap product `α₂ ⌢ θ` of the
*cochain* `θ` (not its coboundary) with `α₂`, which lies in `C_{mj+1}(U ∩ V)` by
`cap_mem_range_inclChains`; the boundary formula `cap_d` together with the vanishing of `θ` on the
boundaries of `α₁`, `α₂`, `α₃` identifies its boundary with `(-1)^(k+1) • (α₂ ⌢ δθ)`.

The proof transports the degrees along the hypothesis `hkN : k + (mj + 1) = N` (all the data lives
in degree `k + (mj+1)`), and uses that `θ` kills the chains supported in `Lᶜ` and in `Kᶜ` through
`cap_inclChains_eq_zero`.  The scalar multiplication is written in the canonical `ℤ`-form
(`int_smul_eq_zsmul` converts the `Module ℤ`-smul of `cap_d` into it).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem cap_cochainDiff_mem_range {X : TopCat} {U V K L : Set X} {N k mj : ℕ}
    (hkN : k + (mj + 1) = N)
    (α₁ α₂ α₃ : (Work.Cohomology.singularChains ℤ X).X N)
    (hα₁ : α₁ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U \ L)).f N).hom))
    (hα₂ : α₂ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f N).hom))
    (hα₃ : α₃ ∈ LinearMap.range (((Work.Cohomology.inclChains X (V \ K)).f N).hom))
    (hL : (Work.Cohomology.singularChains ℤ X).d N (N-1) α₁ ∈
      LinearMap.range (((Work.Cohomology.inclChains X Lᶜ).f (N-1)).hom))
    (hK : (Work.Cohomology.singularChains ℤ X).d N (N-1) α₃ ∈
      LinearMap.range (((Work.Cohomology.inclChains X Kᶜ).f (N-1)).hom))
    (hd : (Work.Cohomology.singularChains ℤ X).d N (N-1) (α₁ + α₂ + α₃) = 0)
    {θ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) k}
    (hθ : θ ∈ Work.Cohomology.relKern ℤ X Kᶜ k ⊓ Work.Cohomology.relKern ℤ X Lᶜ k) :
    ∃ γ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f (mj+1)).hom),
      (Work.Cohomology.singularChains ℤ X).d (mj+1) mj γ =
        (-1:ℤ)^(k+1) • Work.Cohomology.cap ℤ (TopCat.toSSet.obj X)
          (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ) mj
            ((Work.Cohomology.capIdx k mj) ▸ (hkN.symm ▸ α₂)) := by
  -- All the data lives in degree `k + (mj+1)`; transport it along `hkN`.
  subst N
  rw [show (k + (mj + 1)) - 1 = k + mj by omega] at hL hK hd
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  -- The boundary of `α₂` is a sum of chains supported in `Lᶜ` and in `Kᶜ`.
  have hdα : (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
      = - ((Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
          + (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) := by
    have h := hd
    rw [map_add, map_add, add_assoc] at h
    have h2 : (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        + (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃
        = - (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁ :=
      eq_neg_of_add_eq_zero_right h
    have h3 : (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        = - (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
          - (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ :=
      eq_sub_of_add_eq h2
    rw [h3, neg_add, sub_eq_add_neg]
  -- `θ` kills the chains supported in `Lᶜ` ...
  have hzeroL : Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ mj
      ((Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact Work.Cohomology.cap_inclChains_eq_zero X Lᶜ θ hθ.2 mj e'
  -- ... and the chains supported in `Kᶜ`.
  have hzeroK : Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ mj
      ((Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact Work.Cohomology.cap_inclChains_eq_zero X Kᶜ θ hθ.1 mj f'
  have hzero : Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ mj
      ((Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) = 0 := by
    rw [hdα, map_neg, map_add, hzeroL, hzeroK, add_zero, neg_zero]
  -- The witness: the cap product of `α₂` with `θ` itself.
  refine ⟨Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ (mj+1) α₂, ?_, ?_⟩
  · exact Work.Cohomology.cap_mem_range_inclChains (M := X) (S := U ∩ V) k (mj+1) θ hα₂
  · -- The boundary formula, with the term `α₂ ⌢ θ` killed.
    have hcapd : (Work.Cohomology.singularChains ℤ X).d (mj+1) mj
        (Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ (mj+1) α₂)
        = (-1:ℤ)^k • (Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) θ mj
              ((Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
            - Work.Cohomology.cap ℤ (TopCat.toSSet.obj X)
              (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ) mj
              ((Work.Cohomology.capIdx k mj) ▸ α₂)) := by
      refine (Work.Cohomology.cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) θ α₂).trans ?_
      exact int_smul_eq_zsmul (inferInstance : Module ℤ
        ↑(((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X mj)) ((-1:ℤ)^k) _
    rw [hzero] at hcapd
    rw [hcapd, zero_sub, zsmul_neg]
    rw [show (-1:ℤ)^(k+1) = -((-1:ℤ)^k) by rw [pow_succ]; ring, neg_zsmul]

end

end Work.Cohomology
