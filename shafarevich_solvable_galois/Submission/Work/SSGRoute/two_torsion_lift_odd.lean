import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.exists_kerSuccAddEquiv_equivariant
import Submission.Work.SSGRoute.kerSuccCocycle_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting `2`-torsion along the refined filtration, the odd prime case

Schmidt–Wingberg (arXiv:math/9809211), Step 1 of the induction, clause (B): if
`γ ∈ Γ(τ) = F(n)/F(n)^{(τ)} ⋊ Gal(K/ℚ)` is an involution whose `Gal(K/ℚ)`-component is
non-trivial, then `γ` lifts to an element of order `2` in `Γ(τ+1)`.

For odd `p` this is elementary and does **not** need the structure of the graded piece beyond
the fact that the kernel of the projection `Γ(τ+1) ↠ Γ(τ)` has exponent `p`:

* choose any lift `y₀` of `γ` (surjectivity of `flowGroupSucc`), so `y₀² ∈ ker`;
* the kernel has exponent `p`, hence `(y₀²)^p = 1`;
* `y := y₀ ^ p` then satisfies `π y = (π y₀)^p = γ^p = γ` (as `γ² = 1` and `p` is odd) and
  `y² = y₀^{2p} = (y₀²)^p = 1`.

The case `p = 2`, where `x ↦ x²` is not a bijection on the kernel, is the content of
`Work.SSGRoute.flowGroup_two_torsion_lift`.

## Main declarations

* `Work.SSGRoute.sq_one_lift_of_odd_kernel` — the abstract group-theoretic lemma;
* `Work.SSGRoute.flowGroupSucc_ker_pow` — the kernel of `flowGroupSucc` has exponent `p`;
* `Work.SSGRoute.two_torsion_lift_odd` — the target.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-- **Abstract lifting of an involution through a surjection with a kernel of odd exponent `p`.**
If `π : Γ' →* Γ` has kernel of exponent dividing `p` (an odd number) and `π y₀` is an involution
of `Γ`, then `y₀ ^ p` is an involution of `Γ'` above `π y₀`. -/
theorem sq_one_lift_of_odd_kernel {Γ Γ' : Type*} [Group Γ] [Group Γ'] (π : Γ' →* Γ)
    (p : ℕ) (hodd : Odd p)
    (hexp : ∀ x : ↥π.ker, (x : Γ') ^ p = 1)
    (y₀ : Γ') (hγ : (π y₀) ^ 2 = 1) :
    ∃ y : Γ', π y = π y₀ ∧ y ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨y₀ ^ p, ?_, ?_⟩
  · rw [map_pow, show p = 2 * m + 1 from hm, pow_succ, pow_mul, hγ, one_pow, one_mul]
  · have hmem : y₀ ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hγ]
    have hxp : (y₀ ^ 2) ^ p = 1 := hexp ⟨y₀ ^ 2, hmem⟩
    rw [← pow_mul, Nat.mul_comm p 2, pow_mul, hxp]

/-- The kernel of the projection `flowGroupSucc p G m i j : Γ(τ+1) →* Γ(τ)` has exponent
dividing `p`: it identifies through `succKerIso` with the graded piece `E(m,τ)`, on which
`x ↦ x ^ p` is trivial. -/
theorem flowGroupSucc_ker_pow (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : ↥(flowGroupSucc p G m i j).ker) :
    (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) ^ p = 1 := by
  obtain ⟨z, rfl⟩ := (succKerIso p G m i j).surjective x
  rw [← Subgroup.coe_pow, ← map_pow, pow_eq_one_refinedQuotient, map_one]
  rfl

/-- **Odd-prime case of the `2`-torsion lifting along the refined filtration.**  For an odd prime
`p`, every involution `γ ∈ Γ(τ)` whose `Gal(K/ℚ)`-component is non-trivial lifts to an involution
of `Γ(τ+1)`, where `τ + 1 = tauSucc i j`. -/
theorem two_torsion_lift_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (γ : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j) (hγ : γ ^ 2 = 1)
    (hδ : Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) n i j γ ≠ 1) :
    ∃ y : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  have hpodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two hp
  obtain ⟨y₀, hy₀⟩ := flowGroupSucc_surjective p (K ≃ₐ[ℚ] K) n i j γ
  have hy₀sq : (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j y₀) ^ 2 = 1 := by rw [hy₀, hγ]
  obtain ⟨y, hy1, hy2⟩ := sq_one_lift_of_odd_kernel
    (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) p hpodd
    (fun x => flowGroupSucc_ker_pow p (K ≃ₐ[ℚ] K) n i j x) y₀ hy₀sq
  exact ⟨y, by rw [liftsFlowAt_iff_flowGroupSucc, hy1, hy₀], hy2⟩

end Work.SSGRoute
