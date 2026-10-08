import Mathlib
import Submission.Work.Clifford.clifford_decomposition
import Submission.Work.Clifford.cfInner_orbitSum_eq_ite
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.clifford_constituents`

**Clifford's theorem, constituent form.**  For `N ⊴ G` and `χ ∈ Irr G` there is `θ ∈ Irr N`
such that the irreducible constituents of `χ|_N` are exactly the `G`-conjugates of `θ`:

`IsConstituentOf φ (χ|_N) ↔ φ ∈ charOrbit N θ` for every `φ ∈ Irr N`.

Proof: by `clifford_decomposition` there are `θ ∈ Irr N` and `e > 0` with
`χ|_N = e • orbitSum N θ`; pairing against `φ ∈ Irr N` and using
`cfInner_orbitSum_eq_ite` (which says `⟪orbitSum N θ, φ⟫ = 1` if `φ` is a conjugate of `θ`
and `0` otherwise) reduces the claim to `e * (if φ ∈ charOrbit N θ then 1 else 0) ≠ 0`,
i.e. to `e ≠ 0` and to membership in the orbit.
-/

noncomputable section

namespace Work.Clifford

/-- The pairing of a multiple of an orbit sum against an irreducible character:
`⟪e • orbitSum N θ, φ⟫ = e * (if φ ∈ charOrbit N θ then 1 else 0)` for `θ, φ ∈ Irr N`. -/
theorem cfInner_smul_orbitSum_eq_mul_ite {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] [Fintype N] {θ φ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N)
    (hφ : φ ∈ Work.Clifford.Irr N) (e : ℕ) :
    Work.Clifford.cfInner ((e : ℂ) • Work.Clifford.orbitSum N θ) φ =
      (e : ℂ) * (if φ ∈ Work.Clifford.charOrbit N θ then (1 : ℂ) else 0) := by
  rw [cfInner_smul_left, cfInner_orbitSum_eq_ite hθ hφ]

theorem clifford_constituents {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    ∃ θ : N → ℂ, θ ∈ Work.Clifford.Irr N ∧
      ∀ φ : N → ℂ, φ ∈ Work.Clifford.Irr N →
        (Work.Clifford.IsConstituentOf φ (Work.Clifford.resFun N χ) ↔
          φ ∈ Work.Clifford.charOrbit N θ) := by
  obtain ⟨θ, hθ, e, he, hres⟩ := clifford_decomposition (N := N) hχ
  refine ⟨θ, hθ, fun φ hφ => ?_⟩
  have hec : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have key : (e : ℂ) * (if φ ∈ Work.Clifford.charOrbit N θ then (1 : ℂ) else 0) ≠ 0 ↔
      φ ∈ Work.Clifford.charOrbit N θ := by
    constructor
    · intro h
      by_contra hc
      exact h (by rw [if_neg hc, mul_zero])
    · intro hc
      rw [if_pos hc, mul_one]
      exact hec
  rw [IsConstituentOf, hres, cfInner_smul_orbitSum_eq_mul_ite hθ hφ e]
  exact key

end Work.Clifford
