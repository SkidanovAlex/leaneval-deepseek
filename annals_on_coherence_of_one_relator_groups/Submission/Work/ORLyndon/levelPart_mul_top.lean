import Mathlib
import Submission.Work.ORLyndon.powDefs

/-!
# The top level of a product is the product of the top levels

Let `G` be a group, `φ : G →* Multiplicative ℤ` a "level" homomorphism and, for `k : ℤ`,
`levelPart φ k a` the sum of the terms of `a : R[G]` whose group element has level `k`.  The
level map is a homomorphism, so levels add under multiplication.  Consequently, if all the group
elements occurring in `a` have level `≤ N` and all those occurring in `b` have level `≤ M`, then
the terms of `a * b` of level exactly `N + M` are precisely the products of a term of `a` of
level `N` and a term of `b` of level `M`:

`levelPart φ N a * levelPart φ M b = levelPart φ (N+M) (a * b)`.

This is `Work.ORLyndon.levelPart_mul_top`, the compatibility of the `σ_t`-level grading with the
multiplication used in the Magnus step of the Cohen--Lyndon induction.  Everything is proved here
for an arbitrary group algebra; the one-relator statement is the specialization to
`φ = Work.ORLyndon.levelOf t r u l hpow hσ`.
-/

namespace Work.ORLyndon

open MonoidAlgebra

section General

variable {G : Type*} [Group G] {R : Type*} [Semiring R]

/-- **The coefficient of a product of two level parts.**  If every group element in the support
of `a` has level `≤ N` and every group element in the support of `b` has level `≤ M`, then the
coefficient at `g₀` of the product of the two level parts is the coefficient of `g₀` in `a * b`
if the level of `g₀` is exactly `N + M`, and `0` otherwise. -/
theorem coeff_filter_mul_filter (φ : G →* Multiplicative ℤ) (N M : ℤ) (a b : R[G])
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ M) (g₀ : G) :
    ((MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff) :
          R[G]) *
        (MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff) :
          R[G])).coeff g₀
      = if φ g₀ = Multiplicative.ofAdd (N + M) then (a * b).coeff g₀ else 0 := by
  classical
  let Ac : G →₀ R := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff
  let Bc : G →₀ R := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff
  have hAc : ∀ h, Ac h = if φ h = Multiplicative.ofAdd N then a.coeff h else 0 := by
    intro h; simp only [Ac, Finsupp.filter_apply]
  have hBc : ∀ h, Bc h = if φ h = Multiplicative.ofAdd M then b.coeff h else 0 := by
    intro h; simp only [Bc, Finsupp.filter_apply]
  have hAc_supp : Ac.support ⊆ a.coeff.support := by
    intro h hh
    rw [Finsupp.mem_support_iff] at hh ⊢
    by_cases hp : φ h = Multiplicative.ofAdd N
    · rw [hAc h, if_pos hp] at hh; exact hh
    · rw [hAc h, if_neg hp] at hh; exact absurd rfl hh
  have hlev_Ac : ∀ h ∈ Ac.support, (φ h).toAdd = N := by
    intro h hh
    have hne : Ac h ≠ 0 := Finsupp.mem_support_iff.mp hh
    have hp : φ h = Multiplicative.ofAdd N := by
      by_contra hc
      rw [hAc h, if_neg hc] at hne; exact hne rfl
    rw [hp, toAdd_ofAdd]
  have hlev_inv : ∀ h, (φ (h⁻¹ * g₀)).toAdd = -(φ h).toAdd + (φ g₀).toAdd := by
    intro h; simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  have hsum : (Ac.sum fun h r => r * Bc (h⁻¹ * g₀)) = ∑ h ∈ Ac.support, Ac h * Bc (h⁻¹ * g₀) :=
    Finsupp.sum_of_support_subset Ac (le_refl _) _ (fun i _ => by simp)
  have hab : (a * b).coeff g₀ = ∑ h ∈ a.coeff.support, a.coeff h * b.coeff (h⁻¹ * g₀) := by
    rw [MonoidAlgebra.coeff_mul_apply_left,
      Finsupp.sum_of_support_subset a.coeff (le_refl _) _ (fun i _ => by simp)]
  change (MonoidAlgebra.ofCoeff Ac * MonoidAlgebra.ofCoeff Bc).coeff g₀ =
    if φ g₀ = Multiplicative.ofAdd (N + M) then (a * b).coeff g₀ else 0
  rw [MonoidAlgebra.coeff_mul_apply_left]
  show Ac.sum (fun h r => r * Bc (h⁻¹ * g₀)) = _
  rw [hsum]
  by_cases hp : φ g₀ = Multiplicative.ofAdd (N + M)
  · rw [if_pos hp, hab]
    have hg0 : (φ g₀).toAdd = N + M := by rw [hp, toAdd_ofAdd]
    have key : ∀ h ∈ Ac.support, Ac h * Bc (h⁻¹ * g₀) = a.coeff h * b.coeff (h⁻¹ * g₀) := by
      intro h hh
      have hlevh : (φ h).toAdd = N := hlev_Ac h hh
      have hz : (φ (h⁻¹ * g₀)).toAdd = M := by
        rw [hlev_inv h, hlevh, hg0]; ring
      have hph : φ h = Multiplicative.ofAdd N := by rw [← ofAdd_toAdd (φ h), hlevh]
      have hpz : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        rw [← ofAdd_toAdd (φ (h⁻¹ * g₀)), hz]
      rw [hAc h, if_pos hph, hBc (h⁻¹ * g₀), if_pos hpz]
    rw [Finset.sum_congr rfl key]
    rw [Finset.sum_subset hAc_supp]
    intro x hxa hxAc
    have hax : a.coeff x ≠ 0 := Finsupp.mem_support_iff.mp hxa
    have hle : (φ x).toAdd ≤ N := ha x hxa
    have hpx : φ x ≠ Multiplicative.ofAdd N := by
      intro hcon
      apply hxAc
      have hx0 : Ac x ≠ 0 := by
        rw [hAc x, if_pos hcon]; exact hax
      exact Finsupp.mem_support_iff.mpr hx0
    have hne : (φ x).toAdd ≠ N := fun hc => hpx (by rw [← ofAdd_toAdd (φ x), hc])
    have hlt : (φ x).toAdd < N := lt_of_le_of_ne hle hne
    have hbz : b.coeff (x⁻¹ * g₀) = 0 := by
      by_contra hbne
      have hmem : x⁻¹ * g₀ ∈ b.coeff.support := Finsupp.mem_support_iff.mpr hbne
      have hbb := hb _ hmem
      rw [hlev_inv x, hg0] at hbb
      linarith
    rw [hbz, mul_zero]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro h hh
    have hlevh : (φ h).toAdd = N := hlev_Ac h hh
    have hz : Bc (h⁻¹ * g₀) = 0 := by
      by_contra hne
      have hph : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        by_contra hc
        rw [hBc (h⁻¹ * g₀), if_neg hc] at hne; exact hne rfl
      have hzM : (φ (h⁻¹ * g₀)).toAdd = M := by rw [hph, toAdd_ofAdd]
      have hg0 : (φ g₀).toAdd = N + M := by
        have h2 := hzM
        rw [hlev_inv h, hlevh] at h2
        linarith
      exact hp (by rw [← ofAdd_toAdd (φ g₀), hg0])
    rw [hz, mul_zero]

/-- **The top level parts multiply.**  If the levels of the terms of `a` are bounded above by `N`
and those of `b` by `M`, then the `N`-th level part of `a` times the `M`-th level part of `b` is
the `(N+M)`-th level part of `a * b`. -/
theorem filter_mul_filter (φ : G →* Multiplicative ℤ) (N M : ℤ) (a b : R[G])
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ M) :
    MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff) *
        MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff) =
      MonoidAlgebra.ofCoeff
        (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext (fun g₀ => ?_))
  rw [coeff_filter_mul_filter φ N M a b ha hb g₀]
  show (if φ g₀ = Multiplicative.ofAdd (N + M) then (a * b).coeff g₀ else 0) =
    (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) g₀
  rw [Finsupp.filter_apply]

end General

theorem levelPart_mul_top {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {a b : MonoidAlgebra K (OneRelatorGroup r)} {N M : ℤ}
    (ha : ∀ g ∈ a.coeff.support, (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ M) :
    Work.ORLyndon.levelPart t r u l hpow hσ N a * Work.ORLyndon.levelPart t r u l hpow hσ M b =
      Work.ORLyndon.levelPart t r u l hpow hσ (N + M) (a * b) := by
  classical
  have h := filter_mul_filter (Work.ORLyndon.levelOf t r u l hpow hσ) N M a b ha hb
  simpa only [Work.ORLyndon.levelPart] using h

end Work.ORLyndon
