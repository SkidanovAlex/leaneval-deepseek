import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.topPart_mul
import Submission.Work.ORLyndon.levelPart_mul_top

/-!
# The bottom level part of a product is the product of the bottom level parts

This is the mirror of `Work.ORLyndon.topPart_mul` (`Submission/Work/ORLyndon/topPart_mul.lean`) for
the *minimum* level instead of the maximum: if every group element in the support of `a` has level
`≥ N` and every one in the support of `b` has level `≥ M`, then the terms of `a * b` of level exactly
`N + M` are precisely the products of a term of `a` of level `N` and a term of `b` of level `M`:

`levelPart N a * levelPart M b = levelPart (N+M) (a * b)`.

Together with the `≤` version (`topPart_mul`) this shows that the `σ_t`-level grading is compatible
with multiplication at *both* extreme levels; the leading-level transfer of the Magnus step of the
Cohen--Lyndon induction (`Work.ORLyndon.ann_rootVec_of_level_decomp`) needs the top version, and its
mirror (`Work.ORLyndon.ann_rootVec_of_level_decomp_bot`) the bottom one.

The proof reduces to the `≤` case (`Work.ORLyndon.filter_mul_filter`) applied to the homomorphism
`g ↦ (φ g)⁻¹`, whose level is the negative of the level of `φ`: the bound `N ≤ (φ g).toAdd` becomes
`(-(φ g).toAdd) ≤ -N`, i.e. `≤` for the negated level, and the `k`-th level part of `φ` is the
`-k`-th level part of `φ ∘ (-)⁻¹`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The negated level homomorphism `g ↦ (φ g)⁻¹`; it is a homomorphism because the target
`Multiplicative ℤ` is commutative. -/
def levelNeg {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) : G →* Multiplicative ℤ where
  toFun g := (φ g)⁻¹
  map_one' := by simp
  map_mul' g h := by
    show (φ (g * h))⁻¹ = (φ g)⁻¹ * (φ h)⁻¹
    rw [map_mul, mul_inv_rev, mul_comm]

@[simp] theorem levelNeg_apply {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) (g : G) :
    levelNeg φ g = (φ g)⁻¹ := rfl

@[simp] theorem levelNeg_toAdd {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) (g : G) :
    (levelNeg φ g).toAdd = -(φ g).toAdd := by
  simp [levelNeg]

/-- Congruence of `Finsupp.filter` in the predicate. -/
theorem Finsupp_filter_congr {α M : Type*} [Zero M] {p p' : α → Prop} [DecidablePred p]
    [DecidablePred p'] (h : p = p') (f : α →₀ M) :
    Finsupp.filter p f = Finsupp.filter p' f := by
  classical
  ext g
  by_cases hg : p g
  · rw [Finsupp.filter_apply_pos (f := f) (p := p) hg,
      Finsupp.filter_apply_pos (f := f) (p := p') (h ▸ hg)]
  · have hg' : ¬ p' g := by
      intro hc
      rw [← h] at hc
      exact hg hc
    rw [Finsupp.filter_apply_neg (f := f) (p := p) hg,
      Finsupp.filter_apply_neg (f := f) (p := p') hg']

/-- The level predicates of `φ` and of `levelNeg φ` agree up to negating the level. -/
theorem levelNeg_eq_pred {G : Type*} [Group G] (φ : G →* Multiplicative ℤ) (k : ℤ) :
    (fun g => levelNeg φ g = Multiplicative.ofAdd (-k))
      = (fun g => φ g = Multiplicative.ofAdd k) := by
  funext g
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : -((φ g).toAdd) = -k := by
      have h3 := congrArg Multiplicative.toAdd h
      simpa using h3
    refine Multiplicative.toAdd.injective ?_
    simpa using congrArg Neg.neg h2
  · refine Multiplicative.toAdd.injective ?_
    show (levelNeg φ g).toAdd = (Multiplicative.ofAdd (-k)).toAdd
    rw [levelNeg_toAdd, toAdd_ofAdd]
    have h2 := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd] at h2
    omega

/-- **The coefficient of a product of two bottom level parts**, in the general `ofCoeff` form: if the
levels of the support of `a` are `≥ N` and those of `b` are `≥ M`, then the coefficient at `g₀` of
the product of the two level parts is the coefficient of `g₀` in `a * b` when the level of `g₀` is
exactly `N + M`, and `0` otherwise. -/
theorem filter_mul_filter_bot {G : Type*} [Group G] {R : Type*} [Semiring R]
    (φ : G →* Multiplicative ℤ) (N M : ℤ) (a b : R[G])
    (ha : ∀ g ∈ a.coeff.support, N ≤ (φ g).toAdd)
    (hb : ∀ g ∈ b.coeff.support, M ≤ (φ g).toAdd) :
    MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff) *
        MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff) =
      MonoidAlgebra.ofCoeff
        (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) := by
  classical
  have ha' : ∀ g ∈ a.coeff.support, (levelNeg φ g).toAdd ≤ -N := by
    intro g hg
    rw [levelNeg_toAdd]
    have := ha g hg
    omega
  have hb' : ∀ g ∈ b.coeff.support, (levelNeg φ g).toAdd ≤ -M := by
    intro g hg
    rw [levelNeg_toAdd]
    have := hb g hg
    omega
  have hmain := filter_mul_filter (levelNeg φ) (-N) (-M) a b ha' hb'
  rw [show -N + -M = -(N + M) from by ring] at hmain
  rw [Finsupp_filter_congr (levelNeg_eq_pred φ N) a.coeff,
    Finsupp_filter_congr (levelNeg_eq_pred φ M) b.coeff,
    Finsupp_filter_congr (levelNeg_eq_pred φ (N + M)) (a * b).coeff] at hmain
  exact hmain

/-- The definition of `Work.ORLyndon.levelPart` in the `ofCoeff` vocabulary of
`filter_mul_filter_bot`. -/
theorem levelPart_eq_ofCoeff' {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ)
    (a : MonoidAlgebra K (OneRelatorGroup r)) :
    Work.ORLyndon.levelPart t r u l hpow hσ k a =
      MonoidAlgebra.ofCoeff (Finsupp.filter
        (fun g => Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) a.coeff) :=
  rfl

/-- **The bottom level parts multiply.**  If the levels of the terms of `a` are bounded below by `N`
and those of `b` by `M`, then the `N`-th level part of `a` times the `M`-th level part of `b` is the
`(N+M)`-th level part of `a * b`. -/
theorem botPart_mul {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {a b : MonoidAlgebra K (OneRelatorGroup r)} {N M : ℤ}
    (ha : ∀ g ∈ a.coeff.support, N ≤ (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd)
    (hb : ∀ g ∈ b.coeff.support, M ≤ (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd) :
    Work.ORLyndon.levelPart t r u l hpow hσ N a * Work.ORLyndon.levelPart t r u l hpow hσ M b =
      Work.ORLyndon.levelPart t r u l hpow hσ (N + M) (a * b) := by
  rw [levelPart_eq_ofCoeff' (K := K) t r u l hpow hσ N a,
    levelPart_eq_ofCoeff' (K := K) t r u l hpow hσ M b,
    levelPart_eq_ofCoeff' (K := K) t r u l hpow hσ (N + M) (a * b)]
  exact filter_mul_filter_bot (Work.ORLyndon.levelOf t r u l hpow hσ) N M a b ha hb

end Work.ORLyndon
