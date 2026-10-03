import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.foxD_eq_sum_zeta_magRewRel
import Submission.Work.ORLyndon.levelPart_finset_sum
import Submission.Work.ORLyndon.levelPart_eq_of_support_level
import Submission.Work.ORLyndon.levelOf_mul_support
import Submission.Work.ORLyndon.levelOf_zpow_presentRho_t
import Submission.Work.ORLyndon.levelOf_support_mapDomainRingHom_zeta
import Submission.Work.ORLyndon.sigma_zeta_eq_one

/-!
# The `σ_t`-level decomposition of the root Fox vector (Magnus step)

Let `r = u ^ l` with `σ_t u = 0` (written multiplicatively `sigma t u = 1`), let `G = ⟨α | r⟩` and
let `ζ = zeta t : F((α \ {t}) × ℤ) →* F α`, `(s,i) ↦ t^i s t^{-i}`, be the Magnus section, so that
`u = ζ (magRewRel t u)` (`Work.ORLyndon.eq_zeta_magRewRel`).

The main theorem of this file, `Work.ORLyndon.levelPart_rootVec_magnus`, computes the `i`-th level
part of the `x`-component of the root Fox vector: it is the image under the presentation of the
`(x,i)`-component of the Fox derivative of the Magnus rewriting of `u`, multiplied by `t̄^i`.  This
is the "leading term" computation of the Magnus induction of the Cohen--Lyndon theorem.

The proof decomposes into

* the chain rule `Work.ORLyndon.foxD_eq_sum_zeta_magRewRel`, which writes `∂u/∂x` as the sum over
  the decorated letters `(x,j)` of the Fox vector of `magRewRel t u` pushed through `ζ` (the terms
  with first component `≠ x` vanish, since `∂ζ(s,j)/∂x = 0` for `s ≠ x`);
* the homogeneity of the summands: `mapDomainRingHom K (presentRho r ∘ ζ)` has image in the
  level-`0` part (every `ζ(s,j) = t^j s t^{-j}` has `σ_t`-exponent `0`) and `of (t̄^j)` has level
  `j`, so the summand with decorated index `j` is homogeneous of level `j`;
* consequently the level-`i` part picks out the single summand `(x,i)`.

## Main result

* `Work.ORLyndon.levelPart_rootVec_magnus`
-/

namespace Work.ORLyndon

open MonoidAlgebra

/-- `mapDomainRingHom` sends the basis element `of g` to `of (φ g)`. -/
theorem mapDomainRingHom_of_of {K M N : Type*} [Semiring K] [Monoid M] [Monoid N]
    (φ : M →* N) (g : M) :
    MonoidAlgebra.mapDomainRingHom K φ (MonoidAlgebra.of K M g) =
      MonoidAlgebra.of K N (φ g) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
    MonoidAlgebra.of_apply]

/-- `mapDomainRingHom` is compatible with the composition of the monoid homomorphisms. -/
theorem mapDomainRingHom_comp_of {K M N P : Type*} [Semiring K] [Monoid M] [Monoid N] [Monoid P]
    (φ : N →* P) (ψ : M →* N) (c : MonoidAlgebra K M) :
    MonoidAlgebra.mapDomainRingHom K (φ.comp ψ) c =
      MonoidAlgebra.mapDomainRingHom K φ (MonoidAlgebra.mapDomainRingHom K ψ c) := by
  rw [MonoidAlgebra.mapDomainRingHom_comp (R := K) φ ψ]
  rfl

/-- **The Fox chain rule with `ζ = zeta t`.**  For `σ_t u = 0` one has `u = ζ (magRewRel t u)`,
so the Fox derivative of `u` with respect to `x ≠ t` is the sum, over the decorated letters `(x,j)`
of the Magnus rewriting, of the pushed-forward Fox derivative times `t^j`. -/
theorem rootVec_eq_sum_zeta {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (hσ : Work.OROneRel.sigma t u = 1) :
    Work.ORLyndon.rootVec K r u x =
      ∑ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
        (if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
        else 0) := by
  classical
  have hchain : foxD (K := K) x u =
      (foxFD (K := K) (Work.OROneRel.magRewRel t u)).sum (fun q c =>
        if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t) c *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0) :=
    foxD_eq_sum_zeta_magRewRel t x hxt u hσ
  have hsum : (foxFD (K := K) (Work.OROneRel.magRewRel t u)).sum (fun q c =>
        if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t) c *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0)
      = ∑ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
          (if (q.1 : α) = x then
            MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)
                (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
              MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
          else 0) :=
    Finsupp.sum_of_support_subset _ (le_refl _) _ (by
      intro q _
      by_cases h : (q.1 : α) = x <;> simp [h])
  have hper : ∀ q : ({a : α // a ≠ t} × ℤ),
      presentAlg K r (if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0) =
      (if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
        else 0) := by
    intro q
    show MonoidAlgebra.mapDomainRingHom K (presentRho r) (if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0) = _
    by_cases h : (q.1 : α) = x
    · rw [if_pos h, if_pos h, map_mul, mapDomainRingHom_comp_of]
      rw [mapDomainRingHom_of_of, ← map_zpow (presentRho r) (FreeGroup.of t) (q.2)]
    · rw [if_neg h, if_neg h, map_zero]
  calc Work.ORLyndon.rootVec K r u x
      = presentAlg K r (foxD (K := K) x u) := by rw [Work.ORLyndon.rootVec_apply]
    _ = presentAlg K r ((foxFD (K := K) (Work.OROneRel.magRewRel t u)).sum (fun q c =>
          if (q.1 : α) = x then
            MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t) c *
              MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
          else 0)) := by rw [hchain]
    _ = presentAlg K r (∑ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
          (if (q.1 : α) = x then
            MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)
                (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
              MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
          else 0)) := by rw [hsum]
    _ = ∑ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
          presentAlg K r (if (q.1 : α) = x then
            MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)
                (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
              MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
          else 0) := map_sum _ _ _
    _ = _ := Finset.sum_congr rfl (fun q _ => hper q)

/-- **The level-`i` part of the `x`-component of the root Fox vector.**  This is the leading-term
computation of the Magnus step of the Cohen--Lyndon induction: the level-`i` part consists of the
single summand of the chain rule belonging to the decorated letter `(x, i)`. -/
theorem levelPart_rootVec_magnus {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ) :
    Work.ORLyndon.levelPart t r u l hpow hσ i (Work.ORLyndon.rootVec K r u x) =
      MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
          (Work.ORLyndon.foxD (K := K) (X := ({a : α // a ≠ t} × ℤ))
            ((⟨x, hxt⟩ : {a : α // a ≠ t}), i) (Work.OROneRel.magRewRel t u)) *
        MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (i : ℤ)) := by
  classical
  -- the two indices between which the level decomposition singles out a summand
  set q₀ : ({a : α // a ≠ t} × ℤ) := ((⟨x, hxt⟩ : {a : α // a ≠ t}), i) with hq₀
  have hqq : ∀ q : ({a : α // a ≠ t} × ℤ), (q.1 : α) = x → i = q.2 → q = q₀ := by
    intro q h1 h2
    rw [hq₀]
    exact Prod.ext (Subtype.ext h1) h2.symm
  -- step 1: the summands of the chain rule are homogeneous, of level the decoration index
  have hstep : ∀ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
      levelPart t r u l hpow hσ i (if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
        else 0) =
      (if (q.1 : α) = x then
        (if i = q.2 then
          MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
              (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
        else 0) else 0) := by
    intro q _
    by_cases h : (q.1 : α) = x
    · rw [if_pos h, if_pos h]
      have hA : ∀ g ∈ (MonoidAlgebra.mapDomainRingHom K
            ((presentRho r).comp (Work.OROneRel.zeta t))
            (foxFD (K := K) (Work.OROneRel.magRewRel t u) q)).coeff.support,
          levelOf t r u l hpow hσ g = Multiplicative.ofAdd (0 : ℤ) := by
        intro g hg
        simpa using levelOf_support_mapDomainRingHom_zeta t r u l hpow hσ
          (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) g hg
      have hB : ∀ g ∈ (MonoidAlgebra.of K (OneRelatorGroup r)
            ((presentRho r (FreeGroup.of t)) ^ (q.2))).coeff.support,
          levelOf t r u l hpow hσ g = Multiplicative.ofAdd (q.2) := by
        intro g hg
        rw [MonoidAlgebra.of_apply] at hg
        have hg' : g = (presentRho r (FreeGroup.of t)) ^ (q.2) := by
          have := Finsupp.support_single_subset hg
          rwa [Finset.mem_singleton] at this
        rw [hg', levelOf_zpow_presentRho_t t r u l hpow hσ (q.2)]
      have hAB : ∀ g ∈ (MonoidAlgebra.mapDomainRingHom K
            ((presentRho r).comp (Work.OROneRel.zeta t))
            (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
            MonoidAlgebra.of K (OneRelatorGroup r)
              ((presentRho r (FreeGroup.of t)) ^ (q.2))).coeff.support,
          levelOf t r u l hpow hσ g = Multiplicative.ofAdd (q.2) := by
        have hm := levelOf_mul_support t r u l hpow hσ hA hB
        simpa using hm
      exact levelPart_eq_of_support_level t r u l hpow hσ i (q.2) _ hAB
    · rw [if_neg h, if_neg h, levelPart_zero]
  -- step 2: all summands vanish except the one of the decorated letter `(x, i)`
  have hfin : (∑ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
        (if (q.1 : α) = x then
          (if i = q.2 then
            MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
                (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
              MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
          else 0) else 0)) =
      MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
          (foxFD (K := K) (Work.OROneRel.magRewRel t u) q₀) *
        MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (i : ℤ)) := by
    by_cases hmem : q₀ ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support
    · have hsingle : ∀ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
          q ≠ q₀ →
          (if (q.1 : α) = x then
            (if i = q.2 then
              MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
                  (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
                MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
            else 0) else 0) = 0 := by
        intro q _ hne
        by_cases h : (q.1 : α) = x
        · by_cases h2 : i = q.2
          · rw [if_pos h, if_pos h2]
            exact absurd (hqq q h h2) hne
          · rw [if_pos h, if_neg h2]
        · rw [if_neg h]
      rw [Finset.sum_eq_single q₀ hsingle (fun hnot => absurd hmem hnot), hq₀]
      simp
    · have hzero : ∀ q ∈ (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support,
          (if (q.1 : α) = x then
            (if i = q.2 then
              MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
                  (foxFD (K := K) (Work.OROneRel.magRewRel t u) q) *
                MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (q.2))
            else 0) else 0) = 0 := by
        intro q hq
        by_cases h : (q.1 : α) = x
        · by_cases h2 : i = q.2
          · rw [if_pos h, if_pos h2]
            exact absurd ((hqq q h h2) ▸ hq) hmem
          · rw [if_pos h, if_neg h2]
        · rw [if_neg h]
      rw [Finset.sum_eq_zero hzero]
      have hz : (foxFD (K := K) (Work.OROneRel.magRewRel t u)) q₀ = 0 :=
        Finsupp.notMem_support_iff.mp hmem
      rw [hz, map_zero, zero_mul]
  rw [rootVec_eq_sum_zeta t x hxt r u hσ,
    Work.ORLyndon.levelPart_finset_sum t r u l hpow hσ i
      (foxFD (K := K) (Work.OROneRel.magRewRel t u)).support _,
    Finset.sum_congr rfl hstep, hfin]
  rw [hq₀]
  simp only [Work.ORLyndon.foxFD_apply]

end Work.ORLyndon
