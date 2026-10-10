import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reduction modulo a quadratic relation in `x₀`

`Work.MotAS.ASRulV2M.reduce_quad`: for a commutative ring `R`, polynomials
`l A ∈ R[x₁,x₂]` and an arbitrary `y ∈ R[x₀,x₁,x₂]`, the class of `y` in
`R[x₀,x₁,x₂]/(x₀² + l x₀ + A)` can be represented by a polynomial which is
affine in `x₀`, with coefficients in `R[x₁,x₂]`.

The proof is a direct induction on the `MvPolynomial` structure
(`MvPolynomial.induction_on`): the set of elements of the form
`rename Fin.succ α + rename Fin.succ β * X 0` is closed under addition and,
modulo the quadratic relation, under multiplication by each variable `X n`
(`n = 0` uses `X 0² ≡ -(l X 0 + A)`; `n = 1, 2` because `X 1` and `X 2` are the
`Fin.succ`-pullbacks of `X 0` and `X 1`).
-/

namespace Work.MotAS.ASRulV2M

theorem reduce_quad {R : Type*} [CommRing R] (l A : MvPolynomial (Fin 2) R)
    (y : MvPolynomial (Fin 3) R) :
    ∃ α β : MvPolynomial (Fin 2) R,
      y - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
        ∈ Ideal.span {MvPolynomial.X 0 ^ 2
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A} := by
  classical
  set q : MvPolynomial (Fin 3) R := MvPolynomial.X 0 ^ 2
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A with hq
  have hqmem : q ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R)) :=
    Ideal.subset_span (Set.mem_singleton q)
  -- Every `y` is congruent modulo `q` to an element which is affine in `X 0`.
  have key : ∀ y : MvPolynomial (Fin 3) R,
      ∃ m : MvPolynomial (Fin 3) R,
        (∃ α β : MvPolynomial (Fin 2) R,
          m = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
        ∧ y - m ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R)) := by
    intro y
    refine MvPolynomial.induction_on (motive := fun z => ∃ m : MvPolynomial (Fin 3) R,
        (∃ α β : MvPolynomial (Fin 2) R,
          m = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
        ∧ z - m ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R))) y ?_ ?_ ?_
    · -- constants
      intro a
      exact ⟨MvPolynomial.C a, ⟨MvPolynomial.C a, 0, by simp⟩,
        by rw [sub_self]; exact Ideal.zero_mem _⟩
    · -- sums
      intro p r hp hr
      obtain ⟨mp, ⟨αp, βp, hmp⟩, hpI⟩ := hp
      obtain ⟨mr, ⟨αr, βr, hmr⟩, hrI⟩ := hr
      refine ⟨mp + mr, ⟨αp + αr, βp + βr, ?_⟩, ?_⟩
      · rw [hmp, hmr]; simp only [map_add]; ring
      · have : p + r - (mp + mr) = (p - mp) + (r - mr) := by ring
        rw [this]; exact Ideal.add_mem _ hpI hrI
    · -- multiplication by a variable
      intro p n hp
      obtain ⟨m, ⟨α, β, hm⟩, hpI⟩ := hp
      fin_cases n
      · -- `X 0`: use `X 0 ^ 2 = q - l * X 0 - A`
        refine ⟨_, ⟨-(β * A), α - β * l, rfl⟩, ?_⟩
        change p * MvPolynomial.X (0 : Fin 3)
            - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (-(β * A))
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α - β * l)
                  * MvPolynomial.X (0 : Fin 3)) ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R))
        have h2 : m * MvPolynomial.X (0 : Fin 3)
            - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (-(β * A))
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α - β * l)
                  * MvPolynomial.X (0 : Fin 3))
            = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * q := by
          rw [hm, hq]; simp only [map_mul, map_neg, map_sub]; ring
        have h4 : p * MvPolynomial.X (0 : Fin 3)
            - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (-(β * A))
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α - β * l)
                  * MvPolynomial.X (0 : Fin 3))
            = (p - m) * MvPolynomial.X (0 : Fin 3)
              + (m * MvPolynomial.X (0 : Fin 3)
                - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (-(β * A))
                    + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α - β * l)
                      * MvPolynomial.X (0 : Fin 3))) := by
          first | refl_ring1 | ring
        rw [h4, h2]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpI) (Ideal.mul_mem_left _ _ hqmem)
      · -- `X 1 = rename Fin.succ (X 0)`
        refine ⟨_, ⟨α * MvPolynomial.X (0 : Fin 2), β * MvPolynomial.X (0 : Fin 2), rfl⟩, ?_⟩
        change p * MvPolynomial.X (1 : Fin 3)
            - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α * MvPolynomial.X (0 : Fin 2))
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (β * MvPolynomial.X (0 : Fin 2))
                  * MvPolynomial.X (0 : Fin 3)) ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R))
        have hm' : m * MvPolynomial.X (1 : Fin 3)
            = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α * MvPolynomial.X (0 : Fin 2))
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (β * MvPolynomial.X (0 : Fin 2))
                * MvPolynomial.X (0 : Fin 3) := by
          rw [hm, map_mul, map_mul, MvPolynomial.rename_X, Fin.succ_zero_eq_one]; ring
        rw [← hm', ← sub_mul]
        exact Ideal.mul_mem_right _ _ hpI
      · -- `X 2 = rename Fin.succ (X 1)`
        refine ⟨_, ⟨α * MvPolynomial.X (1 : Fin 2), β * MvPolynomial.X (1 : Fin 2), rfl⟩, ?_⟩
        change p * MvPolynomial.X (2 : Fin 3)
            - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α * MvPolynomial.X (1 : Fin 2))
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (β * MvPolynomial.X (1 : Fin 2))
                  * MvPolynomial.X (0 : Fin 3)) ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) R))
        have hm' : m * MvPolynomial.X (2 : Fin 3)
            = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (α * MvPolynomial.X (1 : Fin 2))
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (β * MvPolynomial.X (1 : Fin 2))
                * MvPolynomial.X (0 : Fin 3) := by
          rw [hm, map_mul, map_mul, MvPolynomial.rename_X, Fin.succ_one_eq_two]; ring
        rw [← hm', ← sub_mul]
        exact Ideal.mul_mem_right _ _ hpI
  obtain ⟨m, ⟨α, β, hm⟩, hmI⟩ := key y
  exact ⟨α, β, by rw [hm] at hmI; exact hmI⟩

end Work.MotAS.ASRulV2M
