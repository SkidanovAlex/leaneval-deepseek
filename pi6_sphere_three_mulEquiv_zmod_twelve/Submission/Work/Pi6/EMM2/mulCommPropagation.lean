import Mathlib
import Submission.Work.Pi6.EMM2.Statements
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000

/-!
# Graded commutativity propagates from page 2 to all pages

If the product of a `CohSS` is commutative in *every* bidegree on page `2`, then it is commutative
in every bidegree on every page `r ≥ 2`.

The point is that `S.proj r ·` presents `E_{r+1}^{·}` as a quotient of the cycles of `E_r^{·}` and
`S.proj_mul` says that the product agrees with the induced product on the quotient; since `proj` is
surjective on every page (`S.proj_surj`), two elements of `E_{r+1}` can be lifted to cycles of
`E_r`, their product is again a cycle by the Leibniz rule `S.leibniz` (the differentials of the
factors vanish), and the comparison is pushed to the quotient.  No bidegree restriction (first
quadrant / stable range) is needed: the statement is purely about the `CohSS` axioms.
-/

namespace Work.Pi6.EMM2

theorem mulCommPropagation (𝕜 : Type) [Field 𝕜] (S : Work.Pi6.CohSS 𝕜)
    (a b c : ℤ × ℤ) (h : a + b = c)
    (h2 : ∀ (x : S.E 2 a) (y : S.E 2 b),
      S.mul 2 a b c h x y = S.mul 2 b a c (by rw [← h]; abel) y x) :
    ∀ (r : ℕ) (x : S.E r a) (y : S.E r b), 2 ≤ r →
      S.mul r a b c h x y = S.mul r b a c (by rw [← h]; abel) y x := by
  -- We prove the statement for page `k + 2` for every `k`, with the reversed proof argument `h'`
  -- kept general so that `mul_congr` is available at every step.
  have key : ∀ k : ℕ, ∀ (h' : b + a = c) (x : S.E (k+2) a) (y : S.E (k+2) b),
      S.mul (k+2) a b c h x y = S.mul (k+2) b a c h' y x := by
    intro k
    induction k with
    | zero =>
      intro h' x y
      rw [S.mul_congr 2 b a c h' (by rw [← h]; abel) y x]
      exact h2 x y
    | succ k ih =>
      intro h' x y
      have hr : 2 ≤ k + 2 := by omega
      -- lift the two classes to cycles on page `k + 2`
      obtain ⟨X, hX⟩ := S.proj_surj (k + 2) a hr x
      obtain ⟨Y, hY⟩ := S.proj_surj (k + 2) b hr y
      have hx0 : (ModuleCat.Hom.hom (S.d (k + 2) a (a + Work.Pi6.vr (k + 2))))
          (X : S.E (k+2) a) = 0 := by simpa using X.2
      have hy0 : (ModuleCat.Hom.hom (S.d (k + 2) b (b + Work.Pi6.vr (k + 2))))
          (Y : S.E (k+2) b) = 0 := by simpa using Y.2
      -- products of cycles are cycles (Leibniz rule, both differentials vanish)
      have hw1 : (ModuleCat.Hom.hom (S.d (k + 2) c (c + Work.Pi6.vr (k + 2))))
          (S.mul (k+2) a b c h (X : S.E (k+2) a) (Y : S.E (k+2) b)) = 0 := by
        rw [S.leibniz (k+2) a b c h (X : S.E (k+2) a) (Y : S.E (k+2) b) hr, hx0, hy0]
        simp
      have hw2 : (ModuleCat.Hom.hom (S.d (k + 2) c (c + Work.Pi6.vr (k + 2))))
          (S.mul (k+2) b a c h' (Y : S.E (k+2) b) (X : S.E (k+2) a)) = 0 := by
        rw [S.leibniz (k+2) b a c h' (Y : S.E (k+2) b) (X : S.E (k+2) a) hr, hy0, hx0]
        simp
      -- the product on page `k + 3` is the product of the projections
      have hp1 : S.proj (k + 2) c ⟨S.mul (k+2) a b c h (X : S.E (k+2) a) (Y : S.E (k+2) b), hw1⟩
          = S.mul (k+2+1) a b c h (S.proj (k+2) a X) (S.proj (k+2) b Y) :=
        S.proj_mul (k+2) a b c h X Y ⟨_, hw1⟩ hr rfl
      have hp2 : S.proj (k + 2) c ⟨S.mul (k+2) b a c h' (Y : S.E (k+2) b) (X : S.E (k+2) a), hw2⟩
          = S.mul (k+2+1) b a c h' (S.proj (k+2) b Y) (S.proj (k+2) a X) :=
        S.proj_mul (k+2) b a c h' Y X ⟨_, hw2⟩ hr rfl
      -- the two representatives agree on page `k + 2` by the induction hypothesis
      have hz : (⟨S.mul (k+2) a b c h (X : S.E (k+2) a) (Y : S.E (k+2) b), hw1⟩ :
            ↥(ModuleCat.Hom.hom (S.d (k + 2) c (c + Work.Pi6.vr (k+2)))).ker)
          = ⟨S.mul (k+2) b a c h' (Y : S.E (k+2) b) (X : S.E (k+2) a), hw2⟩ :=
        Subtype.ext (ih h' X Y)
      calc S.mul (k+2+1) a b c h x y
          = S.mul (k+2+1) a b c h (S.proj (k+2) a X) (S.proj (k+2) b Y) := by rw [hX, hY]
        _ = S.proj (k + 2) c ⟨S.mul (k+2) a b c h (X : S.E (k+2) a) (Y : S.E (k+2) b), hw1⟩ :=
              hp1.symm
        _ = S.proj (k + 2) c ⟨S.mul (k+2) b a c h' (Y : S.E (k+2) b) (X : S.E (k+2) a), hw2⟩ :=
              by rw [hz]
        _ = S.mul (k+2+1) b a c h' (S.proj (k+2) b Y) (S.proj (k+2) a X) := hp2
        _ = S.mul (k+2+1) b a c h' y x := by rw [hX, hY]
  intro r x y hr
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  exact key k (by rw [← h]; abel) x y

end Work.Pi6.EMM2
