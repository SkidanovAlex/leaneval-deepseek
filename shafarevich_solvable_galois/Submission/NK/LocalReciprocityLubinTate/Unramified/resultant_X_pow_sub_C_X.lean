import Mathlib.RingTheory.Polynomial.Resultant.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

open Polynomial

namespace NK.LocalReciprocityLubinTate.Unramified

/-- For a commutative domain `A` of characteristic `p`, a prime, and `q = p ^ k`, the resultant
of `X ^ q - C X` with `h` (viewed over `A[X]`) equals the polynomial obtained from `h` by raising
each coefficient to the `q`-th power. -/
theorem resultant_X_pow_sub_C_X {A : Type u} [CommRing A] [IsDomain A]
    {p q k : ℕ} [Fact p.Prime] [CharP A p] (hq : q = p ^ k) (h : Polynomial A) :
    Polynomial.resultant (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A))
        (Polynomial.map Polynomial.C h)
      = ∑ j ∈ h.support, Polynomial.C (h.coeff j ^ q) * (Polynomial.X : Polynomial A) ^ j := by
  rw [hq]
  -- Work over the ring `A[X]`, and base change along `φ : A[X] → A[X]`, `X ↦ X ^ (p ^ k)`,
  -- which adjoins a `p ^ k`-th root of `X` (namely `X` itself in the target) and is injective.
  set F : (Polynomial A)[X] := Polynomial.X ^ (p ^ k) - Polynomial.C (Polynomial.X : Polynomial A)
    with hF
  set G : (Polynomial A)[X] := Polynomial.map Polynomial.C h with hG
  set φ : (Polynomial A) →+* (Polynomial A) := (Polynomial.expand A (p ^ k)).toRingHom with hφ
  have hnpos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hφinj : Function.Injective φ := by
    rw [hφ]
    intro a b hab
    exact Polynomial.expand_injective hnpos hab
  -- `φ` fixes the constants `C a`.
  have hcomp : φ.comp Polynomial.C = Polynomial.C := by
    ext a
    rw [RingHom.comp_apply, hφ]
    rw [show (Polynomial.expand A (p ^ k)).toRingHom (Polynomial.C a)
          = (Polynomial.expand A (p ^ k)) (Polynomial.C a) from rfl, Polynomial.expand_C]
  have hFnat : F.natDegree = p ^ k := by
    rw [hF]; exact Polynomial.natDegree_X_pow_sub_C
  have hGn : (Polynomial.map φ G).natDegree ≤ G.natDegree :=
    le_of_eq (Polynomial.natDegree_map_eq_of_injective hφinj G)
  have hGmap : Polynomial.map φ G = G := by
    rw [hG, Polynomial.map_map, hcomp]
  -- In the target, `X ^ (p ^ k) - C X = (X - C X) ^ (p ^ k)`.
  have hFmap : Polynomial.map φ F
      = (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial A)) ^ (p ^ k) := by
    rw [hF, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hφ]
    rw [show (Polynomial.expand A (p ^ k)).toRingHom (Polynomial.X : Polynomial A)
          = (Polynomial.expand A (p ^ k)) (Polynomial.X : Polynomial A) from rfl,
        Polynomial.expand_X]
    rw [sub_pow_char_pow, Polynomial.C_pow]
  have h1 : φ (Polynomial.resultant F G)
      = Polynomial.resultant (Polynomial.map φ F) (Polynomial.map φ G) F.natDegree G.natDegree :=
    (Polynomial.resultant_map_map F G F.natDegree G.natDegree φ).symm
  -- The right hand side is `map (iterateFrobenius A p k) h`.
  have hA : Polynomial.map (iterateFrobenius A p k) h
      = ∑ j ∈ h.support, Polynomial.C (h.coeff j ^ (p ^ k)) * (Polynomial.X : Polynomial A) ^ j := by
    rw [show Polynomial.map (iterateFrobenius A p k) h
          = Polynomial.eval₂ (Polynomial.C.comp (iterateFrobenius A p k))
              (Polynomial.X : Polynomial A) h from rfl]
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    simp only [RingHom.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
  -- `expand` and `map` commute, and `map (iterateFrobenius A p k) ∘ expand = (·) ^ (p ^ k)`.
  have hB : φ (Polynomial.map (iterateFrobenius A p k) h) = h ^ (p ^ k) := by
    rw [show φ (Polynomial.map (iterateFrobenius A p k) h)
          = (Polynomial.expand A (p ^ k)) (Polynomial.map (iterateFrobenius A p k) h) from rfl]
    rw [← Polynomial.map_expand, Polynomial.map_iterateFrobenius_expand]
  have key : φ (Polynomial.resultant F G)
      = φ (∑ j ∈ h.support, Polynomial.C (h.coeff j ^ (p ^ k))
            * (Polynomial.X : Polynomial A) ^ j) := by
    rw [h1, hFmap, hFnat]
    rw [Polynomial.resultant_X_sub_C_pow_left (Polynomial.X : Polynomial A)
          (Polynomial.map φ G) (p ^ k) G.natDegree hGn]
    rw [hGmap]
    rw [show Polynomial.eval (Polynomial.X : Polynomial A) G = h from by
          rw [hG, Polynomial.eval_map, Polynomial.eval₂_C_X]]
    rw [← hA, hB]
  exact hφinj key

end NK.LocalReciprocityLubinTate.Unramified
