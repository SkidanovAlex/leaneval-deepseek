import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE10.Psi
import Submission.Work.WilE8.StarR.psiV_preimage_init_ocube

namespace Work.WilE8.StarR

open WilkiesDesign WilkiesDesign.E

/-!
# Projection of `StarR`-sets

The area-E7 intersection theorem `hE7` says that a finite intersection of `Star`-sets is a
`Star`-set, at the price of a polynomial in the sum of the degrees (and after intersecting with
the cube).  `hOcube` says that the open cube `(-1,1)^N` is a `Star`-set, and `hStarProj` says that
projecting away the last coordinate of a `Star`-set is again a `Star`-set (at no cost).

Together they give the same closure statement for the *unbounded* sets `StarR` (preimages of
`Star`-sets under the coordinatewise compactification `psiV`), which is what the induction of
`E8_reduce` uses.

The mathematical point is the following.  For `X = psiV ⁻¹' Z` one would like to take
`projLast X = psiV ⁻¹' (projLast Z)`, but this is **false**: `projLast Z` may be witnessed only by
a boundary value of the last coordinate, and `psi` never takes the values `±1`, so such a witness
is killed by `psiV ⁻¹'`.  Intersecting `Z` with the *open* cube before projecting removes exactly
the bad witnesses: with `W = Fin.init '' (cubeC (n+1) ∩ (Z ∩ ocube (n+1)))` one has

  `psiV ⁻¹' W = projLast (psiV ⁻¹' Z)`

(`ψ` is a bijection `ℝ ≃ (-1,1)`, so an existential quantifier over the last coordinate can be
moved through it).  The `Star`-bounds for `W` come from `hE7` (intersect `Z` with `ocube`),
`hStarProj` (project) and `hOcube`; the degree is `p (D + (2(n+1)+1))`, which is again a
polynomial in `D`.
-/

theorem proj
    (hE7 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, WilkiesDesign.E.Star F (D i) n (Y i)) →
      WilkiesDesign.E.Star a (p.eval (∑ i, D i)) n (WilkiesDesign.E.cubeC n ∩ ⋂ i, Y i))
    (hStarProj : ∀ {N F D : ℕ} {Z : Set (Fin (N + 1) → ℝ)}, WilkiesDesign.E.Star F D (N + 1) Z →
      WilkiesDesign.E.Star F D N (Fin.init '' Z))
    (hOcube : ∀ N : ℕ, WilkiesDesign.E.Star N (2 * N + 1) N (Work.WilE8.ocube N))
    (a0 n : ℕ) :
    ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (n + 1) → ℝ)),
      WilkiesDesign.E.StarR a0 D (n + 1) X →
        WilkiesDesign.E.StarR a (p.eval D) n (WilkiesDesign.projLast X) := by
  -- The intersection theorem at the format bound `max a0 (n+1)`, in dimension `n+1`
  -- (`a0` bounds the pieces of `Z`, `n+1` bounds those of the open cube).
  obtain ⟨a, p, hp⟩ := hE7 (max a0 (n + 1)) (n + 1)
  refine ⟨a, p.comp (Polynomial.X + Polynomial.C (2 * (n + 1) + 1)), ?_⟩
  intro D X hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  -- `Z` is a `Star`-set of format `max a0 (n+1)` …
  have hZ' : Star (max a0 (n + 1)) D (n + 1) Z := Star.mono hZ (le_max_left _ _) le_rfl
  -- … and so is the open cube, by `hOcube`.
  have hoc : Star (max a0 (n + 1)) (2 * (n + 1) + 1) (n + 1) (Work.WilE8.ocube (n + 1)) :=
    Star.mono (hOcube (n + 1)) (le_max_right _ _) le_rfl
  -- Intersect the two.
  have hmain := hp 2 (![D, 2 * (n + 1) + 1] : Fin 2 → ℕ)
    (![Z, Work.WilE8.ocube (n + 1)] : Fin 2 → Set (Fin (n + 1) → ℝ))
    (by
      intro i
      fin_cases i
      · simpa using hZ'
      · simpa using hoc)
  have hsum : (∑ i : Fin 2, (![D, 2 * (n + 1) + 1] : Fin 2 → ℕ) i) = D + (2 * (n + 1) + 1) := by
    rw [Fin.sum_univ_two]
    simp
  have hset : (⋂ i : Fin 2,
        (![Z, Work.WilE8.ocube (n + 1)] : Fin 2 → Set (Fin (n + 1) → ℝ)) i)
      = Z ∩ Work.WilE8.ocube (n + 1) := by
    ext x
    simp [Fin.forall_fin_two]
  rw [hsum, hset] at hmain
  -- Project away the last coordinate.
  have hproj := hStarProj hmain
  refine ⟨Fin.init '' (cubeC (n + 1) ∩ (Z ∩ Work.WilE8.ocube (n + 1))), ?_, ?_⟩
  · -- the degree `p (D + (2(n+1)+1))` is `q D` for the fixed polynomial `q = p.comp (X + 2n+3)`
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact hproj
  · -- and its `psiV`-preimage is exactly `projLast (psiV ⁻¹' Z)`
    rw [psiV_preimage_init_ocube]

end Work.WilE8.StarR
