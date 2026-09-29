import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Submission.Commons.Polynomial.Prod.MonicProdConjClosed

open Polynomial
open scoped BigOperators

noncomputable section

namespace Commons.Polynomial.Prod

/-- If `b : Fin n → ℂ` is an injective family of algebraic integers closed
under `ℚ`-conjugation (every `ℂ`-root of each `minpoly ℚ (b k)` is again one
of the `b`-values), then for every `G : ℚ[X]` the product of the values
`G(b i)` over all `i` is a rational number.

Proof sketch: `MonicProdConjClosed` gives an integer polynomial `P` whose
complexification is `∏ (X - b i)`; the product `∏ G(b i)` is then the
resultant `Res(P, G)` (a rational number, by the definition of the resultant
as a determinant), identified with the product of evaluations via the root
product formula for resultants. -/
lemma ProdEvalConjClosed {n : ℕ} (b : Fin n → ℂ) (G : ℚ[X])
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : ∀ k : Fin n, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t : Fin n, b t = w) :
    ∃ q : ℚ, (∏ i : Fin n, (G.map (algebraMap ℚ ℂ)).eval (b i)) = (q : ℂ) := by
  classical
  obtain ⟨P, hP⟩ := MonicProdConjClosed b hb hinj hclosed
  let Pq : ℚ[X] := P.map (algebraMap ℤ ℚ)
  let f : ℂ[X] := Pq.map (algebraMap ℚ ℂ)
  let g : ℂ[X] := G.map (algebraMap ℚ ℂ)
  let q : ℚ := Pq.resultant G (natDegree f) (natDegree g)
  let S : Finset ℂ := Finset.univ.image b
  have hf_map : f = P.map (algebraMap ℤ ℂ) := by
    dsimp [f, Pq]
    rw [Polynomial.map_map]
    congr
  have hf_prod : f = ∏ a ∈ S, (X - C a) := by
    calc
      f = ∏ i : Fin n, (X - C (b i)) := by rw [hf_map, hP]
      _ = ∏ a ∈ S, (X - C a) := by
        symm
        exact Finset.prod_image (s := (Finset.univ : Finset (Fin n))) (g := b)
          (f := fun a : ℂ => X - C a) (by intro x hx y hy hxy; exact hinj hxy)
  have hroots : f.roots = S.val := by
    calc
      f.roots = (∏ a ∈ S, (X - C a)).roots := by rw [hf_prod]
      _ = S.val := roots_prod_X_sub_C S
  have hmonic : f.Monic := by
    rw [hf_map, ← hP]
    exact monic_prod_of_monic (Finset.univ : Finset (Fin n)) (fun i => X - C (b i))
      (by intro i hi; exact monic_X_sub_C (b i))
  have hres : f.resultant g (natDegree f) (natDegree g) =
      (f.roots.map (fun x => Polynomial.eval x g)).prod := by
    rw [Polynomial.resultant_eq_prod_eval f g (natDegree g) (le_rfl) (IsAlgClosed.splits f)]
    rw [Polynomial.Monic.leadingCoeff hmonic]
    simp
  have hq_complex : (q : ℂ) = f.resultant g (natDegree f) (natDegree g) := by
    dsimp [q, f, g]
    symm
    exact Polynomial.resultant_map_map Pq G (natDegree (Pq.map (algebraMap ℚ ℂ)))
      (natDegree (G.map (algebraMap ℚ ℂ))) (algebraMap ℚ ℂ)
  refine ⟨q, ?_⟩
  calc
    (∏ i : Fin n, (G.map (algebraMap ℚ ℂ)).eval (b i))
        = ∏ i : Fin n, Polynomial.eval (b i) g := by rfl
    _ = ∏ a ∈ S, Polynomial.eval a g := by
        dsimp [S]
        symm
        exact Finset.prod_image (s := (Finset.univ : Finset (Fin n))) (g := b)
          (f := fun a : ℂ => Polynomial.eval a g) (by intro x hx y hy hxy; exact hinj hxy)
    _ = (f.roots.map (fun x => Polynomial.eval x g)).prod := by
        rw [hroots]
        exact (Finset.prod_eq_multiset_prod S (fun x : ℂ => Polynomial.eval x g)).symm
    _ = f.resultant g (natDegree f) (natDegree g) := hres.symm
    _ = (q : ℂ) := hq_complex.symm

end Commons.Polynomial.Prod