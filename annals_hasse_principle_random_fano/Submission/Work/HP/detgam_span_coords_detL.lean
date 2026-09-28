import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram

namespace Work.HP

open Matrix

/-- The real Gram matrix of a family of real vectors transforms as expected under a change of
coordinates: if `u i = ∑ j, A i j • w j` (equivalently `u i x = ∑ j, A i j * w j x`), then
`Gram(u) = A * Gram(w) * Aᵀ`.

Proof: the matrix `U` with rows indexed by `ι` and columns by `κ'` whose `(x,i)` entry is `u i x`
equals `W * Aᵀ` where `W x j = w j x`; then `Gram(u) = Uᵀ * U` and `Gram(w) = Wᵀ * W`, and
`(W * Aᵀ)ᵀ * (W * Aᵀ) = A * (Wᵀ * W) * Aᵀ`. -/
lemma gram_of_coord_expansion {κ κ' ι : Type*} [Fintype κ] [Fintype ι]
    (w : κ → ι → ℝ) (A : Matrix κ' κ ℝ) (u : κ' → ι → ℝ)
    (h : ∀ i x, u i x = ∑ j, A i j * w j x) :
    (Matrix.of fun i j => ∑ x, u i x * u j x)
      = A * (Matrix.of fun i j => ∑ x, w i x * w j x) * Aᵀ := by
  set U : Matrix ι κ' ℝ := Matrix.of fun x i => u i x with hU
  set W : Matrix ι κ ℝ := Matrix.of fun x j => w j x with hW
  have hUW : U = W * Aᵀ := by
    ext x i
    simp only [hU, hW, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (w j x) (A i j))]
    exact h i x
  have hgram : (Matrix.of fun i j : κ' => ∑ x, u i x * u j x) = Uᵀ * U := by
    ext i j
    simp [hU, Matrix.mul_apply]
  have hgramw : (Matrix.of fun i j : κ => ∑ x, w i x * w j x) = Wᵀ * W := by
    ext i j
    simp [hW, Matrix.mul_apply]
  rw [hgram, hgramw, hUW, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- Covolume scaling under passing to a finite-index sublattice, in coordinates.

`K ⊆ ℤ^ι` is a rank-`2` lattice with `ℤ`-basis `b`, and `c, d ∈ K` are `ℤ`-linearly independent.
Writing `c = x₀ • b 0 + x₁ • b 1`, `d = y₀ • b 0 + y₁ • b 1` (the integer coordinates are
`(b.repr ⟨c, hc⟩) i` and `(b.repr ⟨d, hd⟩) i`), the lattice `span ℤ {c, d} ⊆ K` has covolume
`|x₀ y₁ - x₁ y₀|` times that of `K`.

PROOF.  Let `T : Matrix (Fin 2) (Fin 2) ℤ` be the coordinate matrix,
`T i j = (b.repr ⟨![c,d] i, _⟩) j`, so that `![c,d] i = ∑ j, T i j • (b j : ι → ℤ)`
(`Module.Basis.sum_repr`).  Let `G` be the real Gram matrix of `b` and `G'` that of the pair
`c, d`; passing to real coordinates, `G' = A G Aᵀ` with `A = T.map (↑)`, by
`gram_of_coord_expansion` (`Fin.sum_univ_two` unfolds the sums).  Hence
`G'.det = (T.det)^2 * G.det`.  Both `detL`s are the square roots of the corresponding Gram
determinants (`Lat.detL_basis_gram`, applied to `b` and to the basis `![c,d]` of
`span ℤ (Set.range ![c,d])`), and `√((T.det)^2 * G.det) = |T.det| * √(G.det)` by
`Real.sqrt_mul`/`Real.sqrt_sq_eq_abs`; finally `|(T.det : ℝ)| = ((|T.det| : ℤ) : ℝ)`
(`Int.cast_abs`) and `T.det = x₀ y₁ - x₁ y₀` by `Matrix.det_fin_two`. -/
theorem detgam_span_coords_detL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin 2) ℤ K)
    (c d : ι → ℤ) (hc : c ∈ K) (hd : d ∈ K) (hcd : LinearIndependent ℤ ![c, d]) :
    detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) =
      (((|(b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1 - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0| : ℤ)) : ℝ)
        * detL K := by
  classical
  -- Membership of the two vectors in `K`, phrased for the family `![c,d]`.
  have hmem : ∀ i : Fin 2, ![c, d] i ∈ K := by
    intro i
    fin_cases i
    · simpa using hc
    · simpa using hd
  -- The coordinate matrix of `c, d` in the basis `b`.
  set T : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => (b.repr ⟨![c, d] i, hmem i⟩) j with hT
  have hT0 : ∀ j : Fin 2, T 0 j = (b.repr ⟨c, hc⟩) j := by
    intro j
    have hsub : (⟨![c, d] 0, hmem 0⟩ : K) = ⟨c, hc⟩ := by
      apply Subtype.ext
      simp
    rw [hT]
    simp only [Matrix.of_apply, hsub]
  have hT1 : ∀ j : Fin 2, T 1 j = (b.repr ⟨d, hd⟩) j := by
    intro j
    have hsub : (⟨![c, d] 1, hmem 1⟩ : K) = ⟨d, hd⟩ := by
      apply Subtype.ext
      simp
    rw [hT]
    simp only [Matrix.of_apply, hsub]
  have hdetT : T.det = (b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
      - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0 := by
    rw [Matrix.det_fin_two]
    simp only [hT0, hT1]
  -- Expansion of `c, d` in the basis `b`.
  have hrepr : ∀ i : Fin 2, (∑ j, T i j • (b j : ι → ℤ)) = ![c, d] i := by
    intro i
    have h := congrArg (fun w : K => (w : ι → ℤ))
      (Module.Basis.sum_repr b (⟨![c, d] i, hmem i⟩ : K))
    have h2 : (∑ j, (b.repr ⟨![c, d] i, hmem i⟩) j • (b j : ι → ℤ)) = ![c, d] i := by
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [← h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hT]
    simp only [Matrix.of_apply]
  -- The Gram matrices of `b` and of `c, d`.
  set G : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of fun i j => ∑ x, (((b i : ι → ℤ)) x : ℝ) * (((b j : ι → ℤ)) x : ℝ) with hG
  set A : Matrix (Fin 2) (Fin 2) ℝ := T.map (fun z : ℤ => (z : ℝ)) with hA
  set G' : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of fun i j => ∑ x, ((![c, d] i) x : ℝ) * ((![c, d] j) x : ℝ) with hG'
  -- `c, d` in real coordinates are given by the matrix `A` applied to `b`.
  have hu : ∀ i x, ((![c, d] i) x : ℝ) = ∑ j, A i j * (((b j : ι → ℤ)) x : ℝ) := by
    intro i x
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (congrFun (hrepr i).symm x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      hA, Matrix.map_apply] at h2 ⊢
    exact h2
  have hGG' : G' = A * G * Aᵀ := by
    rw [hG', hG, hA]
    exact gram_of_coord_expansion (w := fun j x => (((b j : ι → ℤ)) x : ℝ))
      (A := T.map (fun z : ℤ => (z : ℝ))) (u := fun i x => ((![c, d] i) x : ℝ)) hu
  have hdet : G'.det = (T.det : ℝ) ^ 2 * G.det := by
    rw [hGG', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA]
    rw [show (T.map (fun z : ℤ => (z : ℝ))).det = (T.det : ℝ) from (Int.cast_det T).symm]
    ring
  -- Both `detL`s are square roots of the corresponding Gram determinants.
  have hL2 : detL K = Real.sqrt G.det := by
    rw [Lat.detL_basis_gram K b, hG]
  have hrange : (Set.range ![c, d] : Set (ι → ℤ)) = ({c, d} : Set (ι → ℤ)) := by
    rw [show (![c, d] : Fin 2 → ι → ℤ) = Matrix.vecCons c ![d] from rfl, Matrix.range_cons,
      show (![d] : Fin 1 → ι → ℤ) = Matrix.vecCons d Matrix.vecEmpty from rfl, Matrix.range_cons,
      Matrix.range_empty]
    ext x
    simp only [Set.mem_union, Set.mem_empty_iff_false, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have hspan : Submodule.span ℤ ({c, d} : Set (ι → ℤ))
      = Submodule.span ℤ (Set.range ![c, d]) := by
    rw [hrange]
  have hL1 : detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = Real.sqrt G'.det := by
    rw [hspan, Lat.detL_basis_gram _ (Module.Basis.span hcd)]
    congr 1
    rw [hG']
    simp only [Module.Basis.coe_span_apply]
  calc detL (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))
      = Real.sqrt G'.det := hL1
    _ = Real.sqrt ((T.det : ℝ) ^ 2 * G.det) := by rw [hdet]
    _ = |(T.det : ℝ)| * Real.sqrt G.det := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    _ = |(T.det : ℝ)| * detL K := by rw [hL2]
    _ = (((|(b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
              - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0| : ℤ)) : ℝ) * detL K := by
          rw [hdetT, ← Int.cast_abs]

end Work.HP
