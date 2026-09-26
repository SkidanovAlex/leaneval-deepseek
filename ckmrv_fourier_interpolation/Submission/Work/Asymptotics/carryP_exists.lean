import Mathlib
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.PropagateCarries
import Submission.Work.Residues.idealI_direct_augIdeal

/-!
# The carries `N` of the second basis `M'` (`carryP_exists`)

This file provides the second-basis analogue of `Work.Asymptotics.carry₁`, `carry₂`
(`Work.Asymptotics.PropagateCarries`): for every element `x ∈ R` the error vector
`rowDiffP x i = M'_i x - ∑ j, σ'(x)_{ij} M'_j` of the reduction modulo `𝓘` has a
decomposition

  `rowDiffP x i - ((T-1)² · (N x i).1 + S(T-1)² · (N x i).2) ∈ (z-1)R`

along the two generators `(T-1)²` and `S(T-1)²` of `𝓘` (the third generator `z-1` is absorbed
into the collapse ideal `augIdeal`).  The main point is that such carries are automatically a
**cocycle** modulo `augIdeal`:

  `(N (x*y) i).k - ∑ j, σ'(x)_{ij} • (N y j).k - (N x i).k * y ∈ augIdeal`,

which follows from the *exact* cocycle identity `rowDiffP_mul` for the error vector together
with the directness `Work.Residues.idealI_direct_augIdeal` of `(T-1)²R + S(T-1)²R` modulo
`(z-1)R`.

The construction is the same as in `Work.Asymptotics.PropagateCarries`:
`Work.Asymptotics.mem_idealI_exists` splits `rowDiffP x i ∈ 𝓘` into its `(T-1)²`, `S(T-1)²`
and `z-1` components, and `Classical.choose` turns this into the carry.
-/

noncomputable section

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- The scalars of `R` are central: `c • (e * u) = e * (c • u)`. -/
private lemma smul_mul_comm_P (c : ℂ) (e u : R) : c • (e * u) = e * (c • u) := by
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, Algebra.commutes c e, mul_assoc]

/-- Multiplication by `e ∈ R` distributes over a `ℂ`-linear combination of elements of `R`. -/
private lemma mul_sum_smul_P (e : R) (c : Fin 6 → ℂ) (w : Fin 6 → R) :
    e * (∑ j, c j • w j) = ∑ j, c j • (e * w j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (smul_mul_comm_P (c j) e (w j)).symm

/-- Expansion of the carry expression: pulling the left factors `e₁`, `e₂` inside the
`σ'(x)`-combination of the carries of `rowDiffP y`. -/
private lemma carry_expand (c : Fin 6 → ℂ) (e1 e2 u1 v1 u0 v0 y : R) (u v : Fin 6 → R) :
    e1 * (u1 - (∑ j, c j • u j) - u0 * y) + e2 * (v1 - (∑ j, c j • v j) - v0 * y)
      = (e1 * u1 + e2 * v1) - (∑ j, c j • (e1 * u j + e2 * v j))
        - (e1 * u0 + e2 * v0) * y := by
  have hsum : (∑ j, c j • (e1 * u j + e2 * v j))
      = e1 * (∑ j, c j • u j) + e2 * (∑ j, c j • v j) := by
    simp only [smul_add, Finset.sum_add_distrib]
    rw [← mul_sum_smul_P, ← mul_sum_smul_P]
  rw [hsum, add_mul]
  simp only [mul_sub, mul_assoc]
  abel

/-- Decomposition of the carry expression as an exact `rowDiffP`-term plus a term built out of
the *errors* `rowDiffP z k - T z k`. -/
private lemma carry_decomp (c : Fin 6 → ℂ) (T1 T0 R1 R0 y : R) (Ty Ry : Fin 6 → R) :
    T1 - (∑ j, c j • Ty j) - T0 * y
      = (R1 - (∑ j, c j • Ry j) - R0 * y)
        + (-(R1 - T1) + (∑ j, c j • (Ry j - Ty j)) + (R0 - T0) * y) := by
  simp only [smul_sub, Finset.sum_sub_distrib, sub_mul]
  abel

/-- Every `rowDiffP x i ∈ 𝓘` has a decomposition along `(T-1)²` and `S(T-1)²` modulo the
collapse ideal `(z-1)R`. -/
private lemma exists_carryP (hred : ∀ (x : R) (i : Fin 6), rowDiffP x i ∈ idealI)
    (x : R) (i : Fin 6) :
    ∃ p : R × R, rowDiffP x i
      - ((R_T - 1) ^ 2 * p.1 + R_S * (R_T - 1) ^ 2 * p.2) ∈ augIdeal := by
  obtain ⟨A, B, C, hABC⟩ := mem_idealI_exists (hred x i)
  refine ⟨(A, B), ?_⟩
  have h : rowDiffP x i - ((R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B)
      = (Rneg - 1) * C := by
    rw [hABC]; abel
  rw [h]
  exact Rneg_sub_one_mul_mem C

/-- The carry of the second basis: `(N x i).1`, `(N x i).2` are the `(T-1)²`- and
`S(T-1)²`-components of `rowDiffP x i` modulo `(z-1)R`. -/
private noncomputable def carryP (hred : ∀ (x : R) (i : Fin 6), rowDiffP x i ∈ idealI)
    (x : R) (i : Fin 6) : R × R :=
  Classical.choose (exists_carryP hred x i)

/-- The defining property of `carryP`. -/
private lemma carryP_spec (hred : ∀ (x : R) (i : Fin 6), rowDiffP x i ∈ idealI)
    (x : R) (i : Fin 6) :
    rowDiffP x i - ((R_T - 1) ^ 2 * (carryP hred x i).1
      + R_S * (R_T - 1) ^ 2 * (carryP hred x i).2) ∈ augIdeal :=
  Classical.choose_spec (exists_carryP hred x i)

/-- **The carry cocycle.**  Any `N` whose `(T-1)²`/`S(T-1)²`-component reproduces `rowDiffP`
modulo `(z-1)R` is automatically a cocycle modulo `(z-1)R` for both components. -/
private lemma cocycle_general (N : R → Fin 6 → R × R)
    (hN : ∀ (x : R) (i : Fin 6),
      rowDiffP x i - ((R_T - 1) ^ 2 * (N x i).1
        + R_S * (R_T - 1) ^ 2 * (N x i).2) ∈ augIdeal)
    (x y : R) (i : Fin 6) :
    (R_T - 1) ^ 2 * ((N (x * y) i).1 - ∑ j, sigmaP x i j • (N y j).1 - (N x i).1 * y)
      + R_S * (R_T - 1) ^ 2
          * ((N (x * y) i).2 - ∑ j, sigmaP x i j • (N y j).2 - (N x i).2 * y)
      ∈ augIdeal := by
  set e2 : R := R_S * (R_T - 1) ^ 2 with he2
  set e1 : R := (R_T - 1) ^ 2 with he1
  have hA : e1 * ((N (x * y) i).1 - ∑ j, sigmaP x i j • (N y j).1 - (N x i).1 * y)
      + e2 * ((N (x * y) i).2 - ∑ j, sigmaP x i j • (N y j).2 - (N x i).2 * y)
      = (e1 * (N (x * y) i).1 + e2 * (N (x * y) i).2)
        - (∑ j, sigmaP x i j • (e1 * (N y j).1 + e2 * (N y j).2))
        - (e1 * (N x i).1 + e2 * (N x i).2) * y :=
    carry_expand (fun j => sigmaP x i j) e1 e2 ((N (x * y) i).1) ((N (x * y) i).2)
      ((N x i).1) ((N x i).2) y (fun j => (N y j).1) (fun j => (N y j).2)
  rw [hA]
  have hdec : (e1 * (N (x * y) i).1 + e2 * (N (x * y) i).2)
        - (∑ j, sigmaP x i j • (e1 * (N y j).1 + e2 * (N y j).2))
        - (e1 * (N x i).1 + e2 * (N x i).2) * y
      = (rowDiffP (x * y) i - (∑ j, sigmaP x i j • rowDiffP y j) - rowDiffP x i * y)
        + (-(rowDiffP (x * y) i - (e1 * (N (x * y) i).1 + e2 * (N (x * y) i).2))
           + (∑ j, sigmaP x i j • (rowDiffP y j - (e1 * (N y j).1 + e2 * (N y j).2)))
           + (rowDiffP x i - (e1 * (N x i).1 + e2 * (N x i).2)) * y) :=
    carry_decomp (fun j => sigmaP x i j)
      (e1 * (N (x * y) i).1 + e2 * (N (x * y) i).2)
      (e1 * (N x i).1 + e2 * (N x i).2) (rowDiffP (x * y) i) (rowDiffP x i) y
      (fun j => e1 * (N y j).1 + e2 * (N y j).2) (fun j => rowDiffP y j)
  rw [hdec]
  have h0 : rowDiffP (x * y) i - (∑ j, sigmaP x i j • rowDiffP y j) - rowDiffP x i * y = 0 := by
    rw [rowDiffP_mul x y i]; abel
  rw [h0, zero_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.neg_mem _ (hN (x * y) i)
  · exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hN y j))
  · exact mul_mem_augIdeal_right (hN x i) y

theorem carryP_exists {k : ℤ}
    (hred : ∀ (x : Work.Kernels.R) (i : Fin 6), rowDiffP x i ∈ Work.Residues.idealI) :
    ∃ N : Work.Kernels.R → Fin 6 → Work.Kernels.R × Work.Kernels.R,
      (∀ (x : Work.Kernels.R) (i : Fin 6),
        rowDiffP x i - ((Work.Kernels.R_T - 1) ^ 2 * (N x i).1
          + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * (N x i).2) ∈ Work.Residues.augIdeal) ∧
      (∀ (x y : Work.Kernels.R) (i : Fin 6),
        (N (x * y) i).1 - ∑ j, sigmaP x i j • (N y j).1 - (N x i).1 * y
          ∈ Work.Residues.augIdeal) ∧
      (∀ (x y : Work.Kernels.R) (i : Fin 6),
        (N (x * y) i).2 - ∑ j, sigmaP x i j • (N y j).2 - (N x i).2 * y
          ∈ Work.Residues.augIdeal) := by
  refine ⟨carryP hred, carryP_spec hred, ?_, ?_⟩
  · intro x y i
    exact (idealI_direct_augIdeal (cocycle_general (carryP hred) (carryP_spec hred) x y i)).1
  · intro x y i
    exact (idealI_direct_augIdeal (cocycle_general (carryP hred) (carryP_spec hred) x y i)).2

end Work.Asymptotics
