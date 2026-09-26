/-
# The carries of a word of atoms: the recursion and its equation

The carries of an element of `R = ℂ[SL(2,ℤ)]` are triples `(a,b,c)` with
`(T-1)²a + S(T-1)²b + (z-1)c = rowDiff x i`.  They are generated from the atom data by the
cocycle law `rowDiff (x*y) i = ∑_j σ(x)_{ij} • rowDiff y j + rowDiff x i * y`, which reads on the
level of carries as

  `carry (μ :: L) i = ∑_j σ(μ)_{ij} • carry L j + carryAt μ i * of (L.prod)`.

This file sets up that recursion for words in the four atoms and proves that the resulting triples
satisfy the defining equation, *given* the atom data.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Asymptotics.AtomCarries

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The atom data: the carries of `rowDiff (of μ) i` for the four atoms `μ` and all rows `i`. -/
def AtomCarry (carry : SL(2,ℤ) → Fin 6 → R × R × R) : Prop :=
  ∀ μ ∈ atomSet, ∀ i : Fin 6,
    carryComb (carry μ i).1 (carry μ i).2.1 (carry μ i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ SL(2,ℤ) μ) i

lemma carryComb_zero : carryComb (0 : R) (0 : R) (0 : R) = 0 := by
  simp [carryComb]


lemma carryComb_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → R × R × R) :
    carryComb (∑ i ∈ s, c i • (f i).1) (∑ i ∈ s, c i • (f i).2.1) (∑ i ∈ s, c i • (f i).2.2)
      = ∑ i ∈ s, c i • carryComb (f i).1 (f i).2.1 (f i).2.2 := by
  simp only [carryComb]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, smul_add, smul_add]

lemma carryComb_mul_mono (a b c : R) (γ : SL(2,ℤ)) :
    carryComb (a * MonoidAlgebra.of ℂ SL(2,ℤ) γ) (b * MonoidAlgebra.of ℂ SL(2,ℤ) γ)
        (c * MonoidAlgebra.of ℂ SL(2,ℤ) γ)
      = carryComb a b c * MonoidAlgebra.of ℂ SL(2,ℤ) γ := by
  simp only [carryComb]
  noncomm_ring

/-- The carries of a word of atoms, defined by the cocycle recursion from the atom carries. -/
noncomputable def wordCarry (carry : SL(2,ℤ) → Fin 6 → R × R × R) :
    List SL(2,ℤ) → Fin 6 → R × R × R
  | [], _ => (0, 0, 0)
  | μ :: L, i =>
      (∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
            • (wordCarry carry L j).1
          + (carry μ i).1 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod,
       ∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
            • (wordCarry carry L j).2.1
          + (carry μ i).2.1 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod,
       ∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
            • (wordCarry carry L j).2.2
          + (carry μ i).2.2 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod)

/-- **The recursion satisfies the defining equation**, provided the atom carries do. -/
theorem wordCarry_spec (carry : SL(2,ℤ) → Fin 6 → R × R × R) (h : AtomCarry carry) :
    ∀ L : List SL(2,ℤ), (∀ μ ∈ L, μ ∈ atomSet) → ∀ i : Fin 6,
      carryComb (wordCarry carry L i).1 (wordCarry carry L i).2.1 (wordCarry carry L i).2.2
        = Work.Residues.rowDiff (MonoidAlgebra.of ℂ SL(2,ℤ) L.prod) i := by
  intro L
  induction L with
  | nil =>
    intro _ i
    rw [show MonoidAlgebra.of ℂ SL(2,ℤ) ([] : List SL(2,ℤ)).prod = (1 : R) from map_one _,
      Work.Residues.rowDiff_one]
    simp [wordCarry, carryComb]
  | cons μ L ih =>
    intro hL i
    have hμ : μ ∈ atomSet := hL μ (by simp)
    have hL' : ∀ ν ∈ L, ν ∈ atomSet := fun ν hν => hL ν (List.mem_cons_of_mem μ hν)
    have hspec := ih hL'
    show carryComb _ _ _ = _
    rw [wordCarry]
    have key : carryComb
        (∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • (wordCarry carry L j).1
            + (carry μ i).1 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod)
        (∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • (wordCarry carry L j).2.1
            + (carry μ i).2.1 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod)
        (∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • (wordCarry carry L j).2.2
            + (carry μ i).2.2 * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod)
        = ∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • carryComb (wordCarry carry L j).1 (wordCarry carry L j).2.1
                  (wordCarry carry L j).2.2
            + carryComb (carry μ i).1 (carry μ i).2.1 (carry μ i).2.2
              * MonoidAlgebra.of ℂ SL(2,ℤ) L.prod := by
      rw [carryComb_add, carryComb_sum_smul, carryComb_mul_mono]
    rw [key]
    have hstep : (∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • carryComb (wordCarry carry L j).1 (wordCarry carry L j).2.1
                  (wordCarry carry L j).2.2)
        = ∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) μ)) i j
              • Work.Residues.rowDiff (MonoidAlgebra.of ℂ SL(2,ℤ) L.prod) j :=
      Finset.sum_congr rfl fun j _ => by rw [hspec j]
    rw [hstep, h μ hμ i]
    rw [List.prod_cons, map_mul, Work.Residues.rowDiff_mul]

end Work.Asymptotics
