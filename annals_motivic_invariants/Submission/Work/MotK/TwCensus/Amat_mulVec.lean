import Mathlib
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

/-- The coefficient vector `c = (0, a, b, -b, -a)` of the Klein matrix
`M_{i j} = c_{j - i} · x_{i + j}` (`Work.MotK.kleinM`), written as a function
`Fin 5 → K`. -/
def kleinCoeff {K : Type} [Field K] (a b : K) : Fin 5 → K := ![0, a, b, -b, -a]

/-- **Closed form of the Klein matrix.**  The definition of `Work.MotK.kleinM` (five rows, each a
five-term vector) is the entrywise formula `M_{i j} = c_{j - i} · x_{i + j}` with
`c = (0, a, b, -b, -a)` (indices in `Fin 5`, i.e. mod `5`). -/
theorem kleinM_eq {K : Type} [Field K] (a b : K) (x : Fin 5 → K) (i j : Fin 5) :
    Work.MotK.kleinM a b x i j = kleinCoeff a b (j - i) * x (i + j) := by
  fin_cases i <;> fin_cases j <;>
    simp [Work.MotK.kleinM, Work.MotK.kleinM0, Work.MotK.kleinM1, Work.MotK.kleinM2,
      Work.MotK.kleinM3, Work.MotK.kleinM4, kleinCoeff]

/-- **The ruling system of the T-twisted quadro map is the twisted Klein matrix read along `c'`.**
Both sides describe the fibre of the twisted quadro map `kleinTwP` over `[c']` (see the discussion
of `kleinTwM` and `Amat` in `Submission/Work/MotK/TwCensus/STClass.lean`):

* `kleinTwM a b h y *ᵥ c'` is the linear system `∑_j h^{w(i,j)} c_{j-i} y_{i+j} c'_j = 0` in `y`;
* `Amat a b h c' *ᵥ y` is the same system with `y_l` as the coefficient of the `l`-th column of
  `Amat`, obtained by the relabelling `l = i + j`.

The proof expands `kleinM` into its closed form `kleinM_eq`, uses
`kleinM a b (Pi.single l 1) i (l - i) = c_{l - 2i}`, and reindexes the sum over `j ↦ j + i`. -/
theorem Amat_mulVec {K : Type} [Field K] (a b h : K) (y c' : Fin 5 → K) :
    Matrix.mulVec (Work.MotK.TwCensus.Amat a b h c') y
      = Matrix.mulVec (Work.MotK.TwCensus.kleinTwM a b h y) c' := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hRHS : ∑ j, Work.MotK.TwCensus.kleinTwM a b h y i j * c' j
      = ∑ j, h ^ Work.MotK.TwCensus.twW i j * kleinCoeff a b (j - i) * y (i + j) * c' j :=
    Finset.sum_congr rfl (fun j _ => by
      rw [Work.MotK.TwCensus.kleinTwM, kleinM_eq]; ring)
  have hLHS : ∑ l, Work.MotK.TwCensus.Amat a b h c' i l * y l
      = ∑ l, h ^ Work.MotK.TwCensus.twW i (l - i) * kleinCoeff a b ((l - i) - i)
          * c' (l - i) * y l :=
    Finset.sum_congr rfl (fun l _ => by
      rw [Work.MotK.TwCensus.Amat, kleinM_eq]
      have hii : i + (l - i) = l := by simp
      rw [hii, Pi.single_eq_same]
      ring)
  rw [hLHS, hRHS]
  rw [← Equiv.sum_comp (Equiv.addRight i)
        (fun l => h ^ Work.MotK.TwCensus.twW i (l - i) * kleinCoeff a b ((l - i) - i)
          * c' (l - i) * y l)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Equiv.coe_addRight]
  have h1 : j + i - i = j := by simp
  rw [h1]
  have hy : y (j + i) = y (i + j) := by rw [add_comm]
  rw [hy]
  first | refl_ring1 | ring

end Work.MotK.TwCensus
