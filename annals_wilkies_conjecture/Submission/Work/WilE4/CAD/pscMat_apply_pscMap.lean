import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.psc_entry
import Submission.Work.WilE4.CAD.PscMapDefs

namespace Work.WilE4.CAD

/-- **`pscMat` is the matrix of `pscMap` in the standard monomial bases.**

Let `m`, `n` be the formal degrees (`f.natDegree ≤ m`, `g.natDegree ≤ n`) and let
`hd : (n - i) + (m - i) = m + n - 2 * i`, so that the index types of the two blocks of columns of
the principal subresultant matrix can be identified with `Fin (m + n - 2 * i)`.  Then the column
`c` of `pscMat f g m n i` (identified through `finCongr hd` with a `Fin ((n - i) + (m - i))`) is
the value of `pscMap f g m n i` at the `c`-th element of the standard basis
`Polynomial.degreeLT.basisProd ℝ (n - i) (m - i)` of `ℝ[X]_{< n - i} × ℝ[X]_{< m - i}` (that basis
is `(X ^ c, 0)` on the first block and `(0, X ^ j)` on the second).

The ingredients are already available: `Work.WilE4.CAD.pscMat_apply` (in
`Submission.Work.WilE4.CAD.psc_entry`) gives the entries, and `pscMap_apply` (in
`Submission.Work.WilE4.CAD.PscMapDefs`) gives the values of `pscMap` on the basis, together with
`Polynomial.degreeLT.basisProd_castAdd`, `Polynomial.degreeLT.basisProd_natAdd`,
`Polynomial.degreeLT.basis_val` and `finCongr_apply_coe`.  The only `Fin` bookkeeping is that a
`c : Fin ((n - i) + (m - i))` with `(c : ℕ) < n - i` is `Fin.castAdd (m - i) ⟨c, ·⟩`, and otherwise
`Fin.natAdd (n - i) ⟨(c : ℕ) - (n - i), ·⟩`. -/
theorem pscMat_apply_pscMap {f g : Polynomial ℝ} {m n i : ℕ} (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (hd : (n - i) + (m - i) = m + n - 2 * i)
    (r : Fin (m + n - 2 * i)) (c : Fin ((n - i) + (m - i))) :
    Work.WilE4.CAD.pscMat f g m n i r (finCongr hd c)
      = Work.WilE4.CAD.pscMap f g m n i
          (Polynomial.degreeLT.basisProd ℝ (n - i) (m - i) c) r := by
  rw [pscMat_apply f g hf hg r (finCongr hd c), pscMap_apply, finCongr_apply_coe]
  by_cases hc : (c : ℕ) < n - i
  · have hcc : c = (⟨(c : ℕ), hc⟩ : Fin (n - i)).castAdd (m - i) := by
      ext
      simp
    rw [ite_eq_left hc, hcc, Polynomial.degreeLT.basisProd_castAdd,
      Polynomial.degreeLT.basis_val]
    simp
  · have hlt : (c : ℕ) - (n - i) < m - i := by
      have := c.isLt
      omega
    have hcc : c = (⟨(c : ℕ) - (n - i), hlt⟩ : Fin (m - i)).natAdd (n - i) := by
      ext
      simp
      omega
    rw [ite_eq_right hc, hcc, Polynomial.degreeLT.basisProd_natAdd,
      Polynomial.degreeLT.basis_val]
    simp

end Work.WilE4.CAD
