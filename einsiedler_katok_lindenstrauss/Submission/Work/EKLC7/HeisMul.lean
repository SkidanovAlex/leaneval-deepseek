import Mathlib
import Submission.Work.EKLC7.Defs

/-!
# C7: the Heisenberg multiplication law

`Work.EKLC7.heis hij hjk hik p q r = u_ij(p) · u_jk(r) · u_ik(q - p r)` is the element
`1 + p E_ij + q E_ik + r E_jk` of `SL₃(ℝ)` (`toMat_heis` below).  This file establishes, for
distinct indices `i, j, k`, the complete algebraic API of that parametrisation:

* `toMat_heis`   — the matrix `1 + p E_ij + q E_ik + r E_jk`;
* `heis_mul`     — `(p,q,r)·(p',q',r') = (p+p', q+q'+p r', r+r')`;
* `heis_inv`     — `(p,q,r)⁻¹ = (-p, p r - q, -r)`;
* `pcoord_heis`, `qcoord_heis`, `rcoord_heis` — the three matrix-entry coordinates.

All of it is a direct `3 × 3` matrix computation: for distinct `i, j, k` the only non-vanishing
product among `E_ij, E_ik, E_jk` is `E_ij E_jk = E_ik` (`Matrix.single_mul_single_same`), every
other product of two of them is `0` (`Matrix.single_mul_single_of_ne`), because the middle index
never matches.
-/

set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-- The underlying matrix of the Heisenberg parametrisation: `heis p q r = 1 + p E_ij + q E_ik +
r E_jk`. -/
theorem toMat_heis {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : ℝ) :
    toMat (heis hij hjk hik p q r)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j p + Matrix.single i k q
          + Matrix.single j k r := by
  rw [heis, toMat_mul, toMat_mul, Work.EKLContract.Lemmas.horoUij_toMat hij,
    Work.EKLContract.Lemmas.horoUij_toMat hjk, Work.EKLContract.Lemmas.horoUij_toMat hik]
  have e1 : Matrix.single i j p * Matrix.single i k (q - p * r) = 0 :=
    Matrix.single_mul_single_of_ne p i j i hij.symm _
  have e2 : Matrix.single j k r * Matrix.single i k (q - p * r) = 0 :=
    Matrix.single_mul_single_of_ne r j k i hik.symm _
  have e3 : Matrix.single i k (p * r) * Matrix.single i k (q - p * r) = 0 :=
    Matrix.single_mul_single_of_ne (p * r) i k i hik.symm _
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_same, e1, e2, e3]
  rw [show Matrix.single i k q
        = Matrix.single i k (p * r) + Matrix.single i k (q - p * r) by
      rw [← Matrix.single_add]; congr 1; ring]
  abel

/-- The multiplication law of the Heisenberg parametrisation:
`(p,q,r)·(p',q',r') = (p+p', q+q'+p r', r+r')`. -/
theorem heis_mul {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r p' q' r' : ℝ) :
    heis hij hjk hik p q r * heis hij hjk hik p' q' r'
      = heis hij hjk hik (p + p') (q + q' + p * r') (r + r') := by
  apply toMat_injective
  rw [toMat_mul, toMat_heis hij hjk hik p q r, toMat_heis hij hjk hik p' q' r',
    toMat_heis hij hjk hik (p + p') (q + q' + p * r') (r + r')]
  have e1 : Matrix.single i j p * Matrix.single i j p' = 0 :=
    Matrix.single_mul_single_of_ne p i j i hij.symm _
  have e2 : Matrix.single i j p * Matrix.single i k q' = 0 :=
    Matrix.single_mul_single_of_ne p i j i hij.symm _
  have e3 : Matrix.single i k q * Matrix.single i j p' = 0 :=
    Matrix.single_mul_single_of_ne q i k i hik.symm _
  have e4 : Matrix.single i k q * Matrix.single i k q' = 0 :=
    Matrix.single_mul_single_of_ne q i k i hik.symm _
  have e5 : Matrix.single i k q * Matrix.single j k r' = 0 :=
    Matrix.single_mul_single_of_ne q i k j hjk.symm _
  have e6 : Matrix.single j k r * Matrix.single i j p' = 0 :=
    Matrix.single_mul_single_of_ne r j k i hik.symm _
  have e7 : Matrix.single j k r * Matrix.single i k q' = 0 :=
    Matrix.single_mul_single_of_ne r j k i hik.symm _
  have e8 : Matrix.single j k r * Matrix.single j k r' = 0 :=
    Matrix.single_mul_single_of_ne r j k j hjk.symm _
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_same, Matrix.single_add, e1, e2, e3, e4, e5, e6, e7, e8]
  abel

/-- The inverse in the Heisenberg parametrisation: `(p,q,r)⁻¹ = (-p, p r - q, -r)`
(equivalently `(1 + N)⁻¹ = 1 - N + N²` with `N = p E_ij + q E_ik + r E_jk`, `N² = p r E_ik`). -/
theorem heis_inv {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : ℝ) :
    (heis hij hjk hik p q r)⁻¹ = heis hij hjk hik (-p) (p * r - q) (-r) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [heis_mul hij hjk hik p q r (-p) (p * r - q) (-r)]
  have h1 : p + -p = 0 := by ring
  have h2 : q + (p * r - q) + p * (-r) = 0 := by ring
  have h3 : r + -r = 0 := by ring
  rw [h1, h2, h3, heis_zero]

/-- The `(i,j)`-entry of `heis p q r` is `p`. -/
theorem pcoord_heis {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r : ℝ) : pcoord i j (heis hij hjk hik p q r) = p := by
  rw [show pcoord i j (heis hij hjk hik p q r)
        = toMat (heis hij hjk hik p q r) i j from rfl]
  rw [toMat_heis hij hjk hik]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [hij, hjk, hik, hij.symm, hjk.symm, hik.symm]

/-- The `(i,k)`-entry of `heis p q r` is `q`. -/
theorem qcoord_heis {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r : ℝ) : qcoord i k (heis hij hjk hik p q r) = q := by
  rw [show qcoord i k (heis hij hjk hik p q r)
        = toMat (heis hij hjk hik p q r) i k from rfl]
  rw [toMat_heis hij hjk hik]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [hij, hjk, hik, hij.symm, hjk.symm, hik.symm]

/-- The `(j,k)`-entry of `heis p q r` is `r`. -/
theorem rcoord_heis {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r : ℝ) : rcoord j k (heis hij hjk hik p q r) = r := by
  rw [show rcoord j k (heis hij hjk hik p q r)
        = toMat (heis hij hjk hik p q r) j k from rfl]
  rw [toMat_heis hij hjk hik]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [hij, hjk, hik, hij.symm, hjk.symm, hik.symm]

/-- The Heisenberg commutator relation `[u_ij(p), u_jk(r)] = u_ik(p r)`: the element
`u_ij(p) u_jk(r)` may be swapped across at the price of the central correction `u_ik(p r)`.

(EKL/Pisa use this with `i, j, k` the three distinct indices of a Heisenberg triple; it is the
group-level content of the "two orders" comparison `U_ij · U_jk · U_ik` vs `U_jk · U_ij · U_ik`
of the leafwise product formulae.) -/
theorem uij_commutator {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p r : ℝ) :
    uij hij p * uij hjk r * (uij hij p)⁻¹ * (uij hjk r)⁻¹ = uij hik (p * r) := by
  have h1 : heis hij hjk hik p 0 0 * heis hij hjk hik 0 0 r
      = heis hij hjk hik p (p * r) r := by
    rw [heis_mul hij hjk hik p 0 0 0 0 r]
    have e1 : p + 0 = p := by ring
    have e2 : 0 + 0 + p * r = p * r := by ring
    have e3 : 0 + r = r := by ring
    rw [e1, e2, e3]
  have h2 : heis hij hjk hik p (p * r) r * heis hij hjk hik (-p) 0 0
      = heis hij hjk hik 0 (p * r) r := by
    rw [heis_mul hij hjk hik p (p * r) r (-p) 0 0]
    have e1 : p + -p = (0 : ℝ) := by ring
    have e2 : p * r + 0 + p * 0 = p * r := by ring
    have e3 : r + 0 = r := by ring
    rw [e1, e2, e3]
  have h3 : heis hij hjk hik 0 (p * r) r * heis hij hjk hik 0 0 (-r)
      = heis hij hjk hik 0 (p * r) 0 := by
    rw [heis_mul hij hjk hik 0 (p * r) r 0 0 (-r)]
    have e1 : 0 + 0 = (0 : ℝ) := by ring
    have e2 : p * r + 0 + 0 * (-r) = p * r := by ring
    have e3 : r + -r = (0 : ℝ) := by ring
    rw [e1, e2, e3]
  rw [← heis_uij hij hjk hik p, ← heis_ujk hij hjk hik r, ← heis_uik hij hjk hik (p * r),
    heis_inv hij hjk hik p 0 0, heis_inv hij hjk hik 0 0 r]
  have e1 : p * 0 - 0 = (0 : ℝ) := by ring
  have e2 : -0 = (0 : ℝ) := by ring
  have e3 : 0 * r - 0 = (0 : ℝ) := by ring
  rw [e1, e2, e3, h1, h2, h3]

/-- The Heisenberg parametrisation is a bijection onto its image: the coordinates of
`heis p q r` are `p`, `q`, `r`.  (Convenience wrapper used by C7.) -/
theorem heis_coords {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : ℝ) :
    pcoord i j (heis hij hjk hik p q r) = p ∧ qcoord i k (heis hij hjk hik p q r) = q
      ∧ rcoord j k (heis hij hjk hik p q r) = r :=
  ⟨pcoord_heis hij hjk hik p q r, qcoord_heis hij hjk hik p q r, rcoord_heis hij hjk hik p q r⟩

/-- **The Heisenberg multiplication law** (C7, `Work.EKLC7.HeisMul`).  Bundles the group law,
the identity, the inverse, the matrix form and the three coordinates of `heis p q r`
(`(p,q,r)(p',q',r') = (p+p', q+q'+p r', r+r')`), all for a triple `i, j, k` of *distinct*
indices of `Fin 3`. -/
theorem HeisMul : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r p' q' r' : ℝ),
    (Work.EKLC7.heis hij hjk hik p q r * Work.EKLC7.heis hij hjk hik p' q' r'
        = Work.EKLC7.heis hij hjk hik (p + p') (q + q' + p * r') (r + r'))
      ∧ (Work.EKLC7.heis hij hjk hik 0 0 0 = 1)
      ∧ ((Work.EKLC7.heis hij hjk hik p q r)⁻¹
          = Work.EKLC7.heis hij hjk hik (-p) (p * r - q) (-r))
      ∧ (Work.EKLContract.toMat (Work.EKLC7.heis hij hjk hik p q r)
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j p + Matrix.single i k q
            + Matrix.single j k r)
      ∧ (Work.EKLC7.pcoord i j (Work.EKLC7.heis hij hjk hik p q r) = p)
      ∧ (Work.EKLC7.qcoord i k (Work.EKLC7.heis hij hjk hik p q r) = q)
      ∧ (Work.EKLC7.rcoord j k (Work.EKLC7.heis hij hjk hik p q r) = r) := by
  intro i j k hij hjk hik p q r p' q' r'
  exact ⟨heis_mul hij hjk hik p q r p' q' r', heis_zero hij hjk hik,
    heis_inv hij hjk hik p q r, toMat_heis hij hjk hik p q r,
    pcoord_heis hij hjk hik p q r, qcoord_heis hij hjk hik p q r,
    rcoord_heis hij hjk hik p q r⟩

end Work.EKLC7
