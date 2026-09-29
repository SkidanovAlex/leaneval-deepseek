import Mathlib
import Submission.Work.ResMath.resE_defs

/-!
# `Work.ResMath.Nmat_apply`

The entrywise description of the matrix `Nmat = rowSel · resTmat · diagD` of
`Submission/HvdH/Interfaces.lean`: for `0 < s < t` and `ℓ j : Fin s`,

`(Nmat) ℓ j = (Σ_{q∈ℤ} e^{-πα²(tq + t(j-ℓ)/s + β_ℓ)²}) · e^{πα²β_j²}`.

This is the "big step" form of the lattice sum, obtained from the definition
`resTmat k j = Σ_q e^{-πα²t²(k/t - j/s - q)²}` by the change of variable
`k = [tℓ/s] = tℓ/s - β_ℓ`, which makes the two quadratic forms negatives of each other.
-/

namespace Work.ResMath

open HvdH

/-- Real-arithmetic core of `Nmat_apply`: the two quadratic forms that appear in the two
descriptions of an entry of `Nmat` agree up to sign. -/
lemma exp_arg_sq_eq (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ j : Fin s) (q : ℤ) (r : ℝ)
    (hr : r = (t : ℝ) * (ℓ : ℝ) / (s : ℝ) - HvdH.betaR s t ℓ) :
    (t : ℝ) ^ 2 * (r / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2
      = ((t : ℝ) * (q : ℝ) + (t : ℝ) * (((j : ℤ) : ℝ) - ((ℓ : ℤ) : ℝ)) / (s : ℝ)
          + betaI s t (ℓ : ℤ)) ^ 2 := by
  subst hr
  rw [betaI_eq_betaR]
  have ht : (0 : ℝ) < t := by exact_mod_cast (lt_trans hs hst)
  have hcast : (((j : ℤ) : ℝ) - ((ℓ : ℤ) : ℝ)) = (j : ℝ) - (ℓ : ℝ) := by push_cast; ring
  rw [hcast]
  field_simp
  ring

theorem Nmat_apply (s t α : ℕ) (hs : 0 < s) (hst : s < t) (ℓ j : Fin s) :
    HvdH.Nmat s t α ℓ j
      = (∑' q : ℤ, (Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
            ((t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ)
              + betaI s t (ℓ : ℤ)) ^ 2)) : ℂ))
        * (Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t j) ^ 2) : ℂ) := by
  obtain ⟨hR0, hRt⟩ := rndI_mem s t hs hst ℓ
  have htoNat : (((rndI s t ℓ).toNat : ℤ)) = rndI s t ℓ := Int.toNat_of_nonneg hR0
  let k : Fin t := ⟨(rndI s t ℓ).toNat, by omega⟩
  have hkZ : (k : ℤ) = rndI s t ℓ := htoNat
  -- the real value of the selected index `k`
  have hkR : (k : ℝ) = (t : ℝ) * (ℓ : ℝ) / (s : ℝ) - HvdH.betaR s t ℓ := by
    have h1 : (k : ℝ) = ((rndI s t ℓ : ℤ) : ℝ) := by
      show (((rndI s t ℓ).toNat : ℕ) : ℝ) = ((rndI s t ℓ : ℤ) : ℝ)
      rw [← Int.cast_natCast, htoNat]
    rw [h1, rndI, HvdH.betaR]
    ring
  -- the `diagD` factor is picked out at the diagonal entry `j`
  have hN : HvdH.Nmat s t α ℓ j
      = (∑ i : Fin t, HvdH.rowSel s t ℓ i * HvdH.resTmat s t α i j)
        * (Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t j) ^ 2) : ℂ) := by
    rw [HvdH.Nmat]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [HvdH.diagD, Matrix.diagonal_apply_eq]
    · intro b _ hb
      rw [HvdH.diagD, Matrix.diagonal_apply]
      simp [hb]
  -- the `rowSel` factor picks out the row `k` of `resTmat`
  have hsum : (∑ i : Fin t, HvdH.rowSel s t ℓ i * HvdH.resTmat s t α i j)
      = HvdH.resTmat s t α k j := by
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · rw [show HvdH.rowSel s t ℓ k
            = (if (k : ℤ) = rndI s t ℓ then (1 : ℂ) else 0) from rfl]
      simp [hkZ]
    · intro b _ hb
      have hbR : ¬ ((b : ℤ) = rndI s t ℓ) := by
        intro h
        exact hb (Fin.ext (by have hbk : (b : ℤ) = (k : ℤ) := h.trans hkZ.symm
                              omega))
      rw [show HvdH.rowSel s t ℓ b
            = (if (b : ℤ) = rndI s t ℓ then (1 : ℂ) else 0) from rfl]
      simp [hbR]
  -- the lattice sum of `resTmat`, rewritten in the paper's normalisation
  have hres : HvdH.resTmat s t α k j
      = (∑' q : ℤ, (Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
            ((t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ)
              + betaI s t (ℓ : ℤ)) ^ 2)) : ℂ)) := by
    rw [show HvdH.resTmat s t α k j
          = ((∑' q : ℤ, Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
              ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)) : ℝ) from rfl]
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun q => ?_
    rw [Complex.ofReal_inj]
    congr 1
    rw [← exp_arg_sq_eq s t hs hst ℓ j q ((k : ℕ) : ℝ) hkR]
    ring
  rw [hN, hsum, hres]

end Work.ResMath
