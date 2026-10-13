/-
  WilE4 / CAD — constancy of the degree of the gcd, from the *principal subresultant* data.

  `gcd_spec_natDegree_const_on_C` (`gcd_spec_natDegree_const_on_C.lean`) proves the same conclusion
  from the hypothesis that the signs of *all* Sylvester minors are constant on `C`; that hypothesis
  is uninstantiable from a polynomial-size projection (the minors are exponentially many — see
  `NOTES.md` §2quater).  This file proves the conclusion from the *polynomial-size* hypothesis
  `PscSignConst P C` instead, i.e. the sign-constancy of the principal subresultant coefficients
  `psc f g a b r = det (pscMat f g a b r)` (`Proj.lean`).

  The mathematical input is the classical subresultant theorem, in the two halves isolated in
  `psc_eq_zero_of_lt_gcd` and `psc_gcd_natDegree_ne_zero`: for nonzero `F G : ℝ[X]`, `deg (gcd F G)`
  is the *least* index `i` with `psc F G F.natDegree G.natDegree i ≠ 0`.  Since sign-constancy on
  `C` makes the vanishing pattern of every one of those coefficients constant on `C`, so is the
  degree of the gcd.

  This is the lemma that the type constancy of the CAD consumes, in place of
  `gcd_spec_natDegree_const_on_C`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.psc_eq_zero_of_lt_gcd
import Submission.Work.WilE4.CAD.psc_gcd_natDegree_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

variable {m k : ℕ}

/-- The two halves of the classical subresultant theorem, packaged: if the *vanishing pattern* of
the principal subresultant coefficients of `F, G` agrees with that of `F', G'` (at the respective
degrees), then `deg (gcd F G) ≤ deg (gcd F' G')`.

Indeed `psc_eq_zero_of_lt_gcd` shows that `psc F G (deg F) (deg G) d'` vanishes for
`d' = deg (gcd F' G') < deg (gcd F G)`, while `psc_gcd_natDegree_ne_zero` shows that
`psc F' G' (deg F') (deg G') d'` does not; the assumed agreement of the vanishing patterns
contradicts that. -/
theorem gcd_natDegree_le_of_psc {F G F' G' : Polynomial ℝ} (hF : F ≠ 0)
    (hG : G ≠ 0) (hF' : F' ≠ 0) (hG' : G' ≠ 0)
    (hiff : ∀ r : ℕ, r ≤ min F.natDegree G.natDegree →
      (psc F G F.natDegree G.natDegree r = 0 ↔ psc F' G' F'.natDegree G'.natDegree r = 0)) :
    (gcd F G).natDegree ≤ (gcd F' G').natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  have hle1 : (gcd F G).natDegree ≤ F.natDegree :=
    Polynomial.natDegree_le_of_dvd (gcd_dvd_left F G) hF
  have hle2 : (gcd F G).natDegree ≤ G.natDegree :=
    Polynomial.natDegree_le_of_dvd (gcd_dvd_right F G) hG
  have hd'le : (gcd F' G').natDegree ≤ min F.natDegree G.natDegree :=
    le_min (by omega) (by omega)
  have hz : psc F G F.natDegree G.natDegree ((gcd F' G').natDegree) = 0 :=
    psc_eq_zero_of_lt_gcd hF hG hcon
  have hnz : psc F' G' F'.natDegree G'.natDegree ((gcd F' G').natDegree) ≠ 0 :=
    psc_gcd_natDegree_ne_zero hF' hG'
  exact hnz ((hiff _ hd'le).mp hz)

/-- **Constancy of the degree of the gcd from the subresultant data.**  If the signs of all
coefficients and of all principal subresultant coefficients of the specialisations of a family `P`
are constant on a set `C`, then the degree of the gcd of two specialisations is constant on `C`.

(The companion `gcd_spec_natDegree_const_on_C` proves the same from the *all-minors* hypothesis,
which is not instantiable from polynomial-size data; this one is, because `PscSignConst` is exactly
what the sign condition of the projection data `pscFam H ⊆ projData H` provides.) -/
theorem gcd_spec_natDegree_const_on_C_psc {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hpsc : PscSignConst P C)
    (i j : Fin k) (x x' : Fin m → ℝ) (hx : x ∈ C) (hx' : x' ∈ C) :
    (gcd (Work.WilE4.spec (P i) x) (Work.WilE4.spec (P j) x)).natDegree
      = (gcd (Work.WilE4.spec (P i) x') (Work.WilE4.spec (P j) x')).natDegree := by
  -- the `natDegree` of every specialisation is constant on `C`
  have hnd : ∀ i : Fin k, (spec (P i) x).natDegree = (spec (P i) x').natDegree :=
    fun i => natDegree_spec_const
      (fun i j hj y hy y' hy' => hcoeff i j (le_trans hj (hD i)) y hy y' hy') hx hx'
  -- a coefficient of index `≤ D` vanishes at `x` exactly when it vanishes at `x'`
  have hzero : ∀ i : Fin k, ∀ j : ℕ, j ≤ D →
      ((spec (P i) x).coeff j = 0 ↔ (spec (P i) x').coeff j = 0) := by
    intro i j hj
    rw [← sign_eq_zero_iff, hcoeff i j hj x hx x' hx', sign_eq_zero_iff]
  have hdeg : ∀ i : Fin k, (spec (P i) x).natDegree ≤ D :=
    fun i => (natDegree_spec_le (P i) x).trans (hD i)
  have hdeg' : ∀ i : Fin k, (spec (P i) x').natDegree ≤ D :=
    fun i => (natDegree_spec_le (P i) x').trans (hD i)
  -- hence a member vanishes at `x` exactly when it vanishes at `x'`
  have hz : ∀ i : Fin k, ((spec (P i) x) = 0 ↔ (spec (P i) x') = 0) :=
    fun i => gsc_eq_zero_iff_of_coeff_eq_zero_iff (hdeg i) (hdeg' i) (hzero i)
  by_cases hFi : (spec (P i) x) = 0
  · -- `spec (P i)` vanishes identically on `C`: both sides equal `natDegree (spec (P j))`
    have hFi' : (spec (P i) x') = 0 := (hz i).mp hFi
    rw [hFi, hFi', gsc_gcd_zero_left, gsc_gcd_zero_left]
    exact hnd j
  · have hFi' : (spec (P i) x') ≠ 0 := fun h => hFi ((hz i).mpr h)
    by_cases hGj : (spec (P j) x) = 0
    · have hGj' : (spec (P j) x') = 0 := (hz j).mp hGj
      rw [hGj, hGj', gsc_gcd_zero_right, gsc_gcd_zero_right]
      exact hnd i
    · -- both members are nonzero: the vanishing pattern of the subresultant coefficients
      -- determines the degree of the gcd, and it is constant on `C`
      have hGj' : (spec (P j) x') ≠ 0 := fun h => hGj ((hz j).mpr h)
      have hsign : ∀ r : ℕ, r ≤ min (spec (P i) x).natDegree (spec (P j) x).natDegree →
          (psc (spec (P i) x) (spec (P j) x) (spec (P i) x).natDegree
              (spec (P j) x).natDegree r = 0 ↔
            psc (spec (P i) x') (spec (P j) x') (spec (P i) x').natDegree
              (spec (P j) x').natDegree r = 0) := by
        intro r hr
        have h1 := hpsc i j ((spec (P i) x).natDegree) ((spec (P j) x).natDegree)
          (natDegree_spec_le (P i) x) (natDegree_spec_le (P j) x) r hr x hx x' hx'
        rw [← hnd i, ← hnd j]
        exact gsc_eq_zero_iff_of_sign_eq h1
      have hle1 : (gcd (spec (P i) x) (spec (P j) x)).natDegree
          ≤ (gcd (spec (P i) x') (spec (P j) x')).natDegree :=
        gcd_natDegree_le_of_psc hFi hGj hFi' hGj' hsign
      have hle2 : (gcd (spec (P i) x') (spec (P j) x')).natDegree
          ≤ (gcd (spec (P i) x) (spec (P j) x)).natDegree := by
        refine gcd_natDegree_le_of_psc hFi' hGj' hFi hGj ?_
        intro r hr
        refine (hsign r ?_).symm
        rw [hnd i, hnd j]
        exact hr
      exact le_antisymm hle1 hle2

end Work.WilE4.CAD
