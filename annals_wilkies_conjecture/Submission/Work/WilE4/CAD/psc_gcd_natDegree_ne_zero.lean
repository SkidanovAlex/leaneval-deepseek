import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.PscMapDefs
import Submission.Work.WilE4.CAD.psc_amul_add_bmul_eq_zero
import Submission.Work.WilE4.CAD.pscMat_apply_pscMap

set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE4.CAD

open Polynomial Matrix

/-- **Nonvanishing of the principal subresultant coefficient at the degree of the gcd.**

This is the companion of `psc_eq_zero_of_lt_gcd`: together they say that
`deg (gcd f g)` is the *least* `i` with `psc f g (f.natDegree) (g.natDegree) i ≠ 0`.

MATHEMATICAL CONTENT.  As in `psc_eq_zero_of_lt_gcd`, the matrix `pscMat f g m n i` is the matrix
of `Ψ_i : ℝ[X]_{< n-i} × ℝ[X]_{< m-i} → (Fin (m+n-2i) → ℝ)`,
`(A,B) ↦ (r ↦ (A*f + B*g).coeff (i + (i+r)))`, whose kernel is
`{(A,B) : A*f + B*g ∈ ℝ[X]_{< i}}`; the two spaces have the same dimension `m+n-2i`, so
`det (pscMat f g m n i) ≠ 0 ↔ Ψ_i injective`.

Let `δ = (gcd f g).natDegree`, `f = D * f₁`, `g = D * g₁` with `D = gcd f g` and `f₁, g₁` coprime
(`gsc_range_kerIota` in `Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C` carries out the
same computation for the full Sylvester map).  If `A*f + B*g ∈ ℝ[X]_{< δ}` then
`D * (A*f₁ + B*g₁)` has degree `< δ`, so `A*f₁ + B*g₁ = 0`; coprimality gives `A = g₁ * s`,
`B = -f₁ * s`, and `deg (g₁*s) = (n-δ) + deg s < n-δ` forces `s = 0`.  Hence `Ψ_δ` is injective and
its determinant is nonzero. -/
theorem psc_gcd_natDegree_ne_zero {f g : Polynomial ℝ} (hf : f ≠ 0) (hg : g ≠ 0) :
    Work.WilE4.CAD.psc f g f.natDegree g.natDegree ((gcd f g).natDegree) ≠ 0 := by
  set d := (gcd f g).natDegree with hd_def
  have h1 : d ≤ f.natDegree := Polynomial.natDegree_le_of_dvd (gcd_dvd_left f g) hf
  have h2 : d ≤ g.natDegree := Polynomial.natDegree_le_of_dvd (gcd_dvd_right f g) hg
  have hdim : (g.natDegree - d) + (f.natDegree - d) = f.natDegree + g.natDegree - 2 * d := by
    omega
  have hgd : (g / gcd f g).natDegree = g.natDegree - d := by
    have h := gsc_deg_snd f g hf hg
    omega
  have hfd : (f / gcd f g).natDegree = f.natDegree - d := by
    have h := gsc_deg_fst f g hf
    omega
  -- The kernel of `pscMap` at the degree of the gcd is trivial: it is the space of pairs `(A, B)`
  -- with `A * f + B * g` of degree `< d`, and there are no nonzero ones.
  have hker : LinearMap.ker (pscMap f g f.natDegree g.natDegree d) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro P hP
    rw [LinearMap.mem_ker] at hP
    have hcoeff := (pscMap_eq_zero_iff f g f.natDegree g.natDegree d P).mp hP
    by_cases hN0 : f.natDegree + g.natDegree - 2 * d = 0
    · -- Degenerate case: `f` and `g` are nonzero constants, so both components vanish.
      have hg0 : g.natDegree - d = 0 := by omega
      have hf0 : f.natDegree - d = 0 := by omega
      have hA0 : (P.1 : Polynomial ℝ) = 0 := by
        have key : ∀ p : Polynomial ℝ,
            p ∈ Polynomial.degreeLT ℝ (g.natDegree - d) → p = 0 := by
          intro p hp
          rw [hg0] at hp
          by_contra hne
          have := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr
            (Polynomial.mem_degreeLT.mp hp)
          omega
        exact key _ P.1.2
      have hB0 : (P.2 : Polynomial ℝ) = 0 := by
        have key : ∀ p : Polynomial ℝ,
            p ∈ Polynomial.degreeLT ℝ (f.natDegree - d) → p = 0 := by
          intro p hp
          rw [hf0] at hp
          by_contra hne
          have := (Polynomial.natDegree_lt_iff_degree_lt hne).mpr
            (Polynomial.mem_degreeLT.mp hp)
          omega
        exact key _ P.2.2
      exact Prod.ext (Subtype.ext hA0) (Subtype.ext hB0)
    · -- `f * P.1 + g * P.2` is a polynomial of degree `< d`.
      have hpos : 0 < d + (f.natDegree + g.natDegree - 2 * d) := by omega
      have hb1 : (f * (P.1 : Polynomial ℝ)).natDegree
          < d + (f.natDegree + g.natDegree - 2 * d) := by
        by_cases h0 : (P.1 : Polynomial ℝ) = 0
        · rw [h0, mul_zero]
          simpa using hpos
        · have hnd : (P.1 : Polynomial ℝ).natDegree < g.natDegree - d :=
            (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (Polynomial.mem_degreeLT.mp P.1.2)
          have hle : (f * (P.1 : Polynomial ℝ)).natDegree
              ≤ f.natDegree + (P.1 : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
          omega
      have hb2 : (g * (P.2 : Polynomial ℝ)).natDegree
          < d + (f.natDegree + g.natDegree - 2 * d) := by
        by_cases h0 : (P.2 : Polynomial ℝ) = 0
        · rw [h0, mul_zero]
          simpa using hpos
        · have hnd : (P.2 : Polynomial ℝ).natDegree < f.natDegree - d :=
            (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (Polynomial.mem_degreeLT.mp P.2.2)
          have hle : (g * (P.2 : Polynomial ℝ)).natDegree
              ≤ g.natDegree + (P.2 : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
          omega
      have hQlt : (f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).natDegree
          < d + (f.natDegree + g.natDegree - 2 * d) :=
        (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hb1 hb2)
      have hQmem : f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)
          ∈ Polynomial.degreeLT ℝ d := by
        by_cases h0 : f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ) = 0
        · rw [h0]
          exact Submodule.zero_mem _
        · rw [Polynomial.mem_degreeLT]
          refine (Polynomial.natDegree_lt_iff_degree_lt h0).mp ?_
          by_contra hcon
          have hge : d ≤ (f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).natDegree := by
            omega
          have hz : (f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).coeff
              ((f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).natDegree) = 0 := by
            have hr := hcoeff
              ⟨(f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ)).natDegree - d, by omega⟩
            rwa [Nat.add_sub_of_le hge] at hr
          rw [Polynomial.coeff_natDegree] at hz
          exact (Polynomial.leadingCoeff_ne_zero.mpr h0) hz
      -- Coprimality of the cofactors kills the remaining possibility.
      have hcore : (P.1 : Polynomial ℝ) = 0 ∧ (P.2 : Polynomial ℝ) = 0 :=
        psc_amul_add_bmul_eq_zero (f := f) (g := g) hf hg
          (A := (P.1 : Polynomial ℝ)) (B := (P.2 : Polynomial ℝ))
          (by rw [hgd]; exact P.1.2) (by rw [hfd]; exact P.2.2)
          (by
            have hsum : (P.1 : Polynomial ℝ) * f + (P.2 : Polynomial ℝ) * g
                = f * (P.1 : Polynomial ℝ) + g * (P.2 : Polynomial ℝ) := by ring
            rw [hsum, ← hd_def]
            exact hQmem)
      exact Prod.ext (Subtype.ext hcore.1) (Subtype.ext hcore.2)
  -- The columns of `pscMat` are the values of `pscMap` on the standard basis of its domain, and
  -- `pscMap` is injective, so those columns are linearly independent.
  have hLI1 : LinearIndependent ℝ
      (fun c : Fin ((g.natDegree - d) + (f.natDegree - d)) =>
        pscMap f g f.natDegree g.natDegree d
          (Polynomial.degreeLT.basisProd ℝ (g.natDegree - d) (f.natDegree - d) c)) :=
    (Polynomial.degreeLT.basisProd ℝ (g.natDegree - d) (f.natDegree - d)).linearIndependent.map'
      (pscMap f g f.natDegree g.natDegree d) hker
  have hcol : ∀ (r : Fin (f.natDegree + g.natDegree - 2 * d))
      (c : Fin ((g.natDegree - d) + (f.natDegree - d))),
      pscMat f g f.natDegree g.natDegree d r (finCongr hdim c)
        = pscMap f g f.natDegree g.natDegree d
            (Polynomial.degreeLT.basisProd ℝ (g.natDegree - d) (f.natDegree - d) c) r :=
    fun r c => pscMat_apply_pscMap le_rfl le_rfl hdim r c
  have hfun : (pscMat f g f.natDegree g.natDegree d).col ∘ (finCongr hdim)
      = fun c : Fin ((g.natDegree - d) + (f.natDegree - d)) =>
          pscMap f g f.natDegree g.natDegree d
            (Polynomial.degreeLT.basisProd ℝ (g.natDegree - d) (f.natDegree - d) c) := by
    funext c r
    simpa [Function.comp_def, Matrix.col_apply] using hcol r c
  have hLI2 : LinearIndependent ℝ (pscMat f g f.natDegree g.natDegree d).col := by
    have hLI1' : LinearIndependent ℝ
        ((pscMat f g f.natDegree g.natDegree d).col ∘ (finCongr hdim)) := by
      rw [hfun]
      exact hLI1
    have hcomp := hLI1'.comp (finCongr hdim).symm (finCongr hdim).symm.injective
    simpa [Function.comp_def] using hcomp
  -- A square matrix with linearly independent columns has nonzero determinant.
  rw [Work.WilE4.CAD.psc]
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp hLI2)

end Work.WilE4.CAD
