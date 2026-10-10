import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.ASZParam
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.ASZChartKernelLeGen
import Submission.Work.MotC5N3.KerAevalKleinPASGenAlt
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas

The proof of `ASZhk_notMem` follows the route of
`Work.MotAS.asZOm_zero_ne_zero` (`Submission/Work/MotAS/asZOm_zero_ne_zero.lean`), transposed to
an arbitrary `𝕜`-algebra field `K`:

* `Zk a b 0 = (3a+b)·X 1 + (3a+4b)·X 3`, so its image under the chart evaluation is
  `(3a+b)·(y₁/y₀) + (3a+4b)·(y₃/y₀)`, which after clearing the denominator `y₀` (nonzero) becomes a
  `K̄`-linear combination `Σ_i c_i κ_i` of the Klein coordinates with
  `c_i = -(w+i)·(A·(w+i)² + B)`, `w = asRoot (3g)`, `A = 3a+b`, `B = 3a+4b`;
* the `κ_i` are `K̄`-linearly independent, so each `c_i = 0`; multiplying the `i`-th relation by
  `(w+i)` and summing gives `A · Σ_i (w+i)⁴ + B · Σ_i (w+i)² = 4A = 0`, so `A = 0`, which
  contradicts `a² - ab - b² ≠ 0`. -/

section Helpers

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The `1`-st row of the Lagrange matrix: `asMinv w 1 i = -(w+i)³`. -/
lemma mc_asMinv_one {R : Type*} [CommRing R] (w : R) (i : Fin 5) :
    Work.MotAS.asMinv w 1 i = -((w + (i : ℕ)) ^ 3) := by
  simp [Work.MotAS.asMinv]

/-- The `3`-rd row of the Lagrange matrix: `asMinv w 3 i = -(w+i)`. -/
lemma mc_asMinv_three {R : Type*} [CommRing R] (w : R) (i : Fin 5) :
    Work.MotAS.asMinv w 3 i = -(w + (i : ℕ)) := by
  simp [Work.MotAS.asMinv]

/-- The twisted coordinates are the `K̄`-linear combinations of the Klein coordinates given by the
Lagrange matrix `asMinv (asRoot h) = (asM (asRoot h))⁻¹`. -/
lemma asTwY_eq_Kb_sum_A (D : Work.MotV.KleinData 𝕜) (h : K) (j : Fin 5) :
    asTwY D h j = ∑ i : Fin 5, algebraMap (KbA K) (OmA K D)
      (Work.MotAS.asMinv (asRoot h) j i) * Work.MotV.kleinCoord D (KbA K) i := by
  have hinv : (Work.MotAS.asM (asRoot h))⁻¹ = Work.MotAS.asMinv (asRoot h) :=
    Matrix.inv_eq_right_inv (asM_mul_asMinv (five_eq_zero_KbA K) (asRoot h))
  simp only [asTwY, hinv]

/-- The `i`-th coefficient of `z₀ = A·y₁ + B·y₃` in the `K̄`-basis of Klein coordinates:
`c_i = -(w+i)·(A·(w+i)² + B)` with `w = asRoot h`, `A = 3a+b`, `B = 3a+4b`. -/
noncomputable def asZcIA (D : Work.MotV.KleinData 𝕜) (h : K) (i : Fin 5) : KbA K :=
  -((asRoot h + (i : ℕ)) *
    (algebraMap K (KbA K) (3 * aK K D + bK K D) * (asRoot h + (i : ℕ)) ^ 2
      + algebraMap K (KbA K) (3 * aK K D + 4 * bK K D)))

/-- **The key identity**: clearing the denominator `y₀ = asTwY D h 0` from
`A·(y₁/y₀) + B·(y₃/y₀)` expresses it as the `K̄`-linear combination `Σ_i c_i κ_i` of the Klein
coordinates with `c_i = asZcIA D h i`. -/
lemma asZ0_key_A (D : Work.MotV.KleinData 𝕜) (h : K) :
    algebraMap K (OmA K D) (3 * aK K D + bK K D) * asTwY D h 1
      + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D) * asTwY D h 3
    = ∑ i : Fin 5, algebraMap (KbA K) (OmA K D) (asZcIA D h i) *
        Work.MotV.kleinCoord D (KbA K) i := by
  rw [asTwY_eq_Kb_sum_A D h 1, asTwY_eq_Kb_sum_A D h 3,
    IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) (3 * aK K D + bK K D),
    IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) (3 * aK K D + 4 * bK K D)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← add_mul, ← map_add]
  congr 1
  rw [mc_asMinv_one, mc_asMinv_three]
  simp only [asZcIA]
  ring_nf

/-- In characteristic `5`, `a² - ab - b² = (3a+b)(2a+4b)`, so `3a+b ≠ 0`. -/
lemma three_mul_add_ne_zero_A (a b : K) (hδ : a ^ 2 - a * b - b ^ 2 ≠ 0) : 3 * a + b ≠ 0 := by
  intro h
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hfac : (3 * a + b) * (2 * a + 4 * b) = a ^ 2 - a * b - b ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) (a ^ 2 + 3 * a * b + b ^ 2) * h5
  rw [h, zero_mul] at hfac
  exact hδ hfac.symm

/-- The characteristic-`5` power sum `Σ_{i<5} (w+i)² = 0`. -/
lemma sum_five_sq_A {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    ∑ i : Fin 5, (w + (i : ℕ)) ^ 2 = 0 := by
  rw [Fin.sum_univ_five]
  norm_num
  ring_nf
  linear_combination (norm := first | refl_ring1 | ring1) (6 + 4 * w + w ^ 2) * h5

end Helpers

/-- **The linear form `Z₀ = (3a+b)X₁ + (3a+4b)X₃` is not in the chart ideal of `C_{3g}`**, i.e.
`Z₀ ≠ 0` in `K[X₀..X₄] ⧸ asChartIdeal a b (3g)`.  This is the well-definedness input for the forward
map `Xᵢ ↦ Z_{i+1}/Z₀` of the K6 leaf (`ASZTwistDivPlaneGeom_three`).

SUGGESTED ROUTE (all ingredients proved and importable):
* `Work.MotC5N3.ASZChartSetupGen.asChartIdeal_le_ker_A` and
  `Work.MotC5N3.ASZChartKernelLeGen.asChartKernelLe_of_aux_A` (with the proved
  `asChartHomogeniseA` and `Work.MotC5N3.KerAevalKleinPASGenAlt.kerAevalKleinPASGenAlt`) give
  `RingHom.ker (asChartPhiA D h) = asChartIdeal (aK K D) (bK K D) h` for every `h : K`; specialise
  `h := 3*g`.  Hence `Zk a b 0 ∉ asChartIdeal a b (3g) ↔ asChartPhiA D (3g) (Zk a b 0) ≠ 0`.
* `asChartPhiA D h (X j) = asTwY D h j / asTwY D h 0` and `Zk a b 0 = (3a+b)·X 1 + (3a+4b)·X 3`
  (fill `phiAS a b` — row 0 is `0, 3a+b, 0, 3a+4b, 0`).  Multiply by `asTwY D (3g) 0`, which is
  nonzero (`Work.MotC5N3.twistFieldAS_eq` has `asTwY_zero_ne_zero`), so it suffices to prove
  `(3a+b) * asTwY D (3g) 1 + (3a+4b) * asTwY D (3g) 3 ≠ 0` in `OmA K D`.
* `asTwY D h j = Σ_i asMinv (asRoot h) j i * κ_i` with the explicit entries
  `asMinv w j i = (if j = 0 then 1 else 0) - (w+i)^(4-j)` (see `asNO_apply` in
  `twistFieldAS_eq.lean`; `asNO = asMinv` pushed forward).  So the combination above is
  `Σ_i c_i κ_i` with `c_i = -(3a+b)(w+i)^3 - (3a+4b)(w+i)`, `w = asRoot (3*g)`.
* `Work.MotC5N3.twistFieldAS_eq.kleinCoord_linearIndependent_KbA` says the `κ_i` are linearly
  independent over `KbA K`; hence `c_i = 0` for all `i`, i.e. the polynomial
  `T * ((3a+b) * T^2 + (3a+4b))` (degree 3, nonzero because `3a+b ≠ 0`) would vanish at the five
  *distinct* points `w, w+1, ..., w+4` — impossible (degree 3 < 5; e.g.
  `Polynomial.card_roots'`).  Note `3a+b ≠ 0` follows from `hD.1` (`a²-ab-b² ≠ 0`). -/
theorem ASZhk_notMem (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotC5N3.Zk (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (0 : Fin 5) ∉
      Work.MotAS.asChartIdeal (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (3 * g) := by
  intro hmem
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hG : D.Good := hD.1
  -- Step 1: membership in the chart ideal puts `Z₀` in the kernel of the chart evaluation.
  have hphi0 : asChartPhiA D (3 * g) (Zk (aK K D) (bK K D) 0) = 0 :=
    RingHom.mem_ker.mp (asChartIdeal_le_ker_A D hG (3 * g) hmem)
  have hphi0' : asChartPhiOmA D (3 * g) (Zk (aK K D) (bK K D) 0) = 0 := by
    have h1 : ((asChartPhiA D (3 * g) (Zk (aK K D) (bK K D) 0) :
        ↥(twistFieldAS D (3 * g))) : OmA K D) = 0 := by
      rw [hphi0]; rfl
    rwa [asChartPhiA_coe] at h1
  -- Step 2: the explicit value of the chart evaluation at `Z₀`.
  have hval : asChartPhiOmA D (3 * g) (Zk (aK K D) (bK K D) 0)
      = algebraMap K (OmA K D) (3 * aK K D + bK K D)
          * (asTwY D (3 * g) 1 / asTwY D (3 * g) 0)
        + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D)
          * (asTwY D (3 * g) 3 / asTwY D (3 * g) 0) := by
    rw [show Zk (aK K D) (bK K D) 0
        = C (3 * aK K D + bK K D) * X 1 + C (3 * aK K D + 4 * bK K D) * X 3 from by
      simp only [Zk, Fin.sum_univ_five, Work.MotAS.phiAS]; norm_num]
    simp only [asChartPhiOmA, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [hval] at hphi0'
  -- Step 3: clear the denominator `y₀ = asTwY D (3*g) 0 ≠ 0`.
  have hy0 : asTwY D (3 * g) 0 ≠ 0 := asTwY_zero_ne_zero D (3 * g) hG
  have hprod : algebraMap K (OmA K D) (3 * aK K D + bK K D) * asTwY D (3 * g) 1
      + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D) * asTwY D (3 * g) 3 = 0 := by
    have h2 : (algebraMap K (OmA K D) (3 * aK K D + bK K D)
          * (asTwY D (3 * g) 1 / asTwY D (3 * g) 0)
        + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D)
          * (asTwY D (3 * g) 3 / asTwY D (3 * g) 0))
        * asTwY D (3 * g) 0 = 0 := by rw [hphi0', zero_mul]
    have h3 : (algebraMap K (OmA K D) (3 * aK K D + bK K D)
          * (asTwY D (3 * g) 1 / asTwY D (3 * g) 0)
        + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D)
          * (asTwY D (3 * g) 3 / asTwY D (3 * g) 0))
        * asTwY D (3 * g) 0
        = algebraMap K (OmA K D) (3 * aK K D + bK K D) * asTwY D (3 * g) 1
          + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D) * asTwY D (3 * g) 3 := by
      rw [add_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ hy0, div_mul_cancel₀ _ hy0]
    rw [h3] at h2; exact h2
  -- Step 4: rewrite as a `K̄`-linear combination of the Klein coordinates.
  have hkey := asZ0_key_A D (3 * g)
  rw [hprod] at hkey
  have hsum : ∑ i : Fin 5, asZcIA D (3 * g) i • Work.MotV.kleinCoord D (KbA K) i = 0 := by
    simpa only [Algebra.smul_def] using hkey.symm
  -- Step 5: linear independence over `K̄` forces all coefficients to vanish.
  have hind : LinearIndependent (KbA K) (Work.MotV.kleinCoord D (KbA K)) :=
    kleinCoord_linearIndependent_KbA D hG
  rw [Fintype.linearIndependent_iff] at hind
  have hc : ∀ i : Fin 5, asZcIA D (3 * g) i = 0 := fun i => hind (asZcIA D (3 * g)) hsum i
  -- Step 6: multiply the `i`-th relation by `(w+i)` and sum over `i`.
  have hrel : ∀ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i = 0 := by
    intro i; rw [hc i, mul_zero]
  have hsum0 : ∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i = 0 :=
    Finset.sum_eq_zero (fun i _ => hrel i)
  have hexp : (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i)
      = -(algebraMap K (KbA K) (3 * aK K D + bK K D)
            * (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) ^ 4)
          + algebraMap K (KbA K) (3 * aK K D + 4 * bK K D)
            * (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [asZcIA]
    first | refl_ring1 | ring
  have hfin : algebraMap K (KbA K) (3 * aK K D + bK K D) * (4 : KbA K) = 0 := by
    have h := hsum0
    rw [hexp, sum_five_pow_four (five_eq_zero_KbA K) (asRoot (3 * g)),
      sum_five_sq_A (five_eq_zero_KbA K) (asRoot (3 * g))] at h
    simpa using h
  have h4ne : (4 : KbA K) ≠ 0 := by
    rw [show (4 : KbA K) = -(1 : KbA K) by linear_combination five_eq_zero_KbA K]
    exact neg_ne_zero.mpr one_ne_zero
  have hα0 : algebraMap K (KbA K) (3 * aK K D + bK K D) = 0 := by
    rcases mul_eq_zero.mp hfin with h | h
    · exact h
    · exact absurd h h4ne
  have h3ab : 3 * aK K D + bK K D ≠ 0 :=
    three_mul_add_ne_zero_A (aK K D) (bK K D) (aK_sq_sub_ne D hD)
  exact h3ab ((algebraMap K (KbA K)).injective (by rw [hα0, map_zero]))

end Work.MotC5N3
