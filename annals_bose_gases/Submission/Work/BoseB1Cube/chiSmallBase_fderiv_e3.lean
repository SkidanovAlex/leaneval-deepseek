import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.BoseB1Cube.ShapeIdentDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coordinate derivative of the cosine-power bump `chiSmallBase`

`chiSmallBase M z = (ζ(z₀)ζ(z₁)ζ(z₂))^M` is a product of one-variable factors, hence
differentiable (for `M ≥ 2`, where the faces `|z_j| = 1/2` are order-`M` zeros of `ζ`), and its
partial derivative in the `k`-th coordinate is the product of the other two factors times the
derivative of the `k`-th one:

    fderiv ℝ (chiSmallBase M) z (e3 k)
      = deriv (ζ^M) (z.ofLp k) · ∏_{i ≠ k} ζ(z.ofLp i)^M .

The proof is the product rule `HasFDerivAt.finsetProd` over the three coordinates, together with
the chain rule for `ζ^M ∘ (coordinate projection)` and the one-dimensional derivative of `ζ^M`
available in `Submission.Work.ConvQuadDev`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `chiSmallBase M` is the product, over the three coordinates, of the one-dimensional profile
`ζ(y)^M`. -/
lemma chiSmallBase_eq_prod_zeta1d (M : ℕ) :
    Submission.BoseGases.chiSmallBase M
      = fun x : E3 => ∏ i : Fin 3, Submission.BoseGases.zeta1d (x.ofLp i) ^ M := by
  funext x
  rw [Submission.BoseGases.chiSmallBase, Fin.prod_univ_three, mul_pow, mul_pow]

/-- `ζ^M` is differentiable everywhere for `M ≥ 2`: on `|y| < 1/2` by the cosine-power chain
rule, and on `|y| ≥ 1/2` the faces are order-`M` zeros so the derivative vanishes. -/
lemma zeta1d_pow_hasDerivAt_all {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    HasDerivAt (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M)
      (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) y) y := by
  rcases lt_or_ge (|y|) (1 / 2) with hy | hy
  · have h := Submission.BoseGases.zeta1d_pow_hasDerivAt_of_abs_lt (M := M) y hy
    rw [h.deriv]; exact h
  · have h := Submission.BoseGases.zeta1d_pow_hasDerivAt_zero_of_one_half_le (M := M) hM hy
    rw [h.deriv]; exact h

/-- The Fréchet derivative of the `i`-th one-variable factor `x ↦ ζ(x.ofLp i)^M`: it is the
scalar `deriv (ζ^M) (z.ofLp i)` applied to the `i`-th coordinate projection. -/
lemma fderiv_zeta1d_pow_coord {M : ℕ} (hM : 2 ≤ M) (z : E3) (i : Fin 3) :
    fderiv ℝ (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp i) ^ M) z
      = ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))
        ∘SL EuclideanSpace.proj (𝕜 := ℝ) i := by
  have hp : HasFDerivAt (fun x : E3 => x.ofLp i) (EuclideanSpace.proj (𝕜 := ℝ) i) z := by
    simpa using (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i) (x := z))
  have hd : HasFDerivAt (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))) (z.ofLp i) :=
    (zeta1d_pow_hasDerivAt_all hM (z.ofLp i)).hasFDerivAt
  exact (HasFDerivAt.comp (f := fun x : E3 => x.ofLp i)
    (g := fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) z hd hp).fderiv

theorem chiSmallBase_fderiv_e3 {M : ℕ} (hM : 3 ≤ M) (z : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)
      = deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp k)
        * ∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) ^ M := by
  have hM2 : 2 ≤ M := by omega
  rw [chiSmallBase_eq_prod_zeta1d]
  have hp : ∀ i : Fin 3, HasFDerivAt (fun x : E3 => x.ofLp i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) z :=
    fun i => by
      simpa using (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i) (x := z))
  have hd : ∀ i : Fin 3, HasFDerivAt (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))) (z.ofLp i) :=
    fun i => (zeta1d_pow_hasDerivAt_all hM2 (z.ofLp i)).hasFDerivAt
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasFDerivAt (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp i) ^ M)
        (ContinuousLinearMap.toSpanSingleton ℝ
            (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))
          ∘SL EuclideanSpace.proj (𝕜 := ℝ) i) z :=
    fun i _ => HasFDerivAt.comp (f := fun x : E3 => x.ofLp i)
      (g := fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) z (hd i) (hp i)
  have hfin := HasFDerivAt.finsetProd hg
  rw [hfin.fderiv]
  have hval : ∀ i : Fin 3,
      ((ContinuousLinearMap.toSpanSingleton ℝ
            (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))
          ∘SL EuclideanSpace.proj (𝕜 := ℝ) i) (e3 k))
        = ((e3 k).ofLp i) * deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i) := by
    intro i
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [sum_apply, smul_apply, hval, smul_eq_mul, e3_ofLp_apply]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi])
      (fun hk => absurd (Finset.mem_univ k) hk)]
  simp only [↓reduceIte, one_mul]
  ring

end Work.BoseB1Cube
