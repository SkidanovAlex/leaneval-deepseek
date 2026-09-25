import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The canonical lift `iwRep` is a section of the quotient map `ℝ → 𝕋`: the circle point
`(iwRep ξ : 𝕋)` is `ξ`. -/
lemma coe_iwRep (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    ((iwRep ξ : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = ξ := by
  simp only [iwRep, AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply,
    AddCircle.coe_equivIoc]

/-- **The Weyl kernel as the fibre sum of the `ℤ`-indexed density kernel**: at the real point
`θ`, the trigonometric polynomial `Σ_j k_N(j) · e_j` with the density coefficients
`k_N(j) = polyKernelZ P N j` is the Weyl sum `N⁻¹ Σ_{n<N} e(θ P(n))`.

The proof is the grouping of `N⁻¹ Σ_{n<N} e(θ P(n))` by the value `j = P(n)`
(`Finset.sum_fiberwise_of_maps_to`, all values lying in the support `[-polySupportZ, polySupportZ]`
by `eval_natAbs_lt_polySupportZ`), the definition of `polyKernelZ` as the fibre cardinality, and
`fourier_coe_apply` for the value of the character `e_j` at `(θ : 𝕋)`. -/
lemma sum_polyKernelZ_fourier (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
      (polyKernelZ P N j : ℂ) * fourier j ((θ : ℝ) :
        Work.BourgainPlan.IonescuWainger.Circle))
      = polyWeylKernel P N θ := by
  have hE : ∀ n ∈ Finset.range N,
      fourier (P.eval (n : ℤ)) ((θ : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
        = Complex.exp
            (2 * Real.pi * Complex.I * ((θ * ((P.eval (n:ℤ) : ℤ) : ℝ) : ℝ) : ℂ)) := by
    intro n _
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hkey : (∑ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
        (polyKernelZ P N j : ℂ) * fourier j ((θ : ℝ) :
          Work.BourgainPlan.IonescuWainger.Circle))
      = ((N:ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
          fourier (P.eval (n:ℤ)) ((θ:ℝ) :
            Work.BourgainPlan.IonescuWainger.Circle) := by
    have hfib := Finset.sum_fiberwise_of_maps_to
        (s := Finset.range N)
        (t := Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N))
        (g := fun i : ℕ => P.eval (i : ℤ))
        (fun i hi => Finset.mem_Icc.mpr (by
          have h := eval_natAbs_lt_polySupportZ P N i hi; omega))
        (fun i : ℕ => fourier (P.eval (i : ℤ)) ((θ : ℝ) :
          Work.BourgainPlan.IonescuWainger.Circle))
    rw [← hfib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.sum_const, nsmul_eq_mul]
    unfold polyKernelZ
    push_cast
    ring
  rw [hkey, polyWeylKernel]
  congr 1
  exact Finset.sum_congr rfl hE

/-- **The a.e. values of the density symbol** `khatZMult P N` (the multiplier class of the density average `discAvgZC P N`, `ftLp_discAvgZC_z`) are the conjugates of the Weyl kernel read along the canonical lift: `khatZMult P N =ᵐ star ∘ mstWeyl P N`. Both sides are computed by grouping the finite sum `N⁻¹ Σ_{n<N} exp (2π i θ P(n))` by the value `j = P(n)`, which is the definition of `polyKernelZ`; `star` reflects `fourier (-j)` to `fourier j` (`fourier_neg`) while the real coefficients `polyKernelZ P N j` are unaffected. The a.e. qualifier is forced only by the `Lp`-representative of the finite sum; no measurability of `iwRep` is needed. The companion `khatMult_coeFn` in `Submission/Work/BourgainPlan/Maximal/khatMult.lean` carries out the same computation for the `ℕ`-indexed variant `khatMult` and is the template for the proof. -/
theorem khatZMult_coeFn_star_mstWeyl (P : Polynomial ℤ) (N : ℕ) :
    ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      (Work.BourgainPlan.Maximal.khatZMult P N :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
        = star (Work.BourgainPlan.Maximal.mstWeyl P N ξ) := by
  classical
  rw [khatZMult]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  have hterm : ∀ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
      (((polyKernelZ P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-j) :
          Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => star ((polyKernelZ P N j : ℂ) * fourier j ξ) := by
    intro j _
    refine (Lp.coeFn_smul _ _).trans ?_
    refine (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _)
      (coeFn_fourierLp (T := 1) (⊤ : ℝ≥0∞) (-j))).trans ?_
    filter_upwards with ξ
    show (polyKernelZ P N j : ℂ) * fourier (-j) ξ
      = star ((polyKernelZ P N j : ℂ) * fourier j ξ)
    rw [fourier_neg, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hev : ∀ᵐ ξ ∂haarT,
      ∀ j ∈ Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N),
      (((polyKernelZ P N j : ℂ) • fourierLp (T := 1) (p := ⊤) (-j) :
          Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
        = star ((polyKernelZ P N j : ℂ) * fourier j ξ) :=
    (Finset.eventually_all (Finset.Icc (-(polySupportZ P N : ℤ)) (polySupportZ P N))).mpr
      fun j hj => hterm j hj
  filter_upwards [hev] with ξ hξ
  rw [Finset.sum_congr rfl (fun j hj => hξ j hj), ← star_sum]
  congr 1
  have h := sum_polyKernelZ_fourier P N (iwRep ξ)
  rw [coe_iwRep] at h
  exact h

end

end Work.BourgainPlan.Maximal
