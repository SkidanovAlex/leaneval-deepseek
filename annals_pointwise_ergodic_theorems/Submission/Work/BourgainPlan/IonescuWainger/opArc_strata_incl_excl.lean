import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl
import Submission.Work.BourgainPlan.IonescuWainger.opArc_arcShift

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

noncomputable section

/-! ## Linearity of `opMul` in its symbol

`opMul Φ f hf` is defined through `Φ • ftLp f hf`, and the `L^∞`-action on `L²` is linear in its
first argument (`Lp.smul_add`, `Lp.smul_assoc`); `opMul` is recovered from `Φ • ftLp f hf` by the
linear map `fourierBasis.repr` (`opMul_apply`).  Hence `opMul` is additive and `ℂ`-semilinear in
its symbol, and therefore commutes with finite sums. -/

/-- `opMul` with the zero symbol is the zero operator. -/
theorem opMul_zero (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opMul (0 : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) f hf = 0 := by
  funext n
  rw [opMul_apply, Pi.zero_apply]
  simp only [opMulLp]
  rw [show (0 : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) • ftLp f hf = 0 from
    Lp.zero_smul ℂ ⊤ (ftLp f hf)]
  exact inner_zero_right _

/-- `opMul` is additive in its symbol. -/
theorem opMul_add (Φ Ψ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) :
    opMul (Φ + Ψ) f hf = opMul Φ f hf + opMul Ψ f hf := by
  funext n
  rw [Pi.add_apply, opMul_apply, opMul_apply, opMul_apply]
  simp only [opMulLp, Lp.smul_add, inner_add_right]

/-- `opMul` is `ℂ`-homogeneous in its symbol. -/
theorem opMul_smul (c : ℂ) (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) :
    opMul (c • Φ) f hf = c • opMul Φ f hf := by
  funext n
  rw [Pi.smul_apply, opMul_apply, opMul_apply]
  simp only [opMulLp, Lp.smul_assoc, inner_smul_right, smul_eq_mul]

/-- `opMul` commutes with finite linear combinations of symbols. -/
theorem opMul_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opMul (∑ i ∈ s, c i • Φ i) f hf = ∑ i ∈ s, c i • opMul (Φ i) f hf := by
  classical
  induction s using Finset.induction with
  | empty => simp [opMul_zero]
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, opMul_add, opMul_smul, ih]

/-! ## The inclusion–exclusion identity for the shifted arc symbols -/

/-- **The strata inclusion–exclusion for the translated arc sets.**  Since
`Σ_A = Σ_{⊆ A} \ ⋃_{B ⊊ A} Σ_{⊆ B}` and the translated symbols are just the symbols of the
translated sets (`arcSymbol_arcShift_apply'`), the pointwise symbol identity
`arcSymbol_strata_incl_excl` continues to hold after translating every arc by `α`. -/
theorem arcSymbol_arcShift_strata_incl_excl (A : Finset ℕ) (h2 : ∀ q ∈ A, 2 ≤ q)
    (hcop : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → Nat.Coprime p q) (α : Circle) (φ : Circle → ℂ) :
    arcSymbol φ (arcShift (sigmaStrataFinset A) α)
      = fun ξ => ∑ B ∈ A.powerset,
          ((-1 : ℂ) ^ (A.card - B.card)) * arcSymbol φ (arcShift (sigmaSubAFinset B) α) ξ := by
  funext ξ
  rw [arcSymbol_arcShift_apply', arcSymbol_strata_incl_excl φ A h2 hcop]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [arcSymbol_arcShift_apply' φ (sigmaSubAFinset B) α ξ]

/-- **The strata inclusion–exclusion for the shifted arc symbols, in `L^∞(𝕋)`.**  The pointwise
identity of `arcSymbol_arcShift_strata_incl_excl` is an equality of `L^∞`-symbols; using
`MemLp.coeFn_toLp` it turns into the corresponding identity of `L^∞`-classes, which is what the
multiplier `opMul` sees. -/
theorem arcSymbolLp_arcShift_strata_incl_excl (A : Finset ℕ) (h2 : ∀ q ∈ A, 2 ≤ q)
    (hcop : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → Nat.Coprime p q)
    (α : Circle) (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    arcSymbolLp φ hφ (arcShift (sigmaStrataFinset A) α)
      = ∑ B ∈ A.powerset, ((-1 : ℂ) ^ (A.card - B.card)) •
          arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α) := by
  classical
  have hpt := arcSymbol_arcShift_strata_incl_excl A h2 hcop α φ
  -- The `L^∞`-class of the alternating sum of torsion symbols agrees a.e. with the alternating sum
  -- of the classes.
  have hA : (⇑(∑ B ∈ A.powerset, ((-1 : ℂ) ^ (A.card - B.card)) •
        arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α)) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => ∑ B ∈ A.powerset,
          ((-1 : ℂ) ^ (A.card - B.card)) * arcSymbol φ (arcShift (sigmaSubAFinset B) α) ξ := by
    refine (Lp.coeFn_fun_finsetSum A.powerset
      (fun B => ((-1 : ℂ) ^ (A.card - B.card)) •
        arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α))).trans ?_
    have hper : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)), ∀ B ∈ A.powerset,
        (⇑(((-1 : ℂ) ^ (A.card - B.card)) •
          arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α)) : Circle → ℂ) ξ
          = ((-1 : ℂ) ^ (A.card - B.card)) * arcSymbol φ (arcShift (sigmaSubAFinset B) α) ξ :=
      (Finset.eventually_all A.powerset).mpr (fun B _ =>
        (Lp.coeFn_smul ((-1 : ℂ) ^ (A.card - B.card))
          (arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α))).trans (by
            filter_upwards [arcSymbolLp_coeFn φ hφ (arcShift (sigmaSubAFinset B) α)]
              with ξ h2'
            simp only [Pi.smul_apply, smul_eq_mul] at h2' ⊢
            rw [h2']))
    filter_upwards [hper] with ξ hξ
    exact Finset.sum_congr rfl fun B hB => hξ B hB
  refine Lp.ext ?_
  refine (arcSymbolLp_coeFn φ hφ (arcShift (sigmaStrataFinset A) α)).trans ?_
  rw [hpt]
  exact hA.symm

/-- **The operator form of the strata inclusion–exclusion** (Tao, arXiv:2008.05066, §4, the step of
the proof of the real-form multiplier result that reads "By the inclusion–exclusion formula, and
conceding a factor of `2^k`, it suffices to show ...", and the analogous step of the `p = ∞`
paragraph of `ortho-apply`(ii)): the arc multiplier over the strata `Σ_A` is the alternating sum of
the arc multipliers over the torsion subgroups `Σ_{⊆ B}`, `B ⊆ A`, with the arcs translated by `α`.

This is what lets every bound proved for the *torsion* multipliers
`opArc φ hφ (arcShift (sigmaSubAFinset B) α)` — e.g. the torsion-arc `p = ∞` family bound
`opArc_sup_torsion_family`, or the Magyar–Stein–Wainger sampling bound — be transferred to the
*strata* multipliers `opArc φ hφ (arcShift (sigmaStrataFinset A) α)` that occur in the proof of the
Ionescu–Wainger multiplier result, at the cost of a factor `2^{|A|}`.

Route.  By the landed symbol identity `arcSymbol_strata_incl_excl`, applied at the shifted argument
`ξ - α`, together with `arcSymbol_arcShift` (`arcSymbol φ (arcShift E α) ξ = arcSymbol φ E (ξ - α)`),
the two sides have a.e.-equal symbols; two `L^∞`-symbols that agree a.e. give the same element of
`Lp ℂ ⊤` (so the same multiplier), and `opMul` is additive/semilinear in its symbol because
`opMul Φ f hf` is defined through `Φ • ftLp f hf` and the scalar action of `Lp ℂ ⊤` on `Lp ℂ 2` is
linear.  The only bookkeeping is a finite-sum induction for the alternating sum (or a direct appeal
to linearity of the map `Φ ↦ opMul Φ f hf`; the pattern of `opArc_arcShift`, going through
a.e.-equality of the Fourier transforms, avoids any `IsScalarTower` friction). -/
theorem opArc_strata_incl_excl (A : Finset ℕ) (h2 : ∀ q ∈ A, 2 ≤ q)
    (hcop : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → Nat.Coprime p q)
    (α : Work.BourgainPlan.IonescuWainger.Circle)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ
        (Work.BourgainPlan.IonescuWainger.arcShift
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) α) f hf
      = ∑ B ∈ A.powerset, (-1 : ℂ) ^ (A.card - B.card) •
          Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.arcShift
              (Work.BourgainPlan.IonescuWainger.sigmaSubAFinset B) α) f hf := by
  have hLp := arcSymbolLp_arcShift_strata_incl_excl A h2 hcop α φ hφ
  simp only [opArc]
  rw [hLp]
  exact opMul_finset_sum A.powerset (fun B => (-1 : ℂ) ^ (A.card - B.card))
    (fun B => arcSymbolLp φ hφ (arcShift (sigmaSubAFinset B) α)) f hf

end

end Work.BourgainPlan.IonescuWainger
