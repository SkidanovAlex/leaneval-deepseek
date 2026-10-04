import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC
import Submission.Work.Diff.STE.B3.VarCoef.pd_comp_chain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

Lead design (2026-10-03): the chain-rule bridge that transports the flat Laplacian power of chart i into chart l as a variable-coefficient operator. This is what lets the commutator be computed in the cutoff's own chart, so S = flatCut is never transported (that transport caused all the equivariance and strip failures).
ROUTE:
1. For smooth periodic w, lapPow k w = (−lapC)^[k] w pointwise. Use lapPow_one_eq_neg_lapC (SymCalcStep6, PROVED); lapPow (j+1) = lapPow 1 ∘ lapPow j holds on Fourier coefficients (flatLam^(j+1) = flatLam · flatLam^j); then seriesFun/fourierCoeff inversion for smooth periodic functions (existing).
2. One step of the chain rule. On the open set τ '' W, w = G ∘ σ, and τ ∘ σ = id there (from hστ). Then
   −lapC (G∘σ)(z) = varLap A B G (σ z),
   by the second-order chain rule: ∂_r(G∘σ) = Σ_a (∂_a G)(σz) ∂_r σ_a(z) and ∂_r∂_r(G∘σ) = Σ_{ab} ∂_a∂_b G(σz) ∂_rσ_a ∂_rσ_b + Σ_a ∂_a G(σz) ∂_r∂_r σ_a. At y = σ z one has τ y = z, which matches hAW and hBW.
3. Induction on k. If (−lapC)^[j] w = (varLapPow j A B G) ∘ σ on the OPEN set τ '' W, then their second derivatives agree there (Filter.EventuallyEq.fderiv_eq, twice), so step 2 applies to varLapPow j A B G, which is smooth since A, B and G are smooth. Evaluate at z = τ y.
Prove it directly; no children. Run python3 REFS/tools/dupcheck.py . | grep VarCoef before declare_proven.
-/

noncomputable section

open MeasureTheory BigOperators Filter

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator `f ↦ (- Δ f) = -lapC f` on functions on the flat torus; the `k`-th power of this
operator is `lapPow k` on smooth periodic functions (`lapPow_eq_iterate` below). -/
noncomputable def negLap : ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ) :=
  fun f => fun z => - Work.Diff.STE.B3.SymCalc.lapC f z

/-! ## Locality of `lapC` -/

/-- `lapC` only depends on the germ: eventually equal functions have the same `lapC` at the point.
This is the two-fold application of `Filter.EventuallyEq.fderiv` (the second derivative of
eventually equal functions agrees at the point). -/
theorem lapC_congr {f g : (ι → ℝ) → ℂ} {z : ι → ℝ} (h : f =ᶠ[nhds z] g) :
    Work.Diff.STE.B3.SymCalc.lapC f z = Work.Diff.STE.B3.SymCalc.lapC g z := by
  have h1 : fderiv ℝ f =ᶠ[nhds z] fderiv ℝ g := h.fderiv
  have h2 : ∀ i : ι, (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) =ᶠ[nhds z]
      (fun x : ι → ℝ => (fderiv ℝ g x) (Pi.single i 1)) := by
    intro i
    have := h1.fun_comp (fun T : (ι → ℝ) →L[ℝ] ℂ => T (Pi.single i 1))
    simpa only [Function.comp_def] using this
  have h3 : ∀ i : ι,
      fderiv ℝ (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) =ᶠ[nhds z]
        fderiv ℝ (fun x : ι → ℝ => (fderiv ℝ g x) (Pi.single i 1)) :=
    fun i => (h2 i).fderiv
  simp only [Work.Diff.STE.B3.SymCalc.lapC]
  refine Finset.sum_congr rfl fun i _ => ?_
  show fderiv ℝ (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) z (Pi.single i 1)
    = fderiv ℝ (fun x : ι → ℝ => (fderiv ℝ g x) (Pi.single i 1)) z (Pi.single i 1)
  rw [(h3 i).eq_of_nhds]

/-! ## Smoothness of the variable-coefficient operator -/

/-- `varLap A B g` is smooth as soon as the coefficients `A`, `B` and `g` are. -/
theorem varLap_contDiff {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a))
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (varLap A B g) := by
  have hcast : ∀ (c : (ι → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) c →
      ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => ((c x : ℝ) : ℂ)) :=
    fun c hc => Complex.ofRealCLM.contDiff.comp hc
  have h1 : ∀ a : ι, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ι → ℝ => ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a g x) :=
    fun a => (hcast _ (hB a)).mul (Work.Diff.STE.ste_contDiff_pd a hg)
  have h2 : ∀ a b : ι, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ι → ℝ => ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) x) :=
    fun a b => (hcast _ (hA a b)).mul
      (Work.Diff.STE.ste_contDiff_pd a (Work.Diff.STE.ste_contDiff_pd b hg))
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ =>
    -((∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) x)
      + ∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a g x))
  exact ((ContDiff.sum fun a _ => ContDiff.sum fun b _ => h2 a b).add
    (ContDiff.sum fun a _ => h1 a)).neg

/-- The iterated variable-coefficient operator `varLapPow k A B g` is smooth if `A`, `B`, `g` are. -/
theorem varLapPow_contDiff {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) :
    ∀ (k : ℕ) {g : (ι → ℝ) → ℂ}, ContDiff ℝ (⊤ : ℕ∞) g →
      ContDiff ℝ (⊤ : ℕ∞) (varLapPow k A B g) := by
  intro k
  induction k with
  | zero => intro g hg; simpa only [varLapPow, Function.iterate_zero_apply] using hg
  | succ k ih =>
    intro g hg
    rw [show varLapPow (k + 1) A B g = varLap A B (varLapPow k A B g) from
      Function.iterate_succ_apply' (varLap A B) k g]
    exact varLap_contDiff hA hB (ih hg)

/-! ## `lapPow k` is the `k`-th power of `-lapC` on smooth periodic functions -/

/-- For smooth `1`-periodic `w`, the flat Laplacian power `lapPow k w` is the `k`-fold iterate of
the operator `-lapC`.  Induction on `k`: `lapPow 0 w = w` by Fourier inversion, and
`lapPow (k+1) w = lapPow k (lapPow 1 w) = lapPow k (-lapC w)` by `lapPow_algebra`. -/
theorem lapPow_eq_iterate :
    ∀ (k : ℕ) (w : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      ∀ x : ι → ℝ,
        Work.Diff.STE.B3.SymCalcStep5.lapPow k w x = (negLap^[k] w) x := by
  intro k
  induction k with
  | zero =>
    intro w hw hwp x
    rw [Function.iterate_zero_apply]
    have hcoef : (fun m : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ 0 : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff w m) = Work.Diff.STE.fourierCoeff w := by
      funext m
      rw [pow_zero, Complex.ofReal_one, one_mul]
    rw [show Work.Diff.STE.B3.SymCalcStep5.lapPow 0 w
        = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff w)
      from congrArg Work.Diff.STE.seriesFun hcoef,
      Work.Diff.STE.flat.seriesFun_fourierCoeff w hw hwp x]
  | succ k ih =>
    intro w hw hwp x
    rw [Function.iterate_succ_apply]
    have hnegw : ContDiff ℝ (⊤ : ℕ∞) (negLap w) :=
      (Work.Diff.STE.B3.SymCalcStep6.lapC_contDiff hw).neg
    have hperw : Work.Diff.STE.Periodic1 (negLap w) := by
      intro i z
      exact congrArg Neg.neg (Work.Diff.STE.B3.SymCalcStep6.lapC_periodic hwp i z)
    have heq : Work.Diff.STE.B3.SymCalcStep5.lapPow 1 w = negLap w := by
      funext z
      exact Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC w hw hwp z
    rw [← Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra.1 k 1 w hw hwp, heq]
    exact ih (negLap w) hnegw hperw x


/-! ## The second-order chain rule for `lapC` (local proof of `lapC_comp_chain`) -/

/-- The `a`-th coordinate of a smooth map into `ι → ℝ` is smooth. -/
private lemma contDiff_coord (σ : (ι → ℝ) → (ι → ℝ)) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (a : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => σ z a) :=
  (ContinuousLinearMap.contDiff
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) a)).comp hσ

/-- The real partial derivative `pdR i f` of a smooth real function is smooth. -/
private lemma contDiff_pdR_of_contDiff (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdR i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => fderiv ℝ f x (Pi.single i (1 : ℝ)))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Clairaut's theorem for complex valued smooth functions: mixed second partial derivatives agree. -/
private lemma pd_clairaut {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (a b : ι)
    (z : ι → ℝ) :
    Work.Diff.STE.pd b (Work.Diff.STE.pd a g) z = Work.Diff.STE.pd a (Work.Diff.STE.pd b g) z := by
  have hlt : minSmoothness ℝ 2 ≤ (⊤ : ℕ∞) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hsym : IsSymmSndFDerivAt ℝ g z :=
    (ContDiff.contDiffAt hg (x := z)).isSymmSndFDerivAt (n := (⊤ : ℕ∞)) hlt
  -- the CLM form of a first partial derivative
  have hclm : ∀ c : ι, fderiv ℝ (Work.Diff.STE.pd c g) z
      = (fderiv ℝ (fderiv ℝ g) z).flip (Pi.single c 1) := by
    intro c
    show fderiv ℝ (fun x : ι → ℝ => (fderiv ℝ g x) (Pi.single c 1)) z = _
    have hc2 : DifferentiableAt ℝ (fun x : ι → ℝ => fderiv ℝ g x) z :=
      (ContDiff.contDiffAt (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (x := z)).differentiableAt
        (by simp)
    have h := fderiv_clm_apply (𝕜 := ℝ) (c := fun x : ι → ℝ => fderiv ℝ g x)
      (u := fun _ : ι → ℝ => Pi.single c 1) hc2 (differentiableAt_const _)
    simpa using h
  have h := hsym (Pi.single a 1) (Pi.single b 1)
  show fderiv ℝ (Work.Diff.STE.pd a g) z (Pi.single b 1)
      = fderiv ℝ (Work.Diff.STE.pd b g) z (Pi.single a 1)
  rw [hclm a, hclm b, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h.symm

/-- The Leibniz rule for `((c · : ℝ) : ℂ) * h`, evaluated on the direction `eᵢ`. -/
private lemma fderiv_ofReal_mul_apply (i : ι) (c : (ι → ℝ) → ℝ) (h : (ι → ℝ) → ℂ) {z : ι → ℝ}
    (hc : DifferentiableAt ℝ c z) (hh : DifferentiableAt ℝ h z) :
    fderiv ℝ (fun y => ((c y : ℝ) : ℂ) * h y) z (Pi.single i 1)
      = ((c z : ℝ) : ℂ) * (fderiv ℝ h z (Pi.single i 1))
        + h z * ((fderiv ℝ c z (Pi.single i 1) : ℝ) : ℂ) := by
  have hcC : DifferentiableAt ℝ (fun y : ι → ℝ => ((c y : ℝ) : ℂ)) z :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hc.hasFDerivAt).differentiableAt
  have hmul : fderiv ℝ ((fun y : ι → ℝ => ((c y : ℝ) : ℂ)) * h) z
      = (fun y : ι → ℝ => ((c y : ℝ) : ℂ)) z • fderiv ℝ h z
        + h z • fderiv ℝ (fun y : ι → ℝ => ((c y : ℝ) : ℂ)) z :=
    fderiv_fun_mul hcC hh
  have hof : fderiv ℝ (fun y : ι → ℝ => ((c y : ℝ) : ℂ)) z
      = Complex.ofRealCLM.comp (fderiv ℝ c z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hc.hasFDerivAt).fderiv
  rw [show fderiv ℝ (fun y : ι → ℝ => ((c y : ℝ) : ℂ) * h y) z
      = fderiv ℝ ((fun y : ι → ℝ => ((c y : ℝ) : ℂ)) * h) z from rfl]
  rw [hmul, hof]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

/-- **The second-order chain rule for the flat Laplacian.**  For smooth `g` and smooth `σ`,

  `Δ (g ∘ σ) (z) = Σ_{a,b} (Σ_i ∂_iσ_a ∂_iσ_b)(z) · (∂_a∂_b g)(σz)
                 + Σ_a (Σ_i ∂_i∂_iσ_a)(z) · (∂_a g)(σz)`.

This is the one-step chain-rule computation of the transport lemma (with `Δ = lapC = Σ_i ∂_i∂_i`),
obtained from `pd_comp_chain` applied to `g` and to `pd a g`, the Leibniz rule for the coefficients
`∂_iσ_a`, and `Finset.sum` algebra. -/
private lemma lapC_comp_chain_local (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (σ : (ι → ℝ) → (ι → ℝ)) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (z : ι → ℝ) :
    Work.Diff.STE.B3.SymCalc.lapC (fun z => g (σ z)) z
      = (∑ a, ∑ b, (((∑ i, Work.Diff.STE.pdR i (fun z => σ z a) z
              * Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ)) : ℂ)
            * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) (σ z))
        + (∑ a, (((∑ i, Work.Diff.STE.pdR i (Work.Diff.STE.pdR i (fun z => σ z a)) z : ℝ)) : ℂ)
            * Work.Diff.STE.pd a g (σ z)) := by
  have hstep : ∀ i : ι, Work.Diff.STE.pd i (Work.Diff.STE.pd i (fun z => g (σ z))) z
      = (∑ a, ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
            * (∑ b, ((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
                * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z)))
        + (∑ a, ((Work.Diff.STE.pdR i (Work.Diff.STE.pdR i (fun z => σ z a)) z : ℝ) : ℂ)
            * Work.Diff.STE.pd a g (σ z)) := by
    intro i
    have hsd : ∀ a : ι, ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd a g) :=
      fun a => Work.Diff.STE.ste_contDiff_pd a hg
    have hcd : ∀ a : ι, ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ι → ℝ => ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ)) :=
      fun a => Complex.ofRealCLM.contDiff.comp
        (contDiff_pdR_of_contDiff (fun z => σ z a) (contDiff_coord σ hσ a) i)
    have hprod : ∀ a : ι, ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ =>
        ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ) * Work.Diff.STE.pd a g (σ y)) :=
      fun a => (hcd a).mul ((hsd a).comp hσ)
    have hkey : Work.Diff.STE.pd i (Work.Diff.STE.pd i (fun z => g (σ z))) z
        = fderiv ℝ (fun y : ι → ℝ => ∑ a, ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ)
            * Work.Diff.STE.pd a g (σ y)) z (Pi.single i 1) := by
      show fderiv ℝ (Work.Diff.STE.pd i (fun z => g (σ z))) z (Pi.single i 1) = _
      rw [pd_comp_chain g hg σ hσ i]
    have hsum : (∑ a : ι, fderiv ℝ (fun y : ι → ℝ =>
            ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ) * Work.Diff.STE.pd a g (σ y)) z)
          (Pi.single i 1)
        = ∑ a : ι, fderiv ℝ (fun y : ι → ℝ =>
            ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ) * Work.Diff.STE.pd a g (σ y)) z
          (Pi.single i 1) :=
      map_sum (show ((ι → ℝ) →L[ℝ] ℂ) →+ ℂ from
        { toFun := fun T => T (Pi.single i 1), map_zero' := rfl,
          map_add' := fun _ _ => rfl })
        (fun a => fderiv ℝ (fun y : ι → ℝ =>
          ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ) * Work.Diff.STE.pd a g (σ y)) z)
        Finset.univ
    have hper : ∀ a : ι, fderiv ℝ (fun y : ι → ℝ =>
            ((Work.Diff.STE.pdR i (fun z => σ z a) y : ℝ) : ℂ) * Work.Diff.STE.pd a g (σ y)) z
          (Pi.single i 1)
        = ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
            * (∑ b, ((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
                * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z))
          + ((Work.Diff.STE.pdR i (Work.Diff.STE.pdR i (fun z => σ z a)) z : ℝ) : ℂ)
              * Work.Diff.STE.pd a g (σ z) := by
      intro a
      have hh_a : DifferentiableAt ℝ (fun y : ι → ℝ => Work.Diff.STE.pd a g (σ y)) z :=
        (ContDiff.contDiffAt ((hsd a).comp hσ) (x := z)).differentiableAt (by simp)
      have hc_a : DifferentiableAt ℝ (Work.Diff.STE.pdR i (fun z => σ z a)) z :=
        (ContDiff.contDiffAt (contDiff_pdR_of_contDiff (fun z => σ z a)
          (contDiff_coord σ hσ a) i) (x := z)).differentiableAt (by simp)
      rw [fderiv_ofReal_mul_apply i _ _ hc_a hh_a]
      have hchain_a : fderiv ℝ (fun y : ι → ℝ => Work.Diff.STE.pd a g (σ y)) z (Pi.single i 1)
          = ∑ b, ((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
              * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z) := by
        show Work.Diff.STE.pd i (fun y : ι → ℝ => Work.Diff.STE.pd a g (σ y)) z = _
        rw [pd_comp_chain (Work.Diff.STE.pd a g) (hsd a) σ hσ i]
      have hWa : ((fderiv ℝ (Work.Diff.STE.pdR i (fun z => σ z a)) z) (Pi.single i 1))
          = Work.Diff.STE.pdR i (Work.Diff.STE.pdR i (fun z => σ z a)) z := rfl
      rw [hchain_a, mul_comm (Work.Diff.STE.pd a g (σ z)), hWa]
    rw [hkey, fderiv_fun_sum]
    · rw [hsum, Finset.sum_congr rfl (fun a _ => hper a), Finset.sum_add_distrib]
    · intro a _
      exact (ContDiff.contDiffAt (hprod a) (x := z)).differentiableAt (by simp)
  simp only [Work.Diff.STE.B3.SymCalc.lapC]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : (∑ i : ι, ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
          * (∑ b : ι, ((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
              * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z)))
        = ∑ i : ι, ∑ b : ι, ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
            * (((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
              * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (∑ i : ι, ((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
          * (((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ)
            * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z)))
        = ∑ i : ι, ((((Work.Diff.STE.pdR i (fun z => σ z a) z : ℝ) : ℂ)
            * ((Work.Diff.STE.pdR i (fun z => σ z b) z : ℝ) : ℂ))
            * Work.Diff.STE.pd b (Work.Diff.STE.pd a g) (σ z)) from
      Finset.sum_congr rfl fun i _ => by ring]
    rw [← Finset.sum_mul]
    congr 1
    · rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_mul]
    · rw [pd_clairaut hg a b (σ z)]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    rw [Complex.ofReal_sum]

/-! ## The one-step chain rule at the level of `A` and `B` -/

/-- The `k = 1` step of the conjugation, with the coefficients `A`, `B` matched to the derivatives
of `σ` by `hAW`, `hBW`:

  `- lapC (g ∘ σ) (τ y) = varLap A B g y`  for `y ∈ W`.

This is the instantiation at `z = τ y` of the second-order chain rule
(`∂_i∂_i (g∘σ) = Σ_{a,b} ∂_a∂_b g(σ) ∂_iσ_a ∂_iσ_b + Σ_a ∂_a g(σ) ∂_i∂_iσ_a`, summed over `i`),
together with `σ (τ y) = y`. -/
theorem chain_step {τ σ : (ι → ℝ) → (ι → ℝ)} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {W : Set (ι → ℝ)}
    (hAW : ∀ y ∈ W, ∀ a b, A a b y = ∑ r, Work.Diff.STE.pdR r (fun z => σ z a) (τ y)
        * Work.Diff.STE.pdR r (fun z => σ z b) (τ y))
    (hBW : ∀ y ∈ W, ∀ a, B a y = ∑ r, Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σ z a)) (τ y))
    (hστ : ∀ y ∈ W, σ (τ y) = y)
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∀ y ∈ W, - Work.Diff.STE.B3.SymCalc.lapC (fun z => g (σ z)) (τ y)
      = varLap A B g y := by
  intro y hy
  rw [lapC_comp_chain_local g hg σ hσ (τ y), hστ y hy]
  have hS1 : (∑ a, ∑ b, (((∑ i, Work.Diff.STE.pdR i (fun z => σ z a) (τ y)
          * Work.Diff.STE.pdR i (fun z => σ z b) (τ y) : ℝ)) : ℂ)
        * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) y)
      = ∑ a, ∑ b, ((A a b y : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) y := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hAW y hy a b]
  have hS2 : (∑ a, (((∑ i, Work.Diff.STE.pdR i (Work.Diff.STE.pdR i (fun z => σ z a)) (τ y) : ℝ)) : ℂ)
        * Work.Diff.STE.pd a g y) = ∑ a, ((B a y : ℝ) : ℂ) * Work.Diff.STE.pd a g y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hBW y hy a]
  rw [hS1, hS2, varLap]

theorem lapPow_comp_eq_varLapPow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (τ σ : (ι → ℝ) → (ι → ℝ))
    (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (W : Set (ι → ℝ)) (hW : IsOpen W) (hτW : IsOpen (τ '' W))
    (hστ : ∀ y ∈ W, σ (τ y) = y)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a))
    (hAW : ∀ y ∈ W, ∀ a b, A a b y = ∑ r, Work.Diff.STE.pdR r (fun z => σ z a) (τ y)
        * Work.Diff.STE.pdR r (fun z => σ z b) (τ y))
    (hBW : ∀ y ∈ W, ∀ a, B a y = ∑ r, Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σ z a)) (τ y))
    (w G : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwp : Work.Diff.STE.Periodic1 w)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hwG : ∀ z ∈ τ '' W, w z = G (σ z)) :
    ∀ y ∈ W, Work.Diff.STE.B3.SymCalcStep5.lapPow k w (τ y)
      = Work.Diff.STE.B3.VarCoef.varLapPow k A B G y := by
  have key : ∀ j : ℕ, ∀ z ∈ τ '' W, (negLap^[j] w) z = varLapPow j A B G (σ z) := by
    intro j
    induction j with
    | zero =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Function.iterate_zero_apply]
      show w (τ y) = varLapPow 0 A B G (σ (τ y))
      rw [show varLapPow 0 A B G = G from Function.iterate_zero_apply (varLap A B) G]
      exact hwG (τ y) ⟨y, hy, rfl⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hstep : (negLap^[j + 1] w) (τ y)
          = - Work.Diff.STE.B3.SymCalc.lapC (negLap^[j] w) (τ y) := by
        rw [Function.iterate_succ_apply']
        simp only [negLap]
      rw [hstep]
      have hloc : (negLap^[j] w) =ᶠ[nhds (τ y)]
          (fun z' => varLapPow j A B G (σ z')) :=
        Filter.eventually_of_mem (hτW.mem_nhds ⟨y, hy, rfl⟩) (fun z' hz' => ih z' hz')
      rw [lapC_congr hloc,
        chain_step hσ hAW hBW hστ (varLapPow j A B G) (varLapPow_contDiff hA hB j hG) y hy,
        hστ y hy]
      simp only [varLapPow, Function.iterate_succ_apply']
  intro y hy
  rw [lapPow_eq_iterate k w hw hwp (τ y), key k (τ y) ⟨y, hy, rfl⟩, hστ y hy]

end Work.Diff.STE.B3.VarCoef
