/-
# The a-priori fields of N6's `DynInputs`

This module packages the four a-priori fields that the existence theorem for the dynamic modulated
equation (`Submission/Work/FTS/Galerkin/Existence.lean`) consumes, in the shapes of design §1.3
and §4:

* `hInit` — the projected datum lies in the a-priori ball (design L-N5.6);
* `hCoeffBound` — the coefficients of every Galerkin solution stay in that ball (L-N5.7);
* `hProfileBdd` — the Galerkin profiles are uniformly bounded on compact subsets of the slab
  (L-N5.10, from the paper's `Linf_H2`);
* `hLimBound` — the limit of a locally uniformly convergent subsequence obeys the same `ℋ⁴`-bound
  (L-N5.9, by lower semicontinuity of the `ℋ⁴`-norm);

and `aprioriFields`, which assembles them into the structure `AprioriFields`.

The auxiliary hypotheses of `hCoeffBound`/`hLimBound` are the analytic inputs that the a-priori
chapter does not itself provide:

* `Work.FTS.OpenPkg.PairData'` (N4's pairing estimate) and the two `RegQ`-membership facts for `dynLin`, `dynRHS`
  (the interior-class cost of `𝓛_Γ^T` and `gRHS`), consumed by `galerkin_energy_ineq`;
* `SmoothQuad (slice g τ)` for the limit — the interior regularity of the limit profile, which is
  N6/N7's regularity package (`RegPkg.smooth` is stated with the analytic order `⊤`, which the
  design's §5 T11 asks to replace by `Work.Stability.smoothOrder`; the interior `SmoothQuad`
  hypothesis here is the sharp form of exactly that transfer).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Apriori.Arith
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bound
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bridge
import Submission.Work.FTS.OpenPkg.AprioriOpen.GalSpanOpen
import Submission.Work.FTS.Apriori.Coord
import Submission.Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open
import Submission.Work.FTS.Apriori.Profile.linf_H2_quad
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **`hInit` (field shape)**: the projected datum lies in the a-priori ball `√clo·C₀·α²`. -/
theorem hInit_field (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) {g₀ : Fn}
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2) {φ : ℕ → Fn} (hφ : GalBasis α IP φ) :
    ∀ n, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2
      ≤ (Rstar clo (C0 CcN cc clo Cup Ccs) α) ^ 2 := by
  intro n
  rw [Rstar]
  exact hInit IP hIP hα hRegQ hXn hφ n

/-- **`hCoeffBound` (field shape)**: the coefficients of every Galerkin solution on `[0,T]` stay in
the a-priori ball, with constants independent of `τ, n, T` and `α`. -/
theorem hCoeffBound_field (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : Work.FTS.OpenPkg.PairData' IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) {α : ℝ} (hα : 0 < α)
    (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) {Φs : Fn} {EllSol : Fn → Fn} {φ : ℕ → Fn}
    {g₀ : Fn} (hStar : Work.FTS.VocabO.StarPkgo α Cs Φs) (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hGal : GalBasis α IP φ) (hData : LocData.DataAdm α g₀) (hL12 : Construction.L12 g₀ 0 = 0)
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
        (galFam φ n (fun _ => c)) τ))
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (c : ℝ → Fin n → ℝ)
    (hc : IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c) :
    ∀ τ ∈ Set.Icc 0 T,
      ∑ k : Fin n, (c τ k) ^ 2 ≤ (Rstar clo (C0 CcN cc clo Cup Ccs) α) ^ 2 := by
  have hαIoc : α ∈ Set.Ioc 0 α₂ :=
    ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩
  have hα₄ : α ≤ α₄ := le_trans hα5 (le_trans alpha5_le_alpha4 le_rfl)
  have hmain := galerkin_bound_explicit IP hIP hCe hCs hPair.hCcN hPair.hα₄ α hα hα5
    Φs EllSol φ g₀ hStar hEll hGal hData hL12 hRegQ hXn
    (galerkin_energy_ineq IP hIP hPair hαIoc hα₄ hStar hEll hGal hRegLin hRegRHS)
  rw [Rstar]
  exact fun τ hτ => (hmain n T hT c hc τ hτ).1

/-- **`hLimBound` (field shape)** (design §1.3, L-N5.9): the limit of a locally uniformly
convergent subsequence of Galerkin profiles obeys the a-priori `ℋ⁴`-bound, by lower
semicontinuity. -/
theorem hLimBound_field (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) {φ : ℕ → Fn}
    (hGal : GalBasis α IP φ) {Psi : Fam → Fam}
    {c : ∀ n : ℕ, ℝ → Fin n → ℝ}
    (hfam : IsGalFam α (IP α) φ Psi (Rstar clo (C0 CcN cc clo Cup Ccs) α) c)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {g : Fam}
    (hconv : ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g)
    (hsm : ∀ τ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) :
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
  have hclo := hIP.pos.2.2.1
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs :=
    C0_pos' (CcN := CcN) (cc := cc) (Cup := Cup) hclo hIP.pos.2.2.2.2
  have hiso : Work.FTS.Galerkin.IsIPOrthonormal (IP α) φ :=
    isIPOrthonormal_of_galBasis hIP hα hGal
  intro τ hτ
  refine Work.FTS.OpenPkg.HkNorm_le_of_tendstoLocUnif_open (α := α)
    (B := C0 CcN cc clo Cup Ccs * α ^ 2) (G := fun n => galFun φ (c (ψ n) τ))
    (f := slice g τ) hα.1 ?_ ?_ (hsm τ hτ) ?_
  · intro n
    exact regQ_mono (k := 6) (by norm_num) (hGal.cls (ψ n) (c (ψ n) τ)).reg
  · intro n
    -- the uniform bound along the sequence, from the coefficient ball
    have hcoer : CoerAdm α (galFun φ (c (ψ n) τ)) :=
      coerAdm_of_galClass (hGal.cls (ψ n) (c (ψ n) τ))
    have hlo := hIP.lo α hα _ hcoer
    have henergy := hiso.self (ψ n) (c (ψ n) τ)
    have hR := hfam.2 (ψ n) τ hτ
    have hR' : clo * Work.Spaces.HkSq α 4 (galFun φ (c (ψ n) τ))
        ≤ clo * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
      rw [henergy] at hlo
      have hRsq : (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2
          = clo * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
        rw [Rstar_sq hclo.le hC₀.le, mul_pow]
        ring
      rw [Rstar] at hR
      rw [hRsq] at hR
      exact le_trans hlo hR
    have hHk : Work.Spaces.HkSq α 4 (galFun φ (c (ψ n) τ))
        ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 :=
      le_of_mul_le_mul_left hR' hclo
    calc Xn α (galFun φ (c (ψ n) τ))
        = Real.sqrt (Work.Spaces.HkSq α 4 (galFun φ (c (ψ n) τ))) := rfl
      _ ≤ Real.sqrt ((C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt hHk
      _ = C0 CcN cc clo Cup Ccs * α ^ 2 := Real.sqrt_sq (by positivity)
  · -- the local uniform convergence of the slices
    intro K hK hKsub
    exact convLocUnif_slice hconv τ hτ K hK hKsub

/-- **`hProfileBdd` (field shape)** (design L-N5.10): the Galerkin profiles are uniformly bounded
on compact subsets of the slab — in fact on the whole slab — by the paper's `Linf_H2` estimate
`sup|g| ≤ C/√(γ−1)·|g|_{ℋ²}` applied to the a-priori `ℋ⁴`-bound. -/
theorem hProfileBdd_field (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1)
    {φ : ℕ → Fn} (hGal : GalBasis α IP φ) {Psi : Fam → Fam}
    {c : ∀ n : ℕ, ℝ → Fin n → ℝ}
    (hfam : IsGalFam α (IP α) φ Psi (Rstar clo (C0 CcN cc clo Cup Ccs) α) c) :
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |prof φ c n p| ≤ Cb := by
  intro K _ hKsub
  refine ⟨Real.sqrt (500 / (Work.Spaces.gam α - 1)) * (C0 CcN cc clo Cup Ccs * α ^ 2) + 1,
    fun n p hpK => ?_⟩
  have hclo := hIP.pos.2.2.1
  have hC₀ : 0 < C0 CcN cc clo Cup Ccs :=
    C0_pos' (CcN := CcN) (cc := cc) (Cup := Cup) hclo hIP.pos.2.2.2.2
  have hiso : Work.FTS.Galerkin.IsIPOrthonormal (IP α) φ :=
    isIPOrthonormal_of_galBasis hIP hα hGal
  obtain ⟨hz, hθ, hτ⟩ := (Work.FTS.Galerkin.mem_Slab).mp (hKsub hpK)
  have hcls : GalClass α (galFun φ (c n p.2.2)) := hGal.cls n (c n p.2.2)
  have hmem4 : Work.Spaces.HkMem α 4 (galFun φ (c n p.2.2)) :=
    (regQ_mono (k := 6) (by norm_num) hcls.reg).2.1
  -- the a-priori `ℋ⁴`-bound
  have hHk : Work.Spaces.HkSq α 4 (galFun φ (c n p.2.2))
      ≤ (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
    have hcoer : CoerAdm α (galFun φ (c n p.2.2)) := coerAdm_of_galClass hcls
    have hlo := hIP.lo α hα _ hcoer
    have henergy := hiso.self n (c n p.2.2)
    have hR := hfam.2 n p.2.2 hτ
    have hR' : clo * Work.Spaces.HkSq α 4 (galFun φ (c n p.2.2))
        ≤ clo * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
      rw [henergy] at hlo
      have hRsq : (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2
          = clo * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
        rw [Rstar_sq hclo.le hC₀.le, mul_pow]
        ring
      rw [Rstar] at hR
      rw [hRsq] at hR
      exact le_trans hlo hR
    exact le_of_mul_le_mul_left hR' hclo
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: the axis condition
    have haxis := (hcls.axis p.2.1 hθ).1
    show |galFun φ (c n p.2.2) p.1 p.2.1| ≤ _
    rw [← hz0]
    rw [haxis, abs_zero]
    positivity
  · -- `z > 0`: the pointwise `Linf_H2` estimate
    have hdec2 : Work.Spaces.DecayInZ 2 (galFun φ (c n p.2.2)) :=
      fun j i hij => hcls.decay.1 j i (by omega)
    have hpoint := Work.FTS.Apriori.Profile.linf_pointwise (α := α) hα.1 hα1
      (hcls.reg.1) hcls.vanish hdec2 (regQ_mono (k := 6) (by norm_num) hcls.reg).2.1
      p.1 hzpos p.2.1 hθ
    have hmono : Work.Spaces.HkSq α 2 (galFun φ (c n p.2.2))
        ≤ Work.Spaces.HkSq α 4 (galFun φ (c n p.2.2)) :=
      Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem4
    have hγ : 0 < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one α]
      linarith [hα.1]
    have habs : |galFun φ (c n p.2.2) p.1 p.2.1|
        ≤ Real.sqrt (500 / (Work.Spaces.gam α - 1))
          * (C0 CcN cc clo Cup Ccs * α ^ 2) := by
      have h1 : |galFun φ (c n p.2.2) p.1 p.2.1| ^ 2
          ≤ 500 / (Work.Spaces.gam α - 1) * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 := by
        refine le_trans hpoint ?_
        have hnn : 0 ≤ 500 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ.le
        calc 500 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 2 (galFun φ (c n p.2.2))
            ≤ 500 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 (galFun φ (c n p.2.2)) :=
              mul_le_mul_of_nonneg_left hmono hnn
          _ ≤ 500 / (Work.Spaces.gam α - 1) * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left hHk hnn
      calc |galFun φ (c n p.2.2) p.1 p.2.1|
          = Real.sqrt (|galFun φ (c n p.2.2) p.1 p.2.1| ^ 2) :=
            (Real.sqrt_sq (abs_nonneg _)).symm
        _ ≤ Real.sqrt (500 / (Work.Spaces.gam α - 1)
              * (C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt (500 / (Work.Spaces.gam α - 1))
              * (C0 CcN cc clo Cup Ccs * α ^ 2) := by
            rw [Real.sqrt_mul (div_nonneg (by norm_num) hγ.le),
              Real.sqrt_sq (by positivity)]
    show |galFun φ (c n p.2.2) p.1 p.2.1| ≤ _
    linarith [habs]

/-- **The four a-priori fields, assembled** (design §4 L-N5.10): the structure `AprioriFields` of
`Submission/Work/FTS/Apriori/Defs.lean`, whose four fields have literally the shapes of the
corresponding fields of `Work.FTS.Galerkin.DynInputs`. -/
theorem aprioriFields' (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : Work.FTS.OpenPkg.PairData' IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) {Φs : Fn} {EllSol : Fn → Fn} {φ : ℕ → Fn}
    {g₀ : Fn} (hStar : Work.FTS.VocabO.StarPkgo α Cs Φs) (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hGal : GalBasis α IP φ) (hData : LocData.DataAdm α g₀) (hL12 : Construction.L12 g₀ 0 = 0)
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
        (galFam φ n (fun _ => c)) τ))
    (hE : GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀) :
    Work.FTS.OpenPkg.AprioriFields' IP α (C0 CcN cc clo Cup Ccs) clo cc CcN Ce Cs φ Φs EllSol g₀ :=
  ⟨hInit_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hRegQ hXn hGal,
   fun n T hT c hc => hCoeffBound_field IP hIP hPair hCe hCs hα hα5 hStar hEll hGal hData hL12
     hRegQ hXn hRegLin hRegRHS n T hT c hc,
   fun c hfam K hK hKsub =>
     hProfileBdd_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hα1
       hGal hfam K hK hKsub,
   fun c hfam ψ g hψ hconv hsm τ hτ =>
     hLimBound_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hGal hfam
       hψ hconv hsm τ hτ⟩

end Work.FTS.OpenPkg.AprioriOpen
