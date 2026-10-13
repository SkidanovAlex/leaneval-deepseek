/-
# The bridge: from N2's coercivity and N4's pairing estimate to the Galerkin energy inequality
(design §4 L-N5.4)

This module discharges the hypothesis `GalEnergyIneq` of `galerkin_bound` — the assembled energy
inequality along Galerkin solutions — from

* N2's `UnifIP` (coercivity of `𝓛_Γ^T` and the upper bound for `IP`), and
* N4's `Work.FTS.OpenPkg.PairData'` (the modulation bound and the pairing estimate for the assembled right-hand
  side `gRHS`),

together with two *structural* inputs which are statements about the interior class `RegQ` (and are
the only place where the analytic content of `𝓛_Γ^T` and `gRHS` enters):

* `hRegLin` — the class of `dynLin = −𝓛_Γ^T gₙ` (equivalently: `RegQ α 4 (LGammaT α gₙ)`, needed by
  `UnifIP.smul_fst` to pull the minus sign out);
* `hRegRHS` — the class of `dynRHS = gRHS …` (needed by `UnifIP.add_fst` to split `galRHS`).

The assembly is:
`2Σ_k c_k ċ_k = 2 IP(galRHS, gₙ) = 2 IP(dynLin, gₙ) + 2 IP(dynRHS, gₙ) ≤ −2cc|gₙ|² + 2C_N·Pbd α |gₙ|`,
where the first equality is the pairing of the Galerkin span (`ip_galFun_snd`, which needs the
`RegQ`-linearity of `IP` on the span), the second is `UnifIP.add_fst`, the third is `UnifIP.coer`
on `−𝓛_Γ^T gₙ` and N4's estimate for `IP(gRHS, gₙ)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.AprioriOpen.GalSpanOpen
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bound
import Submission.Work.FTS.Galerkin.Projection

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

/-- **Second-argument linearity of `UnifIP` over the Galerkin span**: for `f ∈ RegQ α 4` and a
`GalBasis` `φ`, the pairing of `f` with a Galerkin combination is the Euclidean pairing with the
coefficients. -/
theorem ip_galFun_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) {φ : ℕ → Fn}
    (hGal : GalBasis α IP φ) {f : Fn} (hf : RegQ α 4 f) (n : ℕ) (c : Fin n → ℝ) :
    IP α f (galFun φ c) = ∑ k : Fin n, c k * IP α f (φ (k : ℕ)) := by
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hGal
  have key : ∀ s : Finset (Fin n),
      IP α f (fun z θ => ∑ i ∈ s, c i * φ (i : ℕ) z θ)
        = ∑ i ∈ s, c i * (IP α f (φ (i : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := ip_smul_snd hIP hα (0 : ℝ) hf (regQ_zero α 4)
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', c i * φ (i : ℕ) z θ)
            = fun z θ => c a * φ (a : ℕ) z θ
              + (∑ i ∈ s', c i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => c a * φ (a : ℕ) z θ) := regQ_smul (c a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', c i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' c (fun i => φ i) (fun i _ => hphi i)
        rw [ip_add_snd hIP hα hf h1 h2, ip_smul_snd hIP hα (c a) hf (hphi (a : ℕ)), ih,
          Finset.sum_insert ha]
  have hmain : IP α f (galFun φ c) = ∑ i : Fin n, c i * (IP α f (φ (i : ℕ))) := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α f (galFun φ c)
        = IP α f (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            c i * φ (i : ℕ) z θ) from rfl]
    exact h
  exact hmain

/-- **The bridge** (design §4 L-N5.4): N2's coercivity plus N4's pairing estimate imply the
Galerkin energy inequality.  See the module docstring for the two structural hypotheses. -/
theorem galerkin_energy_ineq (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN Ce Cs α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : Work.FTS.OpenPkg.PairData' IP CcN Ce Cs α₄)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα₄ : α ≤ α₄) {Φs : Fn} {EllSol : Fn → Fn}
    {φ : ℕ → Fn} {g₀ : Fn}
    (hStar : Work.FTS.VocabO.StarPkgo α Cs Φs) (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hGal : GalBasis α IP φ)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c))) (galFam φ n (fun _ => c)) τ)) :
    GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀ := by
  intro n T c hc τ hτ h7
  have hcc := hIP.pos.2.1
  have hcls : GalClass α (galFun φ (c τ)) := hGal.cls n (c τ)
  have hcoer : CoerAdm α (galFun φ (c τ)) := coerAdm_of_galClass hcls
  have hcls4 : RegQ α 4 (galFun φ (c τ)) := regQ_mono (k := 6) (by norm_num) hcls.reg
  have hregL : RegQ α 4 (dynLin α (galFam φ n (fun _ => c τ)) τ) := hRegLin n (c τ) τ
  have hregR : RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) := hRegRHS n (c τ) τ
  have hregSum : RegQ α 4 (dynLin α (galFam φ n (fun _ => c τ)) τ
      + dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) := regQ_add hregL hregR
  -- `∑ c_k ċ_k = IP (galRHS) gₙ`
  have hpair1 : (∑ k : Fin n, c τ k
        * galField α (IP α) φ n (PsiCan Φs EllSol) τ (c τ) k)
      = IP α (galRHS α φ n (PsiCan Φs EllSol) τ (c τ)) (galFun φ (c τ)) := by
    have h1 : IP α (galRHS α φ n (PsiCan Φs EllSol) τ (c τ)) (galFun φ (c τ))
        = ∑ k : Fin n, c τ k
          * IP α (galRHS α φ n (PsiCan Φs EllSol) τ (c τ)) (φ (k : ℕ)) :=
      ip_galFun_snd hIP hα hGal hregSum n (c τ)
    rw [h1]
    exact Finset.sum_congr rfl fun k _ => by rfl
  -- the split of `galRHS = dynLin + dynRHS`
  have hsplit : IP α (galRHS α φ n (PsiCan Φs EllSol) τ (c τ)) (galFun φ (c τ))
      = IP α (dynLin α (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ))
        + IP α (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ)) := by
    have h := hIP.add_fst α hα (dynLin α (galFam φ n (fun _ => c τ)) τ)
      (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ))
      hregL hregR hcls4
    simpa [galRHS] using h
  -- coercivity of `dynLin = -𝓛_Γ^T`
  have hregLT : RegQ α 4 (Work.Coercivity.LGammaT α (galFun φ (c τ))) := by
    have hneg := regQ_neg hregL
    simpa [dynLin] using hneg
  have hdynLin : IP α (dynLin α (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ))
      = - IP α (Work.Coercivity.LGammaT α (galFun φ (c τ))) (galFun φ (c τ)) := by
    have h := hIP.smul_fst α hα (-1) (Work.Coercivity.LGammaT α (galFun φ (c τ)))
      (galFun φ (c τ)) hregLT hcls4
    have hfun : (fun z θ => (-1) * Work.Coercivity.LGammaT α (galFun φ (c τ)) z θ)
        = dynLin α (galFam φ n (fun _ => c τ)) τ := by
      funext z θ
      show (-1) * Work.Coercivity.LGammaT α (galFun φ (c τ)) z θ
        = -(Work.Coercivity.LGammaT α (galFun φ (c τ)) z θ)
      ring
    rw [hfun] at h
    simpa using h
  have hcoer' : cc * Work.Spaces.HkSq α 4 (galFun φ (c τ))
      ≤ IP α (Work.Coercivity.LGammaT α (galFun φ (c τ))) (galFun φ (c τ)) :=
    hIP.coer α hα _ hcoer
  -- N4's estimate for the right-hand side
  have hN4 := (hPair.bound α hα.1 hα₄ (galFun φ (c τ)) Φs
    (EllSol (galFun φ (c τ))) hcls hStar (hEll (galFun φ (c τ)) hcls) h7).2.2
  have hdynRHS : IP α (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ))
      ≤ CcN * Pbd α (Xn α (galFun φ (c τ))) := by
    have h : rhsPair IP α (galFun φ (c τ)) (fun z θ => Φs z θ + EllSol (galFun φ (c τ)) z θ)
        = IP α (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c τ))) (galFam φ n (fun _ => c τ)) τ) (galFun φ (c τ)) := rfl
    rw [← h]
    exact le_of_abs_le hN4
  -- assembly
  have hkey : (∑ k : Fin n, c τ k * galField α (IP α) φ n (PsiCan Φs EllSol) τ (c τ) k)
      ≤ - cc * Work.Spaces.HkSq α 4 (galFun φ (c τ))
        + CcN * Pbd α (Xn α (galFun φ (c τ))) := by
    rw [hpair1, hsplit, hdynLin]
    linarith [hcoer', hdynRHS]
  linarith [hkey]

/-- **The a-priori bound from the two analytic inputs** (N2's `UnifIP` and N4's `Work.FTS.OpenPkg.PairData'`,
design §3.6): the statement of `galerkin_bound` with its energy-inequality hypothesis discharged by
`galerkin_energy_ineq`.  The two remaining hypotheses are the `RegQ`-membership of `dynLin` and of
`dynRHS` (the interior-class cost of `𝓛_Γ^T` and `gRHS`; design §5 T1). -/
theorem galerkin_bound_of_inputs (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : Work.FTS.OpenPkg.PairData' IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) :
    ∃ α₅ C₀ : ℝ, 0 < α₅ ∧ 0 < C₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₅ →
      ∀ (Φs : Fn) (EllSol : Fn → Fn) (φ : ℕ → Fn) (g₀ : Fn),
        Work.FTS.VocabO.StarPkgo α Cs Φs → (∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g)) →
        GalBasis α IP φ → LocData.DataAdm α g₀ → Construction.L12 g₀ 0 = 0 →
        RegQ α 4 g₀ → Xn α g₀ ≤ α ^ 2 →
        (∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
          RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ)) →
        (∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
          RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
            (galFam φ n (fun _ => c)) τ)) →
        ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
          IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
          ∀ τ ∈ Set.Icc 0 T,
            ∑ k : Fin n, (c τ k) ^ 2
                ≤ (Real.sqrt clo * C0 CcN cc clo Cup Ccs * α ^ 2) ^ 2 ∧
            Xn α (galFun φ (c τ)) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
  refine ⟨alpha5 CcN cc clo Cup Ccs α₂ α₄, C0 CcN cc clo Cup Ccs, ?_, ?_, ?_⟩
  · exact alpha5_pos hPair.hCcN hIP.pos.2.1 hIP.pos.2.2.1 hIP.pos.2.2.2.1 hIP.pos.2.2.2.2
      hIP.pos.1 hPair.hα₄
  · exact C0_pos hPair.hCcN hIP.pos.2.1 hIP.pos.2.2.1 hIP.pos.2.2.2.1 hIP.pos.2.2.2.2
  intro α hα hα5 Φs EllSol φ g₀ hStar hEll hGal hData hL12 hRegQ hXn hRegLin hRegRHS
  have hαIoc : α ∈ Set.Ioc 0 α₂ :=
    ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩
  have hα₄ : α ≤ α₄ := le_trans hα5 (le_trans alpha5_le_alpha4 le_rfl)
  exact galerkin_bound_explicit IP hIP hCe hCs hPair.hCcN hPair.hα₄ α hα hα5 Φs EllSol φ g₀
    hStar hEll hGal hData hL12 hRegQ hXn
    (galerkin_energy_ineq IP hIP hPair hαIoc hα₄ hStar hEll hGal hRegLin hRegRHS)

end Work.FTS.OpenPkg.AprioriOpen
