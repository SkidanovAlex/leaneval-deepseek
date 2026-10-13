/-
# `FTS/Open2/Bridge2` — the N5 bridge at the `StarPkgo2` signatures

The `StarPkgo2`/`PairData2` re-run of the two lemmas of
`Submission/Work/FTS/OpenPkg/AprioriOpen/Bridge.lean`:

* `galerkin_energy_ineq2` — N2's coercivity plus N4's `PairData2` pairing estimate imply the
  Galerkin energy inequality `GalEnergyIneq`;
* `galerkin_bound_of_inputs2` — the a-priori bound (with the constants `alpha5`, `C0` exhibited),
  from `UnifIP` and `PairData2`.

The proofs are those of the delivered lemmas with `PairData'`/`StarPkgo` replaced by
`PairData2`/`StarPkgo2`: the star package occurs only as the hypothesis of `PairData2.bound`, and
the delivered `galerkin_bound_explicit` (which *consumes* a `StarPkgo`) is re-used by
`StarPkgo2.toStarPkgo`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Open2.Defs2
import Submission.Work.FTS.OpenPkg.AprioriOpen.GalSpanOpen
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bound
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bridge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Apriori
open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.OpenPkg
open Work.FTS.OpenPkg.AprioriOpen
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The bridge at the new signatures** (design §4 L-N5.4): N2's coercivity plus N4's pairing
estimate `PairData2` (over `StarPkgo2`) imply the Galerkin energy inequality. -/
theorem galerkin_energy_ineq2 (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs CcN Ce Cs α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : PairData2 IP CcN Ce Cs α₄)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂) (hα₄ : α ≤ α₄) {Φs : Fn} {EllSol : Fn → Fn}
    {φ : ℕ → Fn} {g₀ : Fn}
    (hStar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
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

/-- **The a-priori bound at the new signatures**: `galerkin_bound_of_inputs` with `PairData2` and
the inner hypothesis `StarPkgo2`; the constants `α₅ = alpha5 …`, `C₀ = C0 …` are the delivered
ones. -/
theorem galerkin_bound_of_inputs2 (IP : ℝ → Fn → Fn → ℝ)
    {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : PairData2 IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) :
    ∃ α₅ C₀ : ℝ, 0 < α₅ ∧ 0 < C₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₅ →
      ∀ (Φs : Fn) (EllSol : Fn → Fn) (φ : ℕ → Fn) (g₀ : Fn),
        Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
        (∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g)) →
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
    hStar.toStarPkgo hEll hGal hData hL12 hRegQ hXn
    (galerkin_energy_ineq2 IP hIP hPair hαIoc hα₄ hStar hEll hGal hRegLin hRegRHS)

end Work.FTS.Open2
