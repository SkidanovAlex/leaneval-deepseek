/-
# `FTS/Open2/Fields2` — the N5 a-priori fields at the `StarPkgo2` signatures

The `PairData2`/`StarPkgo2` re-run of the two lemmas of
`Submission/Work/FTS/OpenPkg/AprioriOpen/Fields.lean` that mention the star package and the
pairing data:

* `hCoeffBound_field2` — `hCoeffBound` (the coefficients of every Galerkin solution stay in the
  a-priori ball), from `galerkin_bound_explicit` and the new bridge `galerkin_energy_ineq2`;
* `aprioriFields2` — the four a-priori fields assembled into `Open2.AprioriFields2`.

The other two field lemmas (`hInit_field`, `hProfileBdd_field`, `hLimBound_field`) mention neither
`StarPkgo` nor `PairData'` and are re-used verbatim from `OpenPkg.AprioriOpen.Fields`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Open2.Bridge2
import Submission.Work.FTS.OpenPkg.AprioriOpen.Fields

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

/-- **`hCoeffBound` at the new signatures**: the coefficients of every Galerkin solution on
`[0,T]` stay in the a-priori ball `√clo·C₀·α²`, with constants independent of `τ, n, T, α`. -/
theorem hCoeffBound_field2 (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : PairData2 IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) {α : ℝ} (hα : 0 < α)
    (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) {Φs : Fn} {EllSol : Fn → Fn} {φ : ℕ → Fn}
    {g₀ : Fn} (hStar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
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
    Φs EllSol φ g₀ hStar.toStarPkgo hEll hGal hData hL12 hRegQ hXn
    (galerkin_energy_ineq2 IP hIP hPair hαIoc hα₄ hStar hEll hGal hRegLin hRegRHS)
  rw [Rstar]
  exact fun τ hτ => (hmain n T hT c hc τ hτ).1

/-- **The four a-priori fields at the new signatures** (design §4 L-N5.10): the structure
`Open2.AprioriFields2`, whose four fields have literally the shapes of the corresponding fields
of `Work.FTS.Galerkin.DynInputs`. -/
theorem aprioriFields2 (IP : ℝ → Fn → Fn → ℝ) {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : PairData2 IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) {Φs : Fn} {EllSol : Fn → Fn} {φ : ℕ → Fn}
    {g₀ : Fn} (hStar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ g, GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hGal : GalBasis α IP φ) (hData : LocData.DataAdm α g₀) (hL12 : Construction.L12 g₀ 0 = 0)
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
        (galFam φ n (fun _ => c)) τ))
    (hE : GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀) :
    AprioriFields2 IP α (C0 CcN cc clo Cup Ccs) clo cc CcN Ce Cs φ Φs EllSol g₀ :=
  ⟨hInit_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hRegQ hXn hGal,
   fun n T hT c hc => hCoeffBound_field2 IP hIP hPair hCe hCs hα hα5 hStar hEll hGal hData hL12
     hRegQ hXn hRegLin hRegRHS n T hT c hc,
   fun c hfam K hK hKsub =>
     hProfileBdd_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hα1
       hGal hfam K hK hKsub,
   fun c hfam ψ g hψ hconv hsm τ hτ =>
     hLimBound_field IP hIP ⟨hα, le_trans hα5 (le_trans alpha5_le_alpha2 le_rfl)⟩ hGal hfam
       hψ hconv hsm τ hτ⟩

end Work.FTS.Open2
