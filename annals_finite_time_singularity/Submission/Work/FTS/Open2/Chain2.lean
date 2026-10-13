/-
# `FTS/Open2/Chain2` — the closed chain at the `StarPkgo2` signatures

The `StarPkgo2`/`PairData2` re-run of the two wiring results of
`Submission/Work/FTS/OpenPkg/AprioriChain.lean`, i.e. the two entries of the migrated route that
the caller uses:

* `aprioriFields2_of_inputs` — N5's four a-priori fields `AprioriFields2` from the N4 pairing data
  `PairData2` and the analytic inputs of the Galerkin chapter (this is
  `Open2.aprioriFields2`, re-exported under the canonical name);
* `exists_dynGSol_open_of_aprioriFields2` — the composite: the same inputs produce a solution of
  the dynamic modulated equation with the uniform `ℋ⁴`-bound `C₀α²`, through
  `Open2.exists_dynGSol_open_of_apriori2`.

The proofs are the delivered ones with the star package and the pairing data replaced by
`StarPkgo2`/`PairData2`; the two constants `C0 …`, `alpha5 …` are the delivered ones.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Work.FTS.Open2.Defs2
import Submission.Work.FTS.Open2.Fields2
import Submission.Work.FTS.Open2.Top2
import Submission.Work.FTS.OpenPkg.Galerkin
import Submission.Work.FTS.OpenPkg.Top

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.VocabO2
open Work.FTS.OpenPkg
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof
  galFam GlobalODEExistence IsDynGSolWith dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **N5's four a-priori fields from the primed pairing data** (the migrated
`Work.FTS.Apriori.aprioriFields`). -/
theorem aprioriFields2_of_inputs (IP : ℝ → Fn → Fn → ℝ)
    {α₂ cc clo Cup Ccs Ce Cs CcN α₄ : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hPair : PairData2 IP CcN Ce Cs α₄)
    (hCe : 0 < Ce) (hCs : 0 < Cs) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hα5 : α ≤ Work.FTS.Apriori.alpha5 CcN cc clo Cup Ccs α₂ α₄)
    {Φs : Fn} {EllSol : Fn → Fn} {φ : ℕ → Fn} {g₀ : Fn}
    (hStar : StarPkgo2 α Cs Φs)
    (hEll : ∀ g, GalClass α g → EllPkgGo α Ce g (EllSol g))
    (hGal : GalBasis α IP φ) (hData : Work.FTS.LocData.DataAdm α g₀)
    (hL12 : Work.Construction.L12 g₀ 0 = 0)
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
        (galFam φ n (fun _ => c)) τ))
    (hE : Work.FTS.Apriori.GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀) :
    AprioriFields2 IP α (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) clo cc CcN Ce Cs φ Φs EllSol g₀ :=
  aprioriFields2 IP hIP hPair hCe hCs hα hα1 hα5 hStar hEll hGal
    hData hL12 hRegQ hXn hRegLin hRegRHS hE

/-- **The closed open-quadrant chain**: the primed pairing data plus the analytic inputs of the
Galerkin chapter produce a solution of the dynamic modulated equation with the uniform `ℋ⁴`-bound
`C₀α²`. -/
theorem exists_dynGSol_open_of_aprioriFields2 (hODE : GlobalODEExistence)
    {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {CcN clo cc Ce Cs α₂ Cup Ccs α₄ : ℝ}
    {IP : ℝ → Fn → Fn → ℝ} (hIP : UnifIP IP α₂ cc clo Cup Ccs)
    (hPair : PairData2 IP CcN Ce Cs α₄) (hCe : 0 < Ce) (hCs : 0 < Cs)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hα5 : α ≤ Work.FTS.Apriori.alpha5 CcN cc clo Cup Ccs α₂ α₄)
    {φ : ℕ → Fn} (hφ : GalBasis α IP φ) (hφ_dense : DenseSpan α IP φ)
    {Φs : Fn} {EllSol : Fn → Fn}
    (hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
      Law (Work.Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ))
    {L : ℕ → ℝ} (hL : ∀ n : ℕ, 0 < L n) {K : ℕ → ℝ} (hK : ∀ n : ℕ, 0 ≤ K n)
    (hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
      LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
        (Metric.closedBall 0 (2 * Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α)))
    (hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
      c ∈ Metric.closedBall 0 (2 * Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) →
      ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n)
    (hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ),
      c ∈ Metric.closedBall 0 (2 * Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) →
      ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0))
    (hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c → EquicontSpace (profileFam φ c))
    (hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c → EquicontTau (profileFam φ c))
    (hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g)
    (hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ)
    (hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ)
    (hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol)
      (Ropen clo (Work.FTS.Apriori.C0 CcN cc clo Cup Ccs) α) c →
      ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
      IsDynWeakOn α (IP α) φ g Φ ∧
        (∀ τ : ℝ, 0 ≤ τ → Law (Work.Construction.Ftau α g τ) (slice Φ τ)))
    (hDetermines : WeakDetermines α (IP α) φ)
    (hStar : StarPkgo2 α Cs Φs)
    (hEll : ∀ g, GalClass α g → EllPkgGo α Ce g (EllSol g))
    (hData : Work.FTS.LocData.DataAdm α g₀) (hL12 : Work.Construction.L12 g₀ 0 = 0)
    (hRegQ : RegQ α 4 g₀) (hXn : Xn α g₀ ≤ α ^ 2)
    (hRegLin : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynLin α (galFam φ n (fun _ => c)) τ))
    (hRegRHS : ∀ (n : ℕ) (c : Fin n → ℝ) (τ : ℝ),
      RegQ α 4 (dynRHS α (PsiCan Φs EllSol (galFam φ n (fun _ => c)))
        (galFam φ n (fun _ => c)) τ))
    (hE : Work.FTS.Apriori.GalEnergyIneq IP α cc CcN φ (PsiCan Φs EllSol) g₀) :
    ∃ g Φ : Fam, IsDynGSolWith Law α Φ g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      RegPkg α g ∧
      (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ)
        ≤ Work.FTS.Apriori.C0 CcN cc clo Cup Ccs * α ^ 2) :=
  exists_dynGSol_open_of_apriori2 hODE hIP (Work.FTS.Apriori.C0_pos hPair.hCcN hIP.pos.2.1
      hIP.pos.2.2.1 hIP.pos.2.2.2.1 hIP.pos.2.2.2.2) hα hφ hφ_dense hPsi hL hK
    hField_lip hField_bound hField_cont hProfileSpace hProfileTau hRegLimit hDataLimit hPsiLim
    hGalWeak hDetermines
    (aprioriFields2_of_inputs IP hIP hPair hCe hCs hα hα1 hα5 hStar hEll hφ hData hL12 hRegQ
      hXn hRegLin hRegRHS hE)
    hCs hCe hStar hEll

end Work.FTS.Open2
