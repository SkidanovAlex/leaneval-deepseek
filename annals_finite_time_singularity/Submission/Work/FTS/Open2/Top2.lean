/-
# `FTS/Open2/Top2` — the top-level (N0) wiring at the `StarPkgo2` signatures

The `StarPkgo2`/`PairData2` re-run of the two wiring definitions of
`Submission/Work/FTS/OpenPkg/Top.lean`:

* `dynInputsOpen2OfApriori` — N5's four a-priori fields (`Open2.AprioriFields2`) plus the
  remaining Galerkin data and the `StarPkgo2`/`EllPkgGo` packages produce the migrated bundle
  `Open2.DynInputsOpen2` (via the delivered `OpenPkg.dynCoreOfApriori`, applied to
  `AprioriFields2.toPrimed`);
* `exists_dynGSol_open_of_apriori2` — the resulting Galerkin existence statement, through
  `OpenPkg.exists_dynGSol_of_ode_open` and the projection `DynInputsOpen2.toOpen`.

Both are interface wiring: the ODE/existence layer only ever uses the *core* of the bundle, which
does not mention the star package at all.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Work.FTS.Open2.Fields2
import Submission.Work.FTS.OpenPkg.Top
import Submission.Work.FTS.OpenPkg.Galerkin

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
  galFam GlobalODEExistence IsDynGSolWith)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The migrated bundle (N6 input) from the a-priori fields and the open-quadrant packages.** -/
def dynInputsOpen2OfApriori {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ CcN clo cc Ce Cs : ℝ}
    {IP : ℝ → Fn → Fn → ℝ} {α₂ Cup Ccs : ℝ} {φ : ℕ → Fn} {Φs : Fn} {EllSol : Fn → Fn}
    {L K : ℕ → ℝ} (hIP : UnifIP IP α₂ cc clo Cup Ccs)
    (hC₀ : 0 < C₀) (hα : 0 < α) (hφ : GalBasis α IP φ)
    (hφ_dense : DenseSpan α IP φ)
    (hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
      Law (Work.Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ))
    (hL : ∀ n : ℕ, 0 < L n) (hK : ∀ n : ℕ, 0 ≤ K n)
    (hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
      LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
        (Metric.closedBall 0 (2 * Ropen clo C₀ α)))
    (hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
      c ∈ Metric.closedBall 0 (2 * Ropen clo C₀ α) →
      ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n)
    (hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * Ropen clo C₀ α) →
      ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0))
    (hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      EquicontSpace (profileFam φ c))
    (hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      EquicontTau (profileFam φ c))
    (hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g)
    (hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ)
    (hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ)
    (hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
      IsDynWeakOn α (IP α) φ g Φ ∧
        (∀ τ : ℝ, 0 ≤ τ → Law (Work.Construction.Ftau α g τ) (slice Φ τ)))
    (hDetermines : WeakDetermines α (IP α) φ)
    (hFields : AprioriFields2 IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀)
    (hCs : 0 < Cs) (hCe : 0 < Ce) (hΦs : StarPkgo2 α Cs Φs)
    (hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (EllSol g)) :
    DynInputsOpen2 Law α g₀ C₀ :=
  ⟨dynCoreOfApriori hIP hC₀ hα hφ hφ_dense hPsi hL hK hField_lip hField_bound hField_cont
    hProfileSpace hProfileTau hRegLimit hDataLimit hPsiLim hGalWeak hDetermines hFields.toPrimed,
    Cs, Ce, hΦs, hEllSol⟩

/-- **The Galerkin existence theorem from the a-priori fields and the remaining core data**
(the migrated `Work.FTS.Galerkin.exists_dynGSol_of_ode` wiring). -/
theorem exists_dynGSol_open_of_apriori2 (hODE : GlobalODEExistence)
    {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ CcN clo cc Ce Cs : ℝ}
    {IP : ℝ → Fn → Fn → ℝ} {α₂ Cup Ccs : ℝ} (hIP : UnifIP IP α₂ cc clo Cup Ccs)
    (hC₀ : 0 < C₀) (hα : 0 < α) {φ : ℕ → Fn} (hφ : GalBasis α IP φ)
    (hφ_dense : DenseSpan α IP φ) {Φs : Fn} {EllSol : Fn → Fn}
    (hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
      Law (Work.Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ))
    {L : ℕ → ℝ} (hL : ∀ n : ℕ, 0 < L n) {K : ℕ → ℝ} (hK : ∀ n : ℕ, 0 ≤ K n)
    (hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
      LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
        (Metric.closedBall 0 (2 * Ropen clo C₀ α)))
    (hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
      c ∈ Metric.closedBall 0 (2 * Ropen clo C₀ α) →
      ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n)
    (hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * Ropen clo C₀ α) →
      ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0))
    (hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      EquicontSpace (profileFam φ c))
    (hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      EquicontTau (profileFam φ c))
    (hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g)
    (hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ)
    (hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ)
    (hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Ropen clo C₀ α) c →
      ∀ (ψ : ℕ → ℕ) (g Φ : Fam), StrictMono ψ →
      ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
      ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
      IsDynWeakOn α (IP α) φ g Φ ∧
        (∀ τ : ℝ, 0 ≤ τ → Law (Work.Construction.Ftau α g τ) (slice Φ τ)))
    (hDetermines : WeakDetermines α (IP α) φ)
    (hFields : AprioriFields2 IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀)
    (hCs : 0 < Cs) (hCe : 0 < Ce) (hΦs : StarPkgo2 α Cs Φs)
    (hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (EllSol g)) :
    ∃ g Φ : Fam, IsDynGSolWith Law α Φ g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      RegPkg α g ∧ (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2) :=
  exists_dynGSol_of_ode_open hODE
    (DynInputsOpen2.toOpen (dynInputsOpen2OfApriori hIP hC₀ hα hφ hφ_dense hPsi hL hK
      hField_lip hField_bound hField_cont hProfileSpace hProfileTau hRegLimit hDataLimit hPsiLim
      hGalWeak hDetermines hFields hCs hCe hΦs hEllSol))

end Work.FTS.Open2
