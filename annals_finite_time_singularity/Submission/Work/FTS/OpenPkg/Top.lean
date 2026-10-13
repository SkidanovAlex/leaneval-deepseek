/-
# `OpenPkg/Top` — the wiring of the top-level (N0) assembly on the migrated route

This module contains the *assembly* lemmas that turn the migrated chapters into the inputs of the
Galerkin existence theorem, i.e. the migrated analogue of the role that
`Work.FTS.Apriori.Fields.aprioriFields` and `Work.FTS.Galerkin.DynInputs` play on the delivered
route:

* `dynCoreOfApriori`: N5's four a-priori fields (`OpenPkg.AprioriFields'`, open-quadrant form)
  together with the remaining Galerkin data produce the *core* bundle `OpenPkg.DynCore` — the part
  of the bundle that the ODE/existence layer consumes — with the radius specialised to
  `Rstar clo C₀ α = √clo·C₀·α²`;
* `dynInputsOpenOfApriori`: the same with the open-quadrant packages `StarPkgo`/`EllPkgGo`
  attached, i.e. the migrated `DynInputs`;
* `exists_dynGSol_open_of_apriori`: the resulting Galerkin existence statement.

Nothing here is analytic: these are the interface wiring lemmas which make the migrated chapter
usable at the top level, and they are the exact places where the delivered route mentions
`StarPkg`/`EllPkgG` or the `SmoothQuad` limit hypothesis.
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Galerkin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof
  galFam GlobalODEExistence IsDynGSolWith)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The a-priori radius `√clo·C₀·α²` (`Work.FTS.Apriori.Rstar`). -/
abbrev Ropen (clo C₀ α : ℝ) : ℝ := Work.FTS.Apriori.Rstar clo C₀ α

theorem Ropen_pos {clo C₀ α : ℝ} (hclo : 0 < clo) (hC₀ : 0 < C₀) (hα : 0 < α) :
    0 < Ropen clo C₀ α := by
  rw [Ropen, Work.FTS.Apriori.Rstar]
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr hclo) hC₀) (pow_pos hα 2)

/-- **The core bundle from the a-priori fields** (the migrated analogue of
`Work.FTS.Apriori.dynInputs_apriori_fields`).

`AprioriFields'` supplies exactly the four fields `hInit`, `hCoeffBound`, `hProfileBdd`,
`hLimBound` of the bundle, with the radius `Rstar clo C₀ α`; the remaining fields are the
analytic input of the other nodes (the basis, the stream functions, the projected field's
Lipschitz/bound/continuity constants, the compactness and limit inputs and the fundamental
lemma). -/
def dynCoreOfApriori {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ CcN clo cc Ce Cs : ℝ}
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
    (hFields : AprioriFields' IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀) :
    DynCore Law α g₀ C₀ where
  IP := IP
  α₂ := α₂
  cc := cc
  clo := clo
  Cup := Cup
  Ccs := Ccs
  hIP := hIP
  φ := φ
  hφ := hφ
  hφ_dense := hφ_dense
  Φs := Φs
  EllSol := EllSol
  hPsi := hPsi
  R := Ropen clo C₀ α
  hR := Ropen_pos hIP.pos.2.2.1 hC₀ hα
  L := L
  hL := hL
  K := K
  hK := hK
  hField_lip := hField_lip
  hField_bound := hField_bound
  hField_cont := hField_cont
  hInit := hFields.hInit
  hCoeffBound := hFields.hCoeffBound
  hProfileBdd := hFields.hProfileBdd
  hProfileSpace := hProfileSpace
  hProfileTau := hProfileTau
  hRegLimit := hRegLimit
  hDataLimit := hDataLimit
  hPsiLim := hPsiLim
  hGalWeak := hGalWeak
  hDetermines := hDetermines
  hLimBound := hFields.hLimBound

/-- **The migrated bundle (N6 input) from the a-priori fields and the open-quadrant packages.** -/
def dynInputsOpenOfApriori {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ CcN clo cc Ce Cs : ℝ}
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
    (hFields : AprioriFields' IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀)
    (hCs : 0 < Cs) (hCe : 0 < Ce) (hΦs : StarPkgo α Cs Φs)
    (hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (EllSol g)) :
    DynInputsOpen Law α g₀ C₀ :=
  ⟨dynCoreOfApriori hIP hC₀ hα hφ hφ_dense hPsi hL hK hField_lip hField_bound hField_cont
    hProfileSpace hProfileTau hRegLimit hDataLimit hPsiLim hGalWeak hDetermines hFields,
    Cs, Ce, hΦs, hEllSol⟩

/-- **The Galerkin existence theorem from the a-priori fields and the remaining core data**
(the migrated `Work.FTS.Galerkin.exists_dynGSol_of_ode` wiring). -/
theorem exists_dynGSol_open_of_apriori (hODE : GlobalODEExistence)
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
    (hFields : AprioriFields' IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀)
    (hCs : 0 < Cs) (hCe : 0 < Ce) (hΦs : StarPkgo α Cs Φs)
    (hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (EllSol g)) :
    ∃ g Φ : Fam, IsDynGSolWith Law α Φ g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      RegPkg α g ∧ (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2) :=
  exists_dynGSol_of_ode_open hODE
    (dynInputsOpenOfApriori hIP hC₀ hα hφ hφ_dense hPsi hL hK hField_lip hField_bound
      hField_cont hProfileSpace hProfileTau hRegLimit hDataLimit hPsiLim hGalWeak hDetermines
      hFields hCs hCe hΦs hEllSol)

end Work.FTS.OpenPkg
