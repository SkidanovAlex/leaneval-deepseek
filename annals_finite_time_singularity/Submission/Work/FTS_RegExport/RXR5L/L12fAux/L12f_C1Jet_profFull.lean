/-
# `Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull` — the `L₁₂`-slots of the class data,
# with the **intended** (satisfiable) compact-support hypothesis

The sibling statement `Work.FTS_RegExport.RXR5L.L12f_C1Jet` carries the hypothesis

  `hsupp : ∃ Lf > 0, ∀ τ ∈ Icc 0 S, ∀ z θ, Lf ≤ z → profFull (pExp α) (gS α (tauExt g)) z θ τ = 0`

which is **unsatisfiable**: `profFull β G = Fstar (pExp β) + G`, while the sanitiser `gS α h` is
*by definition* `-Fstar (pExp α)` off the angular interval `Iθ`.  Hence for `θ ∉ Iθ` and `z ≥ Lf`
the stated hypothesis forces `Fstar (pExp (pExp α)) z θ = Fstar (pExp α) z θ`, i.e.
`Fstar (9α) = Fstar (3α)` at every angle outside `Iθ` — false for every `α > 0` (see
`NOTES_L12f_C1Jet_misstated.md`, and the machine-checked core `Gfull_of_profFull` below).  The
tree's own support clauses (`RegPkgGal/Defs.lean`'s `RegPkg.hsupp`, `Supp.suppExport_proved`,
`FinalV2.hsuppOut_gS`) all use `profFull α (…)`, i.e. `Fstar (pExp α) + G`.

This module proves the statement with the **corrected** hypothesis
`hsupp : profFull α (gS α (tauExt g)) = 0` far out — the form in which the construction's
compactness of the full profile actually enters.  Everything else is verbatim the assigned
statement.

## Route

Write `G := profFull α (gS α (tauExt g))` (the full profile, compactly supported by `hsupp`) and
`g̃ := gS α (tauExt g)`; on the box, `G = F_* + g̃` with `F_* = Fstar (pExp α)`.

* **first slot** (`L₁₂` of the slice of `g̃`): by the additivity of `L₁₂` on honest fields
  (`L12_split_of_slice_integrable`, applied to `a = F_*`, `b = g̃(·,·,τ)`),
  `L₁₂(g̃(τ))(z) = L₁₂(G(τ))(z) - L₁₂(F_*)(z)`; the second term is the explicit `2pExp α/(1+z)`, and
  the first is a `C1Jet` by the generic support result `C1Jet_L12f_of_support`;
* **second slot** (`L₁₂(3·D_θg̃/(1+z))(0)`): constant in `(z,θ)`, so only the sup bound and the
  `τ`-modulus are needed — `Tf_SG_facts_profFull`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.Fstar_dens_facts
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS.RegPkgGal.Der.L12fDensUnif
import Submission.Work.FTS.RegPkgGal.Der.L12fDensBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 The full profile of the sanitised family, and the static profile bound -/

/-- The full profile `G = F_* + g̃` of the construction at the sanitised family
`g̃ = gS α (tauExt g)`.  It is compactly supported in `z` by the support hypothesis. -/
def Gfull (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Regularity.profFull α
    (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ

theorem Gfull_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (z θ τ : ℝ) :
    Gfull α g z θ τ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS_RegExport.RXR5.SG α g z θ τ := by
  rw [Gfull, Work.FTS.Regularity.profFull_apply]

/-- `|F_*(z,θ)| ≤ 20 z` on the domain (`F_* = α(Γ/c)·F̂`, `Γ ≤ 1`, `c ≥ 1/10`, `F̂(z) ≤ 2z`). -/
theorem Fstar_abs_le_twenty {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ| ≤ 20 * z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hβ hβ1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hc.1]
  obtain ⟨hg0, hg1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hβ hθ
  have hden : (0:ℝ) < (1 + z) ^ 2 := by positivity
  rw [Work.Construction.Fstar, Work.FM.Fstar, abs_mul, abs_mul,
    abs_of_nonneg hβ.le, abs_of_nonneg (div_nonneg hg0 hcpos.le),
    abs_of_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ 2 * z) hden.le)]
  have hgg : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith [hc.1, hg1]
  have h2 : 2 * z / (1 + z) ^ 2 ≤ 2 * z := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg z, hz]
  have hgg0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α) := div_nonneg hg0 hcpos.le
  have h20 : 0 ≤ 2 * z / (1 + z) ^ 2 := div_nonneg (by linarith) hden.le
  calc Work.FTS.Regularity.pExp α * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * z / (1 + z) ^ 2)
      ≤ 1 * 10 * (2 * z) :=
        mul_le_mul (mul_le_mul hβ1 hgg hgg0 (by norm_num)) h2 h20 (by norm_num)
    _ = 20 * z := by ring

/-! ## §2 The near-axis linearity of the full profile -/

theorem Gfull_lin {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ Kl : ℝ, 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ioo (0:ℝ) 1, |Gfull α g z θ τ| ≤ Kl * z := by
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  refine ⟨20 + K, by linarith, ?_⟩
  intro τ hτ θ hθ z hz
  have hz1 : (0:ℝ) < z := hz.1
  have hF := Fstar_abs_le_twenty hα hα13 hz1.le hθ
  have hSg : |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ K * z ^ 2 := by
    rw [← Work.FTS_RegExport.RXR5L.SG_extG_eq hz1.le hθ hτ]
    exact (hquad τ hτ θ hθ).1 z hz1.le (by linarith [hz.2])
  rw [Gfull_apply]
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ|
      ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        + |Work.FTS_RegExport.RXR5.SG α g z θ τ| := abs_add_le _ _
    _ ≤ 20 * z + K * z ^ 2 := add_le_add hF hSg
    _ ≤ (20 + K) * z := by
        have hsq : z ^ 2 ≤ z := by nlinarith [hz1, hz.2]
        nlinarith [hK, hsq]

/-! ## §3 The jet of the full profile -/

theorem Gfull_jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N : ℝ, 0 ≤ N ∧ Work.FTS.Regularity.Jet α S N (Gfull α g) := by
  obtain ⟨N₁, hN₁0, hC1SG⟩ :=
    Work.FTS_RegExport.RXR5L.SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hJF : Work.FTS.Regularity.Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    (Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13).1
  have hJsum : Work.FTS.Regularity.Jet α S
      (100 + 20 * Work.FTS.Regularity.pExp α + N₁)
      (fun z θ τ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.Regularity.Jet.add hJF hC1SG.1
  refine ⟨100 + 20 * Work.FTS.Regularity.pExp α + N₁, by
      have hp := Work.FTS.Regularity.pExp_pos hα; linarith, ?_⟩
  refine Work.FTS.Regularity.Jet.congr hJsum ?_
  intro z θ τ _ _ _
  exact (Gfull_apply α g z θ τ).symm

/-! ## §4 The support of the full profile -/

theorem Gfull_supp {α S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0) :
    ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Gfull α g z θ τ = 0 := by
  obtain ⟨Lf, hLf, hvan⟩ := hsupp
  exact ⟨Lf, hLf, fun τ hτ z θ hz => hvan τ hτ z θ hz⟩

/-! ## §5 The `τ`-modulus of the full profile (from the sanitised family) -/

theorem Gfull_tau_mod {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z →
        |Gfull α g z θ τ - Gfull α g z θ τ'| ≤ Nt * z * |τ - τ'| ^ α := by
  obtain ⟨Nt, hNt0, hmod⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS
  refine ⟨Nt, hNt0, ?_⟩
  intro τ hτ τ' hτ' θ hθ z hz
  rw [Gfull_apply, Gfull_apply]
  have hkey : (Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ)
      - (Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ')
      = Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ' := by
    ring
  rw [hkey]
  exact hmod τ hτ τ' hτ' θ hθ z hz

/-! ## §6 The angular integrability of the sanitised slice -/

theorem SG_slice_integrable {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ / s) Work.Spaces.Iθ := by
  obtain ⟨N₁, hN₁0, hC1SG⟩ :=
    Work.FTS_RegExport.RXR5L.SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  intro τ hτ s hs
  have hcontSG : ContinuousOn (fun θ => Work.FTS_RegExport.RXR5.SG α g s θ τ) Work.Spaces.Iθ :=
    Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN₁0 hα
      (fun θ hθ θ' hθ' => hC1SG.1.thmod (le_of_lt hs) hθ hθ' hτ)
  have hcontK : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ :=
    (by unfold Work.Spaces.K; fun_prop : Continuous fun θ : ℝ => Work.Spaces.K θ).continuousOn
  have hcont : ContinuousOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ * (1 / s))
      Work.Spaces.Iθ := (hcontK.mul hcontSG).mul continuousOn_const
  rw [Work.Spaces.Iθ] at hcont ⊢
  refine (hcont.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
  intro θ _
  ring

/-! ## §7 Integrability of the density of the full profile -/

theorem Gfull_dens_integrable {α S N Kl Lf : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hJet : Work.FTS.Regularity.Jet α S N (Gfull α g))
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |Gfull α g z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → Gfull α g z θ τ = 0) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice (Gfull α g) τ))
      (Set.Ioi 0) := by
  intro τ hτ
  refine Work.FTS.RegPkgGal.Der.integrableOn_Ioi_of_bound_of_eventually_zero
    (c := 6 * max Kl N) hsupp.1
    (Work.FTS.RegPkgGal.Der.continuousOn_L12dens_gSlice hα hJet hτ) ?_ ?_
  · intro s hs
    exact Work.FTS.RegPkgGal.Der.L12fDensUnif hJet hlin τ hτ s hs
  · intro s hs
    exact (Work.FTS.RegPkgGal.Der.L12fDensBound hJet hlin hsupp).2 τ hτ s hs

/-! ## §8 The additivity of `L₁₂` on the pair `(F_*, g̃(τ))` -/

theorem L12f_split_Gfull {α S N Kl Lf : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hJet : Work.FTS.Regularity.Jet α S N (Gfull α g))
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |Gfull α g z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → Gfull α g z θ τ = 0)
    (hSGE : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ / s) Work.Spaces.Iθ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        = Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
          + Work.Coercivity.L12f
              (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z := by
  obtain ⟨hIa, hIad, _hIav⟩ := Work.FTS_RegExport.RXR5L.L12fAux.Fstar_dens_facts hα hα13
  intro τ hτ z hz
  have hfe : (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS_RegExport.RXR5.SG α g z θ τ)
      = Work.FTS.Regularity.gSlice (Gfull α g) τ := by
    funext z θ
    rw [Work.FTS.Regularity.gSlice_apply, Gfull_apply]
  have hsum : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ)) (Set.Ioi 0) := by
    rw [hfe]
    exact Gfull_dens_integrable hα hJet hlin hsupp τ hτ
  have hsplit := Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
    (α := α)
    (a := fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
    (b := fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hIa (hSGE τ hτ) hsum hIad z hz
  rw [← hfe]
  exact hsplit

/-! ## §9 A family that is constant in `(z,θ)`: the `C1Jet` of a `τ`-curve -/

theorem c1jet_const_family {α S M : ℝ} {T : ℝ → ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hb : ∀ τ ∈ Set.Icc (0:ℝ) S, |T τ| ≤ M)
    (hm : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |T τ - T τ'| ≤ M * |τ - τ'| ^ α) :
    Work.FTS.RegPkgGal.C1Jet α S M (fun _ _ τ => T τ) := by
  refine ⟨⟨hM0, ?_, ?_⟩, ?_⟩
  · intro z θ τ _ _ hτ
    exact hb τ hτ
  · intro z z' θ θ' τ τ' _ _ _ _ hτ hτ'
    have h1 : |T τ - T τ'| ≤ M * |τ - τ'| ^ α := hm τ hτ τ' hτ'
    have h2 : |τ - τ'| ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      have h3 : (0:ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
      linarith
    have h3 : |τ - τ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) h2 hα.le
    calc |T τ - T τ'| ≤ M * |τ - τ'| ^ α := h1
      _ ≤ M * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_left h3 hM0
  · intro τ _ θ _ z _
    exact ⟨0, hasDerivAt_const z (T τ), by simpa using hM0⟩

/-! ## §10 The corrected statement -/

theorem L12f_C1Jet_profFull {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0) :
    ∃ N₇ N₈ : ℝ, 0 ≤ N₇ ∧ 0 ≤ N₈ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₇
        (fun z θ τ => Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
          z) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₈
        (fun z θ τ => Work.Coercivity.L12f
          (fun z θ' => 3 * Work.Spaces.Dth
            (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z θ'
            / (1 + z)) 0) := by
  have hα1 : α ≤ 1 := by linarith
  -- ### the first slot
  obtain ⟨Njet, hNjet0, hJet⟩ := Gfull_jet (S := S) hα hα13 hOK hS hSt1
  obtain ⟨Kl, hKl0, hlin⟩ := Gfull_lin (S := S) hα hα13 hOK hS hSt1
  obtain ⟨Lf, hLf, hsuppG⟩ := Gfull_supp (S := S) (g := g) hsupp
  obtain ⟨Nt, hNt0, htau⟩ := Gfull_tau_mod (S := S) hα hα13 hOK hS
  obtain ⟨Nc, hNc0, hC1G⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support (α := α) (S := S) (N := Njet)
      (Kl := Kl) (Lf := Lf) (Nt := Nt) hα hα1 hS hJet ⟨hKl0, hlin⟩ ⟨hLf, hsuppG⟩ ⟨hNt0, htau⟩
  obtain ⟨N₉, hN₉0, hC1F⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_L12f_Fstar (α := α) (S := S) hα hα13 hS
  have hC1sub : Work.FTS.RegPkgGal.C1Jet α S (Nc + N₉)
      (fun z θ τ => Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        - Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z) :=
    Work.FTS.RegPkgGal.C1Jet.add hC1G (Work.FTS.RegPkgGal.C1Jet.neg hC1F)
  have hsplit := L12f_split_Gfull (α := α) (S := S) (N := Njet) (Kl := Kl) (Lf := Lf)
    hα hα13 hJet ⟨hKl0, hlin⟩ ⟨hLf, hsuppG⟩
    (SG_slice_integrable (S := S) hα hα13 hOK hS hSt1)
  have hconj₁ : Work.FTS.RegPkgGal.C1Jet α S (Nc + N₉)
      (fun z θ τ => Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z) := by
    refine Work.FTS.RegPkgGal.C1Jet.congr hC1sub ?_
    intro z θ τ hz hθ hτ
    have h := hsplit τ hτ z hz
    show Work.Coercivity.L12f (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
      = Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z
    linarith [h]
  -- ### the second slot (the transport zero-mode of the raw family, transported to `g̃`)
  obtain ⟨M₀, hM₀0, hTbnd, hTlip⟩ :=
    Work.FTS_RegExport.RXR5L.aux.Tlim_bounds (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS
  -- `slice g τ` and the sanitised slice agree on the quadrant, hence so do their transport fields
  have hagree : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS.Galerkin.slice g τ)
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) := by
    intro τ hτ z θ hz hθ hθ2
    show g z θ τ = Work.FTS_RegExport.RXR5.SG α g z θ τ
    rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
  have hcongr : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
        = Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
            / (1 + z)) 0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXR5.L12f_congr_of_agreeOnQ ?_ (le_refl (0:ℝ))
    intro z θ hz hθ hθ2
    show 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
      = 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ / (1 + z)
    rw [Work.FTS_RegExport.RXR5.Dth_congr_of_agreeOnQ (hagree τ hτ) hz hθ hθ2]
  have hmax0 : (0:ℝ) ≤ max S 1 := le_trans zero_le_one (le_max_right _ _)
  have hb : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
        / (1 + z)) 0| ≤ M₀ * max S 1 := by
    intro τ hτ
    rw [← hcongr τ hτ]
    exact le_trans (hTbnd τ hτ)
      (le_mul_of_one_le_right hM₀0 (le_max_right S 1))
  have hm : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
          / (1 + z)) 0
        - Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ') z θ
          / (1 + z)) 0| ≤ M₀ * max S 1 * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    rw [← hcongr τ hτ, ← hcongr τ' hτ']
    have h1 := hTlip τ hτ τ' hτ'
    have h2 := Work.FTS_RegExport.RXR5L.abs_sub_le_max_mul_rpow (S := S) hα hα1 hτ hτ'
    calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
        ≤ M₀ * |τ - τ'| := h1
      _ ≤ M₀ * (max S 1 * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hM₀0
      _ = M₀ * max S 1 * |τ - τ'| ^ α := by ring
  refine ⟨Nc + N₉, M₀ * max S 1,
    by linarith [hNc0, hN₉0], mul_nonneg hM₀0 hmax0, hconj₁, ?_⟩
  refine Work.FTS.RegPkgGal.C1Jet.congr
    (c1jet_const_family (α := α) (S := S) (M := M₀ * max S 1) (hα := hα)
      (mul_nonneg hM₀0 hmax0) (fun τ hτ => hb τ hτ)
      (fun τ hτ τ' hτ' => hm τ hτ τ' hτ')) ?_
  intro z θ τ _ _ _
  rfl

end Work.FTS_RegExport.RXR5L.L12fAux
