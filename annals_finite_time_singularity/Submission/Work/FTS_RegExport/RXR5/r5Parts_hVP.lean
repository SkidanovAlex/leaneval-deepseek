import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.Ftau_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.DthFtau_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.DzFtau_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull
import Submission.Work.FTS_RegExport.RXR5L.EllProd_C1JetFull
import Submission.Work.FTS_RegExport.RXR5L.FK_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.NsData_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_RegExport.RXR5L.R0vals
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_RegExport.RXR7.r7Block_proved
import Submission.Work.FTS_RegExport.Supp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5

open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp Jet gSlice)

set_option linter.unusedVariables false

/-! ## The two remaining inputs of the assembly

The `C1Jet`-data of the class slots (`SG_C1Jet`, `DzDthSG_C1Jet_of_inputs`, `Ftau_C1Jet`,
`DthFtau_C1Jet`, `DzFtau_C1Jet`), the elliptic product slots (`EllProd_C1JetFull`), the `FK`-slot
(`FK_C1Jet`), the `N_*`-slot (`NsData_C1Jet`), the `mubar`-data (`mubarData`), the static-profile
slots (`Fstar_C1Jet`) and the three boundary values (`R0vals`) are all proved.  The two inputs
that are *derived* here are

* `profFull_SG_support`: the compact `z`-support of the sanitised full profile
  `profFull α (gS α (tauExt g))` (the `hsupp` of `L12f_C1Jet_profFull`), from `r7Block_proved`
  (= `suppExport`) — note that the profile's own exponent is `α` here (the satisfiable form);
* `muDyn_data_SG`: the bound and the `τ`-modulus of the clock functions `μ, λ` at the sanitised
  family (the `hMuB`/`hMuH` of `NsData_C1Jet`), from `mubarData`, the `Jet` of the transport
  zero-mode (`L12f_C1Jet_profFull`'s second slot) and the clock bound `ClockBd` (which controls
  `λ = -2μ/(1+μ)`), using the congruence `muDyn_congr_of_agreeOnQ` + `muDyn_tauExt`.
-/

/-- **The compact `z`-support of the sanitised full profile.**  For every horizon `S > 0` the
profile `z ↦ profFull α (gS α (tauExt g)) z θ τ` vanishes for `z` beyond a per-horizon threshold,
uniformly in `θ` and in `τ ∈ [0,S]`.

Inside `Iθ` this is finite speed of propagation (`RegPkgGal.R7e.support_strip_zL`) applied to the
`R7Block` produced by `r7Block_proved`; the two angular endpoints use `RegPkgMin.vanish`, and off
`Iθ` the sanitiser is *by definition* `-Fstar`, so the profile is `Fstar - Fstar = 0`. -/
private theorem profFull_SG_support {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (pExp α)
      (Work.FTS.Final.maxMu (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S)
    {S : ℝ} (hS : 0 < S) :
    ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        z θ τ = 0 := by
  obtain ⟨a, b, c, Lz7, hRB⟩ :=
    Work.FTS_RegExport.RXR7.r7Block_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hSol hOK hdat hμ hVP
  have hB := hRB S hS
  -- the two angular boundary values of the sanitised family
  have hSGθ0 : ∀ (τ : ℝ), 0 ≤ τ → ∀ z : ℝ, SG α g z 0 τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [SG_apply_of_pos hz' le_rfl (by linarith [Real.pi_pos]),
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).1
  have hSGθπ : ∀ (τ : ℝ), 0 ≤ τ → ∀ z : ℝ, SG α g z (Real.pi / 2) τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [SG_apply_of_pos hz' (by linarith [Real.pi_pos]) le_rfl,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).2
  -- finite speed of propagation for the extended profile
  have hsupp7 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → 0 < θ →
      θ < Real.pi / 2 → Work.FTS.Regularity.profFull α
        (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ = 0 :=
    Work.FTS.RegPkgGal.R7e.support_strip_zL (S := S) (a := a) (b := b) (c := c) (L := Lz7)
      hS hB.ha hB.hb hB.hc hB.hLz7
      (F := fun z θ τ => Work.FTS.Regularity.profFull α
        (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ)
      hB.hFjoint hB.hVjoint hB.hVlipU hB.hcscont hB.hEq hB.hVz0 hB.hVza hB.hVθb hB.hVθ0 hB.hVθπ
      hB.hcsc hB.hInit
  refine ⟨max 1 (Lz7 * Real.exp (a * S) + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz
  have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_left _ _) hz
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hzbig : Lz7 * Real.exp (a * S) < z :=
    lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hz)
  by_cases hθ : θ ∈ Work.Spaces.Iθ
  · rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [Work.FTS.Regularity.profFull_apply,
        Work.FTS_RegExport.Fstar_zero_left (Work.FTS.Regularity.pExp_pos hα) z,
        show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0
          from hSGθ0 τ hτ.1 z]
      ring
    · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
      · subst hπ
        rw [Work.FTS.Regularity.profFull_apply,
          Work.FTS_RegExport.Fstar_zero_pi (Work.FTS.Regularity.pExp_pos hα) z,
          show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (Real.pi / 2) τ = 0
            from hSGθπ τ hτ.1 z]
        ring
      · have hprof : Work.FTS.Regularity.profFull α (SG α g) z θ τ
            = Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ := by
          rw [Work.FTS.Regularity.profFull_apply, Work.FTS.Regularity.profFull_apply,
            Work.FTS.RegPkgGal.extG_of_pos hz0 hτ.1]
        rw [hprof]
        exact hsupp7 τ hτ z θ hzbig h0 hπ
  · have hnot : ¬ (0 ≤ θ ∧ θ ≤ Real.pi / 2) := fun hh => hθ hh
    have hg : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ
        = - Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
      simp only [Work.FTS.FinalV2.gS, hz0, ↓reduceIte]
      rw [if_neg hnot]
    rw [Work.FTS.Regularity.profFull_apply, hg]
    ring

/-- **The clock data of `N_*` at the sanitised family.**  The bound and the `τ`-modulus of
`μ = muDyn (pExp α) (SΨ α Φs E g) (SG α g)` and `λ = lamDyn (pExp α) (SΨ α Φs E g) (SG α g)`.

`mufunS` makes `μ = (1/(2α))·(μ̄ + T)` with `μ̄` the `mubar` of `mubarData` and `T` the transport
zero-mode of the second slot of `L12f_C1Jet_profFull`; `ClockBd` bounds `|μ| ≤ 1/2`, so
`λ = -2μ/(1+μ)` is bounded by `2` and is `8`-Lipschitz in `μ`. -/
private theorem muDyn_data_SG {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (SG α g))
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (SG α g) z θ τ = 0)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ M ∧
      |Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ M) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'| ≤ L * |τ - τ'| ^ α ∧
      |Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'| ≤ L * |τ - τ'| ^ α) := by
  -- the `μ̄`-data
  obtain ⟨⟨Mub, hMub0, hMubB⟩, ⟨MubH, hMubH0, hMubH⟩⟩ :=
    Work.FTS_RegExport.RXR5L.mubarData (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hS
  -- the transport zero-mode
  obtain ⟨N₇, N₈, hN₇, hN₈, hL12g, hL12T⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS hSt1 hsupp
  have hpi : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  -- the bound of the transport slot
  have hTb : ∀ τ ∈ Set.Icc 0 S, |Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
      (Work.FTS.Regularity.gSlice (SG α g) τ) z θ' / (1 + z)) 0| ≤ N₈ := by
    intro τ hτ
    have h := hL12T.1.2.1 0 0 τ le_rfl hpi hτ
    simpa using h
  -- the `τ`-modulus of the transport slot
  have hTm : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (SG α g) τ) z θ' / (1 + z)) 0
        - Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (SG α g) τ') z θ' / (1 + z)) 0|
        ≤ N₈ * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h := hL12T.1.2.2 0 0 0 0 τ τ' le_rfl le_rfl hpi hpi hτ hτ'
    simpa using h
  -- the definitional expansion of `muDyn`
  have hexp : ∀ τ : ℝ,
      Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        = (1 / (2 * pExp α)) *
            (Work.Construction.mubar
                (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SG α g) τ))
                (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SΨ α Φs E g) τ))
              + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                  (gSlice (SG α g) τ) z θ' / (1 + z)) 0) := by
    intro τ
    have hslice : Work.FTS.Galerkin.slice (SG α g) τ = gSlice (SG α g) τ := rfl
    have hslice' : Work.FTS.Galerkin.slice (SΨ α Φs E g) τ = gSlice (SΨ α Φs E g) τ := rfl
    simp only [Work.FTS.Galerkin.muDyn, Work.Construction.mufunS, Work.Construction.mubar,
      Work.Construction.L12, Work.Coercivity.L12f]
    rw [hslice, hslice']
    ring
  have hgc : (0 : ℝ) < 1 / (2 * pExp α) :=
    div_pos one_pos (by linarith [Work.FTS.Regularity.pExp_pos hα])
  -- the clock bound `|μ| ≤ 1/2`
  have hμhalf : ∀ τ : ℝ, 0 ≤ τ →
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ 1 / 2 := by
    intro τ hτ
    rw [muDyn_congr_of_agreeOnQ (α := pExp α) (g := SG α g)
        (g' := Work.FTS.FinalV2.tauExt g) (Φ := SΨ α Φs E g)
        (Φ' := Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g))
        (SG_slice_agreeOnQ α g τ) (SΨ_slice_agreeOnQ α Φs E g τ),
      Work.FTS.FinalV2.muDyn_tauExt (Φs := Φs) (E := E) (g := g) hτ]
    exact hμ.1 τ hτ
  -- `lamfun` is bounded and `8`-Lipschitz on `|μ| ≤ 1/2`
  have hlam_abs : ∀ μ : ℝ, |μ| ≤ 1 / 2 → |Work.Construction.lamfun μ| ≤ 2 := by
    intro μ hμ
    have hge : -(1 / 2 : ℝ) ≤ μ := le_trans (neg_le_neg hμ) (neg_abs_le μ)
    have hpos : 0 < 1 + μ := by linarith
    rw [Work.Construction.lamfun, abs_div, abs_of_pos hpos]
    rw [show |(-2 : ℝ) * μ| = 2 * |μ| by
      rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]]
    rw [div_le_iff₀ hpos]
    nlinarith [hμ, hge]
  have hlam_lip : ∀ μ μ' : ℝ, |μ| ≤ 1 / 2 → |μ'| ≤ 1 / 2 →
      |Work.Construction.lamfun μ - Work.Construction.lamfun μ'| ≤ 8 * |μ - μ'| := by
    intro μ μ' hμ hμ'
    have hge : -(1 / 2 : ℝ) ≤ μ := le_trans (neg_le_neg hμ) (neg_abs_le μ)
    have hge' : -(1 / 2 : ℝ) ≤ μ' := le_trans (neg_le_neg hμ') (neg_abs_le μ')
    have hd1 : 1 + μ ≠ 0 := by linarith
    have hd2 : 1 + μ' ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < 1 + μ := by linarith
    have hp2 : (0 : ℝ) < 1 + μ' := by linarith
    have hq : (1 / 4 : ℝ) ≤ (1 + μ) * (1 + μ') := by nlinarith
    have hkey : -2 * μ / (1 + μ) - -2 * μ' / (1 + μ')
        = 2 * (μ' - μ) / ((1 + μ) * (1 + μ')) := by
      field_simp
      ring
    simp only [Work.Construction.lamfun]
    rw [hkey, abs_div, abs_mul,
      abs_of_pos (mul_pos hp1 hp2)]
    have hnum : |(2 : ℝ)| * |μ' - μ| = 2 * |μ - μ'| := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
    rw [hnum]
    rw [div_le_iff₀ (mul_pos hp1 hp2)]
    have h1 : 2 * |μ - μ'| ≤ 8 * |μ - μ'| * (1 / 4) := by
      nlinarith [abs_nonneg (μ - μ')]
    have h2 : 8 * |μ - μ'| * (1 / 4) ≤ 8 * |μ - μ'| * ((1 + μ) * (1 + μ')) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) (abs_nonneg _))
    linarith
  -- the two analytic estimates for `muDyn`
  have hμbnd : ∀ τ ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ|
        ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) := by
    intro τ hτ
    rw [hexp τ, abs_mul, abs_of_pos hgc]
    have h1 : |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SG α g) τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SΨ α Φs E g) τ))| ≤ max Mub MubH :=
      le_trans (hMubB τ hτ) (le_max_left _ _)
    have h2 := hTb τ hτ
    refine mul_le_mul_of_nonneg_left ?_ hgc.le
    exact le_trans (abs_add_le _ _) (by linarith)
  have hμmod : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'|
        ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    rw [hexp τ, hexp τ']
    have h1 : |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SG α g) τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
            (gSlice (SG α g) τ'))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
            (gSlice (SΨ α Φs E g) τ'))| ≤ max Mub MubH * |τ - τ'| ^ α :=
      le_trans (hMubH τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) α))
    have h2 := hTm τ hτ τ' hτ'
    have hstep : (1 / (2 * pExp α)) *
            (Work.Construction.mubar
                (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SG α g) τ))
                (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SΨ α Φs E g) τ))
              + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                  (gSlice (SG α g) τ) z θ' / (1 + z)) 0)
          - (1 / (2 * pExp α)) *
              (Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SG α g) τ'))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SΨ α Φs E g) τ'))
                + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ') z θ' / (1 + z)) 0)
          = (1 / (2 * pExp α)) *
              ((Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                    (gSlice (SG α g) τ))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                    (gSlice (SΨ α Φs E g) τ))
                - Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SG α g) τ'))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SΨ α Φs E g) τ')))
              + (Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ) z θ' / (1 + z)) 0
                - Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ') z θ' / (1 + z)) 0)) := by
      ring
    rw [hstep, abs_mul, abs_of_pos hgc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hgc.le
    refine le_trans (abs_add_le _ _) ?_
    have hsum : max Mub MubH * |τ - τ'| ^ α + N₈ * |τ - τ'| ^ α
        = (max Mub MubH + N₈) * |τ - τ'| ^ α := by ring
    linarith [h1, h2, hsum]
  have hc0 : 0 ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) :=
    mul_nonneg hgc.le (add_nonneg (le_trans hMub0 (le_max_left _ _)) hN₈)
  have hkey8 : ∀ r : ℝ, 8 * ((1 / (2 * pExp α)) * (max Mub MubH + N₈)) * r
      = 8 * (((1 / (2 * pExp α)) * (max Mub MubH + N₈)) * r) := by
    intro r; ring
  refine ⟨⟨max ((1 / (2 * pExp α)) * (max Mub MubH + N₈)) 2,
      le_trans hc0 (le_max_left _ _), ?_⟩,
    ⟨8 * ((1 / (2 * pExp α)) * (max Mub MubH + N₈)),
      mul_nonneg (by norm_num) hc0, ?_⟩⟩
  · intro τ hτ
    constructor
    · exact le_trans (hμbnd τ hτ) (le_max_left _ _)
    · exact le_trans (hlam_abs _ (hμhalf τ hτ.1)) (le_max_right _ _)
  · intro τ hτ τ' hτ'
    constructor
    · refine le_trans (hμmod τ hτ τ' hτ') ?_
      rw [hkey8]
      exact le_mul_of_one_le_left (mul_nonneg hc0 (Real.rpow_nonneg (abs_nonneg _) α))
        (by norm_num)
    · refine le_trans (hlam_lip _ _ (hμhalf τ hτ.1) (hμhalf τ' hτ'.1)) ?_
      rw [hkey8]
      exact mul_le_mul_of_nonneg_left (hμmod τ hτ τ' hτ') (by norm_num)

theorem r5Parts_hVP {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S) :
    ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) := by
  intro S hS
  -- the compact support of the profile (the `hsupp` of `L12f_C1Jet_profFull`)
  obtain ⟨Lf, hLf, hsupp⟩ := profFull_SG_support (Φs := Φs) (E := E) (g := g)
    hα hα13 hSol hOK hdat hμ hVP hS
  have hsuppEx : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (SG α g) z θ τ = 0 := ⟨Lf, hLf, hsupp⟩
  -- the `z`-uniform angular slots of the sanitised family (the O1 input)
  have hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => SG α g z θ τ) z θ) :=
    Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  have hO1c := hO1
  obtain ⟨N₂, N₃, hN₂, hN₃, hDzg, hDthg⟩ := hO1c
  -- the class data of the sanitised family
  obtain ⟨N₁, hN₁, hg⟩ := Work.FTS_RegExport.RXR5L.SG_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS)
  obtain ⟨N₄, hN₄, hF⟩ := Work.FTS_RegExport.RXR5L.Ftau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₅, hN₅, hDthF⟩ := Work.FTS_RegExport.RXR5L.DthFtau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₆, hN₆, hDzF⟩ := Work.FTS_RegExport.RXR5L.DzFtau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  -- the two `L₁₂`-slots of the class data
  obtain ⟨N₇, N₈, hN₇, hN₈, hL12g, hL12T⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS (hSt1 S hS) hsuppEx
  -- the `FK`-slot
  obtain ⟨Nf, hNf, hFK⟩ := Work.FTS_RegExport.RXR5L.FK_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS)
  -- the three elliptic product slots
  obtain ⟨N₁₂, N₁₃, Ne, hN₁₂, hN₁₃, hNe, hRopF, hUopF, hVopDzF⟩ :=
    Work.FTS_RegExport.RXR5L.EllProd_C1JetFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVP hSt1 hS
  -- the `N_*`-slot
  have hmudata := muDyn_data_SG (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK
    hS (hSt1 S hS) hsuppEx hμ
  obtain ⟨Nn, hNn, hNsJet, hNsZ⟩ :=
    Work.FTS_RegExport.RXR5L.NsData_C1Jet (Φs := Φs) (E := E) hα hα13 hOK hS (hSt1 S hS) hO1
      hmudata.1 hmudata.2
  -- the `mubar`-data and the boundary values
  obtain ⟨hmb, hmbh⟩ := Work.FTS_RegExport.RXR5L.mubarData (Φs := Φs) (E := E)
    hα hα13 hEll hEL3 hStar hSol hOK hS
  obtain ⟨hRz0, hRθ0, hRθπ⟩ := Work.FTS_RegExport.RXR5L.R0vals (Φs := Φs) (E := E)
    hα hα13 hSol hOK hS
  -- the three static-profile slots
  obtain ⟨N₉, N₁₀, N₁₁, hN₉, hN₁₀, hN₁₁, hL12Fstar, hDthFstar, hDzFstar⟩ :=
    Work.FTS_RegExport.RXR5.Fstar_C1Jet (α := α) hα hα13 hS
  -- ## the two shared constants
  have hg' : Work.FTS.RegPkgGal.C1Jet α S (max N₁ Nn) (SG α g) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_left _ _) hg.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hg.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left _ _)⟩
  have hNsJet' : Work.FTS.Regularity.Jet α S (max N₁ Nn) (fun z θ τ => Work.Construction.Nstar
      (Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
      (Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
      (gSlice (SG α g) τ) z θ) :=
    Work.FTS_RegExport.RXR5.jet_mono (le_max_right _ _) hNsJet
  have hNsZ' : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
        (Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
        (gSlice (SG α g) τ) z' θ) d z ∧ |d| ≤ max N₁ Nn := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hNsZ τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩
  have hFK' : Work.FTS.RegPkgGal.C1Jet α S (max Ne Nf) (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (pExp α) (SG α g) τ) z) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_right _ _) hFK.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hFK.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩
  have hVopDzF' : Work.FTS.RegPkgGal.C1Jet α S (max Ne Nf) (fun z θ τ =>
      Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
            (Work.Construction.Ftau (pExp α) (SG α g) τ) (gSlice (SΨ α Φs E g) τ)) z θ
          * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (pExp α) (SG α g) τ z θ) z θ) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_left _ _) hVopDzF.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hVopDzF.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left _ _)⟩
  -- ## the assembly
  exact Work.FTS.RegPkgGal.Der.R5Parts_of_pieces_F (α := α) (S := S)
    (g := SG α g) (Φ := SΨ α Φs E g)
    hα hα13 hS (sol_SG (Φs := Φs) (E := E) hSol) (h0_SG (Φs := Φs) (E := E) hSol)
    hg' hDzg hDthg hF hDthF hDzF hL12g hL12T hL12Fstar hDthFstar hDzFstar
    hRopF hUopF hVopDzF' hFK' hNsJet' hNsZ' hmb hmbh hRz0 hRθ0 hRθπ

end Work.FTS_RegExport.RXR5
