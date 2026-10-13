/-
# `Work.FTS_RegExport.Supp` — RX-Supp: the compact `z`-support of the full profile

Producer RX-Supp of `RegExportIface.Producers`:

> `suppExport`: for `τ ∈ [0,S]` and `z > Lz7 · e^{aS}`, the full profile
> `F = F_* + g̃ = profFull α (extG g)` vanishes; the per-`τ` threshold is the datum radius
> `Lz7` propagated by the finite-speed bound `a = sup Vz`.

The mathematical content is `Work.FTS.RegPkgGal.R7e.support_strip_zL` (finite speed of
propagation for the transport equation `(E)`); the two angular endpoints `θ = 0, π/2` are not
covered by that lemma (it only states the interior angles) and are discharged from
`RegPkgMin.vanish`: `F_*` vanishes at the endpoints and the perturbation `g̃` does too.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.Basic
import Submission.Work.FTS.RegPkgGal.R7e.support_strip_zL
import Submission.Work.FTS.RegPkgGal.R1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- `Gam α 0 = 0` for `α ≠ 0`. -/
theorem Gam_zero_left {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  have h : (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < α / 3))]

/-- `Gam α (π/2) = 0` for `α ≠ 0`. -/
theorem Gam_zero_pi {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  have h : (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < α / 3))]

/-- `F_*(·,0) = 0`. -/
theorem Fstar_zero_left {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_left hα]
  ring

/-- `F_*(·,π/2) = 0`. -/
theorem Fstar_zero_pi {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (π / 2) = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_pi hα]
  ring

/-- **RX-Supp.**  The full profile `F = F_* + g̃` vanishes for `τ ∈ [0,S]` and
`z > Lz7 · e^{aS}`, at every angle `θ ∈ Iθ`. -/
theorem suppExport_proved {S a b c Lz7 : ℝ} {g : Fam} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} (hS : 0 < S)
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (pExp α) g) (hα : 0 < α)
    (H : Work.FTS.RegExportIface.R7Block α S g Vz Vθ cs a b c Lz7) :
    ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → θ ∈ Work.Spaces.Iθ →
      Work.FTS.Regularity.profFull α (extG g) z θ τ = 0 := by
  have hsupp7 : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → 0 < θ →
      θ < Real.pi / 2 → Work.FTS.Regularity.profFull α (extG g) z θ τ = 0 :=
    Work.FTS.RegPkgGal.R7e.support_strip_zL (S := S) (a := a) (b := b) (c := c) (L := Lz7)
      hS H.ha H.hb H.hc H.hLz7 (F := fun z θ τ => Work.FTS.Regularity.profFull α (extG g) z θ τ)
      H.hFjoint H.hVjoint H.hVlipU H.hcscont H.hEq H.hVz0 H.hVza H.hVθb H.hVθ0 H.hVθπ H.hcsc
      H.hInit
  intro τ hτ z θ hz hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Work.FTS.Regularity.profFull_apply, Fstar_zero_left (Work.FTS.Regularity.pExp_pos hα) z, zero_add,
      show extG g z 0 τ = 0 from (Work.FTS.RegPkgGal.extG_hvt hmin.vanish τ hτ).1 z]
  · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
    · subst hπ
      rw [Work.FTS.Regularity.profFull_apply, Fstar_zero_pi (Work.FTS.Regularity.pExp_pos hα) z, zero_add,
        show extG g z (π / 2) τ = 0 from
          (Work.FTS.RegPkgGal.extG_hvt hmin.vanish τ hτ).2 z]
    · exact hsupp7 τ hτ z θ hz h0 hπ

end Work.FTS_RegExport
