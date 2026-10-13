/-
# `Work.FTS.RegPkgGal.Assembly` — the assembly of `RegPkg'` (design §4, item 10)

**THE MAIN RESULT OF THIS AREA:**

  `regPkg_of_galerkin`: from the input bundle `GalHyp` (`GalHyp.lean` — the lead's `RegPkgMin`, the
  class data `StData` of `g̃`, the angular endpoint continuity, the sup/Lipschitz data, the R1
  joint-limit data, the R7 transport data, and the modulation data of design §2) together with the
  single remaining slot — the fake-time jet `hgdoth` of R5 (`R5c.jet_dtg`, under proof) — the
  corrected regularity package

    `RegPkg' α S (Avort m) (Bdyn m) (extG g)`

  holds; `forall_regPkg_of_galerkin` is the same for an `S`-indexed bundle, i.e. the promised shape
  `∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g)`.

Every field of `RegPkg'` is *derived*:

* the ten clock clauses — `R6.clock_fields` (design §2);
* `hvt`, `hquad0`, `hquad` — `R1.lean` (`extG` is `0` on `z ≤ 0`, so its `z`-derivative at `0`
  is `0`) and `R1.extG_hvt` + `RegPkgMin.vanish`;
* `htay` — `R2c.tay_clauses` (the Hölder form of design correction 5);
* `hg`, `hpz` — `R3b.jet_g`;
* `hvan` — `R4d.van_global` (the *applicable* version: `C¹` on the open quadrant plus continuity
  at the angular endpoints, since the genuine profile is continuous but not `C¹` there);
* `hH4` — `R8.mem4_extG`;
* `hcont` — `R1b.extG_cont` (the `C¹`-gluing across `z = 0` and `τ = 0`, with the *joint* limits);
* `hsupp` — `R7d.support_strip` (finite speed of propagation) plus the two angular endpoint values.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.GalHyp
import Submission.Work.FTS.RegPkgGal.R5Slot
import Submission.Work.FTS.RegPkgGal.R5f.jet_dtg_of_rhs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.R1b.extG_cont
import Submission.Work.FTS.RegPkgGal.R1c.extG_cont
import Submission.Work.FTS.RegPkgGal.R2c.tay_clauses
import Submission.Work.FTS.RegPkgGal.R3d.jet_g
import Submission.Work.FTS.RegPkgGal.R4d.van_global
import Submission.Work.FTS.RegPkgGal.R6.clock_fields
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.RegPkgGal.R7e.support_strip_zL
import Submission.Work.FTS.RegPkgGal.R8

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma Gam_zero_at (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  have h : (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Gam_zero_pi (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  have h : (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Fstar_zero_left (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_at α hα, zero_div]
  ring

private lemma Fstar_zero_pi (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (π / 2) = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_pi α hα, zero_div]
  ring

/-- **THE ASSEMBLY.**  From the input bundle and the single remaining slot `hgdoth` (R5's
fake-time jet), the corrected package `RegPkg'` for `g̃ = extG g` and the clock
`(Avort m, Bdyn m)` of design §2. -/
theorem regPkg_of_galerkin {α S : ℝ} {g Φ : Fam} {m : ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    {a b c Lz7 M Lz Lθ Lt Nz Nθ Nt N0 : ℝ}
    (H : GalHyp α S g m Vz Vθ cs a b c Lz7 M Lz Lθ Lt Nz Nθ Nt)
    (H5 : R5Slot α S g Φ N0) :
    RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  obtain ⟨hα, hα13, hS, hmin, hm, hmb, hmh, hSt, hsm1, hcont0, hcontπ, hfar, hsup, hhz,
    hhθ, hhτ, hhzp, hhθp, hhτp, hbase, hj0, hjz, hjdz, hjdt, hd1, hd1z, hd1z2,
    ht0, hFjoint, hVjoint, hVlipU, hcscont, hEq, hVz0, hVza, hVθb, hVθ0, hVθπ, hcsc, hInit,
    hsuppOut, hLz7, ha, hb, hc, hMn, hLzn, hLθn, hLtn, hNzn, hNθn, hNtn⟩ := H
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- R5: the fake-time jet of `g̃` from the a-priori regularity of the right-hand side
  have hgdoth : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => extG g z θ s) τ) :=
    R5f.jet_dtg_of_rhs hα hα13 hS hmin H5.hsol H5.h0 H5.hRHS H5.hRz0 H5.hRθ0 H5.hRθπ
  -- the ten clock clauses (design §2, R6)
  obtain ⟨hA, hB, hAb, hBb, hAdiff, hBdiff, hAd, hBd, hAdh, hBdh⟩ :=
    R6.clock_fields hα hα1 hS hm hmb hmh
  -- the class data of `StData (extG g)`
  obtain ⟨Cθ, hCθ, hDth⟩ := hSt.dthvan
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt.quad
  -- `hvan` (R4d) for `g̃`
  obtain ⟨Cf, hCf, hfar'⟩ := hfar
  obtain ⟨Cv, hCv, hvan'⟩ := R4d.van_global hα hS hCθ hCf hsm1
    (fun τ _ θ _ => extG_hquad0 g τ θ) hcont0 hcontπ hDth (extG_hvt hmin.vanish) hfar'
  -- `htay` (R2c) for `g̃`
  have htay := R2c.tay_clauses hα hα1 hS hCθ hK hQ hsm1 hcont0 hcontπ
    (fun τ _ θ _ => extG_hquad0 g τ θ) hDth (extG_hvt hmin.vanish)
    (fun τ hτ θ hθ => (hquad τ hτ θ hθ).1) (fun τ hτ θ hθ => (hquad τ hτ θ hθ).2)
  -- the two jets (R3d: `α`-Hölder moduli, the satisfiable version) for `g̃`
  obtain ⟨hg, hpzjet⟩ := R3d.jet_g hα hα1 hS hMn hLzn hLθn hLtn hNzn hNθn hNtn
    hsup hhz hhθ hhτ hhzp hhθp hhτp
  -- `hcont` (R1b)
  have hcont := R1c.extG_cont hS hbase hj0 hjz hjdz hjdt hd1 hd1z hd1z2 ht0
  -- `hsupp` (R7d + the two angular endpoint values)
  have hsupp7 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → 0 < θ →
      θ < Real.pi / 2 → profFull α (extG g) z θ τ = 0 :=
    R7e.support_strip_zL (S := S) (a := a) (b := b) (c := c) (L := Lz7) hS ha hb hc hLz7
      (F := fun z θ τ => profFull α (extG g) z θ τ) hFjoint hVjoint hVlipU hcscont hEq
      hVz0 hVza hVθb hVθ0 hVθπ hcsc hInit
  obtain ⟨Lout, hLout, hsuppOut'⟩ := hsuppOut
  have hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
      profFull α (extG g) z θ τ = 0 := by
    refine ⟨max (Lz7 * Real.exp (a * S) + 1) (Lout + 1), ?_, ?_⟩
    · have h1 : 0 < Lz7 * Real.exp (a * S) + 1 := by
        have h2 : 0 ≤ Lz7 * Real.exp (a * S) :=
          mul_nonneg hLz7 (le_of_lt (Real.exp_pos _))
        linarith
      exact lt_of_lt_of_le h1 (le_max_left _ _)
    · intro τ hτ z θ hz
      have hz7 : Lz7 * Real.exp (a * S) < z :=
        lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_left _ _) hz)
      have hzout : Lout < z :=
        lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hz)
      by_cases hθ : θ ∈ Work.Spaces.Iθ
      · rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · subst h0
          rw [profFull, Fstar_zero_left (pExp α) (pExp_pos hα) z, zero_add,
            show extG g z 0 τ = 0 from (extG_hvt hmin.vanish τ hτ).1 z]
        · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
          · subst hπ
            rw [profFull, Fstar_zero_pi (pExp α) (pExp_pos hα) z, zero_add,
              show extG g z (π / 2) τ = 0 from (extG_hvt hmin.vanish τ hτ).2 z]
          · exact hsupp7 τ hτ z θ hz7 h0 hπ
      · exact hsuppOut' τ hτ z θ (le_of_lt hzout) hθ
  exact
    { hα := hα
      hα13 := hα13
      hS := hS
      hA := hA
      hB := hB
      hAb := hAb
      hBb := hBb
      hAdiff := hAdiff
      hBdiff := hBdiff
      hAd := hAd
      hBd := hBd
      hAdh := hAdh
      hBdh := hBdh
      hvt := extG_hvt hmin.vanish
      hquad0 := fun τ _ θ _ => extG_hquad0 g τ θ
      hquad := fun τ _ θ _ => extG_hquad g τ θ
      hg := hg
      hpz := hpzjet
      hgdoth := hgdoth
      hvan := ⟨Cv, hCv, hvan'⟩
      htay := htay
      hsupp := hsupp
      hH4 := mem4_extG hmin
      hcont := hcont }

/-- **THE DELIVERABLE'S SHAPE.**  If the input bundle and the R5 slot are available at every strip
size `S > 0`, then so is the package: `∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g)`. -/
theorem forall_regPkg_of_galerkin {α : ℝ} {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (H : ∀ S > 0, ∃ Lz7 M Lz Lθ Lt Nz Nθ Nt : ℝ,
      GalHyp α S g m Vz Vθ cs a b c Lz7 M Lz Lθ Lt Nz Nθ Nt)
    (H5 : ∀ S > 0, ∃ N0 : ℝ, R5Slot α S g Φ N0) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  intro S hS
  obtain ⟨Lz7, M, Lz, Lθ, Lt, Nz, Nθ, Nt, hH⟩ := H S hS
  obtain ⟨N0, h5⟩ := H5 S hS
  exact regPkg_of_galerkin hH h5

end Work.FTS.RegPkgGal
