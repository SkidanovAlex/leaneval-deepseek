/-
# `Work.FTS.RegPkgGal.GalMinConv` — the reduction `GalMin → GalHyp`

**THE POINT OF THIS FILE.**  `Assembly.regPkg_of_galerkin` consumes the bundle `GalHyp`, which
still *assumes* five quantities: the sup bounds `hsup` (of `g̃` and of `∂_zg̃`), the `z`-moduli
`hhz`, `hhzp` and the `τ`-moduli `hhτ`, `hhτp`.  Here they are **derived**, from the a-priori class
data of the reduced bundle `GalMin`:

| derived | from | lemma |
|---|---|---|
| `hsup` (sup of `g̃`, `∂_zg̃`) | `RegQ` + uniform `ℋ⁴` bound + `StData.quad` (at `z → 0`) | `Der.sup_extG_ext` |
| `hsup2` (sup of `∂_z²g̃`) | `RegQ` + `ℋ⁴`-bound (for `z ≥ 1`) + `StData2.quad2` (at `z → 0`) | `Der.sup2_extG_ext` |
| `hhz` (z-modulus of `g̃`) | `hsup` + the `C¹` gluing `R1b.extG_cont` | `Der.hzmod` |
| `hhzp` (z-modulus of `∂_zg̃`) | `hsup2` + `SmoothQuad` + `R1b.extG_cont` | `Der.hzmodp_ext` |
| `hhτ` (τ-modulus of `g̃`) | the Jet of `∂_τg̃` (`R5f.jet_dtg_of_rhs`) | `Der.htaumod` |
| `hhτp` (τ-modulus of `∂_zg̃`) | `∂_τg̃ = dynLin+dynRHS` + `R5Slot.hRHz` | `Der.htaumodp` |

Three further fields are derived rather than assumed:

* `hsm1` (`C¹` on the open quadrant at every strip time) — from `RegPkgMin.c4` (the `C⁴` field), by
  order monotonicity and the definition of the extension;
* `hfar` (the far-field `Γ`-bound) — from the support propagation `R7e.support_strip_zL` together
  with `Der.far_of_support`;
* the R7 velocity's Lipschitz constant is only asked on `z > Lz7` in `GalMin` (design item R-a),
  which is what the backward characteristics see.

Consequently the input side of the deliverable is reduced to `GalMin` plus the R5 slot, and the
`∀ S > 0` statement becomes `GalMinAssembly.forall_regPkg_of_galMin`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.GalHyp
import Submission.Work.FTS.RegPkgGal.GalMin
import Submission.Work.FTS.RegPkgGal.R5Slot
import Submission.Work.FTS.RegPkgGal.R5f.jet_dtg_of_rhs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.R1b.extG_cont
import Submission.Work.FTS.RegPkgGal.R1c.extG_cont
import Submission.Work.FTS.RegPkgGal.R7e.support_strip_zL
import Submission.Work.FTS.RegPkgGal.Der.sup_extG_ext
import Submission.Work.FTS.RegPkgGal.Der.sup2_extG_ext
import Submission.Work.FTS.RegPkgGal.Der.hzmod
import Submission.Work.FTS.RegPkgGal.Der.hzmodp_ext
import Submission.Work.FTS.RegPkgGal.Der.htaumod
import Submission.Work.FTS.RegPkgGal.Der.htaumodp
import Submission.Work.FTS.RegPkgGal.Der.far_of_support
import Submission.Work.FTS.RegPkgGal.Der.endpoint_cont

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

/-- The right-hand side of the fake-time equation, as a `Fam`. -/
abbrev rhsFam (α : ℝ) (g Φ : Fam) : Fam :=
  fun z θ τ => Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
    + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z θ

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

/-- **THE REDUCTION.**  From the reduced bundle `GalMin` (the class data `StData`, `StData2`, the
frozen interior class `RegQ (pExp α) 4` and the uniform `ℋ⁴` bound, the two angular moduli, the
lead's `RegPkgMin`, the R1/R7 equation data and the clock) together with the R5 slot (the Jet of the
right-hand side, its boundary values, and its `z`-differentiability `hRHz`), the full bundle
`GalHyp` is obtained: the five quantities it used to assume are derived here. -/
theorem galHyp_of_galMin {α S : ℝ} {g Φ : Fam} {m : ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    {a b c Lz7 N0 : ℝ} (H : GalMin α S g m Vz Vθ cs a b c Lz7)
    (H5 : R5Slot α S g Φ N0) :
    ∃ M Lz Lθ Lt Nz Nθ Nt : ℝ,
      GalHyp α S g m Vz Vθ cs a b c Lz7 M Lz Lθ Lt Nz Nθ Nt := by
  obtain ⟨hα, hα13, hS, hmin, hm, hmb, hmh, hSt1, hRQ, hHkn,
    hbase, hj0, hjz, hjdz, hjdt, hd1, hd1z, hd1z2, ht0, hFjoint, hVjoint, hVlipU,
    hcscont, hEq, hVz0, hVza, hVθb, hVθ0, hVθπ, hcsc, hInit, hsuppOut, hLz7, ha, hb, hc⟩ := H
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- the class data of `StData (extG g)` / `StData2 (extG g)`
  obtain ⟨_, Q, _, hQ, hquad⟩ := hSt1.hSt.quad
  -- the angular vanishing of the slices (`RegPkgMin.vanish`)
  have hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ => hmin.vanish τ hτ.1
  -- the angular endpoint continuity, from the class trace condition `BdryTraces` (R-c)
  have hcont01 := Der.endpoint_cont hα hS hvan (fun τ hτ => (hRQ τ hτ).2.2)
  have hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
        (nhds (extG g z 0 τ)) := hcont01.1
  have hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (extG g z (Real.pi / 2) τ)) := hcont01.2
  -- `C¹` on the open quadrant at every strip time, from `RegPkgMin.c4`
  have hsm1 : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => extG g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := by
    intro τ hτ
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => extG g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
      (hmin.c4 τ hτ.1).congr (fun p hp => extG_of_pos hp.1 hτ.1)
    exact h4.of_le (by norm_num)
  -- the small-`z` bound on `∂_z g̃` (`StData.quad`'s second clause)
  have hquad' : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z :=
    ⟨Q, hQ, fun τ hτ θ hθ z hz hz2 => (hquad τ hτ θ hθ).2 z hz hz2⟩
  -- the sup bounds of `g̃` and `∂_zg̃`
  obtain ⟨M, hM, hsup⟩ := Der.sup_extG_ext hα hα13 hS hRQ hHkn hvan hquad'
  have hsupP : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M :=
    ⟨M, hM, fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).2⟩
  -- the second-order `z`-bound of `∂_z²g̃`
  obtain ⟨M₂, hM₂, hsup2⟩ := Der.sup2_extG_ext hα hα13 hS hRQ hHkn hvan hSt1.hSt2.quad2
  -- the `C¹` gluing of the extension (R1b)
  have hcontR1 : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) :=
    R1c.extG_cont hS hbase hj0 hjz hjdz hjdt hd1 hd1z hd1z2 ht0
  -- the `z`-moduli (R3, from the sup data)
  obtain ⟨Lz, hLzn, hhz⟩ := Der.hzmod hα hα1 hS hcontR1 ⟨M, hM, hsup⟩
  obtain ⟨Nz, hNzn, hhzp⟩ := Der.hzmodp_ext hα hα1 hS
    (fun τ hτ => (hRQ τ hτ).1) hcontR1 hvan hsupP ⟨M₂, hM₂, hsup2⟩
  -- the Jet of `∂_τg̃` (the proved R5, from the right-hand side's Jet)
  have hdt : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => extG g z θ s) τ) :=
    R5f.jet_dtg_of_rhs hα hα13 hS hmin H5.hsol H5.h0 H5.hRHS H5.hRz0 H5.hRθ0 H5.hRθπ
  -- the `τ`-modulus of `g̃`
  obtain ⟨Lt, hLtn, hhτ⟩ := Der.htaumod hα hα1 hS hcontR1 hdt ⟨M, hM, hsup⟩
  -- the `τ`-modulus of `∂_zg̃`, from `∂_τg̃ = dynLin + dynRHS` and its `z`-differentiability
  have hid := R5f.deriv_extG_eq_rhs_of_jet hmin H5.hsol H5.h0 H5.hRz0 H5.hRθ0 H5.hRθπ
  obtain ⟨Nt, hNtn, hhτp⟩ :=
    Der.htaumodp (g := g) (R := rhsFam α g Φ) hα hα1 hS hcontR1 hid H5.hRHz hvan hsupP
  -- the support propagation (R7e: the velocity's Lipschitz constant is needed only on `z > Lz7`)
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
  -- the far-field `Γ`-bound, from the support and `F_* ≲ Γ`
  have hfar : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z →
      θ ∈ Work.Spaces.Iθ → |extG g z θ τ| ≤ Cf * Gamma α θ :=
    Der.far_of_support hα hα13 hsupp
  -- the two angular moduli (class data)
  obtain ⟨Lθ, hLθn, hhθ⟩ := hSt1.hhθ
  obtain ⟨Nθ, hNθn, hhθp⟩ := hSt1.hhθp
  exact ⟨M, Lz, Lθ, Lt, Nz, Nθ, Nt,
    { hα := hα, hα13 := hα13, hS := hS, hmin := hmin, hm := hm, hmb := hmb, hmh := hmh,
      hSt := hSt1.hSt, hsm1 := hsm1, hcont0 := hcont0, hcontπ := hcontπ, hfar := hfar, hsup := hsup,
      hhz := hhz, hhθ := hhθ, hhτ := hhτ, hhzp := hhzp, hhθp := hhθp, hhτp := hhτp,
      hbase := hbase, hj0 := hj0, hjz := hjz, hjdz := hjdz, hjdt := hjdt, hd1 := hd1,
      hd1z := hd1z, hd1z2 := hd1z2, ht0 := ht0, hFjoint := hFjoint, hVjoint := hVjoint,
      hVlipU := hVlipU, hcscont := hcscont, hEq := hEq, hVz0 := hVz0, hVza := hVza,
      hVθb := hVθb, hVθ0 := hVθ0, hVθπ := hVθπ, hcsc := hcsc, hInit := hInit,
      hsuppOut := ⟨Lout, hLout, hsuppOut'⟩, hLz7 := hLz7, ha := ha, hb := hb, hc := hc,
      hMn := hM,
      hLzn := hLzn, hLθn := hLθn, hLtn := hLtn, hNzn := hNzn, hNθn := hNθn, hNtn := hNtn }⟩

end Work.FTS.RegPkgGal
