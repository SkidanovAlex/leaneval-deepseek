/-
# `Work.FTS_RegExport.RX0.MainRecut` — `GalMin'` + R5 ⇒ `RegPkg'`

This is the re-cut of `Work.FTS.RegPkgGal.PartsAssembly.forall_regPkg_of_parts`: the input bundle
`GalMin` is replaced by the re-cut bundle `Work.FTS.RegExportIface.GalMin'`, in which the field

  `hRQ : ∀ τ ∈ Icc 0 S, RegQ (pExp α) 4 (gSlice g τ)`

is replaced by the (producible) interior order-`≤ 2` sup bound `hIS`.  The proof is the proof of
`Work.FTS.RegPkgGal.GalMinConv.galHyp_of_galMin` with its four uses of `hRQ` replaced:

* `Der.endpoint_cont` (only the `a = b = 0` conjunct of `BdryTraces`) ⟶
  `RecutAux.endpoint_cont_of_holder` (from `St1Class.hhθ`);
* `Der.sup_extG_ext` ⟶ `RecutAux.sup_extG_ext_hIS`;
* `Der.sup2_extG_ext` ⟶ `sup2_extG_ext_hIS` (from `hIS` and `RegPkgMin.c4`);
* `Der.hzmodp_ext` (using only `SmoothQuad`) ⟶ `hzmodp_ext_c4` (from `RegPkgMin.c4`).

Every other step is `GalMinConv`'s verbatim.  The conclusion is the one of the deliverable, so the
file also proves the requested `forallRegPkgOfParts` (in `RX0/forallRegPkgOfParts.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS_RegExport.RX0.RecutAux
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RX0.hzmodp_ext_c4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS_RegExport.RX0

open Work.FTS.Regularity
open Work.FTS.RegPkgGal (extG extG_of_pos extG_of_nonpos)
open Work.FTS.RegPkgGal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The right-hand side of the fake-time equation, as a `Fam` (copy of the abbreviation of
`GalMinConv`, which is not exported under a usable name). -/
abbrev rhsFam' (α : ℝ) (g Φ : Fam) : Fam :=
  fun z θ τ => Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
    + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z θ

private lemma Gam_zero_at_rx0 (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  have h : (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Gam_zero_pi_rx0 (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  have h : (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Fstar_zero_left_rx0 (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_at_rx0 α hα, zero_div]
  ring

private lemma Fstar_zero_pi_rx0 (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (π / 2) = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_pi_rx0 α hα, zero_div]
  ring

/-- **THE RE-CUT REDUCTION.**  `GalMinConv.galHyp_of_galMin` with `GalMin` replaced by
`GalMin'` (i.e. `hRQ` replaced by `hIS`). -/
theorem galHyp_of_galMin' {α S : ℝ} {g Φ : Fam} {m : ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    {a b c Lz7 N0 : ℝ} (H : Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : R5Slot α S g Φ N0) :
    ∃ M Lz Lθ Lt Nz Nθ Nt : ℝ,
      GalHyp α S g m Vz Vθ cs a b c Lz7 M Lz Lθ Lt Nz Nθ Nt := by
  have hα := H.hα
  have hα13 := H.hα13
  have hS := H.hS
  have hmin := H.hmin
  have hm := H.hm
  have hmb := H.hmb
  have hmh := H.hmh
  have hSt1 := H.hSt1
  have hHkn := H.hHkn
  have hbase := H.hbase
  have hj0 := H.hj0
  have hjz := H.hjz
  have hjdz := H.hjdz
  have hjdt := H.hjdt
  have hd1 := H.hd1
  have hd1z := H.hd1z
  have hd1z2 := H.hd1z2
  have ht0 := H.ht0
  have hFjoint := H.hFjoint
  have hVjoint := H.hVjoint
  have hVlipU := H.hVlipU
  have hcscont := H.hcscont
  have hEq := H.hEq
  have hVz0 := H.hVz0
  have hVza := H.hVza
  have hVθb := H.hVθb
  have hVθ0 := H.hVθ0
  have hVθπ := H.hVθπ
  have hcsc := H.hcsc
  have hInit := H.hInit
  have hsuppOut := H.hsuppOut
  have hLz7 := H.hLz7
  have ha := H.ha
  have hb := H.hb
  have hc := H.hc
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- the class data of `StData (extG g)` / `StData2 (extG g)`
  obtain ⟨_, Q, _, hQ, hquad⟩ := hSt1.hSt.quad
  -- the angular vanishing of the slices (`RegPkgMin.vanish`)
  have hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ => hmin.vanish τ hτ.1
  -- the angular endpoint continuity, from the `θ`-Hölder class data `St1Class.hhθ` (re-cut)
  have hcont01 := endpoint_cont_of_holder hα hvan hSt1.hhθ
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
  -- the sup bounds of `g̃` and `∂_zg̃`, from `hIS` (re-cut)
  obtain ⟨M, hM, hsup⟩ := sup_extG_ext_hIS hS H.hIS hvan hquad'
  have hsupP : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M :=
    ⟨M, hM, fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).2⟩
  -- the second-order `z`-bound of `∂_z²g̃`, from `hIS` and `c4` (re-cut)
  obtain ⟨M₂, hM₂, hsup2⟩ := sup2_extG_ext_hIS hα hS H.hIS
    (fun τ hτ => hmin.c4 τ hτ.1) hvan hSt1.hSt2.quad2
  -- the `C¹` gluing of the extension (R1b)
  have hcontR1 : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) :=
    R1c.extG_cont hS hbase hj0 hjz hjdz hjdt hd1 hd1z hd1z2 ht0
  -- the `z`-moduli (R3, from the sup data)
  obtain ⟨Lz, hLzn, hhz⟩ := Der.hzmod hα hα1 hS hcontR1 ⟨M, hM, hsup⟩
  obtain ⟨Nz, hNzn, hhzp⟩ := hzmodp_ext_c4 hα hα1 hS (fun τ hτ => hmin.c4 τ hτ.1)
    hcontR1 hvan hsupP ⟨M₂, hM₂, hsup2⟩
  -- the Jet of `∂_τg̃` (the proved R5, from the right-hand side's Jet)
  have hdt : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => extG g z θ s) τ) :=
    R5f.jet_dtg_of_rhs hα hα13 hS hmin H5.hsol H5.h0 H5.hRHS H5.hRz0 H5.hRθ0 H5.hRθπ
  -- the `τ`-modulus of `g̃`
  obtain ⟨Lt, hLtn, hhτ⟩ := Der.htaumod hα hα1 hS hcontR1 hdt ⟨M, hM, hsup⟩
  -- the `τ`-modulus of `∂_zg̃`, from `∂_τg̃ = dynLin + dynRHS` and its `z`-differentiability
  have hid := R5f.deriv_extG_eq_rhs_of_jet hmin H5.hsol H5.h0 H5.hRz0 H5.hRθ0 H5.hRθπ
  obtain ⟨Nt, hNtn, hhτp⟩ :=
    Der.htaumodp (g := g) (R := rhsFam' α g Φ) hα hα1 hS hcontR1 hid H5.hRHz hvan hsupP
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
          rw [profFull, Fstar_zero_left_rx0 (pExp α) (pExp_pos hα) z, zero_add,
            show extG g z 0 τ = 0 from (extG_hvt hmin.vanish τ hτ).1 z]
        · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
          · subst hπ
            rw [profFull, Fstar_zero_pi_rx0 (pExp α) (pExp_pos hα) z, zero_add,
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
      hSt := hSt1.hSt, hsm1 := hsm1, hcont0 := hcont0, hcontπ := hcontπ, hfar := hfar,
      hsup := hsup, hhz := hhz, hhθ := hhθ, hhτ := hhτ, hhzp := hhzp, hhθp := hhθp,
      hhτp := hhτp, hbase := hbase, hj0 := hj0, hjz := hjz, hjdz := hjdz, hjdt := hjdt,
      hd1 := hd1, hd1z := hd1z, hd1z2 := hd1z2, ht0 := ht0, hFjoint := hFjoint,
      hVjoint := hVjoint, hVlipU := hVlipU, hcscont := hcscont, hEq := hEq, hVz0 := hVz0,
      hVza := hVza, hVθb := hVθb, hVθ0 := hVθ0, hVθπ := hVθπ, hcsc := hcsc, hInit := hInit,
      hsuppOut := ⟨Lout, hLout, hsuppOut'⟩, hLz7 := hLz7, ha := ha, hb := hb, hc := hc,
      hMn := hM,
      hLzn := hLzn, hLθn := hLθn, hLtn := hLtn, hNzn := hNzn, hNθn := hNθn, hNtn := hNtn }⟩

/-- **THE RE-CUT DELIVERABLE.**  `PartsAssembly.forall_regPkg_of_parts` with `GalMin` replaced by
`GalMin'`. -/
theorem forall_regPkg_of_parts' {α : ℝ} {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  intro S hS
  obtain ⟨Lz7, hH⟩ := H S hS
  obtain ⟨N0, h5⟩ := R5Slot_of_R5Parts hH.hα hH.hα13 hH.hS (H5 S hS)
  obtain ⟨M, Lz, Lθ, Lt, Nz, Nθ, Nt, hgal⟩ := galHyp_of_galMin' hH h5
  exact regPkg_of_galerkin hgal h5

end Work.FTS_RegExport.RX0
