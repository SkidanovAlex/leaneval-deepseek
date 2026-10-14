import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Final.Defs
import Submission.Work.FTS.MeridianDyn.Main
import Submission.Work.FTS.Physical.Meridian
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
-- ===== merged: Submission.Work.FTS.Final.ExtG.dynOK_extG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.Final.ExtG

set_option autoImplicit false

/-! ## Congruence of the weighted `H^k` integrand on the positive half-plane

These are the general (all `k`, all `α`) forms of the congruence argument of
`Work.FTS.RegPkgGal.R8`: the operators are local, so agreement on `z > 0` pins every integrand on
the domain `Iz = [0,∞)`, the point `z = 0` being trivial because `w 0 = 0`. -/

namespace HkAux

/-- The `H^k`-integrand of two functions that agree on the open half-plane `z > 0` agrees at every
point with `z > 0`.  (Every `DzIter`/`mixed` is a local differential operator, and the weights
only depend on `(z,θ)`.) -/
lemma HkIntegrand_congr_of_pos {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.HkIntegrand α k u z θ = Work.Spaces.HkIntegrand α k v z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : Set.EqOn (Function.uncurry u) (Function.uncurry v)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact h z' hz' θ'
  have hmem : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hz, trivial⟩
  simp only [Work.Spaces.HkIntegrand]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hh := Work.FTS.RegPkgGal.DzIter_congr_of_isOpen hV hagree i hmem
    simp only [Function.uncurry] at hh
    rw [hh]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hij : 1 ≤ i ∧ i + j ≤ k
    · simp only [hij]
      have hh := Work.FTS.RegPkgGal.mixed_congr_of_isOpen hV hagree j i hmem
      simp only [Function.uncurry] at hh
      rw [hh]
    · simp only [hij, ite_false]

/-- The `H^k`-integrand congruence on the whole domain `Iz = [0,∞)`: the open half-plane is the
previous lemma, and at `z = 0` both integrands vanish (`w 0 = 0`). -/
lemma HkIntegrand_eq_of_mem_Iz {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Work.Spaces.HkIntegrand α k u z θ = Work.Spaces.HkIntegrand α k v z θ := by
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with hz0 | hzpos
  · subst hz0
    rw [Work.Coercivity.HkIntegrand_zero_left, Work.Coercivity.HkIntegrand_zero_left]
  · exact HkIntegrand_congr_of_pos h hzpos

/-- `HkSq` is insensitive to a change of the function on `z > 0`: the integrand agrees on `Iz`. -/
lemma HkSq_eq_of_Ioi {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) :
    Work.Spaces.HkSq α k u = Work.Spaces.HkSq α k v := by
  show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
    = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k v z θ)
  simp only [Work.Spaces.Iz, Work.Spaces.Iθ]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => HkIntegrand_eq_of_mem_Iz h hz)

/-- `HkNorm` (and hence `Xn`) is insensitive to a change of the function on `z > 0`. -/
lemma HkNorm_eq_of_Ioi {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) :
    Work.Spaces.HkNorm α k u = Work.Spaces.HkNorm α k v := by
  simp only [Work.Spaces.HkNorm]
  rw [HkSq_eq_of_Ioi h]

end HkAux

/-! ## The pointwise coincidences for the extension `g̃ = extG g` -/

/-- On `z > 0` and `τ ≥ 0` the extension is the family itself. -/
lemma slice_extG_eq_of_pos {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.FTS.Galerkin.slice g τ z θ := by
  simp only [Work.FTS.Galerkin.slice]
  exact Work.FTS.RegPkgGal.extG_of_pos hz hτ

/-- The `ℋ⁴`-size of the extended slice equals that of the original slice, for `τ ≥ 0`. -/
lemma Xn_extG_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ)
      = Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) :=
  HkAux.HkNorm_eq_of_Ioi (k := 4) (fun _z hz _ => slice_extG_eq_of_pos hτ hz)

/-- The `ℋ^k`-membership of the extended slice, for `τ ≥ 0`. -/
lemma mem_slice_extG {α : ℝ} {k : ℕ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : Work.Spaces.HkMem α k (Work.FTS.Galerkin.slice g τ)) :
    Work.Spaces.HkMem α k (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ) :=
  Work.Coercivity.HkMem_congr_Ioi α k h
    (fun _z hz _ _ => (slice_extG_eq_of_pos hτ hz).symm)

/-- The fake-time derivative of the extension is that of the family on `z > 0`, for `τ > 0`
(the `τ`-derivative is local, and for `z > 0` the two functions agree on a neighbourhood of `τ`). -/
lemma gdot_extG_eq_of_pos {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 < τ) (hz : 0 < z) :
    Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.FTS.Galerkin.gdot g τ z θ := by
  have hev : (fun s => Work.FTS.RegPkgGal.extG g z θ s) =ᶠ[𝓝 τ] (fun s => g z θ s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
    exact Work.FTS.RegPkgGal.extG_of_pos hz (le_of_lt hs)
  simpa only [Work.FTS.Galerkin.gdot] using hev.deriv_eq

/-! ## The four structural fields of `RegPkgMin` -/

/-- The horizon-local `ℋ³`-bound on `∂_τ g` transfers to the extension. -/
lemma dbd_extG {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (h : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ)
      ∧ Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd) :
    ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ)
      ∧ Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ) ≤ Cd := by
  intro S hS
  obtain ⟨Cd, hCd⟩ := h S hS
  refine ⟨Cd, fun τ hτ hτS => ⟨?_, ?_⟩⟩
  · exact Work.Coercivity.HkMem_congr_Ioi α 3 (hCd τ hτ hτS).1
      (fun z hz _ _ => (gdot_extG_eq_of_pos hτ hz).symm)
  · rw [HkAux.HkNorm_eq_of_Ioi (k := 3) (fun z hz _ => gdot_extG_eq_of_pos hτ hz)]
    exact (hCd τ hτ hτS).2

/-- Vanishing on the two angular boundaries transfers to the extension. -/
lemma vanish_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z →
      Work.FTS.RegPkgGal.extG g z 0 τ = 0 ∧ Work.FTS.RegPkgGal.extG g z (π / 2) τ = 0 := by
  intro τ hτ z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    exact ⟨Work.FTS.RegPkgGal.extG_of_nonpos le_rfl,
      Work.FTS.RegPkgGal.extG_of_nonpos le_rfl⟩
  · obtain ⟨h1, h2⟩ := h τ hτ z (le_of_lt hzpos)
    exact ⟨by rw [Work.FTS.RegPkgGal.extG_of_pos hzpos hτ, h1],
      by rw [Work.FTS.RegPkgGal.extG_of_pos hzpos hτ, h2]⟩

/-- Joint interior `C¹`-regularity transfers to the extension (the slab has `z > 0`, `τ > 0`,
where the extension agrees with the family). -/
lemma c1_extG {g : Work.FTS.Galerkin.Fam}
    (h : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FTS.RegPkgGal.extG g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0) :=
  h.congr (fun _p hp => Work.FTS.RegPkgGal.extG_of_pos hp.1 (le_of_lt hp.2.2))

/-- Spatial `C⁴`-regularity of the slices transfers to the extension (the quadrant `Q0` has
`z > 0`). -/
lemma c4_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0) :
    ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ))
      Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  refine (h τ hτ).congr (fun p hp => ?_)
  show Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ p.1 p.2
    = Work.FTS.Galerkin.slice g τ p.1 p.2
  exact slice_extG_eq_of_pos hτ hp.1

/-- Continuity in fake time up to `τ = 0` at the points of the open quadrant transfers to the
extension. -/
lemma cont_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => Work.FTS.RegPkgGal.extG g z θ τ) (Set.Ici 0) := by
  intro z θ hz
  refine (h z θ hz).congr (fun τ hτ => ?_)
  exact Work.FTS.RegPkgGal.extG_of_pos hz.1 hτ

/-! ## The transport of `DynOK` -/

theorem dynOK_extG {α C₀ : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam}
    (h : Work.FTS.Final.DynOK α C₀ g) :
    Work.FTS.Final.DynOK α C₀ (Work.FTS.RegPkgGal.extG g) := by
  have hα0 : (0 : ℝ) < α := hα
  obtain ⟨hmin, hbd⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact c1_extG hmin.c1
  · exact c4_extG hmin.c4
  · exact cont_extG hmin.cont
  · intro τ hτ; exact mem_slice_extG hτ (hmin.mem4 τ hτ)
  · exact dbd_extG hmin.dbd
  · exact vanish_extG hmin.vanish
  · intro τ hτ
    rw [Xn_extG_eq hτ]
    exact hbd τ hτ

end Work.FTS.Final.ExtG
end
end
-- ===== merged: Submission.Work.FTS.Final.MeridianMin.meridianEq_of_dynEq_of_regPkgMin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology
namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-- **The dynamic meridian bridge, in pointwise form.**  Same statement as
`Work.FTS.MeridianDyn.meridianEq_of_dynEq`, but

* the fake-time equation is the bare `Galerkin.IsDynEqOn` (the bundled elliptic law of
  `IsDynGSolWith` is not used), and
* the regularity package is replaced by the *pointwise* `C¹`-hypothesis `hreg1` on the odd
  extension `profFamOdd (pExp α) g` at the interior points of the slab `Z > 0`, `0 < Θ < π/2`,
  `τ > 0` — which is all of it the argument consumes.

This is the form the strong route (`Work.FTS.StrongGlobal.RegPkgMin`) can instantiate. -/
theorem meridianEq_of_dynEq_of_pointwise {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {A B : ℝ → ℝ} {Φ g : Fam} {C : Work.FTS.Physical.PhysClock}
    (hEq : Galerkin.IsDynEqOn (Regularity.pExp α) Φ g)
    (hreg1 : ∀ Z Θ τ : ℝ, 0 < Z → 0 < Θ → Θ < Real.pi / 2 → 0 < τ →
      ContDiffAt ℝ 1
        (fun p : ℝ × ℝ × ℝ => profFamOdd (Regularity.pExp α) g p.1 p.2.1 p.2.2) (Z, Θ, τ))
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : ProfDerivData (Regularity.pExp α) Φ g)
    (hA : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hmu : ∀ τ : ℝ, 0 ≤ τ → C.mu τ = Galerkin.muDyn (Regularity.pExp α) Φ g τ) :
    MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (merPsi (Regularity.pExp α) A B Φ C) C.T := by
  have hp0 : 0 < Regularity.pExp α := Regularity.pExp_pos hα
  have hp1 : Regularity.pExp α ≤ 1 := Regularity.pExp_le_one hα13
  -- the modulation stays away from `-1`
  have hne : ∀ τ : ℝ, 0 ≤ τ → 1 + Galerkin.muDyn (Regularity.pExp α) Φ g τ ≠ 0 := by
    intro τ hτ h0
    have h1 := C.hmu_lo τ hτ
    have h2 := hmu τ hτ
    rw [h2] at h1
    linarith
  -- the profile equation `(E)` for the odd extension of `F_* + g`
  have hWeak : DynEqF (Regularity.pExp α) (Galerkin.muDyn (Regularity.pExp α) Φ g)
      (profFamOdd (Regularity.pExp α) g) Φ :=
    DynEqF_of_isDynEqOn_odd hp0 hp1 hD hEq hne
  -- the positive half-plane
  have hpos : ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 C.T →
      Work.CoreResiduals.meridianResid (Work.FTS.Physical.merProfile α A B g C)
        (merPsi (Regularity.pExp α) A B Φ C) r z t = 0 := by
    intro r z t hr hz ht
    have hσpos : 0 < Work.FTS.Physical.clockInv C t :=
      Work.FTS.Physical.clockInv_pos_of_pos C ht
    have hσnn : 0 ≤ Work.FTS.Physical.clockInv C t := le_of_lt hσpos
    have hbpos : 0 < B (Work.FTS.Physical.clockInv C t) := hB _ hσnn
    have hApos : 0 < A (Work.FTS.Physical.clockInv C t) := by
      have h1 := hA _ hσnn
      have h2 := C.hApos _ hσnn
      linarith
    have hθpos : 0 < Work.Cyl.thetaP r z := by
      rw [Work.Cyl.thetaP]; exact Real.arctan_pos.mpr (div_pos hz hr)
    have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
      rw [Work.Cyl.thetaP]; exact Real.arctan_lt_pi_div_two _
    have hZpos : 0 < Work.Cyl.rhoP r z ^ Regularity.pExp α
        / B (Work.FTS.Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hbpos
    -- joint `C¹` of the odd extension of the profile
    have hFc : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ × ℝ => profFamOdd (Regularity.pExp α) g q.1 q.2.1 q.2.2)
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z, Work.FTS.Physical.clockInv C t) :=
      hreg1 _ _ _ hZpos hθpos hθlt hσpos
    -- joint `C¹` of the stream function, in the meridian variables
    have hΦc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Φ q.1 q.2 (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) := by
      have hQd : (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := ⟨hZpos, hθpos, hθlt⟩
      have hQdopen : IsOpen Work.Construction.Qd :=
        show IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) from
          isOpen_Ioi.prod isOpen_Ioo
      exact ((hΦ _ hσpos).contDiffAt (hQdopen.mem_nhds hQd)).of_le
        (by norm_num : ((1 : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞))
    -- the fake-time derivative of the profile at the point
    have hFt : HasDerivAt (fun s => profFamOdd (Regularity.pExp α) g
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z) s)
        (deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t))
        (Work.FTS.Physical.clockInv C t) := by
      have hd : DifferentiableAt ℝ (fun s : ℝ => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t) := by
        show DifferentiableAt ℝ
          ((fun q : ℝ × ℝ × ℝ => profFamOdd (Regularity.pExp α) g q.1 q.2.1 q.2.2)
            ∘ fun s : ℝ => (Work.Cyl.rhoP r z ^ Regularity.pExp α
                / B (Work.FTS.Physical.clockInv C t), Work.Cyl.thetaP r z, s))
          (Work.FTS.Physical.clockInv C t)
        exact (hFc.differentiableAt (by norm_num)).comp
          (Work.FTS.Physical.clockInv C t) (by fun_prop)
      exact hd.hasDerivAt
    -- the three chain-rule facts of amplitude, scale and clock
    have hσ' : HasDerivAt (Work.FTS.Physical.clockInv C)
        ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t :=
      Work.FTS.Physical.clockInv_hasDerivAt C ht
    have ha : HasDerivAt (fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
        ((1 + C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * (A (Work.FTS.Physical.clockInv C t))⁻¹) t :=
      Clock.amplitude_hasDerivAt (A := A) (C := C) hAd hApos ht
    have hb : HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
        (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * B (Work.FTS.Physical.clockInv C t)) t :=
      Clock.scale_hasDerivAt (B := B) (C := C) hBd ht
    have hb' : HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
        (-((1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
          * B (Work.FTS.Physical.clockInv C t)) t := by
      convert hb using 1
      ring
    have h2s : 2 * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = (A (Work.FTS.Physical.clockInv C t))⁻¹ := by
      have h1 := hA _ hσnn
      have hne1 : A (Work.FTS.Physical.clockInv C t) ≠ 0 := ne_of_gt hApos
      have hne2 : C.A (Work.FTS.Physical.clockInv C t) ≠ 0 := ne_of_gt (C.hApos _ hσnn)
      rw [h1]
      field_simp
    -- the residual identity of the area
    have hres := meridianResid_dyn (p := Regularity.pExp α)
      (a := fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
      (b := fun s => B (Work.FTS.Physical.clockInv C s))
      (σ := Work.FTS.Physical.clockInv C)
      (F := profFamOdd (Regularity.pExp α) g) (Φ := Φ)
      (r := r) (z := z) (t := t)
      (A' := (1 + C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * (A (Work.FTS.Physical.clockInv C t))⁻¹)
      (B' := -((1 - C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
        * B (Work.FTS.Physical.clockInv C t))
      (sp := (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
      (μa := C.mu (Work.FTS.Physical.clockInv C t))
      (fτ := deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t))
      hr (ne_of_gt hbpos) ha hb' hσ' rfl rfl h2s hFc hΦc hFt
    -- the profile equation `(E)` at the clock time, with the clock's modulation
    have hE : dynEqLHS (Regularity.pExp α) (C.mu (Work.FTS.Physical.clockInv C t))
        (fun Z Θ => profFamOdd (Regularity.pExp α) g Z Θ (Work.FTS.Physical.clockInv C t))
        (fun Z Θ => Φ Z Θ (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        (deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t)) = 0 := by
      have h := hWeak _ _ _ ⟨hZpos, hθpos, hθlt⟩ hσpos
      rw [← hmu _ hσnn] at h
      exact h
    rw [hE, mul_zero] at hres
    exact hres
  -- parity of the meridian pair
  have hWdyn : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      merProfileDyn α A B g C r (-z) t = -merProfileDyn α A B g C r z t := by
    intro r z t hr hz _
    have hθne : Work.Cyl.thetaP r z ≠ 0 := thetaP_ne_zero hr hz
    have hprof := profFamOdd_neg (α := Regularity.pExp α) (g := g)
      (Z := Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
      (Θ := Work.Cyl.thetaP r z) (σ := Work.FTS.Physical.clockInv C t) hθne
    rw [merProfileDyn_apply', merProfileDyn_apply', rhoP_neg, thetaP_neg, hprof]
    ring
  have hWodd : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      Work.FTS.Physical.merProfile α A B g C r (-z) t
        = -Work.FTS.Physical.merProfile α A B g C r z t := by
    intro r z t hr hz ht
    rw [← merProfileDyn_eq]
    exact hWdyn r z t hr hz ht
  have hψodd : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      merPsi (Regularity.pExp α) A B Φ C r (-z) t
        = -merPsi (Regularity.pExp α) A B Φ C r z t := by
    intro r z t _ _ ht
    have hσpos : 0 < Work.FTS.Physical.clockInv C t :=
      Work.FTS.Physical.clockInv_pos_of_pos C ht
    simp only [merPsi, dynPsi_apply]
    rw [rhoP_neg, thetaP_neg, hΦodd _ hσpos]
    ring
  -- assemble
  intro r z t hr hz ht
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have h := Odd.meridianResid_odd_win (T := C.T) hWodd hψodd r (-z) t
      (ne_of_gt hr) (by linarith) ht
    rw [neg_neg] at h
    rw [h, hpos r (-z) t hr (by linarith) ht, neg_zero]
  · exact absurd heq hz
  · exact hpos r z t hr hgt ht


end Work.FTS.MeridianDyn

namespace Work.FTS.Final.MeridianMin

set_option autoImplicit false

/-- **Interior `C¹` of the odd profile from `RegPkgMin`.**  The joint `C¹`-clause of
`Work.FTS.StrongGlobal.RegPkgMin` is `ContDiffOn ℝ 1` on the quadrant slab
`(0,∞) × (0,π/2) × (0,∞)`; at interior points the odd extension `profFamOdd α g` agrees with
`F_* + g` on a neighbourhood, and `F_*` is `C¹` there (`MeridianDyn.Smooth.contDiffAt_Fstar`). -/
theorem profFamOdd_contDiffAt_of_regPkgMin {α : ℝ} (hα : 0 < α) {g : Work.FTS.MeridianDyn.Fam}
    (hreg : Work.FTS.StrongGlobal.RegPkgMin α g) {Z Θ τ : ℝ}
    (hZ : 0 < Z) (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) (hτ : 0 < τ) :
    ContDiffAt ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.FTS.MeridianDyn.profFamOdd α g p.1 p.2.1 p.2.2)
      (Z, Θ, τ) := by
  have hmem : (Z, Θ, τ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
      ×ˢ Set.Ioi (0 : ℝ) := ⟨hZ, ⟨hΘ, hΘ1⟩, hτ⟩
  have hU : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioi (0 : ℝ)
      ∈ 𝓝 (Z, Θ, τ) :=
    (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioi)).mem_nhds hmem
  -- the joint regularity of `g` at the point, from the `c1` clause
  have hg : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Z, Θ, τ) :=
    hreg.c1.contDiffAt hU
  -- the profile `F_*` is `C¹` at the point
  have hF := Work.FTS.MeridianDyn.Smooth.contDiffAt_Fstar α τ hZ hΘ hΘ1
  have hsum : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.Construction.Fstar α p.1 p.2.1 + g p.1 p.2.1 p.2.2)
      (Z, Θ, τ) :=
    hF.add hg
  -- near the point `θ > 0`, so the odd extension is the `0 ≤ θ` branch `F_* + g`
  refine hsum.congr_of_eventuallyEq ?_
  have hpos : {p : ℝ × ℝ × ℝ | 0 < p.2.1} ∈ 𝓝 (Z, Θ, τ) :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hΘ
  filter_upwards [hpos] with p hp
  rw [Work.FTS.MeridianDyn.profFamOdd_apply,
    Work.ConstructionInstance.profile_of_nonneg (le_of_lt hp)]
  rfl

/-- **The meridian bridge at the strong route's interfaces.**  The strong route's regularity
package `RegPkgMin` and the bare fake-time equation imply the meridian scalar equation for the
meridian pair of the physical reconstruction on the time window `(0, C.T)`, off the axis and off
the equatorial plane. -/
theorem meridianEq_of_dynEq_of_regPkgMin {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {A B : ℝ → ℝ} {Φ g : Work.FTS.Galerkin.Fam} {C : Work.FTS.Physical.PhysClock}
    (hEq : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (hreg : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : Work.FTS.MeridianDyn.ProfDerivData (Work.FTS.Regularity.pExp α) Φ g)
    (hA : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hmu : ∀ τ : ℝ, 0 ≤ τ →
      C.mu τ = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ) :
    Work.FTS.MeridianDyn.MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C) C.T := by
  exact Work.FTS.MeridianDyn.meridianEq_of_dynEq_of_pointwise hα hα13 hEq
    (fun Z Θ τ hZ hΘ hΘ1 hτ =>
      profFamOdd_contDiffAt_of_regPkgMin (α := Work.FTS.Regularity.pExp α) (g := g)
        (Work.FTS.Regularity.pExp_pos hα) hreg hZ hΘ hΘ1 hτ)
    hΦ hΦodd hD hA hAd hBd hB hmu

end Work.FTS.Final.MeridianMin
end
end
-- ===== merged: Submission.Work.FTS.Final.Psi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## Additivity of the elliptic law -/

/-- The open quadrant is a neighbourhood of each of its points. -/
theorem qd_mem_nhds {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) :=
  (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ, hθ2⟩

/-- The pointwise additivity of `bslOp` on the open quadrant, from `C²`-regularity there. -/
theorem bslOp_add_of_contDiffOn {α : ℝ} {Ψ Φ : Fn}
    (hsΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd)
    (hsΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.Construction.Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ + Work.Elliptic.bslOp α Φ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  exact Work.Elliptic.bslOp_add α Ψ Φ z θ hcos
    (hsΨ.contDiffAt (qd_mem_nhds hz hθ hθ2)) (hsΦ.contDiffAt (qd_mem_nhds hz hθ hθ2))


/-! ## The additivity along the canonical stream function -/



end Work.FTS.Final
end
end
-- ===== merged: Submission.Work.FTS.Final.Recon.diffAt2_merProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set

namespace Work.FTS.Final.Recon

/-! ## The two ingredients of the profile `F = F_* + g` -/

/-- The singular profile `F_*(z,θ) = α·(Γ(θ)/c(α))·(2z/(1+z)²)` is `C²` at every point with
`z > 0` and `0 < θ < π/2`: the angular factor `Γ(θ) = (sinθ·cos²θ)^{α/3}` is a real power of a
strictly positive `C²` function there (`Real.contDiffAt_rpow_const`), and
`z ↦ 2z/(1+z)²` is `C²` at `z > 0` (its pole sits at `z = -1`). -/
lemma contDiffAt_Fstar₂ (p : ℝ) {Z Θ : ℝ} (hZ : 0 < Z) (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (Z, Θ) := by
  have hbase : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sin q.2 * Real.cos q.2 ^ 2) (Z, Θ) := by
    fun_prop
  have hne : Real.sin Θ * Real.cos Θ ^ 2 ≠ 0 := by
    have h1 : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi hΘ (by linarith [hΘ1, Real.pi_pos])
    have h2 : 0 < Real.cos Θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hΘ, Real.pi_pos], hΘ1⟩
    positivity
  have hG' := (Real.contDiffAt_rpow_const (x := Real.sin Θ * Real.cos Θ ^ 2) (p := p / 3)
    (n := 2) (Or.inl hne)).comp (Z, Θ) hbase
  have hG : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (Z, Θ) := by
    simpa [Work.Spaces.Gam, Function.comp_def] using hG'
  have hz : ContDiffAt ℝ 2 (fun z : ℝ => Work.FM.Fstar z) Z := by
    change ContDiffAt ℝ 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) Z
    fun_prop (disch := positivity)
  have hproj : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1) (Z, Θ) := by fun_prop
  have hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (Z, Θ) := by
    have := hz.comp (Z, Θ) hproj
    simpa [Function.comp_def] using this
  exact ((contDiffAt_const (c := p)).mul (hG.div_const (Work.Spaces.c p))).mul hF

/-- **Regularity of the odd extension of the profile in the angle, away from `θ = 0`.**

If the random part `gs` is `C²` at `(Z,|Θ|)`, then the odd extension
`profile p gs = if 0 ≤ θ then F_* + gs else -(F_*(·,-θ) + gs(·,-θ))` is `C²` at `(Z,Θ)` for every
`Z > 0` and `0 < |Θ| < π/2`.

At such a point the sign of the angle is locally constant, so the pointwise `if` reduces to one of
its two branches, and each branch is `C²` by `contDiffAt_Fstar₂` (evaluated at the angle `|Θ|`) and
the hypothesis on `gs`, composed with the smooth reflection `(Z,Θ) ↦ (Z,-Θ)` in the negative
case. -/
lemma contDiffAt_profile_of_ne {p : ℝ} {gs : ℝ → ℝ → ℝ} {Z Θ : ℝ}
    (hZ : 0 < Z) (hΘ : Θ ≠ 0) (hΘlo : -(Real.pi / 2) < Θ) (hΘhi : Θ < Real.pi / 2)
    (hgs : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => gs q.1 q.2) (Z, |Θ|)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.ConstructionInstance.profile p gs q.1 q.2) (Z, Θ) := by
  have hflip : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1, -q.2)) (Z, Θ) := by fun_prop
  rcases lt_trichotomy Θ 0 with hneg | hzero | hpos
  · -- the branch `θ < 0`: the profile is `-(F_*(·,-θ) + gs(·,-θ))`
    rw [abs_of_neg hneg] at hgs
    have hg : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => gs q.1 (-q.2)) (Z, Θ) := by
      have := hgs.comp (Z, Θ) hflip
      simpa [Function.comp_def] using this
    have hF' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 (-q.2)) (Z, Θ) := by
      have h := (contDiffAt_Fstar₂ p hZ (by linarith) (by linarith)).comp (Z, Θ) hflip
      simpa [Function.comp_def] using h
    refine (hF'.add hg).neg.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | q.2 < 0} ∈ nhds (Z, Θ) :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hneg
    filter_upwards [hnb] with q hq
    rw [Work.ConstructionInstance.profile_of_neg (not_le.mpr hq)]
  · exact absurd hzero hΘ
  · -- the branch `θ > 0`: the profile is `F_*(·,θ) + gs(·,θ)`
    rw [abs_of_pos hpos] at hgs
    have hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (Z, Θ) :=
      contDiffAt_Fstar₂ p hZ hpos hΘhi
    refine (hF.add hgs).congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < q.2} ∈ nhds (Z, Θ) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hpos
    filter_upwards [hnb] with q hq
    rw [Work.ConstructionInstance.profile_of_nonneg (le_of_lt hq)]

/-! ## The target -/

/-- **The meridian profile of the reconstruction is differentiable in the meridian variables.**

`merProfile α A B g C r z t = A(τ)⁻¹ · profile (3α) (g(·,·,τ)) (ρ(r,z)^{3α}/B(τ)) (θ(r,z))` with
`τ = clockInv C t`; off the axis (`r > 0`) and off the equatorial plane (`z ≠ 0`, so that
`θ(r,z) ≠ 0`) this is a composition of the smooth polar dictionary `(r,z) ↦ (ρ^{3α}/B, θ)` with
the profile, which is `C²` at the interior point of the appropriate branch
(`contDiffAt_profile_of_ne`), the `C²`-input on the slice `g(·,·,τ)` on the open quadrant coming
from the hypothesis `hreg`, and the positivity of `B τ` from `hB`. -/
theorem diffAt2_merProfile {α : ℝ} {A B : ℝ → ℝ} {g : Work.FTS.Galerkin.Fam}
    {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) C.T) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.DiffAt2
      (fun r z => Work.FTS.Physical.merProfile α A B g C r z t) r z := by
  change DifferentiableAt ℝ (fun q : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹ *
      Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP q.1 q.2)) (r, z)
  set τ := Work.FTS.Physical.clockInv C t with hτdef
  have hτnn : 0 ≤ τ := by
    rw [hτdef]
    exact Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hBτ : 0 < B τ := hB τ hτnn
  have hgs : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Regularity.gSlice g τ))
      Work.FTS.EllipticEst.Q0 := hreg τ hτnn
  -- ### Step 1: the polar dictionary `(r,z) ↦ (ρ^{3α}/B, θ)` is `C²` at `(r,z)`
  have hρ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 2) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  have hρp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ) (r, z) := by
    have h4 := hρ.rpow_const_of_ne (p := Work.FTS.Regularity.pExp α) (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := (B τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (B τ)⁻¹) (r, z))
  have hθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3
  -- ### Step 2: the self-similar argument is positive and `θ(r,z) ≠ 0`
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hBτ
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  have hθlo : -(Real.pi / 2) < Work.Cyl.thetaP r z := by
    simpa only [Work.Cyl.thetaP] using Real.neg_pi_div_two_lt_arctan (z / r)
  have hθhi : Work.Cyl.thetaP r z < Real.pi / 2 := by
    simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
  have habs_lt : |Work.Cyl.thetaP r z| < Real.pi / 2 := abs_lt.mpr ⟨hθlo, hθhi⟩
  have habs_pos : 0 < |Work.Cyl.thetaP r z| := abs_pos.mpr hθ0
  -- ### Step 3: the profile is `C²` at the interior point of the relevant branch
  have hmem : (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ,
      |Work.Cyl.thetaP r z|) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hw, habs_pos, habs_lt⟩
  have hgsabs : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.Regularity.gSlice g τ q.1 q.2)
      (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, |Work.Cyl.thetaP r z|) :=
    (hgs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le (by norm_num)
  have hprof : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) q.1 q.2)
      (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, Work.Cyl.thetaP r z) :=
    contDiffAt_profile_of_ne hw hθ0 hθlo hθhi hgsabs
  -- ### Step 4: compose with the polar dictionary and multiply by the amplitude
  have hcomp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ)
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
        (Work.Cyl.thetaP q.1 q.2)) (r, z) := by
    have := hprof.comp (r, z) (hρp.prodMk hθ)
    simpa [Function.comp_def] using this
  have hmain : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (A τ)⁻¹ * Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ)
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
        (Work.Cyl.thetaP q.1 q.2)) (r, z) :=
    (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul hcomp
  exact hmain.differentiableAt (by norm_num)

end Work.FTS.Final.Recon
end
-- ===== merged: Submission.Work.FTS.Final.Small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The ℋ⁴ → sup embedding (the canonical "`N4Norm'` sup bound") -/


/-! ## The main lemma -/



end Work.FTS.Final
end
end
