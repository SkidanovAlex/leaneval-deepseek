import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.isPreconnected_rayAccum
import Submission.Work.LandLeaves.finite_of_closedInCircle_invariant_injective
import Submission.Work.LandLeaves.rayAccum_subset_fixp
import Submission.Work.LandLeaves.rayAccum_nonempty
import Submission.Work.LandLeaves.rayAccum_periodic
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.LandLeaves.closure_escapingSet_of_isRepelling
import Submission.Work.SeedDyn.Main
import Submission.Work.ELTop.All
import Submission.Work.LandLeaves.exists_preimage_rayAccum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A clash-free copy of `Submission/Work/LandLeaves/AnchorHelpers.lean`

The original module `Submission.Work.LandLeaves.AnchorHelpers` declares
`Work.LandLeaves.dynBNakane` and imports
`Submission.Work.LandLeaves.finite_of_ccBet_periodic_point` (which declares
`Work.LandLeaves.fract_sub_fract_of_le`); both names are declared again in
`Submission.Work.LandLeaves.ccBet_v2_defs`, so no module can import `AnchorHelpers` together with
the cyclic-order-preservation vocabulary of `ccBet_v2_defs`.

This file is a verbatim copy of the *statements and proofs* of `AnchorHelpers` under the namespace
`Work.LandLeaves.V2Anchor`, with the two offending imports dropped (neither is used here).  It can
therefore be imported together with `ccBet_v2_defs`, and is the vocabulary base of the clash-free
anchor chain (`V2Anchor/BranchCont.lean`, `V2Anchor/TailCore.lean`, `V2Anchor/Cluster.lean`,
`V2Anchor/Tail.lean`, `V2Anchor/Anchor.lean`).
-/

namespace Work.LandLeaves.V2Anchor

noncomputable section

open Classical Filter Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

/-! ## The dynamical Nakane data attached to an arbitrary Böttcher coordinate -/

theorem elDynPhi_eq {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Work.EL.dynPhi c φ = Work.ParamRays.dynPhi c := by
  have hex : Work.ParamRays.DynBottcherExists c := ⟨φ, hφ⟩
  funext z
  by_cases hz : z ∈ Work.EL.K c
  · simp [Work.EL.dynPhi, Work.ParamRays.dynPhi, hz, Work.EL.K]
  · rw [Work.EL.dynPhi_of_notMem hz, Work.ParamRays.dynPhi_of_not_mem hz]
    exact (Work.ParamRays.dynPhiOf_eq_of_isDynBottcher hex hφ (by
      rw [Work.ParamRays.escaping_iff_not_bounded]
      exact fun hb => hz hb)).symm

/-- The dynamical Nakane data at an arbitrary Böttcher coordinate. -/
noncomputable def dynBNakane {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Work.EL.DynB c φ :=
  Eq.mp (congrArg (fun ψ : ℂ → ℂ => Work.Top.NakaneData (Work.EL.K c) ψ)
      (elDynPhi_eq hφ).symm)
    (Work.SeedDyn.dynB (Work.LandLeaves.dynBottcherOnlyOnMandelbar c ⟨φ, hφ⟩))

/-- The point of the straight ray of angle `θ` at level `t`, in the coordinates of the
Böttcher image. -/
theorem rayPoint_eq (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * Work.Landing.rayDirection θ := by
  rw [Work.Top.NakaneData.rayPoint, Work.Landing.rayDirection]
  congr 1
  push_cast
  ring

/-- **The Böttcher equation for the holomorphic iterate `τ = (T_c)^{2k}`**: away from the filled
Julia set, `φ (τ w) = (φ w) ^ (4 ^ k)`. -/
theorem phi_iterate {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (k : ℕ)
    {w : ℂ} (hw : w ∉ Work.EL.K c) :
    φ ((Tantibar c)^[2 * k] w) = (φ w) ^ (4 ^ k) := by
  have hesc : Work.ParamRays.Escaping c w := by
    rw [Work.ParamRays.escaping_iff_not_bounded]
    exact fun hb => hw (by simpa [Work.EL.K, Work.ParamRays.filledJulia] using hb)
  have h := Work.ParamRays.IsDynBottcher.functional_iterate hφ hesc k
  simpa only [Work.ParamRays.orbit] using h

theorem norm_phi_iterate {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (k : ℕ)
    {w : ℂ} (hw : w ∉ Work.EL.K c) :
    ‖φ ((Tantibar c)^[2 * k] w)‖ = ‖φ w‖ ^ (4 ^ k) := by
  rw [phi_iterate hφ k hw, norm_pow]

/-! ## Elementary interface for the dynamical rays -/

/-- The angle (in turns) of the Böttcher coordinate of a point. -/
def angPt (φ : ℂ → ℂ) (w : ℂ) : ℝ := (φ w).arg / (2 * Real.pi)

theorem rayDirection_angPt (φ : ℂ → ℂ) {w : ℂ} (hw : φ w ≠ 0) :
    Work.Landing.rayDirection (angPt φ w) = φ w / (‖φ w‖ : ℂ) := by
  simpa [angPt] using Work.LandLeaves.rayDirection_arg_div (φ w) hw

/-- A point of the escaping set with a prescribed Böttcher image is the ray point at that
angle and level. -/
theorem eq_rayPt_of_phi {hN : Work.EL.DynB c φ} {w : ℂ} {θ t : ℝ}
    (hw : w ∉ Work.EL.K c) (ht : 1 < t) (h : φ w = (t : ℂ) * Work.Landing.rayDirection θ) :
    w = Work.EL.rayPt hN θ t := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htn : ‖(t : ℂ) * Work.Landing.rayDirection θ‖ = t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      Work.Landing.Rays.norm_rayDirection, mul_one]
  have hΦw : Work.EL.dynPhi c φ w = Work.Top.NakaneData.rayPoint θ t := by
    rw [Work.EL.dynPhi_of_notMem hw, h, rayPoint_eq]
  have hΦr : Work.EL.dynPhi c φ (Work.EL.rayPt hN θ t) = Work.Top.NakaneData.rayPoint θ t :=
    hN.Phi_rayPt ht
  have hmem : w ∉ Work.EL.K c ∧ Work.EL.rayPt hN θ t ∉ Work.EL.K c := ⟨hw, hN.rayPt_notMem ht⟩
  have := hN.injOn_Phi hmem.1 hmem.2 (by rw [hΦw, hΦr])
  exact this

/-- The level of a ray point: the Böttcher modulus of `rayPt hN θ t` is `t`. -/
theorem norm_phi_rayPt {hN : Work.EL.DynB c φ} {θ t : ℝ} (ht : 1 < t) :
    ‖φ (Work.EL.rayPt hN θ t)‖ = t := by
  rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) (hN.rayPt_notMem ht), hN.Phi_rayPt ht,
    Work.Top.NakaneData.norm_rayPoint, abs_of_pos (lt_trans zero_lt_one ht)]

/-- `rayPt` is the unique point of a ray at a given level. -/
theorem eq_rayPt_of_level {hN : Work.EL.DynB c φ} {w : ℂ} {θ t : ℝ}
    (hw : w ∉ Work.EL.K c) (ht : 1 < t) (hwray : w ∈ Work.EL.paramRay hN θ)
    (hlev : ‖φ w‖ = t) : w = Work.EL.rayPt hN θ t := by
  obtain ⟨hwK, s, hs, hsw⟩ := hwray
  have hsw' : φ w = (s : ℂ) * Work.Landing.rayDirection θ := by
    rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hwK, hsw, rayPoint_eq]
  have h1 : (s : ℝ) = t := by
    have h2 : ‖(s : ℂ) * Work.Landing.rayDirection θ‖ = t := by rw [← hsw']; exact hlev
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hs),
      Work.Landing.Rays.norm_rayDirection, mul_one] at h2
  refine eq_rayPt_of_phi hw ht ?_
  rw [hsw', h1]



/-! ## The level sequence -/

/-- The decreasing level sequence `r₀ ^ (1/D)^n`, converging to `1`. -/
noncomputable def lvlSeq (r₀ : ℝ) (D : ℕ) (n : ℕ) : ℝ := r₀ ^ (((D : ℝ)⁻¹) ^ n)

theorem lvlSeq_zero (r₀ : ℝ) (D : ℕ) : lvlSeq r₀ D 0 = r₀ := by simp [lvlSeq]

theorem lvlSeq_one_lt {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D) (n : ℕ) :
    1 < lvlSeq r₀ D n := by
  rw [lvlSeq]
  refine Real.one_lt_rpow hr₀ ?_
  exact pow_pos (inv_pos.mpr (by positivity)) n

theorem lvlSeq_pos {r₀ : ℝ} (hr₀ : 0 < r₀) (D : ℕ) (n : ℕ) : 0 < lvlSeq r₀ D n := by
  rw [lvlSeq]; exact Real.rpow_pos_of_pos hr₀ _

theorem lvlSeq_mono {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D) {n m : ℕ} (h : n ≤ m) :
    lvlSeq r₀ D m ≤ lvlSeq r₀ D n := by
  have h1 : (0:ℝ) < (D:ℝ) := by positivity
  have h2 : ((D:ℝ)⁻¹) ≤ 1 := by
    rw [inv_le_one₀ h1]; exact_mod_cast (by omega : 1 ≤ D)
  rw [lvlSeq, lvlSeq]
  refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hr₀) ?_
  exact pow_le_pow_of_le_one (by positivity) h2 h

theorem lvlSeq_succ {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (D : ℕ) (n : ℕ) :
    lvlSeq r₀ D (n + 1) = (lvlSeq r₀ D n) ^ ((D : ℝ)⁻¹) := by
  rw [lvlSeq, lvlSeq, pow_succ]
  exact Real.rpow_mul hr₀ _ _

theorem lvlSeq_pow {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {D : ℕ} (hD : D ≠ 0) (n : ℕ) :
    (lvlSeq r₀ D (n + 1)) ^ D = lvlSeq r₀ D n := by
  have hD0 : ((D : ℝ)) ≠ 0 := by positivity
  rw [lvlSeq, lvlSeq, ← Real.rpow_natCast, ← Real.rpow_mul hr₀]
  congr 1
  rw [pow_succ]
  field_simp

theorem tendsto_lvlSeq {r₀ : ℝ} (hr₀ : 0 < r₀) {D : ℕ} (hD : 2 ≤ D) :
    Filter.Tendsto (fun n => lvlSeq r₀ D n) Filter.atTop (𝓝 1) := by
  have hlt : ((D : ℝ)⁻¹) < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    exact_mod_cast (by omega : 1 < D)
  have hpow : Filter.Tendsto (fun n : ℕ => ((D : ℝ)⁻¹) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt
  have h2 : Filter.Tendsto (fun n : ℕ => r₀ ^ (((D : ℝ)⁻¹) ^ n)) Filter.atTop
      (𝓝 (r₀ ^ (0:ℝ))) :=
    (Real.continuousAt_const_rpow (a := r₀) (b := (0:ℝ)) (ne_of_gt hr₀)).tendsto.comp hpow
  simpa [lvlSeq] using h2

/-! ## Auxiliary lemmas for the construction -/

theorem lvlSeq_pow_pow {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {D : ℕ} (hD : D ≠ 0) (n j : ℕ) :
    (lvlSeq r₀ D (n + j)) ^ (D ^ j) = lvlSeq r₀ D n := by
  induction j with
  | zero => simp [lvlSeq]
  | succ j ih =>
      have hD0 : D ^ j ≠ 0 := pow_ne_zero j hD
      rw [show n + (j + 1) = (n + j) + 1 from by omega, pow_succ, mul_comm, pow_mul,
        lvlSeq_pow hr₀ hD, ih]

theorem lvlSeq_mem_Icc {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D) (j : ℕ) :
    lvlSeq r₀ D (j + 1) ≤ lvlSeq r₀ D j :=
  lvlSeq_mono hr₀ hD (Nat.le_succ j)

theorem lvlSeq_le_r₀ {r₀ : ℝ} (hr₀ : 1 < r₀) {D : ℕ} (hD : 2 ≤ D) (j : ℕ) :
    lvlSeq r₀ D j ≤ r₀ := by
  rw [lvlSeq]
  have h1 : ((D : ℝ)⁻¹) ^ j ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [inv_le_one₀ (by positivity)]; exact_mod_cast (by omega : 1 ≤ D)
  simpa using Real.rpow_le_rpow_of_exponent_le (le_of_lt hr₀) h1

theorem K_iterate_mem {c : ℂ} {z : ℂ} (hz : z ∈ Work.EL.K c) (m : ℕ) :
    (Tantibar c)^[m] z ∈ Work.EL.K c := by
  have hz' : Work.ParamRays.BoundedOrbit c z := by
    rw [Work.EL.K, Work.ParamRays.filledJulia] at hz; exact hz
  obtain ⟨M, hM⟩ := hz'
  change Work.ParamRays.BoundedOrbit c ((Tantibar c)^[m] z)
  refine ⟨M, fun n => ?_⟩
  have h1 : Work.ParamRays.orbit c ((Tantibar c)^[m] z) n = Work.ParamRays.orbit c z (n + m) := by
    simp only [Work.ParamRays.orbit, Function.iterate_add_apply]
  rw [h1]; exact hM (n + m)

theorem notMem_K_of_iterate {c : ℂ} {w : ℂ} {m : ℕ}
    (h : (Tantibar c)^[m] w ∉ Work.EL.K c) : w ∉ Work.EL.K c :=
  fun hw => h (K_iterate_mem hw m)

/-- A repelling periodic point lies in the filled Julia set. -/
theorem mem_K_of_isRepelling {c : ℂ} {k : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) : y ∈ Work.EL.K c := by
  obtain ⟨hkpos, hfix⟩ := hrep.1
  change Work.ParamRays.BoundedOrbit c y
  refine ⟨∑ i ∈ Finset.range k, ‖Work.ParamRays.orbit c y i‖, fun n => ?_⟩
  have hstep : ((Tantibar c)^[k])^[n / k] y = y :=
    (show Function.IsFixedPt ((Tantibar c)^[k]) y from hfix).iterate _
  have hmain : (Tantibar c)^[n] y = (Tantibar c)^[n % k] y := by
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [show k * (n / k) + n % k = n % k + k * (n / k) from by ring,
      Function.iterate_add_apply, Function.iterate_mul, hstep]
  have hlt : n % k < k := Nat.mod_lt n hkpos
  calc ‖Work.ParamRays.orbit c y n‖ = ‖Work.ParamRays.orbit c y (n % k)‖ := by
        simp only [Work.ParamRays.orbit]; rw [hmain]
    _ ≤ ∑ i ∈ Finset.range k, ‖Work.ParamRays.orbit c y i‖ :=
        Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hlt)

theorem norm_phi_g {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) {k : ℕ}
    {y : ℂ} {g : ℂ → ℂ} {r' : ℝ}
    (hright : ∀ w : ℂ, ‖w - y‖ ≤ r' → (Tantibar c)^[2 * k] (g w) = w)
    {w : ℂ} (hw : ‖w - y‖ ≤ r') (hg : g w ∉ Work.EL.K c) :
    ‖φ (g w)‖ ^ (4 ^ k) = ‖φ w‖ := by
  rw [← norm_phi_iterate hφ k hg, hright w hw]

theorem rayPt_fract {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ t : ℝ) :
    Work.EL.rayPt hN (Int.fract θ) t = Work.EL.rayPt hN θ t := by
  have h : θ = Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) := by
    have := Int.self_sub_fract θ; linarith
  conv_rhs => rw [h]
  exact (Work.ELTop.rayPt_add_int hN (Int.fract θ) t ⌊θ⌋).symm

end

end Work.LandLeaves.V2Anchor

