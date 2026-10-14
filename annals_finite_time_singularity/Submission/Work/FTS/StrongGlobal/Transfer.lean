import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.Fstar_DzIter_le_sharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option maxHeartbeats 1600000

local notation "Fstar" => Work.Elliptic.Fstar
local notation "sg" => Work.Elliptic.sinCos2
local notation "DzIt" => Work.Spaces.DzIter

/-! ## 1. Slice integrability at the sharp level

The only place where the honesty level of `A := z²∂_z²Ψ` in the *odd* direction is consumed:
`D_z^q A·σ` is integrable as soon as `q ≤ k+2`. -/

/-- The `σ`-slice of `D_z^q A` is integrable, for `q ≤ k+2` (sharp honesty of `A`). -/
theorem Aslice_integrable_sharp {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    {q : ℕ} (hq : q ≤ k + 2) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => DzIt q (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ
      * sg θ) Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.H2W.abs_moment_le_energy
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (hSA.DzIter q).continuousOn hu)
    (Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hSA hA q hq hu)).1

/-- The `σ`-slice of `D_z^{k+2} Ψ` is integrable: split `D_z^{k+2}Ψ = D_z^{k+1}Ψ + D_z^k A`. -/
theorem Psislice_k2_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt (k + 2) Ψ u θ * sg θ) Work.Spaces.Iθ := by
  intro u hu
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpt : (fun θ => DzIt (k + 2) Ψ u θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 1) Ψ u θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ k hu hθ
    rw [hid]
    ring
  have hsum : IntegrableOn (fun θ => (DzIt (k + 1) Ψ u θ
      + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ)
      Work.Spaces.Iθ := by
    refine ((Psislice_k1 hk h u hu).add
      (Aslice_integrable_sharp (q := k) hSA hA (by omega) hu)).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply]
    ring
  exact hsum.congr hpt.symm


/-! ## 2. The top moments, at the sharp honesty level

`B_{k-1} = 0` is the sibling's `Bmom_low_zero` (it needs no honesty of `A`).  The two tower
steps and the two top moments are re-run with the level argument `k+2`. -/

/-- **`B_k = 0`**, at the sharp level: the tower at level `k-1` needs `A`-honesty only up to
level `k ≤ k+2`. -/
theorem Bmom_k_zero_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z = 0 := by
  have hlow : ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k - 1) z = 0 :=
    Bmom_low_zero (F := F) hk h
  have hcont : ContinuousOn (fun r : ℝ => Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k r / r) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 2) hSA hA k (by omega)).div
      continuousOn_id (fun r hr => (show (0 : ℝ) < r from hr).ne')
  intro z hz
  have hV : Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z / z = 0 := by
    refine Work.FTS.EllipticEst.H2W.eq_zero_of_interval_integral_eq_zero
      (V := fun r : ℝ => Work.FTS.EllipticEst.Bmom
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k r / r) hz (fun s w hs hsw => ?_) hcont
    have hchain := Work.FTS.EllipticEst.Cert.radIter_bmom_chain
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 2) hSA hA (k - 1)
      (by omega) hs hsw
    rw [show k - 1 + 1 = k from by omega] at hchain
    rw [← hchain, hlow w (lt_of_lt_of_le hs hsw), hlow s hs, sub_self]
  rcases (div_eq_zero_iff.mp hV) with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt hz)

/-- **`B_{k+1} = 0`**, at the sharp level: the tower at level `k` needs `A`-honesty only up to
level `k+1 ≤ k+2`. -/
theorem Bmom_k1_zero_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) z = 0 := by
  have hprev : ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.Bmom (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k z = 0 :=
    Bmom_k_zero_sharp (F := F) hk h hSA hA
  have hcont : ContinuousOn (fun r : ℝ => Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) r / r) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 2) hSA hA (k + 1)
      (by omega)).div
      continuousOn_id (fun r hr => (show (0 : ℝ) < r from hr).ne')
  intro z hz
  have hV : Work.FTS.EllipticEst.Bmom
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) z / z = 0 := by
    refine Work.FTS.EllipticEst.H2W.eq_zero_of_interval_integral_eq_zero
      (V := fun r : ℝ => Work.FTS.EllipticEst.Bmom
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (k + 1) r / r) hz
      (fun s w hs hsw => ?_) hcont
    have hchain := Work.FTS.EllipticEst.Cert.radIter_bmom_chain
      (F := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) α (k + 2) hSA hA k
      (by omega) hs hsw
    rw [← hchain, hprev w (lt_of_lt_of_le hs hsw), hprev s hs, sub_self]
  rcases (div_eq_zero_iff.mp hV) with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt hz)

/-- **`M_{k+2} = 0`**: `D_z^{k+2}Ψ = D_z^{k+1}Ψ + D_z^k A` a.e., and the two integrals vanish. -/
theorem Mom_k2_zero_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z → Fstar (DzIt (k + 2) Ψ) z = 0 := by
  intro z hz
  have hpt : (fun θ => DzIt (k + 2) Ψ z θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 1) Ψ z θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ k hz hθ
    rw [hid]
    ring
  rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae hpt]
  have hsplit : (fun θ => (DzIt (k + 1) Ψ z θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = fun θ => DzIt (k + 1) Ψ z θ * sg θ
        + DzIt k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := by
    funext θ
    ring
  rw [hsplit, MeasureTheory.integral_add (Psislice_k1 hk h z hz)
    (Aslice_integrable_sharp (q := k) hSA hA (by omega) hz)]
  have h1 : (∫ a in Work.Spaces.Iθ, DzIt (k + 1) Ψ z a * sg a) = 0 :=
    lowMom_zero hk h (k + 1) (by omega) z hz
  have h2 : (∫ a in Work.Spaces.Iθ, DzIt k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z a * sg a) = 0 :=
    Bmom_k_zero_sharp (F := F) hk h hSA hA z hz
  rw [h1, h2, add_zero]

/-- **`M_{k+3} = 0`**: `D_z^{k+3}Ψ = D_z^{k+2}Ψ + D_z^{k+1} A` a.e. -/
theorem Mom_k3_zero_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ z : ℝ, 0 < z → Fstar (DzIt (k + 3) Ψ) z = 0 := by
  intro z hz
  have hpt : (fun θ => DzIt (k + 3) Ψ z θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 2) Ψ z θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ (k + 1) hz hθ
    rw [show k + 1 + 2 = k + 3 from by omega,
      show k + 1 + 1 = k + 2 from by omega] at hid
    rw [hid]
    ring
  rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae hpt]
  have hsplit : (fun θ => (DzIt (k + 2) Ψ z θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = fun θ => DzIt (k + 2) Ψ z θ * sg θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := by
    funext θ
    ring
  rw [hsplit, MeasureTheory.integral_add (Psislice_k2_sharp hk h hSA hA z hz)
    (Aslice_integrable_sharp (q := k + 1) hSA hA (by omega) hz)]
  have h1 : (∫ a in Work.Spaces.Iθ, DzIt (k + 2) Ψ z a * sg a) = 0 :=
    Mom_k2_zero_sharp (F := F) hk h hSA hA z hz
  have h2 : (∫ a in Work.Spaces.Iθ, DzIt (k + 1)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z a * sg a) = 0 :=
    Bmom_k1_zero_sharp (F := F) hk h hSA hA z hz
  rw [h1, h2, add_zero]

/-! ## 3. The target -/

theorem Fstar_DzIter_le_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hA : Work.Spaces.HkMem α (k + 2)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨ
  intro i hi z hz
  by_cases hlow : i ≤ k + 1
  · exact lowMom_zero hk h i hlow z hz
  · have hcases : i = k + 2 ∨ i = k + 3 := by omega
    rcases hcases with rfl | rfl
    · exact Mom_k2_zero_sharp hk h hSA hA z hz
    · exact Mom_k3_zero_sharp hk h hSA hA z hz

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.Regularity.gCompHolderQuant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology

namespace Work.FTS.Regularity

theorem gCompHolderQuant {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hKquad : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ K * z ^ 2)
    (hKz : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ K * max z z' * |z - z'|)
    (hKth : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ K * z * |θ - θ'|) :
    HolderWith (Work.FTS.Regularity.gCompConstNN α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 =>
        g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
  have h3α : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  have hvan' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ := hvan
  have hK0 : 0 ≤ K := hK
  have hslice : (∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |g z θ - g z θ'| ≤ K * z * |θ - θ'|) := ⟨hKz, hKth⟩
  obtain ⟨hslicez, hsliceθ⟩ := hslice
  -- the two global bounds of the composite
  have hsup : ∀ z : R3, |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ Cv := by
    intro z
    have hθ := Work.ConstructionInstance.psi_mem_Iθ z
    have h1 := hvan' (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)
      (Real.rpow_nonneg (Work.Cyl.rho_nonneg z) _) hθ
    have h2 : Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ
    have h3 : 0 ≤ Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) := Work.ConstructionInstance.Gamma_nonneg hθ
    nlinarith [hCv]
  have hquadbound : ∀ z : R3, Work.Cyl.rho z ≤ 2 →
      |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ K * (Work.Cyl.rho z) ^ (6 * α) := by
    intro z hz
    have hρ0 := Work.Cyl.rho_nonneg z
    have hZ0 : 0 ≤ Work.Cyl.rho z ^ (3 * α) := Real.rpow_nonneg hρ0 _
    have hZ2 : Work.Cyl.rho z ^ (3 * α) ≤ 2 := by
      calc Work.Cyl.rho z ^ (3 * α) ≤ 2 ^ (3 * α) := Real.rpow_le_rpow hρ0 hz h3α.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
        _ = 2 := Real.rpow_one 2
    have h1 := hKquad _ _ hZ0 hZ2 (Work.ConstructionInstance.psi_mem_Iθ z)
    have h2 : (Work.Cyl.rho z ^ (3 * α)) ^ 2 = (Work.Cyl.rho z) ^ (6 * α) := by
      rw [← Real.rpow_natCast (Work.Cyl.rho z ^ (3 * α)) 2, ← Real.rpow_mul hρ0]
      congr 1
      ring
    calc |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)|
        ≤ K * (Work.Cyl.rho z ^ (3 * α)) ^ 2 := h1
      _ = K * (Work.Cyl.rho z) ^ (6 * α) := by rw [h2]
  -- the Hölder constant
  set C : ℝ := 2 * Cv + (2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1))))) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 2 * Cv ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC2 : 2 * Cv * (3/2) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC3 : 2 * K * 3 ^ (6 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * Cv * (3/2) ^ α + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC4 : Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC5 : K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC6 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)))) by positivity]
  have hC56 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α))) by positivity]
  have hCco : C = gCompConst α Cv Lg Lθ K := by
    simp only [gCompConst]
    rw [hCdef]
  have hCg : 0 ≤ gCompConst α Cv Lg Lθ K := hCco ▸ hCnn
  have hCnne : gCompConstNN α Cv Lg Lθ K = (⟨C, hCnn⟩ : NNReal) := by
    apply Subtype.ext
    simp only [gCompConstNN]
    rw [abs_of_nonneg hCg]
    exact hCco.symm
  rw [hCnne]
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [Real.dist_eq, Work.ConstructionInstance.g_psi_eq hquad0 hvt x, Work.ConstructionInstance.g_psi_eq hquad0 hvt y]
  show |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
      ≤ C * dist x y ^ α
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, sub_self, abs_zero]
    positivity
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hdnn : 0 ≤ dist x y := dist_nonneg
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := Work.ConstructionInstance.abs_sub_le_abs_add
  rcases le_or_gt 1 (dist x y) with hd1 | hd1
  · -- far away (or exactly at distance one): the sup bound suffices
    have h1 : (1 : ℝ) ≤ dist x y ^ α := Real.one_le_rpow hd1 hα.le
    calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
        ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
          + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
      _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
      _ ≤ C * dist x y ^ α := by
          calc 2 * Cv ≤ C := hC1
            _ = C * 1 := by ring
            _ ≤ C * dist x y ^ α := by
                simpa using mul_le_mul_of_nonneg_left h1 hCnn
  · rcases le_or_gt (min (Work.Cyl.rho x) (Work.Cyl.rho y)) (2 * dist x y) with hfar | hnear
    · -- the radii are not large compared with `d`: use the two pointwise bounds
      have hmax3 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 3 * dist x y := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      by_cases hsmall : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2
      · -- both radii at most two: the quadratic vanishing of `g` at `z = 0`
        have hρx2 : Work.Cyl.rho x ≤ 2 := le_trans (le_max_left _ _) hsmall
        have hρy2 : Work.Cyl.rho y ≤ 2 := le_trans (le_max_right _ _) hsmall
        have hρx3 : Work.Cyl.rho x ≤ 3 * dist x y := le_trans (le_max_left _ _) hmax3
        have hρy3 : Work.Cyl.rho y ≤ 3 * dist x y := le_trans (le_max_right _ _) hmax3
        have hpow : dist x y ^ (6 * α) ≤ dist x y ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos (le_of_lt hd1) (by linarith)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ K * (Work.Cyl.rho x) ^ (6 * α) + K * (Work.Cyl.rho y) ^ (6 * α) :=
              add_le_add (hquadbound x hρx2) (hquadbound y hρy2)
          _ ≤ K * (3 * dist x y) ^ (6 * α) + K * (3 * dist x y) ^ (6 * α) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx3 (by linarith)) hK0
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy3 (by linarith)) hK0
          _ = 2 * K * 3 ^ (6 * α) * dist x y ^ (6 * α) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hdnn]; ring
          _ ≤ 2 * K * 3 ^ (6 * α) * dist x y ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hdnn α)
      · -- both radii large: then `d > 2/3` and the sup bound suffices
        have hd23 : 2 / 3 ≤ dist x y := by
          have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
          linarith [not_le.mp hsmall, hfar]
        have h1 : (1 : ℝ) ≤ (3 / 2) ^ α * dist x y ^ α := by
          have h2 : (3 / 2 : ℝ) ^ α * (2 / 3) ^ α = 1 := by
            rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (0:ℝ) ≤ 2 / 3),
              show (3:ℝ)/2 * (2/3) = 1 by ring, Real.one_rpow]
          have h3 : (2 / 3 : ℝ) ^ α ≤ dist x y ^ α :=
            Real.rpow_le_rpow (by norm_num) hd23 hα.le
          have h4 : 0 ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
          calc (1 : ℝ) = (3 / 2 : ℝ) ^ α * (2 / 3) ^ α := h2.symm
            _ ≤ (3 / 2 : ℝ) ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h3 h4
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
          _ = 2 * Cv * 1 := by ring
          _ ≤ 2 * Cv * ((3 / 2) ^ α * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Cv * (3 / 2) ^ α * dist x y ^ α := by ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hdnn α)
    · -- close together and away from the origin
      have hρmin2d : 2 * dist x y < min (Work.Cyl.rho x) (Work.Cyl.rho y) := hnear
      have hρminpos : 0 < min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        lt_of_lt_of_le (by linarith [dist_nonneg (x := x) (y := y)]) (le_of_lt hρmin2d)
      have hminx : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho x := min_le_left _ _
      have hminy : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho y := min_le_right _ _
      have hρxmax : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
      have hρymax : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
      have hmax32 : max (Work.Cyl.rho x) (Work.Cyl.rho y)
          ≤ 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2 := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      have hpsi : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
          ≤ 4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        Work.ConstructionInstance.psi_sub_le x y hρminpos hminx hminy
      have hpsi_nn : 0 ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| := abs_nonneg _
      have hZx0 : 0 ≤ Work.Cyl.rho x ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _
      have hZy0 : 0 ≤ Work.Cyl.rho y ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _
      have hsplit : |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
            - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
          ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := by
        have := abs_add_le
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y))
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
        rwa [show g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
            + (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
            = g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y) from by ring] at this
      by_cases hB1 : 1 ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y)
      · -- both points at radius at least one: `hzk`/`hzth` and the Lipschitz bound for `Work.ConstructionInstance.psi`
        have hρx1 : 1 ≤ Work.Cyl.rho x := le_trans hB1 hminx
        have hρy1 : 1 ≤ Work.Cyl.rho y := le_trans hB1 hminy
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| ≤ 3 * α * dist x y := by
          calc |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ 3 * α * |Work.Cyl.rho x - Work.Cyl.rho y| :=
                Work.ConstructionInstance.abs_rpow_sub_le_mul_of_one_le h3α h3α1 hρx1 hρy1
            _ ≤ 3 * α * dist x y :=
                mul_le_mul_of_nonneg_left (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y) h3α.le
        have hdψ : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ≤ 4 * Real.pi * dist x y := by
          rw [le_div_iff₀ hρminpos] at hpsi
          have h1 : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
              ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| * min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
            le_mul_of_one_le_right (abs_nonneg _) hB1
          linarith
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ Lθ * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α + Lg * |Work.Cyl.rho x ^ (3 * α)
                - Work.Cyl.rho y ^ (3 * α)| ^ α :=
              add_le_add (hzth _ _ _ hZx0 (Work.ConstructionInstance.psi_mem_Iθ x) (Work.ConstructionInstance.psi_mem_Iθ y))
                (hzk _ _ _ hZx0 hZy0 (Work.ConstructionInstance.psi_mem_Iθ y))
          _ ≤ Lθ * (4 * Real.pi * dist x y) ^ α + Lg * (3 * α * dist x y) ^ α := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow hpsi_nn hdψ hα.le) hLθ
              · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hZd hα.le) hLg
          _ = (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α) * dist x y ^ α := by
              rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
                Real.mul_rpow (by linarith : (0:ℝ) ≤ 3 * α) hdnn]
              ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC4 (Real.rpow_nonneg hdnn α)
      · -- both points at radius below one: the slice bounds of the Taylor expansion
        have hρmin1 : min (Work.Cyl.rho x) (Work.Cyl.rho y) < 1 := lt_of_not_ge hB1
        have hmax2 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2 := by linarith
        have hρx32 : Work.Cyl.rho x ≤ 3 / 2 := by
          have := le_trans hρxmax hmax32
          linarith
        have hρy32 : Work.Cyl.rho y ≤ 3 / 2 := by
          have := le_trans hρymax hmax32
          linarith
        have hZx2 : Work.Cyl.rho x ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZy2 : Work.Cyl.rho y ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) (le_trans hρymax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZx32 : Work.Cyl.rho x ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hZy32 : Work.Cyl.rho y ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hmaxZ : max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) ≤ 3 / 2 :=
          max_le hZx32 hZy32
        have hZxle : Work.Cyl.rho x ^ (3 * α)
            ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
          Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32) h3α.le
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ 3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α :=
          Work.ConstructionInstance.A0_rho_pow_diff (β := α) hα (le_trans hα13 (by norm_num)) (Work.Cyl.rho_nonneg x)
            (Work.Cyl.rho_nonneg y) hρx32 hρy32 (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y)
        have hzslice := hslicez (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)
          hZx0 hZx2 hZy0 hZy2 (Work.ConstructionInstance.psi_mem_Iθ y)
        have hθslice := hsliceθ (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) (Work.ConstructionInstance.psi y)
          hZx0 hZx2 (Work.ConstructionInstance.psi_mem_Iθ x) (Work.ConstructionInstance.psi_mem_Iθ y)
        -- the two gradient steps
        have hstep1 : K * (Work.Cyl.rho x ^ (3 * α)) * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
            ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
          have h1 : K * (Work.Cyl.rho x ^ (3 * α))
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
            mul_le_mul_of_nonneg_left hZxle hK0
          calc K * (Work.Cyl.rho x ^ (3 * α)) * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| := mul_le_mul_of_nonneg_right h1 hpsi_nn
            _ = K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|) := by ring
            _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hpsi (by positivity)
        have hstep2 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
          have h1 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              ≤ K * (3 / 2) := mul_le_mul_of_nonneg_left hmaxZ hK0
          calc K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ K * (3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = K * ((3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|) := by ring
            _ ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hZd (by positivity)
        have hstep1' : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
            ≤ (3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α) := by
          have h1 : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              = (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α) := by
            rw [show 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2
                = 3 / 2 * min (Work.Cyl.rho x) (Work.Cyl.rho y) by ring,
              Real.mul_rpow (by norm_num) hρminpos.le]
          rw [h1]
          have h2 := Work.ConstructionInstance.rho_pow_div_mul_le hα h3α1 hdpos (le_of_lt hd1) (le_of_lt hρmin2d)
          have h3 : (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
              = (3 / 2) ^ (3 * α) * 4 * Real.pi
                * (min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                  / min (Work.Cyl.rho x) (Work.Cyl.rho y) * dist x y) := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ K * (Work.Cyl.rho x ^ (3 * α)) * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
              + K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
              add_le_add hθslice hzslice
          _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) :=
              add_le_add hstep1 hstep2
          _ ≤ K * ((3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hstep1' hK0
              · exact le_refl _
          _ = (K * (3 / 2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
                + K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)) * dist x y ^ α := by ring_nf
          _ ≤ C * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hC56 (Real.rpow_nonneg hdnn α)
end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.StrongGlobal.Transfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}




end Work.FTS.StrongGlobal
end
end
