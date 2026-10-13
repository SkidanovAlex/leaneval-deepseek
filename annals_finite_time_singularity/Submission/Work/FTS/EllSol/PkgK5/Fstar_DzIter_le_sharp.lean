/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular moments of the radially differentiated solution vanish -- at the *sharp*
(`k+2`) honesty level

The target is

`F_*(D_z^i Ψ)(z) = 0`  for all `i ≤ k+3` and all `z > 0`,

for a datum `(F, Ψ)` of the weak class `TT.EllWeakPos α k` with `k ≥ 2`, together with the
*sharp* honesty `HkMem α (k+2) (z²∂_z²Ψ)` of the second radial derivative (one level less than
the sibling `PkgK5.Fstar_DzIter_le_honest`, which assumes `HkMem α (k+3)`).

## Shape of the argument (identical to the honest sibling, with the level bookkeeping fixed)

Write `M_i(z) := F_*(D_z^i Ψ)(z)` and `A := z²∂_z²Ψ`.

* the levels `i ≤ k+1` need *no* honesty of `A` at all: they are the level-`2` theorem
  `H2W.Fstar_DzIter_le_Psi` applied to the radially shifted data `(D_z^j F, D_z^j Ψ)`
  (`EllWeakPos_DzIter_shift_le`, iterating the proved
  `Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le`);
* the slices `D_z^q Ψ·σ` for `q ≤ k+1` likewise only need the class at level `k`
  (`Psislice_k`, `Psislice_k1`), and the slices `D_z^q A·σ` need the source honesty only up to
  `q ≤ k+2` (`Aslice_integrable_sharp`);
* the moment tower `B_j(z) - B_j(s) = ∫_s^z B_{j+1}(r)/r dr` for `B_j := Bmom A j` consumes the
  honesty of `A` only up to level `j+1`: the top level used is `k+1` (in `Bmom_k1_zero_sharp`,
  where `B_{k+1} = 0` follows from the tower at level `k`).  Hence `HkMem α (k+2) A` is enough
  — and that is exactly what the sharp hypothesis supplies.

The only textual difference with respect to `Fstar_DzIter_le_honest` is that every use of the
`A`-honesty is instantiated at level `k+2` instead of `k+3`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.Fstar_DzIter_le_honest
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.mixed_comm

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

/-- The `σ`-slice of `D_z^{k+3} Ψ` is integrable: split `D_z^{k+3}Ψ = D_z^{k+2}Ψ + D_z^{k+1}A`. -/
theorem Psislice_k3_sharp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hSA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hA : Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ u : ℝ, 0 < u → IntegrableOn (fun θ => DzIt (k + 3) Ψ u θ * sg θ) Work.Spaces.Iθ := by
  intro u hu
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpt : (fun θ => DzIt (k + 3) Ψ u θ * sg θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (DzIt (k + 2) Ψ u θ
        + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.H2W.ae_Ioo_mem,
      self_mem_ae_restrict measurableSet_Icc] with θ hθ _
    have hid := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨ (k + 1) hu hθ
    rw [show k + 1 + 2 = k + 3 from by omega,
      show k + 1 + 1 = k + 2 from by omega] at hid
    rw [hid]
    ring
  have hsum : IntegrableOn (fun θ => (DzIt (k + 2) Ψ u θ
      + DzIt (k + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) * sg θ)
      Work.Spaces.Iθ := by
    refine ((Psislice_k2_sharp hk h hSA hA u hu).add
      (Aslice_integrable_sharp (q := k + 1) hSA hA (by omega) hu)).congr ?_
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
