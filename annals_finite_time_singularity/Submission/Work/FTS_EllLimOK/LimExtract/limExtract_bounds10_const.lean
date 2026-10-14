import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EpsEngine.HkMem_intervalIntegral_counterexample =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-! ## The profile `θ ↦ 1/sin(2θ)` and the constant family -/






/-! ## The `HkIntegrand` of a single slice -/





/-! ## Non-integrability of the angular slices -/


/-! ## The junk values: `HkSq`, `HkNorm`, and the failure of `HkMem` -/





/-! ## The hypotheses of the requested lemma hold for the constant family -/







/-! ## The conclusion fails -/





end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Sup

open scoped Real Topology
open Set Filter

/-! ## Finite-order commutation of `D_θ`- and `D_z`-iterates

`D_θ f = sin(2θ) ∂_θ f` and `D_z f = z ∂_z f` commute at every point where the profile is
`C²` (`Work.Spaces.Dz_Dth_comm`): the coefficient of `D_θ` depends only on `θ` and that of
`D_z` only on `z`, so the identity is Clairaut's theorem.  On an open set on which the
profile is *genuinely* smooth, iterating gives `D_θ^i (D_z^b f) = D_z^b (D_θ^i f)`
(`Work.Blocks.Half.DthIter_DzIter_comm_eqOn`, `Work.Spaces.DthIter_DzIter_comm_eqOn`, …).

Here we record the **finite-order** version: it suffices that the profile is `C^n` on the
open set `V`, with `i + b ≤ n`.  Each of the two operators costs exactly one order of
differentiability (`contDiffOn_Dth_fin`, `contDiffOn_Dz_fin`), so after moving `i` angular
derivatives across `b` radial ones every Clairaut step still has two orders to spare. -/

/-- `D_θ` is local: two functions that agree on an open set have the same `D_θ` at every
point of that set.  (Only the `θ`-slice near the point matters.) -/
theorem Dth_congr_of_isOpen_fin {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro y hy
  show Real.sin (2 * y.2) * Work.Spaces.pth g y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth g' y.1 y.2
  rw [Work.Spaces.pth_congr_of_isOpen hV h hy]

/-- **A single `D_θ` crosses any number of `D_z`-iterates**, for a profile of class `C^{b+1}`
(or better) on the open set `V`. -/
theorem Dth_DzIter_comm_fin_aux {Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (m : ℕ) (hY : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (Function.uncurry Y) V) :
    ∀ b : ℕ, b + 1 ≤ m →
      Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b Y)))
        (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth Y))) V := by
  intro b
  induction b with
  | zero => intro _ y hy; rfl
  | succ b ih =>
      intro hb y hy
      -- `D_z^b Y` has `m - b ≥ 2` orders, so Clairaut applies at `y`.
      have hDb : ContDiffOn ℝ (((m - b : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter b Y)) V :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin hV hY b (by omega)
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b Y)) (y.1, y.2) :=
        (hDb.contDiffAt (hV.mem_nhds hy)).of_le (by
          have h2 : (2 : ℕ) ≤ m - b := by omega
          exact_mod_cast h2)
      -- Clairaut at `y`, then the induction hypothesis transported through `D_z`.
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b Y)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b Y) hcd
      have hpz : Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV (ih (by omega)) hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b Y)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b Y)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth Y)) y.1 y.2
      rw [hpz]

/-- **Finite-order commutation of the curvilinear derivatives on an open set.**  If the
uncurried profile `X` is `C^n` on the open set `V` and `i + b ≤ n`, then
`D_θ^i (D_z^b X) = D_z^b (D_θ^i X)` on `V`. -/
theorem DthIter_DzIter_comm_fin {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ n (Function.uncurry X) V) (i b : ℕ) (hib : i + b ≤ n) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i X))) V := by
  induction i generalizing b with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hib' : i + b ≤ n := by omega
      -- `D_θ^i X` is `C^{n-i}` on `V`, with `n - i ≥ b + 1`.
      have hDi : ContDiffOn ℝ (((n - i : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DthIter i X)) V :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin hV h i (by omega)
      -- transport the induction hypothesis through the outer `D_θ` …
      have hcongr : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) y.1 y.2 :=
        Dth_congr_of_isOpen_fin hV (ih b hib') hy
      -- … and cross the `b` radial derivatives.
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) y.1 y.2 :=
        (Dth_DzIter_comm_fin_aux (Y := Work.Spaces.DthIter i X) hV (n - i) hDi b (by omega)) hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) y.1 y.2
      rw [hcongr, hstep]

end Work.FTS.RegPkgGal.Sup
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G5

/-- **Exchange of `mixed j i` (`j + i ≤ n`) with the interval integral.**

This is the order-unrestricted version of `Work.FTS.StrongEps.mixed_intervalIntegral_eq` (which
is the case `n = 4`): for a family `s ↦ H s` of functions smooth on the open quadrant `Q0`,
uniformly bounded in every slot of order `≤ n` on a closed box `⊆ Q0`, and with every slot
a.e.-strongly-measurable in `s`, the iterated derivatives `D_z^j D_θ^i` (for `j + i ≤ n`) of the
interval integral `∫_a^b H s z θ ds` are the interval integrals of the iterated derivatives.

The two inductions behind it (`DthIter_intervalIntegral_eq_gen` in the angular direction and
`DzIter_intervalIntegral_eq_gen` in the radial one) are the order-`n` versions of the
corresponding lemmas of `EpsSlotAux`; the same parametric differentiation
(`hasDerivAt_intervalIntegral_of_deriv_le`) supplies each single step. -/
theorem mixed_intervalIntegral_eq_gen {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq_gen (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ
    (l := i) (by omega)
  have hB := DzIter_intervalIntegral_eq_gen (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ
    j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

end Work.FTS.StrongEps.E5G5
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.LimExtract

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The elementary lower bound for `sin (2θ)` on a closed angular interval.**  For `0 < c` and
`d < π/2` and every `θ ∈ [c,d]`, the (positive) number `(4/π) · min c (π/2 - d)` is a lower bound
for `sin (2θ)`.

Both ingredients are elementary: `min c (π/2 - d) ≤ min θ (π/2 - θ)`, and `Real.mul_le_sin`
(`(2/π)x ≤ sin x` for `x ∈ [0,π/2]`) applied to `x = 2θ` when `θ ≤ π/4` and to `x = π - 2θ` (with
`Real.sin_pi_sub`) when `θ ≥ π/4`. -/
lemma sin_two_ge_min_of_Icc {c d θ : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2)
    (hθ : θ ∈ Set.Icc c d) :
    (4 / Real.pi) * min c (Real.pi / 2 - d) ≤ Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  have hθ0 : 0 ≤ θ := le_trans (le_of_lt hc) hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := le_of_lt (lt_of_le_of_lt hθ.2 hd)
  have hcoef : (0 : ℝ) ≤ 4 / Real.pi := by positivity
  have hmn : min c (Real.pi / 2 - d) ≤ min θ (Real.pi / 2 - θ) :=
    le_min (le_trans (min_le_left c (Real.pi / 2 - d)) hθ.1)
      (by have hm := min_le_right c (Real.pi / 2 - d); linarith [hθ.2])
  have h1 : (4 / Real.pi) * min c (Real.pi / 2 - d)
      ≤ (4 / Real.pi) * min θ (Real.pi / 2 - θ) :=
    mul_le_mul_of_nonneg_left hmn hcoef
  rcases le_total θ (Real.pi / 4) with h | h
  · have hmn' : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hmn'] at h1
    have h2 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have h3 : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    linarith [h1, h2, h3.le, h3.ge]
  · have hmn' : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hmn'] at h1
    have h2 : 2 / Real.pi * (Real.pi - 2 * θ) ≤ Real.sin (Real.pi - 2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at h2
    have h3 : 2 / Real.pi * (Real.pi - 2 * θ) = (4 / Real.pi) * (Real.pi / 2 - θ) := by ring
    linarith [h1, h2, h3.le, h3.ge]

theorem limExtract_bounds10_const {C : ℝ} {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 → |Work.Spaces.mixed j i (G n) z θ| ≤ C) :
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C' : ℝ,
        ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ‖Work.FTS_EllLimOK.fam10 G n p‖ ≤ C') ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ∀ q : ℝ × ℝ, q ∈ K →
          dist p q < δ → ‖Work.FTS_EllLimOK.fam10 G n p - Work.FTS_EllLimOK.fam10 G n q‖ < ε) := by
  -- replace `C` by `max C 0`, so that the bound is a nonnegative constant
  have hM : ∀ (n j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 → |Work.Spaces.mixed j i (G n) z θ| ≤ max C 0 :=
    fun n j i hji z θ hQ => le_trans (hbnd n j i hji z θ hQ) (le_max_left C 0)
  constructor
  · -- (1) local uniform boundedness of the family on compact subsets of the open quadrant
    intro K hKc hKQ
    refine ⟨max C 0, ?_⟩
    intro n p hp
    rw [pi_norm_le_iff_of_nonneg (le_max_right C 0)]
    intro m
    have hsum := P10_sum_le_three m
    simpa only [Work.FTS_EllLimOK.fam10, Real.norm_eq_abs] using
      hM n (P10 m).1 (P10 m).2 (by omega) p.1 p.2 (hKQ hp)
  · -- (2) local uniform equicontinuity of the family on compact subsets of the open quadrant
    intro K hKc hKQ ε hε
    rcases Set.eq_empty_or_nonempty K with rfl | hne
    · -- the empty compact set: any `δ` works
      exact ⟨1, one_pos, fun n p hp => absurd hp (Set.notMem_empty p)⟩
    obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
      Work.FTS_EllLimOK.box_of_compact_inside_Q0 hKc hKQ hne
    -- the box lies in the open quadrant
    have hboxQ : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨lt_of_lt_of_le ha hp1.1, lt_of_lt_of_le hc hp2.1, lt_of_le_of_lt hp2.2 hd⟩
    -- the angular lower bound `s₀ > 0` for `sin(2θ)` on `[c,d]`
    set s0 : ℝ := (4 / Real.pi) * min c (Real.pi / 2 - d) with hs0def
    have hs0pos : 0 < s0 := by
      rw [hs0def]; exact mul_pos (by positivity) (lt_min hc (by linarith))
    have hs0le : ∀ θ ∈ Set.Icc c d, s0 ≤ Real.sin (2 * θ) := by
      intro θ hθI; rw [hs0def]; exact sin_two_ge_min_of_Icc hc hd hθI
    -- the `∂_z`-derivative of an order-`≤ 3` jet, divided by `z`, is bounded by `M / a` on the box
    have hpz : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ| ≤ max C 0 / a := by
      intro n j i hji z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).1 z θ hQ]
      have hb := hM n (j + 1) i (by omega) z θ hQ
      rw [abs_div, abs_of_pos hzpos, div_le_div_iff₀ hzpos ha]
      calc |Work.Spaces.mixed (j + 1) i (G n) z θ| * a ≤ max C 0 * a :=
            mul_le_mul_of_nonneg_right hb (le_of_lt ha)
        _ ≤ max C 0 * z := mul_le_mul_of_nonneg_left hz.1 (le_max_right C 0)
    -- the `∂_θ`-derivative of an order-`≤ 3` jet, divided by `sin 2θ`, is bounded by `M / s₀`
    have hpth : ∀ (n j i : ℕ), j + i ≤ 3 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ| ≤ max C 0 / s0 := by
      intro n j i hji z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i (hsm n)).2.1 z θ hQ]
      have hb := hM n j (i + 1) (by omega) z θ hQ
      rw [abs_div, abs_of_pos hsin, div_le_div_iff₀ hsin hs0pos]
      calc |Work.Spaces.mixed j (i + 1) (G n) z θ| * s0 ≤ max C 0 * s0 :=
            mul_le_mul_of_nonneg_right hb (le_of_lt hs0pos)
        _ ≤ max C 0 * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (hs0le θ hθI) (le_max_right C 0)
    -- the common Lipschitz constant on the box
    set L : ℝ := max (max C 0 / a) (max C 0 / s0) + 1 with hLdef
    have hLpos : 0 < L := by
      rw [hLdef]
      have h0 : 0 ≤ max (max C 0 / a) (max C 0 / s0) :=
        le_trans (div_nonneg (le_max_right C 0) (le_of_lt ha)) (le_max_left _ _)
      linarith
    have hLz : max C 0 / a ≤ L := by
      rw [hLdef]; have := le_max_left (max C 0 / a) (max C 0 / s0); linarith
    have hLth : max C 0 / s0 ≤ L := by
      rw [hLdef]; have := le_max_right (max C 0 / a) (max C 0 / s0); linarith
    -- slice differentiability in `z`, at fixed angle
    have hslice_z : ∀ (n j i : ℕ), ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
        HasDerivWithinAt (fun z' : ℝ => Work.Spaces.mixed j i (G n) z' θ)
          (Work.Spaces.pz (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc a b) z := by
      intro n j i θ hθI z hz
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (((hsm n).mixed j i).hasDerivAt_slice ⟨hθ0, hθ1⟩ hzpos).hasDerivWithinAt
    -- slice differentiability in `θ`, at fixed radius
    have hslice_θ : ∀ (n j i : ℕ), ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        HasDerivWithinAt (fun θ' : ℝ => Work.Spaces.mixed j i (G n) z θ')
          (Work.Spaces.pth (Work.Spaces.mixed j i (G n)) z θ) (Set.Icc c d) θ := by
      intro n j i z hz θ hθI
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hboxQ (Set.mem_prod.mpr ⟨hz, hθI⟩)
      obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
      exact (Work.FTS_EllLimOK.smoothOpen_hasDerivAt_slice_theta ((hsm n).mixed j i) hzpos
        ⟨hθ0, hθ1⟩).hasDerivWithinAt
    -- every component of the family is `L`-Lipschitz on the box, hence on `K`
    have hcoord : ∀ (n : ℕ) (m : Fin 10) (p q : ℝ × ℝ), p ∈ K → q ∈ K →
        |Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m|
          ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := by
      intro n m p q hp hq
      have hb := Work.FTS_EllLimOK.abs_sub_le_of_box_bounds
        (g := Work.Spaces.mixed (P10 m).1 (P10 m).2 (G n))
        (hslice_z n (P10 m).1 (P10 m).2) (hslice_θ n (P10 m).1 (P10 m).2)
        (fun z hz θ hθI =>
          le_trans (hpz n (P10 m).1 (P10 m).2 (P10_sum_le_three m) z hz θ hθI) hLz)
        (fun z hz θ hθI =>
          le_trans (hpth n (P10 m).1 (P10 m).2 (P10_sum_le_three m) z hz θ hθI) hLth)
        p (hbox hp) q (hbox hq)
      simpa only [Work.FTS_EllLimOK.fam10] using hb
    -- the `ε`-`δ` step
    refine ⟨ε / (4 * (L + 1)), by positivity, ?_⟩
    intro n p hp q hq hdist
    have hL1pos : 0 < L + 1 := by linarith
    have hmax1 : |p.1 - q.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hmax2 : |p.2 - q.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have hsum : |p.1 - q.1| + |p.2 - q.2| ≤ 2 * dist p q := by linarith
    have hbound : ‖Work.FTS_EllLimOK.fam10 G n p - Work.FTS_EllLimOK.fam10 G n q‖ ≤ ε / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2)]
      intro m
      change ‖Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m‖ ≤ ε / 2
      have hcm := hcoord n m p q hp hq
      have hstep1 : |Work.FTS_EllLimOK.fam10 G n p m - Work.FTS_EllLimOK.fam10 G n q m|
          ≤ L * (2 * dist p q) :=
        le_trans hcm (mul_le_mul_of_nonneg_left hsum (le_of_lt hLpos))
      have hstep2 : L * (2 * dist p q) ≤ (L + 1) * (2 * dist p q) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hstep3 : (L + 1) * (2 * dist p q) < (L + 1) * (2 * (ε / (4 * (L + 1)))) :=
        mul_lt_mul_of_pos_left (by linarith) hL1pos
      have hstep4 : (L + 1) * (2 * (ε / (4 * (L + 1)))) = ε / 2 := by
        have hne : L + 1 ≠ 0 := ne_of_gt hL1pos
        field_simp
        norm_num
      rw [Real.norm_eq_abs]
      linarith
    linarith

end Work.FTS_EllLimOK.LimExtract
end
