import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Slots
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Leaf.lean` — the level-zero transfer bound

The level-one pairing `H1IP α` is a linear combination of four `wip` slots, so its transfer defect
at the shifted words `D_z^{b₀}D_θ^{a₀}` is the sum of four *slot* defects, each controlled by the
hypothesis `SlotTransfer`; the `√`-factors are replaced by the `ℋ⁴`- and `ℋ⁵`-norms.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The level-zero bound -/

/-- The slot transfer hypothesis of the headline, as a predicate. -/
def SlotTransfer (ρ : ℝ × ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {w : ℝ → ℝ → ℝ} {a b : ℕ}, Work.FTS.TransportS.IsLeafW α a w → a + b ≤ 4 →
    ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
    SlotIntegrableDeriv ρ ε w a b u v →
    |Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
        (Work.Spaces.mixed b a v)
      - Work.Coercivity.wip w (Work.Spaces.mixed b a u)
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))|
      ≤ K * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a u)
            (Work.Spaces.mixed b a u))
        * (Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a v)
              (Work.Spaces.mixed b a v))
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a v)
              (Work.Spaces.mixed (b + 1) a v))
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
              (Work.Spaces.mixed b (a + 1) v)))

theorem abs_sum_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- **The slot transfer at the shifted words.**  The slot transfer hypothesis, applied to the two
schematically given profiles `D_z^{b₀}D_θ^{a₀}f` and `D_z^{b₀}D_θ^{a₀}h` through their cuts, with
the `√`-factors replaced by the `ℋ⁴`- and `ℋ⁵`-norms by the composed-slot identity. -/
theorem slot_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (hmf : Work.Spaces.HkMem α 4 f) (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ : ℕ}
    (hab₀ : a₀ + b₀ ≤ 3) {w : ℝ → ℝ → ℝ} {a b : ℕ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a w) (hab : a + b ≤ 1) :
    |Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  set U : Fn := cut (Work.Spaces.mixed b₀ a₀ f) with hU
  set V : Fn := cut (Work.Spaces.mixed b₀ a₀ h) with hV
  have hJU : Work.FTS.StrongEps.Jeps ρ ε U
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f) := Jeps_cut ρ ε _
  have hJV : Work.FTS.StrongEps.Jeps ρ ε V
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h) := Jeps_cut ρ ε _
  have hint := slotIntegrableDeriv_cut hρ hα hε hfs hhs hmf hmh hab₀ hab hleaf
  have h1 := hST α hα ε hε hleaf (by omega) U V
    (by rw [hU]; exact smoothOpen_cut (hfs.mixed b₀ a₀))
    (by rw [hV]; exact smoothOpen_cut (hhs.mixed b₀ a₀)) hint
  have hconv1 : Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a V)
      = Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h)) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_snd
      (fun z θ hh => by rw [hV]; exact mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b a hh)
  have hconv2 : Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
      = Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_fst
      (fun z θ hh => by rw [hU]; exact mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a hh)
  rw [hJU, hJV, hconv1, hconv2] at h1
  -- the `√`-factors
  have hAU : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a U)) ≤ Work.Spaces.HkNorm α 4 f := by
    rw [hU]
    exact sqrt_wip_cut_le hα0 hfs (by omega : (a + a₀) + (b + b₀) ≤ 4) (IsLeafW.add hleaf) hmf
  have hBV : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
        (Work.Spaces.mixed b a V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + a₀) + (b + b₀) ≤ 5) (IsLeafW.add hleaf) hmh
  have hBV1 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
        (Work.Spaces.mixed (b + 1) a V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + a₀) + (b + 1 + b₀) ≤ 5)
      (IsLeafW.mono hleaf (Nat.le_add_right a a₀)) hmh
  have hBV2 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
        (Work.Spaces.mixed b (a + 1) V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + 1 + a₀) + (b + b₀) ≤ 5)
      (IsLeafW.mono hleaf (by omega : a ≤ a + 1 + a₀)) hmh
  have hN4 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hN5 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 5 h := Work.Spaces.HkNorm_nonneg α 5 h
  have hR : (0 : ℝ) ≤ Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
        (Work.Spaces.mixed b a V))
      + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
          (Work.Spaces.mixed (b + 1) a V))
      + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
          (Work.Spaces.mixed b (a + 1) V)) := by positivity
  have hL : K * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a U)) ≤ K * ε * Work.Spaces.HkNorm α 4 f :=
    mul_le_mul_of_nonneg_left hAU (mul_nonneg hK hε0.le)
  have h2 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
          (Work.Spaces.mixed b a V))
        + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
            (Work.Spaces.mixed (b + 1) a V))
        + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
            (Work.Spaces.mixed b (a + 1) V))
      ≤ 3 * Work.Spaces.HkNorm α 5 h := by linarith
  refine h1.trans ?_
  refine (mul_le_mul hL h2 hR (by positivity)).trans (le_of_eq ?_)
  ring

/-- The four-slot decomposition of `H1IP`. -/
theorem H1IP_eq_slots (α : ℝ) (X Y : Fn) :
    Work.Coercivity.H1IP α X Y
      = 10 * Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.Dz X)
            (Work.Spaces.Dz Y)
        + 10 ^ 10 * Work.Coercivity.wip Work.FTS.TransportS.leafEta X Y
        + 10 ^ 17 * Work.Coercivity.wip Work.FTS.TransportS.leafOne X Y
        + 10 ^ 21 * Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth X) (Work.Spaces.Dth Y) := by
  simp only [Work.Coercivity.H1IP]
  rw [show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = Work.FTS.TransportS.leafEta from rfl,
      show (fun z _ : ℝ => (Work.Spaces.w z) ^ 2) = Work.FTS.TransportS.leafOne from rfl,
      show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = Work.FTS.TransportS.leafGam α from rfl]

/-- **The level-zero transfer bound**: the transfer defect of `H1IP` at the shifted words is
`O(ε)`, with one derivative charged on the second argument. -/
theorem leaf_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (hmf : Work.Spaces.HkMem α 4 f) (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ : ℕ}
    (hab : a₀ + b₀ ≤ 3) :
    |Work.Coercivity.H1IP α
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.H1IP α (Work.Spaces.mixed b₀ a₀ f)
          (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ 3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h := by
  have hdecomp : Work.Coercivity.H1IP α
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.H1IP α (Work.Spaces.mixed b₀ a₀ f)
          (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))
      = 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
            (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ h))
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))))
        + 10 ^ 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.mixed b₀ a₀ h)
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.mixed b₀ a₀ f)
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
        + 10 ^ 17 * (Work.Coercivity.wip Work.FTS.TransportS.leafOne
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.mixed b₀ a₀ h)
          - Work.Coercivity.wip Work.FTS.TransportS.leafOne (Work.Spaces.mixed b₀ a₀ f)
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
        + 10 ^ 21 * (Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
            (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ h))
          - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))) := by
    rw [H1IP_eq_slots, H1IP_eq_slots]
    ring
  have i1 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 1) (Or.inl rfl) (by norm_num)
  have i2 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 0) (Or.inl rfl) (by norm_num)
  have i3 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafOne) (a := 0) (b := 0) (Or.inr (Or.inl rfl)) (by norm_num)
  have i4 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafGam α) (a := 1) (b := 0)
    (Or.inr (Or.inr ⟨le_refl 1, rfl⟩)) (by norm_num)
  have hC : (0 : ℝ) ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK hε.1.le) (Work.Spaces.HkNorm_nonneg α 4 f))
      (mul_nonneg (by norm_num) (Work.Spaces.HkNorm_nonneg α 5 h))
  -- the four slot bounds, in the form in which they occur in the decomposition
  have j1 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i1
  have j2 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.mixed b₀ a₀ f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i2
  have j3 : |Work.Coercivity.wip Work.FTS.TransportS.leafOne
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.wip Work.FTS.TransportS.leafOne (Work.Spaces.mixed b₀ a₀ f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i3
  have j4 : |Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i4
  rw [hdecomp]
  refine (abs_sum_four_le _ _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  norm_num
  have e : (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21)
        * (K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h))
      = 3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h := by ring
  linarith [e, j1, j2, j3, j4]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
