import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.StrongPersist.N6Trans.slotT1Six
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.N6Trans.slotT3SixRoute
import Submission.Work.FTS.TransportS.T2S_coef2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6Trans_exists` — the level-six transport clauses for `IP6`

`N6Trans (IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ct` is the `k = 6` restatement of the transport clauses
T1/T2/T3 of Elgindi's paper (tex 1099–1123) for the concrete coercive pairing `IP6` with all
step coefficients `1`.

## The route

`IP6 1 1 1 1 1 1 1 1 1 1 α = IPn α 5` (the five-fold iteration of `HkIPStep 1 1` applied to
`H1IP`), and the proved unfolding bound `Work.FTS.TransportS.ip4_unfold_bound` gives

  `|IP6 1 … 1 α u v| ≤ 3^5 · 10^22 · SlotSum α 6 u v`,

where `SlotSum α 6 u v` is the sum of the absolute values of the *leaf slot pairings*
`∫_z ∫_θ ρ · (D_z^b D_θ^a u) · (D_z^b D_θ^a v)` over the slots `a + b ≤ 6` and the three leaf
weights `ρ` of `H1IP` (`leafEta`, `leafOne`, and `leafGam α` at the slots with `a ≥ 1`).

The three clauses therefore follow from the three *per-slot* transport estimates at level six,
one for each of the three velocity classes of the paper:

* `slotT1Six` — `D_θ`-transport with an `ℋ⁶`-coefficient (the paper's `Transport1`, tex 1099);
* `slotT2Six` — `D_z`-transport with a flat angular coefficient (the paper's `Transport2`,
  tex 1114, in the `CoefTh`-form of `VocabO.T2Clause`);
* `slotT3Six` — `D_z`-transport with a `𝒲^{6,∞}`-coefficient (the paper's `Transport3`,
  tex 1119).

The present file contains the *assembly*: the unfolding, the summation over the `84 = 28 · 3`
leaf slots, the merging of the three constants, and the packaging into the `N6Trans` structure.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem SmoothOpen.mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hF.mul hG using 1
  ext p
  rfl

/-- `IPn α 5` is the concrete `IP6 1 1 1 1 1 1 1 1 1 1`. -/
theorem IP6_one_eq_IPn_five (α : ℝ) (u v : Fn) :
    IP6 1 1 1 1 1 1 1 1 1 1 α u v = Work.FTS.TransportS.IPn α 5 u v := by
  have hIP6 : IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  have h5 : Work.FTS.TransportS.IPn α 5
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  rw [hIP6, h5]

/-- The level-six slot sum is bounded by `84 * B` when every leaf slot is bounded by `B`:
there are `28` slots `(a,b)` with `a + b ≤ 6` and three leaf weights each. -/
theorem SlotSum_six_le (α : ℝ) (u v : Fn) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b u v| ≤ B) :
    Work.FTS.TransportS.SlotSum α 6 u v ≤ 84 * B := by
  have hterm : ∀ a ∈ Finset.range 7, ∀ b ∈ Finset.range (7 - a),
      Work.FTS.TransportS.SlotTerm α a b u v ≤ 3 * B := by
    intro a ha b hb
    have hab : a + b ≤ 6 := by
      have h1 : a ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have h2 : b < 7 - a := Finset.mem_range.mp hb
      omega
    have hE := hB a b Work.FTS.TransportS.leafEta hab (Or.inl rfl)
    have hO := hB a b Work.FTS.TransportS.leafOne hab (Or.inr (Or.inl rfl))
    have hG : (if 1 ≤ a then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) ≤ B := by
      by_cases h : 1 ≤ a
      · rw [if_pos h]
        exact hB a b (Work.FTS.TransportS.leafGam α) hab (Or.inr (Or.inr ⟨h, rfl⟩))
      · rw [if_neg h]; exact hB0
    calc Work.FTS.TransportS.SlotTerm α a b u v
        = |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u v|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u v|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) := rfl
      _ ≤ B + B + B := by linarith
      _ = 3 * B := by ring
  calc Work.FTS.TransportS.SlotSum α 6 u v
      = ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a),
          Work.FTS.TransportS.SlotTerm α a b u v :=
        Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm α 6 u v
    _ ≤ ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a), (3 * B) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ) * (3 * B) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) * (3 * B) := by
        rw [Finset.sum_mul]
    _ = 84 * B := by
        have h : (∑ a ∈ Finset.range 7, (7 - a)) = 28 := by decide
        have h' : (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) = 28 := by
          exact_mod_cast h
        rw [h']; ring

/-! ## The three clauses from the per-slot bounds -/

/-- **The `t1` clause at level six from the per-slot `D_θ` bounds.** -/
theorem T1Clause6_of_slot {A C1 : ℝ} (hC1 : 0 < C1)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    T1Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * C1) := by
  intro α hα f g hf hg
  obtain ⟨hF, hmF⟩ := hf
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dth g z θ) :=
    hF.mul hG.Dth
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dth g z θ) g hsm hG
  rw [← hIP] at hb
  have hX0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hY0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1.le hr0) hX0) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hG hmG hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) (le_of_eq ?_))
  simp only [hP]
  ring

/-- **The `t2` clause at level six from the per-slot `D_z` bounds.** -/
theorem T2Clause6_of_slot {A C2 : ℝ} (hC2 : 0 < C2)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.CoefThMem 1 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C2 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    T2Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * C2) := by
  intro α hα f g hF hmF hcf hg hm7 hdec
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    hF.mul hG.Dz
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hsm hG
  rw [← hIP] at hb
  have hX0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hK0 : (0 : ℝ) ≤ Work.FTS.VocabO.CoefTh 1 f := Work.FTS.TransportS.coefTh_nonneg 1 f
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C2 * α ^ (-(1 / 2 : ℝ))
    * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC2.le hr0) (add_nonneg hX0 hK0)) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) (le_of_eq ?_))
  simp only [hP]
  ring

/-- **The `t3` clause at level six from the per-slot `D_z` bounds.** -/
theorem T3Clause6_of_slot {A C3 : ℝ} (hC3 : 0 < C3)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 3 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    T3Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * C3) := by
  intro α hα f g hF hmF hcf5 hg hm7 hdec
  have hcf3 : Work.FTS.VocabO.CoefThMem 3 f :=
    Work.FTS.TransportS.coefThMem_mono (by norm_num) hcf5
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    hF.mul hG.Dz
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hsm hG
  rw [← hIP] at hb
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C3 * α ^ (-(1 / 2 : ℝ))
    * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hmF
    have h2 : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
    exact mul_nonneg (mul_nonneg (mul_nonneg hC3.le hr0) (add_nonneg h1 h2)) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hcf3 hG hmG hm7 hdec hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  have hcoef : Work.FTS.VocabO.CoefTh 3 f ≤ Work.FTS.VocabO.CoefTh 5 f :=
    Work.FTS.TransportS.coefTh_mono (by norm_num) f
  have hX0 : (0 : ℝ) ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hmF
  have hY0 : (0 : ℝ) ≤ (Work.Spaces.HkNorm α 6 g) ^ 2 := sq_nonneg _
  have hN84 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 * 84 * C3 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) ?_)
  rw [hP]
  have hcore : C3 * α ^ (-(1 / 2 : ℝ))
        * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
        * (Work.Spaces.HkNorm α 6 g) ^ 2
      ≤ C3 * α ^ (-(1 / 2 : ℝ))
        * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
        * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have h1 : (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
        ≤ (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f) := by linarith
    have h2 : α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
        ≤ α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f) :=
      mul_le_mul_of_nonneg_left h1 hr0
    have h3 : C3 * (α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f))
        ≤ C3 * (α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)) :=
      mul_le_mul_of_nonneg_left h2 hC3.le
    have h4 := mul_le_mul_of_nonneg_right h3 hY0
    calc C3 * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2
        = C3 * (α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f))
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
      _ ≤ C3 * (α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f))
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := h4
      _ = C3 * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hstep : 3 ^ 5 * 10 ^ 22
        * (84 * (C3 * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2))
      ≤ (3 ^ 5 * 10 ^ 22 * 84 * C3) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    calc 3 ^ 5 * 10 ^ 22
          * (84 * (C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2))
        = (3 ^ 5 * 10 ^ 22 * 84) * (C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
      _ ≤ (3 ^ 5 * 10 ^ 22 * 84) * (C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
          mul_le_mul_of_nonneg_left hcore (by norm_num)
      _ = (3 ^ 5 * 10 ^ 22 * 84 * C3) * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  exact hstep

/-! ## The final assembly -/

/-- **The three per-slot bounds at level six give `N6Trans` for the concrete `IP6`.** -/
theorem N6Trans_of_slots
    (C1 C2 C3 a1 a2 a3 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (h1 : ∀ α ∈ Set.Ioc 0 a1, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2)
    (h2 : ∀ α ∈ Set.Ioc 0 a2, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.CoefThMem 1 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C2 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2)
    (h3 : ∀ α ∈ Set.Ioc 0 a3, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 3 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    ∃ α₂ Ct : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      N6Trans (IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ct := by
  set A : ℝ := min 1 (min a1 (min a2 a3)) with hA
  have hA0 : 0 < A := by
    rw [hA]; exact lt_min one_pos (lt_min ha1 (lt_min ha2 ha3))
  have hAa1 : A ≤ a1 := by
    rw [hA]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hAa2 : A ≤ a2 := by
    rw [hA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAa3 : A ≤ a3 := by
    rw [hA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have t1 : T1Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    T1Clause6_of_slot (A := A) (C1 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hG hmG hab hρ => by
        have hr := h1 α ⟨hα.1, le_trans hα.2 hAa1⟩ f g a b ρ hF hmF hG hmG hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
            ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C1 * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  have t2 : T2Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    T2Clause6_of_slot (A := A) (C2 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ => by
        have hr := h2 α ⟨hα.1, le_trans hα.2 hAa2⟩ f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f :=
          add_nonneg (Work.Spaces.HkNorm_nonneg α 6 f) (Work.FTS.TransportS.coefTh_nonneg 1 f)
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
            ≤ C2 * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C2 * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  have t3 : T3Clause6 (IP6 1 1 1 1 1 1 1 1 1 1) A (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    T3Clause6_of_slot (A := A) (C3 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ => by
        have hr := h3 α ⟨hα.1, le_trans hα.2 hAa3⟩ f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f :=
          add_nonneg (Work.Spaces.WlInf_nonneg α 6 f hmF) (Work.FTS.TransportS.coefTh_nonneg 3 f)
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
            ≤ C3 * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C3 * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 3 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  have hCtot : 0 < 3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3) := by positivity
  exact ⟨A, 3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3), hCtot, hA0,
    ⟨⟨hCtot, hA0⟩, t1, t2, t3⟩⟩

theorem N6Trans_exists : ∃ α₂ Ct : ℝ, 0 < Ct ∧ 0 < α₂ ∧
    Work.FTS.StrongPersist.N6Trans (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ct := by
  obtain ⟨C1, a1, hC1, ha1, h1⟩ := Work.FTS.StrongPersist.N6Trans.slotT1Six
  obtain ⟨C2, a2, hC2, ha2, h2⟩ := Work.FTS.StrongPersist.N6Trans.slotT2Six
  obtain ⟨C3, a3, hC3, ha3, h3⟩ := Work.FTS.StrongPersist.N6Trans.slotT3SixRoute
  exact N6Trans_of_slots C1 C2 C3 a1 a2 a3 hC1 hC2 hC3 ha1 ha2 ha3 h1 h2 h3

end Work.FTS.StrongPersist
