import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Slots
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Leaf
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slot_transfer_deriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logPlane_transfer_deriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/JfamPDefectTransfer.lean` — the level-four `ε`-transfer, assembled locally

The `Jeps`-transfer estimate at the level-four pairing

  `|IP4 α (J_ε f) g − IP4 α f (J_ε g)| ≤ C ε ‖f‖_{ℋ⁴} (‖g‖_{ℋ⁴} + ‖g‖_{ℋ⁵})`

(the component `E3` of the `hneg` argument of the level-four barrier).  The analytic content is the
*slot* transfer of `TransferDeriv/IP4Leaf.lean` (`SlotTransfer`, proved by `slot_transfer_deriv`
from the plane estimate `logPlane_transfer_deriv`); this file lifts it to the three-step recursion
`IP4 = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` **without** introducing a
recursively defined defect: the slot bookkeeping is carried by the predicate `Good ρ α K P k`
("the defect of the pairing `P` is `O(ε)` at every slot of order `≤ k`"), the base case `k = 3` is
`IP4Leaf.leaf_bound`, and each recursion step lowers the slot budget by one (the shifted slots have
one more derivative).  Three applications give the level-four statement.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Pairings that only see the open quadrant -/

/-- A pairing whose value only depends on the two arguments on the open quadrant `Q0` (the
quadrant is co-null for every pairing of the chapter, and all the identities `D_θ`/`D_z` commute
for smooth profiles hold there). -/
def SeesQ0 (P : Fn → Fn → ℝ) : Prop :=
  ∀ X X' Y Y' : Fn,
    Set.EqOn (Function.uncurry X) (Function.uncurry X') Work.FTS.EllipticEst.Q0 →
    Set.EqOn (Function.uncurry Y) (Function.uncurry Y') Work.FTS.EllipticEst.Q0 →
    P X Y = P X' Y'

/-- `H1IP` only sees its arguments on the open quadrant. -/
theorem seesQ0_H1IP (α : ℝ) : SeesQ0 (Work.Coercivity.H1IP α) :=
  fun X X' Y Y' hX hY =>
    Work.FTS.StrongEps.EpsE4Thr.H1IP_congr_Q0 α (fun _ _ h => hX h) (fun _ _ h => hY h)

/-- The recursion `HkIPStep` preserves "only sees the open quadrant". -/
theorem seesQ0_hkIPStep {P : Fn → Fn → ℝ} (hP : SeesQ0 P) (c₁ c₂ : ℝ) :
    SeesQ0 (Work.Coercivity.HkIPStep c₁ c₂ P) := by
  intro X X' Y Y' hX hY
  have hDX : Set.EqOn (Function.uncurry (Work.Spaces.DthIter 1 X))
      (Function.uncurry (Work.Spaces.DthIter 1 X')) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.TransportS.DthIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 hX 1
  have hDY : Set.EqOn (Function.uncurry (Work.Spaces.DthIter 1 Y))
      (Function.uncurry (Work.Spaces.DthIter 1 Y')) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.TransportS.DthIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 hY 1
  have hZX : Set.EqOn (Function.uncurry (Work.Spaces.DzIter 1 X))
      (Function.uncurry (Work.Spaces.DzIter 1 X')) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 hX 1
  have hZY : Set.EqOn (Function.uncurry (Work.Spaces.DzIter 1 Y))
      (Function.uncurry (Work.Spaces.DzIter 1 Y')) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 hY 1
  have eD : Work.Spaces.DthIter 1 = (Work.Spaces.Dth : Fn → Fn) := rfl
  have eZ : Work.Spaces.DzIter 1 = (Work.Spaces.Dz : Fn → Fn) := rfl
  rw [eD] at hDX hDY
  rw [eZ] at hZX hZY
  simp only [Work.Coercivity.HkIPStep]
  rw [hP X X' Y Y' hX hY, hP (Work.Spaces.Dth X) (Work.Spaces.Dth X')
        (Work.Spaces.Dth Y) (Work.Spaces.Dth Y') hDX hDY,
    hP (Work.Spaces.Dz X) (Work.Spaces.Dz X') (Work.Spaces.Dz Y) (Work.Spaces.Dz Y') hZX hZY]

/-! ## The slot-indexed defect predicate -/

/-- **The transfer defect of a pairing at every slot of bounded order.**  `Good ρ α K P k` says
that `P` only sees the open quadrant and that its `J_ε`-defect at the shifted slots
`D_z^b D_θ^a` (`a + b ≤ k`) is `O(ε)`, with one derivative charged on the second argument. -/
def Good (ρ : ℝ × ℝ → ℝ) (α : ℝ) (K : ℝ) (P : Fn → Fn → ℝ) (k : ℕ) : Prop :=
  SeesQ0 P ∧
  ∀ (ε : ℝ), ε ∈ Set.Ioc (0 : ℝ) 1 →
  ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 5 g →
    ∀ b a : ℕ, a + b ≤ k →
      |P (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f)) (Work.Spaces.mixed b a g)
        - P (Work.Spaces.mixed b a f) (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))|
        ≤ K * ε * Work.Spaces.HkNorm α 4 f
            * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g)

/-! ## The base case: `H1IP` -/

theorem good_H1IP {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    Good ρ α (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) (Work.Coercivity.H1IP α) 3 := by
  refine ⟨seesQ0_H1IP α, ?_⟩
  intro ε hε f g hfs hhs hmf hmh b a hab
  -- the slot of the mollified profile is the mollification of the slot
  have eJf : Set.EqOn (Function.uncurry
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f)))
      (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε.1
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hfs) hp.1 hp.2 b a
  have eJg : Set.EqOn (Function.uncurry
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g)))
      (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a g)))
      Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε.1
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hhs) hp.1 hp.2 b a
  have hXY : Work.Coercivity.H1IP α
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f)) (Work.Spaces.mixed b a g)
      = Work.Coercivity.H1IP α (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a f))
          (Work.Spaces.mixed b a g) :=
    seesQ0_H1IP α _ _ _ _ eJf (fun _ _ => rfl)
  have hXY' : Work.Coercivity.H1IP α (Work.Spaces.mixed b a f)
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))
      = Work.Coercivity.H1IP α (Work.Spaces.mixed b a f)
          (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a g)) :=
    seesQ0_H1IP α _ _ _ _ (fun _ _ => rfl) eJg
  rw [hXY, hXY']
  have h := leaf_bound hρ hK hST hα hε hfs hhs hmf hmh (a₀ := a) (b₀ := b) (by omega)
  refine h.trans ?_
  have hle : Work.Spaces.HkNorm α 5 g
      ≤ Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g :=
    le_add_of_nonneg_left (Work.Spaces.HkNorm_nonneg α 4 g)
  refine mul_le_mul_of_nonneg_left hle ?_
  have hK0 : (0 : ℝ) ≤ 3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) := by norm_num
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε.1
  exact mul_nonneg (mul_nonneg (mul_nonneg hK0 hK) hε0)
    (Work.Spaces.HkNorm_nonneg α 4 f)

/-! ## The recursion step -/

theorem good_step {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} {K c₁ c₂ : ℝ} {P : Fn → Fn → ℝ} {k : ℕ}
    (hP : Good ρ α K P (k + 1)) :
    Good ρ α (K * (1 + |c₁| + |c₂|)) (Work.Coercivity.HkIPStep c₁ c₂ P) k := by
  obtain ⟨hS, hB⟩ := hP
  refine ⟨seesQ0_hkIPStep hS c₁ c₂, ?_⟩
  intro ε hε f g hfs hhs hmf hmh b a hab
  have h0 := hB ε hε f g hfs hhs hmf hmh b a (by omega)
  have h1 := hB ε hε f g hfs hhs hmf hmh b (a + 1) (by omega)
  have h2 := hB ε hε f g hfs hhs hmf hmh (b + 1) a (by omega)
  -- smoothness of the mollified profiles (the shift identities need it)
  have hJf : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hfs)
  have hJg : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hhs)
  -- the `D_θ`-shifts
  have eth1 : Set.EqOn (Function.uncurry
        (Work.Spaces.Dth (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f))))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε f)))
      Work.FTS.EllipticEst.Q0 := Dth_mixed_eqOn hJf b a
  have eth2 : Set.EqOn (Function.uncurry
        (Work.Spaces.Dth (Work.Spaces.mixed b a g)))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) g))
      Work.FTS.EllipticEst.Q0 := Dth_mixed_eqOn hhs b a
  have eth3 : Set.EqOn (Function.uncurry
        (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) f))
      Work.FTS.EllipticEst.Q0 := Dth_mixed_eqOn hfs b a
  have eth4 : Set.EqOn (Function.uncurry
        (Work.Spaces.Dth (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε g)))
      Work.FTS.EllipticEst.Q0 := Dth_mixed_eqOn hJg b a
  -- the `D_z`-shifts (definitional)
  have ez1 : Work.Spaces.Dz (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f))
      = Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε f) := rfl
  have ez2 : Work.Spaces.Dz (Work.Spaces.mixed b a g)
      = Work.Spaces.mixed (b + 1) a g := rfl
  have ez3 : Work.Spaces.Dz (Work.Spaces.mixed b a f)
      = Work.Spaces.mixed (b + 1) a f := rfl
  have ez4 : Work.Spaces.Dz (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))
      = Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε g) := rfl
  -- the recursion identity for the defect
  have key : Work.Coercivity.HkIPStep c₁ c₂ P
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f)) (Work.Spaces.mixed b a g)
      - Work.Coercivity.HkIPStep c₁ c₂ P (Work.Spaces.mixed b a f)
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))
      = (P (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f)) (Work.Spaces.mixed b a g)
          - P (Work.Spaces.mixed b a f) (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g)))
        + c₁ * (P (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε f))
              (Work.Spaces.mixed b (a + 1) g)
            - P (Work.Spaces.mixed b (a + 1) f)
              (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε g)))
        + c₂ * (P (Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε f))
              (Work.Spaces.mixed (b + 1) a g)
            - P (Work.Spaces.mixed (b + 1) a f)
              (Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε g))) := by
    simp only [Work.Coercivity.HkIPStep]
    rw [hS _ _ _ _ eth1 eth2, hS _ _ _ _ eth3 eth4, ez1, ez2, ez3, ez4]
    ring
  set A : ℝ := P (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε f))
      (Work.Spaces.mixed b a g)
    - P (Work.Spaces.mixed b a f) (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g))
    with hAdef
  set B : ℝ := P (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε f))
      (Work.Spaces.mixed b (a + 1) g)
    - P (Work.Spaces.mixed b (a + 1) f) (Work.Spaces.mixed b (a + 1) (Work.FTS.StrongEps.Jeps ρ ε g))
    with hBdef
  set D : ℝ := P (Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε f))
      (Work.Spaces.mixed (b + 1) a g)
    - P (Work.Spaces.mixed (b + 1) a f) (Work.Spaces.mixed (b + 1) a (Work.FTS.StrongEps.Jeps ρ ε g))
    with hDdef
  have hA : |A| ≤ K * ε * Work.Spaces.HkNorm α 4 f
      * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) := h0
  have hB' : |B| ≤ K * ε * Work.Spaces.HkNorm α 4 f
      * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) := h1
  have hD' : |D| ≤ K * ε * Work.Spaces.HkNorm α 4 f
      * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) := h2
  have hsum : |A + c₁ * B + c₂ * D|
      ≤ (1 + |c₁| + |c₂|) * (K * ε * Work.Spaces.HkNorm α 4 f
          * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g)) := by
    set C : ℝ := K * ε * Work.Spaces.HkNorm α 4 f
      * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) with hCdef
    have h1' : |c₁ * B| ≤ |c₁| * C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB' (abs_nonneg c₁)
    have h2' : |c₂ * D| ≤ |c₂| * C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD' (abs_nonneg c₂)
    have h3 := abs_add_le (A + c₁ * B) (c₂ * D)
    have h4 := abs_add_le A (c₁ * B)
    have h5 : |A| + |c₁ * B| + |c₂ * D| ≤ (1 + |c₁| + |c₂|) * C := by
      have e : (1 + |c₁| + |c₂|) * C = C + |c₁| * C + |c₂| * C := by ring
      linarith [hA, h1', h2']
    linarith [h3, h4]
  have e2 : (1 + |c₁| + |c₂|) * (K * ε * Work.Spaces.HkNorm α 4 f
        * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g))
      = K * (1 + |c₁| + |c₂|) * ε * Work.Spaces.HkNorm α 4 f
          * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) := by ring
  rw [key, hAdef, hBdef, hDdef]
  rw [← e2]
  exact hsum

/-! ## The level-four transfer estimate -/

theorem IP4_transfer_deriv_local (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
        Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 5 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.FTS.StrongEps.Jeps ρ ε f) g
          - Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f
              (Work.FTS.StrongEps.Jeps ρ ε g)|
          ≤ C * ε * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 g + Work.Spaces.HkNorm α 5 g) := by
  obtain ⟨K, hK, hST⟩ := slot_transfer_deriv (ρ := ρ) hρ logPlane_transfer_deriv
  refine ⟨(3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|)
      * (1 + |c₁'| + |c₂'|) * (1 + |c₁''| + |c₂''|), by positivity, ?_⟩
  intro α hα ε hε f g hfs hhs hmf hmh
  have h1 : Good ρ α (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K)
      (Work.Coercivity.H1IP α) 3 := good_H1IP hρ hK hST hα
  have h2 : Good ρ α ((3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|))
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)) 2 :=
    good_step hρ (c₁ := c₁) (c₂ := c₂) h1
  have h3 : Good ρ α (((3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|))
        * (1 + |c₁'| + |c₂'|))
      (Work.Coercivity.HkIPStep c₁' c₂'
        (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))) 1 :=
    good_step hρ (c₁ := c₁') (c₂ := c₂') h2
  have h4 : Good ρ α ((((3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|))
        * (1 + |c₁'| + |c₂'|)) * (1 + |c₁''| + |c₂''|))
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) 0 :=
    good_step hρ (c₁ := c₁'') (c₂ := c₂'') h3
  have h5 := h4.2 ε hε f g hfs hhs hmf hmh 0 0 (by norm_num)
  have e : ((((3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|))
        * (1 + |c₁'| + |c₂'|)) * (1 + |c₁''| + |c₂''|))
      = (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K) * (1 + |c₁| + |c₂|)
        * (1 + |c₁'| + |c₂'|) * (1 + |c₁''| + |c₂''|) := by ring
  rw [e] at h5
  simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
    Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h5

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
