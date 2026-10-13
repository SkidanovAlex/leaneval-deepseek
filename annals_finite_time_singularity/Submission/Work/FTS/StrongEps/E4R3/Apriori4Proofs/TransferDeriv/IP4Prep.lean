import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Prep.lean` — the bookkeeping of the level-four derivative-priced transfer

`IP4_transfer_deriv` reduces the `O(ε)`-smallness of the level-four transfer defect
`IP4 α (J_ε f) h − IP4 α f (J_ε h)` to the hypothesised *slot* transfer `hslot`.  The slot transfer
is stated for the flat pairings `wip w (mixed b a ·) (mixed b a ·)`, while the recursion
`IP4 = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` produces the pairing at the
mixed slots `D_z^b D_θ^a` of *shifted* profiles.

This file contains the two elementary ingredients of that reduction.

* `cut u` — the profile which agrees with `u` on the open quadrant and vanishes outside.  It is the
  representative on which the slot transfer is applied: the pairing `wip` only sees the open
  quadrant, while the *integrability certificates* of the slot transfer are honest
  `Integrable`-statements over the whole plane, which can only hold for representatives that
  vanish off the quadrant.
* `mixed_comp` — the composition rule `D_z^{b'} D_θ^{a'} (D_z^b D_θ^a f) = D_z^{b'+b} D_θ^{a'+a} f`
  on the open quadrant, i.e. the fact that the slot of a slot is again a slot (it is the
  commutation of `D_θ` with the iterates of `D_z`, Clairaut's theorem on the open quadrant).
* `IsLeafW.mono` — the leaf weights of the slot transfer are indexed by the *angular* slot order
  `a`, the only constraint being `1 ≤ a` for the `γ`-weight, so the index may be raised.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The cut of a profile to the open quadrant -/

/-- The profile which is `u` on the open quadrant and `0` outside it.  The pairings `wip` of the
coercivity chapter only see the open quadrant (the boundary of `Iz × Iθ` is null), so `cut u`
represents the same slot data as `u`; on the other hand `cut u` and all its mixed derivatives
vanish off the closed quadrant, which is what makes the `Integrable`-certificates of the slot
transfer available. -/
def cut (u : Fn) : Fn := fun z θ => if 0 < z ∧ 0 < θ ∧ θ < π / 2 then u z θ else 0

@[simp] theorem cut_apply (u : Fn) (z θ : ℝ) :
    cut u z θ = if 0 < z ∧ 0 < θ ∧ θ < π / 2 then u z θ else 0 := rfl

/-- `cut u` agrees with `u` on the open quadrant. -/
theorem cut_eqOn_Q0 (u : Fn) :
    Set.EqOn (Function.uncurry (cut u)) (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show cut u p.1 p.2 = u p.1 p.2
  rw [cut_apply, if_pos (show 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 from ⟨hz, hθ0, hθ1⟩)]

/-- `cut u` is smooth wherever `u` is: the two agree on the open quadrant. -/
theorem smoothOpen_cut {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (cut u) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
    (hu.forall n).congr (fun p hp => cut_eqOn_Q0 u hp)

/-- `cut u` vanishes on the complement of the product of the open half lines. -/
theorem cut_eq_zero_of_not_mem {u : Fn} {z θ : ℝ}
    (h : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) : cut u z θ = 0 := by
  rw [cut_apply, ite_eq_right h]

/-! ## The leaf weights of the slot transfer -/

/-- The leaf weights are indexed by the angular order `a`, and the only constraint on the index is
the guard `1 ≤ a` of the `γ`-weight: hence the index may be raised. -/
theorem IsLeafW.mono {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ} (h : Work.FTS.TransportS.IsLeafW α a w)
    {a' : ℕ} (ha : a ≤ a') : Work.FTS.TransportS.IsLeafW α a' w := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨le_trans h1 ha, h2⟩)

/-- A leaf weight at the slot `a` is a leaf weight at every larger slot: the form used with the
composed slots. -/
theorem IsLeafW.add {α : ℝ} {a a' : ℕ} {w : ℝ → ℝ → ℝ} (h : Work.FTS.TransportS.IsLeafW α a w) :
    Work.FTS.TransportS.IsLeafW α (a + a') w :=
  IsLeafW.mono h (Nat.le_add_right a a')

/-! ## The composition of the slot operators -/

/-- **The slot of a slot is a slot**: on the open quadrant,
`D_z^{b'}D_θ^{a'}(D_z^bD_θ^a f) = D_z^{b'+b}D_θ^{a'+a} f` for `f` smooth there.  This is the
commutation of `D_θ` with the iterates of `D_z` (`DthIter_DzIter_eqOn`), which holds on the open
quadrant because the two operators carry multipliers depending on the *other* variable. -/
theorem mixed_comp {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (b a b' a' : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b' a' (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed (b' + b) (a' + a) f))
      Work.FTS.EllipticEst.Q0 := by
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter a f) := hf.DthIter a
  have h1 := Work.FTS.TransportS.DthIter_DzIter_eqOn hX b a'
  have h2 := Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h1 b'
  intro p hp
  have h3 := h2 hp
  change Work.Spaces.DzIter b' (Work.Spaces.DthIter a'
      (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) p.1 p.2
    = Work.Spaces.DzIter b'
      (Work.Spaces.DzIter b (Work.Spaces.DthIter a' (Work.Spaces.DthIter a f))) p.1 p.2 at h3
  change Work.Spaces.DzIter b'
        (Work.Spaces.DthIter a' (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) p.1 p.2
      = Work.Spaces.DzIter (b' + b) (Work.Spaces.DthIter (a' + a) f) p.1 p.2
  rw [h3, Work.Spaces.DthIter_add_right a' a f,
    (Work.Spaces.DzIter_add_right b' b (Work.Spaces.DthIter (a' + a) f)).symm]

/-- The shift identity `D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f` on the open quadrant, obtained
from `mixed_comp` with the outer slot `(a',b') = (1,0)`; it is the form in which the recursion
`HkIPStep` shifts the slot. -/
theorem Dth_mixed_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) f)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h := mixed_comp hf b a 0 1 hp
  change Work.Spaces.mixed 0 1 (Work.Spaces.mixed b a f) p.1 p.2
    = Work.Spaces.mixed (0 + b) (1 + a) f p.1 p.2 at h
  change Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
      = Work.Spaces.mixed b (a + 1) f p.1 p.2
  rw [show Work.Spaces.Dth (Work.Spaces.mixed b a f)
      = Work.Spaces.mixed 0 1 (Work.Spaces.mixed b a f) from rfl, h,
    Nat.zero_add, Nat.add_comm 1 a]

/-! ## Slots of a profile vanishing off the open quadrant

The `Integrable`-certificates of the slot transfer are statements about the *whole* plane, while
the `ℋ^k`-membership of the paper only constrains the quadrant.  The representatives on which the
slot transfer is applied therefore have to vanish off the open quadrant — and so must all their
mixed slots, which is the content of this section.

The proof is a locality argument.  Away from the two coordinate axes the profile vanishes on a
neighbourhood of the point, so every derivative vanishes there.  On the axes two reductions
suffice: `D_z` carries the factor `z` and `D_θ` the factor `sin(2θ)`, and at a point of the
boundary of the quadrant one of the two factors vanishes, while for the other factor the relevant
slice is identically zero. -/

/-- **`D_θ` of a profile vanishing off the open quadrant vanishes off it.**  On `θ = 0` and
`θ = π/2` the factor `sin(2θ)` vanishes.  Otherwise, if `z ≤ 0` the whole angular slice is zero,
while for `z > 0` the point lies strictly outside `(0, π/2)` and the slice is zero on a
neighbourhood. -/
theorem Dth_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0)
    {z θ : ℝ} (hzθ : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) :
    Work.Spaces.Dth G z θ = 0 := by
  show Real.sin (2 * θ) * Work.Spaces.pth G z θ = 0
  rcases eq_or_ne θ 0 with h0 | h0
  · rw [h0]; simp
  rcases eq_or_ne θ (π / 2) with h2 | h2
  · rw [h2, show 2 * (π / 2) = π from by ring, Real.sin_pi]; ring
  have hslice : ∀ᶠ θ' in 𝓝 θ, G z θ' = 0 := by
    rcases lt_trichotomy z 0 with hz | hz | hz
    · exact Filter.Eventually.of_forall fun θ' => hG z θ' (by rintro ⟨h1, -⟩; linarith)
    · subst hz
      exact Filter.Eventually.of_forall fun θ' => hG 0 θ' (by rintro ⟨h1, -⟩; exact lt_irrefl 0 h1)
    · have hth : θ < 0 ∨ π / 2 < θ := by
        by_contra h
        push_neg at h
        exact hzθ ⟨hz, lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne h.2 h2⟩
      rcases hth with h | h
      · filter_upwards [Iio_mem_nhds h] with θ' hθ'
        rw [Set.mem_Iio] at hθ'
        exact hG z θ' (by rintro ⟨-, h2', -⟩; linarith)
      · filter_upwards [Ioi_mem_nhds h] with θ' hθ'
        rw [Set.mem_Ioi] at hθ'
        exact hG z θ' (by rintro ⟨-, -, h3'⟩; linarith)
  have hslice' : (fun θ' => G z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := hslice
  rw [Work.Spaces.pth, hslice'.deriv_eq]
  simp

/-- **`D_z` of a profile vanishing off the open quadrant vanishes off it.**  At `z = 0` the factor
`z` vanishes; for `z < 0` the radial slice is zero on a neighbourhood; for `z > 0` the angular
coordinate lies outside `(0, π/2)` and the radial slice is identically zero. -/
theorem Dz_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0)
    {z θ : ℝ} (hzθ : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) :
    Work.Spaces.Dz G z θ = 0 := by
  show z * Work.Spaces.pz G z θ = 0
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0]; ring
  have hslice : ∀ᶠ z' in 𝓝 z, G z' θ = 0 := by
    rcases lt_or_gt_of_ne hz0 with hz | hz
    · filter_upwards [Iio_mem_nhds hz] with z' hz'
      rw [Set.mem_Iio] at hz'
      exact hG z' θ (by rintro ⟨h1, -⟩; linarith)
    · have hth : θ ≤ 0 ∨ π / 2 ≤ θ := by
        by_contra h
        push_neg at h
        exact hzθ ⟨hz, h.1, h.2⟩
      rcases hth with h | h
      · exact Filter.Eventually.of_forall fun z' =>
          hG z' θ (by rintro ⟨-, h2', -⟩; linarith)
      · exact Filter.Eventually.of_forall fun z' =>
          hG z' θ (by rintro ⟨-, -, h3'⟩; linarith)
  have hslice' : (fun z' => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := hslice
  rw [Work.Spaces.pz, hslice'.deriv_eq]
  simp

/-- **Every mixed slot of a profile vanishing off the open quadrant vanishes off it.** -/
theorem mixed_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0) :
    ∀ (b a : ℕ) (z θ : ℝ), ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) →
      Work.Spaces.mixed b a G z θ = 0 := by
  have hDth : ∀ a : ℕ, ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) →
      Work.Spaces.DthIter a G z θ = 0 := by
    intro a
    induction a with
    | zero => exact hG
    | succ a ih => exact fun z θ h => Dth_eq_zero_of_zero_off ih h
  intro b
  induction b with
  | zero => exact fun a z θ h => hDth a z θ h
  | succ b ih =>
      intro a z θ h
      exact Dz_eq_zero_of_zero_off (G := Work.Spaces.DzIter b (Work.Spaces.DthIter a G))
        (fun z' θ' h' => ih a z' θ' h') h

/-- `cut u` vanishes off the open quadrant. -/
theorem cut_zero_off (u : Fn) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → cut u z θ = 0 :=
  fun z θ h => cut_eq_zero_of_not_mem h

/-- **`J_ε f` vanishes off the open quadrant** (it is defined to be `0` there). -/
theorem Jeps_zero_off (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → Work.FTS.StrongEps.Jeps ρ ε f z θ = 0 := by
  intro z θ h
  rw [Work.FTS.StrongEps.Jeps]
  exact ite_eq_right (by intro hc; exact h ⟨hc.1, hc.2.1, hc.2.2⟩)

/-- The slot transfer is applied to the representative `cut A₀`, which agrees with `A₀` on the
open quadrant; consequently every pairing written with `cut A₀` equals the one written with
`A₀` (`wip` only sees the open quadrant). -/
theorem mixed_cut_eqOn_Q0 (u : Fn) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (cut (u : Fn))))
      (Function.uncurry (Work.Spaces.mixed b a (u : Fn))) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.TransportS.DthIter_congrOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 (cut_eqOn_Q0 u) a
  exact Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h b

/-! ## Congruence of `J_ε` on the open quadrant -/

/-- `J_ε` only depends on its argument through the values on the *open* quadrant: it samples the
argument at points of the quadrant and vanishes outside it. -/
theorem Jeps_congr_Q0 {X X' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = X' z θ)
    (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Work.FTS.StrongEps.Jeps ρ ε X = Work.FTS.StrongEps.Jeps ρ ε X' := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  · rw [Work.FTS.StrongEps.Jeps, if_pos hc, Work.FTS.StrongEps.Jeps, if_pos hc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have hz : 0 < z * Real.exp (-p.1) := mul_pos hc.1 (Real.exp_pos _)
    have hth : Real.arctan (Real.tan θ * Real.exp (-p.2)) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨Real.arctan_pos.mpr (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hc.2.1 hc.2.2)
          (Real.exp_pos _)),
        Real.arctan_lt_pi_div_two _⟩
    exact congrArg (fun c : ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) * c)
      (h _ _ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hth.1, hth.2⟩))
  · rw [Work.FTS.StrongEps.Jeps, if_neg hc, Work.FTS.StrongEps.Jeps, if_neg hc]

/-- `J_ε (cut u) = J_ε u`. -/
theorem Jeps_cut (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (u : Fn) :
    Work.FTS.StrongEps.Jeps ρ ε (cut u) = Work.FTS.StrongEps.Jeps ρ ε u :=
  Jeps_congr_Q0 (fun z θ h => cut_eqOn_Q0 u h) ρ ε

/-! ## A.e. strong measurability of profiles vanishing off the open quadrant -/

/-- A function continuous on the open quadrant and vanishing outside it is a.e. strongly
measurable (it is the indicator of the open quadrant times a function continuous there). -/
theorem aestronglyMeasurable_of_zero_off {F : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn F Work.FTS.EllipticEst.Q0)
    (hzero : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0) :
    AEStronglyMeasurable F volume := by
  have hs : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have h1 : F = Set.indicator Work.FTS.EllipticEst.Q0 F := by
    funext p
    by_cases hp : p ∈ Work.FTS.EllipticEst.Q0
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, hzero p hp]
  rw [h1]
  exact (aestronglyMeasurable_indicator_iff hs).mpr (hcont.aestronglyMeasurable hs)

/-! ## Integrability of the cross term -/

/-- **The weighted cross term is integrable** when the two weighted squares are: pointwise AM–GM
on the open quadrant, and both profiles vanish outside it. -/
theorem integrable_cross_of_zero_off {ρ X Y : ℝ → ℝ → ℝ}
    (hX0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → X z θ = 0)
    (hY0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → Y z θ = 0)
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    (hρ0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hX : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (X z θ) ^ 2)) volume)
    (hY : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (Y z θ) ^ 2)) volume) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * X z θ * Y z θ)) volume := by
  refine Integrable.mono' (hX.add hY) ?_ ?_
  · refine aestronglyMeasurable_of_zero_off ((hρc.mul hXc).mul hYc) ?_
    intro p hp
    show ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 = 0
    rw [hX0 p.1 p.2 hp, hY0 p.1 p.2 hp]
    ring
  · filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Pi.add_apply, Function.uncurry_apply_pair]
    by_cases hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0
    · obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hρz : 0 ≤ ρ z θ := hρ0 z (le_of_lt hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρz]
      have h2 : 2 * |X z θ| * |Y z θ| ≤ (X z θ) ^ 2 + (Y z θ) ^ 2 := by
        have h := sq_nonneg (|X z θ| - |Y z θ|)
        rw [sub_sq, sq_abs, sq_abs] at h
        nlinarith [h]
      nlinarith [h2, hρz, abs_nonneg (X z θ), abs_nonneg (Y z θ)]
    · have hP : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) := fun hc => hp (Work.FTS.EllipticEst.mem_Q0.mpr hc)
      rw [hX0 z θ hP, hY0 z θ hP]
      simp



/-- **The pointwise form of the `D_θ`-shift of a slot**: on the open quadrant
`D_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1} f`.  This is the form in which the recursion of the transfer
defect consumes the shift.  It is proved directly — rather than through the
`Function.uncurry`-form `mixed_comp` — because the elaborator does not manage the definitional
comparison of the two forms for `D_θ`-headed terms (it unfolds `deriv`). -/
theorem Dth_mixed_apply {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter a f) := hf.DthIter a
  have key : ∀ b : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)) z θ
        = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) z θ := by
    intro b
    induction b with
    | zero => intro z θ hp; rfl
    | succ b ih =>
        intro z θ hp
        have h1 : Work.Spaces.Dth
              (Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) z θ
            = Work.Spaces.Dz
              (Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) z θ :=
          Work.FTS.TransportS.Dth_Dz_apply_of (hX.DzIter b) hp.1 ⟨hp.2.1, hp.2.2⟩
        have h2 : Work.Spaces.Dz
              (Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) z θ
            = Work.Spaces.Dz
              (Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f))) z θ := by
          have hpc : Work.Spaces.pz
                (Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) z θ
              = Work.Spaces.pz
                (Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f))) z θ :=
            Work.Spaces.pz_congr_of_isOpen
              (f := Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)))
              (f' := Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)))
              Work.FTS.EllipticEst.isOpen_Q0 (by intro p hp'; exact ih p.1 p.2 hp') hp
          show z * Work.Spaces.pz
                (Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) z θ
              = z * Work.Spaces.pz
                (Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f))) z θ
          rw [hpc]
        show Work.Spaces.Dth (Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f)) z θ
            = Work.Spaces.DzIter (b + 1)
                (Work.Spaces.Dth (Work.Spaces.DthIter a f)) z θ
        rw [show Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f)
              = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)) from rfl,
          show Work.Spaces.DzIter (b + 1) (Work.Spaces.Dth (Work.Spaces.DthIter a f))
              = Work.Spaces.Dz
                (Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f))) from rfl,
          h1, h2]
  intro z θ hp
  have hkey := key b z θ hp
  show Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ
  rw [show Work.Spaces.mixed b a f
        = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl,
      show Work.Spaces.mixed b (a + 1) f
        = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) from rfl]
  exact hkey

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
