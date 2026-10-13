/-
Copyright: work module for the Elgindi finite-time singularity project.

# The repaired slot domination of `IP4`

`Submission/Work/FTS/TransportS/NOTES_ip4SlotDom.md` shows that the *original* statement of
`ip4SlotDom` is FALSE: the unfolding of the coercive inner product

`IP4 α = HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))`

contains the `w² sin(2θ)^{-η}`-weighted pairing at **every** slot `(a,b)` with `a + b ≤ 4`
(the `10`- and `10^10`-terms of `H1IP`, each of them carrying that weight), while the original
`leafSum` attached that weight only to the slots with `a = 0`.

With the repaired leaf sum (`Slots.lean`: the weights `w² sin(2θ)^{-η}` and `w²` at every slot
`a + b ≤ 4`, and `w² sin(2θ)^{-γ}` at every such slot with `a ≥ 1` — the guard matching
`IsLeafW`) the domination becomes a purely *combinatorial* statement.  Indeed the recursion
unfolds over the 15 words in `D_θ, D_z` of length `≤ 3`, and each word applied to `u` is the
slot derivative `D_z^bD_θ^a u` where `a`, `b` count the `D_θ`'s and `D_z`'s of the word: the two
operators **commute** on the open quadrant, since `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` carry
multipliers depending on the *other* variable (Clairaut).  This is the only analytic input, it
is exactly what the hypothesis `SmoothOpen` supplies, and it is why the two slot integrands
agree only a.e. on `Iz × Iθ` (the mismatch set is `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`).

The proof below is organised as

* `ae_restrict_Iz_of_pos`, `setIntegral2_congr_Q0` — equality on the open quadrant implies
  equality of the double integrals over `Iz = [0,∞)` and `Iθ = [0,π/2]` (the complement of `Q0`
  in `Iz × Iθ` is null);
* `pz_congrOn`, `Dz_congrOn`, `Dth_congrOn`, `DzIter_congrOn`, `DthIter_congrOn` — the operators
  respect pointwise equality on an open set;
* `DzIter_comp`, `DthIter_comp` — associativity of the iterates (pure bookkeeping);
* `Dth_Dz_apply_of`, `Dth_DzIter_eqOn`, `DthIter_DzIter_eqOn` — `D_θ` commutes with the iterates
  of `D_z` on the open quadrant (Clairaut);
* `mixed_dth`, `mixed_dz_eqOn`, `slotPairing_dth`, `slotPairing_dz` — the shifts of the slot
  pairings along `D_θ` and `D_z` (`D_θ` is again pure bookkeeping, `D_z` uses the commutation);
* `SlotSum_mono`, `slotPairing_le_SlotSum`, `leafSum_eq_SlotSum_four`, `H1IP_eq_slot_sum`,
  `H1IP_le_SlotSum_one` — the finite-sum API of the slot sums;
* `SlotTerm_dth_le`, `SlotTerm_dz_le`, `SlotSum_dth_le`, `SlotSum_dz_le` — the shift
  inequalities for the slot sums;
* `ip4_unfold_bound` — the induction `|IPn α n u v| ≤ 3^n · 10^22 · SlotSum α (n+1) u v`;
* `ip4SlotDomFixed` — the theorem.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.IPFixDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Equality on the open quadrant gives equality of the integrals -/

/-- A.e. statement for the restricted measure on `Iz = [0,∞)`: it suffices to prove the
statement on the open half line, where the radial weight `w` does not vanish. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- **Two double integrals agree as soon as their integrands agree on the open quadrant**: the
complement of `Q0` in `Iz × Iθ` is `({0} × Iθ) ∪ (Ioi 0 × ({0} ∪ {π/2}))`, a null set. -/
theorem setIntegral2_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G z θ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_Iz_of_pos (p := fun z => 0 < z) (fun z hz => hz)] with z hz
  refine integral_congr_ae ?_
  refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
  exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩)

/-! ## The operators respect equality on an open set -/

theorem pz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pz g p.1 p.2 = Work.Spaces.pz g' p.1 p.2 :=
  Work.Spaces.pz_congr_of_isOpen hV h hp

theorem Dz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro p hp
  show p.1 * Work.Spaces.pz g p.1 p.2 = p.1 * Work.Spaces.pz g' p.1 p.2
  rw [pz_congrOn hV h hp]

theorem Dth_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hslice.deriv_eq

theorem DzIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b g))
      (Function.uncurry (Work.Spaces.DzIter b g')) V := by
  induction b with
  | zero => exact h
  | succ b ih => simpa only [Work.Spaces.DzIter_succ] using Dz_congrOn hV ih

theorem DthIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congrOn hV ih

/-! ## Associativity of the iterates -/

/-- `D_z^b(D_z f) = D_z^{b+1} f` (pure bookkeeping, no smoothness). -/
theorem DzIter_comp (b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f := by
  induction b with
  | zero => rfl
  | succ b ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dz f))
          = Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter b f))
      rw [ih]
      rfl

/-- `D_θ^a(D_θ f) = D_θ^{a+1} f` (pure bookkeeping, no smoothness). -/
theorem DthIter_comp (a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter a (Work.Spaces.Dth f) = Work.Spaces.DthIter (a + 1) f := by
  induction a with
  | zero => rfl
  | succ a ih =>
      show Work.Spaces.Dth (Work.Spaces.DthIter a (Work.Spaces.Dth f))
          = Work.Spaces.Dth (Work.Spaces.Dth (Work.Spaces.DthIter a f))
      rw [ih]
      rfl

/-! ## `D_θ` commutes with the iterates of `D_z` on the open quadrant -/

/-- `D_θ(D_z X) = D_z(D_θ X)` at a point of the open quadrant where `X` is `C²` (Clairaut,
using `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z`). -/
theorem Dth_Dz_apply_of {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.Dz X) z θ = Work.Spaces.Dz (Work.Spaces.Dth X) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry X) (z, θ) :=
    (hX.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz X) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz X) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz X z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz X z θ') θ
    rw [deriv_const_mul_field]
  have h2 : Work.Spaces.pz (Work.Spaces.Dth X) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth X) z θ := by
    show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth X z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Work.Spaces.pth X z' θ) z
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz X) z θ = Work.Spaces.pz (Work.Spaces.pth X) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dz X) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth X) z θ
  rw [h1, h2, h3]
  ring

/-- `D_θ` can be moved across any iterate of `D_z` on the open quadrant. -/
theorem Dth_DzIter_eqOn {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth X))) Work.FTS.EllipticEst.Q0 := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hb : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter b X) := hX.DzIter b
      have h1 : Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b X)) p.1 p.2 :=
        Dth_Dz_apply_of hb hz ⟨hθ0, hθ1⟩
      have h2 : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth X)) p.1 p.2 :=
        Dz_congrOn Work.FTS.EllipticEst.isOpen_Q0 ih hp
      show Work.Spaces.Dth (Work.Spaces.DzIter (b + 1) X) p.1 p.2
          = Work.Spaces.DzIter (b + 1) (Work.Spaces.Dth X) p.1 p.2
      rw [show Work.Spaces.DzIter (b + 1) X = Work.Spaces.Dz (Work.Spaces.DzIter b X) from rfl,
        show Work.Spaces.DzIter (b + 1) (Work.Spaces.Dth X)
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth X)) from rfl]
      exact h1.trans h2

/-- The iterates of `D_θ` can be moved across any iterate of `D_z` on the open quadrant. -/
theorem DthIter_DzIter_eqOn {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      intro p hp
      have h1 : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) p.1 p.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) p.1 p.2 :=
        Dth_congrOn Work.FTS.EllipticEst.isOpen_Q0 ih hp
      have h2 : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i X)) p.1 p.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i X)) p.1 p.2 :=
        Dth_DzIter_eqOn (hX.DthIter i) b hp
      show Work.Spaces.DthIter (i + 1) (Work.Spaces.DzIter b X) p.1 p.2
          = Work.Spaces.DzIter b (Work.Spaces.DthIter (i + 1) X) p.1 p.2
      rw [show Work.Spaces.DthIter (i + 1) (Work.Spaces.DzIter b X)
            = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b X)) from rfl,
        show Work.Spaces.DthIter (i + 1) X = Work.Spaces.Dth (Work.Spaces.DthIter i X) from rfl]
      exact h1.trans h2

/-! ## The slot pairings shift along the operators -/

/-- `D_θ` shifts the slot index by one in the `θ`-direction:
`D_z^bD_θ^a(D_θ f) = D_z^bD_θ^{a+1} f` (no smoothness needed — pure associativity of the
iterates). -/
theorem mixed_dth (b a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (Work.Spaces.Dth f) = Work.Spaces.mixed b (a + 1) f := by
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dth f))
      = Work.Spaces.DzIter b (Work.Spaces.DthIter (a + 1) f)
  rw [DthIter_comp]

/-- `D_z` shifts the slot index by one in the `z`-direction, on the open quadrant:
`D_z^bD_θ^a(D_z f) = D_z^{b+1}D_θ^a f` (this is where the commutation of `D_θ` with `D_z^b` is
used). -/
theorem mixed_dz_eqOn {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h2 := DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0
    (DthIter_DzIter_eqOn hu 1 a) b hp
  have h2' : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.DzIter 1 u)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.DzIter 1 (Work.Spaces.DthIter a u)) p.1 p.2 := h2
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.DzIter 1 u)) p.1 p.2
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) p.1 p.2
  rw [h2']
  rw [show Work.Spaces.DzIter 1 (Work.Spaces.DthIter a u)
        = Work.Spaces.Dz (Work.Spaces.DthIter a u) from rfl, DzIter_comp]

/-- **The slot pairing shifts along `D_θ`.** -/
theorem slotPairing_dth (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : Fn) :
    slotPairing ρ a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      = slotPairing ρ (a + 1) b u v := by
  unfold slotPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  rw [mixed_dth b a u, mixed_dth b a v]

/-- **The slot pairing shifts along `D_z`** (on the open quadrant). -/
theorem slotPairing_dz (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = slotPairing ρ a (b + 1) u v := by
  unfold slotPairing
  refine setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz u) p.1 p.2
      = Work.Spaces.mixed (b + 1) a u p.1 p.2 := mixed_dz_eqOn hu b a hp
  have h2 : Work.Spaces.mixed b a (Work.Spaces.Dz v) p.1 p.2
      = Work.Spaces.mixed (b + 1) a v p.1 p.2 := mixed_dz_eqOn hv b a hp
  rw [h1, h2]

/-! ## The finite-sum API of the slot sums -/

/-- The slot sum is monotone in the level. -/
theorem SlotSum_mono {α : ℝ} {u v : Fn} {n m : ℕ} (h : n ≤ m) :
    SlotSum α n u v ≤ SlotSum α m u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  have hinner : ∀ a : ℕ, (∑ b ∈ Finset.range (n + 1 - a), SlotTerm α a b u v)
      ≤ ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v := by
    intro a
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_)
      (fun b _ _ => SlotTerm_nonneg α a b u v)
    simp only [Finset.mem_range] at hb ⊢
    omega
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a), SlotTerm α a b u v)
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v :=
        Finset.sum_le_sum (fun a _ => hinner a)
    _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a), SlotTerm α a b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

/-- Every single slot pairing with a leaf weight of the slot `(a,b)` is dominated by the slot
sum of any level `n ≥ a + b`. -/
theorem slotPairing_le_SlotSum {α : ℝ} {a b n : ℕ} {ρ : ℝ → ℝ → ℝ} (u v : Fn)
    (hρ : IsLeafW α a ρ) (hab : a + b ≤ n) :
    |slotPairing ρ a b u v| ≤ SlotSum α n u v := by
  have hT : |slotPairing ρ a b u v| ≤ SlotTerm α a b u v := by
    have h3 : (0 : ℝ) ≤ (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0) := by
      by_cases h : 1 ≤ a
      · rw [if_pos h]; exact abs_nonneg _
      · rw [if_neg h]
    rcases hρ with rfl | rfl | ⟨ha, rfl⟩
    · unfold SlotTerm
      linarith [abs_nonneg (slotPairing leafOne a b u v)]
    · unfold SlotTerm
      linarith [abs_nonneg (slotPairing leafEta a b u v)]
    · unfold SlotTerm
      rw [if_pos ha]
      linarith [abs_nonneg (slotPairing leafEta a b u v),
        abs_nonneg (slotPairing leafOne a b u v)]
  rw [SlotSum_eq_sum_SlotTerm]
  calc |slotPairing ρ a b u v| ≤ SlotTerm α a b u v := hT
    _ ≤ ∑ b' ∈ Finset.range (n + 1 - a), SlotTerm α a b' u v :=
        Finset.single_le_sum (fun b' _ => SlotTerm_nonneg α a b' u v)
          (show b ∈ Finset.range (n + 1 - a) from Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (n + 1), ∑ b' ∈ Finset.range (n + 1 - a'),
          SlotTerm α a' b' u v :=
        Finset.single_le_sum
          (f := fun a' : ℕ => ∑ b' ∈ Finset.range (n + 1 - a'), SlotTerm α a' b' u v)
          (fun a' _ => Finset.sum_nonneg (fun b' _ => SlotTerm_nonneg α a' b' u v))
          (show a ∈ Finset.range (n + 1) from Finset.mem_range.mpr (by omega))

/-- `∑_{b < n+1} (if a + b ≤ n then f b else 0) = ∑_{b < n+1-a} f b`. -/
theorem sum_range_ite_eq (n a : ℕ) (f : ℕ → ℝ) (ha : a ≤ n) :
    (∑ b ∈ Finset.range (n + 1), (if a + b ≤ n then f b else 0))
      = ∑ b ∈ Finset.range (n + 1 - a), f b := by
  have hsub : Finset.range (n + 1 - a) ⊆ Finset.range (n + 1) := by
    intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  have hzero : ∀ b ∈ Finset.range (n + 1), b ∉ Finset.range (n + 1 - a) →
      (if a + b ≤ n then f b else 0) = 0 := by
    intro b hb hnb
    rw [if_neg]
    intro hle
    exact hnb (Finset.mem_range.mpr (by omega))
  have h1 : (∑ b ∈ Finset.range (n + 1 - a), f b)
      = ∑ b ∈ Finset.range (n + 1 - a), (if a + b ≤ n then f b else 0) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [if_pos]
    simp only [Finset.mem_range] at hb
    omega
  have h2 : (∑ b ∈ Finset.range (n + 1 - a), (if a + b ≤ n then f b else 0))
      = ∑ b ∈ Finset.range (n + 1), (if a + b ≤ n then f b else 0) :=
    Finset.sum_subset hsub hzero
  exact h2.symm.trans h1.symm

/-- The repaired leaf sum is the slot sum of level `4`. -/
theorem leafSum_eq_SlotSum_four (α : ℝ) (u v : Fn) : leafSum α u v = SlotSum α 4 u v := by
  rw [SlotSum_eq_sum_SlotTerm]
  unfold leafSum
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have ha4 : a ≤ 4 := by
    have := Finset.mem_range.mp ha
    omega
  exact sum_range_ite_eq 4 a (fun b => SlotTerm α a b u v) ha4

/-- The `wip` pairing with the mixed derivative of a slot is the slot pairing. -/
theorem wip_eq_slotPairing (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (X Y : Fn) :
    Work.Coercivity.wip ρ (Work.Spaces.mixed b a X) (Work.Spaces.mixed b a Y)
      = slotPairing ρ a b X Y := by
  unfold Work.Coercivity.wip slotPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-- `H1IP` is the sum of its four slot pairings. -/
theorem H1IP_eq_slot_sum (α : ℝ) (u v : Fn) :
    Work.Coercivity.H1IP α u v
      = 10 * slotPairing leafEta 0 1 u v + (10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v
        + (10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v
        + (10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v := by
  have h1 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Work.Spaces.Dz u) (Work.Spaces.Dz v) = slotPairing leafEta 0 1 u v :=
    wip_eq_slotPairing leafEta 0 1 u v
  have h2 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        u v = slotPairing leafEta 0 0 u v :=
    wip_eq_slotPairing leafEta 0 0 u v
  have h3 : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) u v
      = slotPairing leafOne 0 0 u v :=
    wip_eq_slotPairing leafOne 0 0 u v
  have h4 : Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth u) (Work.Spaces.Dth v) = slotPairing (leafGam α) 1 0 u v :=
    wip_eq_slotPairing (leafGam α) 1 0 u v
  unfold Work.Coercivity.H1IP
  rw [h1, h2, h3, h4]

/-- Absolute value of a four-term sum. -/
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  rw [show a + b + c + d = (a + b) + (c + d) from by ring]
  have h1 := abs_add_le (a + b) (c + d)
  have h2 := abs_add_le a b
  have h3 := abs_add_le c d
  linarith

/-- `|H1IP α u v|` is bounded by `10^22` times the slot sum of level `1`. -/
theorem H1IP_le_SlotSum_one (α : ℝ) (u v : Fn) :
    |Work.Coercivity.H1IP α u v| ≤ (10 : ℝ) ^ 22 * SlotSum α 1 u v := by
  rw [H1IP_eq_slot_sum]
  have hS := SlotSum_nonneg α 1 u v
  have hA : |slotPairing leafEta 0 1 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inl rfl) (show 0 + 1 ≤ 1 by norm_num)
  have hB : |slotPairing leafEta 0 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inl rfl) (show 0 + 0 ≤ 1 by norm_num)
  have hC : |slotPairing leafOne 0 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inr (Or.inl rfl)) (show 0 + 0 ≤ 1 by norm_num)
  have hD : |slotPairing (leafGam α) 1 0 u v| ≤ SlotSum α 1 u v :=
    slotPairing_le_SlotSum u v (Or.inr (Or.inr ⟨le_refl 1, rfl⟩))
      (show 1 + 0 ≤ 1 by norm_num)
  have h1 : |10 * slotPairing leafEta 0 1 u v| ≤ 10 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h2 : |(10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v|
      ≤ (10 : ℝ) ^ 10 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 10)]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have h3 : |(10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v|
      ≤ (10 : ℝ) ^ 17 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 17)]
    exact mul_le_mul_of_nonneg_left hC (by norm_num)
  have h4 : |(10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v|
      ≤ (10 : ℝ) ^ 21 * SlotSum α 1 u v := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 21)]
    exact mul_le_mul_of_nonneg_left hD (by norm_num)
  have hsplit := abs_add_four_le (10 * slotPairing leafEta 0 1 u v)
    ((10 : ℝ) ^ 10 * slotPairing leafEta 0 0 u v)
    ((10 : ℝ) ^ 17 * slotPairing leafOne 0 0 u v)
    ((10 : ℝ) ^ 21 * slotPairing (leafGam α) 1 0 u v)
  have hcoef : (10 : ℝ) + (10 : ℝ) ^ 10 + (10 : ℝ) ^ 17 + (10 : ℝ) ^ 21 ≤ (10 : ℝ) ^ 22 := by
    norm_num
  nlinarith [hsplit, h1, h2, h3, h4, hS, hcoef]

/-! ## The shift inequalities for the slot sums -/

/-- Termwise, `D_θ` moves a slot term to the next slot. -/
theorem SlotTerm_dth_le (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotTerm α (a + 1) b u v := by
  have heta := slotPairing_dth leafEta a b u v
  have hone := slotPairing_dth leafOne a b u v
  have hgam := slotPairing_dth (leafGam α) a b u v
  have hthird : (if 1 ≤ a then |slotPairing (leafGam α) (a + 1) b u v| else 0)
      ≤ (if 1 ≤ a + 1 then |slotPairing (leafGam α) (a + 1) b u v| else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold SlotTerm
  rw [heta, hone, hgam]
  linarith [hthird]

/-- Termwise, `D_z` moves a slot term to the next slot. -/
theorem SlotTerm_dz_le (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotTerm α a (b + 1) u v := by
  unfold SlotTerm
  rw [slotPairing_dz leafEta a b hu hv, slotPairing_dz leafOne a b hu hv,
    slotPairing_dz (leafGam α) a b hu hv]

/-- Shifting the slot sum along `D_θ` raises the level by one. -/
theorem SlotSum_dth_le (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dth_le α a b hu hv))
    _ = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - (a + 1)),
          SlotTerm α (a + 1) b u v := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [show n + 2 - (a + 1) = n + 1 - a from Nat.succ_sub_succ (n := n + 1) (m := a)]
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right
          (show (0 : ℝ) ≤ ∑ b ∈ Finset.range (n + 2 - 0), SlotTerm α 0 b u v from
            Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α 0 b u v))

/-- Shifting the slot sum along `D_z` raises the level by one. -/
theorem SlotSum_dz_le (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dz_le α a b hu hv))
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - a),
          SlotTerm α a b u v := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        by_cases ha : a ≤ n + 1
        · rw [show n + 2 - a = (n + 1 - a) + 1 from by omega]
          conv_rhs => rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right
            (show (0 : ℝ) ≤ SlotTerm α a 0 u v from SlotTerm_nonneg α a 0 u v)
        · rw [show n + 1 - a = 0 from by omega]
          simp only [Finset.range_zero, Finset.sum_empty]
          exact Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v)
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

/-! ## The unfolding of the recursion -/

/-- **The induction of the unfolding.**  For every `n`, the `n`-fold iterate of the coercive
recursion is dominated by `3^n · 10^22` times the slot sum of level `n + 1`. -/
theorem ip4_unfold_bound :
    ∀ (n : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      |IPn α n u v| ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v := by
  intro n
  induction n with
  | zero =>
      intro α u v hu hv
      rw [show IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using H1IP_le_SlotSum_one α u v
  | succ n ih =>
      intro α u v hu hv
      have hIHu := ih α u v hu hv
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hu.Dth hv.Dth
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hu.Dz hv.Dz
      have hd := SlotSum_dth_le α (n + 1) hu hv
      have hz := SlotSum_dz_le α (n + 1) hu hv
      have hmono := SlotSum_mono (α := α) (u := u) (v := v) (n := n + 1) (m := n + 2) (by omega)
      have hsum : SlotSum α (n + 1) u v + SlotSum α (n + 1) (Work.Spaces.Dth u)
            (Work.Spaces.Dth v) + SlotSum α (n + 1) (Work.Spaces.Dz u)
            (Work.Spaces.Dz v) ≤ 3 * SlotSum α (n + 2) u v := by
        linarith
      have hstep : IPn α (n + 1) u v
          = IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show IPn α (n + 1) = Work.Coercivity.HkIPStep 1 1 (IPn α n) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |IPn α n u v| + |IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le (IPn α n u v + IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (IPn α n u v) (IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |IPn α n u v| + |IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v)
          = (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (SlotSum α (n + 1) u v
              + SlotSum α (n + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (n + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (SlotSum α (n + 1) u v
              + SlotSum α (n + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (n + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22 * SlotSum α (n + 2) u v := by
        have h3 : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * (3 * SlotSum α (n + 2) u v)
            = (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22 * SlotSum α (n + 2) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]

/-- **The slot domination of the concrete `IP4`** with the repaired leaf sum: there are
`K, α₂ > 0` such that for every `α ∈ (0, α₂]` and all `u, v` smooth on the open quadrant,
`|IP4 α u v| ≤ K · leafSum α u v`.

This is the algebraic input of the `N3 → N2` seam: the per-slot transport bounds
`T2Slot`/`T3Slot` are summed over the leaves of the unfolding of `IP4` (`IP4_unfold`). -/
theorem ip4SlotDomFixed : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ Work.FTS.TransportS.SlotDomIP α₂ K (fun α => Work.FTS.CoercivityStep.IP4 α) := by
  refine ⟨(3 : ℝ) ^ 3 * (10 : ℝ) ^ 22, 1, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
  · intro α hα u v hu hv
    have hb := ip4_unfold_bound 3 α u v hu hv
    have hb' : |IPn α 3 u v| ≤ (3 : ℝ) ^ 3 * (10 : ℝ) ^ 22 * leafSum α u v := by
      rw [leafSum_eq_SlotSum_four]
      exact hb
    show |Work.FTS.CoercivityStep.IP4 α u v|
      ≤ (3 : ℝ) ^ 3 * (10 : ℝ) ^ 22 * leafSum α u v
    rw [← IPn_three_eq_IP4 α]
    exact hb'

end Work.FTS.TransportS
