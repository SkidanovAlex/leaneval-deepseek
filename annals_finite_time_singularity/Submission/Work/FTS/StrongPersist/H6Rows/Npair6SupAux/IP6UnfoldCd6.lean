/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IP6UnfoldCd6` — the level-six slot domination of `IP6 1…1` at smoothness order `C⁶`

`Work.FTS.TransportS.ip4_unfold_bound` bounds the `n`-fold iterate `IPn α n` of the paper's
coercive recursion by `3^n · 10^22 · SlotSum α (n+1) u v`, but only for profiles that are
`C^∞` on the open quadrant (`SmoothOpen`).  The present file proves the finite-order version
needed by the level-six rows:

  `|IP6 1 … 1 α u v| ≤ 3^5 · 10^22 · SlotSum α 6 u v`   for `u, v` merely `C⁶` on the
  open quadrant.

Since `IP6 1 … 1 α = IPn α 5` definitionally, it suffices to redo the unfolding induction of
`TransportS/ip4SlotDomFixed.lean` at finite order.  The only analytic input of that induction
is the commutation of `D_θ` and `D_z` on the open quadrant (Clairaut), used exactly once per
level, to shift the slot sums:

  `SlotSum α n (D_z u) (D_z v) ≤ SlotSum α (n+1) u v`,

which is slotwise `mixed b a (D_z u) = mixed (b+1) a u` for the slots `a + b ≤ n`, i.e.
`C^{a+1}` of `u` — and `a ≤ n`, so `C^{n+1}` of `u` suffices.

**The bookkeeping.**  At level `m` (where the conclusion is a bound by
`3^m · 10^22 · SlotSum α (m+1)`) a node of the recursion tree carries the datum `w u`, where
`w` is a word of length `m - m_node` in `D_θ, D_z`; the only differentiability demanded at
that node is `w u ∈ C^{m_node + 1}`, i.e. `u ∈ C^{m+1}` throughout.  So the induction runs
with the *level-dependent* hypothesis `ContDiffOn ℝ (m+1)` — exactly one order below the
(also true, but weaker) statement with `m+2` used by the sibling
`N0pair6bWork/ip6_le_slotSum6_cd.lean`, whose extra order comes from quoting the shift
`SlotSum α n (D_z ·) ≤ SlotSum α (n+1) ·` with its coarse hypothesis `C^{n+2}` instead of the
sharp `C^{n+1}`.  At level `5` this is the difference between `C⁷` and `C⁶`, and `C⁶` is what
the target statement supplies.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.IPFixDefs
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.CoercivityFix.Transfer.HkIntegrand_Dz_le_succ_Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Cd6Unfold

open Work.FTS.TransportS

/-- **The `D_z`-shift of a slot pairing at finite order.**  Moving one `D_z` off a slot onto
the next slot costs the commutation `D_z^b D_θ^a (D_z u) = D_z^{b+1} D_θ^a u` on the open
quadrant, which is Clairaut up to order `a + 1`: `ContDiffOn ℝ (a+1)` of `u` is exactly the
hypothesis of the transfer chapter's `mixed_Dz_shift_Q0Sm`.  The two integrands then agree on
the quadrant, whose complement in `Iz × Iθ` is null. -/
theorem slotPairing_dz_fin {a b : ℕ} {u v : ℝ → ℝ → ℝ} (ρ : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = slotPairing ρ a (b + 1) u v := by
  have hXu := Work.FTS.CoercivityFix.Transfer.mixed_Dz_shift_Q0Sm (u := u) (N := a + 1)
    (hu : Work.FTS.CoercivityFix.Transfer.Q0Sm (a + 1) u) (le_refl (a + 1)) b
  have hXv := Work.FTS.CoercivityFix.Transfer.mixed_Dz_shift_Q0Sm (u := v) (N := a + 1)
    (hv : Work.FTS.CoercivityFix.Transfer.Q0Sm (a + 1) v) (le_refl (a + 1)) b
  unfold slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  rw [hXu p.1 p.2 hp, hXv p.1 p.2 hp]

/-- **The `D_z`-shift of a slot term at finite order.** -/
theorem slotTerm_dz_le_fin (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotTerm α a (b + 1) u v := by
  have h1 : |slotPairing leafEta a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      = |slotPairing leafEta a (b + 1) u v| := by
    rw [slotPairing_dz_fin (a := a) (b := b) leafEta hu hv]
  have h2 : |slotPairing leafOne a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      = |slotPairing leafOne a (b + 1) u v| := by
    rw [slotPairing_dz_fin (a := a) (b := b) leafOne hu hv]
  have h3 : (if 1 ≤ a then
        |slotPairing (leafGam α) a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)| else 0)
      = (if 1 ≤ a then |slotPairing (leafGam α) a (b + 1) u v| else 0) := by
    by_cases ha : 1 ≤ a
    · rw [if_pos ha, if_pos ha]
      rw [slotPairing_dz_fin (a := a) (b := b) (leafGam α) hu hv]
    · rw [if_neg ha, if_neg ha]
  unfold SlotTerm
  linarith [h1, h2, h3]

/-- **The `D_θ`-shift of a slot term** (pure bookkeeping of the iterates, no smoothness). -/
theorem slotTerm_dth_le_fin (α : ℝ) (a b : ℕ) (u v : ℝ → ℝ → ℝ) :
    SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotTerm α (a + 1) b u v := by
  have h1 : |slotPairing leafEta a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      = |slotPairing leafEta (a + 1) b u v| := by
    rw [slotPairing_dth leafEta a b u v]
  have h2 : |slotPairing leafOne a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      = |slotPairing leafOne (a + 1) b u v| := by
    rw [slotPairing_dth leafOne a b u v]
  have h3 : (if 1 ≤ a then
        |slotPairing (leafGam α) a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)| else 0)
      ≤ (if 1 ≤ a + 1 then |slotPairing (leafGam α) (a + 1) b u v| else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
      rw [slotPairing_dth (leafGam α) a b u v]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold SlotTerm
  linarith [h1, h2, h3]

/-- **The `D_θ`-shift of the slot sums** (pure bookkeeping). -/
theorem slotSum_dth_le_fin (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ) :
    SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => slotTerm_dth_le_fin α a b u v))
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

/-- **The `D_z`-shift of the slot sums, at the sharp finite order `C^{n+1}`.**  (The sibling
`N0pair6bWork.slotSum_Dz_le_fin` states the same with the coarser hypothesis `C^{n+2}`.) -/
theorem slotSum_dz_le_fin (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b _ =>
            slotTerm_dz_le_fin α a b
              (hu.of_le (m := (((a + 1 : ℕ)) : WithTop ℕ∞))
                (by exact_mod_cast (show a + 1 ≤ n + 1 from by
                  have := Finset.mem_range.mp ha; omega)))
              (hv.of_le (m := (((a + 1 : ℕ)) : WithTop ℕ∞))
                (by exact_mod_cast (show a + 1 ≤ n + 1 from by
                  have := Finset.mem_range.mp ha; omega)))))
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

/-- **The unfolding induction at finite order.**  For every level `m`, profiles that are
`C^{m+1}` on the open quadrant satisfy
`|IPn α m u v| ≤ 3^m · 10^22 · SlotSum α (m+1) u v`.

The two analytic inputs are `slotSum_dth_le_fin` (free) and `slotSum_dz_le_fin`, whose
hypothesis `C^{(m+1)+1}` is exactly the induction hypothesis at level `m + 1`; the children
`D_θ u`, `D_z u` are `C^{m+1}`, one order below, as supplied by `contDiffOn_Dth_nat` /
`contDiffOn_Dz_nat`. -/
theorem IPn_le_SlotSum_cd6 :
    ∀ (m : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
      ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
        Work.FTS.EllipticEst.Q0 →
      ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
        Work.FTS.EllipticEst.Q0 →
      |IPn α m u v| ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v := by
  intro m
  induction m with
  | zero =>
      intro α u v _ _
      rw [show IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using H1IP_le_SlotSum_one α u v
  | succ m ih =>
      intro α u v hu hv
      have hu2 : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
          Work.FTS.EllipticEst.Q0 :=
        hu.of_le (m := (((m + 1 : ℕ)) : WithTop ℕ∞))
          (by exact_mod_cast (show m + 1 ≤ (m + 1) + 1 from by omega))
      have hv2 : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
          Work.FTS.EllipticEst.Q0 :=
        hv.of_le (m := (((m + 1 : ℕ)) : WithTop ℕ∞))
          (by exact_mod_cast (show m + 1 ≤ (m + 1) + 1 from by omega))
      have hDthu : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dth u)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dth_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hu
      have hDthv : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dth v)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dth_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hv
      have hDzu : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz u)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dz_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hu
      have hDzv : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz v)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dz_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hv
      have hIHu := ih α u v hu2 hv2
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hDthu hDthv
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hDzu hDzv
      have hd := slotSum_dth_le_fin α (m + 1) u v
      have hz := slotSum_dz_le_fin α (m + 1) hu hv
      have hmono := SlotSum_mono (α := α) (u := u) (v := v)
        (n := m + 1) (m := m + 2) (by omega)
      have hsum : SlotSum α (m + 1) u v
            + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)
          ≤ 3 * SlotSum α (m + 2) u v := by
        linarith
      have hstep : IPn α (m + 1) u v
          = IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show IPn α (m + 1)
              = Work.Coercivity.HkIPStep 1 1 (IPn α m) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |IPn α m u v| + |IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le
          (IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (IPn α m u v)
          (IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |IPn α m u v|
            + |IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)
          = (3 : ℝ) ^ m * (10 : ℝ) ^ 22
            * (SlotSum α (m + 1) u v
              + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ m * (10 : ℝ) ^ 22
            * (SlotSum α (m + 1) u v
              + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (m + 1) * (10 : ℝ) ^ 22 * SlotSum α (m + 2) u v := by
        have h3 : (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * (3 * SlotSum α (m + 2) u v)
            = (3 : ℝ) ^ (m + 1) * (10 : ℝ) ^ 22 * SlotSum α (m + 2) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]

end Cd6Unfold

theorem IP6UnfoldCd6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u v : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
      ≤ C * Work.FTS.TransportS.SlotSum α 6 u v := by
  refine ⟨(3 : ℝ) ^ 5 * (10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro α u v hu hv
  have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.FTS.TransportS.IPn α 5 := rfl
  rw [hIP6]
  exact Cd6Unfold.IPn_le_SlotSum_cd6 5 α u v hu hv

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
