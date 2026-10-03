import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.ZMod

open scoped BigOperators

/-- Condition transfer: an integer `x` satisfies `d ∣ x² + b²` if and only if its class in
`ZMod d` satisfies the analogous congruence. -/
lemma int_dvd_iff_zmod (d : ℕ) (b : ℕ) (x : ℤ) :
    (d : ℤ) ∣ x ^ 2 + (b : ℤ) ^ 2 ↔ (x : ZMod d) ^ 2 + (b : ZMod d) ^ 2 = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 + (b : ℤ) ^ 2) d]
  push_cast
  ring_nf

/-- The class of `(α.val : ℤ) + m * d` in `ZMod d` is `α`. -/
lemma zmod_cast_val_add_mul (d : ℕ) [NeZero d] (α : ZMod d) (m : ℤ) :
    (((α.val : ℤ) + m * (d : ℤ) : ℤ) : ZMod d) = α := by
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero]

/-- Condition transfer along one residue class modulo `d`. -/
lemma int_dvd_iff_zmod_add (d : ℕ) [NeZero d] (b : ℕ) (α : ZMod d) (m : ℤ) :
    (d : ℤ) ∣ ((α.val : ℤ) + m * (d : ℤ)) ^ 2 + (b : ℤ) ^ 2 ↔
      α ^ 2 + (b : ZMod d) ^ 2 = 0 := by
  rw [int_dvd_iff_zmod d b, zmod_cast_val_add_mul]

theorem tsum_int_quadratic_coset (d : ℕ) [NeZero d] (b : ℕ) (g : ℤ → ℝ) (hg : Summable g) :
    ∑' a : ℤ, (if (d : ℤ) ∣ a^2 + (b : ℤ)^2 then g a else 0)
      = ∑ α : ZMod d, (if α^2 + (b : ZMod d)^2 = 0 then
          ∑' m : ℤ, g ((α.val : ℤ) + m * (d : ℤ)) else 0) := by
  classical
  let T : Set (ZMod d) := {α | α ^ 2 + (b : ZMod d) ^ 2 = 0}
  let S : Set ℤ := {a | (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2}
  -- The fibration map: a residue class together with an integer gives an integer.
  let psi : ↥T × ℤ → ↥S := fun p =>
    ⟨(p.1.val.val : ℤ) + p.2 * (d : ℤ), by
      show (d : ℤ) ∣ ((p.1.val.val : ℤ) + p.2 * (d : ℤ)) ^ 2 + (b : ℤ) ^ 2
      rw [int_dvd_iff_zmod_add]
      exact p.1.2⟩
  have psi_inj : Function.Injective psi := by
    rintro ⟨⟨α, hα⟩, m⟩ ⟨⟨β, hβ⟩, n⟩ h
    have h' : (α.val : ℤ) + m * (d : ℤ) = (β.val : ℤ) + n * (d : ℤ) := by
      simpa only [psi] using Subtype.ext_iff.mp h
    have hab : α = β := by
      have := congr_arg (fun z : ℤ => (z : ZMod d)) h'
      simpa only [zmod_cast_val_add_mul] using this
    have hval : (α.val : ℤ) = (β.val : ℤ) := congr_arg (fun z : ZMod d => (z.val : ℤ)) hab
    have hmn : m = n := by
      have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.pos d).ne'
      rw [← hval] at h'
      exact mul_right_cancel₀ hd (add_left_cancel h')
    exact Prod.ext (Subtype.ext hab) hmn
  have psi_surj : Function.Surjective psi := by
    intro a
    have haS : (d : ℤ) ∣ a.val ^ 2 + (b : ℤ) ^ 2 := a.2
    have hα : ((a.val : ZMod d)) ^ 2 + (b : ZMod d) ^ 2 = 0 :=
      (int_dvd_iff_zmod d b a.val).mp haS
    let α : ZMod d := (a.val : ZMod d)
    have hαT : α ∈ T := hα
    let m : ℤ := (a.val - (α.val : ℤ)) / (d : ℤ)
    refine ⟨(⟨α, hαT⟩, m), ?_⟩
    apply Subtype.ext
    show (α.val : ℤ) + m * (d : ℤ) = a.val
    have hdvd : (d : ℤ) ∣ a.val - (α.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (((a.val : ℤ) - (α.val : ℤ) : ℤ) : ZMod d) = 0
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact sub_self α
    show (α.val : ℤ) + ((a.val - (α.val : ℤ)) / (d : ℤ)) * (d : ℤ) = a.val
    rw [Int.ediv_mul_cancel hdvd]
    ring
  -- Step 1: rewrite the indicator sum as a sum over the subtype of admissible integers.
  have hLHS : (∑' a : ℤ, (if (d : ℤ) ∣ a^2 + (b : ℤ)^2 then g a else 0))
      = ∑' a : ↥S, g a.val := by
    rw [tsum_subtype S g]
    exact tsum_congr (fun a => by simp [S, Set.indicator_apply])
  -- Step 2: reindex the subtype sum along the fibration.
  have h2 : (∑' a : ↥S, g a.val) = ∑' p : ↥T × ℤ, g (psi p).val :=
    (Equiv.tsum_eq (Equiv.ofBijective psi ⟨psi_inj, psi_surj⟩) (fun a : ↥S => g a.val)).symm
  -- Step 3: split the product sum.
  have hsS : Summable (fun a : ↥S => g a.val) :=
    hg.comp_injective (Subtype.val_injective (p := fun a : ℤ => a ∈ S))
  have h3 : (∑' p : ↥T × ℤ, g (psi p).val)
      = ∑' t : ↥T, ∑' m : ℤ, g (psi (t, m)).val :=
    (hsS.comp_injective psi_inj).tsum_prod
  -- Step 4: simplify the inner summand.
  have h4 : (∑' t : ↥T, ∑' m : ℤ, g (psi (t, m)).val)
      = ∑' t : ↥T, ∑' m : ℤ, g ((t.val.val : ℤ) + m * (d : ℤ)) := by
    apply tsum_congr
    intro t
    apply tsum_congr
    intro m
    rfl
  -- Step 5: rewrite the right-hand side.
  have hRHS : (∑ α : ZMod d, (if α^2 + (b : ZMod d)^2 = 0 then
        ∑' m : ℤ, g ((α.val : ℤ) + m * (d : ℤ)) else 0))
      = ∑' t : ↥T, ∑' m : ℤ, g ((t.val.val : ℤ) + m * (d : ℤ)) := by
    have hfin : (∑ α : ZMod d, (if α^2 + (b : ZMod d)^2 = 0 then
          ∑' m : ℤ, g ((α.val : ℤ) + m * (d : ℤ)) else 0))
        = ∑' α : ZMod d, T.indicator (fun α : ZMod d =>
            ∑' m : ℤ, g ((α.val : ℤ) + m * (d : ℤ))) α := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro α _
      simp [T, Set.indicator_apply]
    rw [hfin, ← tsum_subtype T (fun α : ZMod d =>
      ∑' m : ℤ, g ((α.val : ℤ) + m * (d : ℤ)))]
  rw [hLHS, h2, h3, h4, ← hRHS]

end Commons.NumberTheory.ZMod