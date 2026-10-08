import Mathlib
import Submission.Work.A7REC.Excl

/-!
Area `A7REC`, file `Char/a7NoNine.lean`: leaf `A7NoNineProp` of the design-pass-8 contract
(`Submission/Work/_design_gw/Core8.lean` §1).

From the degree-`6` representation `ρ` of `C1` — trace `3` on every nonidentity element of `U` —
no subgroup `P` of order `9` has *all* of its nonidentity elements conjugate into `U`.

The argument is the average over `P`: put `T = Σ_{p ∈ P} ρ p`.  Then
* `T x` is fixed by every element of `P` (multiplying `T` on the left by `ρ q` permutes the
  running index), and
* `T x = 9 · x` whenever `x` is fixed by `P`,
so `(1/9) • T` is the projection onto the common fixed space `FixSub ρ P`, whence
`trace T = 9 · dim Fix(P)`.

If every nonidentity `p ∈ P` were conjugate into `U`, the trace of `ρ p` would be `3` for all such
`p` (trace is invariant under conjugation, and conjugation preserves `≠ 1`), so
`trace T = trace (ρ 1) + 8·3 = 6 + 24 = 30`, and `30 = 9 · dim Fix(P)` is impossible.
-/

namespace Work.A7REC.Char

open Subgroup

variable {G : Type*} [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The common fixed space of a subgroup `H ≤ G` under a representation `ρ`. -/
def FixSub (ρ : Representation ℂ G W) (H : Subgroup G) : Submodule ℂ W where
  carrier := {x | ∀ g ∈ H, ρ g x = x}
  zero_mem' := by intro g _; simp
  add_mem' := by
    intro x y hx hy g hg
    simp only [map_add, hx g hg, hy g hg]
  smul_mem' := by
    intro a x hx g hg
    simp only [map_smul, hx g hg]

theorem mem_FixSub {ρ : Representation ℂ G W} {H : Subgroup G} {x : W} :
    x ∈ FixSub ρ H ↔ ∀ g ∈ H, ρ g x = x := Iff.rfl

theorem a7NoNine : Work.A7REC.A7NoNineProp := by
  classical
  intro G _ _ U z W _ _ _ ρ hρ
  obtain ⟨h6, _hztr, hUtr, _h7tr⟩ := hρ
  intro P hPcard
  by_contra hcon
  push_neg at hcon
  haveI : Fintype ↥P := Fintype.ofFinite ↥P
  have hcard : Fintype.card ↥P = 9 := by
    rw [← Nat.card_eq_fintype_card]; exact hPcard
  -- trace of `ρ 1` is the degree `6`
  have htr1 : LinearMap.trace ℂ W (ρ ((1 : ↥P) : G)) = 6 := by
    rw [show ((1 : ↥P) : G) = 1 from rfl, map_one,
      show (1 : W →ₗ[ℂ] W) = LinearMap.id from rfl, LinearMap.trace_id, h6]
    norm_num
  -- trace of `ρ p` is `3` for every nonidentity `p ∈ P` (conjugate into `U#`)
  have htrne : ∀ p : ↥P, p ≠ 1 → LinearMap.trace ℂ W (ρ (p : G)) = 3 := by
    intro p hp
    have hp1 : (p : G) ≠ 1 := fun h => hp (Subtype.ext h)
    obtain ⟨g, u, huU, hgu⟩ := hcon (p : G) p.2 hp1
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, mul_one, mul_inv_cancel] at hgu
      exact hp1 hgu.symm
    have hconj : ρ (p : G) = ρ g * ρ u * ρ g⁻¹ := by
      rw [← hgu, map_mul, map_mul]
    rw [hconj]
    calc LinearMap.trace ℂ W (ρ g * ρ u * ρ g⁻¹)
        = LinearMap.trace ℂ W (ρ g⁻¹ * (ρ g * ρ u)) :=
          LinearMap.trace_mul_comm ℂ (ρ g * ρ u) (ρ g⁻¹)
      _ = LinearMap.trace ℂ W (ρ u) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = 3 := hUtr u huU hu1
  set T : W →ₗ[ℂ] W := ∑ p : ↥P, ρ (p : G) with hT
  -- the sum of the traces is `30`
  have htrT : LinearMap.trace ℂ W T = 30 := by
    rw [hT, map_sum]
    have h1 : ∑ p : ↥P, LinearMap.trace ℂ W (ρ (p : G))
        = ∑ p : ↥P, (if p = 1 then (6 : ℂ) else 3) :=
      Finset.sum_congr rfl (fun p _ => by
        split_ifs with hp
        · rw [hp]; exact htr1
        · exact htrne p hp)
    rw [h1]
    have h2 : ∀ p : ↥P, (if p = 1 then (6 : ℂ) else 3) = 3 + (if p = 1 then (3 : ℂ) else 0) := by
      intro p; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl (fun p _ => h2 p)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
      Finset.sum_ite_eq']
    norm_num
  -- left multiplication by `ρ q` fixes `T`
  have hTfix : ∀ q : ↥P, ρ (q : G) * T = T := by
    intro q
    rw [hT, Finset.mul_sum]
    have hstep : ∀ p : ↥P, ρ (q : G) * ρ (p : G) = ρ ((q * p : ↥P) : G) := by
      intro p; rw [← map_mul]; rfl
    rw [Finset.sum_congr rfl (fun p _ => hstep p)]
    rw [show (∑ p : ↥P, ρ ((q * p : ↥P) : G)) = ∑ r : ↥P, ρ ((r : G))
        from Equiv.sum_comp (Equiv.mulLeft q) (fun r : ↥P => ρ ((r : G)))]
  -- `(1/9) • T` is the projection onto the fixed space
  have hproj : LinearMap.IsProj (FixSub ρ P) (((1 / 9 : ℂ)) • T) := by
    refine ⟨?_, ?_⟩
    · intro x
      rw [mem_FixSub]
      intro q hq
      have hq' : ρ q * T = T := by
        have h := hTfix ⟨q, hq⟩
        simpa using h
      have hx : ρ q (T x) = T x := by
        have h := congrArg (fun f : W →ₗ[ℂ] W => f x) hq'
        simpa [Module.End.mul_apply] using h
      show ρ q (((1 / 9 : ℂ) • T) x) = ((1 / 9 : ℂ) • T) x
      rw [LinearMap.smul_apply, map_smul, hx]
    · intro x hx
      rw [mem_FixSub] at hx
      have hTx : T x = (9 : ℂ) • x := by
        rw [hT, LinearMap.sum_apply]
        have hx' : ∀ p : ↥P, ρ (p : G) x = x := fun p => hx (p : G) p.2
        rw [Finset.sum_congr rfl (fun p _ => hx' p), Finset.sum_const, Finset.card_univ, hcard]
        exact (Nat.cast_smul_eq_nsmul ℂ 9 x).symm
      show ((1 / 9 : ℂ) • T) x = x
      rw [LinearMap.smul_apply, hTx, smul_smul, show (1 / 9 : ℂ) * 9 = 1 by norm_num, one_smul]
  -- hence `trace T = 9 · dim Fix(P)`, but `trace T = 30`
  have htrproj := hproj.trace
  rw [map_smul, htrT] at htrproj
  have h9 : (9 : ℂ) * (Module.finrank ℂ ↥(FixSub ρ P) : ℂ) = 30 := by
    rw [smul_eq_mul] at htrproj
    rw [← htrproj]
    norm_num
  have hnat : 9 * Module.finrank ℂ ↥(FixSub ρ P) = 30 := by exact_mod_cast h9
  omega

end Work.A7REC.Char
