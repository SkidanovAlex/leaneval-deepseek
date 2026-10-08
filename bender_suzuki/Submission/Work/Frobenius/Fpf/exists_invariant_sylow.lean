import Mathlib
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# F6: an `α`-invariant Sylow `p`-subgroup exists for a fixed-point-free `α`

If `α` is a fixed-point-free automorphism of a finite group `K` (in the sense of
`Work.NPC.Fpf.IsFpf`: the only fixed point of `α` is `1`), then for every prime `p` some Sylow
`p`-subgroup of `K` is `α`-invariant.

The argument is the one from `NOTES_LEAD_ft_npc.md` §2.2 (F6), and needs no hypothesis on the
order of `α`:

* all Sylow `p`-subgroups are conjugate, so `α • P = g • P` for some `g : K`;
* the map `x ↦ x⁻¹ * α x` is bijective (F2), so pick `y` with `y⁻¹ * α y = g⁻¹`, i.e.
  `α y * g = y`;
* then `α • (y • P) = conj (α y) • (α • P) = conj (α y) • (g • P) = conj ((α y) * g) • P
  = conj y • P = y • P`, so `y • P` is the required invariant Sylow subgroup.
-/

namespace Work.Frobenius.Fpf

open Work.NPC.Fpf
open MulAction
open scoped Pointwise

variable {K : Type*}

section Helpers

variable [Group K]

/-- `α * conj y = conj (α y) * α`, i.e. conjugating by `α y` after applying `α` is the same as
applying `α` after conjugating by `y`. -/
private lemma mulAut_mul_conj (α : MulAut K) (y : K) :
    α * MulAut.conj y = MulAut.conj (α y) * α := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]

/-- `conj a * conj b = conj (a * b)`. -/
private lemma conj_mul_conj (a b : K) :
    MulAut.conj a * MulAut.conj b = MulAut.conj (a * b) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]

end Helpers

theorem exists_invariant_sylow {K : Type*} [Group K] [Finite K] {α : MulAut K} (hα : Work.NPC.Fpf.IsFpf α) (p : ℕ) [Fact p.Prime] : ∃ P : Sylow p K, Work.NPC.Fpf.IsInv α (P : Subgroup K) := by
  classical
  -- an arbitrary Sylow `p`-subgroup
  let P : Sylow p K := Sylow.nonempty.some
  -- its image under `α` is conjugate to it (Sylow's second theorem)
  obtain ⟨g, hg⟩ := IsPretransitive.exists_smul_eq (M := K) P (α • P)
  -- at the level of the underlying subgroups this reads `conj g • P = α • P`
  have hg' : MulAut.conj g • (P : Subgroup K) = α • (P : Subgroup K) := by
    have h := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def] using h
  -- F2: the map `x ↦ x⁻¹ * α x` is bijective, so there is `y` with `y⁻¹ * α y = g⁻¹`
  obtain ⟨y, hy⟩ := (isFpf_mulInv_bijective hα).2 g⁻¹
  have hy' : y⁻¹ * α y = g⁻¹ := hy
  have hαy : α y = y * g⁻¹ := by
    calc α y = y * (y⁻¹ * α y) := by group
      _ = y * g⁻¹ := by rw [hy']
  have hyg : α y * g = y := by rw [hαy]; group
  -- the conjugate `y • P` is `α`-invariant
  refine ⟨y • P, isInv_of_map_eq ?_⟩
  rw [Sylow.coe_subgroup_smul]
  change α • (MulAut.conj y • (P : Subgroup K)) = MulAut.conj y • (P : Subgroup K)
  rw [← mul_smul, mulAut_mul_conj, mul_smul, ← hg', ← mul_smul, conj_mul_conj, hyg]

end Work.Frobenius.Fpf
