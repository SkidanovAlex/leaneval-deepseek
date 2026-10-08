import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.H0Conj
import Submission.Work.BG.S02
import Submission.OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- The involution `t` of the §2 context is central in `H₀` (it commutes with all of `H`,
by `Sec2Ctx.t_comm_H`, and `H₀ ≤ H`). -/
theorem Sec2Ctx.t_mem_center (C : Sec2Ctx G) : C.t ∈ Subgroup.center ↥C.P.H0 := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subtype.ext (C.t_comm_H (x : G) (C.P.H0_le_H x.2))

theorem centralValue {G : Type} [Group G] [Finite G] :
    ∀ C : Work.BG.Sec2Ctx G, Work.BG.CentralValueProp C := by
  intro C ν hν
  -- realise `ν` as the character of a finite-dimensional irreducible `ℂ`-representation
  obtain ⟨W, _, _, _, ρ, hirr, hchar⟩ := hν
  haveI : Representation.IsIrreducible ρ := hirr
  -- Schur: the central involution `t` acts on `W` by a scalar
  obtain ⟨c, hc⟩ := center_isScalar ρ (C.t_mem_center)
  -- `ρ t` is an involution, so the scalar satisfies `c * c = 1`
  have hsq : ρ C.t * ρ C.t = 1 := by
    rw [← map_mul, ← pow_two, C.t_sq, map_one]
  haveI : Nontrivial W := nontrivial_of_isIrreducible ρ
  have hcc : c * c = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : ρ C.t (ρ C.t w) = w := by
      rw [← Module.End.mul_apply, hsq, Module.End.one_apply]
    rw [hc] at h1
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul] at h1
    exact smul_left_injective ℂ hw (by simpa using h1)
  have hcpm : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (by linear_combination h')
  -- character values: `ν t = c · ν 1`
  have hch1 : ν 1 = (Module.finrank ℂ W : ℂ) := by
    rw [show ν 1 = (ν : ↥C.P.H0 → ℂ) 1 from rfl, congrFun hchar 1, ρ.char_one]
  have hcht : ν C.t = (Module.finrank ℂ W : ℂ) * c := by
    rw [show ν C.t = (ν : ↥C.P.H0 → ℂ) C.t from rfl, congrFun hchar C.t]
    change LinearMap.trace ℂ W (ρ C.t) = _
    rw [hc, map_smul, LinearMap.trace_id]
    simp [smul_eq_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · rcases hcpm with h | h
    · left; rw [hcht, hch1, h, mul_one]
    · right; rw [hcht, hch1, h]; ring
  · rw [hch1]
    exact Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)

end Work.BG
