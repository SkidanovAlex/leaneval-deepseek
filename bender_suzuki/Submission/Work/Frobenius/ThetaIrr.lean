import Mathlib
import Submission.Work.Frobenius.Theta
import Submission.Work.Frobenius.VCharInd
import Submission.Work.Frobenius.VChar.vchar_norm_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `θ*` is an irreducible character

For a Frobenius complement `H ≤ G` and `θ ∈ Irr H`, `θ ≠ 1`, the class function
`θ* = (θ - θ 1 · 1_H)^G + θ 1 · 1_G` is a virtual character of norm one and positive degree,
hence an irreducible character of `G`.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise MonoidAlgebra

set_option linter.style.haveILetI false

namespace Work.Frobenius

variable {G : Type*} [Group G] [Fintype G]

section LocalFintype

local instance instFintypeSubgroupThetaIrr (H : Subgroup G) : Fintype H := Fintype.ofFinite H

omit [Fintype G] in
/-- The degree of an irreducible character is a positive natural number. -/
theorem character_one_eq_natCast {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = (n : ℂ) := by
  obtain ⟨d, hd⟩ := mem_Irr_iff.mp hχ
  haveI : IsSimpleModule ℂ[G] d.ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule d.ρ).mp d.irred
  haveI : Nontrivial d.V := IsSimpleModule.nontrivial ℂ[G] (d.ρ.asModule)
  refine ⟨Module.finrank ℂ d.V, Module.finrank_pos, ?_⟩
  rw [← hd, Representation.char_one]

/-- `θ*` is a virtual character. -/
theorem isVChar_thetaStar {H : Subgroup G} {θ : H → ℂ} (hθ : θ ∈ Irr H) :
    IsVChar (thetaStar H θ) := by
  classical
  obtain ⟨d, hd⟩ := mem_Irr_iff.mp hθ
  have hdeg : d.ρ.character 1 = (Module.finrank ℂ d.V : ℂ) := Representation.char_one d.ρ
  have hθcl : d.ρ.character ∈ AddSubgroup.closure (Irr H) :=
    AddSubgroup.subset_closure (mem_Irr_iff.mpr ⟨d, rfl⟩)
  have hone : (1 : H → ℂ) ∈ AddSubgroup.closure (Irr H) :=
    AddSubgroup.subset_closure Work.Frobenius.Irr.isIrr_one
  have hsub : IsVChar (d.ρ.character - (d.ρ.character 1) • (1 : H → ℂ)) := by
    rw [hdeg, Nat.cast_smul_eq_nsmul ℂ]
    exact AddSubgroup.sub_mem _ hθcl (AddSubgroup.nsmul_mem _ hone _)
  have hind : IsVChar (indFun H (d.ρ.character - (d.ρ.character 1) • (1 : H → ℂ))) :=
    isVChar_indFun hsub
  have honeG : (1 : G → ℂ) ∈ AddSubgroup.closure (Irr G) :=
    AddSubgroup.subset_closure Work.Frobenius.Irr.isIrr_one
  have hsmul : IsVChar ((d.ρ.character 1) • (1 : G → ℂ)) := by
    rw [hdeg, Nat.cast_smul_eq_nsmul ℂ]
    exact AddSubgroup.nsmul_mem _ honeG _
  rw [thetaStar, ← hd]
  exact AddSubgroup.add_mem _ hind hsmul

/-- `θ*` is an irreducible character. -/
theorem thetaStar_mem_Irr {H : Subgroup G} (hH : IsFrobeniusComplement H) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) : thetaStar H θ ∈ Irr G := by
  classical
  have hV : IsVChar (thetaStar H θ) := isVChar_thetaStar hθ
  have hnorm : charPair (thetaStar H θ) (thetaStar H θ) = 1 := charPair_thetaStar_self hH hθ hθ1
  obtain ⟨χ, hχ, hcase⟩ := Work.Frobenius.VChar.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact hχ
  · exfalso
    obtain ⟨m, hmpos, hm⟩ := character_one_eq_natCast hθ
    obtain ⟨n, hnpos, hn⟩ := character_one_eq_natCast hχ
    have hb : ((m : ℕ) : ℂ) = -((n : ℕ) : ℂ) := by
      have hthis := congrFun h 1
      rw [thetaStar_apply_one H θ, hm, Pi.neg_apply, hn] at hthis
      exact hthis
    have hcast : ((m : ℕ) : ℂ) + ((n : ℕ) : ℂ) = 0 := by rw [hb]; ring
    have : (m : ℕ) + n = 0 := by exact_mod_cast hcast
    omega

end LocalFintype

end Work.Frobenius
