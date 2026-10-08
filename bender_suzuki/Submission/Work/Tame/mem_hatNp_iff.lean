import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- Membership in `⋃_{H ∈ 𝔎^#} C_{N(𝔎)}(H)` (Feit–Thompson (ii)(e), p. 804): `x` lies in the
union exactly when `x ∈ N(𝔎)` and `x` commutes with some non-identity element of `𝔎`. -/
theorem mem_hatNCore_iff_local {X : Type*} [Group X] {K : Subgroup X} {x : X} :
    x ∈ hatNCore K ↔
      x ∈ Lgrp K ∧ ∃ H : X, H ∈ K ∧ H ≠ 1 ∧ x * H = H * x := by
  simp only [hatNCore, Set.mem_iUnion, mem_punct,
    SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨i, ⟨hiK, hi1⟩, hcomm, hLgrp⟩
    exact ⟨hLgrp, i, hiK, hi1, hcomm⟩
  · rintro ⟨hLgrp, H, hHK, hH1, hcomm⟩
    exact ⟨H, ⟨hHK, hH1⟩, hcomm, hLgrp⟩

/-- Membership in `Ñ^#` (Feit–Thompson (ii)(e)): `x ∈ Ñ^#` iff `x ∈ N(𝔎)`, `x ∉ 𝔎`, and `x`
commutes with a non-identity element of `𝔎`. -/
theorem mem_hatNp_iff {X : Type*} [Group X] {K : Subgroup X} {x : X} :
    x ∈ hatNp K ↔ x ∈ Lgrp K ∧ x ∉ K ∧
      ∃ H : X, H ∈ K ∧ H ≠ 1 ∧ x * H = H * x := by
  simp only [hatNp, punct, Set.mem_sdiff, Set.mem_singleton_iff, hatN, mem_hatNCore_iff_local]
  constructor
  · rintro ⟨⟨⟨hLgrp, H, hHK, hH1, hcomm⟩, hnotK⟩, hx1⟩
    exact ⟨hLgrp, fun hxK => hnotK ⟨hxK, hx1⟩, H, hHK, hH1, hcomm⟩
  · rintro ⟨hLgrp, hxK, H, hHK, hH1, hcomm⟩
    exact ⟨⟨⟨hLgrp, H, hHK, hH1, hcomm⟩, fun h => hxK h.1⟩,
      fun h1 => hxK (by rw [h1]; exact K.one_mem)⟩

end Work.Tame
