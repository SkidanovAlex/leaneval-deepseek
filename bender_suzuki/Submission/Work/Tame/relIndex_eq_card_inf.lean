import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.projEC_eq_self

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- The index of `𝔎_i` in `𝔑_i = N(𝔎_i)` equals the order of the "complement" `𝔏 ⊓ 𝔑_i`
of Definition 9.1(ii)(c) (`𝔑_i = 𝔎_i ⊔ (𝔏 ⊓ 𝔑_i)`, `𝔎_i ⊓ 𝔏 = 1`).

Proof route: `projEC Lhat (Hs i)` is the map `𝔑_i → 𝔏 ⊓ 𝔑_i` sending `N` to the unique
`M ∈ 𝔏 ⊓ 𝔑_i` with `N * M⁻¹ ∈ 𝔎_i`.  By `projEC_mul` (with the two fields
(ii)(c) of `h`, available from `hD`) and `projEC_one` it is a group homomorphism; its kernel is
`𝔎_i.subgroupOf 𝔑_i` (if `projEC N = 1` then `N = N * 1⁻¹ ∈ 𝔎_i` by `mul_projEC_inv_mem`, and
conversely `projEC N = 1` for `N ∈ 𝔎_i` by `projEC_eq_of`), and it is surjective because
`projEC M = M` for `M ∈ 𝔏 ⊓ 𝔑_i` (`projEC_eq_self`).  Then `Subgroup.index_ker` gives
`(𝔎_i.subgroupOf 𝔑_i).index = Nat.card ↥(𝔏 ⊓ 𝔑_i)`, and `Subgroup.relIndex` is by definition the
index of `H.subgroupOf K`. -/
theorem relIndex_eq_card_inf {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    (i : Fin n) :
    (Hs i).relIndex (Lgrp (Hs i : Set X)) = Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) := by
  -- the two fields (ii)(c) of Definition 9.1
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hD i
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD i
  -- the projection `𝔑_i → 𝔏 ⊓ 𝔑_i` is a group homomorphism
  let f : ↥(Lgrp (Hs i : Set X)) →* ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    { toFun := fun N => projEC Lhat (Hs i) N
      map_one' := projEC_one hinf
      map_mul' := fun N₁ N₂ => projEC_mul hsup hinf N₁ N₂ }
  -- its kernel is `𝔎_i` (viewed inside `𝔑_i`)
  have hker : f.ker = (Hs i).subgroupOf (Lgrp (Hs i : Set X)) := by
    ext N
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hN
      have hN' : projEC Lhat (Hs i) N = 1 := hN
      have hmem := mul_projEC_inv_mem hsup N
      rw [hN'] at hmem
      simpa using hmem
    · intro hN
      exact projEC_eq_of hinf (by simpa using hN)
  -- and it is surjective
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    rintro m -
    exact ⟨⟨(m : X), m.2.2⟩, projEC_eq_self hinf m⟩
  -- `Subgroup.index_ker` then yields the index as the order of the complement
  have hindex := Subgroup.index_ker f
  rw [hker, hrange, Subgroup.card_top] at hindex
  exact hindex

end Work.Tame
