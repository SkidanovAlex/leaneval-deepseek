import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.relIndex_eq_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- Definition 9.1(ii)(b) transfers to the complement `𝔏 ⊓ 𝔑_i`: the order of the element
`M = projEC Lhat (Hs i) N ∈ 𝔏 ⊓ 𝔑_i` is coprime to `|𝔎_i|`.

Proof route: `orderOf M ∣ Nat.card ↥(𝔏 ⊓ 𝔑_i)` (`orderOf_dvd_natCard`), and
`Nat.card ↥(𝔏 ⊓ 𝔑_i) = (𝔎_i).relIndex (𝔑_i)`; the Hall condition `h.supp_hall hD i` gives that
`|𝔎_i|` is coprime to that index, so `Nat.Coprime.coprime_dvd_right` finishes.  The identity
between the index and the cardinality of the complement is the statement of
`Work.Tame.relIndex_eq_card_inf`. -/
theorem coprime_card_orderOf_projEC {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    (i : Fin n) (N : ↥(Lgrp (Hs i : Set X))) :
    (Nat.card ↥(Hs i)).Coprime (orderOf ((projEC Lhat (Hs i) N :
      ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) : X)) := by
  -- (ii)(b): `𝔎_i` is an `S`-subgroup (a Hall subgroup) of `𝔑_i = N(𝔎_i)`, i.e. `|𝔎_i|` is
  -- coprime to the index `|𝔑_i : 𝔎_i|`.
  have hhall : IsHallIn (Hs i) (Lgrp (Hs i : Set X)) := h.supp_hall hD i
  -- `𝔑_i = 𝔎_i ⊔ (𝔏 ⊓ 𝔑_i)` with `𝔎_i ⊓ 𝔏 = 1`, so that index is the order of the complement.
  have hcard : Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) =
      (Hs i).relIndex (Lgrp (Hs i : Set X)) := (relIndex_eq_card_inf h hD i).symm
  have hcop : (Nat.card ↥(Hs i)).Coprime
      (Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) := by
    rw [hcard]
    exact hhall.2
  -- the order of an element of the complement divides the order of the complement
  have hdvd : orderOf ((projEC Lhat (Hs i) N : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) : X) ∣
      Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ (projEC Lhat (Hs i) N).2
  exact hcop.coprime_dvd_right hdvd

end Work.Tame
