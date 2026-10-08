import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.ThmF.Bender.ncard_Kset_eq_ncard_InvHt
import Submission.Work.ThmF.Bender.ncard_InvHt_eq_ncard_involutions

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|K(D,t)| = |Inv(H)|` (Peterfalvi I, Ch. I §2, Prop. 1 (c))

Let `H` be a strongly embedded subgroup of the finite group `G` and `t ∉ H` an involution.
With `D = H ∩ H^t = twoPoint H t` and `K = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹} = Kset H t`, the
number of elements of `K` equals the number `n = |Inv(H)|` of involutions of `H`.

This is the `|K| = n` clause of Peterfalvi I, Ch. I §2 Prop. 2 (b).  The counting is split into
the two facts established in the sibling files:

* `Work.ThmF.Bender.ncard_Kset_eq_ncard_InvHt` : `|K| = |InvHt H t|`, where `InvHt H t` is the
  set of involutions `u` transforming `H` into the conjugate `H^t`; the bijection is right
  multiplication by `t` (`x ↦ x * t`), since `(x t)² = x (t x t) = 1` and `H^{xt} = x H^t x⁻¹
  = H^t` for `x ∈ H ∩ H^t`, while conversely an involution `u` with `H^u = H^t` satisfies
  `t⁻¹u ∈ N_G(H) = H`, and then `u t = h⁻¹` with `h = t⁻¹ u`;
* `Work.ThmF.Bender.ncard_InvHt_eq_ncard_involutions` : `|InvHt H t| = |Inv(H)|` — Peterfalvi
  I, Ch. I §2 Prop. 1 (c) — conjugating by `t` and using the uniqueness of the conjugating
  involution.

Source: Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §2.
-/

set_option autoImplicit false

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem cardKsetEqInv {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht2 : orderOf t = 2) (htH : t ∉ H) : (Kset H t).ncard = (involutions (H : Set G)).ncard := by
  -- `|K| = |InvHt H t|` (bijection `x ↦ x * t`), then `|InvHt H t| = |Inv(H)|`.
  rw [ncard_Kset_eq_ncard_InvHt hH ht2 htH, ncard_InvHt_eq_ncard_involutions hH ht2 htH]

end Work.ThmF.Bender
