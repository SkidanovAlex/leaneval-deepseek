import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PGroup.All
import Submission.Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

-- `O_{p'}(G) · Z(J(P))` is the preimage of `Z(J(P O_{p'}(G)/O_{p'}(G)))` under the quotient map.
-- (Here `O_{p'}(G)` is a `p'`-group, so `P ⊓ O_{p'}(G) = ⊥` for a `p`-subgroup `P`, and `Z(J(·))`
-- transports across quotients injective on `P` — `Work.PGroup.ZJ_map_of_ker_inf_eq_bot`.)
theorem ZJ_comap_mk_eq_sup {G : Type*} [Group G] [Finite G] (p : ℕ) (P : Subgroup G)
    [(Submission.Blueprint.pPrimeCore p G).Normal]
    (hdisj : P ⊓ Submission.Blueprint.pPrimeCore p G = ⊥) :
    (Submission.Blueprint.ZJ (P.map
        (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)))).comap
        (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)) =
      Submission.Blueprint.pPrimeCore p G ⊔ Submission.Blueprint.ZJ P := by
  -- The kernel of the quotient map is `O_{p'}(G)`; by hypothesis it meets `P` trivially, so the
  -- quotient map is injective on `P`.
  have hker : (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)).ker ⊓ P = ⊥ := by
    rw [QuotientGroup.ker_mk', inf_comm]
    exact hdisj
  -- `Z(J(·))` is natural under such a map: `Z(J(P)).map mk' = Z(J(P.map mk'))`.
  have hmap :=
    Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot
      (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)) P hker
  -- Preimages of images are the product with the kernel: `(X.map f).comap f = X ⊔ f.ker`.
  rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]

end Work.GlaubermanZJ
