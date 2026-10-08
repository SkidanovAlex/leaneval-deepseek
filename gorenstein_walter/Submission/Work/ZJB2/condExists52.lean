import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.Step1.sylowInInfNormal
import Submission.Work.ZJB2.cbarNormalizes
import Submission.Work.ZJB2.existsConjSylowIn

/-!
# gorenstein_walter — `ZJB2.condExists52` (T52.ex)

Glauberman 1968, p. 1122 proof of Theorem 5.2: for every `W ≤ S`, `S` a Sylow `p`-subgroup,
there is a conjugate `V = x W x⁻¹ ≤ S` such that `V ≤ O_p(G)` or `C_S(V̄)` is a Sylow
`p`-subgroup of `C_G(V̄)` (`V̄ = VP/P`).

**Route** (design pass 17, item B).  Always the right disjunct.  With `P = O_p(G)`,
`U = W ⊔ P ≤ S`, apply G4 (`Work.ZJB2.existsConjSylowIn`) with `Y = N_G(U)`: there is `x`
with `U^x ≤ S` and `N_G(U)^x ∩ S` Sylow in `N_G(U)^x`.  Since `P ⊴ G`, `U^x = V ⊔ P` and
`N_G(U)^x = N_G(V ⊔ P)`, so `T = N_G(V ⊔ P) ∩ S` is Sylow in `N_G(V ⊔ P)`.

Now `Cbar P V = C_G(V̄) ≤ N_G(V ⊔ P)` and is *normal* in it (both elementary; the second is
the quotient-computation `N_{G/P}(V̄) ≤ N_{G/P}(C_{G/P}(V̄))` pulled back along `G → G/P`).
So G2 (`Work.ZJB2.Step1.sylowInInfNormal`) with `M = N_G(V ⊔ P)`, `L = Cbar P V` gives
`T ∩ Cbar P V = Cbar P V ∩ S` Sylow in `Cbar P V`.  That is the claim.
-/

namespace Work.ZJB2

open Work.ZJB
open Subgroup

/-- `C_G(V̄) ≤ N_G(V ⊔ P)` (`P =` the fixed normal subgroup, `V̄` the image in `G/P`).

If `y ∈ C_G(V̄)` and `v ∈ V`, then `y⁻¹ v y ∈ vP ⊆ V ⊔ P`; if `p ∈ P`, then `y⁻¹ p y ∈ P`.  So
`y⁻¹` carries the generating set `V ∪ P` of `V ⊔ P` into `V ⊔ P`. -/
theorem cbar_le_normalizer_sup {G : Type*} [Group G] (P : Subgroup G) [P.Normal]
    (V : Subgroup G) :
    Work.ZJB.Cbar P V ≤ Subgroup.normalizer ((V ⊔ P : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro y hy k hk
  obtain ⟨v, hv, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  -- `y * v * y⁻¹ ∈ V ⊔ P`
  have hv1 : y * v * y⁻¹ ∈ V ⊔ P := by
    obtain ⟨p, hp, hpe⟩ := Work.ZJB2.exists_mul_of_mem_cbar P V hy v hv
    -- `v = (y * v * y⁻¹) * (y * p * y⁻¹)`, hence `y * v * y⁻¹ = v * (y * p * y⁻¹)⁻¹`
    have hconj' : v = (y * v * y⁻¹) * (y * p * y⁻¹) := by
      calc v = y * (y⁻¹ * v * y) * y⁻¹ := by group
        _ = y * (v * p) * y⁻¹ := by rw [hpe]
        _ = (y * v * y⁻¹) * (y * p * y⁻¹) := by group
    have key : y * v * y⁻¹ = v * (y * p * y⁻¹)⁻¹ :=
      eq_mul_inv_of_mul_eq hconj'.symm
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right
        (P.inv_mem (Subgroup.Normal.conj_mem (inferInstance : P.Normal) p hp y)))
  have hq1 : y * q * y⁻¹ ∈ V ⊔ P :=
    Subgroup.mem_sup_right (Subgroup.Normal.conj_mem (inferInstance : P.Normal) q hq y)
  have hsum : y * (v * q) * y⁻¹ = (y * v * y⁻¹) * (y * q * y⁻¹) := by group
  rw [hsum]
  exact Subgroup.mul_mem _ hv1 hq1

/-- `C_G(V̄)` is normal in `N_G(V ⊔ P)`.

Write `π : G → G/P`.  Then `C_G(V̄) = π⁻¹(C_{G/P}(V̄))` while
`π(N_G(V ⊔ P)) ≤ N_{G/P}((V ⊔ P)/P) = N_{G/P}(V̄) ≤ N_{G/P}(C_{G/P}(V̄))`
(centralizers are normal in their normalizers), so pulling back along the surjection `π` and
using `comap_normalizer_eq_of_surjective` gives the claim. -/
theorem normalizer_sup_le_normalizer_cbar {G : Type*} [Group G] (P : Subgroup G) [P.Normal]
    (V : Subgroup G) :
    Subgroup.normalizer ((V ⊔ P : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.ZJB.Cbar P V : Subgroup G) : Set G) := by
  have hCbar : Work.ZJB.Cbar P V =
      (Subgroup.centralizer ((V.map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) :
        Set (G ⧸ P))).comap (QuotientGroup.mk' P) := rfl
  rw [hCbar, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective P)]
  intro n hn
  rw [Subgroup.mem_comap]
  -- centralizers are normal in their normalizers
  have hnc : Subgroup.normalizer
        ((V.map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) : Set (G ⧸ P)) ≤
      Subgroup.normalizer (Subgroup.centralizer
        ((V.map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) : Set (G ⧸ P)) :
          Set (G ⧸ P)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  apply hnc
  -- `π n` normalizes `(V ⊔ P)/P = V̄`
  have hmap := Subgroup.le_normalizer_map (H := (V ⊔ P : Subgroup G)) (QuotientGroup.mk' P)
  have hn' : (QuotientGroup.mk' P) n ∈
      Subgroup.map (QuotientGroup.mk' P)
        (Subgroup.normalizer ((V ⊔ P : Subgroup G) : Set G)) :=
    Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have hn'' := hmap hn'
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff P).mpr (by rw [QuotientGroup.ker_mk']),
    sup_bot_eq] at hn''
  exact hn''

theorem condExists52 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.CondExists52Prop p G := by
  intro S W hW
  -- `U = W ⊔ P` is a `p`-subgroup contained in `S`
  have hUS : W ⊔ Work.GW2.pCore p G ≤ (S : Subgroup G) :=
    sup_le hW (Work.GW2.pCore_le_sylow S)
  have hUp : IsPGroup p ↥(W ⊔ Work.GW2.pCore p G) := (S.isPGroup').to_le hUS
  -- G4 with `Y = N_G(U)`, `U = W ⊔ P`
  obtain ⟨x, hx1, hx2⟩ := Work.ZJB2.existsConjSylowIn p G S
    (Subgroup.normalizer ((W ⊔ Work.GW2.pCore p G : Subgroup G) : Set G))
    (W ⊔ Work.GW2.pCore p G) Subgroup.le_normalizer hUp
  refine ⟨x, ?_, Or.inr ?_⟩
  · -- `x W x⁻¹ ≤ x (W ⊔ P) x⁻¹ ≤ S`
    exact le_trans (Subgroup.map_mono le_sup_left) hx1
  · -- the right disjunct, with `V = x W x⁻¹`
    have hPeq : Subgroup.map (MulAut.conj x).toMonoidHom (Work.GW2.pCore p G) =
        Work.GW2.pCore p G :=
      Subgroup.Normal.map_conj_eq (Work.GW2.pCore p G) x
    -- `x (W ⊔ P) x⁻¹ = (x W x⁻¹) ⊔ P`
    have hUmap : (W ⊔ Work.GW2.pCore p G).map (MulAut.conj x).toMonoidHom
        = W.map (MulAut.conj x).toMonoidHom ⊔ Work.GW2.pCore p G := by
      rw [Subgroup.map_sup, hPeq]
    -- `N_G(W ⊔ P)^x = N_G(x (W ⊔ P) x⁻¹)`
    have hnorm : (Subgroup.normalizer ((W ⊔ Work.GW2.pCore p G : Subgroup G) : Set G)).map
          (MulAut.conj x).toMonoidHom
        = Subgroup.normalizer
            ((W.map (MulAut.conj x).toMonoidHom ⊔ Work.GW2.pCore p G : Subgroup G) : Set G) := by
      rw [Subgroup.map_equiv_normalizer_eq, hUmap]
    have hSyl' : IsSylowIn p
        (Subgroup.normalizer
            ((W.map (MulAut.conj x).toMonoidHom ⊔ Work.GW2.pCore p G : Subgroup G) : Set G)
          ⊓ (S : Subgroup G))
        (Subgroup.normalizer
            ((W.map (MulAut.conj x).toMonoidHom ⊔ Work.GW2.pCore p G : Subgroup G) : Set G)) := by
      rw [← hnorm]; exact hx2
    -- G2 with `M = N_G(V ⊔ P)`, `L = Cbar P V`
    have hG2 := Work.ZJB2.Step1.sylowInInfNormal hSyl'
      (cbar_le_normalizer_sup (Work.GW2.pCore p G) (W.map (MulAut.conj x).toMonoidHom))
      (normalizer_sup_le_normalizer_cbar (Work.GW2.pCore p G)
        (W.map (MulAut.conj x).toMonoidHom))
    have hTCL : (Subgroup.normalizer
          ((W.map (MulAut.conj x).toMonoidHom ⊔ Work.GW2.pCore p G : Subgroup G) : Set G)
          ⊓ (S : Subgroup G)) ⊓ Work.ZJB.Cbar (Work.GW2.pCore p G)
            (W.map (MulAut.conj x).toMonoidHom)
        = Work.ZJB.Cbar (Work.GW2.pCore p G) (W.map (MulAut.conj x).toMonoidHom)
            ⊓ (S : Subgroup G) := by
      rw [inf_assoc, inf_comm (S : Subgroup G), ← inf_assoc,
        inf_eq_right.mpr (cbar_le_normalizer_sup (Work.GW2.pCore p G) _)]
    rwa [hTCL] at hG2

end Work.ZJB2
