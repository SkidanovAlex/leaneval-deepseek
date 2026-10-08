import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.Step1.sylowInInfNormal
import Submission.Work.ZJB2.existsConjSylowIn

namespace Work.ZJB2

/-!
# ZJB2 leaf `condExists51` — Theorem 5.1, step (IV): existence of `V` with `C_S(V) ∈ Syl_p(C(V))`

`Work.ZJB.CondExists51Prop p G` says: for a Sylow `p`-subgroup `S` of `G` and any `W ≤ S`
there is a conjugate `V = x W x⁻¹ ≤ S` (Mathlib's `W.map (MulAut.conj x).toMonoidHom`) with
`C_S(V) ∈ Syl_p(C(V))`.

**Route** (Glauberman 1968, p. 1120, step (IV)):

* Apply **G4** (`Work.ZJB2.existsConjSylowIn`) with `Y = N_G(W)` and `U = W`, obtaining `x`
  such that `V = x W x⁻¹ ≤ S` and `S ⊓ x N_G(W) x⁻¹ = S ⊓ N_G(V)` is a Sylow `p`-subgroup of
  `N_G(V)` (using `Subgroup.map_equiv_normalizer_eq` for `x N_G(W) x⁻¹ = N_G(V)`);
* Apply **G2** (`Work.ZJB2.Step1.sylowInInfNormal`) with `M = N_G(V)` and `L = C_G(V)`
  (legitimate because `C_G(V) ≤ N_G(V)` and `N_G(V) ≤ N_G(C_G(V))`, the latter being the
  normality of `C_G(V)` in `N_G(V)`).  Since `C_G(V) ≤ N_G(V)`, the intersection
  `(S ⊓ N_G(V)) ⊓ C_G(V)` is just `S ⊓ C_G(V)`, which is therefore a Sylow `p`-subgroup of
  `C_G(V)`.
-/

theorem condExists51 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.CondExists51Prop p G := by
  intro S W hWS
  -- `W ≤ S` is a `p`-subgroup.
  have hWp : IsPGroup p W := S.isPGroup'.to_le hWS
  -- **G4** with `Y = N_G(W)`, `U = W`.
  obtain ⟨x, hxle, hxsyl⟩ :=
    Work.ZJB2.existsConjSylowIn p G S (Subgroup.normalizer (W : Set G)) W
      Subgroup.le_normalizer hWp
  refine ⟨x, hxle, ?_⟩
  -- `x · N_G(W) · x⁻¹ = N_G(V)`, `V = x W x⁻¹`.
  have hYmap : (Subgroup.normalizer (W : Set G)).map (MulAut.conj x).toMonoidHom =
      Subgroup.normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq W (MulAut.conj x)
  have hMsyl : Work.ZJB.IsSylowIn p
      (Subgroup.normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ⊓ (S : Subgroup G))
      (Subgroup.normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) := by
    rw [← hYmap]; exact hxsyl
  -- `N_G(V) ≤ N_G(C_G(V))` (from the normality of `C_G(V)` in `N_G(V)`).
  have hML : Subgroup.normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer
          ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer
        ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G))
  -- **G2** with `M = N_G(V)`, `L = C_G(V)`.
  have hG2 := Work.ZJB2.Step1.sylowInInfNormal hMsyl
      (Subgroup.centralizer_le_normalizer
        ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) hML
  -- `C_G(V) ≤ N_G(V)`, so `(S ⊓ N_G(V)) ⊓ C_G(V) = C_G(V) ⊓ S`.
  have heq : (Subgroup.normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ⊓ (S : Subgroup G)) ⊓
        Subgroup.centralizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
      Subgroup.centralizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
    rw [inf_assoc, inf_eq_right.mpr
      (le_trans inf_le_right (Subgroup.centralizer_le_normalizer _)), inf_comm]
  rw [heq] at hG2
  exact hG2

end Work.ZJB2
