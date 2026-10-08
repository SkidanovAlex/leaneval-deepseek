import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.isSylowInOfLe
import Submission.Work.ZJB2.Assembly

/-!
# gorenstein_walter, ZJB2 — the leaf `case52Proper` (`T52.lt`)

Source: Glauberman 1968, p. 1121, the case `C_G(P)·S < G` (`P = O_p(G)`).

`Case52ProperProp p G` says: if `G = C_G(P)·N_G(Z(J(S)))` for every element, and `(C_p*)`
holds in the subgroup `M = C_G(P) ⊔ S`, then `N_G(Z(J(S)))` controls strong fusion in `S`.

**Route.**  Given `W ≤ S` and `g` with `W^g ⊆ S`, write `g = d n` with `d ∈ C_G(P)` and
`n ∈ N_G(Z(J(S)))`.  Then `d⁻¹ W d = n (W^g) n⁻¹ ⊆ n S n⁻¹ ⊆ N_G(Z(J(S)))` (as `n` and `S`
both lie in `N_G(Z(J(S)))`).  Now `W ≤ M`, `W ≤ N_G(Z(J(S)))`, `W` is a `p`-group and
`d ∈ M`, so `(C_p*)` in `M` (at the Sylow subgroup `S` of `M`, G3) gives `d = c m` with
`c ∈ C_G(W)` and `m ∈ N_G(Z(J(S)))`.  Then `g = c·(m n)` with `c ∈ C_G(W)`,
`m n ∈ N_G(Z(J(S)))`.
-/

namespace Work.ZJB2

open Work.ZJB
open Work.GW2
open Subgroup

theorem case52Proper (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.Case52ProperProp p G := by
  intro S hGCN hCS
  apply Work.ZJB.cpPaper_of_goodFor
  intro W hW
  intro g hg
  obtain ⟨d, hdC, n₀, hn₀, hgeq⟩ := hGCN g
  have hSyl : Work.ZJB.IsSylowIn p (S : Subgroup G)
      (centralizer (pCore p G : Set G) ⊔ (S : Subgroup G)) :=
    isSylowInOfLe p G S _ le_sup_right
  have hWM : W ≤ centralizer (pCore p G : Set G) ⊔ (S : Subgroup G) := hW.trans le_sup_right
  have hWN : W ≤ normalizer (ZJ (S : Subgroup G) : Set G) :=
    hW.trans (le_normalizer_ZJ (S : Subgroup G))
  have hWp : IsPGroup p W := S.isPGroup'.to_le hW
  have hdM : d ∈ centralizer (pCore p G : Set G) ⊔ (S : Subgroup G) :=
    Subgroup.mem_sup_left hdC
  have hdcond : ∀ w ∈ W, d⁻¹ * w * d ∈ normalizer (ZJ (S : Subgroup G) : Set G) := by
    intro w hw
    have hs : g⁻¹ * w * g ∈ (S : Subgroup G) := hg w hw
    have hSle : (S : Subgroup G) ≤ normalizer (ZJ (S : Subgroup G) : Set G) :=
      le_normalizer_ZJ _
    have hEq : d⁻¹ * w * d = n₀ * (g⁻¹ * w * g) * n₀⁻¹ := by
      rw [hgeq]; group
    rw [hEq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₀ (hSle hs)) (Subgroup.inv_mem _ hn₀)
  obtain ⟨c, n, _, hcW, _, hnN, hdeq⟩ :=
    hCS (S : Subgroup G) hSyl W hWM hWN hWp d hdM hdcond
  exact ⟨c, n * n₀, hcW, Subgroup.mul_mem _ hnN hn₀, by rw [hgeq, hdeq, mul_assoc]⟩

end Work.ZJB2
