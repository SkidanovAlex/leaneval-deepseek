import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.prop4b_S_le_centralizer
import Submission.Work.ThreePoints.maximal_isPGroup_of_normal_twoGroup_compl
import Submission.Work.GlaubermanZJ.Thm41.lowerCentralSeries_le_iterComm_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThreePoints

open Submission.Blueprint

/-! ### The Sylow step of Peterfalvi I Ch. II §4 Prop. 4 (b)

We prove a general group-theoretic statement in the ambient group: if `S` is a `2`-subgroup of `G`
normalised by a subgroup `NC ≤ G`, `NC = S ⊔ V` with `S ⊓ V = ⊥`, `p` is an odd prime and
`X ≤ V` is maximal among the `p`-subgroups of `V`, then `X` is maximal among the `p`-subgroups of
`NC`.  The `p`-group-theoretic core (maximality transfers through the quotient by the normal
`2`-subgroup `S`) is `Work.ThreePoints.maximal_isPGroup_of_normal_twoGroup_compl`; here we
translate it to subgroups of `G` via the inclusion `≤ NC`. -/

/-- **Sylow step, ambient-group form.**  If `S ≤ NC`, `V ≤ NC`, `NC = S ⊔ V`, `S ⊓ V = ⊥`, `S` is
a `2`-subgroup normalised by `NC`, `p` is an odd prime, and `X ≤ V` is maximal among the
`p`-subgroups of `V`, then `X` is maximal among the `p`-subgroups of `NC`. -/
theorem maximal_p_of_normal_twoGroup_compl {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {S V X NC : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSleNC : S ≤ NC) (hVleNC : V ≤ NC)
    (hNCnorm : NC ≤ Subgroup.normalizer (S : Set G)) (hsup : S ⊔ V = NC) (hdisj : S ⊓ V = ⊥)
    (hXp : IsPGroup p X) (hXleV : X ≤ V)
    (hXmax : ∀ Y : Subgroup G, X ≤ Y → Y ≤ V → IsPGroup p Y → Y = X) :
    ∀ Z : Subgroup G, X ≤ Z → Z ≤ NC → IsPGroup p Z → Z = X := by
  intro Z hXZ hZleNC hZp
  have hXleNC : X ≤ NC := le_trans hXleV hVleNC
  have hmap_top : Subgroup.map NC.subtype (⊤ : Subgroup ↥NC) = NC := by
    refine le_antisymm (Subgroup.map_subtype_le (⊤ : Subgroup ↥NC)) ?_
    intro g hg
    exact ⟨⟨g, hg⟩, trivial, rfl⟩
  -- in `↥NC`: `S₀ ⊔ V₀ = ⊤`
  have hsup₀ : S.subgroupOf NC ⊔ V.subgroupOf NC = ⊤ := by
    apply Subgroup.map_injective NC.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hSleNC, inf_eq_left.mpr hVleNC, hmap_top, hsup]
  have hSnorm₀ : (S.subgroupOf NC).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSleNC).mpr hNCnorm
  have hdisj₀ : Disjoint (S.subgroupOf NC) (V.subgroupOf NC) := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxV
    have hx : (x : G) ∈ S ⊓ V := ⟨hxS, hxV⟩
    rw [hdisj] at hx
    exact Subtype.ext (Subgroup.mem_bot.mp hx)
  have hS2₀ : IsPGroup 2 (S.subgroupOf NC) := by
    rw [← Subgroup.comap_subtype S NC]
    exact hS2.comap_of_injective NC.subtype NC.subtype_injective
  have hXp₀ : IsPGroup p (X.subgroupOf NC) := by
    rw [← Subgroup.comap_subtype X NC]
    exact hXp.comap_of_injective NC.subtype NC.subtype_injective
  have hXleV₀ : X.subgroupOf NC ≤ V.subgroupOf NC := fun x hx => hXleV hx
  -- maximality of `X` in `V` transfers to `↥NC`
  have hXmax₀ : ∀ Y : Subgroup ↥NC, X.subgroupOf NC ≤ Y → Y ≤ V.subgroupOf NC →
      IsPGroup p Y → Y = X.subgroupOf NC := by
    intro Y hXY hYV hYp
    have hY'map : Subgroup.map NC.subtype Y = X := by
      refine hXmax (Subgroup.map NC.subtype Y) ?_ ?_ (hYp.map NC.subtype)
      · intro x hx
        exact ⟨⟨x, hXleNC hx⟩,
          hXY (show (⟨x, hXleNC hx⟩ : ↥NC) ∈ X.subgroupOf NC from hx), rfl⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        exact hYV hz
    calc Y = Subgroup.comap NC.subtype (Subgroup.map NC.subtype Y) :=
          (Subgroup.comap_map_eq_self_of_injective NC.subtype_injective Y).symm
      _ = Subgroup.comap NC.subtype X := by rw [hY'map]
      _ = X.subgroupOf NC := Subgroup.comap_subtype X NC
  have hkey := maximal_isPGroup_of_normal_twoGroup_compl hp hp2 hS2₀ hSnorm₀ hsup₀ hdisj₀
    hXp₀ hXleV₀ hXmax₀
  have hZp₀ : IsPGroup p (Z.subgroupOf NC) := by
    rw [← Subgroup.comap_subtype Z NC]
    exact hZp.comap_of_injective NC.subtype NC.subtype_injective
  have hZ₀ : Z.subgroupOf NC = X.subgroupOf NC :=
    hkey (Z.subgroupOf NC) (fun x hx => hXZ hx) hZp₀
  have hmap_eq : Subgroup.map NC.subtype (Z.subgroupOf NC) =
      Subgroup.map NC.subtype (X.subgroupOf NC) := by rw [hZ₀]
  have hZ1 : Subgroup.map NC.subtype (Z.subgroupOf NC) = Z := by
    rw [Subgroup.subgroupOf_map_subtype Z NC, inf_eq_left.mpr hZleNC]
  have hX1 : Subgroup.map NC.subtype (X.subgroupOf NC) = X := by
    rw [Subgroup.subgroupOf_map_subtype X NC, inf_eq_left.mpr hXleNC]
  rw [hZ1, hX1] at hmap_eq
  exact hmap_eq

/-- The "`X` is a Sylow `p`-subgroup of `C_H(Inv H)`" step of Peterfalvi I Ch. II §4 Prop. 4 (b)
(p. 171).  With `D = H ∩ H^t`, `K = J(D,t)`, `C = C_H(Inv H)` and `W = D ⊓ C = C_V(K)`: if
`X ∈ Syl_p(W)` (`p` odd), `S ≤ C` is the `2`-subgroup of Prop. 3 (b) with
`N_H(X) = S ⋊ N_D(X)`, then `X ∈ Syl_p(C)`.

Mathematical argument (source, p. 171: "`N_H(X) ∩ C_H(Inv H) = S ⋊ (N_D(X) ∩ C_D(Inv H))`;
hence `X` is a Sylow subgroup of `C_H(Inv H)`"):
* `N_C(X) = N_H(X) ⊓ C = S ⊔ (W ⊓ N(X))`, because `N_H(X) = S ⊔ (D ⊓ N(X))` and `S ≤ C`;
* `S ⊓ (W ⊓ N(X)) = ⊥` (as `S ⊓ D = ⊥`), so `|N_C(X)| = |S| · |W ⊓ N(X)|`;
* `X` is a maximal `p`-subgroup of `W ⊓ N(X)` (it is one of `W ⊇ W ⊓ N(X)`), so the `p`-part of
  `|N_C(X)|` equals `|X|` (as `p ∤ |S|`, `p` odd), i.e. `X ∈ Syl_p(N_C(X))`;
* a maximal `p`-subgroup of `N_C(X)` is maximal in `C`: if `Y ≤ C` is a `p`-subgroup with
  `X ≤ Y`, then `N_Y(X)` is a `p`-subgroup of `N_C(X)` containing `X`, hence equals `X`; since a
  proper subgroup of a `p`-group is properly contained in its normalizer inside that `p`-group,
  `Y = X` follows.

Reviewers note `hH`, `ht`, `htH` are not needed by this argument (they are carried for uniformity
of call sites); `hSN` and `hNS` are used (the latter gives the normality of `S` inside
`H ⊓ N_G(X)`, needed to decompose `N_H(X) = S ⊔ N_D(X)` into products).  Useful helpers:
`Subgroup.inf_normalizer`, `Subgroup.card_mul_index`, `IsPGroup.of_card`, `Nat.card_congr`. -/
theorem prop4b_X_sylow {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (S X : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (X : Set G))
    (hNS : H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hSD : S ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    (hA : S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G))
    (hSleC : S ≤ H ⊓ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)))
    (hXp : IsPGroup p X)
    (hXW : X ≤ Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)))
    (hXsylW : ∀ Y : Subgroup G, X ≤ Y →
        Y ≤ Submission.Blueprint.twoPoint H t ⊓
          Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) →
        IsPGroup p Y → Y = X) :
    ∀ Y : Subgroup G, X ≤ Y → Y ≤ H ⊓ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) →
      IsPGroup p Y → Y = X := by
  set C : Subgroup G := H ⊓ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G))
    with hCdef
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hDdef
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hNdef
  set W : Subgroup G := D ⊓ C with hWdef
  set V : Subgroup G := W ⊓ N with hVdef
  set NC : Subgroup G := C ⊓ N with hNCdef
  -- `W` coincides with the statement's `D ⊓ C_H(Inv H)`
  have hW_eq : W = Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    rw [hWdef, hDdef, hCdef, ← inf_assoc, inf_eq_left.mpr inf_le_left]
  have hXW' : X ≤ W := hW_eq ▸ hXW
  have hXsylW' : ∀ Y : Subgroup G, X ≤ Y → Y ≤ W → IsPGroup p Y → Y = X :=
    fun Y h1 h2 h3 => hXsylW Y h1 (hW_eq ▸ h2) h3
  have hXleV : X ≤ V := le_inf hXW' Subgroup.le_normalizer
  have hWV : W ≤ D := by rw [hWdef]; exact inf_le_left
  have hCleH : C ≤ H := by rw [hCdef]; exact inf_le_left
  -- `S ⊓ V = ⊥`, from `S ⊓ D = ⊥`
  have hdisjV : S ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [← hSD]
    exact ⟨hg.1, hWV hg.2.1⟩
  -- `S ≤ C ⊓ N` and `W ⊓ N ≤ C ⊓ N`
  have hSleNC : S ≤ NC := by rw [hNCdef]; exact le_inf hSleC hSN
  have hVleNC : V ≤ NC := by
    rw [hNCdef, hVdef, hWdef]
    exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right
  have hNCleHN : NC ≤ H ⊓ N := by
    rw [hNCdef]
    exact le_inf (le_trans inf_le_left hCleH) inf_le_right
  -- `C ⊓ N = S ⊔ (W ⊓ N)`
  have hsup : S ⊔ V = NC := by
    apply le_antisymm
    · exact sup_le hSleNC hVleNC
    · intro g hg
      rw [hNCdef] at hg
      have hgC : g ∈ C := hg.1
      have hgN : g ∈ N := hg.2
      have hgH : g ∈ H := hCleH hgC
      have hg'' : g ∈ S ⊔ (D ⊓ N) := by rw [hA]; exact ⟨hgH, hgN⟩
      have hg' : g ∈ (D ⊓ N) ⊔ S := by rw [sup_comm]; exact hg''
      have hDH : D ≤ H := by rw [hDdef]; exact inf_le_left
      have hDNleHN : D ⊓ N ≤ H ⊓ N := fun x hx => ⟨hDH hx.1, hx.2⟩
      have hDNnorm : D ⊓ N ≤ Subgroup.normalizer (S : Set G) := le_trans hDNleHN hNS
      obtain ⟨d, hd, s, hs, hds⟩ :=
        (Work.GlaubermanZJ.Thm41.mem_sup_of_le_normalizer hDNnorm (x := g)).mp hg'
      have hdC : d ∈ C := by
        have h1 : d = g * s⁻¹ := by rw [← hds]; group
        rw [h1]
        exact Subgroup.mul_mem C hgC (Subgroup.inv_mem C (hSleC hs))
      have hdV : d ∈ V := ⟨⟨hd.1, hdC⟩, hd.2⟩
      have : g ∈ V ⊔ S := by
        rw [← hds]
        exact Subgroup.mul_mem_sup hdV hs
      rwa [sup_comm] at this
  have hkey : ∀ Z : Subgroup G, X ≤ Z → Z ≤ NC → IsPGroup p Z → Z = X :=
    maximal_p_of_normal_twoGroup_compl hp hp2 hS2 hSleNC hVleNC (le_trans hNCleHN hNS)
      hsup hdisjV hXp hXleV (fun Y h1 h2 h3 => hXsylW' Y h1 (le_trans h2 inf_le_left) h3)
  intro Y hXY hYC hYp
  by_contra hne
  have hlt : X < Y := lt_of_le_of_ne hXY (Ne.symm hne)
  -- `Y ⊓ N_G(X) = X` by the Sylow step, so `X < Y ⊓ N_G(X)` contradicts the normalizer condition
  have hMleNC : Y ⊓ N ≤ NC := by
    rw [hNCdef]
    exact le_inf (le_trans inf_le_left hYC) inf_le_right
  have hMp : IsPGroup p ↥(Y ⊓ N) := hYp.to_le inf_le_left
  have hM : Y ⊓ N = X := hkey (Y ⊓ N) (le_inf hXY Subgroup.le_normalizer) hMleNC hMp
  have hfact : Fact p.Prime := ⟨hp⟩
  have hcontra : X < Y ⊓ N :=
    @Work.Coprime.lt_inf_normalizer_of_lt G _ _ p hfact X Y hYp hlt
  rw [hM] at hcontra
  exact absurd hcontra (lt_irrefl X)

end Work.ThreePoints
