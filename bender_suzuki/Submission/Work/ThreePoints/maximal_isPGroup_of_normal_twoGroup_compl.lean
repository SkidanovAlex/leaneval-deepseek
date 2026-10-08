import Mathlib
import Submission.Work.ThreePoints.card_map_eq_card_of_disjoint_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- If `f` is injective on `V` (its kernel meets `V` trivially) and `L` is contained in the
preimage of a `p`-subgroup `T`, then `L ⊓ V` is a `p`-subgroup: the restriction of `f` to
`L ⊓ V` is injective into the `p`-group `T`. -/
private theorem isPGroup_inf_of_le_comap_aux {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) {V : Subgroup G} (hV : Disjoint V f.ker) {T : Subgroup H}
    (hT : IsPGroup p ↥T) {L : Subgroup G} (hL : L ≤ T.comap f) :
    IsPGroup p ↥(L ⊓ V) := by
  have hle : L ⊓ V ≤ T.comap f := le_trans inf_le_left hL
  refine IsPGroup.of_injective hT ((f.comp (L ⊓ V).subtype).codRestrict T ?_) ?_
  · intro x
    simpa using hle x.2
  · intro x y hxy
    have h1 : f x.1 = f y.1 := by
      have h2 := congrArg Subtype.val hxy
      simpa using h2
    have h2 : x.1 * y.1⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have h3 : x.1 * y.1⁻¹ ∈ V :=
      V.mul_mem x.2.2 (V.inv_mem y.2.2)
    have h4 : x.1 * y.1⁻¹ = 1 := by
      have hbot : x.1 * y.1⁻¹ ∈ (⊥ : Subgroup G) := hV.le_bot ⟨h3, h2⟩
      rwa [Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp h4)

/-- If `S ⊔ V = ⊤` with `S` normal and `S ≤ L`, then `L = S ⊔ (L ⊓ V)`. -/
private theorem eq_sup_inf_of_sup_eq_top_aux {G : Type*} [Group G] {S V L : Subgroup G}
    (hSnorm : S.Normal) (hsup : S ⊔ V = ⊤) (hSL : S ≤ L) :
    L = S ⊔ (L ⊓ V) := by
  haveI := hSnorm
  refine le_antisymm ?_ (sup_le hSL inf_le_left)
  intro x hx
  have hxSV : x ∈ S ⊔ V := by rw [hsup]; trivial
  obtain ⟨s, hs, v, hv, hsv⟩ := Subgroup.mem_sup_of_normal_left.mp hxSV
  have hvL : v ∈ L := by
    have hveq : v = s⁻¹ * x := by rw [← hsv]; group
    rw [hveq]
    exact L.mul_mem (L.inv_mem (hSL hs)) hx
  exact Subgroup.mem_sup_of_normal_left.mpr ⟨s, hs, v, ⟨hvL, hv⟩, hsv⟩

/-- **Key abstract step (Peterfalvi I Ch. II §4 Prop. 4 (b), the Sylow step).**
Let `S ⊴ P` be a `2`-subgroup with a complement `V` (i.e. `S ⊔ V = ⊤` and `S ⊓ V = ⊥`), let `p`
be an odd prime, and let `X ≤ V` be a maximal `p`-subgroup of `V`.  Then `X` is a maximal
`p`-subgroup of `P`.

Proof (sketch): let `π : P →* P ⧸ S`.  For a `p`-subgroup `T ≤ P ⧸ S` with `π(X) ≤ T`, put
`L := π⁻¹(T)`.  Every `x ∈ L` is `s * v` with `s ∈ S`, `v ∈ V`, and then `π v = π x ∈ T`, so
`v ∈ L ⊓ V`; hence `L = S ⊔ (L ⊓ V)`.  Moreover `L ⊓ V` is a `p`-group: the restriction of `π`
to `L ⊓ V` is injective (its kernel meets `V` trivially) with image `T`.  So `L ⊓ V = X` by
maximality of `X` in `V`, and `T = π(L) = π(L ⊓ V) = π(X)`: thus `π(X)` is maximal among the
`p`-subgroups of `P ⧸ S`.  Now if `Z ≤ P` is a `p`-subgroup with `X ≤ Z`, then `π(Z) = π(X)`,
so `Z ≤ π⁻¹(π(X)) = X ⊔ S`; as `Z ⊓ S = ⊥` (a `p`-group meets a `2`-group trivially for odd `p`)
we get `|Z| = |π(Z)| = |π(X)| = |X|`, whence `Z = X`. -/
theorem maximal_isPGroup_of_normal_twoGroup_compl {P : Type*} [Group P] [Finite P]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S V X : Subgroup P}
    (hS2 : IsPGroup 2 S) (hSnorm : S.Normal) (hsup : S ⊔ V = ⊤) (hdisj : Disjoint S V)
    (hXp : IsPGroup p X) (hXle : X ≤ V)
    (hXmax : ∀ Y : Subgroup P, X ≤ Y → Y ≤ V → IsPGroup p Y → Y = X) :
    ∀ Z : Subgroup P, X ≤ Z → IsPGroup p Z → Z = X := by
  haveI := hSnorm
  intro Z hXZ hZp
  let π : P →* P ⧸ S := QuotientGroup.mk' S
  have hker : π.ker = S := QuotientGroup.ker_mk' S
  have hdisjVπ : Disjoint V π.ker := by rw [hker]; exact hdisj.symm
  -- `p` is coprime to `2`
  have hpCop : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hd) hp.two_le))
  have hXS : X ⊓ S = ⊥ := (IsPGroup.disjoint_of_coprime hXp hS2 hpCop).eq_bot
  have hZS : Z ⊓ S = ⊥ := (IsPGroup.disjoint_of_coprime hZp hS2 hpCop).eq_bot
  -- `π(X)` is maximal among the `p`-subgroups of `P ⧸ S`
  have hmaxπ : ∀ T : Subgroup (P ⧸ S), X.map π ≤ T → IsPGroup p T → T = X.map π := by
    intro T hXT hTp
    have hS_le : S ≤ T.comap π := by
      intro s hs
      have hs' : π s = 1 := by
        have : s ∈ π.ker := by rw [hker]; exact hs
        rwa [MonoidHom.mem_ker] at this
      show π s ∈ T
      rw [hs']
      exact T.one_mem
    have hLV : T.comap π ⊓ V = X := by
      refine hXmax (T.comap π ⊓ V) ?_ inf_le_right ?_
      · exact le_inf (Subgroup.map_le_iff_le_comap.mp hXT) hXle
      · exact isPGroup_inf_of_le_comap_aux π hdisjVπ hTp (L := T.comap π) le_rfl
    have hL : T.comap π = S ⊔ X := by
      have h := eq_sup_inf_of_sup_eq_top_aux hSnorm hsup hS_le
      rwa [hLV] at h
    have hmapS : S.map π = ⊥ := (Subgroup.map_eq_bot_iff S).mpr (le_of_eq hker.symm)
    have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective S)
    calc T = π.range ⊓ T := by rw [hrange, top_inf_eq]
      _ = (T.comap π).map π := (Subgroup.map_comap_eq π T).symm
      _ = (S ⊔ X).map π := by rw [hL]
      _ = S.map π ⊔ X.map π := Subgroup.map_sup S X π
      _ = ⊥ ⊔ X.map π := by rw [hmapS]
      _ = X.map π := bot_sup_eq _
  -- hence `π(Z) = π(X)`
  have hZmap : Z.map π = X.map π := hmaxπ (Z.map π) (Subgroup.map_mono hXZ) (hZp.map π)
  -- cardinality: `π` is injective on `Z` and on `X`
  have hZcard : Nat.card ↥Z = Nat.card ↥(Z.map π) :=
    (card_map_eq_card_of_disjoint_ker π Z (disjoint_iff.mpr (by rw [hker]; exact hZS))).symm
  have hXcard : Nat.card ↥(X.map π) = Nat.card ↥X :=
    card_map_eq_card_of_disjoint_ker π X (disjoint_iff.mpr (by rw [hker]; exact hXS))
  have hcard : Nat.card ↥Z ≤ Nat.card ↥X := by rw [hZcard, hZmap, hXcard]
  exact (Subgroup.eq_of_le_of_card_ge hXZ hcard).symm

end Work.ThreePoints
