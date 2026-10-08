import Mathlib
import Submission.Work.AUTA7.A7.D16MaxIntersect

namespace Work.AUTA7.A7

set_option linter.style.haveILetI false

/-!
# The four-group contradiction

Let `Q` be a group with a Sylow `2`-subgroup `P₁ ≅ D₁₆ = DihedralGroup 8` (of order `16`),
let `L ≤ Q`, and suppose `T ≤ P₁` has order `8` while `P₁ ⊓ L` also has order `8`.  If
`T ⊓ L` is a Klein four-group (order `4`, exponent `2`) then `T = P₁ ⊓ L`.

The mathematical content is the following.  `V = T ⊓ L` is contained both in `T` and in
`P₁ ⊓ L` (it lies in `P₁` because `T ≤ P₁`), and `V = T ⊓ (P₁ ⊓ L)`.  Two distinct subgroups of
order `8` in `D₁₆` meet in a cyclic group (`D16MaxIntersect`), but every cyclic subgroup of order
`4` contains an element of order `4`, contradicting the exponent `2` of `V`.
-/
theorem contradiction_of_four_group {Q : Type*} [Group Q] (L : Subgroup Q) (P₁ : Sylow 2 Q)
    (e : ↥(P₁ : Subgroup Q) ≃* DihedralGroup 8) (T : Subgroup Q)
    (hTle : T ≤ (P₁ : Subgroup Q)) (hTcard : Nat.card ↥T = 8)
    (hDcard : Nat.card ↥((P₁ : Subgroup Q) ⊓ L) = 8) (hne : T ≠ (P₁ : Subgroup Q) ⊓ L)
    (hVcard : Nat.card ↥(T ⊓ L) = 4) (hVexp : ∀ v ∈ T ⊓ L, v ^ 2 = 1) : False := by
  set P : Subgroup Q := (P₁ : Subgroup Q) with hP
  set D : Subgroup Q := P ⊓ L with hD
  set V : Subgroup Q := T ⊓ L with hV
  have hDle : D ≤ P := by rw [hD]; exact inf_le_left
  -- `V` is exactly the intersection of `T` with `P₁ ⊓ L`
  have hVD : V = T ⊓ D := by
    rw [hV, hD]
    refine le_antisymm ?_ ?_
    · intro x hx
      exact ⟨hx.1, ⟨hTle hx.1, hx.2⟩⟩
    · intro x hx
      exact ⟨hx.1, hx.2.2⟩
  -- the images of `T` and `D` under `e` inside `DihedralGroup 8`
  set A : Subgroup (DihedralGroup 8) := (T.subgroupOf P).map e.toMonoidHom with hA
  set B : Subgroup (DihedralGroup 8) := (D.subgroupOf P).map e.toMonoidHom with hB
  have hcardTsub : Nat.card ↥(T.subgroupOf P) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
  have hcardDsub : Nat.card ↥(D.subgroupOf P) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
  have hAcard : Nat.card A = 8 := by
    rw [hA, Subgroup.card_map_of_injective e.injective, hcardTsub, hTcard]
  have hBcard : Nat.card B = 8 := by
    rw [hB, Subgroup.card_map_of_injective e.injective, hcardDsub, hDcard]
  -- distinctness of the two order-`8` subgroups
  have hAneB : A ≠ B := by
    intro hAB
    apply hne
    have h1 : T.subgroupOf P = D.subgroupOf P :=
      Subgroup.map_injective e.injective (by rw [← hA, ← hB]; exact hAB)
    calc T = T ⊓ P := (inf_eq_left.mpr hTle).symm
      _ = (T.subgroupOf P).map P.subtype := (Subgroup.subgroupOf_map_subtype T P).symm
      _ = (D.subgroupOf P).map P.subtype := by rw [h1]
      _ = D ⊓ P := Subgroup.subgroupOf_map_subtype D P
      _ = D := inf_eq_left.mpr hDle
  -- `A ⊓ B` is the image of `V`
  have hsub : (T ⊓ D).subgroupOf P = T.subgroupOf P ⊓ D.subgroupOf P := by
    show Subgroup.comap P.subtype (T ⊓ D) =
      Subgroup.comap P.subtype T ⊓ Subgroup.comap P.subtype D
    rw [Subgroup.comap_inf]
  have hAB : A ⊓ B = ((T ⊓ D).subgroupOf P).map e.toMonoidHom := by
    rw [hA, hB,
      ← Subgroup.map_inf (T.subgroupOf P) (D.subgroupOf P) e.toMonoidHom e.injective, hsub]
  have hABcard : Nat.card ↥(A ⊓ B) = 4 := by
    rw [hAB, Subgroup.card_map_of_injective e.injective]
    have hcp : Nat.card ↥((T ⊓ D).subgroupOf P) = Nat.card ↥(T ⊓ D) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hTle)).toEquiv
    rw [hcp, ← hVD]
    exact hVcard
  -- every element of `A ⊓ B` squares to `1`
  have hexp : ∀ m : DihedralGroup 8, m ∈ A ⊓ B → m ^ 2 = 1 := by
    intro m hm
    rw [hAB] at hm
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hm
    have hvD : ((v : ↥P) : Q) ∈ T ⊓ D := Subgroup.mem_subgroupOf.mp hv
    have hvV : ((v : ↥P) : Q) ∈ V := by rw [hVD]; exact hvD
    have h1 : ((v : ↥P) : Q) ^ 2 = 1 := hVexp _ hvV
    have hv2 : v ^ 2 = 1 := Subtype.ext h1
    rw [← map_pow, hv2, map_one]
  have hABexp : ∀ m : ↥(A ⊓ B), m ^ 2 = 1 := fun m => Subtype.ext (hexp m m.2)
  -- a cyclic group of order `4` cannot have exponent `2`
  haveI : IsCyclic ↥(A ⊓ B) := D16MaxIntersect A B hAcard hBcard hAneB
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(A ⊓ B))
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
  have hord : orderOf g = 4 := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top, hABcard]
  have hg2 : g ^ 2 = 1 := hABexp g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Work.AUTA7.A7
