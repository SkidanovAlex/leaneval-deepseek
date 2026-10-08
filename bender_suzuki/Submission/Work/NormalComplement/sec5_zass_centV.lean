import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.centV_le_A
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement

namespace Work.NormalComplement

/-- The image of `O^{2'}(C)` in `G` (along `Subtype.val`) lies in `C`. -/
private lemma oddResidual_map_subtype_le {G : Type} [Group G] (C : Subgroup G) :
    (Submission.Blueprint.oddResidual ↥C).map C.subtype ≤ C := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- **`C_P(A) = 1` in the §5 configuration.** `P` has prime order `p` (`h.P_card`, `h.prime`), so
`P ⊓ C_G(A)`, a subgroup of `P`, is either `⊥` or `P`; it is not `P` because `P ≤ C_G(A)` would
force `⁅A, P⁆ = ⊥`, whereas `h.E'V` and the third conjunct of (D2) give `⁅A, P⁆ = E' ⊓ V ≠ ⊥`. -/
private lemma setup5_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    P ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  have hE'ne : ⁅A, P⁆ ≠ ⊥ := fun hbot => h.d2.2.2 (h.E'V.trans hbot)
  by_contra hne
  have hdvd : Nat.card ↥(P ⊓ Subgroup.centralizer (A : Set G)) ∣ p := by
    rw [← h.P_card]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases h.prime.eq_one_or_self_of_dvd _ hdvd with h1 | h2
  · refine hne ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hdvd1 : Nat.card ↥(Subgroup.zpowers x) ∣ 1 := by
      rw [← h1]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
    rw [Nat.card_zpowers] at hdvd1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  · have heq : P ⊓ Subgroup.centralizer (A : Set G) = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, h.P_card])
    have hPleC : P ≤ Subgroup.centralizer (A : Set G) := heq ▸ inf_le_right
    have hAleCP : A ≤ Subgroup.centralizer (P : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (hPleC hy)) a ha).symm
    exact hE'ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAleCP)

/-- **`p ∤ |A|` in the §5 configuration.** `P` is a Sylow `p`-subgroup of `D = twoPoint H t`
(`h.P_syl`) and `P ≤ V = centD H t ≤ D`, so `p ∤ |V : P|`; and `V = A ⊔ P` with `A ⊓ P = ⊥` gives
`|V : P| = |A|`. -/
private lemma setup5_not_dvd_card_A {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ¬ p ∣ Nat.card ↥A := by
  have hP_le_V : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hV_le_D : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t := inf_le_left
  have hPsyl : IsSylowIn p P (Submission.Blueprint.centD H t) :=
    sylowIn_of_le_of_le h.P_syl hP_le_V hV_le_D
  have hcardV : Nat.card ↥(Submission.Blueprint.centD H t) = Nat.card ↥A * p := by
    have h1 := card_sup_mul_card_inf (H := A) (K := P) (hP_le_V.trans h.A_normal)
    rw [h.A_sup, h.A_inf, h.P_card] at h1
    simpa using h1
  have hindex : (P.subgroupOf (Submission.Blueprint.centD H t)).index = Nat.card ↥A := by
    have h1 := Subgroup.index_mul_card (P.subgroupOf (Submission.Blueprint.centD H t))
    have h2 : Nat.card ↥(P.subgroupOf (Submission.Blueprint.centD H t)) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_V).toEquiv
    rw [h2, h.P_card, hcardV] at h1
    exact Nat.eq_of_mul_eq_mul_right h.prime.pos h1
  rw [← hindex]
  exact hPsyl.2.2

theorem sec5_zass_centV (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    let C : Subgroup G := Subgroup.centralizer (A : Set G)
    let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
    ∀ x : ↥F₀, (x : G) ∈ Submission.Blueprint.centD H t → x ∈ Subgroup.center ↥F₀ := by
  classical
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
  change ∀ x : ↥F₀, (x : G) ∈ Submission.Blueprint.centD H t → x ∈ Subgroup.center ↥F₀
  intro x hxV
  have hF₀_le_C : F₀ ≤ C := oddResidual_map_subtype_le C
  have hxC : (x : G) ∈ C := hF₀_le_C x.2
  have hxA : (x : G) ∈ A :=
    centV_le_A h.A_normal h.A_sup
      (by rw [h.P_card]
          exact h.prime.coprime_iff_not_dvd.mpr (setup5_not_dvd_card_A h))
      (setup5_inf_centralizer_eq_bot h) ⟨hxV, hxC⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hyC : (y : G) ∈ C := hF₀_le_C y.2
  exact (Subgroup.mem_centralizer_iff.mp hyC (x : G) hxA).symm

end Work.NormalComplement
