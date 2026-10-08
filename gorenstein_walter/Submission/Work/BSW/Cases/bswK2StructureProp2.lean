import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.bswK2Complement
import Submission.Work.BSW.Cases.bswK2Involution
import Submission.Work.BSW.Cases.bswK2SylowFive
import Submission.Work.BSW.Cases.bswK2CentralizerSylowFive
import Submission.Work.BSW.Api.prime_card_inf_conjSub_eq_bot
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.CardSup

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-! ## Elementary auxiliary facts

Three self-contained group-theoretic lemmas used in the assembly below. -/

/-- A non-trivial subgroup of a group of order `2` is that group. -/
theorem normalizer_eq_normalizer_of_le_of_ne_bot_card_two {G : Type} [Group G]
    [Finite G] {D X : Subgroup G} (hD : Nat.card ↥D = 2) (hX : X ≤ D) (hne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) = Subgroup.normalizer (D : Set G) := by
  have h1 : Nat.card ↥X ∣ 2 := by
    have h' := Subgroup.card_dvd_of_le hX
    rwa [hD] at h'
  have h2 : Nat.card ↥X ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have h3 : Nat.card ↥X = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd h h2
    · exact h
  have hXeq : X = D := Subgroup.eq_of_le_of_card_ge hX (le_of_eq (by rw [h3, hD]))
  rw [hXeq]

/-- If `P` has order `5` and `w` is an involution normalizing `P`, then `P ⊔ ⟨w⟩` has order
`10 = 5 * 2`: the two subgroups have coprime orders, so they meet trivially. -/
theorem card_sup_sylow_zpowers_of_orderOf_two {G : Type} [Group G] [Finite G]
    {P : Subgroup G} {w : G} (hP : Nat.card ↥P = 5) (hw : orderOf w = 2)
    (hwN : w ∈ Subgroup.normalizer (P : Set G)) :
    Nat.card ↥(P ⊔ Subgroup.zpowers w) = 10 := by
  have hle : Subgroup.zpowers w ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hwN
  have hinf : P ⊓ Subgroup.zpowers w = ⊥ := by
    refine Work.BSW.Cases.K4.inf_eq_bot_of_coprime ?_
    rw [hP, Nat.card_zpowers, hw]
    norm_num
  rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hle hinf, hP, Nat.card_zpowers, hw]

/-- **Bender 1974, §1**, `(4)` for `q = 5`: for a subgroup `D` of order `2` of `G` and an
involution `u ∉ D` inverting `D`, the normalizer of `D` is `D ⊔ ⟨u⟩`.

Both sides have order `4`: writing `D = ⟨x⟩` for its non-identity element `x` (an involution),
`N_G(D) = N_G(⟨x⟩) = C_G(x)` has order `4` by hypothesis, while `u` normalizes `D`, so
`D ⊔ ⟨u⟩ ≤ N_G(D)` and `|D ⊔ ⟨u⟩| = |D| * |⟨u⟩| = 4` because `D` and `⟨u⟩` meet trivially
(`u ∉ D`). -/
theorem normalizer_eq_sup_zpowers_of_card_two {G : Type} [Group G] [Finite G]
    {D : Subgroup G} {u : G} (hD : Nat.card ↥D = 2) (hu : orderOf u = 2) (huD : u ∉ D)
    (hInv : Inverts u D)
    (hC : ∀ v : G, orderOf v = 2 → Nat.card ↥(Subgroup.centralizer ({v} : Set G)) = 4) :
    Subgroup.normalizer (D : Set G) = D ⊔ Subgroup.zpowers u := by
  -- the non-identity element `x` of `D`, an involution, generates `D`
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD
    omega
  obtain ⟨x, hxD, hxneG⟩ : ∃ x : G, x ∈ D ∧ x ≠ 1 := by
    obtain ⟨y, hyne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    exact ⟨(y : G), y.2, fun h => hyne (Subtype.ext h)⟩
  have hxord : orderOf x = 2 := by
    have h1 : orderOf x ∣ 2 := by
      have h' := Work.BSW.Cases.K4.orderOf_dvd_natCard_of_mem hxD
      rwa [hD] at h'
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf x) h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxneG
    · exact h
  have hDgen : D = Subgroup.zpowers x := by
    have hle : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
    have hcard : Nat.card ↥D ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hxord, hD]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hNce : Subgroup.normalizer (D : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [hDgen]
    exact Work.BSW.Cases.K4.normalizer_zpowers_eq_centralizer_of_orderOf_eq_two hxord
  have hcardN : Nat.card ↥(Subgroup.normalizer (D : Set G)) = 4 := by
    rw [hNce]
    exact hC x hxord
  -- `u` normalizes `D`, because it inverts it
  -- `u` normalizes `D`, because it inverts it
  have hzp_le : Subgroup.zpowers u ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    rcases mem_zpowers_of_orderOf_two hu hh with rfl | rfl
    · simpa using hk
    · rw [hInv k hk]
      exact D.inv_mem hk
  have huN : u ∈ Subgroup.normalizer (D : Set G) := Subgroup.zpowers_le.mp hzp_le
  have hsup_le : D ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (D : Set G) :=
    sup_le Subgroup.le_normalizer hzp_le
  have hinf : D ⊓ Subgroup.zpowers u = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hzD, hzu⟩
    rcases mem_zpowers_of_orderOf_two hu hzu with h | h
    · exact h
    · exact absurd (h ▸ hzD) huD
  have hsup_card : Nat.card ↥(D ⊔ Subgroup.zpowers u) = 4 := by
    rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hzp_le hinf, hD, Nat.card_zpowers, hu]
  exact (Subgroup.eq_of_le_of_card_ge hsup_le (le_of_eq (by rw [hcardN, hsup_card]))).symm

/-- **Bender 1974, §1**, the `|K| = 2`, `|G| = 60` case: Bender's conclusion (1)–(4) with `q = 5`,
i.e. `Work.BSW.IsBSWData G 5`, in the strengthened form that `Work.BSW.BSWDataZassProp` needs
(Bender 3.7, and (4) as the equalities `N_G(X) = N_G(D)` and `N_G(D) = D⟨u⟩`).

Same construction as the superseded `Cases/bswK2StructureProp.lean`: a Sylow 5-subgroup `P` has
order `5` and normalizer of order `10` (`bswK2SylowFive`), `C_G(P) = P` (`bswK2CentralizerSylowFive`),
and `D = ⟨w₀⟩` of order `2` complements `P` in `N_G(P)` (`bswK2Complement`), with `3.7` from
`Work.BSW.Api.prime_card_inf_conjSub_eq_bot`.  The two extra conjuncts:

* every `⊥ ≠ X ≤ D` equals `D` because `|D| = 2` (cardinality divisibility), so `N_G(X) = N_G(D)`;
* `N_G(D) = D ⊔ ⟨u⟩` for the involution `u ≠ w₀` commuting with `w₀` (`bswK2Involution`): both
  sides have order `4`, since `N_G(⟨w₀⟩) = C_G(w₀)` (normalizing the two-element set `{1, w₀}`
  means fixing `w₀`) and `|C_G(w₀)| = 4` (`bswK2Involution`), while `D ⊓ ⟨u⟩ = ⊥` (as `u ∉ D` and
  both have order `2`) gives `|D ⊔ ⟨u⟩| = |D| * 2 = 4`. -/
theorem bswK2StructureProp2 : Work.BSW.BSWK2StructureProp := by
  intro G _ _ hS hnab t s K h hK2 h60
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 5) (G := G)
  -- `Q` is a Sylow `5`-subgroup of order `5` with normalizer of order `10`
  have hQcard : Nat.card ↥(Q : Subgroup G) = 5 := (bswK2SylowFive hS h60 Q).1
  have hNcard : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 10 :=
    (bswK2SylowFive hS h60 Q).2
  -- every involution has centralizer of order `4` and is inverted by a second involution
  have hinv : ∀ v : G, orderOf v = 2 → Nat.card ↥(Subgroup.centralizer ({v} : Set G)) = 4 :=
    fun v hv => (bswK2Involution h hK2 hv).1
  have hCeq : Subgroup.centralizer ((Q : Subgroup G) : Set G) = (Q : Subgroup G) :=
    bswK2CentralizerSylowFive (Q : Subgroup G) hQcard hNcard hinv
  -- an involution `w` in `N_G(Q)` (Cauchy, `2 ∣ |N_G(Q)| = 10`)
  have hex : ∃ w : G, w ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf w = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
      rw [hNcard]; norm_num
    obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G))) 2 h2dvd
    exact ⟨(w₀ : G), w₀.2, by rw [Subgroup.orderOf_coe, hw₀]⟩
  obtain ⟨w, hwN, hw⟩ := hex
  have hsup : Nat.card ↥((Q : Subgroup G) ⊔ Subgroup.zpowers w) = 10 :=
    card_sup_sylow_zpowers_of_orderOf_two hQcard hw hwN
  have huEx : ∃ u : G, orderOf u = 2 ∧ u ≠ w ∧ u * w = w * u :=
    (bswK2Involution h hK2 hw).2
  -- the complement `D` of `Q` in `N_G(Q)`, and the involution `u` inverting it
  obtain ⟨D, hDcomm, hDcard, hQD, hNPD, _hnormle, u, huord, huD, huInv⟩ :=
    bswK2Complement (Q : Subgroup G) hQcard hNcard hwN hw huEx hsup
  have hD2 : Nat.card ↥D = (5 - 1) / 2 := by
    rw [show (5 - 1) / 2 = 2 from by norm_num]
    exact hDcard
  -- every non-trivial subgroup of `D` is `D` itself
  have hnorm : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D →
      Subgroup.normalizer (X : Set G) = Subgroup.normalizer (D : Set G) :=
    fun X hne hle => normalizer_eq_normalizer_of_le_of_ne_bot_card_two hDcard hle hne
  have hND : Subgroup.normalizer (D : Set G) = D ⊔ Subgroup.zpowers u :=
    normalizer_eq_sup_zpowers_of_card_two hDcard huord huD huInv hinv
  -- Bender 3.7: `Q` is disjoint from its conjugates
  have hTI : ∀ g : G, g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
      (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥ :=
    fun g hg =>
      Work.BSW.Api.prime_card_inf_conjSub_eq_bot hg (by rw [hQcard]; exact Nat.prime_five)
  refine ⟨⟨5, 1, ⟨Nat.prime_five⟩, by norm_num, by norm_num⟩, by norm_num, (Q : Subgroup G),
    hQcard, hCeq, hTI, D, hDcomm, hD2, hQD, hNPD, hnorm,
    ⟨u, huord, huD, huInv, hND⟩, ?_⟩
  rw [h60]

end Work.BSW.Cases
