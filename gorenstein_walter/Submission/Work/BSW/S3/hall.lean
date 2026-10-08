import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.S3

open Subgroup

/-- **Fixed point lemma.**  Let `G` be a finite group, `p` a prime, `H` a subgroup of order
divisible by `p` (so a nontrivial `p`-group when `H` is a `p`-group), and `K` a `p`-subgroup of `G`
normalizing `H`.  Then the conjugation action of `K` on `H` fixes a non-identity element of `H`:
the number of fixed points of a `p`-group action is congruent mod `p` to the cardinality of the
set acted on, and contains the identity, while `p ∣ |H|`. -/
lemma exists_fixed_point_of_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hK : IsPGroup p K) (hHK : K ≤ Subgroup.normalizer (H : Set G))
    (hp : p ∣ Nat.card ↥H) :
    ∃ a ∈ H, a ≠ 1 ∧ ∀ k ∈ K, k * a * k⁻¹ = a := by
  classical
  haveI : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  let φ : ↥K →* MulAut ↥(H.subgroupOf (Subgroup.normalizer (H : Set G))) :=
    MulAut.conjNormal.comp (Subgroup.inclusion hHK)
  letI : MulAction ↥K ↥(H.subgroupOf (Subgroup.normalizer (H : Set G))) := MulAction.compHom _ φ
  have hcard : Nat.card ↥(H.subgroupOf (Subgroup.normalizer (H : Set G))) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
  have hp' : p ∣ Nat.card ↥(H.subgroupOf (Subgroup.normalizer (H : Set G))) := hcard ▸ hp
  obtain ⟨b, hb, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point (hK) _
      hp' (a := (1 : ↥(H.subgroupOf (Subgroup.normalizer (H : Set G)))))
      (MulAction.mem_fixedPoints.mpr
        (fun k => by rw [MulAction.compHom_smul_def, MulAut.smul_def]; simp))
  refine ⟨(b.1.1 : G), (Subgroup.mem_subgroupOf.mp b.2), ?_, ?_⟩
  · intro hb1
    exact hbne (Subtype.ext (Subtype.ext (by simpa using hb1.symm)))
  · intro k hk
    have hkb : (⟨k, hk⟩ : ↥K) • b = b := MulAction.mem_fixedPoints.mp hb ⟨k, hk⟩
    rw [MulAction.compHom_smul_def, MulAut.smul_def] at hkb
    change MulAut.conjNormal (Subgroup.inclusion hHK ⟨k, hk⟩) b = b at hkb
    have key : ((Subgroup.inclusion hHK ⟨k, hk⟩ : ↥(Subgroup.normalizer (H : Set G))) * (b.1)
        * (Subgroup.inclusion hHK ⟨k, hk⟩ : ↥(Subgroup.normalizer (H : Set G)))⁻¹
          : ↥(Subgroup.normalizer (H : Set G))) = b.1 := by
      rw [← MulAut.conjNormal_apply]
      exact congrArg Subtype.val hkb
    have := congrArg (fun x : ↥(Subgroup.normalizer (H : Set G)) => (x.1 : G)) key
    simpa using this

/-- **The `hall` lemma.** If a subgroup `F` of a finite group `G` is "self-centralizing elementwise"
(`C_G(a) = F` for every `a ∈ F`, `a ≠ 1`), then `F` is a Hall subgroup: `|F|` is coprime to its
index.  Indeed, if `p` is a prime dividing `|F|` and `P` is a Sylow `p`-subgroup of `F`, then the
image of `P` in `G` is a Sylow `p`-subgroup of `G`; the normalizer of that image fixes a nontrivial
element of it, hence lies in `F`, and the normalizer condition in the `p`-group forces the image to
be the whole Sylow subgroup of `G`. -/
theorem hall {G : Type} [Group G] [Finite G] (F : Subgroup G)
    (h : ∀ a ∈ F, a ≠ 1 → Subgroup.centralizer ({a} : Set G) = F) :
    Nat.Coprime (Nat.card F) F.index := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : p ∣ Nat.card ↥F := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpIdx : p ∣ F.index := hpd.trans (Nat.gcd_dvd_right _ _)
  -- A Sylow `p`-subgroup of `F`, and its image in `G`.
  let P : Sylow p ↥F := Sylow.nonempty.some
  set Pg : Subgroup G := (P : Subgroup ↥F).map F.subtype with hPgdef
  -- `P` is nontrivial (since `p ∣ |F|`), so `p ∣ |Pg|`.
  have hPne : (P : Subgroup ↥F) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hpF
  have hPgt : 1 < Nat.card ↥(P : Subgroup ↥F) :=
    (Subgroup.one_lt_card_iff_ne_bot (P : Subgroup ↥F)).mpr hPne
  have hPcard : p ∣ Nat.card ↥(P : Subgroup ↥F) := by
    rcases IsPGroup.card_eq_or_dvd P.isPGroup' with h1 | hd
    · omega
    · exact hd
  have hPgcard : Nat.card ↥Pg = Nat.card ↥(P : Subgroup ↥F) := by
    rw [hPgdef]; exact Subgroup.card_map_of_injective F.subtype_injective
  have hpPg : p ∣ Nat.card ↥Pg := hPgcard ▸ hPcard
  -- A Sylow `p`-subgroup `Q` of `G` with `Q ∩ F = Pg`.
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_subtype_eq (p := p) P
  have hQ' : (Q : Subgroup G).subgroupOf F = (P : Subgroup ↥F) := hQ
  have hQK : (Q : Subgroup G) ⊓ F = Pg := by
    rw [← Subgroup.subgroupOf_map_subtype (Q : Subgroup G) F, hQ', hPgdef]
  have hPg_le_F : Pg ≤ F := by rw [hPgdef]; exact Subgroup.map_subtype_le (P : Subgroup ↥F)
  have hPg_le_Q : Pg ≤ (Q : Subgroup G) := hQK ▸ inf_le_left
  -- The normalizer of `Pg` inside `Q` fixes a nontrivial element of `Pg`, hence lies in `F`,
  -- hence equals `Pg`.
  obtain ⟨a, haPg, ha1, hfix⟩ :=
    exists_fixed_point_of_normalizer (p := p)
      (IsPGroup.to_le Q.isPGroup' (inf_le_right :
        Subgroup.normalizer (Pg : Set G) ⊓ (Q : Subgroup G) ≤ (Q : Subgroup G)))
      inf_le_left hpPg
  have hKnleF : Subgroup.normalizer (Pg : Set G) ⊓ (Q : Subgroup G) ≤ F := by
    intro y hy
    have hya : y * a * y⁻¹ = a := hfix y hy
    have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := congrArg (fun z => z * y) hya
      simpa [mul_assoc] using h2
    rw [h a (hPg_le_F haPg) ha1] at hyC
    exact hyC
  have hK_eq : Subgroup.normalizer (Pg : Set G) ⊓ (Q : Subgroup G) = Pg :=
    le_antisymm (fun y hy => hQK ▸ ⟨hy.2, hKnleF hy⟩)
      (le_inf Subgroup.le_normalizer hPg_le_Q)
  -- Normalizer condition in the `p`-group `Q` then forces `Pg = Q`.
  have hnorm : Subgroup.normalizer (↑(Pg.subgroupOf (Q : Subgroup G))) =
      Pg.subgroupOf (Q : Subgroup G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPg_le_Q,
        ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (Pg : Set G)) (Q : Subgroup G),
        hK_eq]
  have hnc : NormalizerCondition ↥(Q : Subgroup G) :=
    @Group.normalizerCondition_of_isNilpotent ↥(Q : Subgroup G) _ (Q.isPGroup'.isNilpotent)
  have htop : Pg.subgroupOf (Q : Subgroup G) = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hnorm
  have hPgQ : Pg = (Q : Subgroup G) :=
    le_antisymm hPg_le_Q (Subgroup.subgroupOf_eq_top.mp htop)
  -- Finish: `Pg` is a Sylow `p`-subgroup of `G`, so `p ∤ [G : Pg]`, while `F.index ∣ Pg.index`.
  have hdvd : F.index ∣ Pg.index :=
    ⟨Pg.relIndex F, by rw [mul_comm, Subgroup.relIndex_mul_index hPg_le_F]⟩
  exact (Sylow.not_dvd_index Q) (hPgQ ▸ hpIdx.trans hdvd)

end Work.BSW.S3
