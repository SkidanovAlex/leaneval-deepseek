import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup
import Submission.Work.BSW.Cases.K4.card_normalizer_sylow_three
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Cases.K4.orderOf_even_eq_two_or_four
import Submission.Work.BSW.Cases.K4.orderOf_odd_mem
import Submission.Work.BSW.Cases.K4.ncard_orderOf_eq_five
import Submission.Work.BSW.Cases.K4.ncard_orderOf_eq_three_or_nine_le
import Submission.Work.BSW.Cases.K4.ncard_orderOf_eq_fifteen_le

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

variable {G : Type} [Group G] [Finite G]

/-- Union bound for six sets: `|s₁ ∪ … ∪ s₆| ≤ |s₁| + … + |s₆|`. -/
theorem ncard_union_six_le {α : Type} (s1 s2 s3 s4 s5 s6 : Set α) :
    (s1 ∪ s2 ∪ s3 ∪ s4 ∪ s5 ∪ s6).ncard ≤
      s1.ncard + s2.ncard + s3.ncard + s4.ncard + s5.ncard + s6.ncard := by
  have h1 := Set.ncard_union_le (s1 ∪ s2 ∪ s3 ∪ s4 ∪ s5) s6
  have h2 := Set.ncard_union_le (s1 ∪ s2 ∪ s3 ∪ s4) s5
  have h3 := Set.ncard_union_le (s1 ∪ s2 ∪ s3) s4
  have h4 := Set.ncard_union_le (s1 ∪ s2) s3
  have h5 := Set.ncard_union_le s1 s2
  omega

/-- In a group of order `360`, the number `n₅` of Sylow `5`-subgroups is `1`, `6` or `36`.

`n₅ = [G : N_G(P)]` divides `360`; moreover `N_G(P)` contains the Sylow `5`-subgroup `P` of order
`5`, so `n₅ = 360/|N_G(P)|` divides `360/5 = 72`; together with `n₅ ≡ 1 (mod 5)` this leaves
`n₅ ∈ {1, 6, 36}`. -/
theorem natCard_sylow_five_dichotomy (hG : Nat.card G = 360) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 ∨ Nat.card (Sylow 5 G) = 36 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := G)
  -- a Sylow `5`-subgroup has order `5`
  have hPcard : Nat.card ↥(P : Subgroup G) = 5 := by
    rw [Sylow.card_eq_multiplicity, hG]
    have h1 : 1 ≤ (360 : ℕ).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mp (by norm_num)
    have h2 : (360 : ℕ).factorization 5 < 2 := by
      by_contra h
      have hd : 5 ^ 2 ∣ (360 : ℕ) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mpr (by omega)
      norm_num at hd
    have : (360 : ℕ).factorization 5 = 1 := by omega
    rw [this]; norm_num
  have hmul : (Subgroup.normalizer (P : Set G)).index *
      Nat.card ↥(Subgroup.normalizer (P : Set G)) = 360 := by
    rw [Subgroup.index_mul_card, hG]
  set n := Nat.card (Sylow 5 G) with hn
  have hix : n = (Subgroup.normalizer (P : Set G)).index := by
    rw [hn]; exact Sylow.card_eq_index_normalizer P
  have h5dvd : 5 ∣ Nat.card ↥(Subgroup.normalizer (P : Set G)) := by
    have h' := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup G)))
    rwa [hPcard] at h'
  have hmod : n % 5 = 1 := by
    rw [hn]
    have h := card_sylow_modEq_one 5 G
    rwa [Nat.ModEq] at h
  -- `n = [G : N_G(P)]` divides `360 / 5 = 72`
  have hdvd : n ∣ 72 := by
    obtain ⟨k, hk⟩ := h5dvd
    refine ⟨k, ?_⟩
    have h' : 5 * (n * k) = 360 := by
      rw [← hmul, hix, hk]; ring
    omega
  have hmem : n ∈ (72).divisors.filter (fun d => d % 5 = 1) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩, hmod⟩
  have hset : (72).divisors.filter (fun d => d % 5 = 1) = {1, 6, 36} := by decide
  rw [hset] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A finite simple group of order `360` has more than one Sylow `5`-subgroup (a unique one would be
normal, hence `⊥` or `⊤`, but it has order `5`). -/
theorem natCard_sylow_five_ne_one [IsSimpleGroup G] (hG : Nat.card G = 360) :
    Nat.card (Sylow 5 G) ≠ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := G)
  intro h1
  haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hnrm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  haveI := hnrm
  have hPcard : Nat.card ↥(P : Subgroup G) = 5 := by
    rw [Sylow.card_eq_multiplicity, hG]
    have h1 : 1 ≤ (360 : ℕ).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mp (by norm_num)
    have h2 : (360 : ℕ).factorization 5 < 2 := by
      by_contra h
      have hd : 5 ^ 2 ∣ (360 : ℕ) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mpr (by omega)
      norm_num at hd
    have : (360 : ℕ).factorization 5 = 1 := by omega
    rw [this]; norm_num
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) with h | h
  · rw [h, Subgroup.card_bot] at hPcard; omega
  · rw [h, Subgroup.card_top] at hPcard; omega

/-- In the `|K| = 4`, `|G| = 360` case of BSW the number of involutions is `|G : C_G(t)| = 45`. -/
theorem ncard_orderOf_eq_two {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K)
    (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360) :
    {x : G | orderOf x = 2}.ncard = 45 := by
  rw [Work.BSW.Api.ncard_involutions_eq_index h]
  have hc := Work.BSW.Cases.K4.card_centralizer_t h hK4
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({t} : Set G))
  rw [hc, hG] at hmul
  omega

/-- A finite simple nonabelian group of order `360` has exactly `10` Sylow `3`-subgroups. -/
theorem natCard_sylow_three_eq_ten [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hG : Nat.card G = 360) : Nat.card (Sylow 3 G) = 10 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := G)
  have hburn : ∀ {p : ℕ} [Fact (Nat.Prime p)] (Q' : Sylow p G), p ∣ Nat.card G →
      ∃ g : G, g ∈ Subgroup.normalizer (Q' : Set G) ∧
        g ∉ Subgroup.centralizer ((Q' : Subgroup G) : Set G) :=
    fun Q' hp => Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup hnab Q'.isPGroup'
      (Sylow.not_dvd_index Q') hp
  have hNcard : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 36 :=
    Work.BSW.Cases.K4.card_normalizer_sylow_three hG hburn Q
  have hix : Nat.card (Sylow 3 G) =
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index := Sylow.card_eq_index_normalizer Q
  rw [hix]
  have hmul := Subgroup.index_mul_card (Subgroup.normalizer ((Q : Subgroup G) : Set G))
  rw [hNcard, hG] at hmul
  omega

/-- In the `|K| = 4` case, an involution has at most two square roots.

If `y` is an involution and `x * x = y`, then `x` commutes with `y = x * x`, so `x ∈ C_G(y)`; and
for `y = t` the elements `z` with `z * z = t` are among `k` and `k⁻¹`, where `K = ⟨k⟩` is the
cyclic group of order `4` with `k * k = t` (`Work.BSW.Cases.K4.exists_gen_K`).  Conjugation
(`Work.BSW.involutions_conj`) carries the statement for `t` to the statement for `y`. -/
theorem ncard_sq_eq_involution_le_two {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K)
    (hK4 : Nat.card ↥K = 4) (y : G) (hy : orderOf y = 2) :
    {x : G | x * x = y}.ncard ≤ 2 := by
  obtain ⟨k, hk4, hkgen, hkt⟩ := Work.BSW.Cases.K4.exists_gen_K h hK4
  have hkK : k ∈ K := by rw [hkgen]; exact Subgroup.mem_zpowers k
  -- the square roots of `t` in `G` are among `k` and `k⁻¹`
  have hbase : {z : G | z * z = t}.ncard ≤ 2 := by
    have hsub : {z : G | z * z = t} ⊆ ({k, k⁻¹} : Set G) := by
      intro z hz
      have hzt : z * z = t := hz
      have hzct : z ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z * t = z * (z * z) := by rw [← hzt]
          _ = (z * z) * z := by group
          _ = t * z := by rw [hzt]
      rcases (Work.BSW.Api.mem_centralizer_iff h z).mp hzct with hzK | ⟨w, hwK, hw⟩
      · -- `z ∈ K`: then `z * k⁻¹` is an involution of `K`, hence `1` or `t`
        have h1 : z * k⁻¹ ∈ K := K.mul_mem hzK (K.inv_mem hkK)
        have hcomm : z * k⁻¹ = k⁻¹ * z := by
          haveI := Work.BSW.isMulCommutative_K h
          exact (congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥K)).comm
            (⟨z, hzK⟩ : ↥K) (⟨k⁻¹, K.inv_mem hkK⟩ : ↥K)))
        have h2 : (z * k⁻¹) * (z * k⁻¹) = 1 := by
          calc (z * k⁻¹) * (z * k⁻¹) = z * (k⁻¹ * z) * k⁻¹ := by group
            _ = z * (z * k⁻¹) * k⁻¹ := by rw [hcomm]
            _ = (z * z) * k⁻¹ * k⁻¹ := by group
            _ = t * k⁻¹ * k⁻¹ := by rw [hzt]
            _ = (k * k) * k⁻¹ * k⁻¹ := by rw [hkt]
            _ = 1 := by group
        rcases Work.BSW.involution_mem_K h h1 h2 with h3 | h3
        · have hz_eq : z = k := by
            calc z = z * k⁻¹ * k := by group
              _ = 1 * k := by rw [h3]
              _ = k := by group
          rw [hz_eq]; exact Set.mem_insert _ _
        · have hz_eq : z = k⁻¹ := by
            calc z = z * k⁻¹ * k := by group
              _ = t * k := by rw [h3]
              _ = (k * k) * k := by rw [hkt]
              _ = k⁻¹ := by
                rw [eq_inv_iff_mul_eq_one]
                calc ((k * k) * k) * k = (k * k) * (k * k) := by group
                  _ = t * t := by rw [hkt]
                  _ = 1 := Work.BSW.t_mul_self h
          rw [hz_eq]
          exact Set.mem_insert_iff.mpr (Or.inr rfl)
      · -- `z = w * s` with `w ∈ K`: then `z * z = 1 ≠ t`
        exfalso
        have hz' : z * z = t := hz
        rw [hw] at hz'
        have h1 := Work.BSW.Cases.K4.mul_s_self h hwK
        rw [h1] at hz'
        exact Work.BSW.t_ne_one h hz'.symm
    have hkne : k ≠ k⁻¹ := by
      intro hh
      have h2 : k * k = 1 := eq_inv_iff_mul_eq_one.mp hh
      have hd : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      rw [hk4] at hd
      omega
    calc ({z : G | z * z = t} : Set G).ncard ≤ ({k, k⁻¹} : Set G).ncard := Set.ncard_mono hsub
      _ = 2 := Set.ncard_pair hkne
  -- transport to `y` by conjugation
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h y hy)
  have hconj : {z : G | z * z = y}.ncard = {z : G | z * z = t}.ncard := by
    have himg : (fun z : G => c * z * c⁻¹) '' {z : G | z * z = y} =
        {z : G | z * z = t} := by
      rw [← hc]
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        simp only [Set.mem_ofPred_eq] at hz ⊢
        calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
          _ = c * y * c⁻¹ := by rw [hz]
      · intro hw
        refine ⟨c⁻¹ * w * c, ?_, ?_⟩
        · simp only [Set.mem_ofPred_eq]
          calc (c⁻¹ * w * c) * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c := by group
            _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [hw]
            _ = y := by group
        · group
    have hinj : Function.Injective (fun z : G => c * z * c⁻¹) := by
      intro a b hab
      have h' := congrArg (fun w : G => c⁻¹ * w * c) hab
      simpa [mul_assoc] using h'
    rw [← Set.ncard_image_of_injective _ hinj, himg]
  rw [hconj]
  exact hbase

/-- In the `|K| = 4`, `|G| = 360` case of BSW, `G` has at most `90` elements of order `4`: each of
them squares to one of the `45` involutions (`ncard_orderOf_eq_two`), and an involution has at most
two square roots (`ncard_sq_eq_involution_le_two`). -/
theorem ncard_orderOf_eq_four_le_aux {t s : G} {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K)
    (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360) :
    {x : G | orderOf x = 4}.ncard ≤ 90 := by
  have hinv : {x : G | orderOf x = 2}.ncard = 45 := ncard_orderOf_eq_two h hK4 hG
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype {y : G // orderOf y = 2} := Fintype.ofFinite _
  have hcover : {x : G | orderOf x = 4} ⊆
      ⋃ y : {y : G // orderOf y = 2}, {x : G | x * x = (y : G)} := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x * x, ?_⟩, ?_⟩
    · have hx2 : x * x = x ^ 2 := (pow_two x).symm
      rw [hx2, orderOf_pow, hx]
      norm_num
    · exact Set.mem_ofPred_eq.mpr rfl
  have hcard : Nat.card {y : G // orderOf y = 2} = 45 := by
    haveI : Fintype ↥({y : G | orderOf y = 2} : Set G) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Set.toFinset_ofPred,
      ← Set.ncard_eq_toFinset_card']
    exact hinv
  calc {x : G | orderOf x = 4}.ncard
      ≤ ∑ y : {y : G // orderOf y = 2}, ({x : G | x * x = (y : G)} : Set G).ncard :=
        le_trans (Set.ncard_mono hcover) (Set.ncard_iUnion_le_of_fintype _)
    _ ≤ ∑ _y : {y : G // orderOf y = 2}, 2 :=
        Finset.sum_le_sum (fun y _ => ncard_sq_eq_involution_le_two h hK4 y y.2)
    _ = 90 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
        norm_num

/-- In the `|K| = 4`, `|G| = 360` case of BSW the number of Sylow `5`-subgroups is `36` (it is
`6` or `36` by Sylow, and `6` is impossible).

Strategy: `n₅ ∣ 72` and `n₅ ≡ 1 (mod 5)` give `n₅ ∈ {1, 6, 36}`; `n₅ ≠ 1` by simplicity.  Assume
`n₅ = 6`.  Every element of `G` has order in `{1, 2, 3, 4, 5, 9, 15}`: orders `6` and `18` are
excluded by `Work.BSW.Cases.K4.orderOf_ne_six` / `orderOf_ne_eighteen`; there is no element of
order `8` (its own centralizer, of order `8 = |G|₂` — the Sylow `2`-subgroups are the involution
centralizers, whose order is `8`); no element has order `10` or `30` (a `5`-th or `15`-th power is
an involution whose centralizer has order `8`); an element of order `12`, `20`, `36`, `60` has a
power of order `4` lying in its own cyclic centralizer (`C_G` of an element of order `4` has order
`4`); orders `24`, `40`, `72`, `120`, `360` contain order `8`; an element of order `45` has its
`5`-th power generating a Sylow `3`-subgroup of order `9`, so it is centralized by that Sylow, and
`C_G` of a Sylow `3`-subgroup is itself (the same statement as the hypothesis `hC` of
`Work.BSW.Cases.K4.sylow_three_ti`, conjugated for other Sylow `3`-subgroups).
Counting: `#{involutions} = |G|/|C_G(t)| = 45`
(`Work.BSW.Api.ncard_involutions_eq_index`); `#{order 4} = 90` (every involution is the square of
exactly two elements of order `4`, because its centralizer is `D₈`); `#{order 5} = 4·n₅ = 24`;
`#{order 15} ≤ 8·n₅ = 48` (each element of order `15` lies in `C_G(P)` for the unique Sylow
`5`-subgroup `P = ⟨x³⟩`, and every `C_G(P)` — of order in `{5, 10, 15, 20, 30}` — has at most `8`
elements of order `15`: for order `15` it is cyclic, for order `30` its Sylow `3` is normal since
`10` subgroups of order `3` would give `80 > 30` elements of order `15`); and
`#{x | orderOf x = 3 ∨ orderOf x = 9} ≤ 80 = 10 · 8` (each Sylow `3`-subgroup has order `9`).
Hence `360 = 1 + 45 + 90 + 24 + ≤80 + ≤48 ≤ 288`, a contradiction. -/
theorem natCard_sylow_five_eq_thirtysix {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360) :
    Nat.card (Sylow 5 G) = 36 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases natCard_sylow_five_dichotomy (G := G) hG with h1 | h6 | h36
  · exact absurd h1 (natCard_sylow_five_ne_one (G := G) hG)
  · exfalso
    -- Element counts in the `n₅ = 6` branch
    have hn3 : Nat.card (Sylow 3 G) = 10 := natCard_sylow_three_eq_ten hnab hG
    have hinv : {x : G | orderOf x = 2}.ncard = 45 := ncard_orderOf_eq_two h hK4 hG
    have h4b : {x : G | orderOf x = 4}.ncard ≤ 90 := ncard_orderOf_eq_four_le_aux h hK4 hG
    have h5b : {x : G | orderOf x = 5}.ncard ≤ 24 := by
      have hh := ncard_orderOf_eq_five (G := G) hG
      rw [hh, h6]
    have h39b : {x : G | orderOf x = 3 ∨ orderOf x = 9}.ncard ≤ 80 :=
      ncard_orderOf_eq_three_or_nine_le (G := G) hG hn3
    have h15b : {x : G | orderOf x = 15}.ncard ≤ 48 :=
      ncard_orderOf_eq_fifteen_le hnab h hK4 hG h6
    -- Every element has order in `{1, 2, 3, 4, 5, 9, 15}`
    have hclass : ∀ x : G, orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 ∨ orderOf x = 5 ∨
        orderOf x = 3 ∨ orderOf x = 9 ∨ orderOf x = 15 := by
      intro x
      rcases Nat.even_or_odd (orderOf x) with hev | hod
      · rcases orderOf_even_eq_two_or_four h hK4 x hev with h2 | h4
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h4))
      · rcases orderOf_odd_mem h hK4 hG h6 x hod with h1 | h3 | h5' | h9 | h15'
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h5')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h15')))))
    set A1 : Set G := {x : G | orderOf x = 1} with hA1
    set A2 : Set G := {x : G | orderOf x = 2} with hA2
    set A4 : Set G := {x : G | orderOf x = 4} with hA4
    set A5 : Set G := {x : G | orderOf x = 5} with hA5
    set A39 : Set G := {x : G | orderOf x = 3 ∨ orderOf x = 9} with hA39
    set A15 : Set G := {x : G | orderOf x = 15} with hA15
    -- the six sets cover `G`
    have hcover : (Set.univ : Set G) ⊆ A1 ∪ A2 ∪ A4 ∪ A5 ∪ A39 ∪ A15 := by
      intro x _
      have hx := hclass x
      simp only [hA1, hA2, hA4, hA5, hA39, hA15, Set.mem_union, Set.mem_ofPred_eq]
      tauto
    have hmono : Nat.card G ≤ (A1 ∪ A2 ∪ A4 ∪ A5 ∪ A39 ∪ A15).ncard := by
      rw [← Set.ncard_univ]
      exact Set.ncard_mono hcover
    have hA1b : A1.ncard ≤ 1 := by
      rw [hA1]
      have hset : {x : G | orderOf x = 1} = {1} := by
        ext x; simp [orderOf_eq_one_iff]
      rw [hset, Set.ncard_singleton]
    have hA2b : A2.ncard ≤ 45 := by rw [hA2]; exact le_of_eq hinv
    have hA4b : A4.ncard ≤ 90 := by rw [hA4]; exact h4b
    have hA5b : A5.ncard ≤ 24 := by rw [hA5]; exact h5b
    have hA39b : A39.ncard ≤ 80 := by rw [hA39]; exact h39b
    have hA15b : A15.ncard ≤ 48 := by rw [hA15]; exact h15b
    have hU := ncard_union_six_le A1 A2 A4 A5 A39 A15
    omega
  · exact h36

end Work.BSW.Cases.K4
