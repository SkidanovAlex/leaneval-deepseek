import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.L27_two_part
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.L27cf_fittingIn_le_sup_three
import Submission.Work.CORE2B.L27cf_twoResidual
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.Dihedral.Defs

/-!
# `Work.CORE2B.L27_centralizes_fittingIn`

Bender 1981, Lemma 2.7, p. 221: under the hypotheses of Lemma 2.7 on `M`,

  `⁅M, ⟨t⟩⁆ ≤ C_G(F(M))`   ("Now `[M,t] ⊆ C_M(F(M))`").

`F(M)` is nilpotent, hence the join of its parts `F_2(M)`, `F_{π ∩ {2}ᶜ}(M)` (the odd part of the
`π`-part) and `F_{π'}(M)`, where `π = π(F(Ĥ)) = B.pi`:

  `F(M) ≤ F_2(M) ⊔ F_{π ∩ {2}ᶜ}(M) ⊔ F_{π'}(M)`   (`L27cf_fittingIn_le_sup_three`).

On the three parts, the conjugation action of the involution `t` is respectively trivial
(`L27_two_part_centralized`, Bender's step 1) / trivial (`F_{π ∩ {2}ᶜ}(M) ≤ F_π(M) ≤ Ĥ` by
Lemma 2.3(i) and `t ∈ O₂(Ĥ) ◁ Ĥ`, so commutators with `t` lie in a `2`-group and in a group of odd
order) / inversion (`L27cf_inverts_fittingPiIn_pi_compl`, Lemma 2.3(ii)).  Since all three parts
are normalized by `M`, and `C_G` of the join is the intersection of the `C_G`'s, the commutator
`⁅M,⟨t⟩⁆` centralizes each part, hence all of `F(M)`.
-/

open scoped MatrixGroups commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Two elementary commutator computations

If `t` is an involution normalizing `F` and acting on `F` trivially (resp. by inversion), then
`⁅M,⟨t⟩⁆` centralizes `F`.  Conjugation by `⁅m,t⁆ = m t m⁻¹ t⁻¹` is `c_m c_t c_m⁻¹ c_t`, and either
behaviour of `c_t` on `F` makes this trivial. -/

/-- If `t` inverts `F` pointwise and `t² = 1`, then `⁅M,t⁆` centralizes `F`. -/
theorem comm_le_centralizer_of_inverts {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G)) (hinv : ∀ x ∈ F, t * x * t⁻¹ = x⁻¹)
    (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  refine Subgroup.commutator_le.mpr ?_
  intro m hm y hy
  rcases hpow y hy with hy1 | hy1
  · rw [hy1, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [hy1]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have key1 : t⁻¹ * z * t = z⁻¹ := by
      rw [htinv]
      simpa [htinv] using hinv z hz
    have hmemF : m⁻¹ * z⁻¹ * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z⁻¹).mp (F.inv_mem hz)
      simpa using h
    have key2 : t * (m⁻¹ * z⁻¹ * m) * t⁻¹ = m⁻¹ * z * m := by
      have h := hinv (m⁻¹ * z⁻¹ * m) hmemF
      rw [h]
      group
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (t * (m⁻¹ * z⁻¹ * m) * t⁻¹) * m⁻¹ := by rw [key1]
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [key2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm

/-- If `t` centralizes `F` pointwise and `t² = 1`, then `⁅M,t⁆` centralizes `F`. -/
theorem comm_le_centralizer_of_centralizes {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G)) (hcen : ∀ x ∈ F, t * x * t⁻¹ = x)
    (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcen' : ∀ x ∈ F, t⁻¹ * x * t = x := by
    intro x hx
    simpa [htinv] using hcen x hx
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  refine Subgroup.commutator_le.mpr ?_
  intro m hm y hy
  rcases hpow y hy with hy1 | hy1
  · rw [hy1, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [hy1]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hmemF : m⁻¹ * z * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z).mp hz
      simpa using h
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      have h2 : t * (m⁻¹ * z * m) * t⁻¹ = m⁻¹ * z * m := by
        simpa [htinv] using hcen' _ hmemF
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [hcen' z hz, h2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm

/-- **Assembly.**  If `F` is covered by three subgroups on which the involution `t` acts
respectively trivially, trivially and by inversion, and all three are normalized by `M`, then
`⁅M,⟨t⟩⁆` centralizes `F`. -/
theorem comm_le_centralizer_of_three {G : Type} [Group G] {M F A B C : Subgroup G} {t : G}
    (hA : M ≤ Subgroup.normalizer (A : Set G)) (hB : M ≤ Subgroup.normalizer (B : Set G))
    (hC : M ≤ Subgroup.normalizer (C : Set G))
    (hcenA : ∀ x ∈ A, t * x * t⁻¹ = x) (hcenB : ∀ x ∈ B, t * x * t⁻¹ = x)
    (hinvC : ∀ x ∈ C, t * x * t⁻¹ = x⁻¹) (ht : t * t = 1)
    (hcover : F ≤ A ⊔ B ⊔ C) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have h1 : ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (A : Set G) :=
    comm_le_centralizer_of_centralizes hA hcenA ht
  have h2 : ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (B : Set G) :=
    comm_le_centralizer_of_centralizes hB hcenB ht
  have h3 : ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (C : Set G) :=
    comm_le_centralizer_of_inverts hC hinvC ht
  have h4 : ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup, Subgroup.centralizer_sup]
    exact le_inf (le_inf h1 h2) h3
  exact h4.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hcover))

/-! ## 2. The `π`-cores of the Fitting subgroup -/

/-- `O_π` is monotone in `π`. -/
theorem piCore_mono_local {G : Type} [Group G] {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) :
    Work.GW2.piCore π₁ G ≤ Work.GW2.piCore π₂ G := by
  rw [Work.GW2.piCore, Work.GW2.piCore]
  refine Subgroup.normalCore_mono (sSup_le ?_)
  rintro N ⟨hN, hpi⟩
  exact le_sSup ⟨hN, fun q hq => h (hpi q hq)⟩

/-- `F_σ` is monotone in `σ`. -/
theorem fittingPiIn_mono_local {G : Type} [Group G] {σ₁ σ₂ : Set ℕ} (h : σ₁ ⊆ σ₂)
    (K : Subgroup G) : Work.GW2.fittingPiIn σ₁ K ≤ Work.GW2.fittingPiIn σ₂ K := by
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPiIn, Work.GW2.fittingPi, Work.GW2.fittingPi]
  exact Subgroup.map_mono (Subgroup.map_mono (piCore_mono_local h))

/-- `F_σ(M)` has odd order when `σ` contains no `2`. -/
theorem odd_card_fittingPiIn_local {G : Type} [Group G] [Finite G] {σ : Set ℕ}
    (hσ : σ ⊆ ({2}ᶜ : Set ℕ)) (M : Subgroup G) :
    Odd (Nat.card (Work.GW2.fittingPiIn σ M)) := by
  refine L27cf_odd_card_of_isPiSubgroup hσ ?_
  have hcard : Nat.card (Work.GW2.fittingPiIn σ M)
      = Nat.card (Work.GW2.piCore σ ↥(Work.GW2.fitting ↥M)) := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi, Subgroup.map_map]
    exact Subgroup.card_map_of_injective
      (M.subtype_injective.comp (Work.GW2.fitting ↥M).subtype_injective)
  intro q hq
  rw [hcard] at hq
  exact isPiSubgroup_piCore_local σ q hq

/-! ## 3. `t` is `2`-central in `M` (the size hypotheses of Lemma 2.7)

`t` is central in some Sylow `2`-subgroup of `M`, in each of the three cases of the size
hypothesis: `8 ≤ |S ⊓ M|` (`sylow_central_of_large_inter`), `|S| = 4`
(`L27two.sylow_central_of_card_four`) and `t ∈ O²(M)` (`L27cf_twoResidual`). -/

theorem two_central_sylow_local {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hD : L27Hyp B M) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * B.t = B.t * (x : G) := by
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · exact h
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  rcases hD.size with h8 | h4 | hres
  · exact sylow_central_of_large_inter B.S n hn B.t B.t_order htc M hD.t_mem hD.sylow_nc h8
  · exact L27two.sylow_central_of_card_four B.S B.t B.t_order h4 M hD.t_mem hD.sylow_nc
  · exact L27cf_twoResidual B.S n hn B.t B.t_order htc M hD.t_mem hD.sylow_nc hres

/-- Bender's step 1 for the two-part: `t` centralizes `F_2(M)`. -/
theorem two_part_centralized_local {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hD : L27Hyp B M) :
    Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ Subgroup.centralizer ({B.t} : Set G) := by
  obtain ⟨P, hP⟩ := two_central_sylow_local hCtx B M hD
  exact (L27two.fitting_two_le_two_core M).trans
    (L27two.pCoreIn_two_le_centralizer_of_sylow M B.t P hP)

/-! ## 4. The odd part of the `π`-part of `F(M)` is centralized by `t`

`O_{π ∩ {2}ᶜ}(F(M))` lies in `F_π(M) ≤ Ĥ` (Lemma 2.3(i)) and is normalized by `M ∋ t`
(`le_normalizer_fittingPiIn_local`); since `t ∈ O₂(Ĥ) ◁ Ĥ`, every commutator `⁅t,x⁆` with `x` in
this piece lies in both `O₂(Ĥ)` (a `2`-group) and the piece itself (of odd order), hence is `1`.

If `F*(Ĥ)` is a `p`-group, Lemma 2.3(i) is not available, but then `π = {2}`
(`L27cf_pi_eq_two_of_isPGroup_fstar`) and the piece is trivial
(`L27cf_fittingPiIn_inter_compl_eq_bot`). -/

theorem odd_pi_part_centralized_local {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : L27Hyp B M) :
    Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ≤ Subgroup.centralizer ({B.t} : Set G) := by
  set σ : Set ℕ := B.pi ∩ ({2}ᶜ : Set ℕ) with hσdef
  have hsubπ : σ ⊆ B.pi := Set.inter_subset_left
  have hsub2 : σ ⊆ ({2}ᶜ : Set ℕ) := Set.inter_subset_right
  by_cases hpg : ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)
  · -- the odd part of `π` is empty, so the piece is trivial
    have hbot : Work.GW2.fittingPiIn σ M = ⊥ := by
      rw [hσdef]
      exact L27cf_fittingPiIn_inter_compl_eq_bot h26 hFT hCtx B hpg M
    intro x hx
    rw [hbot] at hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hx1, mul_one, one_mul]
  · -- Lemma 2.3(i): `F_π(M) ≤ Ĥ`
    have hleπ : Work.GW2.fittingPiIn B.pi M ≤ B.Hhat :=
      (h23 G hFT hCtx B M hD.M_ne_top hD.rel).1 hpg
    have ht2 : B.t * B.t = 1 := by
      have h := pow_orderOf_eq_one B.t
      rw [B.t_order] at h
      simpa [pow_two] using h
    have hodd : Odd (Nat.card (Work.GW2.fittingPiIn σ M)) :=
      odd_card_fittingPiIn_local hsub2 M
    have h2pow : IsPGroup 2 (Work.GW2.pCoreIn 2 B.Hhat) := isPGroup_pCoreIn_two B.Hhat
    have htP : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := L27cf_t_mem_pCoreIn_two h26 hFT hCtx B
    have htN : B.t ∈ Subgroup.normalizer
        ((Work.GW2.fittingPiIn σ M : Subgroup G) : Set G) :=
      le_normalizer_fittingPiIn_local σ M hD.t_mem
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    -- `x ∈ F_σ(M) ≤ F_π(M) ≤ Ĥ`
    have hxH : x ∈ B.Hhat := hleπ (fittingPiIn_mono_local hsubπ M hx)
    -- the commutator lies in `F_σ(M)`
    have hcom_mem : ⁅B.t, x⁆ ∈ Work.GW2.fittingPiIn σ M := by
      have h1 : B.t * x * B.t⁻¹ ∈ Work.GW2.fittingPiIn σ M :=
        (Subgroup.mem_normalizer_iff.mp htN x).mp hx
      have h2 : x⁻¹ ∈ Work.GW2.fittingPiIn σ M := (Work.GW2.fittingPiIn σ M).inv_mem hx
      rw [commutatorElement_def]
      exact (Work.GW2.fittingPiIn σ M).mul_mem h1 h2
    -- the commutator lies in the `2`-group `O₂(Ĥ)`
    have hcom_P : ⁅B.t, x⁆ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      have hle2 : ⁅(Work.GW2.pCoreIn 2 B.Hhat : Subgroup G), B.Hhat⁆ ≤
          Work.GW2.pCoreIn 2 B.Hhat := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          (L27cf_le_normalizer_pCoreIn_two B.Hhat)
      exact hle2 (Subgroup.commutator_mem_commutator htP hxH)
    -- a `2`-power which is odd is `1`
    have hcom_eq_one : ⁅B.t, x⁆ = 1 := by
      have h1 : orderOf ⁅B.t, x⁆ ∣ Nat.card (Work.GW2.fittingPiIn σ M) := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcom_mem)
        rwa [Nat.card_zpowers] at h
      have h2 : orderOf ⁅B.t, x⁆ ∣ Nat.card (Work.GW2.pCoreIn 2 B.Hhat) := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcom_P)
        rwa [Nat.card_zpowers] at h
      have ho : Odd (orderOf ⁅B.t, x⁆) := Odd.of_dvd_nat hodd h1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2pow
      have h2' : orderOf ⁅B.t, x⁆ ∣ 2 ^ k := by rw [← hk]; exact h2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2'
      have hj0 : j = 0 := by
        by_contra hjn
        have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 hjn
        rw [← hj] at h2j
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h2j)
      have hone : orderOf ⁅B.t, x⁆ = 1 := by rw [hj, hj0, pow_zero]
      exact orderOf_eq_one_iff.mp hone
    -- conclude `B.t * x = x * B.t`
    rw [commutatorElement_def] at hcom_eq_one
    have hx1 : B.t * x * B.t⁻¹ = x := by
      calc B.t * x * B.t⁻¹ = B.t * x * B.t⁻¹ * x⁻¹ * x := by group
        _ = 1 * x := by rw [hcom_eq_one]
        _ = x := one_mul x
    calc B.t * x = B.t * x * B.t⁻¹ * B.t := by group
      _ = x * B.t := by rw [hx1]

/-! ## 5. The target -/

theorem L27_centralizes_fittingIn :
    ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        ⁅M, Subgroup.zpowers B.t⁆ ≤ Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  -- the three pieces
  have hcen2 : ∀ x ∈ Work.GW2.fittingPiIn ({2} : Set ℕ) M, B.t * x * B.t⁻¹ = x := by
    intro x hx
    have h := Subgroup.mem_centralizer_iff.mp (two_part_centralized_local hCtx B M hD hx) B.t rfl
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hcenσ : ∀ x ∈ Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M, B.t * x * B.t⁻¹ = x := by
    intro x hx
    have h := Subgroup.mem_centralizer_iff.mp (odd_pi_part_centralized_local h23 h26 hFT hCtx B M hD hx)
      B.t rfl
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hinvπ : ∀ x ∈ Work.GW2.fittingPiIn B.piᶜ M, B.t * x * B.t⁻¹ = x⁻¹ :=
    L27cf_inverts_fittingPiIn_pi_compl h23 h26 hFT hCtx B M hD
  -- the three pieces are normalized by `M`
  have hnorm : ∀ π : Set ℕ, M ≤
      Subgroup.normalizer ((Work.GW2.fittingPiIn π M : Subgroup G) : Set G) :=
    fun π => le_normalizer_fittingPiIn_local π M
  -- the nilpotent splitting of `F(M)` into the three pieces
  have hdec : Work.GW2.fittingIn M ≤
      Work.GW2.fittingPiIn ({2} : Set ℕ) M ⊔
        Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ⊔ Work.GW2.fittingPiIn B.piᶜ M :=
    L27cf_fittingIn_le_sup_three M (fun q _ => by
      rcases eq_or_ne q 2 with h | h
      · exact Or.inl (by rw [h]; exact Set.mem_singleton 2)
      · by_cases hqπ : q ∈ B.pi
        · exact Or.inr (Or.inl ⟨hqπ, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact h⟩)
        · exact Or.inr (Or.inr (by rw [Set.mem_compl_iff]; exact hqπ)))
  exact comm_le_centralizer_of_three (hnorm {2}) (hnorm (B.pi ∩ ({2}ᶜ : Set ℕ)))
    (hnorm B.piᶜ) hcen2 hcenσ hinvπ ht2 hdec

end Work.CORE2B
