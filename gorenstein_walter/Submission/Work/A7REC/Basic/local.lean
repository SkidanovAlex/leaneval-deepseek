/-
Area `A7REC` (recognition of `A₇`), file `Basic/local.lean`.

# The local structure of a group satisfying the `A₇` hypotheses

Everything in this file is a consequence of the hypotheses `A7RecCtx G` alone -- no character
theory and no recognition input is used.  The two substantive statements are

* `card_centralizer_U` : `|C_G(U)| = 36`, so that `N_G(U)/C_G(U) ≅ C₂`; this is the value
  Suzuki 1959 §8 obtains (`C_G(U)` of order `36`, normalizer of order `72`);
* `index_centralizer_U`, `index_NU`, `index_centralizer_z` : the indices `70`, `35`, `105`,
  i.e. the numbers of conjugates of `U`, of `V`, and of `z`.

The key point of `card_centralizer_U` is that `|C_G(U)| = 72` is impossible: it would force
`S ≤ C_G(U)`, hence `C_G(z) = U × S` with `S` normal of order `8` in `C_G(z)`, contradicting
`V = O₂(C_G(z))` being a *four*-group.
-/
import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Basic.card_S
import Submission.Work.A7REC.Basic.V_le_C
import Submission.Work.A7REC.Basic.card_centralizer_z
import Submission.Work.A7REC.Basic.four_subgroups_of_S

namespace Work.A7REC.Basic

open Subgroup

/-- **A normal `p`-subgroup is contained in `O_p`.**  `O_p K` is the normal core of the
supremum of all normal `p`-subgroups of `K`; a normal `p`-subgroup `M` is one of them, and
since `M` is normal it survives taking the normal core. -/
theorem le_pCore_of_normal {K : Type*} [Group K] {p : ℕ} {M : Subgroup K} [M.Normal]
    (hM : IsPGroup p M) : M ≤ Work.A7REC.pCore p K :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hM⟩)

/-- `U ≤ C_G(z)`: immediate from `C_G(z) = U ⊔ S`. -/
theorem U_le_centralizer (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.U ≤ Subgroup.centralizer ({ctx.z} : Set G) := by
  rw [ctx.hCz]
  exact le_sup_left

/-- `V = O₂(C_G(z))` is normal in `C_G(z)`. -/
theorem V_normal_C (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (ctx.V.subgroupOf (Subgroup.centralizer ({ctx.z} : Set G))).Normal := by
  set K : Subgroup G := ctx.U ⊔ (ctx.S : Subgroup G) with hK
  have hVK : ctx.V = (Work.A7REC.pCore 2 K).map K.subtype := by
    rw [hK]; exact ctx.hVdef
  have hCK : Subgroup.centralizer ({ctx.z} : Set G) = K := by rw [hK, ctx.hCz]
  rw [hVK, hCK, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K)]
  exact Work.A7REC.pCore_normal 2 K

/-- `S ≤ C_G(z)`: `z` is central in `S`. -/
theorem S_le_centralizer_z (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (ctx.S : Subgroup G) ≤ Subgroup.centralizer ({ctx.z} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (ctx.hzcen s hs).symm

/-- `C_G(z) ≤ N_G(V)`: `V = O₂(C_G(z))` is normal in `C_G(z)`. -/
theorem centralizer_z_le_normalizer_V (G : Type*) [Group G] [Finite G]
    (ctx : Work.A7REC.A7RecCtx G) :
    Subgroup.centralizer ({ctx.z} : Set G) ≤ Subgroup.normalizer (ctx.V : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (V_le_C G ctx)).mp (V_normal_C G ctx)

/-- Since `S ≤ C_G(z) ≤ N_G(V) = N_G(U)`, `S` is contained in the normalizer of `U`. -/
theorem S_le_normalizer_U (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (ctx.S : Subgroup G) ≤ Subgroup.normalizer (ctx.U : Set G) := by
  have h : (ctx.S : Subgroup G) ≤ Subgroup.normalizer (ctx.V : Set G) :=
    le_trans (S_le_centralizer_z G ctx) (centralizer_z_le_normalizer_V G ctx)
  rw [ctx.hNUV]
  exact h

/-- The index of `N_G(U)`: `2520/72 = 35`, the number of conjugates of `U` (equivalently of
`V`, since `N_G(U) = N_G(V)`). -/
theorem index_NU (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (Subgroup.normalizer (ctx.U : Set G)).index = 35 := by
  have h := Subgroup.card_mul_index (Subgroup.normalizer (ctx.U : Set G))
  rw [ctx.hNUcard, ctx.hcard] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 72 by norm_num)
    (by rw [show 72 * 35 = (2520 : ℕ) from by norm_num]; exact h)

/-- The index of `C_G(z)`: `2520/24 = 105`, the number of involutions conjugate to `z`. -/
theorem index_centralizer_z (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (Subgroup.centralizer ({ctx.z} : Set G)).index = 105 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({ctx.z} : Set G))
  rw [card_centralizer_z G ctx, ctx.hcard] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 24 by norm_num)
    (by rw [show 24 * 105 = (2520 : ℕ) from by norm_num]; exact h)

/-- **`|C_G(U)| = 36`.**

`U ⊴ N_G(U)` and `N_G(U)/C_G(U) ↪ Aut(U) ≅ C₂` give `|C_G(U)| | 72` with
`[N_G(U) : C_G(U)] ≤ 2`, hence `|C_G(U)| ∈ {36, 72}`.  The value `72` would mean
`C_G(U) = N_G(U)`, hence (as `S ≤ N_G(U)`) that `S` centralizes `U`; then `S` is a normal
`2`-subgroup of `C_G(z) = U ⊔ S` of order `8`, so `S ≤ O₂(C_G(z)) = V`, contradicting
`|V| = 4`. -/
theorem card_centralizer_U (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Nat.card (Subgroup.centralizer (ctx.U : Set G)) = 36 := by
  have hC_le_N : Subgroup.centralizer (ctx.U : Set G) ≤ Subgroup.normalizer (ctx.U : Set G) :=
    Subgroup.centralizer_le_normalizer _
  -- the conjugation hom `N_G(U) →* Aut(U)`
  have hker : Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).ker
      = Nat.card (Subgroup.centralizer (ctx.U : Set G)) := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_N).toEquiv
  have hprod : Nat.card (Subgroup.centralizer (ctx.U : Set G)) *
      Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).range = 72 := by
    have h := card_ker_mul_card_range (Subgroup.normalizerMonoidHom (H := ctx.U))
    rw [hker, ctx.hNUcard] at h
    exact h
  -- `Aut(U)` has order `2`
  haveI : IsCyclic ↥ctx.U := isCyclic_of_card_dvd_prime (p := 3) (by rw [ctx.hUcard])
  have hAut : Nat.card (MulAut ↥ctx.U) = 2 := by
    rw [IsCyclic.card_mulAut, ctx.hUcard]
    decide
  have hrange_le : Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).range ≤ 2 := by
    calc Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).range
        ≤ Nat.card (⊤ : Subgroup (MulAut ↥ctx.U)) := Subgroup.card_le_of_le le_top
      _ = Nat.card (MulAut ↥ctx.U) := Subgroup.card_top
      _ = 2 := hAut
  have hge : 36 ≤ Nat.card (Subgroup.centralizer (ctx.U : Set G)) := by
    have h2 : 72 ≤ Nat.card (Subgroup.centralizer (ctx.U : Set G)) * 2 := by
      calc (72 : ℕ) = Nat.card (Subgroup.centralizer (ctx.U : Set G)) *
            Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).range := hprod.symm
        _ ≤ Nat.card (Subgroup.centralizer (ctx.U : Set G)) * 2 :=
            Nat.mul_le_mul_left _ hrange_le
    omega
  have hdvd : Nat.card (Subgroup.centralizer (ctx.U : Set G)) ∣ 72 :=
    ⟨Nat.card (Subgroup.normalizerMonoidHom (H := ctx.U)).range, hprod.symm⟩
  rcases hdvd with ⟨k, hk⟩
  have hk_le : k ≤ 2 := by
    have h36k : 36 * k ≤ 72 := by
      calc 36 * k ≤ Nat.card (Subgroup.centralizer (ctx.U : Set G)) * k :=
            Nat.mul_le_mul_right k hge
        _ = 72 := hk.symm
    omega
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  rcases (by omega : k = 1 ∨ k = 2) with h1 | h2
  · -- `|C_G(U)| = 72`: contradiction
    exfalso
    have h72 : Nat.card (Subgroup.centralizer (ctx.U : Set G)) = 72 := by
      rw [h1, mul_one] at hk
      omega
    have hCN : Subgroup.centralizer (ctx.U : Set G) = Subgroup.normalizer (ctx.U : Set G) :=
      Subgroup.eq_of_le_of_card_ge hC_le_N (by rw [ctx.hNUcard, h72])
    -- `S ≤ C_G(U)`, so `S` centralizes `U`
    have hS_le_CU : (ctx.S : Subgroup G) ≤ Subgroup.centralizer (ctx.U : Set G) := by
      rw [hCN]
      exact S_le_normalizer_U G ctx
    have hcomm : ∀ s ∈ (ctx.S : Subgroup G), ∀ u ∈ ctx.U, u * s = s * u := by
      intro s hs u hu
      exact Subgroup.mem_centralizer_iff.mp (hS_le_CU hs) u hu
    -- `U` normalizes `S`, and so does `S`; hence `S ⊴ C_G(z) = U ⊔ S`
    have hU_le_NS : ctx.U ≤ Subgroup.normalizer ((ctx.S : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro u hu s hs
      rw [hcomm s hs u hu, mul_assoc, mul_inv_cancel, mul_one]
      exact hs
    have hS_C : (ctx.S : Subgroup G) ≤ Subgroup.centralizer ({ctx.z} : Set G) :=
      S_le_centralizer_z G ctx
    -- `S ⊴ U ⊔ S`, since `U` and `S` both normalize `S`
    have hSnorm : ((ctx.S : Subgroup G).subgroupOf (ctx.U ⊔ (ctx.S : Subgroup G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
        (sup_le hU_le_NS Subgroup.le_normalizer)
    have hSp : IsPGroup 2 ((ctx.S : Subgroup G).subgroupOf (ctx.U ⊔ (ctx.S : Subgroup G))) :=
      IsPGroup.of_card_dvd_pow (p := 2) (n := 3) (by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (le_sup_right : (ctx.S : Subgroup G) ≤
            ctx.U ⊔ (ctx.S : Subgroup G))).toEquiv, card_S G ctx]
        norm_num)
    haveI : ((ctx.S : Subgroup G).subgroupOf (ctx.U ⊔ (ctx.S : Subgroup G))).Normal := hSnorm
    have hle_pcore : ((ctx.S : Subgroup G).subgroupOf (ctx.U ⊔ (ctx.S : Subgroup G))) ≤
        Work.A7REC.pCore 2 ↥(ctx.U ⊔ (ctx.S : Subgroup G)) :=
      le_pCore_of_normal hSp
    have hS_le_V : (ctx.S : Subgroup G) ≤ ctx.V := by
      rw [ctx.hVdef]
      calc (ctx.S : Subgroup G)
          = ((ctx.S : Subgroup G).subgroupOf (ctx.U ⊔ (ctx.S : Subgroup G))).map
              (ctx.U ⊔ (ctx.S : Subgroup G)).subtype := by
            rw [Subgroup.subgroupOf_map_subtype]
            exact (inf_eq_left.mpr le_sup_right).symm
        _ ≤ (Work.A7REC.pCore 2 ↥(ctx.U ⊔ (ctx.S : Subgroup G))).map
              (ctx.U ⊔ (ctx.S : Subgroup G)).subtype := Subgroup.map_mono hle_pcore
    have hcard := Subgroup.card_le_of_le hS_le_V
    rw [card_S G ctx, ctx.hV4.1] at hcard
    omega
  · have h36 : Nat.card (Subgroup.centralizer (ctx.U : Set G)) = 36 := by
      rw [h2] at hk
      omega
    exact h36

/-- Normality transfer: if `N ⊴ K` (both subgroups of `G`) then `k * n * k⁻¹ ∈ N` for
`k ∈ K`, `n ∈ N`. -/
theorem conj_mem_of_subgroupOf_normal {G : Type*} [Group G] {N K : Subgroup G} (hNK : N ≤ K)
    (h : (N.subgroupOf K).Normal) {k n : G} (hk : k ∈ K) (hn : n ∈ N) : k * n * k⁻¹ ∈ N :=
  h.conj_mem (⟨n, hNK hn⟩ : ↥K) (show (⟨n, hNK hn⟩ : ↥K) ∈ N.subgroupOf K from hn) (⟨k, hk⟩ : ↥K)

/-- **`⁅U, V⁆ = ⊥`.**

`U` and `V` are both normal in `C_G(z)` (`hUnorm`, `V_normal_C`) and have coprime orders, so they
centralize each other: for `u ∈ U`, `v ∈ V` the commutator `v*u*v⁻¹*u⁻¹` lies in `U` (both
factors do, by normality of `U` in `C_G(z)`) and in `V` (both factors do, by normality of `V`),
hence in `U ⊓ V = ⊥`. -/
theorem commute_U_V (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ⁅ctx.U, ctx.V⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hUC : ctx.U ≤ Subgroup.centralizer ({ctx.z} : Set G) := U_le_centralizer G ctx
  have hVC : ctx.V ≤ Subgroup.centralizer ({ctx.z} : Set G) := V_le_C G ctx
  have hUn : (ctx.U.subgroupOf (Subgroup.centralizer ({ctx.z} : Set G))).Normal := ctx.hUnorm
  have hVn : (ctx.V.subgroupOf (Subgroup.centralizer ({ctx.z} : Set G))).Normal := V_normal_C G ctx
  have hbot : ctx.U ⊓ ctx.V = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have h1 : Nat.card ↥(ctx.U ⊓ ctx.V) ∣ 3 := by
      rw [← ctx.hUcard]
      exact Subgroup.card_dvd_of_le (α := G) inf_le_left
    have h2 : Nat.card ↥(ctx.U ⊓ ctx.V) ∣ 4 := by
      rw [← ctx.hV4.1]
      exact Subgroup.card_dvd_of_le (α := G) inf_le_right
    have hg : Nat.card ↥(ctx.U ⊓ ctx.V) ∣ 1 := by
      have h := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 3 4 = 1 from by norm_num] at h
    exact Nat.dvd_one.mp hg
  have hwU : v * u * v⁻¹ * u⁻¹ ∈ ctx.U := by
    have h1 : v * u * v⁻¹ ∈ ctx.U := conj_mem_of_subgroupOf_normal hUC hUn (hVC hv) hu
    exact ctx.U.mul_mem h1 (ctx.U.inv_mem hu)
  have hwV : v * u * v⁻¹ * u⁻¹ ∈ ctx.V := by
    have h1 : u * v⁻¹ * u⁻¹ ∈ ctx.V := conj_mem_of_subgroupOf_normal hVC hVn (hUC hu) (ctx.V.inv_mem hv)
    have h2 : v * (u * v⁻¹ * u⁻¹) = v * u * v⁻¹ * u⁻¹ := by group
    rw [← h2]
    exact ctx.V.mul_mem hv h1
  have hw : v * u * v⁻¹ * u⁻¹ = 1 := by
    have hmem : v * u * v⁻¹ * u⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hwU, hwV⟩
    simpa using hmem
  have hwu : v * u * (u * v)⁻¹ = 1 := by
    simpa [mul_inv_rev, mul_assoc] using hw
  exact mul_inv_eq_one.mp hwu

/-- **`z ∈ V`.**  Every four-subgroup of a dihedral group of order `8` contains its centre, and
`V ≤ S` is a four-subgroup (`V_le_S`, `hV4`), while `z` is the central involution of `S`
(`hzcen`, `hz2`).  This is `mem_of_isFourGroup_le_dihedral` from
`Basic/four_subgroups_of_S.lean`, applied to `V`. -/
theorem z_mem_V (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.z ∈ ctx.V :=
  mem_of_isFourGroup_le_dihedral (S := (ctx.S : Subgroup G)) ctx.hSdih ctx.hzS ctx.hz2
    ctx.hzcen (V_le_S G ctx) ctx.hV4.1 ctx.hV4.2

/-- The index of `C_G(U)`: `2520/36 = 70`, the number of conjugates of `U`. -/
theorem index_centralizer_U (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    (Subgroup.centralizer (ctx.U : Set G)).index = 70 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer (ctx.U : Set G))
  rw [card_centralizer_U G ctx, ctx.hcard] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 36 by norm_num)
    (by rw [show 36 * 70 = (2520 : ℕ) from by norm_num]; exact h)

/-- **There is an elementary abelian subgroup of order `9` containing `U`.**

By the crossing hypothesis there is a conjugate `U^g ≠ U` inside `N_G(V) = N_G(U)`; then
`T = U ⊔ U^g` has order `3 · 3 = 9` and is commutative (groups of order `p²` are), so
`T ≤ C_G(U)`.  In particular the Sylow `3`-subgroups of `G` are not cyclic, and `G` has no
element of order `9`. -/
theorem exists_order_nine (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ∃ T : Subgroup G, Nat.card T = 9 ∧ ctx.U ≤ T ∧ T ≤ Subgroup.normalizer (ctx.U : Set G) ∧
      T ≤ Subgroup.centralizer (ctx.U : Set G) := by
  obtain ⟨g, hg_ne, hg_le⟩ := ctx.hcross
  set T : Subgroup G := ctx.U ⊔ ctx.U.map (MulAut.conj g).toMonoidHom with hT
  have hWcard : Nat.card (ctx.U.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [← ctx.hUcard]
    exact (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) ctx.U).toEquiv).symm
  have hWle : ctx.U.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (ctx.U : Set G) := by
    rw [ctx.hNUV]
    exact hg_le
  have hbot : ctx.U ⊓ ctx.U.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have hdvd : Nat.card ↥(ctx.U ⊓ ctx.U.map (MulAut.conj g).toMonoidHom) ∣ 3 := by
      rw [← ctx.hUcard]
      exact Subgroup.card_dvd_of_le (α := G) inf_le_left
    have hne : Nat.card ↥(ctx.U ⊓ ctx.U.map (MulAut.conj g).toMonoidHom) ≠ 3 := by
      intro h3
      have heq : ctx.U ⊓ ctx.U.map (MulAut.conj g).toMonoidHom = ctx.U :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, ctx.hUcard])
      have hle : ctx.U ≤ ctx.U.map (MulAut.conj g).toMonoidHom :=
        (le_of_eq heq.symm).trans inf_le_right
      have heq2 : ctx.U = ctx.U.map (MulAut.conj g).toMonoidHom :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hWcard, ctx.hUcard])
      exact hg_ne heq2.symm
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exact absurd h hne
  have hcard9 : Nat.card ↥T = 9 := by
    have hd : Disjoint ctx.U (ctx.U.map (MulAut.conj g).toMonoidHom) :=
      disjoint_iff.mpr (by rw [hbot])
    rw [hT, card_sup_mul_card_of_le_normalizer_of_disjoint hWle hd, ctx.hUcard, hWcard]
  refine ⟨T, hcard9, ?_, ?_, ?_⟩
  · rw [hT]; exact le_sup_left
  · rw [hT]; exact sup_le Subgroup.le_normalizer hWle
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    haveI : IsMulCommutative ↥T :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard9]; norm_num)
    have hcomm : ∀ a b : ↥T, a * b = b * a :=
      isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥T)
    have hmem : u ∈ T := by rw [hT]; exact Subgroup.mem_sup_left hu
    exact congrArg (fun x : ↥T => (x : G)) (hcomm (⟨u, hmem⟩ : ↥T) (⟨t, ht⟩ : ↥T))

/-- **The Suzuki §8 case analysis, arithmetic part.**

If `H ≤ G` contains a subgroup of order `24` (in §8: `H ≥ ⟨U, S'⟩`, of order `24`) and its index is
divisible by `7` (in §8: `H` contains no element of order `7`, because the degree-`6` character
`Y` satisfies `dim Fix(C₇) = 0`), then `|H| ∈ {24, 72, 120, 360}`.  Suzuki rules out the first
three by local arguments and concludes `|H| = 360`, i.e. `[G : H] = 7`. -/
theorem card_eq_of_dvd_24_and_index_dvd_seven (G : Type*) [Group G] [Finite G]
    (ctx : Work.A7REC.A7RecCtx G) {H : Subgroup G} (h24 : 24 ∣ Nat.card H)
    (h7 : 7 ∣ H.index) :
    Nat.card H = 24 ∨ Nat.card H = 72 ∨ Nat.card H = 120 ∨ Nat.card H = 360 := by
  have h := Subgroup.card_mul_index H
  rw [ctx.hcard] at h
  rcases h7 with ⟨k, hk⟩
  rw [hk] at h
  -- `|H| * 7 * k = 2520`, i.e. `|H| * k = 360`
  have h360 : Nat.card H * k = 360 := by
    have h'' : 7 * (Nat.card H * k) = 2520 := by
      rw [← h]; ring
    have h' : 7 * (Nat.card H * k) = 7 * 360 := by rw [h'']
    exact Nat.eq_of_mul_eq_mul_left (show 0 < 7 by norm_num) h'
  rcases h24 with ⟨m, hm⟩
  -- `|H| = 24 * m` and `24 * m * k = 360`, so `m * k = 15`
  have hmk : m * k = 15 := by
    rw [hm, mul_assoc] at h360
    omega
  have hm_le : m ≤ 15 := Nat.le_of_dvd (by norm_num) ⟨k, hmk.symm⟩
  interval_cases m <;> omega

end Work.A7REC.Basic
