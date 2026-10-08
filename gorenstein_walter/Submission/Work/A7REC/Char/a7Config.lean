/-
Area `A7REC`, file `Char/a7Config.lean`: **C2** of the pass-8 design
(`Submission/Work/_design_gw/Core8.lean` §1, `Work.A7REC.A7ConfigProp`).

Let `G` satisfy the `A₇` hypotheses (`A7RecHyps G S z U V`, i.e. `|G| = 2520`, `S` a Sylow
`2`-subgroup isomorphic to `D₈`, `z` its central involution, `C_G(z) = U ⊔ S` with `|U| = 3`,
`V = O₂(C_G(z))` a four-group, `N_G(U) = N_G(V)` of order `72`), and suppose that `G` has a
single class of involutions.  We produce the **Suzuki configuration** `(U, S', τ)`:
a Sylow `2`-subgroup `S'` and an involution `τ ∈ Z(S')` normalizing `U` with
`S' ∩ C_G(U) = 1`.

The construction (design pass 8, §1.2):

* `S ∩ C_G(U) = V`: the `2`-part of `C_G(U)` is `4` and `V ⊴ C_G(U)`;
* take an involution `τ ∈ S \ V` (a dihedral group of order `8` has five involutions and a
  four-subgroup only three, so such a `τ` exists); then `τ ∈ N_G(U) \ C_G(U)`, hence
  `U^τ = U`;
* one-class gives `τ = z^g`; set `V' = V^g`.  Then `z ∉ V'` (if `z ∈ V'` then `U^g ≤ C_G(z)`,
  so `U^g = U` by uniqueness of the order-`3` subgroup of `C_G(z)`, and `τ = z^g ∈ C_G(U)`, a
  contradiction);
* a normal `2`-subgroup of `C_G(τ)` has order `≤ 4`, so not every Sylow `2`-subgroup of
  `C_G(τ)` contains `z` (`sylowNotMemOfCard24`); take such a Sylow `2`-subgroup `S'` of `G`
  (its order is `8 = |G|₂`);
* `τ ∈ S'` because `⟨τ⟩ ◁ C_G(τ)` is contained in every Sylow `2`-subgroup of `C_G(τ)`;
* finally `S' ∩ C_G(U) ⊆ V ∩ C_G(τ) = ⟨z⟩` and `z ∉ S'`, so `S' ∩ C_G(U) = 1`.
-/
import Mathlib
import Submission.Work.A7REC.Excl
import Submission.Work.A7REC.Basic.card_centralizer_V
import Submission.Work.A7REC.Char.involutionNotMemFour
import Submission.Work.A7REC.Char.sylowNotMemOfCard24

namespace Work.A7REC.Char

open Subgroup

/-! ## Conjugating centralizers -/

/-- For a bijective monoid homomorphism `f : G →* G'`, the image of the centralizer of a set `s`
is the centralizer of the image `f '' s`. -/
theorem mapCentralizerOfBijective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Bijective f) (s : Set G) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f) ?_
  intro z hz
  obtain ⟨y, rfl⟩ := hf.2 z
  rw [Subgroup.mem_map]
  refine ⟨y, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro a ha
  exact hf.1 (by simpa using hz (f a) ⟨a, ha, rfl⟩)

/-- The image of `C_G(x)` under conjugation by `g` is `C_G(g * x * g⁻¹)`. -/
theorem mapConjCentralizer {G : Type*} [Group G] (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom
      = Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  rw [mapCentralizerOfBijective _ (MulAut.conj g).bijective]
  congr 1
  ext y
  simp [MulAut.conj_apply]

/-- The centralizers of conjugate elements have the same cardinality. -/
theorem cardCentralizerConj {G : Type*} [Group G] (x g : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  rw [← mapConjCentralizer g x, Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-! ## Small arithmetic: the `2`-parts -/

theorem two_pow_factorization_24 : 2 ^ (24 : ℕ).factorization 2 = 8 := by
  have h : (24 : ℕ).factorization 2 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num)]
    norm_num [Nat.Prime.factorization]
  rw [h]; norm_num

theorem two_pow_factorization_36 : 2 ^ (36 : ℕ).factorization 2 = 4 := by
  have h : (36 : ℕ).factorization 2 = 2 := by
    rw [show (36 : ℕ) = 2 ^ 2 * 9 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num)]
    norm_num [Nat.Prime.factorization]
  rw [h]; norm_num

theorem two_pow_factorization_2520 : 2 ^ (2520 : ℕ).factorization 2 = 8 := by
  have h : (2520 : ℕ).factorization 2 = 3 := by
    rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num)]
    norm_num [Nat.Prime.factorization]
  rw [h]; norm_num

/-! ## The configuration `C2` -/

theorem a7Config : Work.A7REC.A7ConfigProp := by
  intro G _instG _finG S z U V hyps hone
  let ctx : Work.A7REC.A7RecCtx G := Work.A7REC.A7RecCtx.ofHyps hyps
  -- local copies of the hypothesis fields, in the syntactic form used below
  have hGcard : Nat.card G = 2520 := ctx.hcard
  have hS8 : Nat.card (S : Subgroup G) = 8 := Work.A7REC.Basic.card_S G ctx
  have hCz24 : Nat.card (Subgroup.centralizer ({z} : Set G)) = 24 :=
    Work.A7REC.Basic.card_centralizer_z G ctx
  have hCU36 : Nat.card (Subgroup.centralizer (U : Set G)) = 36 :=
    Work.A7REC.Basic.card_centralizer_U G ctx
  have hUcard' : Nat.card U = 3 := ctx.hUcard
  have hz2' : orderOf z = 2 := ctx.hz2
  have hCz' : Subgroup.centralizer ({z} : Set G) = U ⊔ (S : Subgroup G) := ctx.hCz
  have hNUV' : Subgroup.normalizer (U : Set G) = Subgroup.normalizer (V : Set G) := ctx.hNUV
  have hVdef'' : V = Work.A7REC.pCoreIn 2 (U ⊔ (S : Subgroup G)) := ctx.hVdef
  have hUnorm' : (U.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := ctx.hUnorm
  have hVcard : Nat.card V = 4 := ctx.hV4.1
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    simpa [pow_two] using ctx.hV4.2 v hv
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Work.A7REC.Basic.commute_of_sq_eq_one (hVsq a ha) (hVsq b hb)
      (hVsq (a * b) (V.mul_mem ha hb))
  have hV_le_S : V ≤ (S : Subgroup G) := Work.A7REC.Basic.V_le_S G ctx
  have hV_le_Cz : V ≤ Subgroup.centralizer ({z} : Set G) := Work.A7REC.Basic.V_le_C G ctx
  have hzV : z ∈ V := Work.A7REC.Basic.z_mem_V G ctx
  have hzsq : z * z = 1 := by
    have h : z ^ 2 = 1 := (orderOf_eq_prime_iff.mp hz2').1
    simpa [pow_two] using h
  have hV_le_CU : V ≤ Subgroup.centralizer (U : Set G) := by
    have h := Work.A7REC.Basic.commute_U_V G ctx
    rw [Subgroup.commutator_comm] at h
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := V) (H₂ := U)).mp h
  have hz_in_CU : z ∈ Subgroup.centralizer (U : Set G) := hV_le_CU hzV

  -- ### Step 1: `S ⊓ C_G(U) = V`
  have hSinfCU : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = V := by
    have hle : V ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := le_inf hV_le_S hV_le_CU
    have hdvd : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ∣ 8 := by
      have h := Subgroup.card_dvd_of_le (α := G)
        (inf_le_left : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ (S : Subgroup G))
      rwa [hS8] at h
    have hne8 : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ≠ 8 := by
      intro h8
      have hEq : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = (S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hS8])
      have hS_le : (S : Subgroup G) ≤ Subgroup.centralizer (U : Set G) := hEq ▸ inf_le_right
      have hdvd8 : (8 : ℕ) ∣ 36 := by
        have h := Subgroup.card_dvd_of_le (α := G) hS_le
        rwa [hS8, hCU36] at h
      norm_num at hdvd8
    have hge : 4 ≤ Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) := by
      have h := Subgroup.card_le_of_le hle
      rwa [hVcard] at h
    have hcard4 : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) = 4 := by
      rcases hdvd with ⟨k, hk⟩
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hkle : k ≤ 2 := by nlinarith
      interval_cases k
      · omega
      · omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard4, hVcard])).symm

  -- ### Step 2: an involution `τ ∈ S \ V`
  obtain ⟨eS⟩ := ctx.hSdih
  obtain ⟨t, ht2, htW⟩ :=
    involutionNotMemFour eS (V.subgroupOf (S : Subgroup G)) (fun w hw => Subtype.ext (by
      have hw' : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
      simpa using hVsq (w : G) hw'))
  set τ : G := (t : G) with hτdef
  have hτ_mem_S : τ ∈ (S : Subgroup G) := t.2
  have hτ_notin_V : τ ∉ V := fun h => htW h
  have hτsq : τ * τ = 1 := by
    have := congrArg (fun x : ↥(S : Subgroup G) => (x : G)) ht2
    simpa using this
  have ht_ne : t ≠ 1 := fun h => htW (h ▸ (V.subgroupOf (S : Subgroup G)).one_mem)
  have hτ_ne : τ ≠ 1 := fun h => ht_ne (Subtype.ext h)
  have hτ2ord : orderOf τ = 2 :=
    orderOf_eq_prime (p := 2) (by simpa [pow_two] using hτsq) hτ_ne

  -- ### Step 3: `τ ∈ N_G(U) \ C_G(U)`
  have hτ_mem_NU : τ ∈ Subgroup.normalizer (U : Set G) :=
    Work.A7REC.Basic.S_le_normalizer_U G ctx hτ_mem_S
  have hτ_notin_CU : τ ∉ Subgroup.centralizer (U : Set G) := by
    intro h
    have : τ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := ⟨hτ_mem_S, h⟩
    rw [hSinfCU] at this
    exact hτ_notin_V this
  have hU_conj : U.map (MulAut.conj τ).toMonoidHom = U :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hτ_mem_NU

  -- ### Step 4: conjugation data `τ = g z g⁻¹`
  obtain ⟨g, hg⟩ := isConj_iff.mp (hone z τ hz2' hτ2ord)
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  let ψ : G →* G := ((MulAut.conj g)⁻¹).toMonoidHom
  have hφ : ∀ x : G, φ x = g * x * g⁻¹ := fun x => by
    show MulAut.conj g x = g * x * g⁻¹
    exact MulAut.conj_apply g x
  have hψ : ∀ x : G, ψ x = g⁻¹ * x * g := fun x => by
    show (MulAut.conj g)⁻¹ x = g⁻¹ * x * g
    rw [(map_inv MulAut.conj g).symm, MulAut.conj_apply, inv_inv]
  have hconj_apply : ∀ x : G, φ (ψ x) = x := fun x => by rw [hφ, hψ]; group
  have hconj_apply' : ∀ x : G, ψ (φ x) = x := fun x => by rw [hψ, hφ]; group
  have hφinj : Function.Injective φ := fun a b h => by
    have h2 := congrArg ψ h
    rwa [hconj_apply', hconj_apply'] at h2
  have hψinj : Function.Injective ψ := fun a b h => by
    have h2 := congrArg φ h
    rwa [hconj_apply, hconj_apply] at h2
  have hconj_z : φ z = τ := by rw [hφ]; exact hg
  set Cτ : Subgroup G := Subgroup.centralizer ({τ} : Set G) with hCτdef
  have hCτ24 : Nat.card ↥Cτ = 24 := by
    rw [hCτdef, ← hg, ← mapConjCentralizer g z,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hCz24
  set V' : Subgroup G := V.map φ with hV'def
  have hV'card : Nat.card ↥V' = 4 := by
    rw [hV'def, Subgroup.card_map_of_injective hφinj, hVcard]
  have hV'sq : ∀ v ∈ V', v * v = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul φ u u, hVsq u hu, map_one]
  have hτ_in_Cτ : τ ∈ Cτ := by
    rw [hCτdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  have hz_in_Cτ : z ∈ Cτ := by
    rw [hCτdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.A7REC.Basic.S_le_centralizer_z G ctx hτ_mem_S) z (Set.mem_singleton z)).symm
  have hV'_le_Cτ : V' ≤ Cτ := by
    rw [hV'def, hCτdef]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show τ * φ u = φ u * τ
    rw [← hconj_z, ← map_mul, ← map_mul]
    congr 1
    exact hVcomm z hzV u hu
  have hV'_norm : (V'.subgroupOf Cτ).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hV'_le_Cτ).mpr ?_
    rw [Subgroup.le_normalizer_iff]
    intro c hc v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    have hψc : ψ c ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hcτ : c * τ = τ * c :=
        (Subgroup.mem_centralizer_iff.mp hc τ (Set.mem_singleton τ)).symm
      have key : φ (z * ψ c) = φ (ψ c * z) := by
        rw [map_mul, map_mul, hconj_apply, hconj_z, hcτ]
      exact hφinj key
    have hmem : ψ c * u * (ψ c)⁻¹ ∈ V :=
      Work.A7REC.Basic.conj_mem_of_subgroupOf_normal hV_le_Cz (Work.A7REC.Basic.V_normal_C G ctx)
        hψc hu
    have key2 : c * φ u * c⁻¹ = φ (ψ c * u * (ψ c)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hconj_apply]
    rw [key2]
    exact Subgroup.mem_map_of_mem φ hmem

  -- ### Step 5: `z ∉ V'`
  have hU_uniq : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({z} : Set G) → Nat.card A = 3 →
      A = U := by
    intro A hA hAcard
    by_contra hne
    have hUA_le : U ⊔ A ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (Work.A7REC.Basic.U_le_centralizer G ctx) hA
    have hinf : U ⊓ A = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      have hdvd : Nat.card ↥(U ⊓ A) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (α := G) (inf_le_left : U ⊓ A ≤ U)
        rwa [hUcard'] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso
        have hA_le_U : A ≤ U := by
          have h1 : U ⊓ A = A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hAcard])
          exact (le_of_eq h1.symm).trans inf_le_left
        exact hne (Subgroup.eq_of_le_of_card_ge hA_le_U (by rw [hAcard, hUcard']))
    have hn : A ≤ Subgroup.normalizer (U : Set G) :=
      le_trans hA ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Work.A7REC.Basic.U_le_centralizer G ctx)).mp hUnorm')
    have hcard9 : Nat.card ↥(U ⊔ A) = 9 := by
      rw [Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint (A := U) (B := A) hn
        (disjoint_iff.mpr hinf), hUcard', hAcard]
    have hdvd9 : (9 : ℕ) ∣ 24 := by
      have h := Subgroup.card_dvd_of_le (α := G) hUA_le
      rwa [hcard9, hCz24] at h
    norm_num at hdvd9
  have hz_notin_V' : z ∉ V' := by
    intro hzV'
    have hU'_le_Cz : U.map φ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro u' hu'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzV'
      rw [← hwz, ← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_centralizer_iff.mp (hV_le_CU hw) u hu).symm
    have hU'card : Nat.card ↥(U.map φ) = 3 := by
      rw [Subgroup.card_map_of_injective hφinj, hUcard']
    have hU'eq : U.map φ = U := hU_uniq _ hU'_le_Cz hU'card
    have hφU : φ '' (U : Set G) = (U : Set G) := by
      rw [← Subgroup.coe_map, hU'eq]
    have hτ_in : φ z ∈ (Subgroup.centralizer (U : Set G)).map φ :=
      Subgroup.mem_map_of_mem φ hz_in_CU
    rw [mapCentralizerOfBijective φ (MulAut.conj g).bijective (U : Set G), hφU] at hτ_in
    exact hτ_notin_CU (hconj_z ▸ hτ_in)

  -- ### Step 6: `V ⊓ C_G(τ) = ⟨z⟩`
  have hV_not_le_Cτ : ¬ (V ≤ Cτ) := by
    intro hVle
    -- inside `↥S`: `V ⊔ ⟨τ⟩ = ⊤` and every element squares to `1`, so `↥S` is commutative
    set τs : ↥(S : Subgroup G) := ⟨τ, hτ_mem_S⟩ with hτsdef
    have hVs_norm : (V.subgroupOf (S : Subgroup G)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV_le_S).mpr (by
        rw [← hNUV']
        exact Work.A7REC.Basic.S_le_normalizer_U G ctx)
    haveI := hVs_norm
    have hτs_sq : τs * τs = 1 := Subtype.ext (by simpa using hτsq)
    have hτs_ne : τs ≠ 1 := fun h => hτ_ne (by
      have h' : (τs : G) = (1 : G) := congrArg Subtype.val h
      simpa [hτsdef] using h')
    have hτs_order : orderOf τs = 2 :=
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hτs_sq) hτs_ne
    have hdisj : Disjoint (V.subgroupOf (S : Subgroup G)) (Subgroup.zpowers τs) := by
      rw [disjoint_iff, Subgroup.eq_bot_iff_card]
      have hdvd : Nat.card ↥((V.subgroupOf (S : Subgroup G)) ⊓ Subgroup.zpowers τs) ∣ 2 := by
        have h := Subgroup.card_dvd_of_le (α := ↥(S : Subgroup G))
          (inf_le_right : (V.subgroupOf (S : Subgroup G)) ⊓ Subgroup.zpowers τs ≤
            Subgroup.zpowers τs)
        rwa [Nat.card_zpowers, hτs_order] at h
      have hne : Nat.card ↥((V.subgroupOf (S : Subgroup G)) ⊓ Subgroup.zpowers τs) ≠ 2 := by
        intro h2
        have heq : (V.subgroupOf (S : Subgroup G)) ⊓ Subgroup.zpowers τs = Subgroup.zpowers τs :=
          Subgroup.eq_of_le_of_card_ge inf_le_right
            (by rw [h2, Nat.card_zpowers, hτs_order])
        have : τs ∈ V.subgroupOf (S : Subgroup G) :=
          (le_of_eq heq.symm).trans inf_le_left (Subgroup.mem_zpowers τs)
        exact htW this
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd h hne
    have hVsub_card : Nat.card ↥(V.subgroupOf (S : Subgroup G)) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_S).toEquiv).trans hVcard
    have hsup : (V.subgroupOf (S : Subgroup G)) ⊔ Subgroup.zpowers τs = ⊤ := by
      have hcard : Nat.card ↥((V.subgroupOf (S : Subgroup G)) ⊔ Subgroup.zpowers τs) = 8 := by
        rw [Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint
          (A := V.subgroupOf (S : Subgroup G)) (B := Subgroup.zpowers τs)
          (by rw [Subgroup.normalizer_eq_top]; exact le_top) hdisj,
          hVsub_card, Nat.card_zpowers, hτs_order]
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw [Subgroup.card_top, hcard]
      exact le_of_eq hS8
    have hVsq_s : ∀ w ∈ V.subgroupOf (S : Subgroup G), w * w = 1 := fun w hw => Subtype.ext (by
      have hw' : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
      simpa using hVsq (w : G) hw')
    have hexp : ∀ x : ↥(S : Subgroup G), x * x = 1 := by
      intro x
      have hx : x ∈ V.subgroupOf (S : Subgroup G) ⊔ Subgroup.zpowers τs := by rw [hsup]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := V.subgroupOf (S : Subgroup G))
          (t := Subgroup.zpowers τs)).mp hx
      rw [← hab]
      have ha2 : a * a = 1 := hVsq_s a ha
      have hb2 : b * b = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← hk, ← zpow_add, show k + k = 2 * k by ring, zpow_mul, zpow_two, hτs_sq, one_zpow]
      have hcomm : a * b = b * a := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← hk]
        have haτ : a * τs = τs * a := Subtype.ext (by
          have hmem : (a : G) ∈ V := ha
          have hca : (a : G) ∈ Cτ := hVle hmem
          have h1 : τ * (a : G) = (a : G) * τ :=
            Subgroup.mem_centralizer_iff.mp hca τ (Set.mem_singleton τ)
          simpa using h1.symm)
        exact ((commute_iff_eq a τs).mpr haτ).zpow_right k
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, mul_one]
    have hcomm_all : ∀ x y : ↥(S : Subgroup G), x * y = y * x := fun x y =>
      Work.A7REC.Basic.commute_of_sq_eq_one (hexp x) (hexp y) (hexp (x * y))
    obtain ⟨x, y, hxy⟩ := Work.A7REC.Basic.exists_not_commute_dihedral_four eS
    exact hxy (hcomm_all x y)
  have hVinfCτ : V ⊓ Cτ = Subgroup.zpowers z := by
    have hle : Subgroup.zpowers z ≤ V ⊓ Cτ := Subgroup.zpowers_le.mpr ⟨hzV, hz_in_Cτ⟩
    have hdvd : Nat.card ↥(V ⊓ Cτ) ∣ 4 := by
      have h := Subgroup.card_dvd_of_le (α := G) (inf_le_left : V ⊓ Cτ ≤ V)
      rwa [hVcard] at h
    have hge : 2 ≤ Nat.card ↥(V ⊓ Cτ) := by
      have h := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, hz2'] at h
    have hne4 : Nat.card ↥(V ⊓ Cτ) ≠ 4 := by
      intro h4
      have heq : V ⊓ Cτ = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hVcard])
      exact hV_not_le_Cτ ((le_of_eq heq.symm).trans inf_le_right)
    have hcard2 : Nat.card ↥(V ⊓ Cτ) = 2 := by
      rcases hdvd with ⟨k, hk⟩
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hkle : k ≤ 2 := by nlinarith
      interval_cases k
      · omega
      · omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, Nat.card_zpowers, hz2'])).symm

  -- ### Step 7: bounds on the normal `2`-subgroups of `C_G(z)` and of `C_G(τ)`
  have hmaxz : ∀ N : Subgroup G, N ≤ Subgroup.centralizer ({z} : Set G) →
      (N.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal → IsPGroup 2 N →
      Nat.card N ≤ 4 := by
    intro N hN hNnorm hNp
    have hN_le_K : N ≤ U ⊔ (S : Subgroup G) := by rw [← hCz']; exact hN
    have hnormK : (N.subgroupOf (U ⊔ (S : Subgroup G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_K]
      intro x hx
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mp hNnorm (by rw [hCz']; exact hx)
    haveI := hnormK
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
    have hsub_card : Nat.card ↥(N.subgroupOf (U ⊔ (S : Subgroup G))) = 2 ^ k := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_K).toEquiv, hk]
    have hsub_p : IsPGroup 2 (N.subgroupOf (U ⊔ (S : Subgroup G))) := IsPGroup.of_card hsub_card
    have hle_p := Work.A7REC.Basic.le_pCore_of_normal (p := 2) hsub_p
    have hmap : (N.subgroupOf (U ⊔ (S : Subgroup G))).map (U ⊔ (S : Subgroup G)).subtype = N := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hN_le_K]
    have hVdef' : V = (Work.A7REC.pCore 2 ↥(U ⊔ (S : Subgroup G))).map
        (U ⊔ (S : Subgroup G)).subtype := by
      rw [hVdef'', Work.A7REC.pCoreIn]
    have hN_le_V : N ≤ V := by
      have hle' : N ≤ (Work.A7REC.pCore 2 ↥(U ⊔ (S : Subgroup G))).map
          (U ⊔ (S : Subgroup G)).subtype := by
        rw [← hmap]
        exact Subgroup.map_mono hle_p
      rwa [← hVdef'] at hle'
    calc Nat.card N ≤ Nat.card V := Subgroup.card_le_of_le hN_le_V
      _ = 4 := hVcard
  have hmaxτ : ∀ N : Subgroup G, N ≤ Cτ → (N.subgroupOf Cτ).Normal → IsPGroup 2 N →
      Nat.card N ≤ 4 := by
    intro N hN hNnorm hNp
    set M : Subgroup G := N.map ψ with hMdef
    have hMcard : Nat.card ↥M = Nat.card ↥N := by
      rw [hMdef, Subgroup.card_map_of_injective hψinj]
    have hM_le : M ≤ Subgroup.centralizer ({z} : Set G) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hn_comm : n * τ = τ * n :=
        (Subgroup.mem_centralizer_iff.mp (hN hn) τ (Set.mem_singleton τ)).symm
      have key : φ (ψ n * z) = φ (z * ψ n) := by
        rw [map_mul, map_mul, hconj_apply, hconj_z, hn_comm]
      exact (hφinj key).symm
    have hM_norm : (M.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hM_le).mpr ?_
      rw [Subgroup.le_normalizer_iff]
      intro c hc m hm
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hm
      have hcτ : φ c ∈ Cτ := by
        rw [hCτdef, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hcz : c * z = z * c :=
          (Subgroup.mem_centralizer_iff.mp hc z (Set.mem_singleton z)).symm
        have hkey : φ (c * z) = φ (z * c) := by rw [hcz]
        rw [map_mul, map_mul, hconj_z] at hkey
        exact hkey.symm
      have hmem : φ c * n * (φ c)⁻¹ ∈ N :=
        Work.A7REC.Basic.conj_mem_of_subgroupOf_normal hN hNnorm hcτ hn
      have key : c * ψ n * c⁻¹ = ψ (φ c * n * (φ c)⁻¹) := by
        rw [map_mul, map_mul, map_inv, hconj_apply']
      rw [key]
      exact Subgroup.mem_map_of_mem ψ hmem
    have hMp : IsPGroup 2 M := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
      refine IsPGroup.of_card (n := k) ?_
      rw [hMcard, hk]
    have hres := hmaxz M hM_le hM_norm hMp
    rwa [hMcard] at hres

  -- ### Step 8: a Sylow `2`-subgroup of `C_G(τ)` missing `z`
  have hCτ_sub_card : Nat.card ↥(V'.subgroupOf Cτ) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'_le_Cτ).toEquiv).trans hV'card
  have hz0sq : (⟨z, hz_in_Cτ⟩ : ↥Cτ) * ⟨z, hz_in_Cτ⟩ = 1 :=
    Subtype.ext (by simpa using hzsq)
  have hz0_notin : (⟨z, hz_in_Cτ⟩ : ↥Cτ) ∉ V'.subgroupOf Cτ :=
    fun h => hz_notin_V' (Subgroup.mem_subgroupOf.mp h)
  have hmaxτ' : ∀ M : Subgroup ↥Cτ, M.Normal → IsPGroup 2 M → Nat.card ↥M ≤ 4 := by
    intro M hMn hMp
    have hle : M.map Cτ.subtype ≤ Cτ := Subgroup.map_subtype_le M
    have hcard : Nat.card ↥(M.map Cτ.subtype) = Nat.card ↥M :=
      Subgroup.card_map_of_injective Cτ.subtype_injective
    have hp : IsPGroup 2 (M.map Cτ.subtype) := hMp.map Cτ.subtype
    have hnorm : ((M.map Cτ.subtype).subgroupOf Cτ).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, Subgroup.le_normalizer_iff]
      intro c hc mv hmv
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hmv
      refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * m * ⟨c, hc⟩⁻¹, hMn.conj_mem m hm ⟨c, hc⟩, ?_⟩
      simp
    have hres := hmaxτ _ hle hnorm hp
    rwa [hcard] at hres
  obtain ⟨P, hPz⟩ := sylowNotMemOfCard24 (V'.subgroupOf Cτ) ⟨z, hz_in_Cτ⟩ hCτ24 hCτ_sub_card
    hV'_norm hz0sq hz0_notin hmaxτ'
  have hPcard : Nat.card ↥((P : Subgroup ↥Cτ).map Cτ.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective Cτ.subtype_injective]
    have h := Sylow.card_eq_multiplicity P
    rw [hCτ24] at h
    exact h.trans two_pow_factorization_24
  have hS'card : Nat.card ↥((P : Subgroup ↥Cτ).map Cτ.subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [hPcard, hGcard]
    exact two_pow_factorization_2520.symm
  set S' : Sylow 2 G := Sylow.ofCard ((P : Subgroup ↥Cτ).map Cτ.subtype) hS'card with hS'def
  have hS'coe : (S' : Subgroup G) = (P : Subgroup ↥Cτ).map Cτ.subtype := Sylow.coe_ofCard _ _
  have hS'_p : IsPGroup 2 (S' : Subgroup G) := S'.isPGroup'
  have hS'_le_Cτ : (S' : Subgroup G) ≤ Cτ := by
    rw [hS'coe]
    exact Subgroup.map_subtype_le (P : Subgroup ↥Cτ)

  -- ### Step 9: assemble
  have hτ0_mem : (⟨τ, hτ_in_Cτ⟩ : ↥Cτ) ∈ P := by
    have hpow_normal : (Subgroup.zpowers (⟨τ, hτ_in_Cτ⟩ : ↥Cτ)).Normal :=
      ⟨fun n hn c => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        refine ⟨k, ?_⟩
        have hccomm : (MulAut.conj c) (⟨τ, hτ_in_Cτ⟩ : ↥Cτ) = ⟨τ, hτ_in_Cτ⟩ := by
          refine Subtype.ext ?_
          show (c : G) * ((⟨τ, hτ_in_Cτ⟩ : ↥Cτ) : G) * (c : G)⁻¹ = ((⟨τ, hτ_in_Cτ⟩ : ↥Cτ) : G)
          have hcg : (c : G) * τ * (c : G)⁻¹ = τ := by
            have h1 : τ * (c : G) = (c : G) * τ :=
              Subgroup.mem_centralizer_iff.mp c.2 τ (Set.mem_singleton τ)
            rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
          simpa using hcg
        calc (⟨τ, hτ_in_Cτ⟩ : ↥Cτ) ^ k
            = ((MulAut.conj c) (⟨τ, hτ_in_Cτ⟩ : ↥Cτ)) ^ k := by rw [hccomm]
          _ = (MulAut.conj c) ((⟨τ, hτ_in_Cτ⟩ : ↥Cτ) ^ k) := (map_zpow _ _ _).symm
          _ = c * (⟨τ, hτ_in_Cτ⟩ : ↥Cτ) ^ k * c⁻¹ := by rw [MulAut.conj_apply]⟩
    have hpow_p : IsPGroup 2 (Subgroup.zpowers (⟨τ, hτ_in_Cτ⟩ : ↥Cτ)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers]
      have hord : orderOf (⟨τ, hτ_in_Cτ⟩ : ↥Cτ) = 2 :=
        orderOf_eq_prime (p := 2)
          (Subtype.ext (by simpa [pow_two] using hτsq)) (fun h => hτ_ne (by
            have h' : ((⟨τ, hτ_in_Cτ⟩ : ↥Cτ) : G) = (1 : G) := congrArg Subtype.val h
            simpa using h'))
      rw [hord]
      norm_num
    exact IsPGroup.le_sylow_of_normal hpow_p P (Subgroup.mem_zpowers _)
  have hτ_mem_S' : τ ∈ (S' : Subgroup G) := by
    rw [hS'coe]
    exact Subgroup.mem_map_of_mem Cτ.subtype hτ0_mem
  have hz_notin_S' : z ∉ (S' : Subgroup G) := by
    intro hz
    rw [hS'coe] at hz
    obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hz
    have hmz : m = ⟨z, hz_in_Cτ⟩ := Subtype.ext hme
    exact hPz (hmz ▸ hm)
  have hzpow_bot : (S' : Subgroup G) ⊓ Subgroup.zpowers z = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have hdvd : Nat.card ↥((S' : Subgroup G) ⊓ Subgroup.zpowers z) ∣ 2 := by
      have h := Subgroup.card_dvd_of_le (α := G)
        (inf_le_right : (S' : Subgroup G) ⊓ Subgroup.zpowers z ≤ Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hz2'] at h
    have hne : Nat.card ↥((S' : Subgroup G) ⊓ Subgroup.zpowers z) ≠ 2 := by
      intro h2
      have heq : (S' : Subgroup G) ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, Nat.card_zpowers, hz2'])
      exact hz_notin_S' ((le_of_eq heq.symm).trans inf_le_left (Subgroup.mem_zpowers z))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd h hne
  have h2sub_le_V : ∀ A : Subgroup G, A ≤ Subgroup.centralizer (U : Set G) → IsPGroup 2 A →
      A ≤ V := by
    intro A hA hAp
    have hVn : (V.subgroupOf (Subgroup.centralizer (U : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV_le_CU).mpr (by
        calc Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (U : Set G) :=
              Subgroup.centralizer_le_normalizer _
          _ = Subgroup.normalizer (V : Set G) := hNUV')
    haveI := hVn
    have hVp : IsPGroup 2 (V.subgroupOf (Subgroup.centralizer (U : Set G))) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [(Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_CU).toEquiv), hVcard]
      norm_num
    have hVsub_card : Nat.card ↥(V.subgroupOf (Subgroup.centralizer (U : Set G))) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_CU).toEquiv).trans hVcard
    have hPcard' : ∀ Q : Sylow 2 ↥(Subgroup.centralizer (U : Set G)), Nat.card ↥Q = 4 := by
      intro Q
      have h := Sylow.card_eq_multiplicity Q
      rw [hCU36] at h
      exact h.trans two_pow_factorization_36
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
    have hAsub_p : IsPGroup 2 (A.subgroupOf (Subgroup.centralizer (U : Set G))) := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hk]
    obtain ⟨P₂, hP₂⟩ := IsPGroup.exists_le_sylow hAsub_p
    have hVle_P₂ : V.subgroupOf (Subgroup.centralizer (U : Set G)) ≤ P₂ :=
      IsPGroup.le_sylow_of_normal hVp P₂
    have hP₂eq : P₂ = V.subgroupOf (Subgroup.centralizer (U : Set G)) :=
      (Subgroup.eq_of_le_of_card_ge hVle_P₂ (by
        rw [hVsub_card]
        exact le_of_eq (hPcard' P₂))).symm
    have hA_le : A.subgroupOf (Subgroup.centralizer (U : Set G)) ≤
        V.subgroupOf (Subgroup.centralizer (U : Set G)) := by
      rw [← hP₂eq]
      exact hP₂
    intro a ha
    have hmem : (⟨a, hA ha⟩ : ↥(Subgroup.centralizer (U : Set G))) ∈
        V.subgroupOf (Subgroup.centralizer (U : Set G)) :=
      hA_le (Subgroup.mem_subgroupOf.mpr ha)
    simpa only [Subgroup.mem_subgroupOf, Subtype.coe_mk] using hmem
  have hS'infCU : (S' : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
    refine le_bot_iff.mp ?_
    have hle_V : (S' : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ V :=
      h2sub_le_V _ inf_le_right (hS'_p.to_le inf_le_left)
    have hle_z : (S' : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.zpowers z := by
      intro x hx
      have hxV : x ∈ V := hle_V hx
      have hxCτ : x ∈ Cτ := hS'_le_Cτ hx.1
      have hmem : x ∈ V ⊓ Cτ := ⟨hxV, hxCτ⟩
      rwa [hVinfCτ] at hmem
    have hle : (S' : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) ≤
        (S' : Subgroup G) ⊓ Subgroup.zpowers z := le_inf inf_le_left hle_z
    rw [hzpow_bot] at hle
    exact hle
  exact ⟨S', τ, hUcard', by rw [hS'coe]; exact hPcard, hτ_mem_S', hτ2ord,
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (hS'_le_Cτ hx) τ (Set.mem_singleton τ)).symm),
    hU_conj, hS'infCU⟩

end Work.A7REC.Char
