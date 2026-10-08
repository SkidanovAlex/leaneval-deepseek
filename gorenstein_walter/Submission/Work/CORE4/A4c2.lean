
import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Defs17
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.A4i
import Submission.Work.CORE4.A4a
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

/-!
# `A4c2` (design pass 17)

Area CORE4, the `A₇` sub-case of Bender 1981, §4: from the data of `A4b` (`e ∈ E(M)` with
`K^e ≤ Ĥ`, `K^e ≠ K`, `s` inverting `K^e`), together with the export `U = F · I_U(s)` and
`K = Z(U)`, we derive a contradiction.

The argument (see the docstring of `Work.CORE4.C15.A4c2Prop`):

* `K' := K^e = Z(U^e)` centralizes `I_U(s)` (by `A4i`, since `K' ≤ Ĥ` normalises `I_U(s) ⊴ Ĥ`,
  and `s` inverts both) and `F` (since `K' ≤ E(M)` and `F ≤ C(E(M))`); as `U = F · I_U(s)` as
  sets, `K' ≤ C_G(U)`;
* hence `U ≤ C(K') ≤ N(K') = Ĥ^e` (the last equality by maximality of the coatom `Ĥ^e`), and
  `K' ∩ U = ⊥` (as `K' ≤ C(U)` and `K ∩ K' = ⊥`);
* from `U ≤ N(U^e)` and `|Ĥ^e : U^e| = |Ĥ : U| = 24` one gets `|U : U ∩ U^e| = 3`;
* finally `U^e = K' · (U ∩ U^e)` is a direct product (the two factors commute and meet trivially),
  so `Z(U ∩ U^e)` would be trivial — impossible, since `U ∩ U^e` is a nontrivial subgroup of the
  `3`-group `U`, and a nontrivial `p`-group has nontrivial centre.

Note: the "design pass 15" route through the normality of `U ∩ U^e` is *not* used here; the
contradiction above is shorter and avoids the (delicate) claim that `U ∩ U^e ⊴ Ĥ`.
-/

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-! ## Conjugation helpers -/

/-- Membership in a conjugate: `x ∈ K^g ↔ g⁻¹ * x * g ∈ K`. -/
theorem mem_conjSub_iff_A4c2 {g : G} {K : Subgroup G} {x : G} :
    x ∈ Work.GW2.conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rwa [show g⁻¹ * ((MulAut.conj g).toMonoidHom h) * g = h from by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group]
  · intro h
    exact ⟨g⁻¹ * x * g, h, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- Membership in the image of the centre: `x ∈ Z(K)` (as a subgroup of `G`) if and only if
`x ∈ K` and `x` commutes with every element of `K`. -/
theorem mem_center_map_iff_A4c2 {K : Subgroup G} {x : G} :
    x ∈ (Subgroup.center ↥K).map K.subtype ↔ x ∈ K ∧ ∀ y ∈ K, y * x = x * y := by
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    refine ⟨hzx ▸ z.2, fun y hy => ?_⟩
    have h := Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : ↥K)
    rw [← hzx]
    simpa using congrArg Subtype.val h
  · rintro ⟨hxK, hxc⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g.1 g.2)

/-- Conjugation commutes with the centre: `Z(K)^g = Z(K^g)`. -/
theorem conjSub_center_A4c2 (g : G) (K : Subgroup G) :
    Work.GW2.conjSub g ((Subgroup.center ↥K).map K.subtype) =
      (Subgroup.center ↥(Work.GW2.conjSub g K)).map (Work.GW2.conjSub g K).subtype := by
  ext x
  rw [mem_conjSub_iff_A4c2, mem_center_map_iff_A4c2, mem_center_map_iff_A4c2]
  constructor
  · rintro ⟨hxK, hxc⟩
    refine ⟨by rw [mem_conjSub_iff_A4c2]; exact hxK, fun z hz => ?_⟩
    have hy : g⁻¹ * z * g ∈ K := mem_conjSub_iff_A4c2.mp hz
    have hcomm : (g⁻¹ * z * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * z * g) := hxc _ hy
    calc z * x = g * (g⁻¹ * (z * x) * g) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
      _ = g * (g⁻¹ * (x * z) * g) * g⁻¹ := by group
      _ = x * z := by group
  · rintro ⟨hxc, hcx⟩
    refine ⟨mem_conjSub_iff_A4c2.mp hxc, fun y hy => ?_⟩
    have h1 : g * y * g⁻¹ ∈ Work.GW2.conjSub g K := by
      rw [mem_conjSub_iff_A4c2]; convert hy using 1; group
    have hcomm : (g * y * g⁻¹) * x = x * (g * y * g⁻¹) := hcx _ h1
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * y := by group

/-- Conjugation preserves coatoms. -/
theorem isCoatom_conjSub_A4c2 {H : Subgroup G} (h : IsCoatom H) (g : G) :
    IsCoatom (Work.GW2.conjSub g H) := by
  have hiff := (MulEquiv.mapSubgroup (MulAut.conj g)).isCoatom_iff H
  rw [Work.GW2.conjSub]
  exact hiff.mpr h

/-- A nontrivial subgroup `H` normal in a coatom `M`, with `G` simple, has normalizer `M`.
(Used for `N_G(K^e) = Ĥ^e` and `N_G(U^e) = Ĥ^e`.) -/
theorem normalizer_eq_of_isCoatom_A4c2 [IsSimpleGroup G] {M H : Subgroup G} (hM : IsCoatom M)
    (hHM : (H.subgroupOf M).Normal) (hHne : H ≠ ⊥) (hHle : H ≤ M) :
    Subgroup.normalizer (H : Set G) = M := by
  have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.le_normalizer_iff).mpr
      (fun m hm k hk => (Subgroup.normal_subgroupOf_iff hHle).mp hHM k m hk hm)
  refine le_antisymm ?_ hMH
  by_contra hcon
  have hlt : M < Subgroup.normalizer (H : Set G) :=
    lt_of_le_of_ne hMH (fun heq => hcon (le_of_eq heq.symm))
  have htop : Subgroup.normalizer (H : Set G) = ⊤ := hM.lt_iff.mp hlt
  have hHnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact hHne h
  · exact hM.1 (top_le_iff.mp (h ▸ hHle))

/-- A nontrivial subgroup of a `p`-group (with `p` prime) has nontrivial centre. -/
theorem center_ne_bot_of_isPGroup_A4c2 {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hp : IsPGroup p ↥H) (hne : H ≠ ⊥) : Subgroup.center ↥H ≠ ⊥ := by
  have hnt : Nontrivial ↥H := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨a, 1, ha⟩
  have hc : Nontrivial ↥(Subgroup.center ↥H) := IsPGroup.center_nontrivial hp
  intro hbot
  haveI : Subsingleton ↥(Subgroup.center ↥H) := by rw [hbot]; infer_instance
  haveI := hc
  exact not_subsingleton ↥(Subgroup.center ↥H) inferInstance

/-! ## `A4c2` -/

/-- **A4c2 (design pass 17 ruling on `NOTES_TO_LEAD.md` §14).**  The design-15 `A4c` with the
`U = F · I_U(s)` export added as a hypothesis; the earlier refutation of the design-15 finish was
withdrawn by the lead (`e ∈ Ĥ^e` holds iff `e ∈ Ĥ`, and `Ĥ^e ≠ Ĥ` forces `e ∉ Ĥ`, so `X^e = U^e`
does **not** follow).

`A4c2Prop I`: from `Hyp9 G B C`, `IsA7Case C.D`, `A7Facts1`, `A7Facts2`, `A7UData`,
`Case2InvNormal B C.D`, `C.D.K = Z(U)`, `(B.U : Set G) = (C.D.F : Set G) * invSet B.U C.D.s`, and
the five data of `A4b` (`e ∈ E`, `e s = s e`, `K^e ≤ Ĥ`, `K^e ≠ K`, `s` inverts `K^e`): `False`.

Route (design pass 15 §1.3, A4c, with the export available), `K' := K^e`, `X := U ⊓ U^e`,
`V := O₂(Ĥ)`:

1. `K'` centralizes `I := I_U(s)` (A4i: `K' ≤ Ĥ` normalizes `I ⊴ Ĥ`) and `F` (`F ≤ C(E)`), hence
   `K' ≤ C_G(U)` using `U = F · I` (the new hypothesis);
2. `N_G(K) = Ĥ` (`K = Z(U)` characteristic in `U = O(Ĥ) ⊴ Ĥ`, `Ĥ` a coatom, `G` simple), so
   `U ≤ C(K') ≤ N(K') = Ĥ^e`; and `Ĥ^e ≠ Ĥ` (else `U^e = U` and `K' = Z(U^e) = K`);
3. `K' ⊄ U` (else `K' ⊆ invSet (U ⊓ M) s = K`); `s ∉ V U` and `s ∉ V^e U^e` (an involution of
   `V × U` lies in `V`, hence centralizes `U ⊇ K ≠ 1`, but `s` inverts `K`; likewise for `K'`);
   `|Ĥ : V U| = 6` (`I.thm26`, second case, as `V = O₂(Ĥ)` is a four-group);
4. `T := U U^e` is a 3-subgroup of `Ĥ^e`, so `|T| ≤ 3|U|`; hence `|U : X| ≤ 3`, `U ⊴ T`,
   `U^e ≤ N(U) = Ĥ`, and `|X| ≥ |U|/3 ≥ 3` (as `|U| ≥ |K F| = 9`);
5. `N_Ĥ(X) ⊇ V U, K', s` and `N_{Ĥ^e}(X) ⊇ V^e U^e, U, s`, whence `X ⊴ Ĥ` and `X ⊴ Ĥ^e` (both
   indices divide `|Ĥ : V U| = 6` and are divisible by `2` and `3`);
6. `X ⊴ ⟨Ĥ, Ĥ^e⟩ = G` with `1 ≠ X ≤ U < G`, contradicting `BenderCtx.simple`.

**As formalised here** steps 3–6 of the above route are replaced by a shorter argument which avoids
the (delicate) normality of `U ∩ U^e`: after step 2 one has

* `K' = Z(U^e)` (conjugation commutes with centres) and `K' ∩ U = ⊥`, so `K' · X` is a direct
  product of the two subgroups `K' ≅ C₃` and `X := U ∩ U^e`;
* `N(U^e) = Ĥ^e` by maximality of the coatom `Ĥ^e`, so `U ≤ N(U^e)` and — using
  `|Ĥ : U| = 24` from `I.thm26` — the index `|U : X|` is `3`;
* hence `U^e = K' · X ≅ C₃ × X`, which forces `Z(X) = ⊥`; but `X ≤ U` is a nontrivial `3`-group,
  and a nontrivial `p`-group has nontrivial centre — the contradiction.

`invNormalFrom_of_parts2` (`Defs17.lean`, PROVED) assembles this leaf with `A4a2`, `A4s` and `A4b`
into `A7InvNormalFromProp`, i.e. `¬ Case2InvNormal`. -/
theorem A4c2 (I : Work.GW2.C4Inputs) : Work.CORE4.C15.A4c2Prop I := by
  intro G _ _ B C hHyp hA7 h1F h2F hUData hInv hKZ hUFI e he hes heH hne hinv
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  obtain ⟨hKcard, hFcard, hK0eq, hpiFU⟩ := h1F
  obtain ⟨hVfourD, hVeq, hSE, hScard, hENV⟩ := h2F
  obtain ⟨hU3, hB0F, hOMF, hbound⟩ := hUData
  obtain ⟨Isub, hIsubset, hIsubHhat, hIsubNorm⟩ := hInv
  haveI : IsSimpleGroup G := hbc.simple
  have hKleU : C.D.K ≤ B.U := Work.GW2.Case2Data.K_le_U B C.D
  have hKleE : C.D.K ≤ layerIn C.D.M :=
    (A7KBound.K_le_layerIn_and_inf_center (B := B) (D := C.D) hplus B.U_odd).1
  have hFleU : C.D.F ≤ B.U := Work.GW2.Case2Data.F_le_U B C.D
  have hKne : C.D.K ≠ ⊥ := by
    intro hbot; rw [hbot] at hKcard; simp at hKcard
  have hFinfK : C.D.F ⊓ C.D.K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxF, hxK⟩ := Subgroup.mem_inf.mp hx
    have hxfix : C.D.s * x * C.D.s⁻¹ = x := by
      have h1 : x ∈ C.D.B0 := Work.GW2.Case2Data.F_le_B0 B C.D hxF
      rw [Work.GW2.Case2Pre.B0_eq B C.D C.pre] at h1
      have h2 : x * C.D.s = C.D.s * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h1).2
      rw [← h2]
      group
    have hxinv : C.D.s * x * C.D.s⁻¹ = x⁻¹ := Work.GW2.Case2Data.K_inv B C.D x hxK
    have hx2 : x ^ 2 = 1 := by
      rw [hxfix] at hxinv
      rw [pow_two]
      nth_rewrite 2 [hxinv]
      exact mul_inv_cancel x
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U (hKleU hxK))
    have hdvd : orderOf x ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact hx2
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have h26 := I.thm26 G I.toolkit.ft hbc B
  obtain ⟨hUoddCore, hSinterV, hTrich⟩ := h26
  have hUleHhat : B.U ≤ B.Hhat := by
    rw [← hUoddCore]; exact Subgroup.map_subtype_le _
  have hUnormHat : ∀ h ∈ B.Hhat, ∀ u ∈ B.U, h * u * h⁻¹ ∈ B.U := by
    intro h hh u hu
    rw [← hUoddCore, Work.GW2.oddCoreIn] at hu ⊢
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
      (Work.GW2.oddCore_normal ↥B.Hhat).conj_mem y hy ⟨h, hh⟩, ?_⟩
    simp only [map_mul, map_inv]
    rw [← hyu]
    rfl
  have hIsubinv : Inverts C.D.s Isub := by
    intro x hx
    exact ((Set.ext_iff.mp hIsubset x).mp hx).2
  have hK'leNIsub : Work.GW2.conjSub e C.D.K ≤ Subgroup.normalizer (Isub : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    exact (Subgroup.normal_subgroupOf_iff hIsubHhat).mp hIsubNorm x k hx (heH hk)
  have hK'card : Nat.card ↥(Work.GW2.conjSub e C.D.K) = 3 := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj e).injective, hKcard]
  have hK'odd : Odd (Nat.card ↥(Work.GW2.conjSub e C.D.K)) := by
    rw [hK'card]; norm_num
  have hK'leCI : Work.GW2.conjSub e C.D.K ≤ Subgroup.centralizer (Isub : Set G) :=
    A4i G C.D.s Isub (Work.GW2.conjSub e C.D.K) hIsubinv hinv hK'leNIsub hK'odd
  have hlay : (layerIn C.D.M).subgroupOf C.D.M = layer ↥C.D.M := by
    rw [layerIn]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
  have hEnormSub : ((layerIn C.D.M).subgroupOf C.D.M).Normal := by
    rw [hlay]; exact layer_normal C.D.M
  have hK'leE : Work.GW2.conjSub e C.D.K ≤ layerIn C.D.M := by
    refine le_trans (Subgroup.map_mono hKleE) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Subgroup.normal_subgroupOf_iff (layerIn_le C.D.M)).mp hEnormSub x e hx
      (layerIn_le C.D.M he)
  have hK'leCF : Work.GW2.conjSub e C.D.K ≤ Subgroup.centralizer (C.D.F : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (Case2Pre.F_cent B C.D C.pre hy)) x (hK'leE hx)).symm
  have hK'leCU : Work.GW2.conjSub e C.D.K ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ (C.D.F : Set G) * (Work.GW2.invSet B.U C.D.s) := by
      rw [← hUFI]; exact hu
    obtain ⟨f, hf, i, hi, hfi⟩ := Set.mem_mul.mp hu'
    have hkf : f * k = k * f := (Subgroup.mem_centralizer_iff.mp (hK'leCF hk)) f hf
    have hki : i * k = k * i :=
      (Subgroup.mem_centralizer_iff.mp (hK'leCI hk)) i (hIsubset.symm ▸ hi)
    rw [← hfi]
    calc f * i * k = f * (i * k) := by group
      _ = f * (k * i) := by rw [hki]
      _ = f * k * i := by group
      _ = k * f * i := by rw [hkf]
      _ = k * (f * i) := by group
  have hKK' : C.D.K ⊓ Work.GW2.conjSub e C.D.K = ⊥ := by
    have hdvd : Nat.card ↥(C.D.K ⊓ Work.GW2.conjSub e C.D.K) ∣ 3 := by
      rw [← hKcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hcard : Nat.card ↥C.D.K ≤ Nat.card ↥(C.D.K ⊓ Work.GW2.conjSub e C.D.K) := by
        rw [h3, hKcard]
      have hEq : C.D.K ⊓ Work.GW2.conjSub e C.D.K = C.D.K :=
        Subgroup.eq_of_le_of_card_ge inf_le_left hcard
      have hle : C.D.K ≤ Work.GW2.conjSub e C.D.K := by
        have h := inf_le_right (a := C.D.K) (b := Work.GW2.conjSub e C.D.K)
        rw [hEq] at h
        exact h
      have heq : C.D.K = Work.GW2.conjSub e C.D.K :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hK'card, hKcard])
      exact hne heq.symm
  have hK'infU : Work.GW2.conjSub e C.D.K ⊓ B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxK', hxU⟩ := Subgroup.mem_inf.mp hx
    have hxZ : x ∈ (Subgroup.center ↥B.U).map B.U.subtype := by
      rw [mem_center_map_iff_A4c2]
      exact ⟨hxU, fun y hy => (Subgroup.mem_centralizer_iff.mp (hK'leCU hxK')) y hy⟩
    rw [← hKZ] at hxZ
    have hmem : x ∈ C.D.K ⊓ Work.GW2.conjSub e C.D.K := Subgroup.mem_inf.mpr ⟨hxZ, hxK'⟩
    rw [hKK'] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hK'Z : Work.GW2.conjSub e C.D.K =
      (Subgroup.center ↥(Work.GW2.conjSub e B.U)).map (Work.GW2.conjSub e B.U).subtype := by
    rw [hKZ, conjSub_center_A4c2]
  have hHhatE_coatom : IsCoatom (Work.GW2.conjSub e B.Hhat) := isCoatom_conjSub_A4c2 B.Hhat_coatom e
  have hUeNormHat : ∀ k ∈ Work.GW2.conjSub e B.Hhat, ∀ u ∈ Work.GW2.conjSub e B.U,
      k * u * k⁻¹ ∈ Work.GW2.conjSub e B.U := by
    intro k hk u hu
    rw [Work.GW2.conjSub] at hk hu ⊢
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr ⟨h * v * h⁻¹, hUnormHat h hh v hv, by
      simp only [map_mul, map_inv]⟩
  have hUe_le : Work.GW2.conjSub e B.U ≤ Work.GW2.conjSub e B.Hhat := Subgroup.map_mono hUleHhat
  have hUeNormSub : ((Work.GW2.conjSub e B.U).subgroupOf (Work.GW2.conjSub e B.Hhat)).Normal :=
    (Subgroup.normal_subgroupOf_iff hUe_le).mpr (fun h k hh hk => hUeNormHat k hk h hh)
  have hUe_ne_bot : Work.GW2.conjSub e B.U ≠ ⊥ := by
    intro hbot
    have hle : Work.GW2.conjSub e C.D.K ≤ ⊥ := by
      rw [← hbot]; exact Subgroup.map_mono hKleU
    have hK'bot : Work.GW2.conjSub e C.D.K = ⊥ := le_bot_iff.mp hle
    rw [hK'bot] at hK'card
    simp at hK'card
  have hK'ne_bot : Work.GW2.conjSub e C.D.K ≠ ⊥ := by
    intro hbot; rw [hbot] at hK'card; simp at hK'card
  have hK'leHhatE : Work.GW2.conjSub e C.D.K ≤ Work.GW2.conjSub e B.Hhat :=
    le_trans (Subgroup.map_mono hKleU) hUe_le
  have hK'normSub : ((Work.GW2.conjSub e C.D.K).subgroupOf
      (Work.GW2.conjSub e B.Hhat)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hK'leHhatE]
    intro h k hh hk
    rw [hK'Z] at hh ⊢
    rw [mem_center_map_iff_A4c2] at hh ⊢
    obtain ⟨hhUe, hhc⟩ := hh
    have hkUe : k * h * k⁻¹ ∈ Work.GW2.conjSub e B.U :=
      (Subgroup.normal_subgroupOf_iff hUe_le).mp hUeNormSub h k hhUe hk
    refine ⟨hkUe, fun y hy => ?_⟩
    have h1 : k⁻¹ * y * k ∈ Work.GW2.conjSub e B.U := by
      simpa using (Subgroup.normal_subgroupOf_iff hUe_le).mp hUeNormSub y k⁻¹ hy
        (Subgroup.inv_mem _ hk)
    calc y * (k * h * k⁻¹) = k * ((k⁻¹ * y * k) * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * y * k)) * k⁻¹ := by rw [hhc _ h1]
      _ = (k * h * k⁻¹) * y := by group
  have hNK' : Subgroup.normalizer ((Work.GW2.conjSub e C.D.K : Subgroup G) : Set G) =
      Work.GW2.conjSub e B.Hhat :=
    normalizer_eq_of_isCoatom_A4c2 hHhatE_coatom hK'normSub hK'ne_bot hK'leHhatE
  have hNUe : Subgroup.normalizer ((Work.GW2.conjSub e B.U : Subgroup G) : Set G) =
      Work.GW2.conjSub e B.Hhat :=
    normalizer_eq_of_isCoatom_A4c2 hHhatE_coatom hUeNormSub hUe_ne_bot hUe_le
  have hUleHhatE : B.U ≤ Work.GW2.conjSub e B.Hhat := by
    have h1 : B.U ≤ Subgroup.centralizer ((Work.GW2.conjSub e C.D.K : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff).mpr hK'leCU
    rw [← hNK']
    exact le_trans h1 (Subgroup.centralizer_le_normalizer _)
  have hVfour : IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := by
    rw [hVeq]; exact hVfourD
  have hVleCU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    rw [← hSinterV]; exact inf_le_right
  have hVinfU : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxV, hxU⟩ := Subgroup.mem_inf.mp hx
    have hx2 : x ^ 2 = 1 := hVfour.2 x hxV
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hxU)
    have hdvd : orderOf x ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact hx2
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hUleNV : B.U ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    le_trans ((Subgroup.le_centralizer_iff).mpr hVleCU) (Subgroup.centralizer_le_normalizer _)
  have hVUcard : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) =
      Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) * Nat.card ↥B.U :=
    Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hUleNV hVinfU
  have hHhatCard : Nat.card ↥B.Hhat = 24 * Nat.card ↥B.U := by
    have hrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
      rcases hTrich with h1 | h2
      · exact absurd hVfour (not_isFourGroup_of_le_cyclic B.S0_cyclic h1.1)
      · exact h2.2.1
    have h1 := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) B.Hhat
    have h2 : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) ⊓ B.Hhat =
        Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U :=
      inf_eq_left.mpr (sup_le (Subgroup.map_subtype_le _) hUleHhat)
    rw [h2, hrel, hVUcard, hVfour.1] at h1
    rw [← h1]; ring
  have hHatEcard : Nat.card ↥(Work.GW2.conjSub e B.Hhat) = 24 * Nat.card ↥B.U := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj e).injective, hHhatCard]
  have hUecard : Nat.card ↥(Work.GW2.conjSub e B.U) = Nat.card ↥B.U := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj e).injective]
  have hrelU : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) =
      (Work.GW2.conjSub e B.U ⊓ B.U).relIndex (Work.GW2.conjSub e B.U) := by
    refine relIndex_eq_relIndex_inf_of_normal_sup_eq (Work.GW2.conjSub e B.U) B.U
      (B.U ⊔ Work.GW2.conjSub e B.U) le_sup_right le_sup_left ?_ ?_
    · rw [sup_comm]
    · rw [Subgroup.normal_subgroupOf_iff le_sup_right]
      intro h k hh hk
      exact hUeNormHat k ((sup_le hUleHhatE hUe_le) hk) h hh
  have hNmul : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) *
      Nat.card ↥(Work.GW2.conjSub e B.U ⊓ B.U) = Nat.card ↥B.U := by
    have h1 := Subgroup.relIndex_mul_card (Work.GW2.conjSub e B.U ⊓ B.U)
      (Work.GW2.conjSub e B.U)
    rw [inf_eq_left.mpr inf_le_left, hUecard] at h1
    rw [← hrelU] at h1
    exact h1
  have hN24 : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) ∣ 24 := by
    have h1 : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) *
        (B.U ⊔ Work.GW2.conjSub e B.U).relIndex (Work.GW2.conjSub e B.Hhat) =
        B.U.relIndex (Work.GW2.conjSub e B.Hhat) :=
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hUleHhatE hUe_le)
    have h2 : B.U.relIndex (Work.GW2.conjSub e B.Hhat) = 24 := by
      have h3 := Subgroup.relIndex_mul_card B.U (Work.GW2.conjSub e B.Hhat)
      rw [inf_eq_left.mpr hUleHhatE, hHatEcard] at h3
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
    refine ⟨(B.U ⊔ Work.GW2.conjSub e B.U).relIndex (Work.GW2.conjSub e B.Hhat), ?_⟩
    rw [h1, h2]
  obtain ⟨a, ha⟩ : ∃ a, Nat.card ↥B.U = 3 ^ a := IsPGroup.exists_card_eq hU3
  have hNdvd : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) ∣ 3 ^ a := by
    rw [← ha]; exact ⟨_, hNmul.symm⟩
  have hN3 : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) = 3 := by
    have hNne1 : B.U.relIndex (B.U ⊔ Work.GW2.conjSub e B.U) ≠ 1 := by
      intro h1
      have hle : Work.GW2.conjSub e B.U ≤ B.U :=
        le_trans le_sup_right (Subgroup.relIndex_eq_one.mp h1)
      have heq : Work.GW2.conjSub e B.U = B.U :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hUecard])
      have hK'eq : Work.GW2.conjSub e C.D.K = C.D.K := by
        rw [hK'Z, heq, ← hKZ]
      exact hne hK'eq
    obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hNdvd
    have hk24 : 3 ^ k ∣ 24 := hk ▸ hN24
    have hk1 : k ≤ 1 := by
      by_contra hkk
      have h2 : 2 ≤ k := by omega
      have h9 : 9 ∣ 24 := dvd_trans (pow_dvd_pow 3 h2) hk24
      norm_num at h9
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [hk, h0] at hNne1; norm_num at hNne1
    · have hk1' : k = 1 := by omega
      rw [hk, hk1']; norm_num
  have hXmul : 3 * Nat.card ↥(B.U ⊓ Work.GW2.conjSub e B.U) = Nat.card ↥B.U := by
    rw [inf_comm, ← hN3]
    exact hNmul
  have hK'X : Work.GW2.conjSub e C.D.K ⊔ (B.U ⊓ Work.GW2.conjSub e B.U) =
      Work.GW2.conjSub e B.U := by
    have hle : Work.GW2.conjSub e C.D.K ⊔ (B.U ⊓ Work.GW2.conjSub e B.U) ≤
        Work.GW2.conjSub e B.U :=
      sup_le (Subgroup.map_mono hKleU) inf_le_right
    have hcard : Nat.card ↥(Work.GW2.conjSub e C.D.K ⊔ (B.U ⊓ Work.GW2.conjSub e B.U)) =
        Nat.card ↥(Work.GW2.conjSub e B.U) := by
      have hXnorm : (B.U ⊓ Work.GW2.conjSub e B.U) ≤
          Subgroup.normalizer ((Work.GW2.conjSub e C.D.K : Subgroup G) : Set G) := by
        rw [hNK']; exact le_trans inf_le_right hUe_le
      have hinf : Work.GW2.conjSub e C.D.K ⊓ (B.U ⊓ Work.GW2.conjSub e B.U) = ⊥ := by
        rw [← inf_assoc, hK'infU, bot_inf_eq]
      rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hXnorm hinf, hK'card, hXmul,
        ← hUecard]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hXne : B.U ⊓ Work.GW2.conjSub e B.U ≠ ⊥ := by
    intro hbot
    have hUcard3 : Nat.card ↥B.U = 3 := by
      have h1 := hXmul
      rw [hbot, Subgroup.card_bot] at h1
      omega
    have hKU : C.D.K = B.U := by
      refine Subgroup.eq_of_le_of_card_ge hKleU ?_
      rw [hUcard3, hKcard]
    have hFleK : C.D.F ≤ C.D.K := hKU ▸ hFleU
    have hFne : C.D.F ≠ ⊥ := by
      intro h; rw [h, Subgroup.card_bot] at hFcard; simp at hFcard
    refine hFne ?_
    rw [inf_eq_left.mpr hFleK] at hFinfK
    exact hFinfK
  have hX3 : IsPGroup 3 ↥(B.U ⊓ Work.GW2.conjSub e B.U) := hU3.to_le inf_le_left
  have hXcenter : Subgroup.center ↥(B.U ⊓ Work.GW2.conjSub e B.U) ≠ ⊥ :=
    center_ne_bot_of_isPGroup_A4c2 hX3 hXne
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXcenter
  set x : G := (z : ↥(B.U ⊓ Work.GW2.conjSub e B.U)).1 with hxdef
  have hxX : x ∈ B.U ⊓ Work.GW2.conjSub e B.U := by rw [hxdef]; exact z.1.2
  have hxZ : x ∈ (Subgroup.center ↥(B.U ⊓ Work.GW2.conjSub e B.U)).map
      (B.U ⊓ Work.GW2.conjSub e B.U).subtype := by
    rw [hxdef]
    exact Subgroup.mem_map.mpr ⟨z.1, z.2, rfl⟩
  have hxne : x ≠ 1 := fun hx1 => hzne (by
    apply Subtype.ext
    apply Subtype.ext
    rw [← hxdef]; exact hx1)
  rw [mem_center_map_iff_A4c2] at hxZ
  obtain ⟨hxXmem, hxXc⟩ := hxZ
  have hxU : x ∈ B.U := hxXmem.1
  have hxUe : x ∈ Work.GW2.conjSub e B.U := hxXmem.2
  have hK'leCx : Work.GW2.conjSub e C.D.K ≤ Subgroup.centralizer ({x} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hK'leCU hk)) x hxU
  have hXleCx : B.U ⊓ Work.GW2.conjSub e B.U ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    exact (hxXc y hy).symm
  have hUeleCx : Work.GW2.conjSub e B.U ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hK'X]
    exact sup_le hK'leCx hXleCx
  have hxZUe : x ∈ (Subgroup.center ↥(Work.GW2.conjSub e B.U)).map
      (Work.GW2.conjSub e B.U).subtype := by
    rw [mem_center_map_iff_A4c2]
    refine ⟨hxUe, fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hUeleCx hy) x (Set.mem_singleton x)).symm
  rw [← hK'Z] at hxZUe
  have hmem : x ∈ Work.GW2.conjSub e C.D.K ⊓ (B.U ⊓ Work.GW2.conjSub e B.U) :=
    Subgroup.mem_inf.mpr ⟨hxZUe, hxXmem⟩
  rw [← inf_assoc, hK'infU, bot_inf_eq] at hmem
  exact hxne (Subgroup.mem_bot.mp hmem)

end Work.CORE4
