import Mathlib
import Submission.Work.ThmF.Prove.step9Omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9Omega2` — `[S, S] ≤ T ⊓ C_G(y)`

Peterfalvi II Ch. V §3, step (9): the commutator form of the local `Ω₁`-statement.

Let `p` be an odd prime, `T ≤ S ≤ G` with `T` a cyclic `p`-group normalized by `S`,
`y ∈ S \ T` of order `p`, `S = T ⊔ ⟨y⟩` and `|T ⊓ C_G(y)| ≤ p`.  Then every commutator
`a b a⁻¹ b⁻¹` (`a, b ∈ S`) lies in `Z := T ⊓ C_G(y)`; equivalently `S/Z` is abelian.

## Route

Write `Z = T ⊓ C_G(y)`.  The substance is the "core" claim

  `[t, y] = t y t⁻¹ y⁻¹ ∈ Z`  for every `t ∈ T`.

Indeed `T = ⟨g⟩` is cyclic of order `p ^ n`, `y ^ p = 1`, so `σ := conj_y` acts on `T` and
`σ ^ p = id`; writing `y g y⁻¹ = g ^ l`, one has `g ^ (l ^ p) = g`, i.e. `p ^ n ∣ l ^ p - 1`,
and `(g ^ (1 - l) * y) ^ p = g ^ (1 - l ^ p) = 1`.  That is exactly the hypothesis of
`conjFixOfPowMul` (`Work.ThmF.Prove.step9Omega1`), which yields `y * g ^ (1 - l) * y⁻¹ =
g ^ (1 - l)`, i.e. `[g, y] = g ^ (1 - l)` is fixed by `conj_y`.  For a general `t = g ^ m` this
transports by `y g ^ m y⁻¹ = g ^ (l * m)`.

With the core in hand, `Z` is central in `S` (`T` is abelian and `Z ≤ C_G(y)`), and for every
`i` one has `y ^ i * t * (y ^ i)⁻¹ ∈ t * Z` (carried along by `MulAut.conj y`), so each
`[t, y ^ i]` and each `[y ^ i, t]` lies in `Z`.  The final computation uses the commutator
identities `commutatorElement_mul_left_eq_conj_mul` and
`commutatorElement_mul_right_eq_mul_conj`:

`[t₁ y ^ i, t₂ y ^ j] = t₁ [y ^ i, t₂ y ^ j] t₁⁻¹ [t₁, t₂ y ^ j] = [y ^ i, t₂] [t₁, y ^ j] ∈ Z`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000
open scoped IsMulCommutative commutatorElement

namespace Work.ThmF.Prove

/-- **Core of step (9).**  `[t, y] ∈ T ⊓ C_G(y)` for every `t` in the cyclic `p`-group `T`. -/
theorem step9Omega2Core {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S T : Subgroup G} {y : G}
    (hS : S = T ⊔ Subgroup.zpowers y)
    (hTn : ∀ g ∈ S, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hTc : IsCyclic ↥T) (hTp : IsPGroup p T)
    (hyT : y ∉ T) (hordy : orderOf y = p)
    (hC : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ p) :
    ∀ t ∈ T, t * y * t⁻¹ * y⁻¹ ∈ T ⊓ Subgroup.centralizer ({y} : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := T ⊓ Subgroup.centralizer ({y} : Set G) with hZdef
  have hyS : y ∈ S := by rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hTyp : y ^ p = 1 := by rw [← hordy]; exact pow_orderOf_eq_one y
  haveI hcycT : IsCyclic ↥T := hTc
  haveI hcommT : IsMulCommutative ↥T := IsCyclic.isMulCommutative
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥T) (⟨b, hb⟩ : ↥T))
  intro t ht
  by_cases hTbot : T = ⊥
  · rw [hTbot] at ht
    have ht1 : t = 1 := Subgroup.mem_bot.mp ht
    rw [ht1]
    simp
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    have hgord : orderOf g = Nat.card ↥T := orderOf_eq_card_of_forall_mem_zpowers hg
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hn
        exact hTbot (Subgroup.card_eq_one.mp hn)
      · exact hpos
    have hgord' : orderOf (g : G) = p ^ n := by
      rw [Subgroup.orderOf_coe, hgord, hn]
    -- the exponent `l` of the action of `y` on the generator `g`
    have hwgT : y * (g : G) * y⁻¹ ∈ T := hTn y hyS (g : G) g.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y * (g : G) * y⁻¹, hwgT⟩)
    have hl' : y * (g : G) * y⁻¹ = (g : G) ^ l := by
      have h := congrArg Subtype.val hl
      simpa using h.symm
    -- `y ^ p = 1` gives `g ^ (l ^ p) = g`
    have hlp_eq : (g : G) ^ (l ^ p) = (g : G) := by
      have hconj : ((MulAut.conj y) ^ p) (g : G) = (g : G) ^ (l ^ p) :=
        conjPowApply y (g : G) hl' p
      have hwp : (MulAut.conj y) ^ p = 1 := by
        rw [← map_pow (MulAut.conj) y p, hTyp, map_one]
      rw [← hconj, hwp, MulAut.one_apply]
    -- `(g ^ (1 - l) * y) ^ p = 1`
    have hgp : ((g : G) ^ (1 - l) * y) ^ p = 1 := by
      rw [powMulZpow hl' (1 - l) p, hTyp, mul_one]
      have hgeom : (1 - l) * (∑ i ∈ Finset.range p, l ^ i) = 1 - l ^ p := by
        have h := mul_geom_sum l p
        rw [show (1 : ℤ) - l = -(l - 1) from by ring, neg_mul, h]
        ring
      rw [hgeom, show (1 : ℤ) - l ^ p = 1 + (-(l ^ p)) from by ring, zpow_add, zpow_one,
        zpow_neg, hlp_eq, mul_inv_cancel]
    have hcrux : y * (g : G) ^ (1 - l) * y⁻¹ = (g : G) ^ (1 - l) :=
      conjFixOfPowMul hp hp2 hn1 hgord' hTyp hl' hgp
    -- `[g, y] = g ^ (1 - l)`
    have hgy_eq : (g : G) * y * (g : G)⁻¹ * y⁻¹ = (g : G) ^ (1 - l) := by
      have h1 : y * (g : G)⁻¹ * y⁻¹ = ((g : G) ^ l)⁻¹ := by rw [← hl']; group
      rw [show (g : G) * y * (g : G)⁻¹ * y⁻¹ = (g : G) * (y * (g : G)⁻¹ * y⁻¹) from by group,
        h1, ← zpow_neg]
      group
    have hgyZ : (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ Z := by
      rw [hZdef, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [hgy_eq]; exact T.zpow_mem g.2 (1 - l)
      · rw [Subgroup.mem_centralizer_singleton_iff, hgy_eq]
        exact (mul_inv_eq_iff_eq_mul.mp hcrux).symm
    -- transport to an arbitrary `t = g ^ m`
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨t, ht⟩)
    have hm' : (g : G) ^ m = t := by
      have h := congrArg Subtype.val hm
      simpa using h
    have hpow : (g : G) ^ m * y * ((g : G) ^ m)⁻¹ * y⁻¹
        = ((g : G) * y * (g : G)⁻¹ * y⁻¹) ^ m := by
      have hygm : y * (g : G) ^ m * y⁻¹ = (g : G) ^ (l * m) := conjZpow y (g : G) hl' m
      rw [hgy_eq]
      calc (g : G) ^ m * y * ((g : G) ^ m)⁻¹ * y⁻¹
          = (g : G) ^ m * (y * ((g : G) ^ m)⁻¹ * y⁻¹) := by group
        _ = (g : G) ^ m * ((g : G) ^ (l * m))⁻¹ := by
              rw [show y * ((g : G) ^ m)⁻¹ * y⁻¹ = (y * (g : G) ^ m * y⁻¹)⁻¹ from by group,
                hygm]
        _ = (g : G) ^ m * (g : G) ^ (-(l * m)) := by rw [zpow_neg]
        _ = (g : G) ^ (m + (-(l * m))) := by rw [← zpow_add]
        _ = (g : G) ^ ((1 - l) * m) := by
              rw [show m + (-(l * m)) = (1 - l) * m from by ring]
        _ = ((g : G) ^ (1 - l)) ^ m := by rw [← zpow_mul]
    rw [← hm', hpow]
    exact Z.zpow_mem hgyZ m

/-- **Peterfalvi II Ch. V §3, step (9), commutator form.**  `[S, S] ≤ T ⊓ C_G(y)`. -/
theorem step9Omega2 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S T : Subgroup G} {y : G}
    (hS : S = T ⊔ Subgroup.zpowers y)
    (hTn : ∀ g ∈ S, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hTc : IsCyclic ↥T) (hTp : IsPGroup p T)
    (hyT : y ∉ T) (hordy : orderOf y = p)
    (hC : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ p) :
    ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ T ⊓ Subgroup.centralizer ({y} : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := T ⊓ Subgroup.centralizer ({y} : Set G) with hZdef
  have hyS : y ∈ S := by rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hSle : Subgroup.zpowers y ≤ S := Subgroup.zpowers_le.mpr hyS
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun a ha k hk => hTn a (hSle ha) k hk)
  haveI hcycT : IsCyclic ↥T := hTc
  haveI hcommT : IsMulCommutative ↥T := IsCyclic.isMulCommutative
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥T) (⟨b, hb⟩ : ↥T))
  -- decomposition of the elements of `S` as `t * y ^ i`
  have hSdec : ∀ x, x ∈ S ↔ ∃ t ∈ T, ∃ i : ℤ, t * y ^ i = x := by
    intro x
    rw [hS, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers y) hyN]
    constructor
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ⟨a, ha, i, by rw [hi]; exact hab⟩
    · rintro ⟨a, ha, i, rfl⟩
      exact Set.mem_mul.mpr ⟨a, ha, y ^ i, Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩, rfl⟩
  -- the core
  have hkey : ∀ t ∈ T, t * y * t⁻¹ * y⁻¹ ∈ Z :=
    step9Omega2Core hp hp2 hS hTn hTc hTp hyT hordy hC
  have hZy : ∀ z ∈ Z, z * y = y * z := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mp hz.2
  -- `Z` is central in `S`
  have hZcentral : ∀ z ∈ Z, ∀ s ∈ S, s * z = z * s := by
    intro z hz s hs
    obtain ⟨t, ht, i, rfl⟩ := (hSdec s).mp hs
    have hzi : y ^ i * z = z * y ^ i :=
      (Commute.zpow_right (show Commute z y from hZy z hz) i).eq.symm
    calc (t * y ^ i) * z = t * (y ^ i * z) := by rw [mul_assoc]
      _ = t * (z * y ^ i) := by rw [hzi]
      _ = (t * z) * y ^ i := by rw [mul_assoc]
      _ = (z * t) * y ^ i := by rw [hTcomm t ht z hz.1]
      _ = z * (t * y ^ i) := by rw [mul_assoc]
  -- conjugation by `y ^ i` moves `t` within its `Z`-coset
  have hkeyi_ex : ∀ t ∈ T, ∀ i : ℤ, ∃ z ∈ Z, y ^ i * t * (y ^ i)⁻¹ = t * z := by
    intro t ht i
    have hd : ⁅t, y⁆ ∈ Z := hkey t ht
    have hcz : ∀ z ∈ Z, MulAut.conj y z = z := by
      intro z hz
      rw [MulAut.conj_apply, ← hZy z hz]; group
    have hctT : MulAut.conj y t ∈ T := by
      rw [MulAut.conj_apply]; exact hTn y hyS t ht
    have hct : MulAut.conj y t = t * ⁅t, y⁆ ^ (-1 : ℤ) := by
      have h1 : ⁅t, y⁆ = t * (MulAut.conj y t)⁻¹ := by
        rw [commutatorElement_def, MulAut.conj_apply]; group
      rw [zpow_neg_one, h1]
      rw [show t * (t * (MulAut.conj y t)⁻¹)⁻¹ = t * MulAut.conj y t * t⁻¹ from by group]
      rw [hTcomm t ht (MulAut.conj y t) hctT]
      group
    have hbase : ∃ z ∈ Z, (1 : MulAut G) t = t * z := ⟨1, Z.one_mem, by simp⟩
    have hstep : ∀ e : MulAut G, (∃ z ∈ Z, e t = t * z) →
        ∃ z ∈ Z, (MulAut.conj y * e) t = t * z := by
      rintro e ⟨z, hz, hze⟩
      exact ⟨⁅t, y⁆⁻¹ * z, Z.mul_mem (Z.inv_mem hd) hz, by
        rw [MulAut.mul_apply, hze, map_mul, hct, hcz z hz, zpow_neg_one]; group⟩
    have hstepinv : ∀ e : MulAut G, (∃ z ∈ Z, e t = t * z) →
        ∃ z ∈ Z, ((MulAut.conj y)⁻¹ * e) t = t * z := by
      rintro e ⟨z, hz, hze⟩
      have hczinvz : (MulAut.conj y)⁻¹ z = z := by
        have h2 : (MulAut.conj y)⁻¹ ((MulAut.conj y) z) = z := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rwa [hcz z hz] at h2
      have hczinvd : (MulAut.conj y)⁻¹ ⁅t, y⁆ = ⁅t, y⁆ := by
        have h2 : (MulAut.conj y)⁻¹ ((MulAut.conj y) ⁅t, y⁆) = ⁅t, y⁆ := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rwa [hcz (⁅t, y⁆) hd] at h2
      have hcinvt : (MulAut.conj y)⁻¹ t = t * ⁅t, y⁆ := by
        have h2 : (MulAut.conj y)⁻¹ ((MulAut.conj y) t) = t := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        rw [hct, map_mul, map_zpow, hczinvd, zpow_neg_one] at h2
        exact mul_inv_eq_iff_eq_mul.mp h2
      exact ⟨⁅t, y⁆ * z, Z.mul_mem hd hz, by
        rw [MulAut.mul_apply, hze, map_mul, hcinvt, hczinvz]; group⟩
    obtain ⟨z, hz, hze⟩ := zpow_induction_left (g := MulAut.conj y)
      (P := fun e => ∃ z ∈ Z, e t = t * z) hbase hstep hstepinv i
    rw [← map_zpow (MulAut.conj) y i, MulAut.conj_apply] at hze
    exact ⟨z, hz, hze⟩
  -- hence `[t, y ^ i] ∈ Z` for every `i`
  have hkeyiZ : ∀ t ∈ T, ∀ i : ℤ, ⁅t, y ^ i⁆ ∈ Z := by
    intro t ht i
    obtain ⟨z, hz, hze⟩ := hkeyi_ex t ht i
    have hzi : ⁅t, y ^ i⁆ = z⁻¹ := by
      rw [commutatorElement_def]
      rw [show t * y ^ i * t⁻¹ * (y ^ i)⁻¹ = t * (y ^ i * t⁻¹ * (y ^ i)⁻¹) from by group]
      rw [show y ^ i * t⁻¹ * (y ^ i)⁻¹ = (y ^ i * t * (y ^ i)⁻¹)⁻¹ from by group, hze]
      rw [show t * (t * z)⁻¹ = t * z⁻¹ * t⁻¹ from by group]
      rw [hTcomm t ht z⁻¹ (Z.inv_mem hz).1]
      group
    rw [hzi]
    exact Z.inv_mem hz
  -- final computation
  intro a ha b hb
  obtain ⟨t₁, ht₁, i, rfl⟩ := (hSdec a).mp ha
  obtain ⟨t₂, ht₂, j, rfl⟩ := (hSdec b).mp hb
  have ht₁S : t₁ ∈ S := by rw [hS]; exact Subgroup.mem_sup_left ht₁
  have ht₂S : t₂ ∈ S := by rw [hS]; exact Subgroup.mem_sup_left ht₂
  have hZi : ⁅y ^ i, t₂⁆ ∈ Z := by
    rw [← commutatorElement_inv]; exact Z.inv_mem (hkeyiZ t₂ ht₂ i)
  have hZj : ⁅t₁, y ^ j⁆ ∈ Z := hkeyiZ t₁ ht₁ j
  have hcommab : ⁅y ^ i, y ^ j⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, ← zpow_add, ← zpow_add, add_comm]
  have hcommTT : ⁅t₁, t₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hTcomm t₁ ht₁ t₂ ht₂)
  have hbc1 : ⁅y ^ i, t₂ * y ^ j⁆ = ⁅y ^ i, t₂⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hcommab, mul_one]; group
  have hbc2 : ⁅t₁, t₂ * y ^ j⁆ = ⁅t₁, y ^ j⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hcommTT, one_mul]
    rw [hZcentral ⁅t₁, y ^ j⁆ hZj t₂ ht₂S]; group
  have hmain : ⁅t₁ * y ^ i, t₂ * y ^ j⁆ = ⁅y ^ i, t₂⁆ * ⁅t₁, y ^ j⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hbc1, hbc2]
    rw [hZcentral ⁅y ^ i, t₂⁆ hZi t₁ ht₁S]; group
  rw [← commutatorElement_def, hmain]
  exact Z.mul_mem hZi hZj

end Work.ThmF.Prove
