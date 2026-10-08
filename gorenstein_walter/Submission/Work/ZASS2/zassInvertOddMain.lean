import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS.Frobenius
import Submission.Work.ZASS.card_G
import Submission.Work.ZASS.conjBy_mem_pairStab
import Submission.Work.ZASS.zassInvolutionSwapProp
import Submission.Work.ZASS.index_pairStab_normalizer_le_two
import Submission.Work.ZASS.isZGroup_normalizer_of_index_le_two
import Submission.Work.ZASS.normalizer_le_normalizer_pairStab
import Submission.Work.ZASS.false_of_isSimpleGroup_of_normalizer_le_centralizer
import Submission.Work.ZASS2.sylowMapOfNotDvdIndex
import Submission.Work.ZASS2.commutatorLeOfIndexLeTwo
import Submission.Work.ZASS2.eqOfNeOneOfCardLeTwo

namespace Work.ZASS2

open scoped commutatorElement in
/-- **Burnside's transfer theorem against simplicity.**  Let `G` be a finite simple group, `T ≤ G`
a Z-group and `r ≠ 2` a prime dividing the index of `T'`.  If `Q` is a Sylow `r`-subgroup of `G`
with `Q ≤ T` and `N_G(Q) ≤ T`, then `G` cannot be simple: `N_G(Q)' ≤ T'` and `Q ∩ T' = 1`
(coprimality of `|T'|` and `[T : T']`), so `N_G(Q) ≤ C_G(Q)` and Burnside's normal
`r`-complement contradicts simplicity. -/
private theorem burnside_aux {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {T : Subgroup G} (hTZ : IsZGroup ↥T) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrdvd : r ∣ (commutator ↥T).index) (hnr : ¬ IsPGroup r G)
    (Q : Sylow r G) (hQne : (Q : Subgroup G) ≠ ⊥) (hQT : (Q : Subgroup G) ≤ T)
    (hNQT : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤ T) : False := by
  set Tf : Subgroup G := Subgroup.map T.subtype (commutator ↥T) with hTfdef
  have hTfcoe : Tf = ⁅T, T⁆ := by
    rw [hTfdef, Subgroup.map_subtype_commutator]
  -- `r ∤ |T'|`
  have hcop := IsZGroup.coprime_commutator_index ↥T
  have hrT' : ¬ r ∣ Nat.card ↥(commutator ↥T) := by
    intro hd
    have h1 : Nat.Coprime (Nat.card ↥(commutator ↥T)) r :=
      Nat.Coprime.coprime_dvd_right hrdvd hcop
    rw [Nat.Coprime] at h1
    have h3 : r ∣ 1 := by
      have h4 : r ∣ (Nat.card ↥(commutator ↥T)).gcd r := Nat.dvd_gcd hd (dvd_refl r)
      rwa [h1] at h4
    exact (Fact.out : Nat.Prime r).not_dvd_one h3
  have hcardTf : Nat.card ↥Tf = Nat.card ↥(commutator ↥T) :=
    Subgroup.card_map_of_injective (K := commutator ↥T) (f := T.subtype) T.subtype_injective
  have hrTf : ¬ r ∣ Nat.card ↥Tf := by rw [hcardTf]; exact hrT'
  -- `Q ∩ T' = 1`
  have hQTf : (Q : Subgroup G) ⊓ Tf = ⊥ := by
    have hle : (Q : Subgroup G) ⊓ Tf ≤ Q := inf_le_left
    have hPG : IsPGroup r ↥((Q : Subgroup G) ⊓ Tf) := (Q.isPGroup').to_le hle
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPG
    have hdvd : Nat.card ↥((Q : Subgroup G) ⊓ Tf) ∣ Nat.card ↥Tf :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hn] at hdvd
    have hpow : r ^ n = 1 := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · rw [hn0, pow_zero]
      · exact absurd (dvd_pow_self r (by omega : n ≠ 0) |>.trans hdvd) hrTf
    exact Subgroup.card_eq_one.mp (hn.trans hpow)
  -- `⁅Q, N_G(Q)⁆ ≤ Q ∩ T'`
  have hKQ : ⁅(Q : Subgroup G), Subgroup.normalizer ((Q : Subgroup G) : Set G)⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    have h1 : y * x⁻¹ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hy x⁻¹).mp (Q.inv_mem hx)
    rw [commutatorElement_def,
      show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) from by group]
    exact Q.mul_mem hx h1
  have hKTf : ⁅(Q : Subgroup G), Subgroup.normalizer ((Q : Subgroup G) : Set G)⁆ ≤ Tf := by
    rw [hTfcoe]
    exact Subgroup.commutator_mono hQT hNQT
  have hbot : ⁅(Q : Subgroup G), Subgroup.normalizer ((Q : Subgroup G) : Set G)⁆ = ⊥ :=
    le_bot_iff.mp (hQTf ▸ le_inf hKQ hKTf)
  have hcent : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Q : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hbot)
  exact Work.ZASS.false_of_isSimpleGroup_of_normalizer_le_centralizer_subgroup
    (G := G) (q := r) ‹IsSimpleGroup G› hr2 hnr Q hQne hcent

open scoped commutatorElement in
/-- **The endgame of HB III.XI 1.5.**  Let `T` be a finite group, `H ⊴ T` with `H = T'` a Z-group,
and `σ ∈ T \ H` with `σ² ∈ H` and `T = H⟨σ⟩`.  Then `H` is cyclic and `σ` inverts it.

`H` is abelian (cyclic), and `δ x = x (σ x σ⁻¹)⁻¹ = ⁅x, σ⁆` is an endomorphism of `H`; the four
cases of the decomposition `T = H ∪ Hσ` show `T' = ⁅T,T⁆ ≤ δ(H)`, i.e. `δ` is onto.  Since
`σ² ∈ H` centralises `H`, the conjugation `φ` by `σ` satisfies `φ² = id`, and `φ(δ x) = δ x⁻¹`;
so `φ y = y⁻¹` for every `y ∈ H`. -/
private theorem conj_inverts_aux {T : Type} [Group T] [Finite T] {H : Subgroup T}
    (hHc : commutator T = H) (hZ : IsZGroup T) (σ : T) (hσH : σ ∉ H)
    (hσ2 : σ * σ ∈ H) (hTop : H ⊔ Subgroup.zpowers σ = ⊤) :
    IsCyclic H ∧ ∀ x ∈ H, σ * x * σ⁻¹ = x⁻¹ := by
  haveI hHn : H.Normal := hHc ▸ Subgroup.commutator_normal (⊤ : Subgroup T) ⊤
  have hcyc : IsCyclic ↥H := hHc ▸ IsZGroup.isCyclic_commutator T
  -- ## `H` is abelian
  obtain ⟨e, he⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hcomm : ∀ x y : ↥H, x * y = y * x := by
    intro x y
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp (show x ∈ Subgroup.zpowers e from by rw [he]; trivial)
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp (show y ∈ Subgroup.zpowers e from by rw [he]; trivial)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  -- ## basic conjugation facts
  have hconjH : ∀ (u y : ↥H), (u : T) * (y : T) * (u : T)⁻¹ = (y : T) := by
    intro u y
    have h1 : u * y * u⁻¹ = y := by rw [hcomm u y]; group
    calc (u : T) * (y : T) * (u : T)⁻¹ = ((u * y * u⁻¹ : ↥H) : T) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = (y : T) := by rw [h1]
  have hφco : ∀ x : ↥H, (((MulAut.conjNormal σ) x : ↥H) : T) = σ * (x : T) * σ⁻¹ :=
    fun x => MulAut.conjNormal_apply σ x
  have hσ2coe : (↑(⟨σ * σ, hσ2⟩ : ↥H) : T) = σ * σ := rfl
  have hφ2 : ∀ x : ↥H, (MulAut.conjNormal σ) ((MulAut.conjNormal σ) x) = x := by
    intro x
    have hh := hconjH ⟨σ * σ, hσ2⟩ x
    rw [hσ2coe] at hh
    apply Subtype.ext
    rw [hφco, hφco]
    rw [show σ * (σ * (x : T) * σ⁻¹) * σ⁻¹ = (σ * σ) * (x : T) * (σ * σ)⁻¹ from by group]
    exact hh
  -- ## `δ x = x * (σ x σ⁻¹)⁻¹`
  have hδmul : ∀ a b : ↥H,
      a * b * ((MulAut.conjNormal σ) (a * b))⁻¹
        = (a * ((MulAut.conjNormal σ) a)⁻¹) * (b * ((MulAut.conjNormal σ) b)⁻¹) := by
    intro a b
    rw [map_mul, mul_inv_rev]
    calc a * b * (((MulAut.conjNormal σ) b)⁻¹ * ((MulAut.conjNormal σ) a)⁻¹)
        = a * ((b * ((MulAut.conjNormal σ) b)⁻¹) * ((MulAut.conjNormal σ) a)⁻¹) := by group
      _ = a * (((MulAut.conjNormal σ) a)⁻¹ * (b * ((MulAut.conjNormal σ) b)⁻¹)) := by
            rw [hcomm (b * ((MulAut.conjNormal σ) b)⁻¹) ((MulAut.conjNormal σ) a)⁻¹]
      _ = a * ((MulAut.conjNormal σ) a)⁻¹ * (b * ((MulAut.conjNormal σ) b)⁻¹) := by group
  let δ : ↥H →* ↥H :=
    MonoidHom.mk' (fun x => x * ((MulAut.conjNormal σ) x)⁻¹) hδmul
  have hδco : ∀ x : ↥H, ((δ x : ↥H) : T) = (x : T) * (σ * (x : T) * σ⁻¹)⁻¹ := by
    intro x
    show (((x * ((MulAut.conjNormal σ) x)⁻¹ : ↥H)) : T) = (x : T) * (σ * (x : T) * σ⁻¹)⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφco]
  let D : Subgroup T := Subgroup.map H.subtype δ.range
  have hDle : D ≤ H := Subgroup.map_subtype_le _
  have hDmem : ∀ h : ↥H, ((δ h : ↥H) : T) ∈ D := fun h =>
    Subgroup.mem_map.mpr ⟨δ h, ⟨h, rfl⟩, rfl⟩
  -- ## `T = H ∪ Hσ`
  have hsq : σ ^ (2 : ℤ) = σ * σ := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
  have hzpow2 : ∀ k : ℤ, (σ * σ) ^ k = σ ^ (2 * k) := by
    intro k
    rw [← hsq, ← zpow_mul]
  have hdec : ∀ x : T, x ∈ H ∨ ∃ h : ↥H, x = (h : T) * σ := by
    intro x
    have hx : x ∈ H ⊔ Subgroup.zpowers σ := by rw [hTop]; trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hx with ⟨h, hh, z, hz, hzx⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd' j with ⟨k, hk | hk⟩
    · left
      rw [← hzx, hk, ← hzpow2 k]
      exact H.mul_mem hh (H.zpow_mem hσ2 k)
    · right
      refine ⟨⟨h * (σ * σ) ^ k, H.mul_mem hh (H.zpow_mem hσ2 k)⟩, ?_⟩
      rw [← hzx, hk]
      show h * σ ^ (2 * k + 1) = (h * (σ * σ) ^ k) * σ
      rw [show σ ^ (2 * k + 1) = σ ^ (2 * k) * σ from by rw [zpow_add, zpow_one],
        ← hzpow2 k]
      group
  -- ## the four commutator cases
  have hcase1 : ∀ h₁ h₂ : ↥H, ⁅(h₁ : T), (h₂ : T)⁆ = 1 := by
    intro h₁ h₂
    rw [commutatorElement_def, hconjH h₁ h₂, mul_inv_cancel]
  have hcase2 : ∀ h₁ h₂ : ↥H, ⁅(h₁ : T), (h₂ : T) * σ⁆ = ((δ h₁ : ↥H) : T) := by
    intro h₁ h₂
    rw [commutatorElement_def, hδco]
    rw [show (((h₂ : T) * σ))⁻¹ = σ⁻¹ * (h₂ : T)⁻¹ from by group]
    rw [show (h₁ : T) * ((h₂ : T) * σ) * (h₁ : T)⁻¹ * (σ⁻¹ * (h₂ : T)⁻¹)
          = (h₁ : T) * ((h₂ : T) * (σ * (h₁ : T)⁻¹ * σ⁻¹) * (h₂ : T)⁻¹) from by group]
    rw [show σ * (h₁ : T)⁻¹ * σ⁻¹ = (((MulAut.conjNormal σ) h₁⁻¹ : ↥H) : T) from
      (MulAut.conjNormal_apply σ h₁⁻¹).symm]
    rw [hconjH h₂ ((MulAut.conjNormal σ) h₁⁻¹)]
    congr 1
    rw [show (((MulAut.conjNormal σ) h₁⁻¹ : ↥H) : T) = σ * (h₁ : T)⁻¹ * σ⁻¹ from
      MulAut.conjNormal_apply σ h₁⁻¹]
    group
  have hcase3 : ∀ h₁ h₂ : ↥H, ⁅(h₁ : T) * σ, (h₂ : T)⁆ = (((δ h₂ : ↥H) : T))⁻¹ := by
    intro h₁ h₂
    rw [(commutatorElement_inv (h₂ : T) ((h₁ : T) * σ)).symm, hcase2 h₂ h₁]
  have hcase4 : ∀ h₁ h₂ : ↥H,
      ⁅(h₁ : T) * σ, (h₂ : T) * σ⁆ = ((δ h₁ : ↥H) : T) * (((δ h₂ : ↥H) : T))⁻¹ := by
    intro h₁ h₂
    rw [commutatorElement_def, hδco, hδco]
    rw [show (h₁ : T) * σ * ((h₂ : T) * σ) * ((h₁ : T) * σ)⁻¹ * ((h₂ : T) * σ)⁻¹
          = (h₁ : T) * (((MulAut.conjNormal σ) (h₂ * h₁⁻¹) : ↥H) : T) * (h₂ : T)⁻¹ from by
        rw [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]; group]
    rw [show (h₁ : T) * (((MulAut.conjNormal σ) (h₂ * h₁⁻¹) : ↥H) : T) * (h₂ : T)⁻¹
          = (((h₁ * (MulAut.conjNormal σ) (h₂ * h₁⁻¹) * h₂⁻¹ : ↥H)) : T) from by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
    rw [show (h₁ : T) * (σ * (h₁ : T) * σ⁻¹)⁻¹ * ((h₂ : T) * (σ * (h₂ : T) * σ⁻¹)⁻¹)⁻¹
          = (((h₁ * ((MulAut.conjNormal σ) h₁)⁻¹
                * (h₂ * ((MulAut.conjNormal σ) h₂)⁻¹)⁻¹ : ↥H)) : T) from by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]]
    have hkey : h₁ * (MulAut.conjNormal σ) (h₂ * h₁⁻¹) * h₂⁻¹
        = (δ h₁) * (δ h₂)⁻¹ := by
      rw [show δ h₁ = h₁ * ((MulAut.conjNormal σ) h₁)⁻¹ from rfl,
        show δ h₂ = h₂ * ((MulAut.conjNormal σ) h₂)⁻¹ from rfl]
      rw [map_mul, map_inv, mul_inv_rev, inv_inv]
      rw [hcomm ((MulAut.conjNormal σ) h₂) (((MulAut.conjNormal σ) h₁)⁻¹)]
      group
    exact congrArg Subtype.val hkey
  -- ## `commutator T ≤ D`
  have hcommLe : commutator T ≤ D := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    rcases hdec x with hx | ⟨h₁, rfl⟩ <;> rcases hdec y with hy | ⟨h₂, rfl⟩
    · rw [hcase1 ⟨x, hx⟩ ⟨y, hy⟩]; exact D.one_mem
    · rw [hcase2 ⟨x, hx⟩ h₂]; exact hDmem _
    · rw [hcase3 h₁ ⟨y, hy⟩]; exact D.inv_mem (hDmem _)
    · rw [hcase4 h₁ h₂]; exact D.mul_mem (hDmem _) (D.inv_mem (hDmem _))
  -- ## `H ≤ D`, so `δ` is onto
  have hHleD : H ≤ D := hHc ▸ hcommLe
  have honto : ∀ y : ↥H, ∃ x : ↥H, δ x = y := by
    intro y
    have hy : (y : T) ∈ D := hHleD y.2
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨x, rfl⟩
    exact ⟨x, Subtype.ext hzy⟩
  -- ## `σ`-conjugation is inversion on `H`
  have hφinv : ∀ y : ↥H, (MulAut.conjNormal σ) y = y⁻¹ := by
    intro y
    obtain ⟨x, hx⟩ := honto y
    rw [← hx]
    show (MulAut.conjNormal σ) (x * ((MulAut.conjNormal σ) x)⁻¹)
        = (x * ((MulAut.conjNormal σ) x)⁻¹)⁻¹
    rw [show (MulAut.conjNormal σ) (x * ((MulAut.conjNormal σ) x)⁻¹)
            = (MulAut.conjNormal σ) x * x⁻¹ from by rw [map_mul, map_inv, hφ2 x],
        show (x * ((MulAut.conjNormal σ) x)⁻¹)⁻¹
            = (MulAut.conjNormal σ) x * x⁻¹ from by rw [mul_inv_rev, inv_inv]]
  refine ⟨hcyc, ?_⟩
  intro x hx
  have h4 : ((MulAut.conjNormal σ) ⟨x, hx⟩ : ↥H) = ⟨x, hx⟩⁻¹ := hφinv ⟨x, hx⟩
  have h5 := congrArg (fun z : ↥H => (z : T)) h4
  rw [hφco] at h5
  simpa using h5

/-! # ZASS2 leaf: HB III.XI 1.5, the odd-`d` case (`Work.GW2.ZassInvertOddProp`)

Statement (already fixed in `Submission/Work/ZASS/Leaf9.lean`): in the Zassenhaus setting with
`IsSimpleGroup G`, `Odd ((p^k-1)/2)`, and `a ≠ b`, the two-point stabilizer `G_{ab}` is cyclic
and every `s` interchanging `a` and `b` inverts it.

The source proof is HB III.XI 1.5 (`REFS/vision/hb3_1982/p0172.md`, p. 164-165); simplicity
replaces the hypothesis "not `q`-nilpotent for any prime `q ∣ d`":

* `T := N_G(H)`; every element of `T` at most interchanges the two fixed points of `H`, and an
  involution `s₀` interchanging them exists (`Work.ZASS.zassInvolutionSwapProp`, HB 1.7b) and
  normalizes `H` (`Work.ZASS.conjBy_mem_pairStab`).  Hence `|T| = 2d` where `d = |H|`.
* `d` odd ⟹ `H` is a Z-group (`Work.ZASS.isZGroup_of_odd_of_free`, HB V 8.7), hence so is `T`
  (`Work.ZASS.isZGroup_normalizer_of_index_le_two`).  Thus `T'` and `T/T'` are cyclic of
  coprime orders (`IsZGroup.isCyclic_commutator`, `IsZGroup.coprime_commutator_index`,
  `IsZGroup.isCyclic_abelianization` — all in Mathlib).
* For an odd prime `r ∣ [T : T']`: take a Sylow `r`-subgroup `Q ≤ H`; it is also a Sylow of `G`
  (`r ∤ |G : H|`; use `Work.ZASS.card_G` and `Sylow.ofCard`), `N_G(Q) ≤ T`
  (`Work.ZASS.normalizer_le_normalizer_pairStab`), and `[N_G(Q), Q] ≤ Q ∩ T' = 1` because
  `N_G(Q)' ≤ T'` (`Subgroup.commutator_mono`) and `r ∤ |T'|` (coprimality above).  Hence
  `N_G(Q) ≤ C_G(Q)` (`Subgroup.commutator_eq_bot_iff_le_centralizer`) and Burnside's transfer
  theorem (`Work.ZASS.false_of_isSimpleGroup_of_normalizer_le_centralizer`) contradicts
  simplicity.
* So `[T : T'] = 2` — it divides `2d` and is a power of `2` — and `T' = H` (as `T' ≤ H`:
  `T/H` has order `≤ 2`).  So `H` is cyclic (`IsZGroup.isCyclic_commutator`).
* If `H = ⟨h⟩` and `h^{s₀} = h^k`, then `s₀² ∈ H` gives `k² ≡ 1 (d)` and `H = T' = ⟨h^{k-1}⟩`
  gives `(k-1, d) = 1`; hence `k ≡ -1 (d)` and `h^{s₀} = h^{-1}`; a general `s` interchanging
  `a, b` lies in the coset `H s₀`, so it inverts `H` too (H abelian). -/
theorem zassInvertOddMain : Work.GW2.ZassInvertOddProp := by
  intro G X _ _ _ _ p k _ hp hq hs h hodd a b hab
  ---------------------------------------------------------------------------------------------
  -- ## Setup
  ---------------------------------------------------------------------------------------------
  set H : Subgroup G := Work.Zassenhaus.pairStab G a b with hHdef
  set T : Subgroup G := Subgroup.normalizer (H : Set G) with hTdef
  have hHK : H = MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
    rw [hHdef]; exact Work.GW2.pairStab_eq_inf_stabilizer a b
  have hHT : H ≤ T := Subgroup.le_normalizer
  have hcardH : Nat.card ↥H = (p ^ k - 1) / 2 := by
    rw [hHdef]; exact Work.ZASS.card_pairStab h hab
  have hoddH : Odd (Nat.card ↥H) := by rw [hcardH]; exact hodd
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hq; omega
    · exact hkpos
  -- `H` is a Z-group (HB V 8.7), through the fixed-point-free action on the unipotent radical.
  obtain ⟨U, hUB, hcardU, hN, hdec, hfree, hequiv, hcommU, hexp⟩ :=
    Work.ZASS.exists_unipotent_structure (p := p) (k := k) hp hq h (inf := a) (zero := b) hab
  have hntU : Nontrivial ↥U := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardU]; omega
  have hZH : IsZGroup ↥H := by
    rw [hHdef]
    exact Work.ZASS.isZGroup_of_odd_of_free (U := U) (inf := a) (zero := b)
      hUB hN hfree hoddH hntU
  set H' : Subgroup ↥T := H.subgroupOf T with hH'def
  set Tf : Subgroup ↥T := commutator ↥T with hTfdef
  have hidx2 : H'.index ≤ 2 :=
    Work.ZASS.index_pairStab_normalizer_le_two (q := p ^ k) h hab hq
  have hZT : IsZGroup ↥T :=
    Work.ZASS.isZGroup_normalizer_of_index_le_two (H := H) hZH hoddH hidx2
  have hHn : H'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := T) (N := H) le_rfl
  ---------------------------------------------------------------------------------------------
  -- ## An involution `s₀` interchanging `a` and `b`
  ---------------------------------------------------------------------------------------------
  obtain ⟨s0, hs0ord, hs0a, hs0b⟩ :=
    Work.ZASS.zassInvolutionSwap_aux G X (p ^ k) hp.pow h a b hab
  have hs0T : s0 ∈ T := by
    show s0 ∈ Subgroup.normalizer (H : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h2 := Work.ZASS.conjBy_mem_pairStab hs0a hs0b hx
      show s0 * x * s0⁻¹ ∈ H
      rwa [Work.ZASS.conjBy] at h2
    · intro hx
      have hs0ia : s0⁻¹ • a = b := by rw [← hs0b, inv_smul_smul]
      have hs0ib : s0⁻¹ • b = a := by rw [← hs0a, inv_smul_smul]
      have h2 : Work.ZASS.conjBy s0⁻¹ (s0 * x * s0⁻¹) ∈ Work.Zassenhaus.pairStab G a b :=
        Work.ZASS.conjBy_mem_pairStab hs0ia hs0ib hx
      have h3 : Work.ZASS.conjBy s0⁻¹ (s0 * x * s0⁻¹) = x := by
        rw [Work.ZASS.conjBy]; group
      show x ∈ H
      rwa [h3] at h2
  have hs0H : s0 ∉ H := by
    intro hmem
    have h1 : s0 • a = a := (Work.Zassenhaus.mem_pairStab_iff.mp hmem).2
    rw [hs0a] at h1
    exact hab h1.symm
  ---------------------------------------------------------------------------------------------
  -- ## `[T : H] = 2`
  ---------------------------------------------------------------------------------------------
  have hTH2 : H'.index = 2 := by
    have hne1 : H'.index ≠ 1 := by
      intro h1
      have htop : H' = ⊤ := Subgroup.index_eq_one.mp h1
      have : (⟨s0, hs0T⟩ : ↥T) ∈ H' := by rw [htop]; trivial
      exact hs0H (Subgroup.mem_subgroupOf.mp this)
    have hne0 : H'.index ≠ 0 := by
      intro h0
      have hh := Subgroup.index_mul_card H'
      rw [h0, zero_mul] at hh
      exact (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩).ne' hh.symm
    omega
  ---------------------------------------------------------------------------------------------
  -- ## `T' ≤ H'` (the quotient `T/H ≅ C₂` is abelian)
  ---------------------------------------------------------------------------------------------
  have hT'leH' : Tf ≤ H' := commutatorLeOfIndexLeTwo hHn (by omega)
  ---------------------------------------------------------------------------------------------
  -- ## Cardinalities
  ---------------------------------------------------------------------------------------------
  have hcardH' : Nat.card ↥H' = Nat.card ↥H := by
    have h1 : Subgroup.map T.subtype H' = H := by
      rw [hH'def, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hHT
    have h2 : Nat.card ↥(Subgroup.map T.subtype H') = Nat.card ↥H' :=
      Subgroup.card_map_of_injective (K := H') (f := T.subtype) T.subtype_injective
    rw [h1] at h2
    exact h2.symm
  have hcardT : Nat.card ↥T = 2 * Nat.card ↥H := by
    have hh := Subgroup.index_mul_card H'
    rw [hTH2] at hh
    rw [hcardH'] at hh
    exact hh.symm
  ---------------------------------------------------------------------------------------------
  -- ## `m = [H : T']` divides `|H| = d`
  ---------------------------------------------------------------------------------------------
  let m : ℕ := Tf.relIndex H'
  have hm : m * Nat.card ↥Tf = Nat.card ↥H' := by
    have hh := Subgroup.index_mul_card (Tf.subgroupOf H')
    have hc : Nat.card ↥(Tf.subgroupOf H') = Nat.card ↥Tf :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'leH').toEquiv
    rw [hc] at hh
    exact hh
  have hmdvd : m ∣ Nat.card ↥H := by
    rw [← hcardH']
    exact ⟨Nat.card ↥Tf, hm.symm⟩
  ---------------------------------------------------------------------------------------------
  -- ## No odd prime divides `m` (Burnside's transfer theorem)
  ---------------------------------------------------------------------------------------------
  have hm1 : m = 1 := by
    by_contra hne
    obtain ⟨r, hrp, hrdvdm⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact r.Prime := ⟨hrp⟩
    have hrH : r ∣ Nat.card ↥H := hrdvdm.trans hmdvd
    have hrd : r ∣ (p ^ k - 1) / 2 := by rw [← hcardH]; exact hrH
    have hr2 : r ≠ 2 := by
      intro h2
      rw [h2] at hrd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
    have hcardG : Nat.card G = (p ^ k + 1) * p ^ k * ((p ^ k - 1) / 2) :=
      Work.ZASS.card_G (q := p ^ k) h hab
    have hdpos : 0 < (p ^ k - 1) / 2 := by omega
    have hHidx : H.index = (p ^ k + 1) * p ^ k := by
      have hh := Subgroup.index_mul_card H
      rw [hcardH, hcardG] at hh
      exact Nat.mul_right_cancel hdpos hh
    obtain ⟨j, hj⟩ := hp.pow
    have h2dvd : 2 ∣ p ^ k - 1 := ⟨j, by rw [hj]; omega⟩
    have heq : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := Nat.mul_div_cancel' h2dvd
    have hrq1 : r ∣ p ^ k - 1 := by
      rw [← heq]
      exact dvd_mul_of_dvd_right hrd 2
    have hsub1 : p ^ k - (p ^ k - 1) = 1 := by rw [hj]; omega
    have hsub2 : p ^ k + 1 - (p ^ k - 1) = 2 := by rw [hj]; omega
    have hrq : ¬ r ∣ p ^ k := by
      intro hdiv
      have h1 : r ∣ 1 := by
        have h2 := Nat.dvd_sub hdiv hrq1
        rwa [hsub1] at h2
      exact hrp.not_dvd_one h1
    have hrqp1 : ¬ r ∣ p ^ k + 1 := by
      intro hdiv
      have h1 : r ∣ 2 := by
        have h2 := Nat.dvd_sub hdiv hrq1
        rwa [hsub2] at h2
      have h2 : r = 2 := by
        have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) h1
        have hge : 2 ≤ r := hrp.two_le
        omega
      exact hr2 h2
    have hrIdx : ¬ r ∣ H.index := by
      rw [hHidx]
      intro hdiv
      rcases hrp.dvd_mul.mp hdiv with hc | hc
      · exact hrqp1 hc
      · exact hrq hc
    have hnr : ¬ IsPGroup r G := by
      intro hpgrp
      rw [IsPGroup.iff_card] at hpgrp
      obtain ⟨n, hn⟩ := hpgrp
      have hpdvd : p ∣ Nat.card G := by
        rw [hcardG]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (dvd_pow_self p (by omega : k ≠ 0)) (p ^ k + 1))
          ((p ^ k - 1) / 2)
      have hpdrn : p ∣ r ^ n := by rw [← hn]; exact hpdvd
      have hpdr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpdrn
      have hpr : p = r := ((hrp.dvd_iff_eq (Fact.out : Nat.Prime p).ne_one).mp hpdr).symm
      have hp1 : p ∣ 1 := by
        have h2 := Nat.dvd_sub (dvd_pow_self p (by omega : k ≠ 0))
          (show p ∣ p ^ k - 1 from hpr ▸ hrq1)
        rwa [hsub1] at h2
      exact (Fact.out : Nat.Prime p).not_dvd_one hp1
    -- Sylow `r`-subgroup of `H`, pushed to `G`
    obtain ⟨QH⟩ := Sylow.nonempty (p := r) (G := ↥H)
    have hQHne : (QH : Subgroup ↥H) ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥QH = 1 := Subgroup.card_eq_one.mpr hbot
      have h2 : Nat.card ↥QH = r ^ (Nat.card ↥H).factorization r :=
        Sylow.card_eq_multiplicity QH
      have h3 : 0 < (Nat.card ↥H).factorization r :=
        hrp.factorization_pos_of_dvd (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩).ne' hrH
      rw [h1] at h2
      have h4 : 1 < r ^ (Nat.card ↥H).factorization r := by
        have h5 := Nat.pow_lt_pow_right hrp.one_lt h3
        simpa using h5
      omega
    obtain ⟨Q', hQ'⟩ :=
      sylowMapOfNotDvdIndex (G := G) (H := H) (r := r) hrIdx QH
    have hQ'ne : (Q' : Subgroup G) ≠ ⊥ := by
      rw [hQ']
      intro hbot
      have h1 : Subgroup.map H.subtype QH = Subgroup.map H.subtype ⊥ := by
        rw [hbot]; simp
      exact hQHne (Subgroup.map_injective H.subtype_injective h1)
    have hQ'T : (Q' : Subgroup G) ≤ T := by
      rw [hQ']
      exact le_trans (Subgroup.map_subtype_le (H := H) QH) hHT
    have hQ'pair : (Q' : Subgroup G) ≤ Work.Zassenhaus.pairStab G a b := by
      rw [hQ']
      exact le_trans (Subgroup.map_subtype_le (H := H) QH) (show H ≤ Work.Zassenhaus.pairStab G a b from by rw [hHdef])
    have hNQT : Subgroup.normalizer ((Q' : Subgroup G) : Set G) ≤ T :=
      Work.ZASS.normalizer_le_normalizer_pairStab (q := p ^ k) h hab hq hQ'pair hQ'ne
    have hrdvd : r ∣ (commutator ↥T).index := by
      have hidx : (commutator ↥T).index = m * H'.index := (Subgroup.relIndex_mul_index hT'leH').symm
      rw [hidx]
      exact dvd_mul_of_dvd_left hrdvdm _
    exact burnside_aux hZT hr2 hrdvd hnr Q' hQ'ne hQ'T hNQT
  ---------------------------------------------------------------------------------------------
  -- ## `T' = H'` and `H` is cyclic
  ---------------------------------------------------------------------------------------------
  have hcardTf' : Nat.card ↥H' = Nat.card ↥Tf := by
    rw [← hm, hm1, one_mul]
  have hT'eq : Tf = H' :=
    Subgroup.eq_of_le_of_card_ge hT'leH' (le_of_eq hcardTf')
  have hcycTf : IsCyclic ↥Tf := by
    rw [hTfdef]
    exact IsZGroup.isCyclic_commutator ↥T
  have hcycH' : IsCyclic ↥H' := by rw [← hT'eq]; exact hcycTf
  have hcycH : IsCyclic ↥H :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hHT)).mp hcycH'
  ---------------------------------------------------------------------------------------------
  -- ## Conclusion
  ---------------------------------------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · rw [← hHK]; exact hcycH
  · intro s hsa hsb
    rw [← hHK]
    have hsT : s ∈ T := by
      show s ∈ Subgroup.normalizer (H : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h2 := Work.ZASS.conjBy_mem_pairStab hsa hsb hx
        show s * x * s⁻¹ ∈ H
        rwa [Work.ZASS.conjBy] at h2
      · intro hx
        have hia : s⁻¹ • a = b := by rw [← hsb, inv_smul_smul]
        have hib : s⁻¹ • b = a := by rw [← hsa, inv_smul_smul]
        have h2 : Work.ZASS.conjBy s⁻¹ (s * x * s⁻¹) ∈ Work.Zassenhaus.pairStab G a b :=
          Work.ZASS.conjBy_mem_pairStab hia hib hx
        have h3 : Work.ZASS.conjBy s⁻¹ (s * x * s⁻¹) = x := by
          rw [Work.ZASS.conjBy]; group
        show x ∈ H
        rwa [h3] at h2
    have hsH : s ∉ H := by
      intro hmem
      have h1 : s • a = a := (Work.Zassenhaus.mem_pairStab_iff.mp hmem).2
      rw [hsa] at h1
      exact hab h1.symm
    have hs2 : s * s ∈ H := by
      refine Work.Zassenhaus.mem_pairStab_iff.mpr ⟨?_, ?_⟩
      · show (s * s) • b = b
        rw [mul_smul, hsb, hsa]
      · show (s * s) • a = a
        rw [mul_smul, hsa, hsb]
    have hσH' : (⟨s, hsT⟩ : ↥T) ∉ H' := fun hmem =>
      hsH (Subgroup.mem_subgroupOf.mp hmem)
    have hσ2' : (⟨s, hsT⟩ : ↥T) * ⟨s, hsT⟩ ∈ H' := Subgroup.mem_subgroupOf.mpr hs2
    have hTop : H' ⊔ Subgroup.zpowers (⟨s, hsT⟩ : ↥T) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      by_cases hy : y ∈ H'
      · exact Subgroup.mem_sup_left hy
      · have hcard : Nat.card (↥T ⧸ H') ≤ 2 := by
          rw [← Subgroup.index_eq_card]; omega
        have hmk : ∀ z : ↥T, QuotientGroup.mk' H' z = 1 → z ∈ H' := fun z hz => by
          rw [← QuotientGroup.ker_mk' H']
          exact MonoidHom.mem_ker.mpr hz
        have hq : QuotientGroup.mk' H' y ≠ 1 := fun hcon => hy (hmk y hcon)
        have hqσ : QuotientGroup.mk' H' (⟨s, hsT⟩ : ↥T) ≠ 1 := fun hcon =>
          hσH' (hmk _ hcon)
        have heq : QuotientGroup.mk' H' y = QuotientGroup.mk' H' ⟨s, hsT⟩ :=
          eqOfNeOneOfCardLeTwo hcard hq hqσ
        have hyH : y * (⟨s, hsT⟩ : ↥T)⁻¹ ∈ H' := by
          refine hmk _ ?_
          rw [map_mul, map_inv, heq, mul_inv_cancel]
        have heq2 : y = (y * (⟨s, hsT⟩ : ↥T)⁻¹) * ⟨s, hsT⟩ := by group
        rw [heq2]
        exact Subgroup.mul_mem (H' ⊔ Subgroup.zpowers (⟨s, hsT⟩ : ↥T))
          (Subgroup.mem_sup_left hyH)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers (⟨s, hsT⟩ : ↥T)))
    have key := (conj_inverts_aux hT'eq hZT ⟨s, hsT⟩ hσH' hσ2' hTop).2
    intro x hx
    have hx' : (⟨x, hHT hx⟩ : ↥T) ∈ H' := Subgroup.mem_subgroupOf.mpr hx
    have hkey := key ⟨x, hHT hx⟩ hx'
    have hkey2 := congrArg (fun z : ↥T => (z : G)) hkey
    simpa using hkey2

end Work.ZASS2
