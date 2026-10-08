import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27v12_twopart_mem_pCoreIn_Hhat

/-!
# GW design pass 18, item A, leaf A1: scalar action normalizes every subgroup of `F(U)`

If `s` acts on every `O_p(U)` either trivially or by inversion (`hact`), then `s` normalizes every
subgroup `X ≤ F(U)`.

Strategy.  For an element `x` of a finite group and coprime `A B` with `orderOf x ∣ A * B`, Bézout
splits `x = y * z` with `y, z` powers of `x`, `y ^ A = 1` and `z ^ B = 1`
(`c18_zpow_split`).  Running this along `Nat.recOnPrimePow` peels the prime-power factors of
`orderOf x` one at a time (`c18_conj_mem_zpowers`): the `p`-power part `y` is a `p`-element of
`F(U)`, hence lies in `O_p(U) = pCoreIn p U`, so `hact` conjugates it to `y^{±1}`; the rest `z` is
handled inductively; and since both are powers of `x`, the product `s x s⁻¹` is a power of `x`.
This gives `s x s⁻¹ ∈ ⟨x⟩` for every `x ∈ F(U)`, whence `s ∈ N_G(X)` for every `X ≤ F(U)`
(the same argument applied to `s⁻¹` supplies the reverse inclusion, or finiteness does).
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Bézout splitting of an element of a finite group into two coprime parts.**

If `Nat.Coprime A B` and `orderOf x ∣ A * B`, then `x` is the product of two powers `y`, `z` of
`x` with `y ^ A = 1` and `z ^ B = 1`.  (`y` is the `A`-part and `z` the `B`-part of `x`.) -/
theorem c18_zpow_split {G : Type} [Group G] (x : G) {A B : ℕ} (hc : Nat.Coprime A B)
    (hd : orderOf x ∣ A * B) :
    ∃ y z : G, y ∈ Subgroup.zpowers x ∧ z ∈ Subgroup.zpowers x ∧ y * z = x ∧
      y ^ A = 1 ∧ z ^ B = 1 := by
  -- integer Bézout coefficients for the coprime pair `(A, B)`
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (A : ℤ) * u + (B : ℤ) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab A B
    rw [hc.gcd_eq_one] at h
    exact ⟨A.gcdA B, A.gcdB B, h.symm⟩
  -- `x ^ (A * B) = 1`, so every `(A * B)`-multiple of the exponent of `x` is trivial
  have hxN : ∀ w : ℤ, x ^ (((A * B : ℕ) : ℤ) * w) = 1 := by
    intro w
    obtain ⟨c, hc'⟩ := hd
    have hcast : ((A * B : ℕ) : ℤ) = (orderOf x : ℤ) * (c : ℤ) := by
      rw [hc']; push_cast; ring
    have hre : (((A*B:ℕ):ℤ) * w) = (orderOf x : ℤ) * ((c:ℤ) * w) := by
      rw [hcast]; ring
    rw [hre, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨x ^ ((B : ℤ) * v), x ^ ((A : ℤ) * u), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_zpowers_iff]; exact ⟨(B:ℤ)*v, rfl⟩
  · rw [Subgroup.mem_zpowers_iff]; exact ⟨(A:ℤ)*u, rfl⟩
  · rw [← zpow_add]
    have h1 : (B:ℤ)*v + (A:ℤ)*u = 1 := by linarith [huv]
    rw [h1, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have he : (B:ℤ) * v * (A:ℤ) = ((A*B:ℕ):ℤ) * v := by push_cast; ring
    rw [he, hxN v]
  · rw [← zpow_natCast, ← zpow_mul]
    have he : (A:ℤ) * u * (B:ℤ) = ((A*B:ℕ):ℤ) * u := by push_cast; ring
    rw [he, hxN u]

/-- **Key claim.**  If `t` acts on each `O_p(U) = pCoreIn p U` either trivially or by inversion,
then `t` conjugates every element `x` of `F(U) = fittingIn U` to a power of `x`.

The induction is on the integer `m` with `orderOf x ∣ m`, using `Nat.recOnPrimePow` to peel off
prime-power factors: `m = p ^ n * a` with `p ∤ a`, `c18_zpow_split` writes `x = y * z` with
`y ^ (p ^ n) = 1` (so `y` is a `p`-element, hence `y ∈ pCoreIn p U`) and `z ^ a = 1`
(so `orderOf z ∣ a`, handled by the induction hypothesis); then
`t * x * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹)` is a product of two powers of `x`. -/
theorem c18_conj_mem_zpowers {G : Type} [Group G] [Finite G] (U : Subgroup G) (t : G)
    (hact : ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p U, t * z * t⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p U, t * z * t⁻¹ = z⁻¹)) :
    ∀ x ∈ Work.GW2.fittingIn U, t * x * t⁻¹ ∈ Subgroup.zpowers x := by
  intro x hx
  have key := Nat.recOnPrimePow
    (motive := fun m => 0 < m → ∀ x ∈ Work.GW2.fittingIn U,
      orderOf x ∣ m → t * x * t⁻¹ ∈ Subgroup.zpowers x)
    -- `m = 0` is excluded by `0 < m`
    (fun h => absurd h (lt_irrefl 0))
    -- `m = 1`: `orderOf x = 1`, so `x = 1`
    (fun _ x _ hdvd => by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨0, by rw [orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)]; simp⟩)
    -- `m = p ^ n * a` with `p ∤ a`: split off the `p`-part
    (fun a p n hp hpa _ ih _ x hx hdvd => by
      haveI : Fact p.Prime := ⟨hp⟩
      have ha_pos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hpa (dvd_zero p))
      have hc : Nat.Coprime (p ^ n) a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left n
      obtain ⟨y, z, hy_mem, hz_mem, hyz, hyA, hzB⟩ := c18_zpow_split x hc hdvd
      -- `z ∈ F(U)` and `orderOf z ∣ a`, so the induction hypothesis applies
      have hzF : z ∈ Work.GW2.fittingIn U := (Subgroup.zpowers_le.mpr hx) hz_mem
      have hzdiv : orderOf z ∣ a := orderOf_dvd_iff_pow_eq_one.mpr hzB
      have hzin : t * z * t⁻¹ ∈ Subgroup.zpowers x :=
        (Subgroup.zpowers_le.mpr hz_mem) (ih ha_pos z hzF hzdiv)
      -- `y` is a `p`-element of `F(U)`, hence lies in `pCoreIn p U`, on which `hact` acts
      have hyq : IsPGroup p ↥(Subgroup.zpowers y) := by
        have hdvd' : orderOf y ∣ p ^ n := orderOf_dvd_iff_pow_eq_one.mpr hyA
        obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
        exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
      have hypc : y ∈ Work.GW2.pCoreIn p U :=
        L27v12_pCoreIn_of_mem_fittingIn_of_isPGroup_zpowers U p
          (Subgroup.zpowers_le.mpr hx hy_mem) hyq
      have hyin : t * y * t⁻¹ ∈ Subgroup.zpowers x := by
        apply Subgroup.zpowers_le.mpr hy_mem
        rcases hact p hp with hcent | hinv
        · rw [hcent y hypc]; exact Subgroup.mem_zpowers y
        · rw [hinv y hypc]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
      -- conjugation is multiplicative on the product `x = y * z`
      have hh : t * x * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by
        rw [← hyz]; group
      rw [hh]
      exact Subgroup.mul_mem _ hyin hzin)
    (orderOf x)
  exact key (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)) x hx dvd_rfl

-- GW design pass 18, item A, leaf A1 (statement copied from `Core18ScalarActionNormalizes.lean`):
-- if `s` acts on every `O_p(U)` trivially or by inversion (hypothesis `hact`), then `s` normalizes
-- every subgroup `X ≤ F(U)`.
theorem C18ScalarActionNormalizes_proved {G : Type} [Group G] [Finite G] (U : Subgroup G) (s : G)
    (hact : ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹))
    (X : Subgroup G) (hX : X ≤ Work.GW2.fittingIn U) :
    s ∈ Subgroup.normalizer (X : Set G) := by
  -- the same dichotomy holds for `s⁻¹` (inversion/centralization are preserved under inversion)
  have hact_inv0 : ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p U, s⁻¹ * z * s = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p U, s⁻¹ * z * s = z⁻¹) := by
    intro p hp
    rcases hact p hp with hc | hi
    · left; intro z hz
      have h := hc z hz
      calc s⁻¹ * z * s = s⁻¹ * (s * z * s⁻¹) * s := by rw [h]
        _ = z := by group
    · right; intro z hz
      have h := hi z hz
      have hz1 : z = s⁻¹ * z⁻¹ * s := by
        calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
          _ = s⁻¹ * z⁻¹ * s := by rw [h]
      have hinv : z⁻¹ = (s⁻¹ * z⁻¹ * s)⁻¹ := by conv_lhs => rw [hz1]
      calc s⁻¹ * z * s = (s⁻¹ * z⁻¹ * s)⁻¹ := by group
        _ = z⁻¹ := hinv.symm
  have hact_inv : ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p U, s⁻¹ * z * (s⁻¹)⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p U, s⁻¹ * z * (s⁻¹)⁻¹ = z⁻¹) := by
    intro p hp
    simpa only [inv_inv] using hact_inv0 p hp
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · -- forward: `h ∈ X ⟹ s * h * s⁻¹ ∈ X`
    intro hh
    exact (Subgroup.zpowers_le.mpr hh) (c18_conj_mem_zpowers U s hact h (hX hh))
  · -- reverse: `s * h * s⁻¹ ∈ X ⟹ h ∈ X`, using the same claim for `s⁻¹`
    intro hh
    have hw : s * h * s⁻¹ ∈ Work.GW2.fittingIn U := hX hh
    have hmem :=
      (Subgroup.zpowers_le.mpr hh) (c18_conj_mem_zpowers U s⁻¹ hact_inv (s * h * s⁻¹) hw)
    have hh' : s⁻¹ * (s * h * s⁻¹) * (s⁻¹)⁻¹ = h := by group
    rwa [hh'] at hmem

end Work.CORE2B
