import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson

/-- Arithmetic half of the Dickson argument: if `n` is odd, `n ∣ r - 1` and `r ^ 2 = 8 * n + 1`
with `r ≥ 2`, then `n = 1`. -/
private lemma arith_eight_mul {n r : ℕ} (hdvd : n ∣ r - 1) (hr : 2 ≤ r) (h : r ^ 2 = 8 * n + 1)
    (hodd : Odd n) : n = 1 := by
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨j, hj⟩ := hodd
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hk
    omega
  -- Over `ℤ`: from `r - 1 = n * k` and `r ^ 2 = 8 * n + 1` deduce `k * (r + 1) = 8`.
  have hkey : (k : ℤ) * ((r : ℤ) + 1) = 8 := by
    have hZ : (r : ℤ) ^ 2 = 8 * (n : ℤ) + 1 := by exact_mod_cast h
    have h1 : ((r : ℤ) - 1) * ((r : ℤ) + 1) = 8 * (n : ℤ) := by nlinarith
    have h2 : ((r : ℤ) - 1) = (n : ℤ) * k := by omega
    rw [h2] at h1
    have : (n : ℤ) * ((k : ℤ) * ((r : ℤ) + 1)) = (n : ℤ) * 8 := by nlinarith
    exact mul_left_cancel₀ (by exact_mod_cast hn0) this
  have hk1 : (1 : ℤ) ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      rw [hk0] at hk
      omega
    · exact_mod_cast hkpos
  have hr7 : r ≤ 7 := by
    have : ((r : ℤ) + 1) ≤ 8 := by nlinarith
    omega
  interval_cases r <;> omega

/-- **B1** (App. XI Prop. 2, arithmetic half; pure field theory). A finite field `K` with an
involutive automorphism `σ ≠ 1` whose unit group has an odd-order `σ`-fixed subgroup `C` with
`|K| = 8|C| + 1` has `|C| = 1`.

Route. `|K| = |K^σ|²` by Artin's lemma (`FixedPoints.finrank_eq_card` applied to
`G = Subgroup.zpowers σ ≤ (K ≃+* K)`, which acts faithfully on `K` because `σ ≠ 1`; the action of
`K ≃+* K` on `K` is `MulSemiringAction`); put `r = Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) K)`,
so `Nat.card K = r ^ 2` by `Module.card_eq_pow_finrank`.  `C ≤ Kˣ` consists of `σ`-fixed points
(`hCfix`), so `C` is a subgroup of `(K^σ)ˣ` and `Nat.card C ∣ r - 1` (Lagrange +
`Fintype.card_units`, `Nat.card` vs `Fintype.card` via `Nat.card_eq_fintype_card`).  Write
`r - 1 = (Nat.card C) * k`; then `r² - 1 = 8 · Nat.card C` gives `k * (r + 1) = 8`, so
`r + 1 ∈ {4, 8}`, `r ∈ {3, 7}` (note `r ≥ 2`; `r = 1` would make `σ` the identity).  `r = 7` gives
`Nat.card C = 6`, contradicting `Odd (Nat.card C)`; hence `r = 3` and `Nat.card C = 1`. -/
theorem card_eq_one_of_dickson {K : Type} [Field K] [Fintype K] (σ : K ≃+* K)
    (hσ1 : σ ≠ RingEquiv.refl K) (hσ2 : ∀ k, σ (σ k) = k) (C : Subgroup Kˣ)
    (hCodd : Odd (Nat.card C)) (hCfix : ∀ c ∈ C, σ (c : K) = c)
    (hcard : Fintype.card K = 8 * Nat.card C + 1) : Nat.card C = 1 := by
  classical
  have hKft : Fintype (K ≃+* K) :=
    Fintype.ofInjective (fun e : K ≃+* K => (e : K → K))
      (fun a b h => RingEquiv.ext fun x => congrFun h x)
  -- the fixed field of `⟨σ⟩`
  let F : Subfield K := FixedPoints.subfield ↥(Subgroup.zpowers σ) K
  -- `σ` has order `2`
  have hord : orderOf σ = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      ext x
      exact hσ2 x
    · exact hσ1
  -- the action of `⟨σ⟩` on `K` is faithful, since `σ ≠ 1`
  have hfaith : FaithfulSMul ↥(Subgroup.zpowers σ) K := by
    rw [faithfulSMul_iff]
    intro g hg
    exact Subtype.ext (RingEquiv.ext fun x => hg x)
  -- Artin's lemma: `[K : K^σ] = 2`
  have hfr : Module.finrank F K = 2 := by
    change Module.finrank ↥(FixedPoints.subfield ↥(Subgroup.zpowers σ) K) K = 2
    rw [FixedPoints.finrank_eq_card, Fintype.card_zpowers, hord]
  -- hence `|K| = |K^σ| ^ 2`
  have hK : Nat.card K = Nat.card F ^ 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Module.card_eq_pow_finrank (K := F) (V := K), hfr]
  -- `C` consists of elements of the fixed field, hence is a subgroup of `Fˣ`,
  -- so `|C|` divides `|Fˣ| = |F| - 1`
  have hmem : ∀ c : C, ((c : Kˣ) : K) ∈ F := by
    intro c
    have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) ((c : Kˣ) : K) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (hCfix c c.2))
    intro g
    exact (MulAction.mem_stabilizer_iff.mp (hstab g.2))
  have hne : ∀ c : C, (⟨((c : Kˣ) : K), hmem c⟩ : F) ≠ 0 := by
    intro c h
    exact Units.ne_zero (c : Kˣ) (by simpa using congrArg Subtype.val h)
  let phi : C →* Fˣ :=
    { toFun := fun c => Units.mk0 ⟨((c : Kˣ) : K), hmem c⟩ (hne c)
      map_one' := by
        apply Units.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Units.ext
        apply Subtype.ext
        simp }
  have hinj : Function.Injective phi := by
    intro a b hab
    have h2 : (⟨((a : Kˣ) : K), hmem a⟩ : F) = ⟨((b : Kˣ) : K), hmem b⟩ :=
      (Units.mk0_inj (hne a) (hne b)).mp hab
    have h3 : ((a : Kˣ) : K) = ((b : Kˣ) : K) := congrArg Subtype.val h2
    exact Subtype.ext (Units.ext h3)
  have hdvd : Nat.card C ∣ Nat.card F - 1 := by
    have h1 : Nat.card Fˣ = Nat.card F - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
    have h2 : Nat.card C ∣ Nat.card Fˣ := Subgroup.card_dvd_of_injective phi hinj
    rwa [h1] at h2
  -- `|F| ≥ 2`
  have hr2 : 2 ≤ Nat.card F := by
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  -- `|F| ^ 2 = 8 * |C| + 1`
  have hmain : Nat.card F ^ 2 = 8 * Nat.card C + 1 := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact hcard
  exact arith_eight_mul hdvd hr2 hmain hCodd

end Work.AppXIDickson
