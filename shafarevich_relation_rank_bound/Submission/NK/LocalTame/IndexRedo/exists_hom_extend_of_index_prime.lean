import Mathlib

namespace NK.LocalTame.IndexRedo

/-- Conjugation of an element of a normal subgroup by an ambient element. -/
private def conjBy {G : Type*} [Group G] {M : Subgroup G} [hM : M.Normal] (x : G) (m : ↥M) : ↥M :=
  ⟨x * (m : G) * x⁻¹, hM.conj_mem (m : G) m.2 x⟩

private lemma conjBy_one {G : Type*} [Group G] {M : Subgroup G} [hM : M.Normal] (m : ↥M) :
    conjBy (M := M) 1 m = m := by
  apply Subtype.ext; simp [conjBy]

private lemma conjBy_mul {G : Type*} [Group G] {M : Subgroup G} [hM : M.Normal]
    (x y : G) (m : ↥M) :
    conjBy (M := M) (x * y) m = conjBy (M := M) x (conjBy (M := M) y m) := by
  apply Subtype.ext
  simp only [conjBy]
  group

private lemma conjBy_mul_inv {G : Type*} [Group G] {M : Subgroup G} [hM : M.Normal]
    (x : G) (m : ↥M) : conjBy (M := M) x (conjBy (M := M) x⁻¹ m) = m := by
  apply Subtype.ext
  simp only [conjBy]
  group

/-- **Extension of a character from a normal subgroup of prime index.**

Let `M ⊴ G` be a normal subgroup of prime index `ℓ`, let `g ∉ M` and let
`χ : M →* Multiplicative (ZMod ℓ)` be invariant under conjugation by `g` and satisfy
`χ (g ^ [G : M]) = 1`.  Then `χ` extends to a homomorphism `G →* Multiplicative (ZMod ℓ)`.

The proof writes every `x : G` as `x = g ^ k · m` with `m ∈ M` (possible because `G/M` is
cyclic of order `ℓ`), and sets `ψ x = χ m`.  Normality and the invariance of `χ` under
powers of `g` make `ψ` multiplicative, while `χ (g ^ ℓ) = 1` makes it well defined. -/
theorem exists_hom_extend_of_index_prime {G : Type*} [Group G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (M : Subgroup G) [hM : M.Normal] (hMi : M.index = ℓ) (g : G) (hg : g ∉ M)
    (χ : ↥M →* Multiplicative (ZMod ℓ))
    (hinv : ∀ m : ↥M, χ ⟨g * (m : G) * g⁻¹, hM.conj_mem (m : G) m.2 g⟩ = χ m)
    (hpow : χ ⟨g ^ M.index, Subgroup.pow_index_mem M g⟩ = 1) :
    ∃ ψ : G →* Multiplicative (ZMod ℓ), ψ.comp M.subtype = χ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard : Nat.card (G ⧸ M) = ℓ := by
    rw [← Subgroup.index_eq_card]; exact hMi
  have hγne : (QuotientGroup.mk' M) g ≠ 1 := by
    intro h
    exact hg ((QuotientGroup.eq_one_iff g).mp h)
  -- every element of the quotient is a power of the class of `g`
  have hex : ∀ x : G, ∃ k : ℤ, ((QuotientGroup.mk' M) g) ^ k = (QuotientGroup.mk' M) x := by
    intro x
    have h := mem_zpowers_of_prime_card (G := G ⧸ M) hcard hγne (g := (QuotientGroup.mk' M) g)
      (g' := (QuotientGroup.mk' M) x)
    rwa [Subgroup.mem_zpowers_iff] at h
  let kx : G → ℤ := fun x => Classical.choose (hex x)
  have hkx : ∀ x : G, ((QuotientGroup.mk' M) g) ^ (kx x) = (QuotientGroup.mk' M) x :=
    fun x => Classical.choose_spec (hex x)
  have hγpow : ((QuotientGroup.mk' M) g) ^ ℓ = 1 := by
    rw [← map_pow]
    show ((g ^ ℓ : G) : G ⧸ M) = 1
    rw [QuotientGroup.eq_one_iff]
    have h := Subgroup.pow_index_mem M g
    rwa [hMi] at h
  have horder : orderOf ((QuotientGroup.mk' M) g) = ℓ := by
    have hdvd : orderOf ((QuotientGroup.mk' M) g) ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr hγpow
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | hp
    · exact absurd (orderOf_eq_one_iff.mp h1) hγne
    · exact hp
  -- the class of `g` detects exponents modulo `ℓ`
  have hdvd_of_eq : ∀ a b : ℤ, ((QuotientGroup.mk' M) g) ^ a = ((QuotientGroup.mk' M) g) ^ b →
      (ℓ : ℤ) ∣ (a - b) := by
    intro a b hab
    have h1 : ((QuotientGroup.mk' M) g) ^ (a - b) = 1 := by
      rw [zpow_sub, hab, mul_inv_cancel]
    have h2 : (orderOf ((QuotientGroup.mk' M) g) : ℤ) ∣ (a - b) :=
      orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [horder] at h2
  -- the subgroup of elements conjugating `χ` to itself
  let K : Subgroup G :=
    { carrier := {x : G | ∀ m : ↥M, χ (conjBy (M := M) x m) = χ m}
      one_mem' := by
        intro m
        rw [conjBy_one]
      mul_mem' := by
        intro x y hx hy m
        rw [conjBy_mul]
        exact (hx (conjBy (M := M) y m)).trans (hy m)
      inv_mem' := by
        intro x hx m
        have h1 := hx (conjBy (M := M) x⁻¹ m)
        rw [conjBy_mul_inv] at h1
        exact h1.symm }
  have hgK : g ∈ K := by intro m; exact hinv m
  have hinv_zpow : ∀ (j : ℤ) (m : ↥M), χ (conjBy (M := M) (g ^ j) m) = χ m :=
    fun j m => K.zpow_mem hgK j m
  have hgle_mem : g ^ ((ℓ : ℤ)) ∈ M := by
    rw [zpow_natCast]
    have h := Subgroup.pow_index_mem M g
    rwa [hMi] at h
  have hpowℓ : χ ⟨g ^ ((ℓ : ℤ)), hgle_mem⟩ = 1 := by
    have h2 : (⟨g ^ ((ℓ : ℤ)), hgle_mem⟩ : ↥M) = ⟨g ^ M.index, Subgroup.pow_index_mem M g⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mk]
      rw [zpow_natCast, hMi]
    rw [h2]; exact hpow
  have hpow_chi : ∀ c : ℤ, χ (⟨g ^ ((ℓ : ℤ)), hgle_mem⟩ ^ c) = 1 := by
    intro c; rw [map_zpow, hpowℓ, one_zpow]
  -- the `M`-component of `x` with respect to the exponent `kx x`
  have hmem : ∀ x : G, g ^ (-(kx x)) * x ∈ M := by
    intro x
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' M) (g ^ (-(kx x)) * x) = 1
    rw [map_mul, map_zpow, zpow_neg, hkx x, inv_mul_cancel]
  -- changing the exponent by a multiple of `ℓ` does not change the value of `χ`
  have hkey : ∀ (a b : ℤ) (y : G) (hb : g ^ b * y ∈ M) (ha : g ^ a * y ∈ M),
      (ℓ : ℤ) ∣ (a - b) → χ ⟨g ^ a * y, ha⟩ = χ ⟨g ^ b * y, hb⟩ := by
    intro a b y hb ha hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hEq : (⟨g ^ a * y, ha⟩ : ↥M) = ⟨g ^ ((ℓ : ℤ)), hgle_mem⟩ ^ c * ⟨g ^ b * y, hb⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      rw [← zpow_mul, ← hc, zpow_sub]
      group
    rw [hEq, map_mul, hpow_chi c, one_mul]
  let φ : G → Multiplicative (ZMod ℓ) := fun x => χ ⟨g ^ (-(kx x)) * x, hmem x⟩
  have hφmul : ∀ x y : G, φ (x * y) = φ x * φ y := by
    intro x y
    have hdiv : (ℓ : ℤ) ∣ (kx (x * y) - (kx x + kx y)) := by
      apply hdvd_of_eq
      rw [hkx (x*y), zpow_add, hkx x, hkx y, ← map_mul]
    have hdiv' : (ℓ : ℤ) ∣ (-(kx (x*y)) - (-(kx x + kx y))) := by
      rw [show (-(kx (x*y)) - (-(kx x + kx y))) = -(kx (x*y) - (kx x + kx y)) by ring]
      exact dvd_neg.mpr hdiv
    have hky : g ^ (-(kx x + kx y)) * (x * y) ∈ M := by
      have hEq : g ^ (-(kx x + kx y)) * (x * y)
          = (↑(conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩) : G)
            * (↑((⟨g ^ (-(kx y)) * y, hmem y⟩ : ↥M)) : G) := by
        rw [show (↑(conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩) : G)
            = g ^ (-(kx y)) * (g ^ (-(kx x)) * x) * (g ^ (-(kx y)))⁻¹ from rfl]
        rw [show ((⟨g ^ (-(kx y)) * y, hmem y⟩ : ↥M) : G) = g ^ (-(kx y)) * y from rfl]
        group
      rw [hEq]
      exact Subgroup.mul_mem M
        (conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩).2 (hmem y)
    calc φ (x * y)
        = χ ⟨g ^ (-(kx (x*y))) * (x * y), hmem (x * y)⟩ := rfl
      _ = χ ⟨g ^ (-(kx x + kx y)) * (x * y), hky⟩ := hkey _ _ _ hky (hmem (x*y)) hdiv'
      _ = χ (conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩
              * ⟨g ^ (-(kx y)) * y, hmem y⟩) := by
            congr 1
            apply Subtype.ext
            rw [Subgroup.coe_mk, Subgroup.coe_mul]
            rw [show (↑(conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩) : G)
                = g ^ (-(kx y)) * (g ^ (-(kx x)) * x) * (g ^ (-(kx y)))⁻¹ from rfl]
            rw [show ((⟨g ^ (-(kx y)) * y, hmem y⟩ : ↥M) : G) = g ^ (-(kx y)) * y from rfl]
            group
      _ = χ (conjBy (M := M) (g ^ (-(kx y))) ⟨g ^ (-(kx x)) * x, hmem x⟩)
              * χ ⟨g ^ (-(kx y)) * y, hmem y⟩ := map_mul χ _ _
      _ = χ ⟨g ^ (-(kx x)) * x, hmem x⟩ * χ ⟨g ^ (-(kx y)) * y, hmem y⟩ := by
            rw [hinv_zpow (-(kx y)) ⟨g ^ (-(kx x)) * x, hmem x⟩]
      _ = φ x * φ y := rfl
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := hφmul }, ?_⟩
  · have h := hφmul 1 1
    rw [mul_one] at h
    exact (mul_left_cancel (by rw [mul_one]; exact h)).symm
  · ext m
    have hb0 : g ^ (0:ℤ) * (m:G) ∈ M := by rw [zpow_zero, one_mul]; exact m.2
    have hdvdm : (ℓ : ℤ) ∣ (-(kx (m:G)) - 0) := by
      have h0 : ((QuotientGroup.mk' M) g) ^ (kx (m:G)) = ((QuotientGroup.mk' M) g) ^ (0:ℤ) := by
        rw [hkx (m:G), zpow_zero, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq_one_iff]
        exact m.2
      have h1 : (ℓ : ℤ) ∣ kx (m:G) := by
        have := hdvd_of_eq _ _ h0
        simpa using this
      simpa using dvd_neg.mpr h1
    have hone : (⟨g ^ (0:ℤ) * (m:G), hb0⟩ : ↥M) = m := by
      apply Subtype.ext; simp
    show χ ⟨g ^ (-(kx (m:G))) * (m:G), hmem (m:G)⟩ = χ m
    rw [hkey (-(kx (m:G))) 0 (m:G) hb0 (hmem (m:G)) hdvdm, hone]

end NK.LocalTame.IndexRedo
