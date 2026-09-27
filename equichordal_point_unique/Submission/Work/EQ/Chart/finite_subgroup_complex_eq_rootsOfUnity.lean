import Mathlib

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.EQ.Chart

/-- **A finite subgroup of `ℂˣ` is a group of roots of unity.**

If `S ⊆ ℂ` contains `1`, is closed under multiplication and inversion, is finite, and consists of
`k`-th roots of unity (`k ≥ 1`), then `S = μ_d` for `d = |S|`: there is a generator `ω ∈ S` which
is a primitive `d`-th root of unity (`ω ^ d = 1`, `ω ^ m ≠ 1` for `0 < m < d`), and `d ∣ k`.

Route: `S` is a finite subgroup of `ℂˣ` (`0 ∉ S` since `0 ^ k = 0 ≠ 1`); it is cyclic because
`#{a ∈ S | aⁿ = 1} ≤ n` (a nonzero polynomial of degree `n` has ≤ `n` roots), via
`isCyclic_of_card_pow_eq_one_le`. A generator `g` with `orderOf g = Nat.card S` gives
`ω := g : ℂ`, and `S ⊆ μ_d` (every element of `S` is a power of `g`), while `|μ_d| = d`
(`Complex.exp (2 * π * I / d)` is a primitive `d`-th root of unity, `Complex.isPrimitiveRoot_exp`,
and `Nat.card (rootsOfUnity d ℂ) ≤ d`). -/
theorem finite_subgroup_complex_eq_rootsOfUnity {k : ℕ} (hk : 1 ≤ k) {S : Set ℂ}
    (h1 : (1 : ℂ) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hkS : ∀ a ∈ S, a ^ k = 1) (hfin : S.Finite) :
    ∃ (d : ℕ) (ω : ℂ), 0 < d ∧ d ∣ k ∧ ω ∈ S ∧ ω ^ d = 1 ∧
      (∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1) ∧ (∀ u : ℂ, u ∈ S ↔ u ^ d = 1) := by
  classical
  -- `0` is not in `S`, since `0 ^ k = 1` would force `0 = 1`.
  have h0S : (0 : ℂ) ∉ S := by
    intro h
    have hz := hkS 0 h
    rw [zero_pow (by omega : k ≠ 0)] at hz
    exact one_ne_zero hz.symm
  -- `S` is the carrier of a finite subgroup `G` of `ℂˣ`.
  let G : Subgroup ℂˣ :=
    { carrier := {x | (x : ℂ) ∈ S}
      mul_mem' := by intro a b ha hb; exact hmul (a : ℂ) ha (b : ℂ) hb
      one_mem' := h1
      inv_mem' := by intro a ha; simpa using hinv (a : ℂ) ha }
  haveI : Finite ↥G := by
    have hpre : ((fun x : ℂˣ => (x : ℂ)) ⁻¹' S).Finite :=
      Set.Finite.preimage (fun a _ b _ h => Units.ext h) hfin
    exact hpre.to_subtype
  haveI : IsCyclic ↥G := isCyclic_subgroup_units G
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  haveI : Nonempty ↥G := ⟨1⟩
  -- the composite `G → ℂˣ → ℂ`, which is injective.
  let φ : ↥G →* ℂ := (Units.coeHom ℂ).comp (Subgroup.subtype G)
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥G)
  have hφg : φ g = ((g : ℂˣ) : ℂ) := rfl
  have hgS : ((g : ℂˣ) : ℂ) ∈ S := g.2
  refine ⟨Nat.card ↥G, ((g : ℂˣ) : ℂ), Nat.card_pos, ?_, hgS, ?_, ?_, ?_⟩
  · -- `d = orderOf g` divides `k`, because `g ^ k = 1`.
    rw [← hg]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply hφinj
    rw [map_pow, hφg, map_one]
    exact hkS ((g : ℂˣ) : ℂ) hgS
  · -- `ω ^ d = 1`.
    have hgd : g ^ (Nat.card ↥G) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hh := congrArg φ hgd
    rwa [map_pow, hφg, map_one] at hh
  · -- `ω` is a *primitive* `d`-th root of unity.
    intro m hm hmd hgm
    have hgm' : g ^ m = 1 := by
      apply hφinj
      rw [map_pow, hφg, map_one]
      exact hgm
    have hdiv : orderOf g ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hgm'
    rw [hg] at hdiv
    have hle : Nat.card ↥G ≤ m := Nat.le_of_dvd hm hdiv
    omega
  · -- `S = μ_d`.
    intro u
    constructor
    · -- `u ∈ S → u ^ d = 1`, by Lagrange in the finite group `G`.
      intro hu
      have hu0 : u ≠ 0 := fun h => h0S (h ▸ hu)
      let u' : ℂˣ := Units.mk0 u hu0
      have hu'val : (u' : ℂ) = u := rfl
      have hu'G : u' ∈ G := by
        show (u' : ℂ) ∈ S
        rw [hu'val]; exact hu
      have hpd : (⟨u', hu'G⟩ : ↥G) ^ Nat.card ↥G = 1 := by
        have hh := pow_card_eq_one (G := ↥G) (x := (⟨u', hu'G⟩ : ↥G))
        simpa [Nat.card_eq_fintype_card] using hh
      have hh := congrArg φ hpd
      rw [map_pow, map_one] at hh
      rwa [show φ (⟨u', hu'G⟩ : ↥G) = u from rfl] at hh
    · -- `u ^ d = 1 → u ∈ S`: `G` and `μ_d` have the same cardinality `d` and `G ≤ μ_d`.
      intro hu1
      by_cases huz : u = 0
      · subst huz
        rw [zero_pow (by have := Nat.card_pos (α := ↥G); omega)] at hu1
        exact absurd hu1 zero_ne_one
      · let u' : ℂˣ := Units.mk0 u huz
        have hu'val : (u' : ℂ) = u := rfl
        have hu'R : u' ∈ rootsOfUnity (Nat.card ↥G) ℂ := by
          rw [mem_rootsOfUnity]
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, hu'val, hu1]
          rfl
        have hGR : G ≤ rootsOfUnity (Nat.card ↥G) ℂ := by
          intro x hx
          rw [mem_rootsOfUnity]
          have hxd : (⟨x, hx⟩ : ↥G) ^ Nat.card ↥G = 1 := by
            have hh := pow_card_eq_one (G := ↥G) (x := (⟨x, hx⟩ : ↥G))
            simpa [Nat.card_eq_fintype_card] using hh
          have hcoe : ((⟨x, hx⟩ : ↥G) : ℂˣ) ^ Nat.card ↥G = 1 := by
            rw [← Subgroup.coe_pow, hxd]
            rfl
          simpa using hcoe
        haveI : NeZero (Nat.card ↥G) := ⟨by have := Nat.card_pos (α := ↥G); omega⟩
        have hRcard : Nat.card ↥(rootsOfUnity (Nat.card ↥G) ℂ) = Nat.card ↥G :=
          Complex.card_rootsOfUnity _
        haveI : Finite ↥(rootsOfUnity (Nat.card ↥G) ℂ) :=
          (Nat.card_ne_zero.mp (by rw [hRcard]; exact (by have := Nat.card_pos (α := ↥G); omega))).2
        have hGR_eq : G = rootsOfUnity (Nat.card ↥G) ℂ :=
          Subgroup.eq_of_le_of_card_ge hGR (by rw [hRcard])
        rw [← hGR_eq] at hu'R
        have : (u' : ℂ) ∈ S := hu'R
        rw [hu'val] at this
        exact this

end Work.EQ.Chart
