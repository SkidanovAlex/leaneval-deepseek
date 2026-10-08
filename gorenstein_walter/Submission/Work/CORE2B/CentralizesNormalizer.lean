import Mathlib
import Submission.Work.CORE2B.Basic

/-!
# `CentralizesNormalizer`

Bender 1981, 1.1(iv) in the form used in the proof of Theorem 2.10: a `2`-element `t` acting on a
`p`-group `P` (`p` odd) which centralizes `N_P(X)` for some `X ≤ P` centralizes all of `P`.

The proof is Bender's.  Write `H = C_P(t)` and `L = N_P(H)`.  Since `H ⊴ L`, the conjugation
identity `(t g t⁻¹) h (t g t⁻¹)⁻¹ = g h g⁻¹` (`g ∈ L`, `h ∈ H`) holds; it shows that every
"commutator" `t g t⁻¹ g⁻¹` (`g ∈ L`) centralizes `H`, hence lies in `N_P(X) ⊆ C_G(t)`.  There
`t (t g t⁻¹ g⁻¹) t⁻¹ = (t g t⁻¹ g⁻¹)⁻¹`, so the commutator is an element of odd order with square
`1`, hence trivial.  Thus `L` centralizes `t`, i.e. `L ≤ H`; as `H ≤ L` we get `N_P(H) = H`, and a
`p`-group is self-normalizing only in itself: `H = P`.

The general statement follows by the usual descent on the `2`-power order of `t`: if `t ^ (2 ^ n)`
centralizes `P`, then the involution case applies to the `2`-element `t ^ (2 ^ (n-1))`.
-/

namespace Work.CORE2B

open Subgroup

variable {G : Type} [Group G]

/-- In a finite `p`-group, a subgroup which contains its own normalizer is the whole group. -/
theorem eq_of_normalizer_inf_eq {p : ℕ} [Fact p.Prime] [Finite G] {P H : Subgroup G}
    (hP : IsPGroup p P) (hHP : H ≤ P)
    (h : Subgroup.normalizer (H : Set G) ⊓ P = H) : H = P := by
  have hsub : (Subgroup.normalizer (H : Set G)).subgroupOf P = H.subgroupOf P := by
    conv_rhs => rw [← h]
    exact (Subgroup.inf_subgroupOf_right (Subgroup.normalizer (H : Set G)) P).symm
  have hn : Subgroup.normalizer ((H.subgroupOf P : Subgroup ↥P) : Set ↥P) = H.subgroupOf P := by
    rw [← Subgroup.subgroupOf_normalizer_eq hHP]
    exact hsub
  have hnil : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  have hnc : NormalizerCondition ↥P := @Group.normalizerCondition_of_isNilpotent _ _ hnil
  have htop : H.subgroupOf P = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hn
  have hmap : (H.subgroupOf P).map P.subtype = (⊤ : Subgroup ↥P).map P.subtype := by rw [htop]
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hHP] at hmap
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap

/-- The involution case: if `t ^ 2` centralizes the `p`-group `P` (`p` odd) and `t` normalizes `P`
and centralizes `N_P(X)` for some `X ≤ P`, then `t` centralizes `P`. -/
theorem centralizes_of_sq_centralizes (p : ℕ) [Fact p.Prime] [Finite G] (hp2 : p ≠ 2)
    (P X : Subgroup G) (t : G) (hP : IsPGroup p P)
    (htN : t ∈ Subgroup.normalizer (P : Set G)) (hXP : X ≤ P)
    (h2 : ∀ g ∈ P, t * t * g = g * (t * t))
    (hcen : P ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer ({t} : Set G)) :
    P ≤ Subgroup.centralizer ({t} : Set G) := by
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set H : Subgroup G := P ⊓ C with hH
  have hHP : H ≤ P := by rw [hH]; exact inf_le_left
  have hHC : H ≤ C := by rw [hH]; exact inf_le_right
  have hXH : X ≤ H := by
    rw [hH]
    exact le_inf hXP ((le_inf hXP Subgroup.le_normalizer).trans hcen)
  -- membership in the normalizer of `H`, in usable form
  have hmemN : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) → ∀ h : G, h ∈ H →
      g * h * g⁻¹ ∈ H :=
    fun g hg h hh => (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  -- `t` fixes `H` pointwise, and so does `t⁻¹`
  have htHconv : ∀ h ∈ H, t * h * t⁻¹ = h := by
    intro h hh
    have hhC : h ∈ C := hHC hh
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hhC
    rw [← hhC]
    group
  have htHconv' : ∀ h ∈ H, t⁻¹ * h * t = h := by
    intro h hh
    have h1 : t * h = h * t := by
      have h' : t * h * t⁻¹ = h := htHconv h hh
      calc t * h = t * h * t⁻¹ * t := by group
        _ = h * t := by rw [h']
    calc t⁻¹ * h * t = t⁻¹ * (h * t) := by group
      _ = t⁻¹ * (t * h) := by rw [← h1]
      _ = h := by group
  have htH : t ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => by rw [htHconv h hh]; exact hh, fun hh => by
      have h' : t⁻¹ * (t * h * t⁻¹) * t = t * h * t⁻¹ := htHconv' _ hh
      have : h = t * h * t⁻¹ := by rw [← h']; group
      rw [this]; exact hh⟩
  set L : Subgroup G := Subgroup.normalizer (H : Set G) ⊓ P with hL
  have hLP : L ≤ P := by rw [hL]; exact inf_le_right
  have hLN : L ≤ Subgroup.normalizer (H : Set G) := by rw [hL]; exact inf_le_left
  have hHL : H ≤ L := by rw [hL]; exact le_inf Subgroup.le_normalizer hHP
  -- the conjugation identity
  have hconj : ∀ g ∈ L, ∀ h ∈ H,
      t * g * t⁻¹ * h * (t * g * t⁻¹)⁻¹ = g * h * g⁻¹ := by
    intro g hgL h hh
    have hgh : g * h * g⁻¹ ∈ H := hmemN g (hLN hgL) h hh
    have hstep : t * (g * h * g⁻¹) * t⁻¹ = g * h * g⁻¹ := htHconv _ hgh
    have heq : t⁻¹ * h * t = h := htHconv' h hh
    calc t * g * t⁻¹ * h * (t * g * t⁻¹)⁻¹
        = t * g * (t⁻¹ * h * t) * g⁻¹ * t⁻¹ := by group
      _ = t * g * h * g⁻¹ * t⁻¹ := by rw [heq]
      _ = t * (g * h * g⁻¹) * t⁻¹ := by group
      _ = g * h * g⁻¹ := hstep
  -- the commutators centralize `H`
  have hgen_centH : ∀ w ∈ ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G),
      w ∈ Subgroup.centralizer (H : Set G) := by
    rintro w ⟨g, hgL, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hinvN : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.inv_mem _ (hLN hgL)
    have hgh : g⁻¹ * h * g ∈ H := by simpa using hmemN g⁻¹ hinvN h hh
    have hstep : t * g * t⁻¹ * (g⁻¹ * h * g) * (t * g * t⁻¹)⁻¹ =
        g * (g⁻¹ * h * g) * g⁻¹ := hconj g hgL _ hgh
    have key : t * g * t⁻¹ * g⁻¹ * h * (t * g * t⁻¹ * g⁻¹)⁻¹ = h := by
      calc t * g * t⁻¹ * g⁻¹ * h * (t * g * t⁻¹ * g⁻¹)⁻¹
          = t * g * t⁻¹ * (g⁻¹ * h * g) * (t * g * t⁻¹)⁻¹ := by group
        _ = g * (g⁻¹ * h * g) * g⁻¹ := hstep
        _ = h := by group
    calc h * (t * g * t⁻¹ * g⁻¹)
        = (t * g * t⁻¹ * g⁻¹ * h * (t * g * t⁻¹ * g⁻¹)⁻¹) * (t * g * t⁻¹ * g⁻¹) := by
          rw [key]
      _ = (t * g * t⁻¹ * g⁻¹) * h := by group
  -- the commutators lie in `P`
  have hgen_P : ∀ w ∈ ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G), w ∈ P := by
    rintro w ⟨g, hgL, rfl⟩
    have hgP : g ∈ P := hLP hgL
    have h1 : t * g * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp htN g).mp hgP
    exact P.mul_mem h1 (P.inv_mem hgP)
  -- hence all commutators commute with `t`
  have hgen_C : ∀ w ∈ ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G), w ∈ C := by
    intro w hw
    have h1 : Subgroup.closure ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G) ≤
        Subgroup.centralizer (H : Set G) := (Subgroup.closure_le _).mpr hgen_centH
    have h2 : Subgroup.closure ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G) ≤ P :=
      (Subgroup.closure_le _).mpr hgen_P
    have h3 : Subgroup.closure ({w : G | ∃ g ∈ L, w = t * g * t⁻¹ * g⁻¹} : Set G) ≤
        Subgroup.normalizer (X : Set G) :=
      h1.trans ((Subgroup.centralizer_le hXH).trans (Subgroup.centralizer_le_normalizer _))
    exact hcen (Subgroup.mem_inf.mpr
      ⟨h2 (Subgroup.subset_closure hw), h3 (Subgroup.subset_closure hw)⟩)
  -- the key step: a commutator of odd order whose square is `1` is trivial
  have hcomm_one : ∀ g ∈ L, t * g * t⁻¹ * g⁻¹ = 1 := by
    intro g hgL
    have hgP : g ∈ P := hLP hgL
    have hwC : t * g * t⁻¹ * g⁻¹ ∈ C := hgen_C _ ⟨g, hgL, rfl⟩
    have hwfix : t * (t * g * t⁻¹ * g⁻¹) * t⁻¹ = t * g * t⁻¹ * g⁻¹ := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff] at hwC
      rw [← hwC]; group
    have hwinv : t * (t * g * t⁻¹ * g⁻¹) * t⁻¹ = (t * g * t⁻¹ * g⁻¹)⁻¹ := by
      have hg := h2 g hgP
      calc t * (t * g * t⁻¹ * g⁻¹) * t⁻¹
          = (t * t * g) * t⁻¹ * g⁻¹ * t⁻¹ := by group
        _ = (g * (t * t)) * t⁻¹ * g⁻¹ * t⁻¹ := by rw [hg]
        _ = (t * g * t⁻¹ * g⁻¹)⁻¹ := by group
    have hww : t * g * t⁻¹ * g⁻¹ = (t * g * t⁻¹ * g⁻¹)⁻¹ := hwfix.symm.trans hwinv
    have hw2 : (t * g * t⁻¹ * g⁻¹) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hww
    have hwP : t * g * t⁻¹ * g⁻¹ ∈ P := hgen_P _ ⟨g, hgL, rfl⟩
    obtain ⟨k, hk⟩ := hP ⟨t * g * t⁻¹ * g⁻¹, hwP⟩
    have hk' : (t * g * t⁻¹ * g⁻¹) ^ p ^ k = 1 := by
      have h := congrArg (Subtype.val) hk
      simpa using h
    have hdvd1 : orderOf (t * g * t⁻¹ * g⁻¹) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hw2
    have hdvd2 : orderOf (t * g * t⁻¹ * g⁻¹) ∣ p ^ k :=
      orderOf_dvd_iff_pow_eq_one.mpr hk'
    have hodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
    have hcop : Nat.Coprime 2 (p ^ k) := ((Nat.coprime_two_right.mpr hodd).symm)
    have hdvd : orderOf (t * g * t⁻¹ * g⁻¹) ∣ 1 := by
      have hg1 : orderOf (t * g * t⁻¹ * g⁻¹) ∣ Nat.gcd 2 (p ^ k) := Nat.dvd_gcd hdvd1 hdvd2
      rw [hcop] at hg1
      exact hg1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  -- consequently `L` centralizes `t`
  have hLC : L ≤ C := by
    intro g hgL
    have h1 : t * g * t⁻¹ * g⁻¹ = 1 := hcomm_one g hgL
    have h2 : t * g * t⁻¹ = g := by
      have h := congrArg (· * g) h1
      simpa [mul_assoc] using h
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    calc g * t = (t * g * t⁻¹) * t := by rw [h2]
      _ = t * g := by group
  have hLH : L ≤ H := by
    rw [hH]
    exact le_inf hLP hLC
  have hLH' : L = H := le_antisymm hLH hHL
  have hH_P : H = P := by
    refine eq_of_normalizer_inf_eq hP hHP ?_
    rw [← hL]
    exact hLH'
  rw [hH] at hH_P
  intro x hx
  have : x ∈ P ⊓ C := by rw [hH_P]; exact hx
  exact (Subgroup.mem_inf.mp this).2

theorem CentralizesNormalizer {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (P X : Subgroup G) (t : G) (hP : IsPGroup p P)
    (ht : IsPGroup 2 (Subgroup.zpowers t)) (htN : t ∈ Subgroup.normalizer (P : Set G))
    (hXP : X ≤ P)
    (hcen : P ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer ({t} : Set G)) :
    P ≤ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, t ^ 2 ^ K = 1 := by
    obtain ⟨k, hk⟩ := ht ⟨t, Subgroup.mem_zpowers t⟩
    exact ⟨k, by simpa using congrArg (Subtype.val) hk⟩
  have hcen_pow : ∀ n : ℕ, P ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.centralizer ({(t ^ n)} : Set G) := by
    intro n
    refine le_trans hcen ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hx, ← mul_assoc]
  let M : (m : ℕ) → m ≤ K → Prop := fun m _ => P ≤ Subgroup.centralizer ({(t ^ 2 ^ m)} : Set G)
  have hbase : M K le_rfl := by
    simp only [M]
    rw [hK]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp
  have hstep : ∀ j (hj : j < K), M (j + 1) (Nat.succ_le_of_lt hj) → M j (le_of_lt hj) := by
    intro j hj ih
    simp only [M] at ih ⊢
    have huN : t ^ 2 ^ j ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.pow_mem (Subgroup.normalizer (P : Set G)) htN (2 ^ j)
    have hu2 : ∀ g ∈ P, (t ^ 2 ^ j) * (t ^ 2 ^ j) * g =
        g * ((t ^ 2 ^ j) * (t ^ 2 ^ j)) := by
      intro g hgp
      have hcomm : g ∈ Subgroup.centralizer ({(t ^ 2 ^ (j + 1))} : Set G) := ih hgp
      rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
      have hpow : (t ^ 2 ^ j) * (t ^ 2 ^ j) = t ^ 2 ^ (j + 1) := by
        rw [← pow_add]
        congr 1
        rw [← Nat.mul_two, ← Nat.pow_succ]
      rw [hpow]
      exact hcomm.symm
    exact centralizes_of_sq_centralizes p hp2 P X (t ^ 2 ^ j) hP huN hXP hu2
      (hcen_pow (2 ^ j))
  have hgoal : M 0 (Nat.zero_le K) := Nat.decreasingInduction hstep hbase (Nat.zero_le K)
  simpa [M] using hgoal

end Work.CORE2B
