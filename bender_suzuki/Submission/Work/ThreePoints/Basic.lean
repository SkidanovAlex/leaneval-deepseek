/-
# Area `ThreePoints`: Bender groups and the geometry of `Ω = G ⧸ H`

Vocabulary and first lemmas for Chapter II of

  T. Peterfalvi, *Le théorème de Bender–Suzuki I*, Astérisque 142–143 (1986), pp. 163–171
  (with Appendices I–IV, pp. 199–210),

whose main results are `Submission.Blueprint.ThmCProp` (Theorem C, p. 163) and
`Submission.Blueprint.ChIIFourProp` (Ch. II §4, Propositions 1–4, pp. 168–171).

Peterfalvi works with a finite group `G` of 2-rank `≥ 2` having a proper Bender group `H`
(hypotheses (B0)–(B2), pp. 163–168), the set `Ω = G ⧸ H` of conjugates of `H`, the set
`Inv(H)` of involutions of `H` (`n = |Inv(H)|`), the two-point stabiliser `D = H ∩ H^t`
of an involution `t ∉ H`, `V = C_D(t)`, `K = J(D,t) = {x ∈ D | x^t = x⁻¹}`.

This file contains only definitions and definitional API; the numbered results live in
sibling modules.  Mathlib's `G ⧸ H` is the set of left cosets of the subgroup `H` with
`g • xH = gxH`, and `MulAction.stabilizer G ω` is the point stabiliser of `ω`, which is a
conjugate of `H` (see `stabilizer_mk` below).
-/
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-! ## 1. Bender groups (Peterfalvi I Ch. I §1) -/

/-- `H` is a **Bender group for the prime `p`** of the finite group `G` (Peterfalvi I
Ch. I §1 (1)): `p ∣ |H|` and `p ∤ |H ∩ H^x|` for every `x ∉ H`. -/
def IsBenderGroup (p : ℕ) (H : Subgroup G) : Prop :=
  p ∣ Nat.card H ∧ ∀ x : G, x ∉ H → ¬ p ∣ Nat.card (H ⊓ conj x H : Subgroup G)

/-- Unfolding of `IsBenderGroup`. -/
theorem isBenderGroup_iff {p : ℕ} {H : Subgroup G} :
    IsBenderGroup p H ↔
      p ∣ Nat.card H ∧ ∀ x : G, x ∉ H → ¬ p ∣ Nat.card (H ⊓ conj x H : Subgroup G) :=
  Iff.rfl

/-- `n = |Inv(H)|`, the number of involutions of a Bender subgroup (Peterfalvi I Ch. I §2). -/
noncomputable def nInv (H : Subgroup G) : ℕ := (involutions (H : Set G)).ncard

/-- `H` contains a Sylow 2-subgroup of `G` (Peterfalvi I Ch. I §1 (3)). -/
def ContainsSylowTwo (H : Subgroup G) : Prop := ∃ S : Sylow 2 G, (S : Subgroup G) ≤ H

/-- `X` fixes at least three points of `Ω = G ⧸ H` (Peterfalvi I Ch. I §3). -/
def FixesThree (H X : Subgroup G) : Prop := 3 ≤ (fixedPts H X).ncard

/-- Oddness is the negation of divisibility by two. -/
theorem odd_iff_not_two_dvd (n : ℕ) : Odd n ↔ ¬ 2 ∣ n := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]

/-- A strongly embedded subgroup is exactly a proper Bender group for `p = 2`. -/
theorem isStronglyEmbedded_iff_isBenderGroup {H : Subgroup G} :
    IsStronglyEmbedded H ↔ H ≠ ⊤ ∧ IsBenderGroup 2 H := by
  unfold IsStronglyEmbedded IsBenderGroup
  simp only [even_iff_two_dvd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => (odd_iff_not_two_dvd _).mp (h3 x hx)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => (odd_iff_not_two_dvd _).mpr (h3 x hx)⟩

/-! ## 2. Conjugation of subgroups (the notation `H^x` of Peterfalvi) -/

/-- The underlying element of `MulAut.conj g` applied to `h`. -/
theorem mulAut_conj_apply (g h : G) : (MulAut.conj g) h = g * h * g⁻¹ :=
  MulAut.conj_apply g h

/-- The underlying `MonoidHom` of `MulAut.conj g` applied to `h`. -/
theorem mulAut_conj_toMonoidHom_apply (g h : G) :
    (MulAut.conj g).toMonoidHom h = g * h * g⁻¹ :=
  MulAut.conj_apply g h

/-- Membership in a conjugate, in terms of the conjugating element. -/
theorem mem_conj_iff {H : Subgroup G} {g x : G} : x ∈ conj g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have key : g⁻¹ * x * g = h := by
      rw [← hhx]
      change g⁻¹ * (MulAut.conj g) h * g = h
      rw [MulAut.conj_apply]
      group
    rwa [key]
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

/-- Membership in a conjugate, existentially. -/
theorem mem_conj_iff' {H : Subgroup G} {g x : G} :
    x ∈ conj g H ↔ ∃ h ∈ H, x = g * h * g⁻¹ := by
  constructor
  · intro hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    exact ⟨h, hh, by rw [← hhx]; exact MulAut.conj_apply g h⟩
  · rintro ⟨h, hh, rfl⟩
    exact Subgroup.mem_map.mpr ⟨h, hh, (MulAut.conj_apply g h).symm⟩

/-- Conjugation by `1` is the identity. -/
@[simp] theorem conj_one (H : Subgroup G) : conj 1 H = H := by
  ext x
  rw [mem_conj_iff]
  simp

/-- Conjugation composes. -/
theorem conj_mul (g h : G) (K : Subgroup G) : conj (g * h) K = conj g (conj h K) := by
  ext x
  simp only [mem_conj_iff]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

/-- A subgroup is contained in the conjugate determined by any one of its elements. -/
theorem le_conj_of_mem {H X : Subgroup G} {g : G} (hg : g ∈ H) (hX : X ≤ H) :
    X ≤ conj g H := by
  intro x hx
  rw [mem_conj_iff]
  exact H.mul_mem (H.mul_mem (H.inv_mem hg) (hX hx)) hg

/-! ## 3. `IsStronglyEmbedded` unpacked -/

namespace IsStronglyEmbedded

variable {H : Subgroup G}

theorem ne_top (h : IsStronglyEmbedded H) : H ≠ ⊤ := h.1

theorem even_card (h : IsStronglyEmbedded H) : Even (Nat.card H) := h.2.1

theorem two_dvd_card (h : IsStronglyEmbedded H) : 2 ∣ Nat.card H :=
  even_iff_two_dvd.mp (IsStronglyEmbedded.even_card h)

theorem odd_card_inf_conj (h : IsStronglyEmbedded H) {x : G} (hx : x ∉ H) :
    Odd (Nat.card (H ⊓ conj x H : Subgroup G)) := h.2.2 x hx

/-- A strongly embedded subgroup is a Bender group for `2`. -/
theorem isBenderGroup_two (h : IsStronglyEmbedded H) : IsBenderGroup 2 H :=
  (isStronglyEmbedded_iff_isBenderGroup.mp h).2

end IsStronglyEmbedded

/-! ## 4. Peterfalvi I Ch. I §1 (2): normalisers of even-order subgroups of `H` -/

/-- **(Peterfalvi I Ch. I §1 (2)).**  If `H` is a Bender group for `p` and `X ≤ H` has order
divisible by `p`, then `N_G(X) ≤ H`. -/
theorem IsBenderGroup.normalizer_le_of_dvd {p : ℕ} {H X : Subgroup G} (hH : IsBenderGroup p H)
    (hX : X ≤ H) (hdvd : p ∣ Nat.card X) : Subgroup.normalizer (X : Set G) ≤ H := by
  intro g hg
  by_contra hgH
  have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer (X : Set G)).inv_mem hg
  have hXle : X ≤ H ⊓ conj g H := by
    refine le_inf hX fun x hx => ?_
    rw [mem_conj_iff]
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp hg' x).mp hx
      simpa using this
    exact hX hx'
  have hdvd' : p ∣ Nat.card (H ⊓ conj g H : Subgroup G) :=
    dvd_trans hdvd (Subgroup.card_dvd_of_le hXle)
  exact hH.2 g hgH hdvd'

/-- **(Peterfalvi I Ch. I §1 (4)).**  A strongly embedded subgroup is self-normalising. -/
theorem IsStronglyEmbedded.normalizer_eq {H : Subgroup G} (h : IsStronglyEmbedded H) :
    Subgroup.normalizer (H : Set G) = H :=
  le_antisymm
    ((IsStronglyEmbedded.isBenderGroup_two h).normalizer_le_of_dvd le_rfl
      (even_iff_two_dvd.mp (IsStronglyEmbedded.even_card h)))
    Subgroup.le_normalizer

/-- **(Peterfalvi I Ch. I §1 (2)).**  If `x ∈ H` has even order, any conjugate of `H` containing
`x` contains `C_G(x)`; in particular `C_G(x) ≤ H` for the given `H`. -/
theorem IsStronglyEmbedded.centralizer_le {H : Subgroup G} (h : IsStronglyEmbedded H) {x : G}
    (hx : x ∈ H) (hx2 : 2 ∣ orderOf x) : Subgroup.centralizer ({x} : Set G) ≤ H := by
  have h1 : Subgroup.zpowers x ≤ H := by rwa [Subgroup.zpowers_le]
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers x : Subgroup G) := by
    rw [Nat.card_zpowers]; exact hx2
  intro y hy
  have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have hc : (MulAut.conj y) x = x := by rw [mulAut_conj_apply, hxy]; group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hc
  exact IsBenderGroup.normalizer_le_of_dvd (IsStronglyEmbedded.isBenderGroup_two h) h1 h2 hyN

/-! ## 5. Involutions, `J(X,t)`, two-point stabilisers, fixed points -/

theorem mem_involutions {S : Set G} {x : G} : x ∈ involutions S ↔ x ∈ S ∧ orderOf x = 2 :=
  Iff.rfl

theorem mem_invertedBy {X : Subgroup G} {t x : G} :
    x ∈ invertedBy X t ↔ x ∈ X ∧ t * x * t⁻¹ = x⁻¹ :=
  Iff.rfl

theorem one_mem_invertedBy (X : Subgroup G) (t : G) : (1 : G) ∈ invertedBy X t := by
  rw [mem_invertedBy]
  exact ⟨X.one_mem, by group⟩

theorem twoPoint_eq (H : Subgroup G) (t : G) : twoPoint H t = H ⊓ conj t H := rfl

theorem mem_twoPoint {H : Subgroup G} {t x : G} :
    x ∈ twoPoint H t ↔ x ∈ H ∧ t⁻¹ * x * t ∈ H := by
  rw [twoPoint_eq, Subgroup.mem_inf, mem_conj_iff]

theorem centD_eq (H : Subgroup G) (t : G) :
    centD H t = twoPoint H t ⊓ Subgroup.centralizer ({t} : Set G) := rfl

theorem mem_centD {H : Subgroup G} {t x : G} :
    x ∈ centD H t ↔ x ∈ H ∧ t⁻¹ * x * t ∈ H ∧ x * t = t * x := by
  rw [centD_eq, Subgroup.mem_inf, mem_twoPoint, Subgroup.mem_centralizer_singleton_iff]
  tauto

theorem mem_fixedPts {H X : Subgroup G} {ω : G ⧸ H} :
    ω ∈ fixedPts H X ↔ ∀ x ∈ X, x • ω = ω :=
  Iff.rfl

theorem fixedPts_mono {H X Y : Subgroup G} (h : X ≤ Y) : fixedPts H Y ⊆ fixedPts H X :=
  fun _ hω x hx => hω x (h hx)

/-- A point of `Ω` is fixed by `X` exactly when the point stabiliser contains `X`. -/
theorem mem_fixedPts_iff_le_stabilizer {H X : Subgroup G} {ω : G ⧸ H} :
    ω ∈ fixedPts H X ↔ X ≤ MulAction.stabilizer G ω := by
  rw [mem_fixedPts, SetLike.le_def]
  constructor
  · intro h x hx
    rw [MulAction.mem_stabilizer_iff]
    exact h x hx
  · intro h x hx
    exact (MulAction.mem_stabilizer_iff.mp (h hx))

/-! ## 6. Point stabilisers are conjugates of `H` -/

/-- The action of `G` on `Ω = G ⧸ H` by left multiplication: `x • gH = xgH`. -/
theorem smul_mk (H : Subgroup G) (x g : G) :
    x • (g : G ⧸ H) = ((x * g : G) : G ⧸ H) :=
  rfl

/-- The stabiliser of the coset `gH` is the conjugate `gHg⁻¹` of `H`. -/
theorem stabilizer_mk (H : Subgroup G) (g : G) :
    MulAction.stabilizer G (g : G ⧸ H) = conj g H := by
  ext x
  rw [MulAction.mem_stabilizer_iff, smul_mk, QuotientGroup.eq, mem_conj_iff]
  rw [show (x * g)⁻¹ * g = (g⁻¹ * x * g)⁻¹ by group, H.inv_mem_iff]

end Work.ThreePoints
