/-
# Peterfalvi, Appendix I (5)(a)

This file proves `Work.NormalComplement.appI_five_a`: with `d` prime, `t` of order `d`, `X` a finite
solvable subgroup normalised by `t` with `Nat.card X` coprime to `d`, and `K = Kapp t X =
{t⁻¹x⁻¹tx | x ∈ X}`, the prime divisors of `|⟨K⟩|` and of `|K|` coincide:

`q ∣ Nat.card ↥(Subgroup.closure (Kapp t X)) ↔ q ∣ (Kapp t X).ncard` for every prime `q`.

The easy direction `q ∣ |K| → q ∣ |⟨K⟩|` is immediate from App. I (4)
(`Work.NormalComplement.appI_four`), which gives `|⟨K⟩| = |K| · |V ∩ ⟨K⟩|` with `V = C_X(t)`.

For the converse we follow the source (Peterfalvi, p. 201): if `q ∤ |K| = |X : V|` then `|V|_q =
|X|_q`, and Hall's theorem applied to the coprime action of `t` on `X` yields a `t`-invariant Hall
`q'`-subgroup `R ≤ X` (`Work.NormalComplement.appI5_hall_normalized`).  Comparing the two chains of
index decompositions

* `|X| = |V| · |X : V| = |V| · |K|`,
* `|X| = |R| · q^k`, `|R| = |R ∩ V| · |Kapp t R|` and `|V| = |V ∩ R| · |V : V ∩ R|`

shows `|Kapp t R| = |K|`; since `Kapp t R ⊆ Kapp t X` this forces `Kapp t R = Kapp t X ⊆ R`, whence
`⟨K⟩ ≤ R` and `q ∤ |⟨K⟩|`.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI5_hall_normalized

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-- If `t` normalises `R`, then `t⁻¹` does too: the conjugation map `x ↦ t x t⁻¹` is an injective
self-map of the finite group `R`, hence bijective (this is the argument of `conjX_eq`). -/
theorem mem_inv_conj_of_normalizedBy {t : G} {R : Subgroup G} (htR : NormalizedBy t R) {x : G}
    (hx : x ∈ R) : t⁻¹ * x * t ∈ R := by
  have hmap : R.map (MulAut.conj t).toMonoidHom = R := conjX_eq htR
  have hx' : x ∈ R.map (MulAut.conj t).toMonoidHom := by rw [hmap]; exact hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hy' : y = t⁻¹ * x * t := by
    have h : t * y * t⁻¹ = x := by
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyx
    rw [← h]; group
  rwa [← hy']

/-- `Kapp t R ⊆ R` when `t` normalises `R`: each `t⁻¹x⁻¹tx` is a product of two elements of `R`. -/
theorem kapp_subset_self_of_normalizedBy {t : G} {R : Subgroup G} (htR : NormalizedBy t R) :
    Kapp t R ⊆ (R : Set G) := by
  rintro z ⟨x, hx, rfl⟩
  have h1 : t⁻¹ * x⁻¹ * t ∈ R := mem_inv_conj_of_normalizedBy htR (R.inv_mem hx)
  simpa [mul_assoc] using R.mul_mem h1 hx

theorem appI_five_a {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X) :
    ∀ q : ℕ, q.Prime →
      (q ∣ Nat.card ↥(Subgroup.closure (Work.NormalComplement.Kapp t X)) ↔
        q ∣ (Work.NormalComplement.Kapp t X).ncard) := by
  intro q hq
  obtain ⟨hKX, -, -, hsup, -, h6, hcard7⟩ := appI_four hd ht htX hdX
  -- App. I (1)(a): `|K| = |X : V|` where `V = C_X(t)`.
  have hKcard : (Kapp t X).ncard =
      ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index := appI_kapp_ncard t X
  refine ⟨fun hqN => ?_, fun hqd => dvd_trans hqd ⟨_, hcard7⟩⟩
  -- Converse, contrapositive: assume `q ∤ |K|` and `q ∣ |⟨K⟩|`, derive a contradiction.
  by_contra hqd
  -- Hall's theorem + Glauberman: a `t`-invariant Hall `q'`-subgroup `R ≤ X`.
  obtain ⟨R, hRX, htR, hqR, k, hk⟩ := appI5_hall_normalized (d := d) ht htX hdX hsolv hq
  -- `V = C_X(t)` and `V ⊓ R = C_R(t)`.
  have hVR : Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R =
      Subgroup.centralizer ({t} : Set G) ⊓ R := by
    ext x
    constructor
    · rintro ⟨⟨hx1, _⟩, hx3⟩; exact ⟨hx1, hx3⟩
    · rintro ⟨hx1, hx3⟩; exact ⟨⟨hx1, hRX hx3⟩, hx3⟩
  have hidxR : ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf R).index =
      (Kapp t R).ncard := by
    rw [hVR]
    exact (appI_kapp_ncard t R).symm
  -- The index decompositions.
  have hA1 : Nat.card ↥X =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) * (Kapp t X).ncard := by
    have hcard : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X) =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.centralizer ({t} : Set G) ⊓ X ≤ X)).toEquiv
    have hidx : ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index =
        (Kapp t X).ncard := hKcard.symm
    calc Nat.card ↥X
        = Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X) *
            ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) * (Kapp t X).ncard := by
          rw [hcard, hidx]
  have hA2 : Nat.card ↥X = Nat.card ↥R * q ^ k := by
    have hcard : Nat.card ↥(R.subgroupOf X) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
    calc Nat.card ↥X = Nat.card ↥(R.subgroupOf X) * (R.subgroupOf X).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card ↥R * q ^ k := by rw [hcard, hk]
  have hA3 : Nat.card ↥R =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) * (Kapp t R).ncard := by
    have hcard : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf R) =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R ≤ R)).toEquiv
    calc Nat.card ↥R
        = Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf R) *
            ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf R).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) * (Kapp t R).ncard := by
          rw [hcard, hidxR]
  have hA4 : Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) *
        ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
          (Subgroup.centralizer ({t} : Set G) ⊓ X)).index := by
    have hcard : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
          (Subgroup.centralizer ({t} : Set G) ⊓ X)) =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R ≤
          Subgroup.centralizer ({t} : Set G) ⊓ X)).toEquiv
    calc Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)
        = Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
              (Subgroup.centralizer ({t} : Set G) ⊓ X)) *
            ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
              (Subgroup.centralizer ({t} : Set G) ⊓ X)).index :=
          (Subgroup.card_mul_index _).symm
      _ = _ := by rw [hcard]
  -- Cancel `|V ∩ R|` in the two expressions for `|X|`: `m * |K| = |Kapp t R| * q^k`.
  have hfpos : 0 < Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) :=
    Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hkey : ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
        (Subgroup.centralizer ({t} : Set G) ⊓ X)).index * (Kapp t X).ncard =
      (Kapp t R).ncard * q ^ k := by
    apply Nat.mul_left_cancel hfpos
    calc Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) *
            (((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
              (Subgroup.centralizer ({t} : Set G) ⊓ X)).index * (Kapp t X).ncard)
        = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) * (Kapp t X).ncard := by
          rw [← mul_assoc, ← hA4]
      _ = Nat.card ↥X := hA1.symm
      _ = Nat.card ↥R * q ^ k := hA2
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R) *
            ((Kapp t R).ncard * q ^ k) := by rw [← mul_assoc, ← hA3]
  -- `q^k` is coprime to `|K|`, so it divides `m`; write `m = q^k * m₁`.
  have hcop : Nat.Coprime (q ^ k) (Kapp t X).ncard :=
    Nat.Coprime.pow_left k (hq.coprime_iff_not_dvd.mpr hqd)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, ((Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ R).subgroupOf
      (Subgroup.centralizer ({t} : Set G) ⊓ X)).index = q ^ k * m₁ :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop ⟨(Kapp t R).ncard, by rw [hkey, mul_comm]⟩
  -- `m₁ * |K| = |Kapp t R|`, and `|Kapp t R| ≤ |K|`, `1 ≤ m₁` force equality.
  have hepos : 0 < (Kapp t R).ncard := by
    have h1 : (1 : G) ∈ Kapp t R := ⟨1, R.one_mem, by simp⟩
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, h1⟩
  have hkey2 : m₁ * (Kapp t X).ncard = (Kapp t R).ncard := by
    have h := hkey
    rw [hm₁] at h
    rw [mul_assoc, mul_comm (Kapp t R).ncard (q ^ k)] at h
    exact Nat.mul_left_cancel (pow_pos hq.pos k) h
  have hm₁pos : 0 < m₁ := by
    have hpos : 0 < m₁ * (Kapp t X).ncard := by rw [hkey2]; exact hepos
    exact Nat.pos_of_mul_pos_right hpos
  have hsubset : Kapp t R ⊆ Kapp t X := fun z ⟨x, hx, hz⟩ => ⟨x, hRX hx, hz⟩
  have he_le : (Kapp t R).ncard ≤ (Kapp t X).ncard := Set.ncard_le_ncard hsubset (Set.toFinite _)
  have heq : (Kapp t R).ncard = (Kapp t X).ncard := by
    refine le_antisymm he_le ?_
    calc (Kapp t X).ncard = 1 * (Kapp t X).ncard := (one_mul _).symm
      _ ≤ m₁ * (Kapp t X).ncard :=
          Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hm₁pos))
      _ = (Kapp t R).ncard := hkey2
  -- Hence `K = Kapp t X` lies in `R`, so `⟨K⟩ ≤ R` and `q ∤ |⟨K⟩|`.
  have hKsub : Kapp t X ⊆ (R : Set G) := by
    rw [← Set.eq_of_subset_of_ncard_le hsubset (le_of_eq heq.symm) (Set.toFinite _)]
    exact kapp_subset_self_of_normalizedBy htR
  have hclos : Subgroup.closure (Kapp t X) ≤ R := (Subgroup.closure_le R).mpr hKsub
  exact hqR (Nat.dvd_trans hqN (Subgroup.card_dvd_of_le hclos))

end Work.NormalComplement
