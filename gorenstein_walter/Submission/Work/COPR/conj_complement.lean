import Mathlib
import Submission.Work.COPR.Defs

open scoped Pointwise

namespace Work.COPR

open Subgroup MulAction

/-! ### Auxiliary lemmas for `Work.COPR.conj_complement` -/

/-- A `p`-subgroup and a subgroup of order coprime to `p` are disjoint. -/
lemma disjoint_of_isPGroup_of_coprime_card {X : Type*} [Group X] {p : ℕ}
    (P Y : Subgroup X) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card Y)) :
    Disjoint P Y := by
  refine Subgroup.disjoint_def.mpr fun {g} hgP hgY => ?_
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have h1 : orderOf g ∣ p ^ k := Subgroup.orderOf_mk g hgP ▸ orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card ↥Y := Subgroup.orderOf_dvd_natCard Y hgY
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) h1 h2)

/-- For `Y` normal in `X` and `Disjoint P Y`, the join `P ⊔ Y` has cardinality `|P| * |Y|`. -/
lemma card_sup_of_disjoint_of_normal {X : Type*} [Group X]
    (P Y : Subgroup X) [Y.Normal] (hd : Disjoint P Y) :
    Nat.card ↥(P ⊔ Y) = Nat.card ↥P * Nat.card ↥Y := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun x : ↥P × ↥Y =>
    (⟨(x.1 : X) * (x.2 : X),
      (P ⊔ Y).mul_mem ((le_sup_left : P ≤ P ⊔ Y) x.1.2)
        ((le_sup_right : Y ≤ P ⊔ Y) x.2.2)⟩ : ↥(P ⊔ Y)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨p₁, hp₁⟩, ⟨y₁, hy₁⟩⟩ ⟨⟨p₂, hp₂⟩, ⟨y₂, hy₂⟩⟩ h
    simp only [Subtype.mk.injEq] at h
    have key : p₂⁻¹ * p₁ = y₂ * y₁⁻¹ := by
      have h' := congrArg (fun t => p₂⁻¹ * t * y₁⁻¹) h
      simpa [mul_assoc] using h'
    have hP : p₂⁻¹ * p₁ ∈ P := P.mul_mem (P.inv_mem hp₂) hp₁
    have hY : p₂⁻¹ * p₁ ∈ Y := by rw [key]; exact Y.mul_mem hy₂ (Y.inv_mem hy₁)
    have h1 : p₂⁻¹ * p₁ = 1 := Subgroup.disjoint_def.mp hd hP hY
    have hp : p₁ = p₂ := by
      have := congrArg (fun t => p₂ * t) h1
      simpa using this
    have hy : y₁ = y₂ := by rw [← hp] at h; exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hp) (Subtype.ext hy)
  · rintro ⟨h, hh⟩
    have : h ∈ (P : Set X) * (Y : Set X) := by
      rw [← Subgroup.mul_normal P Y]; exact hh
    obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.mp this
    exact ⟨(⟨p, hp⟩, ⟨y, hy⟩), Subtype.ext hpy⟩

/-- Pointwise conjugation of a subgroup is its image under `MulAut.conj`. -/
lemma conj_smul_eq_map {X : Type*} [Group X] (P : Subgroup X) (g : X) :
    MulAut.conj g • P = P.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]; congr 1

/-- Conjugating a subgroup by `y * p` with `p ∈ P` is the same as conjugating it by `y`. -/
lemma map_conj_mul_mem {X : Type*} [Group X] (P : Subgroup X) (y p : X) (hp : p ∈ P) :
    P.map (MulAut.conj (y * p)).toMonoidHom = P.map (MulAut.conj y).toMonoidHom := by
  rw [map_mul MulAut.conj]
  change P.map ((MulAut.conj y).toMonoidHom.comp (MulAut.conj p).toMonoidHom) =
    P.map (MulAut.conj y).toMonoidHom
  rw [← Subgroup.map_map]
  have hfix : P.map (MulAut.conj p).toMonoidHom = P := by
    rw [← conj_smul_eq_map]
    exact Subgroup.conj_smul_eq_self_of_mem hp
  rw [hfix]

/-- Let `Y` be a normal `p'`-subgroup of a finite group `X` (i.e. `p ∤ |Y|`), and let `P, Q ≤ X`
be `p`-subgroups with `P ⊔ Y = Q ⊔ Y`. Then `Q` is conjugate to `P` by an element of `Y`.

This is the "conjugacy of complements" half of Schur–Zassenhaus in the special case where the two
complements `P, Q` are `p`-groups and `Y` is a normal `p'`-subgroup; equivalently `P` and `Q` are
Sylow `p`-subgroups of the common group `P ⊔ Y` and Sylow conjugacy applies. -/
theorem conj_complement {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (P Y Q : Subgroup X) [Y.Normal] (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hcop : Nat.Coprime p (Nat.card Y)) (hsup : P ⊔ Y = Q ⊔ Y) :
    ∃ y ∈ Y, Q = P.map (MulAut.conj y).toMonoidHom := by
  have hdPY : Disjoint P Y := disjoint_of_isPGroup_of_coprime_card P Y hP hcop
  have hdQY : Disjoint Q Y := disjoint_of_isPGroup_of_coprime_card Q Y hQ hcop
  have hPle : P ≤ P ⊔ Y := le_sup_left
  have hQle : Q ≤ P ⊔ Y := by rw [hsup]; exact le_sup_left
  -- Cardinality of the common group `H = P ⊔ Y = Q ⊔ Y`.
  have hcardP : Nat.card ↥(P ⊔ Y) = Nat.card ↥P * Nat.card ↥Y :=
    card_sup_of_disjoint_of_normal P Y hdPY
  have hcardQ : Nat.card ↥(P ⊔ Y) = Nat.card ↥Q * Nat.card ↥Y := by
    rw [hsup]; exact card_sup_of_disjoint_of_normal Q Y hdQY
  -- `P` and `Q` are `p`-subgroups of `↥(P ⊔ Y)`.
  have hPsub : IsPGroup p (P.subgroupOf (P ⊔ Y)) := hP.comap_subtype
  have hQsub : IsPGroup p (Q.subgroupOf (P ⊔ Y)) := hQ.comap_subtype
  have hPcardSub : Nat.card ↥(P.subgroupOf (P ⊔ Y)) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
  have hQcardSub : Nat.card ↥(Q.subgroupOf (P ⊔ Y)) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
  -- Their index inside `↥(P ⊔ Y)` equals `|Y|`, hence is coprime to `p`: they are Sylow.
  have hidxP : (P.subgroupOf (P ⊔ Y)).index = Nat.card ↥Y := by
    have h := Subgroup.card_mul_index (P.subgroupOf (P ⊔ Y))
    rw [hPcardSub, hcardP] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥P)) h
  have hidxQ : (Q.subgroupOf (P ⊔ Y)).index = Nat.card ↥Y := by
    have h := Subgroup.card_mul_index (Q.subgroupOf (P ⊔ Y))
    rw [hQcardSub, hcardQ] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥Q)) h
  have hndP : ¬ p ∣ (P.subgroupOf (P ⊔ Y)).index := by
    rw [hidxP]
    intro h
    exact (Fact.out : p.Prime).ne_one
      (Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_right (m := 1) (by rw [one_mul]; exact h)))
  have hndQ : ¬ p ∣ (Q.subgroupOf (P ⊔ Y)).index := by
    rw [hidxQ]
    intro h
    exact (Fact.out : p.Prime).ne_one
      (Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_right (m := 1) (by rw [one_mul]; exact h)))
  -- Sylow conjugacy inside `↥(P ⊔ Y)`: an element `g` with `Q = P ^ g`.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(P ⊔ Y)
      (hPsub.toSylow hndP) (hQsub.toSylow hndQ)
  have hg1 : (MulAut.conj g : MulAut ↥(P ⊔ Y)) • (P.subgroupOf (P ⊔ Y))
      = Q.subgroupOf (P ⊔ Y) := by
    have h := congrArg (fun S : Sylow p ↥(P ⊔ Y) => (↑S : Subgroup ↥(P ⊔ Y))) hg
    rwa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h
  have hgX : (MulAut.conj (g : X) • P).subgroupOf (P ⊔ Y) = Q.subgroupOf (P ⊔ Y) := by
    rw [← Subgroup.conj_smul_subgroupOf hPle g]; exact hg1
  have hQmap : Subgroup.map (P ⊔ Y).subtype (Q.subgroupOf (P ⊔ Y)) = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]; exact hQle
  have hPmap : Subgroup.map (P ⊔ Y).subtype ((MulAut.conj (g : X) • P).subgroupOf (P ⊔ Y))
      = MulAut.conj (g : X) • P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact Subgroup.conj_smul_le_of_le hPle g
  have hconjEq : MulAut.conj (g : X) • P = Q := by
    have h := congrArg (Subgroup.map (P ⊔ Y).subtype) hgX
    rwa [hPmap, hQmap] at h
  -- Write `g = y * p` with `y ∈ Y`, `p ∈ P` (using `Y` normal and `P ⊔ Y = Y * P`).
  obtain ⟨y, hy, pp, hpp, hyp⟩ : ∃ y ∈ Y, ∃ pp ∈ P, y * pp = (g : X) := by
    have hmem : (g : X) ∈ (Y : Set X) * (P : Set X) := by
      rw [← Subgroup.normal_mul Y P, sup_comm]; exact g.2
    exact Set.mem_mul.mp hmem
  refine ⟨y, hy, ?_⟩
  rw [← hconjEq, ← hyp, conj_smul_eq_map, map_conj_mul_mem P y pp hpp]

end Work.COPR
