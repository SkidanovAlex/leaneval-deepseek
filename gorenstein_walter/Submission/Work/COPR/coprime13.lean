import Mathlib
import Submission.Work.COPR.Defs
import Submission.Work.COPR.Prelude13
import Submission.Work.COPR.conj_complement
import Submission.Work.COPR.centralizer_map_le

namespace Work.COPR

open Subgroup

variable {X : Type*} [Group X] [Finite X]

/-! ## Elementary identities for inner automorphisms -/

/-- Composition of inner automorphisms: `conj a ∘ conj b = conj (a * b)`. -/
theorem coprime13_conj_comp (a b : X) :
    (MulAut.conj a : X →* X).comp (MulAut.conj b : X →* X) =
      (MulAut.conj (a * b) : X →* X) := by
  ext z
  change a * (b * z * b⁻¹) * a⁻¹ = a * b * z * (a * b)⁻¹
  group

/-- The quotient map intertwines inner automorphisms. -/
theorem coprime13_mk_conj_apply {Y : Subgroup X} [Y.Normal] (x z : X) :
    (MulAut.conj ((QuotientGroup.mk' Y) x)) ((QuotientGroup.mk' Y) z) =
      (QuotientGroup.mk' Y) ((MulAut.conj x) z) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- As monoid homomorphisms, the quotient map conjugates. -/
theorem coprime13_mk_comp_conj {Y : Subgroup X} [Y.Normal] (x : X) :
    (MulAut.conj ((QuotientGroup.mk' Y) x) : (X ⧸ Y) →* (X ⧸ Y)).comp
        (QuotientGroup.mk' Y) =
      (QuotientGroup.mk' Y).comp (MulAut.conj x : X →* X) := by
  ext z
  exact coprime13_mk_conj_apply x z

/-- `conj 1` is the identity homomorphism. -/
theorem coprime13_conj_one_toMonoidHom :
    (MulAut.conj (1 : X) : X →* X) = MonoidHom.id X := by
  ext z
  change 1 * z * 1⁻¹ = z
  simp

/-! ## The normalizer inclusion `N_{X̄}(P̄) ≤ N_X(P)·Y` -/

/-- If `x` normalizes the image of `P` in `X ⧸ Y`, then `P^x ≤ P ⊔ Y`. -/
theorem coprime13_map_conj_le_sup_of_mem_normalizer (P Y : Subgroup X) [Y.Normal] (x : X)
    (hx : QuotientGroup.mk' Y x ∈
      Subgroup.normalizer ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y))) :
    P.map (MulAut.conj x : X →* X) ≤ P ⊔ Y := by
  have h : (P.map (QuotientGroup.mk' Y)).map
        (MulAut.conj ((QuotientGroup.mk' Y) x) : (X ⧸ Y) →* (X ⧸ Y)) =
      P.map (QuotientGroup.mk' Y) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have h2 : (P.map (MulAut.conj x : X →* X)).map (QuotientGroup.mk' Y) =
      P.map (QuotientGroup.mk' Y) := by
    rw [← h]
    simp only [Subgroup.map_map, coprime13_mk_comp_conj]
  have h3 : (P.map (MulAut.conj x : X →* X)).map (QuotientGroup.mk' Y) ≤
      P.map (QuotientGroup.mk' Y) := le_of_eq h2
  rw [Subgroup.map_le_map_iff] at h3
  rwa [QuotientGroup.ker_mk'] at h3

/-- The normalizer of the image of `P` in `X ⧸ Y` is contained in the image of `N_X(P)`. -/
theorem coprime13_normalizer_le (p : ℕ) [Fact p.Prime] (P Y : Subgroup X) [Y.Normal]
    (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card Y)) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) ≤
      (Subgroup.normalizer (P : Set X)).map (QuotientGroup.mk' Y) := by
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y q
  set Q : Subgroup X := P.map (MulAut.conj x : X →* X) with hQ
  have h1 : Q ≤ P ⊔ Y := coprime13_map_conj_le_sup_of_mem_normalizer P Y x hq
  -- `Q` and `P` are both `p`-subgroups with `P ⊔ Y = Q ⊔ Y`, via equal cardinality.
  have hmap : (P ⊔ Y).map (MulAut.conj x : X →* X) = Q ⊔ Y := by
    have hYfix : Y.map (MulAut.conj x : X →* X) = Y := Subgroup.Normal.map_conj_eq Y x
    rw [Subgroup.map_sup, hYfix, hQ]
  have hsup : Q ⊔ Y = P ⊔ Y := by
    have hle : Q ⊔ Y ≤ P ⊔ Y := sup_le h1 le_sup_right
    have hcard : Nat.card ↥(P ⊔ Y) ≤ Nat.card ↥(Q ⊔ Y) := by
      rw [← hmap]
      exact le_of_eq (Subgroup.card_map_of_injective (K := P ⊔ Y)
        (MulAut.conj x).injective).symm
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hQp : IsPGroup p Q := by
    rw [hQ]; exact hP.map (MulAut.conj x : X →* X)
  obtain ⟨y, hy, hQy⟩ := conj_complement p P Y Q hP hQp hcop hsup.symm
  -- `P^x = P^y`, hence `y⁻¹ * x ∈ N_X(P)`, and `mk (y⁻¹ * x) = mk x`.
  have hQy' : P.map (MulAut.conj x : X →* X) = P.map (MulAut.conj y : X →* X) :=
    hQ.symm.trans hQy
  have hmem : y⁻¹ * x ∈ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc P.map (MulAut.conj (y⁻¹ * x) : X →* X)
        = P.map ((MulAut.conj y⁻¹ : X →* X).comp (MulAut.conj x : X →* X)) := by
            rw [coprime13_conj_comp]
      _ = (P.map (MulAut.conj x : X →* X)).map (MulAut.conj y⁻¹ : X →* X) := by
            rw [Subgroup.map_map]
      _ = (P.map (MulAut.conj y : X →* X)).map (MulAut.conj y⁻¹ : X →* X) := by
            rw [hQy']
      _ = P.map ((MulAut.conj y⁻¹ : X →* X).comp (MulAut.conj y : X →* X)) := by
            rw [Subgroup.map_map]
      _ = P.map (MulAut.conj (y⁻¹ * y) : X →* X) := by rw [coprime13_conj_comp]
      _ = P.map (MulAut.conj (1 : X) : X →* X) := by rw [inv_mul_cancel]
      _ = P := by rw [coprime13_conj_one_toMonoidHom, Subgroup.map_id]
  have hy1 : (QuotientGroup.mk' Y) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  have hkey : (QuotientGroup.mk' Y) (y⁻¹ * x) = QuotientGroup.mk' Y x := by
    rw [map_mul, map_inv, hy1, inv_one, one_mul]
  exact Subgroup.mem_map.mpr ⟨y⁻¹ * x, hmem, hkey⟩

/-! ## The `C_X(P)·Y/Y ≤ C_{X̄}(P̄)` inclusion -/

/-- The image of `C_X(P)` in `X ⧸ Y` is contained in the centralizer of the image of `P`. -/
theorem coprime13_centralizer_map_le (P Y : Subgroup X) [Y.Normal] :
    (Subgroup.centralizer (P : Set X)).map (QuotientGroup.mk' Y) ≤
      Subgroup.centralizer ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro c hc
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  rw [Subgroup.mem_centralizer_iff] at hc
  intro h hh
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
  rw [← map_mul, ← map_mul, hc a ha]

/-! ## The normalizer inclusion `N_X(P)·Y ≤ N_{X̄}(P̄)` -/

/-- The image of `N_X(P)` in `X ⧸ Y` normalizes the image of `P`. -/
theorem coprime13_normalizer_map_le (P Y : Subgroup X) [Y.Normal] :
    (Subgroup.normalizer (P : Set X)).map (QuotientGroup.mk' Y) ≤
      Subgroup.normalizer ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hn' : P.map (MulAut.conj n : X →* X) = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [Subgroup.map_map, coprime13_mk_comp_conj, ← Subgroup.map_map, hn']

/-- Bender 1981, 1.3: if `P` is a `p`-subgroup and `Y` is a normal `p'`-subgroup of a finite group
`X`, then in `X̄ = X/Y` one has `C_{X̄}(P̄) = C_X(P)·Y/Y` and `N_{X̄}(P̄) = N_X(P)·Y/Y`
(`P̄ = PY/Y`).  (Deliverable `Work.GW2.Coprime13Prop` of area COPR.) -/
theorem coprime13 (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (P Y : Subgroup X) [Y.Normal] (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card Y)) :
    Subgroup.centralizer
        ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) =
      (Subgroup.centralizer (P : Set X)).map (QuotientGroup.mk' Y) ∧
    Subgroup.normalizer
        ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) =
      (Subgroup.normalizer (P : Set X)).map (QuotientGroup.mk' Y) := by
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact centralizer_map_le p P Y hP hcop
  · exact coprime13_centralizer_map_le P Y
  · exact coprime13_normalizer_le p P Y hP hcop
  · exact coprime13_normalizer_map_le P Y

end Work.COPR
