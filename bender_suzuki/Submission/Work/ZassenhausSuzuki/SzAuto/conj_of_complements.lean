import Mathlib
import Submission.Work.Hall.SchurZassenhaus.hall_sz_conj_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzAuto

set_option linter.style.haveILetI false

open scoped Pointwise

/-- Conjugation by an element `b` of a subgroup `B` stabilises `B`. -/
lemma map_conj_eq_self_of_mem {G : Type*} [Group G] {B : Subgroup G} {b : G} (hb : b ∈ B) :
    B.map (MulAut.conj b).toMonoidHom = B := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    show b * y * b⁻¹ ∈ B
    exact B.mul_mem (B.mul_mem hb hy) (B.inv_mem hb)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨b⁻¹ * x * b, ?_, ?_⟩
    · show b⁻¹ * x * b ∈ B
      exact B.mul_mem (B.mul_mem (B.inv_mem hb) hx) hb
    · show b * (b⁻¹ * x * b) * b⁻¹ = x
      group

/-- Conjugating by `k * b` with `b ∈ B` acts on the subgroup `B` the same way as conjugating
by `k`. -/
lemma map_conj_mul_eq_map_conj {G : Type*} [Group G] {B : Subgroup G} {b k : G} (hb : b ∈ B) :
    B.map (MulAut.conj (k * b)).toMonoidHom = B.map (MulAut.conj k).toMonoidHom := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨b * y * b⁻¹, B.mul_mem (B.mul_mem hb hy) (B.inv_mem hb), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro x ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ⟨b⁻¹ * z * b, B.mul_mem (B.mul_mem (B.inv_mem hb) hz) hb, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- If `A = B ^ g` for some `g : G`, and `B ⊔ K = ⊤` is a complement decomposition with `K`
normal, then the conjugating element can be chosen in `K`. -/
lemma exists_mem_conj_of_map_conj_eq {G : Type*} [Group G] {B K : Subgroup G} [K.Normal]
    (hBK : B ⊔ K = ⊤) {A : Subgroup G} {g : G}
    (hg : A = B.map (MulAut.conj g).toMonoidHom) :
    ∃ k ∈ K, A = B.map (MulAut.conj k).toMonoidHom := by
  have hgmem : g ∈ K ⊔ B := by rw [sup_comm, hBK]; exact Subgroup.mem_top g
  obtain ⟨k, hk, b, hb, hkb⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K) (t := B)).mp hgmem
  refine ⟨k, hk, ?_⟩
  rw [hg, ← hkb]
  exact map_conj_mul_eq_map_conj hb

theorem conj_of_complements {E : Type} [Group E] [Finite E]
    (K : Subgroup E) [K.Normal] (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcop : Nat.Coprime (Nat.card K) K.index)
    (A B : Subgroup E) (hA : A ⊔ K = ⊤) (hA' : A ⊓ K = ⊥)
    (hB : B ⊔ K = ⊤) (hB' : B ⊓ K = ⊥) :
    ∃ k ∈ K, A = B.map (MulAut.conj k).toMonoidHom := by
  haveI : IsMulCommutative K :=
    IsMulCommutative.of_comm (fun a b : K => Subtype.ext (hKab a a.2 b b.2))
  have hKA : K.IsComplement' A := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le, inf_comm, hA']
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ K ⊔ A := by rw [sup_comm, hA]; exact Subgroup.mem_top x
      obtain ⟨k, hk, a, ha, hka⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := K) (t := A)).mp hx
      exact Set.mem_mul.mpr ⟨k, hk, a, ha, hka⟩
  have hKB : K.IsComplement' B := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le, inf_comm, hB']
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ K ⊔ B := by rw [sup_comm, hB]; exact Subgroup.mem_top x
      obtain ⟨k, hk, b, hb, hkb⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := K) (t := B)).mp hx
      exact Set.mem_mul.mpr ⟨k, hk, b, hb, hkb⟩
  obtain ⟨g, hg⟩ :=
    Work.Hall.SchurZassenhaus.hall_sz_conj_abelian (N := K) (H := B) (K := A) hcop hKB hKA
  exact exists_mem_conj_of_map_conj_eq hB hg

end Work.ZassenhausSuzuki.SzAuto
