import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.GLUE.Defs

namespace Work.BG

/-- Conjugate elements of a group have the same image in its abelianization. -/
lemma abelianization_of_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Abelianization.of a = Abelianization.of b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, map_mul, map_mul, map_inv]
  simp

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG (G10).** The involution `t` lies in the commutator subgroup `G' = ⁅G, G⁆`.

In the abelianization `A = G/G'` conjugation is trivial, so the single-class-of-involutions
hypothesis forces `t₁`, `t₂` and `t` to have the *same* image `s ∈ A`; but `t ∈ ⟨t₁ t₂⟩`
(`D.gen`, `D.t_mem`), say `t = (t₁t₂)^k`, and `t₁` is an involution, so `s² = 1` and
`φ(t) = (s·s)^k = (s²)^k = 1`.  Hence `t ∈ ker φ = G'`. -/
theorem tDerived : Work.GW2.C16.TDerivedProp := by
  intro G _ _ D
  rw [← Abelianization.ker_of G, MonoidHom.mem_ker]
  -- `t ∈ ⟨t₁ t₂⟩`, so `t = (t₁ t₂)^k`.
  have ht : D.t ∈ Subgroup.zpowers (D.t1 * D.t2) := by
    rw [← D.gen]
    exact D.t_mem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  -- All involutions have the same image in the abelianization (they are all conjugate).
  have h1 : Abelianization.of D.t1 = Abelianization.of D.t :=
    abelianization_of_eq_of_isConj (D.oneClass D.t1 D.t D.t1_order D.t_order)
  have h2 : Abelianization.of D.t2 = Abelianization.of D.t :=
    abelianization_of_eq_of_isConj (D.oneClass D.t2 D.t D.t2_order D.t_order)
  have hsq : (Abelianization.of D.t) ^ 2 = 1 := by
    have ht2 : D.t ^ 2 = 1 := by
      have := pow_orderOf_eq_one D.t
      rwa [D.t_order] at this
    rw [← map_pow, ht2, map_one]
  calc Abelianization.of D.t = (Abelianization.of (D.t1 * D.t2)) ^ k := by rw [← hk, map_zpow]
    _ = (Abelianization.of D.t1 * Abelianization.of D.t2) ^ k := by rw [map_mul]
    _ = (Abelianization.of D.t * Abelianization.of D.t) ^ k := by rw [h1, h2]
    _ = ((Abelianization.of D.t) ^ 2) ^ k := by rw [← pow_two]
    _ = 1 := by rw [hsq, one_zpow]

end Work.BG
