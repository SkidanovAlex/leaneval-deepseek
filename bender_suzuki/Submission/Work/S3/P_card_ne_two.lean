import Mathlib
import Submission.Work.ThmF.ChV3.Ctx

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.S3.P_card_ne_two` — `|P| ≠ 2` in the standing context of Ch. V §3

Peterfalvi II Ch. V §3 takes `P ≤ V = C_D(t)` of prime order and shows (`F1`) that `C_G(P)` has
2-rank `≥ 2` (`HasFourGroup`).  The very first thing this gives is that the prime `|P|` is **odd**,
which is the content of the present lemma: `Nat.card P ≠ 2`.

The argument is elementary.  Suppose `|P| = 2`.  Then `P` has an element `z` of order `2`
(Cauchy), and `P` is commutative (a group of order `2` has exponent `2`).  Since
`P ≤ V = C_D(t) ⊆ C_G(t)`, the involution `t` commutes with `P`, and `z ∈ P` commutes with `P`
because `P` is abelian; hence both `t` and `z` lie in `C_G(P)`.  They are distinct, because
`z ∈ P ≤ V ⊆ D ⊆ H` while `t ∉ H` (split rank-one datum).  So `t` and `z` are two distinct
commuting involutions of `C_G(P)`: `HasFourGroup ↥(C_G(P))`, contradicting (F1).  ∎

Nothing in the argument uses `s`, `r`, the structure identity, simplicity of `G`, or the
situation `(B0)`–`(B2)`; only `P_le`, `P_prime` and `F1` are used.
-/

namespace Work.S3

theorem P_card_ne_two {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) : Nat.card P ≠ 2 := by
  intro h2
  -- Cauchy: an element of `P` of order `2`.
  have hdvd : 2 ∣ Nat.card ↥P := by rw [h2]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (G := ↥P) hdvd
  have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  -- `P` is commutative: it has exponent `2`.
  have hcomm : ∀ a b : ↥P, a * b = b * a :=
    fun a b => Commute.of_orderOf_dvd_two (fun g => h2 ▸ orderOf_dvd_natCard g) a b
  have hzmem : (z : G) ∈ P := z.2
  -- `z` commutes with all of `P`
  have hzC : (z : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ z)
  -- `t` commutes with all of `P` (as `P ≤ centD H t ≤ C_G(t)`)
  have htC : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (c.P_le hy).2 t (Set.mem_singleton t)).symm
  -- `z ∈ D ⊆ H`, while `t ∉ H`
  have hzH : (z : G) ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (c.P_le hzmem)).1).1
  have htne : t ≠ (z : G) := fun h => c.split.not_mem (h ▸ hzH)
  -- `t` and `z` commute
  have htz : t * (z : G) = (z : G) * t :=
    Subgroup.mem_centralizer_iff.mp (c.P_le hzmem).2 t (Set.mem_singleton t)
  -- the four-group `⟨t, z⟩` inside `C_G(P)`, contradicting (F1)
  exact c.F1 ⟨⟨t, htC⟩, ⟨(z : G), hzC⟩,
      by rw [Subgroup.orderOf_mk]; exact c.split.invol,
      by rw [Subgroup.orderOf_mk]; exact hz2,
      fun h => htne (Subtype.ext_iff.mp h),
      Subtype.ext htz⟩

end Work.S3
