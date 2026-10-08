import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.Prove.step1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9WV`

Step (9)'s invariance of `W = C_D(K)` under conjugation by `V = C_D(t)`.

The key point is that `V` normalises the set `K = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}`: if
`a ∈ V` then `t a t⁻¹ = a` and `t a⁻¹ t⁻¹ = a⁻¹`, hence for `k ∈ K`

  `t (a k a⁻¹) t⁻¹ = (t a t⁻¹)(t k t⁻¹)(t a⁻¹ t⁻¹) = a k⁻¹ a⁻¹ = (a k a⁻¹)⁻¹`,

while `a k a⁻¹ ∈ D` because `D` is a subgroup.  It follows that `W = C_D(K)`, the centraliser
of `K` inside `D`, is `V`-invariant: for `k ∈ K` and `b ∈ W`,
`(a b a⁻¹) k = a b (a⁻¹ k a) a⁻¹ = a (a⁻¹ k a) b a⁻¹ = k (a b a⁻¹)`, using the
normalisation on `a⁻¹ k a` and the commuting of `b` with `K`.
-/

namespace Work.ThmF.Prove

open Submission.Blueprint

/-- `V = C_D(t)` normalises `K = J(D,t)`, i.e. `a k a⁻¹ ∈ K` for `a ∈ V`, `k ∈ K`. -/
theorem centD_conj_mem_Kset {G : Type} [Group G] {H : Subgroup G} {t : G} :
    ∀ a ∈ Submission.Blueprint.centD H t, ∀ k ∈ Work.ThmF.Kset H t,
      a * k * a⁻¹ ∈ Work.ThmF.Kset H t := by
  intro a ha k hk
  rw [Work.ThmF.mem_Kset_iff] at hk ⊢
  obtain ⟨hkD, hkinv⟩ := hk
  have haD : a ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp ha).1
  have hca : t * a = a * t :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 t (Set.mem_singleton t)
  have h1 : t * a * t⁻¹ = a := by rw [hca]; group
  have h2 : t * a⁻¹ * t⁻¹ = a⁻¹ := by
    rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, h1]
  constructor
  · exact mul_mem (mul_mem haD hkD) (inv_mem haD)
  · have key : t * (a * k * a⁻¹) * t⁻¹
        = (t * a * t⁻¹) * (t * k * t⁻¹) * (t * a⁻¹ * t⁻¹) := by group
    rw [key, h1, hkinv, h2]
    group

theorem step9WV {G : Type} [Group G] {H : Subgroup G} {t : G} :
    ∀ a ∈ Submission.Blueprint.centD H t, ∀ b ∈ Work.ThmF.W H t,
      a * b * a⁻¹ ∈ Work.ThmF.W H t := by
  intro a ha b hb
  rw [Work.ThmF.le_W_iff] at hb ⊢
  obtain ⟨hbV, hbcomm⟩ := hb
  refine ⟨?_, ?_⟩
  · exact mul_mem (mul_mem ha hbV) (inv_mem ha)
  · intro k hk
    have hka : a⁻¹ * k * a ∈ Work.ThmF.Kset H t :=
      by simpa using centD_conj_mem_Kset a⁻¹ (inv_mem ha) k hk
    have hcomm := hbcomm (a⁻¹ * k * a) hka
    calc k * (a * b * a⁻¹)
        = a * ((a⁻¹ * k * a) * b) * a⁻¹ := by group
      _ = a * (b * (a⁻¹ * k * a)) * a⁻¹ := by rw [hcomm]
      _ = (a * b * a⁻¹) * k := by group

end Work.ThmF.Prove
