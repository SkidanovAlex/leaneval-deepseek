import Mathlib
import Submission.Work.ThreePoints.ThmC.app3_1_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

theorem app3D_stabilizer {F Ω : Type} [Group F] [MulAction F Ω] (a : Ω) {K A : Subgroup F}
    (hK : K.Normal) (hA : A.Normal) (hKfix : K ≤ Work.ThreePoints.ThmC.actKer F Ω)
    (hAinf : A ⊓ MulAction.stabilizer F a ≤ K) :
    ∀ x ∈ A ⊔ K, x • a = a → ∀ ω : Ω, x • ω = ω := by
  have _hK := hK
  intro x hx hxa ω
  haveI := hA
  obtain ⟨a', ha', k, hk, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := A) (t := K)).mp hx
  have hkfix : ∀ c : Ω, k • c = c :=
    fun c => Work.ThreePoints.ThmC.mem_actKer.mp (hKfix hk) c
  have hafix : ∀ c : Ω, a' • c = c := by
    have h1 : a' ∈ MulAction.stabilizer F a := by
      rw [MulAction.mem_stabilizer_iff]
      have h2 : (a' * k) • a = a := hxa
      rwa [mul_smul, hkfix a] at h2
    have haK : a' ∈ K := hAinf ⟨ha', h1⟩
    exact fun c => Work.ThreePoints.ThmC.mem_actKer.mp (hKfix haK) c
  rw [mul_smul, hkfix ω, hafix ω]

end Work.AppXIShadow
