import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.NormalComplement.AppVII

/-- If `Q` is a normal subgroup of `G` and `z` is central in `Q`, then the conjugate
`g z g⁻¹` (which lies in `Q` by normality) is again central in `Q`. -/
lemma center_conj_mem {G : Type*} [Group G] {Q : Subgroup G} (hQ : Q.Normal) {z : ↥Q}
    (hz : z ∈ Subgroup.center ↥Q) (g : G) :
    (⟨g * (z : G) * g⁻¹, hQ.conj_mem (z : G) z.2 g⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  have hkey : (⟨g⁻¹ * (u : G) * g, hQ.conj_mem' (u : G) u.2 g⟩ : ↥Q) * z
      = z * (⟨g⁻¹ * (u : G) * g, hQ.conj_mem' (u : G) u.2 g⟩ : ↥Q) :=
    (Subgroup.mem_center_iff.mp hz) _
  have hkey' : (g⁻¹ * (u : G) * g) * (z : G) = (z : G) * (g⁻¹ * (u : G) * g) := by
    simpa using congrArg Subtype.val hkey
  show (u : G) * (g * (z : G) * g⁻¹) = (g * (z : G) * g⁻¹) * (u : G)
  calc (u : G) * (g * (z : G) * g⁻¹)
      = g * ((g⁻¹ * (u : G) * g) * (z : G)) * g⁻¹ := by group
    _ = g * ((z : G) * (g⁻¹ * (u : G) * g)) * g⁻¹ := by rw [hkey']
    _ = (g * (z : G) * g⁻¹) * (u : G) := by group

/-- **Key step of Peterfalvi Appendix VII, Part 1.**  Let `Q ◁ A` be a non-commutative finite
group such that every proper non-trivial `P`-invariant subgroup `Q' ≤ Q` is centralised by `P`
(`hcent`).  Then `P` centralises the centre of `Q`.

Indeed `Z := Z(Q)` (viewed inside `A`) is a normal subgroup of `A`: it is contained in `Q`, its
image under `Q.subtype` is the centre of `Q` which is fixed by all automorphisms of `Q`, and `Q` is
normal.  Hence `P` normalises `Z`, so `⁅P, Z⁆ ≤ Z`, and `hcent` applies to `Z` (which is a proper
subgroup of the non-commutative `Q` whenever it is non-trivial). -/
theorem center_map_le_centralizer {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    {q : ℕ} (hq : q.Prime) (hQp : IsPGroup q ↥Q) (hnab : ¬ IsMulCommutative ↥Q)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.centralizer (P : Set A) := by
  set Z : Subgroup A := (Subgroup.center ↥Q).map Q.subtype with hZ
  -- `Z ≤ Q`
  have hZQ : Z ≤ Q := by
    rw [hZ]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, _hz, rfl⟩
    exact z.2
  -- `Z` is normal in `A`
  have hZnorm : Z.Normal := by
    rw [hZ]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map.mpr
      ⟨⟨g * (z : A) * g⁻¹, hQn.conj_mem (z : A) z.2 g⟩, center_conj_mem hQn hz g, rfl⟩
  -- hence `⁅P, Z⁆ ≤ Z`
  have hcomm : ⁅P, Z⁆ ≤ Z := by
    haveI : Z.Normal := hZnorm
    exact Subgroup.commutator_le_right (H₁ := P) (H₂ := Z)
  -- `Z ≠ Q` since `Q` is not commutative
  have hZneQ : Z ≠ Q := by
    intro h
    apply hnab
    have hcenter : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rcases Subgroup.mem_map.mp (h.ge y.2) with ⟨w, hw, hweq⟩
      have : w = y := Q.subtype_injective hweq
      simpa [this] using hw
    exact Subgroup.center_eq_top_iff.mp hcenter
  by_cases hZbot : Z = ⊥
  · rw [hZbot]
    exact bot_le
  · have h1 : ⁅P, Z⁆ = ⊥ := hcent Z hZQ hZbot hZneQ hcomm
    have h2 : P ≤ Subgroup.centralizer (Z : Set A) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    exact Subgroup.le_centralizer_iff.mp h2

end Work.NormalComplement.AppVII
