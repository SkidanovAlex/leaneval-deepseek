import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma3_delta
import Submission.Work.Higman.higman_lemma3_base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]
variable {A : Subgroup P}

/-- The `P`-level conjugation defect `w⁻¹ a w a⁻¹` is the value of the `A`-level derivation
`deltaA`; the two differ only by the (abelian) reassociation `a⁻¹ (w⁻¹ a w) = (w⁻¹ a w) a⁻¹`. -/
lemma conj_defect_eq_deltaA (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (w : P) (a : ↥A) :
    w⁻¹ * (a : P) * w * (a : P)⁻¹
      = ((deltaA (C := ⊤) hAn ⟨w, Subgroup.mem_top w⟩ a : ↥A) : P) := by
  rw [deltaA_coe]
  have hconj : w⁻¹ * ((a : P) * w) ∈ A := by
    have hh := hAn.conj_mem (a : P) a.2 w⁻¹
    simpa [mul_assoc] using hh
  rw [hAb (a : P)⁻¹ (A.inv_mem a.2) (w⁻¹ * ((a : P) * w)) hconj]
  group

/-- `P`-level form of `deltaA_mem_powSub_four_of_mem_powSub_two`: conjugation of an element
`c ∈ A²` by any `w : P` lands in `A⁴`. -/
lemma deltaP_mem_powSub_four (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A) (w : P) {c : P}
    (hcA : c ∈ A) (hc : c ∈ powSub A 2) : w⁻¹ * c * w * c⁻¹ ∈ powSub A 4 := by
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hmem := deltaA_mem_powSub_four_of_mem_powSub_two h hA hAn hAb
    (C := ⊤) ⟨w, Subgroup.mem_top w⟩ hcA hc
  have hval : ((deltaA (C := ⊤) hAn ⟨w, Subgroup.mem_top w⟩ ⟨c, hcA⟩ : ↥A) : P)
      = w⁻¹ * c * w * c⁻¹ := by
    rw [deltaA_coe]
    have hconj : w⁻¹ * (c * w) ∈ A := by
      have hh := hAn.conj_mem c hcA w⁻¹
      simpa [mul_assoc] using hh
    rw [hAb c⁻¹ (A.inv_mem hcA) (w⁻¹ * (c * w)) hconj]
    group
  rwa [hval] at hmem

/-- The conjugation defect `δ_u(a) = u⁻¹ a u a⁻¹` (which lies in `A²` by unipotence) is
multiplicative in `u` modulo `A⁴`: `δ_{uv}(a) ≡ δ_u(a) · δ_v(a)  (mod A⁴)`.

Proof sketch.  Write `δ_u(a) = ⁅u⁻¹, a⁆`.  First `u⁻¹ a u = a · δ_u(a)` (`A` is abelian), so
`δ_{uv}(a) = v⁻¹ u⁻¹ a u v a⁻¹ = v⁻¹ (a δ_u(a)) v a⁻¹ = (v⁻¹ a v)·(v⁻¹ δ_u(a) v) · a⁻¹
= δ_u(a) δ_v(a) · X` with `X = δ_u(a)⁻¹ v⁻¹ δ_u(a) v`; since `δ_u(a) ∈ A²` (unipotence,
`commutator_mem_powSub_two`) and `A` is abelian, `X ∈ [A²,P] ⊆ A⁴`.

Alternatively: `Submission/Work/Higman/higman_lemma3_delta.lean` already contains the identity
`deltaA_mul_uv : δ_{uv}(a) = δ_u(a) * δ_v(a) * δ_v(δ_u(a))` and the lemma
`deltaA_mem_powSub_four_of_mem_powSub_two : δ_v(δ_u(a)) ∈ A⁴` for `δ_u(a) ∈ A²` (which holds by
`commutator_mem_powSub_two`); combining the two gives the claim, since `δ_u(a)δ_v(a) ∈ A`. -/
theorem delta_uv_mem_powSub_four {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A) (u v : P) (a : ↥A) :
    ((u * v)⁻¹ * (a : P) * (u * v) * (a : P)⁻¹)
      * ((u⁻¹ * (a : P) * u * (a : P)⁻¹) * (v⁻¹ * (a : P) * v * (a : P)⁻¹))⁻¹
      ∈ Work.Higman.powSub A 4 := by
  have hAn : A.Normal := hA.normal
  -- `δ_u(a) = ⁅u⁻¹, a⁆ = u⁻¹ a u a⁻¹` lies in `A²` by unipotence, hence in `A`.
  have hcA : u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ A := by
    have hh := hAn.conj_mem (a : P) a.2 u⁻¹
    rw [inv_inv] at hh
    exact A.mul_mem hh (A.inv_mem a.2)
  have hc2 : u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ Work.Higman.powSub A 2 := by
    have hh := commutator_mem_powSub_two h hA u⁻¹ (a : P) a.2
    simpa [commutatorElement_def] using hh
  -- `δ_{uv}(a) = δ_u(a) δ_v(a) δ_v(δ_u(a))` and the first two factors are inverted away,
  -- so the defect of the product is `δ_v(δ_u(a)) = v⁻¹ δ_u(a) v δ_u(a)⁻¹`.
  have hT : ((u * v)⁻¹ * (a : P) * (u * v) * (a : P)⁻¹)
      * ((u⁻¹ * (a : P) * u * (a : P)⁻¹) * (v⁻¹ * (a : P) * v * (a : P)⁻¹))⁻¹
      = v⁻¹ * (u⁻¹ * (a : P) * u * (a : P)⁻¹) * v
        * (u⁻¹ * (a : P) * u * (a : P)⁻¹)⁻¹ := by
    group
  rw [hT]
  exact deltaP_mem_powSub_four h hA v hcA hc2

end Work.Higman
