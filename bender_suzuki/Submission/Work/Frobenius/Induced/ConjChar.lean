import Mathlib
import Submission.Work.Frobenius.Char
import Submission.Work.Frobenius.ClassFun
import Submission.Work.Frobenius.Irr.charPair_irr_eq_ite
import Submission.Work.Frobenius.Irr.isIrr_one
import Submission.Work.Frobenius.Induction.charPair_eq_finrank_intertwiningMap
import Submission.Work.Frobenius.Induction.charPair_indFun_resFun
import Submission.Work.Frobenius.Induction.isClassFun_indFun
import Submission.Work.Frobenius.VChar.vchar_norm_one
import Submission.Work.Frobenius.Bridge.mem_Irr_iff_coherence
import Submission.Work.Frobenius.Bridge.isVChar_iff_coherence
import Submission.Work.Clifford.conjFun_mem_Irr
import Submission.Work.Clifford.CoherenceBridge

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugation of functions on a normal subgroup (Frobenius area)

For a normal subgroup `K ⊴ G` and an element `h : G`, the conjugate `θ^h` of a function
`θ : K → ℂ` is `k ↦ θ (h * k * h⁻¹)`.  This is the function `Work.Clifford.conjFun`, copied
here so that the Frobenius area has its own vocabulary; `conjChar_eq_conjFun` records that the
two agree, and `conjChar_mem_Irr` transfers the stability of `Irr` under conjugation
(`Work.Clifford.conjFun_mem_Irr`) to the `Work.Frobenius.Irr` set.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Induced

variable {G : Type*} [Group G]

/-- The conjugate `θ^h` of a function `θ` on a normal subgroup `K ⊴ G`:
`conjChar K h θ k = θ (h * k * h⁻¹)`. -/
def conjChar (K : Subgroup G) [hK : K.Normal] (h : G) (θ : K → ℂ) : K → ℂ :=
  fun k => θ ⟨h * (k : G) * h⁻¹, hK.conj_mem (k : G) k.2 h⟩

@[simp] theorem conjChar_apply (K : Subgroup G) [hK : K.Normal] (h : G) (θ : K → ℂ) (k : K) :
    conjChar K h θ k = θ ⟨h * (k : G) * h⁻¹, hK.conj_mem (k : G) k.2 h⟩ := rfl

@[simp] theorem conjChar_one (K : Subgroup G) [K.Normal] (θ : K → ℂ) :
    conjChar K 1 θ = θ := by
  funext k
  rw [conjChar_apply]
  congr 1
  exact Subtype.ext (by group)

theorem conjChar_mul (K : Subgroup G) [K.Normal] (g h : G) (θ : K → ℂ) :
    conjChar K (g * h) θ = conjChar K h (conjChar K g θ) := by
  funext k
  rw [conjChar_apply, conjChar_apply, conjChar_apply]
  congr 1
  exact Subtype.ext (by group)

@[simp] theorem conjChar_inv_left (K : Subgroup G) [K.Normal] (g : G) (θ : K → ℂ) :
    conjChar K g⁻¹ (conjChar K g θ) = θ := by
  rw [← conjChar_mul, mul_inv_cancel, conjChar_one]

@[simp] theorem conjChar_inv_right (K : Subgroup G) [K.Normal] (g : G) (θ : K → ℂ) :
    conjChar K g (conjChar K g⁻¹ θ) = θ := by
  rw [← conjChar_mul, inv_mul_cancel, conjChar_one]

/-- `conjChar` is `Work.Clifford.conjFun`. -/
theorem conjChar_eq_conjFun (K : Subgroup G) [K.Normal] (h : G) (θ : K → ℂ) :
    conjChar K h θ = Work.Clifford.conjFun K h θ := rfl

section Fintype

variable [Fintype G]

local instance instFintypeSubgroupConjChar (K : Subgroup G) : Fintype K := Fintype.ofFinite K

/-- The conjugate of an irreducible character of a normal subgroup is irreducible. -/
theorem conjChar_mem_Irr {K : Subgroup G} [K.Normal] (h : G) {θ : K → ℂ}
    (hθ : θ ∈ Irr K) : conjChar K h θ ∈ Irr K := by
  have hθc : θ ∈ Work.Coherence.Irr K :=
    (Bridge.mem_Irr_bridge (G := K)).mp hθ
  have hθcli : θ ∈ Work.Clifford.Irr K :=
    (Work.Clifford.mem_Irr_iff_coherence (G := K)).mpr hθc
  have hres : Work.Clifford.conjFun K h θ ∈ Work.Clifford.Irr K :=
    Work.Clifford.conjFun_mem_Irr h hθcli
  have hresc : Work.Clifford.conjFun K h θ ∈ Work.Coherence.Irr K :=
    (Work.Clifford.mem_Irr_iff_coherence (G := K)).mp hres
  rw [conjChar_eq_conjFun]
  exact (Bridge.mem_Irr_bridge (G := K)).mpr hresc

end Fintype

end Work.Frobenius.Induced
