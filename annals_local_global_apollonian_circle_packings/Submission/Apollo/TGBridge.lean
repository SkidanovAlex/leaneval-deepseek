/-
Bridge between the curvature set of the (-3,5,8,8) packing (as the orbit of
the *TransformationGroup*, which also allows coordinate permutations) and the
values of the Apollonian-group orbit `apOrbit`.

Main result: `curvatureSet pack0 = apValues`.  The proof: every
TransformationGroup element reduces to (Apollonian element) · (permutation):
applying an S-move word to a permuted vector is the same as permuting an
S-move word with permuted indices (`apollonian_perm`, from the relabeling
equivariance `Relabel.relabel_move`), and permutations preserve coordinate
value sets (`perm_range`).  Hence every curvature is an apOrbit value and
conversely.
-/
import Submission.Apollo.Defs
import Submission.Apollo.Relabel
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open LocalGlobalApollonianCirclePackings
open Matrix
open scoped Pointwise
namespace Apollo

def Hsub : Subgroup (GL (Fin 4) ℤ) := permMatrixHom.toHomUnits.range

lemma Hsub_mem_iff (x : GL (Fin 4) ℤ) :
    x ∈ Hsub ↔ ∃ σ : Equiv.Perm (Fin 4), x = permMatrixHom.toHomUnits σ := by
  constructor
  · intro hx
    rcases (MonoidHom.mem_range.mp hx) with ⟨σ, hσ⟩
    exact ⟨σ, hσ.symm⟩
  · rintro ⟨σ, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩

lemma ap_le_tg : ApollonianGroup ≤ TransformationGroup := by
  intro x hx
  exact Subgroup.mem_sup_left hx

lemma h_le_tg : Hsub ≤ TransformationGroup := by
  intro x hx
  exact Subgroup.mem_sup_right hx

lemma tg_eq_closure : TransformationGroup = Subgroup.closure (↑ApollonianGroup ∪ ↑Hsub) := by
  exact Subgroup.sup_eq_closure ApollonianGroup Hsub

-- permutation action facts
lemma perm_smul_apply (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) (i : Fin 4) :
    ((permMatrixHom.toHomUnits σ : GL (Fin 4) ℤ) • v) i = v (σ.symm i) := by
  simp [LocalGlobalApollonianCirclePackings.GeneralLinearGroup.smul_def,
    MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]

lemma perm_smul_comp (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) :
    ((permMatrixHom.toHomUnits σ : GL (Fin 4) ℤ) • v) = v ∘ σ.symm := by
  funext i
  rw [perm_smul_apply]
  rfl

lemma perm_range (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) :
    Set.range ((permMatrixHom.toHomUnits σ : GL (Fin 4) ℤ) • v) = Set.range v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨σ.symm i, ?_⟩
    rw [perm_smul_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨σ i, ?_⟩
    rw [perm_smul_apply, Equiv.symm_apply_apply]

lemma gen_perm_comp (σ : Equiv.Perm (Fin 4)) (k : Fin 4) (v : Fin 4 → ℤ) :
    gen k • (v ∘ σ) = (gen (σ k) • v) ∘ σ := by
  have h := relabel_move σ.symm v (σ k)
  simpa using h

theorem apollonian_perm (a : GL (Fin 4) ℤ) (ha : a ∈ ApollonianGroup)
    (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ) :
    ∃ b : GL (Fin 4) ℤ, b ∈ ApollonianGroup ∧ a • (v ∘ σ) = (b • v) ∘ σ := by
  rw [apollonianGroup_eq_closure] at ha
  refine (Subgroup.closure_induction_left
    (s := gens) (p := fun g _ => ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ℤ),
      ∃ b : GL (Fin 4) ℤ, b ∈ ApollonianGroup ∧ g • (v ∘ σ) = (b • v) ∘ σ)
    ?one ?mulL ?invC (x := a) ha) σ v
  · intro σ v
    refine ⟨1, one_mem ApollonianGroup, ?_⟩
    simp
  · intro x hx y hy ih σ v
    rcases hx with ⟨i, rfl⟩
    rcases ih σ v with ⟨b, hb, hEq⟩
    refine ⟨gen (σ i) * b, ?_, ?_⟩
    · have hmem : gen (σ i) ∈ gens := ⟨σ i, rfl⟩
      rw [apollonianGroup_eq_closure]
      exact Subgroup.mul_mem (Subgroup.closure gens) (Subgroup.subset_closure hmem)
        (by simpa [apollonianGroup_eq_closure] using hb)
    · calc
        (gen i * y) • (v ∘ σ) = gen i • (y • (v ∘ σ)) := by rw [mul_smul]
        _ = gen i • ((b • v) ∘ σ) := by rw [hEq]
        _ = (gen (σ i) • (b • v)) ∘ σ := gen_perm_comp σ i (b • v)
        _ = ((gen (σ i) * b) • v) ∘ σ := by rw [mul_smul]
  · intro x hx y hy ih σ v
    rcases hx with ⟨i, rfl⟩
    rcases ih σ v with ⟨b, hb, hEq⟩
    refine ⟨gen (σ i) * b, ?_, ?_⟩
    · have hmem : gen (σ i) ∈ gens := ⟨σ i, rfl⟩
      rw [apollonianGroup_eq_closure]
      exact Subgroup.mul_mem (Subgroup.closure gens) (Subgroup.subset_closure hmem)
        (by simpa [apollonianGroup_eq_closure] using hb)
    · calc
        ((gen i)⁻¹ * y) • (v ∘ σ) = gen i • (y • (v ∘ σ)) := by rw [gen_inv i, mul_smul]
        _ = gen i • ((b • v) ∘ σ) := by rw [hEq]
        _ = (gen (σ i) • (b • v)) ∘ σ := gen_perm_comp σ i (b • v)
        _ = ((gen (σ i) * b) • v) ∘ σ := by rw [mul_smul]

/-- inverse of a permutation matrix is the matrix of the inverse permutation. -/
lemma perm_inv (τ : Equiv.Perm (Fin 4)) :
    ((permMatrixHom.toHomUnits τ : GL (Fin 4) ℤ)⁻¹) = permMatrixHom.toHomUnits τ.symm := by
  apply Units.ext
  have h1 := map_inv (f := (permMatrixHom.toHomUnits : Equiv.Perm (Fin 4) →* GL (Fin 4) ℤ)) τ
  have hsym : τ⁻¹ = τ.symm := rfl
  rw [← h1, hsym]

/-- every TransformationGroup image of q0v is a permutation of an Apollonian
image: g • q0v = (a • q0v) ∘ σ. -/
theorem tg_reduce (g : GL (Fin 4) ℤ) (hg : g ∈ TransformationGroup) :
    ∃ a : GL (Fin 4) ℤ, a ∈ ApollonianGroup ∧
      ∃ σ : Equiv.Perm (Fin 4), g • q0v = (a • q0v) ∘ σ := by
  rw [tg_eq_closure] at hg
  -- property: products with S (Ap ∪ H) elements can be pushed to the right of an Ap factor
  refine (Subgroup.closure_induction_left
    (s := (↑ApollonianGroup ∪ ↑Hsub : Set (GL (Fin 4) ℤ)))
    (p := fun h _ => ∃ a : GL (Fin 4) ℤ, a ∈ ApollonianGroup ∧
      ∃ σ : Equiv.Perm (Fin 4), h • q0v = (a • q0v) ∘ σ) ?base ?mul ?inv (x := g) hg)
  · -- base: h = 1
    refine ⟨1, one_mem ApollonianGroup, 1, ?_⟩
    simp
  · -- left-multiply by x ∈ Ap ∪ Hsub
    intro x hx y hy ih
    rcases hx with hxA | hxH
    · -- x ∈ ApollonianGroup
      rcases ih with ⟨a, ha, σ, hEq⟩
      have hperm := apollonian_perm x hxA σ (a • q0v)
      rcases hperm with ⟨b, hb, hbEq⟩
      refine ⟨b * a, Subgroup.mul_mem ApollonianGroup hb ha, σ, ?_⟩
      calc
        (x * y) • q0v = x • (y • q0v) := by rw [mul_smul]
        _ = x • ((a • q0v) ∘ σ) := by rw [hEq]
        _ = (b • (a • q0v)) ∘ σ := hbEq
        _ = ((b * a) • q0v) ∘ σ := by rw [mul_smul]
    · -- x ∈ Hsub: a permutation
      rcases (Hsub_mem_iff x).1 hxH with ⟨τ, rfl⟩
      rcases ih with ⟨a, ha, σ, hEq⟩
      refine ⟨a, ha, (τ.symm).trans σ, ?_⟩
      calc
        ((permMatrixHom.toHomUnits τ : GL (Fin 4) ℤ) * y) • q0v
            = (permMatrixHom.toHomUnits τ : GL (Fin 4) ℤ) • (y • q0v) := by rw [mul_smul]
        _ = (permMatrixHom.toHomUnits τ : GL (Fin 4) ℤ) • ((a • q0v) ∘ σ) := by rw [hEq]
        _ = ((a • q0v) ∘ σ) ∘ τ.symm := perm_smul_comp τ ((a • q0v) ∘ σ)
        _ = (a • q0v) ∘ ((τ.symm).trans σ) := by rfl
  · intro x hx y hy ih
    -- x⁻¹ ∈ Ap ∪ Hsub:
    rcases hx with hxA | hxH
    · have hxAi : x⁻¹ ∈ ApollonianGroup := inv_mem hxA
      rcases ih with ⟨a, ha, σ, hEq⟩
      rcases apollonian_perm x⁻¹ hxAi σ (a • q0v) with ⟨b, hb, hbEq⟩
      refine ⟨b * a, Subgroup.mul_mem ApollonianGroup hb ha, σ, ?_⟩
      calc
        (x⁻¹ * y) • q0v = x⁻¹ • (y • q0v) := by rw [mul_smul]
        _ = x⁻¹ • ((a • q0v) ∘ σ) := by rw [hEq]
        _ = (b • (a • q0v)) ∘ σ := hbEq
        _ = ((b * a) • q0v) ∘ σ := by rw [mul_smul]
    · rcases (Hsub_mem_iff x).1 hxH with ⟨τ, hxτ⟩
      rcases ih with ⟨a, ha, σ, hEq⟩
      refine ⟨a, ha, τ.trans σ, ?_⟩
      calc
        (x⁻¹ * y) • q0v = x⁻¹ • (y • q0v) := by rw [mul_smul]
        _ = x⁻¹ • ((a • q0v) ∘ σ) := by rw [hEq]
        _ = ((a • q0v) ∘ σ) ∘ τ := by
          rw [hxτ]
          rw [perm_inv]
          rw [perm_smul_comp]
          rfl
        _ = (a • q0v) ∘ (τ.trans σ) := by rfl



/-- every value of a TransformationGroup image of q0v is an Apollonian orbit
value. -/
theorem tg_value_mem (g : GL (Fin 4) ℤ) (hg : g ∈ TransformationGroup) (x : ℤ) :
    x ∈ Set.range (g • q0v) → x ∈ apValues := by
  intro hx
  rcases tg_reduce g hg with ⟨a, ha, σ, hEq⟩
  rcases hx with ⟨i, hi⟩
  refine mem_apValues_iff.mpr ⟨a • q0v, ?_, σ i, ?_⟩
  · rw [apOrbit]
    exact ⟨a, ha, rfl⟩
  · rw [← hi]
    change ((a • q0v) ∘ σ) i = (g • q0v) i
    exact congrArg (fun w : Fin 4 → ℤ => w i) hEq.symm

/-- the packing quadruple of (-3,5,8,8) (raw). -/
def q0s : integralPrimitiveDescartesQuadruple := ⟨q0v, by decide⟩

/-- the packing of (-3,5,8,8) as a quotient. -/
def pack0 : PrimitiveApollonianCirclePacking := Quotient.mk'' q0s

/-- The curvature set of the (-3,5,8,8) packing is exactly the set of all
Apollonian-orbit values. -/
theorem curvatureSet_eq_apValues : curvatureSet pack0 = apValues := by
  ext x
  constructor
  · intro hx
    rw [curvatureSet] at hx
    rw [Set.mem_iUnion₂] at hx
    rcases hx with ⟨v, hv, hxr⟩
    rcases (Set.mem_range.mp hxr) with ⟨i, hxi⟩
    have hmk : Quotient.mk'' v = pack0 := (MulAction.orbitRel.Quotient.mem_orbit).1 hv
    have hrel : (MulAction.orbitRel TransformationGroup integralPrimitiveDescartesQuadruple).r v q0s := by
      exact Quotient.exact (by simpa [pack0] using hmk)
    have hmem : v ∈ MulAction.orbit TransformationGroup q0s := (MulAction.orbitRel_apply.mp hrel)
    rcases hmem with ⟨g, hg_eq⟩
    have hvec : v.1 = (g : GL (Fin 4) ℤ) • q0v := by
      rw [← hg_eq]
      rfl
    have hx2 : x ∈ Set.range ((g : GL (Fin 4) ℤ) • q0v) := by
      rw [← hvec]
      exact ⟨i, hxi⟩
    exact tg_value_mem (g : GL (Fin 4) ℤ) g.2 x hx2
  · intro hx
    rcases (mem_apValues_iff.mp hx) with ⟨w, hw, i, rfl⟩
    rcases hw with ⟨a, ha, hwEq⟩
    have haTG : a ∈ TransformationGroup := ap_le_tg ha
    let g : TransformationGroup := ⟨a, haTG⟩
    let v : integralPrimitiveDescartesQuadruple := g • q0s
    rw [curvatureSet]
    rw [Set.mem_iUnion₂]
    refine ⟨v, ?_, ?_⟩
    · dsimp [pack0]
      rw [MulAction.mem_orbit_iff]
      refine ⟨g, ?_⟩
      rfl
    · refine ⟨i, ?_⟩
      have hsub : v.1 = a • q0v := by
        dsimp [v, g, q0s]
        rfl
      rw [hsub, hwEq]


/-- Same statement in the exact shape used by the challenge theorem: the
curvature set of the (-3,5,8,8) packing equals the Apollonian-orbit values. -/
theorem curvatureSet_q0v :
    curvatureSet (⟦(⟨![-3, 5, 8, 8], by decide⟩ : integralPrimitiveDescartesQuadruple)⟧) = apValues := by
  have hp : pack0 = ⟦(⟨![-3, 5, 8, 8], by decide⟩ : integralPrimitiveDescartesQuadruple)⟧ := by
    apply Quotient.sound
    refine ⟨1, ?_⟩
    simp [pack0, q0s, q0v]
  rw [← hp]
  exact curvatureSet_eq_apValues

end Apollo
