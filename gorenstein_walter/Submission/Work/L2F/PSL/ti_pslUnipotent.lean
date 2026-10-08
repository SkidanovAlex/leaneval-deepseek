import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.Mat2.conj_unipotent_entry
import Submission.Work.L2F.PSL.pslMap_eq_iff
import Submission.Work.L2F.PSL.pslMap_mem_normalizer_pslUnipotent

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- The `(1,0)`-entry of any element of the upper unipotent subgroup of `SL(2,F)` vanishes:
such an element is `unipotent b = !![1,b;0,1]`. -/
lemma unipotentSubgroup_entry10 (F : Type*) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin 2) F) (hu : u ∈ Work.L2F.unipotentSubgroup F) :
    (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [Work.L2F.unipotentSubgroup, Work.PSL2.unipotentSubgroup] at hu
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hu
  change (((Work.PSL2.unipotent F (Multiplicative.toAdd m) :
      Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0
  rw [Work.PSL2.coe_unipotent]
  simp

/-- Multiplying by the central element `-1` does not change the vanishing of the `(1,0)`-entry
of a matrix (the central element is diagonal). -/
lemma negOne_mul_entry10 (F : Type*) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin 2) F)
    (hu : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((Work.L2F.negOne F * u : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have hneg : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 := rfl
  rw [hneg, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_apply, hu, neg_zero]

/-- `pslUnipotent F` is a TI subgroup of `PSL(2,F)` (odd characteristic): its conjugates by
elements outside its normalizer meet it trivially.  Proof: if `1 ≠ z ∈ Q ⊓ Q^g` then `z = π(u)`
with `u` a nontrivial unipotent matrix, `z ∈ Q^g` gives `g⁻¹ u g ∈ U·{±1}`, and the `-` sign is
excluded by the trace (`tr (g⁻¹ug) = tr u = 2 ≠ -2 = tr (-u')`); so `g⁻¹ug = u'` is unipotent, and
then `u` and `u'` have the same `1`-eigenspace `F·e₀` (a nontrivial unipotent matrix fixes a unique
line), which forces `g` to preserve `F·e₀`, i.e. `g` is upper triangular, so `π(g)` normalizes `Q`. -/
theorem ti_pslUnipotent (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hg : g ∉ Subgroup.normalizer (Work.L2F.pslUnipotent F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :
    Work.L2F.pslUnipotent F ⊓
        (Work.L2F.pslUnipotent F).map (MulAut.conj g).toMonoidHom = ⊥ := by
  -- It suffices to show that every element of the intersection is `1`.
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzQ, hzQg⟩ := hz
  rw [Subgroup.mem_bot]
  by_contra hzne
  -- `z` is the image of an upper unipotent matrix `u = unipotent b` with `b ≠ 0`.
  obtain ⟨u, hu, hu_eq⟩ := Subgroup.mem_map.mp hzQ
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hu
  have hu_unip : u = Work.PSL2.unipotent F (Multiplicative.toAdd m) := by rw [← hm]; rfl
  have hu_ne_one : u ≠ 1 := by intro h; exact hzne (by rw [← hu_eq, h, map_one])
  have hb : (Multiplicative.toAdd m : F) ≠ 0 := by
    intro hb0
    have h1 : Work.PSL2.unipotent F (Multiplicative.toAdd m) = 1 :=
      (unipotent_eq_one_iff F (Multiplicative.toAdd m)).mpr hb0
    exact hu_ne_one (by rw [hu_unip, h1])
  -- `z ∈ Q^g` gives `g⁻¹ z g ∈ Q`, i.e. `π (G⁻¹ u G) = π u'` for some `u' ∈ U`.
  have hzQg' : g⁻¹ * z * g ∈ Work.L2F.pslUnipotent F := by
    obtain ⟨y, hy, hyconj⟩ := Subgroup.mem_map.mp hzQg
    change g * y * g⁻¹ = z at hyconj
    have : g⁻¹ * z * g = y := by rw [← hyconj]; group
    rw [this]; exact hy
  obtain ⟨u', hu', hu'_eq⟩ := Subgroup.mem_map.mp hzQg'
  -- Lift `g` to `G ∈ SL(2,F)`.
  obtain ⟨G, hG_eq⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2,F))) g
  have hpg : Work.PSL2.pslMap F G = g := hG_eq
  have hkey : Work.PSL2.pslMap F (G⁻¹ * u * G) = Work.PSL2.pslMap F u' := by
    rw [map_mul, map_mul, map_inv, hpg, hu_eq, hu'_eq]
  -- Hence `G⁻¹ u G = u'` or `G⁻¹ u G = -u'`; in both cases its `(1,0)`-entry vanishes.
  have hcases := (pslMap_eq_iff F h2 (G⁻¹ * u * G) u').mp hkey
  have hentry0 : ((G⁻¹ * u * G : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rcases hcases with hh | hh
    · rw [hh]; exact unipotentSubgroup_entry10 F u' hu'
    · rw [hh]; exact negOne_mul_entry10 F u' (unipotentSubgroup_entry10 F u' hu')
  -- The explicit `(1,0)`-entry of the conjugate is `-(G 1 0)^2 * b`.
  have hformula : ((G⁻¹ * u * G : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0
      = -(((G : Matrix (Fin 2) (Fin 2) F) 1 0)^2) * (Multiplicative.toAdd m) := by
    rw [hu_unip]
    exact Work.L2F.Mat2.conj_unipotent_entry F G (Multiplicative.toAdd m)
  -- Therefore `G` is upper triangular.
  have hG10 : (G : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have hzero : -(((G : Matrix (Fin 2) (Fin 2) F) 1 0)^2) * (Multiplicative.toAdd m) = 0 := by
      rw [← hformula]; exact hentry0
    have h' : -(((G : Matrix (Fin 2) (Fin 2) F) 1 0)^2) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hb
    have hsq : ((G : Matrix (Fin 2) (Fin 2) F) 1 0)^2 = 0 := neg_eq_zero.mp h'
    have : ((G : Matrix (Fin 2) (Fin 2) F) 1 0) * ((G : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
      rwa [pow_two] at hsq
    exact mul_self_eq_zero.mp this
  -- An upper triangular `G` normalizes `Q`, contradicting `hg`.
  exact hg (by rw [← hpg]; exact pslMap_mem_normalizer_pslUnipotent F G hG10)

end Work.L2F.PSL
