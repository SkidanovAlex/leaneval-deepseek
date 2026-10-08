import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.pslMap_eq_iff
import Submission.Work.L2F.PSL.pslSplitTorus_card
import Submission.Work.L2F.PSL.mem_normalizer_torus_iff
import Submission.Work.L2F.PSL.normalizer_pslSplitTorus_dihedral
import Submission.Work.L2F.Involution.orderOf_pslZ
import Submission.Work.L2F.Involution.mem_normalizer_zpowers

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Small auxiliary facts

The `-1`-element of `SL(2,F)` lies in the split torus, and it can be moved past any element
(it is central).  These two facts dispose of the sign ambiguity `α = ± γ β γ⁻¹` coming out of
`pslMap_eq_iff`. -/

/-- The central element `-1` of `SL(2,F)` lies in the split torus: it is `diag (-1)`. -/
lemma ti_negOne_mem_torus (F : Type*) [Field F] : Work.L2F.negOne F ∈ Work.L2F.torus F := by
  rw [Work.L2F.torus, MonoidHom.mem_range]
  exact ⟨-1, (diag_eq_negOne_iff F (-1)).mpr rfl⟩

/-- Conjugation of `negOne F * x` by `γ` is `negOne F * (γ * x * γ⁻¹)`: the central element
`-1` passes to the left of `γ`. -/
lemma ti_conj_negOne_mul (F : Type*) [Field F] (γ x : Matrix.SpecialLinearGroup (Fin 2) F) :
    γ * (Work.L2F.negOne F * x) * γ⁻¹ = Work.L2F.negOne F * (γ * x * γ⁻¹) := by
  rw [← mul_assoc, ← Work.L2F.Involution.negOne_mul_comm F γ]
  group

/-- If the diagonal element `diag a ∈ SL(2,F)` is neither `1` nor `-1` then `a ≠ a⁻¹`.

Proof: if `a = a⁻¹` then `a * a = 1` in `Fˣ`, so `((a:F) - 1) * ((a:F) + 1) = 0` in the field,
hence `(a : F) = 1` or `(a : F) = -1`, and reading off the `(0,0)`-entry of `diag a` turns this
into `diag a = 1` or `diag a = -1 = negOne F`. -/
theorem ti_val_ne_inv_of_diag_ne (F : Type*) [Field F] (a : Fˣ)
    (h1 : Work.PSL2.diag F a ≠ 1) (hm : Work.PSL2.diag F a ≠ Work.L2F.negOne F) :
    a ≠ a⁻¹ := by
  intro h
  -- pass `h` to `F` and deduce `a * a = 1`.
  have hval1 : ((a : F)) = ((a : F))⁻¹ := by
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa only [Units.val_inv_eq_inv_val] using this
  have hval : ((a : F)) * ((a : F)) = 1 := by
    have h' := congrArg (fun x : F => x * (a : F)) hval1
    rw [h', inv_mul_cancel₀ (Units.ne_zero a)]
  -- factor `a ^ 2 - 1 = (a - 1) * (a + 1)` in the field.
  have hfac : (((a : F)) - 1) * (((a : F)) + 1) = 0 := by
    have h' : (((a : F)) - 1) * (((a : F)) + 1) = ((a : F)) ^ 2 - 1 := by ring
    rw [h', pow_two, hval, sub_self]
  rcases mul_eq_zero.mp hfac with h' | h'
  · have hx : ((a : F)) = 1 := sub_eq_zero.mp h'
    exact h1 ((diag_eq_one_iff F a).mpr (Units.ext (by simpa using hx)))
  · have hx : ((a : F)) = -1 := add_eq_zero_iff_eq_neg.mp h'
    exact hm ((diag_eq_negOne_iff F a).mpr (Units.ext (by simpa using hx)))

/-! ## The model-theoretic core -/

/-- If `γ * diag b * γ⁻¹ = diag a` in `SL(2,F)` with `a ≠ a⁻¹` (i.e. `diag a` is not central),
then `γ` normalizes the split (diagonal) torus `T = torus F` in `SL(2,F)`.

This is the model-theoretic core of the TI property of the split torus: a conjugate of a
non-central element of `T` that lies again in `T` forces the conjugating matrix to be monomial.

Proof (no finiteness hypothesis, valid in every characteristic): from
`γ * diag b * γ⁻¹ = diag a` one gets `diag b * γ⁻¹ = γ⁻¹ * diag a`, and hence the matrix equation
`!![b,0;0,b⁻¹] * X = X * !![a,0;0,a⁻¹]` for `X = (γ⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F`,
whose determinant is `1`.  `diag_conj_dichotomy` (from
`Submission/Work/L2F/PSL/mem_normalizer_torus_iff.lean`) then says that `X` is diagonal
(`X 0 1 = X 1 0 = 0` and `X 0 0 * X 1 1 = 1`, so `γ⁻¹ = diag ⟨X 0 0, X 1 1, …⟩ ∈ T`) or
anti-diagonal (`X 0 0 = X 1 1 = 0` and `X 0 1 * X 1 0 = -1`, so `γ⁻¹ = z * diag t` with
`t = ⟨-X 1 0, X 0 1, …⟩`).  In both cases `γ⁻¹ ∈ N(T)` — using `T ≤ N(T)` and
`weyl_mem_normalizer_torus` — whence `γ = (γ⁻¹)⁻¹ ∈ N(T)`, a subgroup. -/
theorem ti_mem_normalizer_torus_of_conj (F : Type*) [Field F]
    {γ : Matrix.SpecialLinearGroup (Fin 2) F} {a b : Fˣ} (ha : a ≠ a⁻¹)
    (hconj : γ * Work.PSL2.diag F b * γ⁻¹ = Work.PSL2.diag F a) :
    γ ∈ Subgroup.normalizer (Work.L2F.torus F : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  -- Work with `X = γ⁻¹`, so that the diagonal factor sits on the left.
  set X : Matrix (Fin 2) (Fin 2) F :=
    ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hX
  have hgrp : Work.PSL2.diag F b * γ⁻¹ = γ⁻¹ * Work.PSL2.diag F a := by
    have h : γ⁻¹ * (γ * Work.PSL2.diag F b * γ⁻¹) = γ⁻¹ * Work.PSL2.diag F a := by rw [hconj]
    calc Work.PSL2.diag F b * γ⁻¹ = γ⁻¹ * (γ * Work.PSL2.diag F b * γ⁻¹) := by group
      _ = γ⁻¹ * Work.PSL2.diag F a := h
  have hmat : (!![((b : F)), 0; 0, ((b : F))⁻¹] : Matrix (Fin 2) (Fin 2) F) * X =
      X * (!![((a : F)), 0; 0, ((a : F))⁻¹] : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hgrp
    simpa only [hX, Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_diag,
      Units.val_inv_eq_inv_val] using h
  have hdet : X.det = 1 := by
    rw [hX]
    exact Matrix.SpecialLinearGroup.det_coe γ⁻¹
  have ha' : ((a : F)) ≠ ((a : F))⁻¹ := by
    intro h
    exact ha (Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h))
  rcases diag_conj_dichotomy F X ha' hdet hmat with
    ⟨h01, h10, hprod⟩ | ⟨h00, h11, hanti⟩
  · -- `γ⁻¹ = diag u ∈ T`
    have hmem : γ⁻¹ ∈ Work.L2F.torus F := by
      rw [Work.L2F.torus, MonoidHom.mem_range]
      let u : Fˣ := ⟨X 0 0, X 1 1, hprod, by rw [mul_comm]; exact hprod⟩
      refine ⟨u, ?_⟩
      apply Subtype.ext
      change ((Work.PSL2.diag F u : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = X
      rw [Work.PSL2.coe_diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, u]
    have hmem' := (Subgroup.normalizer (Work.L2F.torus F :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))).inv_mem
        (Subgroup.le_normalizer hmem)
    simpa using hmem'
  · -- `γ⁻¹ = z * diag t`, a product of two elements of `N(T)`
    have hmem : γ⁻¹ ∈ Subgroup.normalizer (Work.L2F.torus F :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      let t : Fˣ := ⟨-X 1 0, X 0 1, by linear_combination -hanti,
        by linear_combination -hanti⟩
      have ht : γ⁻¹ = Work.L2F.z F * Work.PSL2.diag F t := by
        apply Subtype.ext
        change X = ((Work.L2F.z F * Work.PSL2.diag F t :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        rw [Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_diag]
        simp only [Work.L2F.z, Work.PSL2.coe_weyl, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h11, t]
      rw [ht]
      exact Subgroup.mul_mem _ (weyl_mem_normalizer_torus F)
        (Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨t, rfl⟩))
    have hmem' := (Subgroup.normalizer (Work.L2F.torus F :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))).inv_mem hmem
    simpa using hmem'

/-! ## The TI property -/

/-- `pslSplitTorus F` is a TI subgroup of `PSL(2,F)` (odd characteristic): its conjugates by
elements outside its normalizer meet it trivially.  Proof: suppose `1 ≠ t ∈ Tm ⊓ Tm^g`; lift to
`α ∈ T` (a diagonal matrix) with `π(α) = t` and write `t = π(g β g⁻¹)` for some `β ∈ T`.  Then
`α = ±g β g⁻¹`, so `F[α] = F[g β g⁻¹] = g F[β] g⁻¹`; since `t ≠ 1`, `α` is not central, so the
2-dimensional commutative algebras `C_{M₂(F)}(α) = F[α]` and `C_{M₂(F)}(β) = F[β]` are equal to the
diagonal algebra `D` up to conjugation, i.e. `g D g⁻¹ = D`.  Hence `g ∈ D^• ∪ D^•·z` with
`z = weyl` (as `N_{GL}(D) = D^• ⋊ ⟨z⟩`), and both parts normalize `T` (elements of `D^•` centralize
it, `z` inverts it), so `π(g) ∈ N(Tm)`. -/
theorem ti_pslSplitTorus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hg : g ∉ Subgroup.normalizer (Work.L2F.pslSplitTorus F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :
    Work.L2F.pslSplitTorus F ⊓
        (Work.L2F.pslSplitTorus F).map (MulAut.conj g).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzT, hzTg⟩ := hz
  rw [Subgroup.mem_bot]
  by_contra hzne
  -- Lift `g`, `z` and the element witnessing `z ∈ (pslSplitTorus F)^g` to `SL(2,F)`.
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, F))) g
  have hγ' : Work.PSL2.pslMap F γ = g := hγ
  obtain ⟨α, hαT, hαeq⟩ := Subgroup.mem_map.mp hzT
  obtain ⟨s, hs, hsconj⟩ := Subgroup.mem_map.mp hzTg
  obtain ⟨β, hβT, hβeq⟩ := Subgroup.mem_map.mp hs
  -- `π (γ β γ⁻¹) = g s g⁻¹ = z = π α`
  have hkey : Work.PSL2.pslMap F (γ * β * γ⁻¹) = Work.PSL2.pslMap F α := by
    rw [map_mul, map_mul, map_inv, hγ', hβeq, hαeq, ← MulAut.conj_apply]
    exact hsconj
  -- `z ≠ 1` makes `α` non-central.
  have hα1 : α ≠ 1 := fun h1 => hzne (by rw [← hαeq, h1, map_one])
  have hαm : α ≠ Work.L2F.negOne F :=
    fun hm => hzne (by rw [← hαeq, hm, Work.L2F.Involution.pslMap_negOne F h2])
  -- Absorb the sign `α = -γ β γ⁻¹` by replacing `β` with `-β ∈ T`.
  have hsign : ∃ β' : Matrix.SpecialLinearGroup (Fin 2) F,
      β' ∈ Work.L2F.torus F ∧ γ * β' * γ⁻¹ = α := by
    rcases (pslMap_eq_iff F h2 (γ * β * γ⁻¹) α).mp hkey with h | h
    · exact ⟨β, hβT, h⟩
    · refine ⟨Work.L2F.negOne F * β,
        (Work.L2F.torus F).mul_mem (ti_negOne_mem_torus F) hβT, ?_⟩
      rw [ti_conj_negOne_mul, h, ← mul_assoc, Work.L2F.Involution.negOne_mul_self, one_mul]
  obtain ⟨β', hβ'T, hβ'conj⟩ := hsign
  -- Write `α = diag a`, `β' = diag b` and apply the core computation.
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hαT
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hβ'T
  have ha : a ≠ a⁻¹ := ti_val_ne_inv_of_diag_ne F a hα1 hαm
  have hN : γ ∈ Subgroup.normalizer (Work.L2F.torus F :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    ti_mem_normalizer_torus_of_conj F ha hβ'conj
  have hmem : Work.PSL2.pslMap F γ ∈ Subgroup.normalizer (Work.L2F.pslSplitTorus F :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    map_normalizer_le F (Subgroup.mem_map.mpr ⟨γ, hN, rfl⟩)
  exact hg (by rw [← hγ']; exact hmem)

end Work.L2F.PSL
