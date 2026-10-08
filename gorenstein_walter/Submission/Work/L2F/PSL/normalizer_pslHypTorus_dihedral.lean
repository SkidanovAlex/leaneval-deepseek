import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.exists_sq_sub_mul_sq
import Submission.Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two
import Submission.Work.L2F.PSL.pslHypTorus_cyclic
import Submission.Work.L2F.PSL.pslHypTorus_card
import Submission.Work.L2F.Mat2.quadAlgebra

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- The `⊆` half of the normalizer computation `N_{SL(2,F)}(hypTorus F d) = H ∪ w·H`: if
`x ∈ SL(2,F)` normalizes `H = hypTorus F d` (`d ≠ 0` a nonsquare, `q ≥ 5`), then `x ∈ H` or
`x = w·t` for some `t ∈ H`, where `w = hypWSL d p q hpq` (`p² - d·q² = -1`). -/
theorem hypTorus_normalizer_subset (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (d : F) (hd : d ≠ 0) (hns : ∀ a : F, a * a ≠ d)
    (p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : ∀ h ∈ Work.L2F.hypTorus F d, x * h * x⁻¹ ∈ Work.L2F.hypTorus F d) :
    x ∈ Work.L2F.hypTorus F d ∨
      ∃ t ∈ Work.L2F.hypTorus F d, x = Work.L2F.Mat2.hypWSL d p q hpq * t := by
  classical
  -- An element of `H` with non-zero `(1,0)` entry.
  obtain ⟨h₀, hh₀H, hh₀ne⟩ := Work.L2F.Mat2.hypTorus_entry_ne_zero d h2 h5 hd hns
  obtain ⟨a, b, hab, hh₀'⟩ := (Work.L2F.Conic.mem_hypTorus F d h₀).mp hh₀H
  have hh₀ : (h₀ : Matrix (Fin 2) (Fin 2) F) = Work.L2F.Mat2.quadMat d a b := hh₀'
  have hb : b ≠ 0 := by
    intro hb0
    refine hh₀ne ?_
    rw [hh₀, hb0]
    simp [Work.L2F.Mat2.quadMat]
  -- The matrix `X` of `x`, the matrix `Z` of `x⁻¹`, and the conjugated matrix `Y = X T Z`.
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  set Z : Matrix (Fin 2) (Fin 2) F :=
    ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hZ
  have hXZ : X * Z = 1 := by
    rw [hX, hZ]
    have h := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel x)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hZX : Z * X = 1 := by
    rw [hX, hZ]
    have h := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (inv_mul_cancel x)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  set Y : Matrix (Fin 2) (Fin 2) F := X * Work.L2F.Mat2.quadT d * Z with hY
  -- ## Step 1: `Y ∈ A`
  have hy_inQuad : Work.L2F.Mat2.inQuad d
      (((x * h₀ * x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) :=
    Work.L2F.Mat2.inQuad_of_mem_hypTorus (hx h₀ hh₀H)
  have hU : (((x * h₀ * x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [← hX, ← hZ, hh₀, Work.L2F.Mat2.quadMat_smul_one_add]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, hXZ, ← hY]
  have hbY : Work.L2F.Mat2.inQuad d (b • Y) := by
    have h := Work.L2F.Mat2.inQuad_sub hy_inQuad
      (Work.L2F.Mat2.inQuad_smul a (Work.L2F.Mat2.inQuad_one d))
    rw [hU, add_sub_cancel_left] at h
    exact h
  have hY_inQuad : Work.L2F.Mat2.inQuad d Y := by
    have h := Work.L2F.Mat2.inQuad_smul (b⁻¹) hbY
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h
  -- ## Step 2: `Y * Y = d • 1`
  have hYX : Y * X = X * Work.L2F.Mat2.quadT d := by
    rw [hY, Matrix.mul_assoc, hZX, Matrix.mul_one]
  have hsq : Y * Y = d • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : Y * Y * X = d • X := by
      calc Y * Y * X = Y * (Y * X) := Matrix.mul_assoc Y Y X
        _ = Y * (X * Work.L2F.Mat2.quadT d) := congrArg (fun M => Y * M) hYX
        _ = Y * X * Work.L2F.Mat2.quadT d :=
              (Matrix.mul_assoc Y X (Work.L2F.Mat2.quadT d)).symm
        _ = X * Work.L2F.Mat2.quadT d * Work.L2F.Mat2.quadT d :=
              congrArg (fun M => M * Work.L2F.Mat2.quadT d) hYX
        _ = X * (Work.L2F.Mat2.quadT d * Work.L2F.Mat2.quadT d) :=
              Matrix.mul_assoc X (Work.L2F.Mat2.quadT d) (Work.L2F.Mat2.quadT d)
        _ = X * (d • (1 : Matrix (Fin 2) (Fin 2) F)) :=
              congrArg (fun M => X * M) (Work.L2F.Mat2.quadT_mul_quadT d)
        _ = d • X := (Matrix.mul_smul X d 1).trans (congrArg (fun M => d • M) (Matrix.mul_one X))
    have h2 : Y * Y * X * Z = d • X * Z := congrArg (fun M => M * Z) h1
    have e1 : Y * Y * X * Z = Y * Y :=
      (Matrix.mul_assoc (Y * Y) X Z).trans
        ((congrArg (fun M => Y * Y * M) hXZ).trans (Matrix.mul_one (Y * Y)))
    have e2 : d • X * Z = d • (1 : Matrix (Fin 2) (Fin 2) F) :=
      (Matrix.smul_mul d X Z).trans (congrArg (fun M => d • M) hXZ)
    exact e1.symm.trans (h2.trans e2)
  -- ## Step 3: case analysis on `Y = ±T`
  rcases Work.L2F.Mat2.inQuad_sq_eq h2 hd hns hY_inQuad hsq with hYT | hYT
  · -- `Y = T`: `x` commutes with `T`, so `x ∈ A ∩ SL = H`
    left
    have hcomm : X * Work.L2F.Mat2.quadT d = Work.L2F.Mat2.quadT d * X := by
      rw [← hYX, hYT]
    have hXiq : Work.L2F.Mat2.inQuad d X := Work.L2F.Mat2.inQuad_of_commute hcomm
    have hdetX : X.det = 1 := by rw [hX]; exact Matrix.SpecialLinearGroup.det_coe x
    have hmem : (⟨X, hdetX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) ∈ Work.L2F.hypTorus F d :=
      Work.L2F.Mat2.mem_hypTorus_of_inQuad hXiq hdetX
    have hxe : (⟨X, hdetX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) = x :=
      Subtype.ext (by rw [← hX])
    rwa [hxe] at hmem
  · -- `Y = -T`: `w⁻¹ * x` commutes with `T`, so `w⁻¹ * x ∈ H` and `x = w * (w⁻¹ * x)`
    right
    have hX'T : X * Work.L2F.Mat2.quadT d = -(Work.L2F.Mat2.quadT d * X) := by
      rw [← hYX, hYT, neg_mul]
    set W' : Matrix (Fin 2) (Fin 2) F := Work.L2F.Mat2.hypWMat d (-p) (-q) with hW'
    have hW'T : W' * Work.L2F.Mat2.quadT d = -(Work.L2F.Mat2.quadT d * W') := by
      rw [hW']
      exact Work.L2F.Mat2.hypWMat_mul_quadT d (-p) (-q)
    have hcomm' : W' * X * Work.L2F.Mat2.quadT d = Work.L2F.Mat2.quadT d * (W' * X) := by
      calc W' * X * Work.L2F.Mat2.quadT d
          = W' * (X * Work.L2F.Mat2.quadT d) := Matrix.mul_assoc W' X (Work.L2F.Mat2.quadT d)
        _ = W' * (-(Work.L2F.Mat2.quadT d * X)) := by rw [hX'T]
        _ = -(W' * (Work.L2F.Mat2.quadT d * X)) := Matrix.mul_neg W' (Work.L2F.Mat2.quadT d * X)
        _ = -((W' * Work.L2F.Mat2.quadT d) * X) := by
              rw [(Matrix.mul_assoc W' (Work.L2F.Mat2.quadT d) X).symm]
        _ = -((-(Work.L2F.Mat2.quadT d * W')) * X) := by rw [hW'T]
        _ = (Work.L2F.Mat2.quadT d * W') * X := by rw [neg_mul, neg_neg]
        _ = Work.L2F.Mat2.quadT d * (W' * X) := Matrix.mul_assoc (Work.L2F.Mat2.quadT d) W' X
    have hW'Xiq : Work.L2F.Mat2.inQuad d (W' * X) := Work.L2F.Mat2.inQuad_of_commute hcomm'
    have hcoe : (((Work.L2F.Mat2.hypWSL d p q hpq)⁻¹ * x :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = W' * X := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Work.L2F.Mat2.coe_hypWSL_inv, hW', hX]
    have hdetWX : (W' * X).det = 1 := by
      rw [← hcoe]
      exact Matrix.SpecialLinearGroup.det_coe _
    have hmem : ((Work.L2F.Mat2.hypWSL d p q hpq)⁻¹ * x) ∈ Work.L2F.hypTorus F d := by
      have h := Work.L2F.Mat2.mem_hypTorus_of_inQuad hW'Xiq hdetWX
      rwa [show (⟨W' * X, hdetWX⟩ : Matrix.SpecialLinearGroup (Fin 2) F) =
        (Work.L2F.Mat2.hypWSL d p q hpq)⁻¹ * x from Subtype.ext hcoe.symm] at h
    exact ⟨(Work.L2F.Mat2.hypWSL d p q hpq)⁻¹ * x, hmem, (mul_inv_cancel_left _ _).symm⟩

/-- `-1 ∈ hypTorus F d` for every `d`. -/
theorem negOne_mem_hypTorus (F : Type*) [Field F] (d : F) :
    Work.L2F.negOne F ∈ Work.L2F.hypTorus F d := by
  rw [Work.L2F.Conic.mem_hypTorus]
  exact ⟨-1, 0, by ring, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]⟩

/-- `H ∪ w·H ⊆ N_{SL(2,F)}(H)`: `H` normalizes itself and `w` inverts `H`. -/
theorem hypTorus_union_hypW_le_normalizer (F : Type*) [Field F] (d p q : F)
    (hpq : p ^ 2 - d * q ^ 2 = -1) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Work.L2F.hypTorus F d ∨
      ∃ t ∈ Work.L2F.hypTorus F d, x = Work.L2F.Mat2.hypWSL d p q hpq * t) :
    x ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rcases hx with hx | ⟨t, ht, rfl⟩
  · exact Subgroup.le_normalizer hx
  · exact (Subgroup.normalizer _).mul_mem
      (Work.L2F.Mat2.hypWSL_mem_normalizer d p q hpq) (Subgroup.le_normalizer ht)

/-- `N_{SL(2,F)}(hypTorus F d) = H ∪ w·H`. -/
theorem mem_normalizer_hypTorus_iff (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (d : F) (hd : d ≠ 0) (hns : ∀ a : F, a * a ≠ d)
    (p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) ↔
      x ∈ Work.L2F.hypTorus F d ∨
        ∃ t ∈ Work.L2F.hypTorus F d, x = Work.L2F.Mat2.hypWSL d p q hpq * t := by
  constructor
  · intro hx
    exact hypTorus_normalizer_subset F h2 h5 d hd hns p q hpq x
      (fun h hh => (Subgroup.mem_normalizer_iff.mp hx h).mp hh)
  · exact hypTorus_union_hypW_le_normalizer F d p q hpq x

/-- The kernel of `SL(2,F) → PSL(2,F)` is contained in `hypTorus F d`: `ker π = {±1}` and both
`1` and `-1` lie in `hypTorus F d`. -/
theorem pslMap_ker_le_hypTorus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (d : F) :
    (Work.PSL2.pslMap F).ker ≤ Work.L2F.hypTorus F d := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 y).mp hy with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact negOne_mem_hypTorus F d

/-- `π(x) ∈ π(H) ↔ x ∈ H` (`ker π ⊆ H`). -/
theorem mem_map_hypTorus_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (d : F)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F x ∈ Work.L2F.pslHypTorus F d ↔ x ∈ Work.L2F.hypTorus F d := by
  constructor
  · intro h
    obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp h
    have hker : x * t⁻¹ ∈ (Work.PSL2.pslMap F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, mul_inv_cancel]
    have hmem : x * t⁻¹ ∈ Work.L2F.hypTorus F d := pslMap_ker_le_hypTorus F h2 d hker
    have hx : x = x * t⁻¹ * t := by group
    rw [hx]
    exact (Work.L2F.hypTorus F d).mul_mem hmem ht
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

/-- `N_{PSL(2,F)}(π(H)) = π(N_{SL(2,F)}(H))`.  `⊆`: lift `g` to `x ∈ SL(2,F)`, then
`π(x H x⁻¹) = π(H)` gives `x H x⁻¹ = H` because `ker π ⊆ H`; `⊇`: `π` is a homomorphism. -/
theorem normalizer_pslHypTorus_eq_map (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (d : F)
    (hd : d ≠ 0) :
    Subgroup.normalizer (Work.L2F.pslHypTorus F d :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, F))) g
    have hx' : Work.PSL2.pslMap F x = g := hx
    have hg' : ∀ h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
        h ∈ Work.L2F.pslHypTorus F d ↔ g * h * g⁻¹ ∈ Work.L2F.pslHypTorus F d :=
      Subgroup.mem_normalizer_iff.mp hg
    refine Subgroup.mem_map.mpr ⟨x, ?_, hx'⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro h
    rw [← mem_map_hypTorus_iff F h2 d h, ← mem_map_hypTorus_iff F h2 d (x * h * x⁻¹)]
    have heq : g * Work.PSL2.pslMap F h * g⁻¹ = Work.PSL2.pslMap F (x * h * x⁻¹) := by
      rw [← hx', ← map_inv, ← map_mul, ← map_mul]
    rw [← heq]
    exact hg' (Work.PSL2.pslMap F h)
  · rintro g ⟨x, hxN, rfl⟩
    have hxN' : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
        h ∈ Work.L2F.hypTorus F d ↔ x * h * x⁻¹ ∈ Work.L2F.hypTorus F d :=
      Subgroup.mem_normalizer_iff.mp hxN
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro y
    constructor
    · intro hy
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨x * t * x⁻¹, (hxN' t).mp ht, by rw [map_mul, map_mul, map_inv]⟩
    · intro hy
      obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * s * x, (hxN' (x⁻¹ * s * x)).mpr ?_, ?_⟩
      · rw [show x * (x⁻¹ * s * x) * x⁻¹ = s from by group]; exact hs
      · rw [map_mul, map_mul, map_inv, hs_eq]; group

/-- `w = hypWSL d p q hpq ∉ hypTorus F d` (`d ≠ 0`, `2 ≠ 0`, `p² - d·q² = -1`): if `w` lay in
`A = F·1 + F·T` then `-p = p` and `-(d·q) = d·q`, so `p = q = 0` and `p² - d·q² = -1` fails. -/
theorem hypWSL_notMem_hypTorus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    (p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    Work.L2F.Mat2.hypWSL d p q hpq ∉ Work.L2F.hypTorus F d := by
  intro hmem
  have hA := Work.L2F.Mat2.inQuad_of_mem_hypTorus hmem
  have h1 : -(d * q) = d * q := by
    have h := hA.1
    simpa only [Work.L2F.Mat2.coe_hypWSL, Work.L2F.Mat2.hypWMat_apply_01,
      Work.L2F.Mat2.hypWMat_apply_10] using h
  have h2' : -p = p := by
    have h := hA.2
    simpa only [Work.L2F.Mat2.coe_hypWSL, Work.L2F.Mat2.hypWMat_apply_11,
      Work.L2F.Mat2.hypWMat_apply_00] using h
  have hq0 : q = 0 := by
    have h : 2 * (d * q) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h2
    · exact (mul_eq_zero.mp h').resolve_left hd
  have hp0 : p = 0 := by
    have h : 2 * p = 0 := by linear_combination -h2'
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h2
    · exact h'
  rw [hp0, hq0] at hpq
  simp at hpq

/-- The normalizer in `PSL(2,F)` of the non-split torus image `pslHypTorus F d` (`d ≠ 0` a
nonsquare, `q ≥ 5`) is dihedral of order `q + 1 = 2 * Nat.card (pslHypTorus F d)`.  Proof: let
`A = F·1 + F·T ⊆ M₂(F)` be the quadratic algebra with `T = !![0,d;1,0]`, `T² = d·1`, a field because
`d` is a nonsquare; `H = hypTorus F d` is the norm-one subgroup of `A^• ∩ SL` and generates `A` over
`F`.  Any `x ∈ SL` normalizing `H` satisfies `x A x⁻¹ = A`, so conjugation induces an
`F`-automorphism of the field `A`, which sends `T` to `±T`, hence is `id` or `T ↦ -T`.  In the first
case `x ∈ C(A) = A`, so `x ∈ A ∩ SL = H`; in the second `x` inverts `H` and `x * w⁻¹` centralizes
`A` for the explicit inverting `w` with `w T w⁻¹ = -T` (`w = !![p,q;-q/d,-p]` with
`p² - d*q₁² = -1` from `exists_sq_sub_mul_sq`), so `x ∈ H·w`.  Hence
`N_{PSL}(π(H)) = π(H ⊔ ⟨w⟩)` with `π(H)` cyclic of index two and `π(w)` an involution outside it
inverting it; apply `mulEquiv_dihedral_of_cyclic_index_two`. -/
theorem normalizer_pslHypTorus_dihedral (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (d : F) (hd : d ≠ 0) (hns : ∀ a : F, a * a ≠ d) :
    Nonempty (Subgroup.normalizer (Work.L2F.pslHypTorus F d :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃*
      DihedralGroup (Nat.card (Work.L2F.pslHypTorus F d))) := by
  classical
  -- Pick `p, q` with `p² - d·q² = -1`.
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, p ^ 2 - d * q ^ 2 = -1 :=
    Work.L2F.Conic.exists_sq_sub_mul_sq F h2 d hd (-1)
  -- The element `w = hypWSL d p q hpq`, its image in `PSL(2,F)` and the normalizer `N`.
  have hWmem : Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq) ∈
      Subgroup.normalizer (Work.L2F.pslHypTorus F d :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    rw [normalizer_pslHypTorus_eq_map F h2 d hd]
    exact Subgroup.mem_map.mpr ⟨Work.L2F.Mat2.hypWSL d p q hpq,
      Work.L2F.Mat2.hypWSL_mem_normalizer d p q hpq, rfl⟩
  set N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Subgroup.normalizer (Work.L2F.pslHypTorus F d :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hN
  set C : Subgroup ↥N := (Work.L2F.pslHypTorus F d).subgroupOf N with hC
  obtain ⟨w, hw⟩ : ∃ w : ↥N,
      w = ⟨Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq), hWmem⟩ := ⟨_, rfl⟩
  have hle : Work.L2F.pslHypTorus F d ≤ N := Subgroup.le_normalizer
  have hcyc : IsCyclic ↥C :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hle)).mpr
      (Work.L2F.PSL.pslHypTorus_cyclic F h2 d hd)
  -- `π(w) ∉ π(H)`
  have hw_notMem : w ∉ C := by
    intro hmem
    rw [hC, Subgroup.mem_subgroupOf] at hmem
    rw [hw] at hmem
    exact hypWSL_notMem_hypTorus F h2 d hd p q hpq
      ((mem_map_hypTorus_iff F h2 d (Work.L2F.Mat2.hypWSL d p q hpq)).mp hmem)
  -- `π(w)² = 1`
  have hw_sq : w * w = 1 := by
    rw [hw]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    change Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq) *
        Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq) = 1
    rw [← map_mul, Work.L2F.Mat2.hypWSL_mul_self d p q hpq]
    exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  -- `π(w)` inverts `π(H)`
  have hw_inv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹ := by
    intro c hc
    have hc' : (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈
        Work.L2F.pslHypTorus F d := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hc'
    refine Subtype.ext ?_
    have hcw : (↑(w * c * w⁻¹) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
        Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq) *
          Work.PSL2.pslMap F t *
          (Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw, ht_eq]
    have hcinv : (↑(c⁻¹) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
        (Work.PSL2.pslMap F t)⁻¹ := by
      rw [Subgroup.coe_inv, ht_eq]
    have hkey : Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq) *
          Work.PSL2.pslMap F t *
          (Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq))⁻¹ =
        Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq * t *
          (Work.L2F.Mat2.hypWSL d p q hpq)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    have hkey2 : Work.PSL2.pslMap F (Work.L2F.Mat2.hypWSL d p q hpq * t *
          (Work.L2F.Mat2.hypWSL d p q hpq)⁻¹) = (Work.PSL2.pslMap F t)⁻¹ := by
      rw [Work.L2F.Mat2.hypWSL_conj_hypTorus d p q hpq ht, map_inv]
    exact hcw.trans ((hkey.trans hkey2).trans hcinv.symm)
  -- `π(H)` has index two in `N = N_{PSL}(π(H))`
  have hidx : C.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨w, hw_notMem, ?_⟩
    intro b
    have hb : ((b : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈
        (Subgroup.normalizer (Work.L2F.hypTorus F d :
          Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := by
      rw [← normalizer_pslHypTorus_eq_map F h2 d hd]
      exact b.2
    obtain ⟨y, hyN, hy⟩ := Subgroup.mem_map.mp hb
    rcases (mem_normalizer_hypTorus_iff F h2 h5 d hd hns p q hpq y).mp hyN with
      hyH | ⟨t, ht, hyt⟩
    · right
      rw [hC, Subgroup.mem_subgroupOf, ← hy]
      exact Subgroup.mem_map.mpr ⟨y, hyH, rfl⟩
    · left
      rw [hC, Subgroup.mem_subgroupOf]
      have hyW : y * Work.L2F.Mat2.hypWSL d p q hpq ∈ Work.L2F.hypTorus F d := by
        rw [hyt]
        have h1 : Work.L2F.Mat2.hypWSL d p q hpq * t * Work.L2F.Mat2.hypWSL d p q hpq =
            Work.L2F.negOne F * t⁻¹ := by
          calc Work.L2F.Mat2.hypWSL d p q hpq * t * Work.L2F.Mat2.hypWSL d p q hpq
              = Work.L2F.Mat2.hypWSL d p q hpq * t *
                  (Work.L2F.Mat2.hypWSL d p q hpq)⁻¹ *
                  (Work.L2F.Mat2.hypWSL d p q hpq * Work.L2F.Mat2.hypWSL d p q hpq) := by
                group
            _ = t⁻¹ * (Work.L2F.Mat2.hypWSL d p q hpq * Work.L2F.Mat2.hypWSL d p q hpq) := by
                rw [Work.L2F.Mat2.hypWSL_conj_hypTorus d p q hpq ht]
            _ = t⁻¹ * Work.L2F.negOne F := by rw [Work.L2F.Mat2.hypWSL_mul_self d p q hpq]
            _ = Work.L2F.negOne F * t⁻¹ := (Work.L2F.Involution.negOne_mul_comm F t⁻¹).symm
        rw [h1]
        exact (Work.L2F.hypTorus F d).mul_mem (negOne_mem_hypTorus F d)
          ((Work.L2F.hypTorus F d).inv_mem ht)
      have hbw : ((b * w : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
          Work.PSL2.pslMap F (y * Work.L2F.Mat2.hypWSL d p q hpq) := by
        rw [Subgroup.coe_mul, hw, ← hy, ← map_mul]
      rw [hbw]
      exact Subgroup.mem_map.mpr ⟨y * Work.L2F.Mat2.hypWSL d p q hpq, hyW, rfl⟩
  have hcard : Nat.card ↥C = Nat.card (Work.L2F.pslHypTorus F d) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  obtain ⟨e⟩ := Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two C hcyc hidx
    ⟨w, hw_notMem, hw_sq, hw_inv⟩
  rw [← hcard]
  exact ⟨e⟩

end Work.L2F.PSL
