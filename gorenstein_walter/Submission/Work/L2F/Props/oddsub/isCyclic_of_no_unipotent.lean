import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Props.oddsub.eigenline_setup
import Submission.Work.L2F.Props.oddsub.finite_comap_toPGL
import Submission.Work.L2F.Props.oddsub.two_fixed_points_of_odd_quotient
import Submission.Work.L2F.Props.oddsub.ncard_eigenPointSet_of_semisimple
import Submission.Work.L2F.Props.oddsub.isCyclic_of_fixes_two_points

/-!
# An odd-order subgroup of `PGL(2,F)` with no unipotent lift is cyclic

Let `F` be a field and `K ≤ PGL(2,F)` a subgroup of odd order contained in the image of
`SL(2,F) → PGL(2,F)`, such that no element of `K` lifts to a unipotent matrix of `SL(2,F)`.

Then `K` is cyclic.

## Proof

Write `G = K.comap (toPGL) ≤ SL(2,F)` for the preimage of `K` and `Z ≤ G` for the kernel of
`toPGL`; thus `Z = center(SL(2,F)) ∩ G` consists of scalars and `G ⧸ Z ≃ K`.

Working over the algebraic closure `F̄`: `G` acts on the projective line `ℙ¹(F̄)` through the base
change `SL(2,F) → SL(2,F̄)`.  An element `g ∉ Z` is a non-scalar, non-unipotent element of
`SL(2,F)`, hence has two distinct eigenvalues in `F̄` and therefore acts on `ℙ¹(F̄)` with exactly
two fixed points.  So `G` is a finite group with `Z` in the kernel of the action, `|G ⧸ Z| = |K|`
odd, and every `g ∉ Z` has exactly two fixed points.  The counting lemma
`two_fixed_points_of_odd_quotient` then produces two distinct points `p ≠ q` of `ℙ¹(F̄)` fixed by
all of `G`; equivalently all elements of `G` are simultaneously diagonalisable with respect to the
basis given by `p, q`.  The resulting "ratio of eigenvalues" homomorphism `G → F̄ˣ` is injective,
so `G` is isomorphic to a finite subgroup of the units of a field and hence cyclic.  Finally `K` is
the image of the cyclic group `G` under `toPGL`, hence cyclic.

The supporting lemmas live in the sibling files
* `Work.L2F.Props.oddsub.two_fixed_points_of_odd_quotient`,
* `Work.L2F.Props.oddsub.ncard_eigenPointSet_of_semisimple`,
* `Work.L2F.Props.oddsub.isCyclic_of_fixes_two_points`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

noncomputable section

/-! ## Auxiliary matrix lemmas -/

/-- Entrywise base change commutes with forming a "scalar multiple of the identity": namely
`(f.mapMatrix) (c • 1) = f c • 1`. -/
theorem mapMatrix_smul_one {F : Type*} [Field F] (c : F) :
    (algebraMap F (AlgebraicClosure F)).mapMatrix (c • (1 : Matrix (Fin 2) (Fin 2) F)) =
      (algebraMap F (AlgebraicClosure F) c) •
        (1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- If the base change to `F̄` of a `2 × 2` matrix over `F` is scalar, then the matrix itself is
scalar. -/
theorem mapMatrix_scalar_of_scalar {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (c : AlgebraicClosure F)
    (hc : (algebraMap F (AlgebraicClosure F)).mapMatrix M =
      c • (1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))) :
    ∃ c' : F, M = c' • (1 : Matrix (Fin 2) (Fin 2) F) := by
  set f := algebraMap F (AlgebraicClosure F) with hfdef
  have hf : Function.Injective f := (algebraMap F (AlgebraicClosure F)).injective
  have e00 : f (M 0 0) = c := by
    have h := congrFun (congrFun hc 0) 0
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply] at h
    simpa using h
  have e01 : f (M 0 1) = 0 := by
    have h := congrFun (congrFun hc 0) 1
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h
    simpa using h
  have e10 : f (M 1 0) = 0 := by
    have h := congrFun (congrFun hc 1) 0
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h
    simpa using h
  have e11 : f (M 1 1) = f (M 0 0) := by
    have h := congrFun (congrFun hc 1) 1
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h
    rw [h, ← e00]; simp
  exact ⟨M 0 0, by
    have z01 : M 0 1 = 0 := (map_eq_zero_iff f hf).mp e01
    have z10 : M 1 0 = 0 := (map_eq_zero_iff f hf).mp e10
    have z11 : M 1 1 = M 0 0 := hf e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z01, z10, z11, Matrix.smul_apply]⟩

/-- Entrywise base change to `F̄` preserves `SemisimpleSL`. -/
theorem semisimpleSL_mapMatrix_iff {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    SemisimpleSL ((algebraMap F (AlgebraicClosure F)).mapMatrix M) ↔ SemisimpleSL M := by
  set f := algebraMap F (AlgebraicClosure F) with hfdef
  have hf : Function.Injective f := (algebraMap F (AlgebraicClosure F)).injective
  have hsmul : ∀ c : F, f.mapMatrix (c • (1 : Matrix (Fin 2) (Fin 2) F)) =
      f c • (1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) :=
    fun c => mapMatrix_smul_one c
  have htr : (f.mapMatrix M).trace = f M.trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.map_apply, map_add]
  have hdet : (f.mapMatrix M).det = f M.det := (RingHom.map_det f M).symm
  have hdisc : (f.mapMatrix M).trace ^ 2 - 4 * (f.mapMatrix M).det =
      f (M.trace ^ 2 - 4 * M.det) := by
    rw [htr, hdet, map_sub, map_mul, map_pow, map_ofNat]
  have hdisc0 : ((f.mapMatrix M).trace ^ 2 - 4 * (f.mapMatrix M).det = 0) ↔
      (M.trace ^ 2 - 4 * M.det = 0) := by
    rw [hdisc, map_eq_zero_iff f hf]
  have h20 : ((2 : AlgebraicClosure F) = 0) ↔ ((2 : F) = 0) := by
    rw [show (2 : AlgebraicClosure F) = f 2 from (map_ofNat f 2).symm, map_eq_zero_iff f hf]
  unfold SemisimpleSL
  constructor
  · rintro ⟨hns, h | h⟩
    · exact ⟨fun c hc => hns (f c) (by rw [hc, hsmul c]),
        Or.inl ⟨fun h0 => h.1 (h20.mpr h0), fun h0 => h.2 (hdisc0.mpr h0)⟩⟩
    · exact ⟨fun c hc => hns (f c) (by rw [hc, hsmul c]),
        Or.inr ⟨h20.mp h.1, fun h0 => h.2 (by rw [htr, h0, map_zero])⟩⟩
  · rintro ⟨hns, h | h⟩
    · refine ⟨fun c hc => ?_, Or.inl ⟨fun h0 => h.1 (h20.mp h0), fun h0 => h.2 (hdisc0.mp h0)⟩⟩
      obtain ⟨c', hc'⟩ := mapMatrix_scalar_of_scalar M c hc
      exact hns c' hc'
    · refine ⟨fun c hc => ?_,
        Or.inr ⟨h20.mpr h.1, fun h0 => h.2 ((map_eq_zero_iff f hf).mp (by rw [← htr]; exact h0))⟩⟩
      obtain ⟨c', hc'⟩ := mapMatrix_scalar_of_scalar M c hc
      exact hns c' hc'

/-- Base change `SL(2,F) → SL(2,F̄)` preserves `SemisimpleSL`. -/
theorem semisimpleSL_baseChange_iff {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    SemisimpleSL (((baseChangeSL F g) :
        Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) ↔
      SemisimpleSL ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have h : ((baseChangeSL F g) : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) =
      (algebraMap F (AlgebraicClosure F)).mapMatrix
        ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [h]
  exact semisimpleSL_mapMatrix_iff _

/-- Expansion of a square of a matrix minus a scalar. -/
theorem sub_smul_one_mul_self {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) (a : F) :
    (M - a • (1 : Matrix (Fin 2) (Fin 2) F)) * (M - a • (1 : Matrix (Fin 2) (Fin 2) F)) =
      M * M - (2 * a) • M + (a * a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h2M : (2 * a) • (M : Matrix (Fin 2) (Fin 2) F) = a • M + a • M := by
    rw [two_mul, add_smul]
  rw [h2M]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;> ring

/-- A scalar element of `SL(2,F)` maps to `1` in `PGL(2,F)`. -/
theorem toPGL_eq_one_of_scalar {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (c : F)
    (hc : (g : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    Matrix.SpecialLinearGroup.toPGL g = 1 := by
  rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- A non-scalar, non-unipotent element of `SL(2,F)` has separable characteristic polynomial. -/
theorem semisimpleSL_of_nonScalar_not_unipotent {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hne : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hu : ¬ Work.L2F.Props.UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) :
    SemisimpleSL ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  set G : Matrix (Fin 2) (Fin 2) F := ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) with hG
  have hdet : G.det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F G
  rw [hdet, one_smul] at hCH
  constructor
  · exact fun c hc => hne c (by rw [hc])
  · rcases eq_or_ne (2 : F) 0 with h2 | h2
    · right
      refine ⟨h2, ?_⟩
      intro htr
      apply hu
      refine ⟨1, ?_, ?_⟩
      · intro hzero
        exact hne 1 (sub_eq_zero.mp hzero)
      · rw [sub_smul_one_mul_self, hCH, htr, zero_smul, zero_sub]
        rw [show (2 * (1 : F)) = 0 from by rw [mul_one]; exact h2, zero_smul]
        rw [one_mul, one_smul]
        abel
    · left
      refine ⟨h2, ?_⟩
      rw [hdet, mul_one]
      intro hsq
      have hfac : (G.trace - 2) * (G.trace + 2) = 0 := by
        rw [show (G.trace - 2) * (G.trace + 2) = G.trace ^ 2 - 4 from by ring]
        exact hsq
      rcases mul_eq_zero.mp hfac with htr | htr
      · have ht : G.trace = 2 := sub_eq_zero.mp htr
        apply hu
        refine ⟨1, ?_, ?_⟩
        · intro hzero
          exact hne 1 (sub_eq_zero.mp hzero)
        · rw [sub_smul_one_mul_self, hCH, ht]
          rw [show (2 * (1 : F)) = 2 from by rw [mul_one]]
          rw [one_mul, one_smul]
          abel
      · have ht : G.trace = -2 := by simpa using eq_neg_of_add_eq_zero_left htr
        apply hu
        refine ⟨-1, ?_, ?_⟩
        · intro hzero
          exact hne (-1) (sub_eq_zero.mp hzero)
        · rw [sub_smul_one_mul_self, hCH, ht]
          rw [show (2 * (-1 : F)) = -2 from by ring]
          rw [show ((-1 : F) * (-1 : F)) = 1 from by ring, one_smul]
          rw [show ((-2 : F) • G) = -((2 : F) • G) from by rw [neg_smul]]
          abel

/-! ## The main theorem -/

theorem isCyclic_of_no_unipotent (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K))
    (hK : K ≤ Matrix.SpecialLinearGroup.toPGL.range)
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL g ∈ K →
          ¬ Work.L2F.Props.UnipotentMatrix (g : Matrix (Fin 2) (Fin 2) F)) :
    IsCyclic K := by
  classical
  by_cases hbot : K = ⊥
  · rw [hbot]
    exact inferInstance
  · haveI : Finite K := Nat.finite_of_card_ne_zero (by
      intro h0; obtain ⟨m, hm⟩ := hodd; omega)
    set G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      K.comap (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hGdef
    haveI hGfin : Finite G := finite_comap_toPGL F K hodd
    set Z : Subgroup G := MonoidHom.ker
      ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp G.subtype) with hZdef
    haveI hZnorm : Z.Normal := by rw [hZdef]; exact inferInstance
    -- the action of `G` on the projective line over `F̄`
    let φ : G →* Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F) :=
      (baseChangeSL F).comp G.subtype
    letI : MulAction G (PLineFbar F) := MulAction.compHom (PLineFbar F) φ
    have hsmulG : ∀ (g : G) (x : PLineFbar F),
        g • x = (baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) • x :=
      fun g x => rfl
    -- elements of `Z` are scalars
    have hscalarZ : ∀ z : G, z ∈ Z → ∃ r : F,
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          r • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro z hz
      rw [hZdef] at hz
      have hz1 : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F))
          (z : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
        have h := MonoidHom.mem_ker.mp hz
        simpa using h
      have hzc : (z : Matrix.SpecialLinearGroup (Fin 2) F) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [← Matrix.SpecialLinearGroup.toPGL_ker]
        exact MonoidHom.mem_ker.mpr hz1
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzc
      exact ⟨r, by rw [← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    -- `Z` acts trivially
    have hZtriv : ∀ z ∈ Z, ∀ x : PLineFbar F, z • x = x := by
      intro z hz x
      obtain ⟨r, hr⟩ := hscalarZ z hz
      have hm : ((baseChangeSL F (z : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) =
          (algebraMap F (AlgebraicClosure F) r) •
            (1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) := by
        rw [show ((baseChangeSL F (z : Matrix.SpecialLinearGroup (Fin 2) F)) :
            Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) =
            (algebraMap F (AlgebraicClosure F)).mapMatrix
              ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
          hr]
        exact mapMatrix_smul_one r
      refine Projectivization.ind (P := fun p => z • p = p) (fun v hv => ?_) x
      rw [hsmulG z (Projectivization.mk (AlgebraicClosure F) v hv),
        Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨algebraMap F (AlgebraicClosure F) r, ?_⟩
      rw [show (baseChangeSL F (z : Matrix.SpecialLinearGroup (Fin 2) F)) • v =
          ((baseChangeSL F (z : Matrix.SpecialLinearGroup (Fin 2) F)) :
            Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) *ᵥ v from by
        rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec],
        hm, Matrix.smul_mulVec, Matrix.one_mulVec]
    -- every `g ∉ Z` has exactly two fixed points
    have hfix : ∀ g : G, g ∉ Z →
        (MulAction.fixedBy (PLineFbar F) g).ncard = 2 := by
      intro g hg
      have hgK : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F))
          (g : Matrix.SpecialLinearGroup (Fin 2) F) ∈ K :=
        Subgroup.mem_comap.mp (hGdef ▸ (g : G).2)
      have hgne : (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F))
          (g : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
        rw [hZdef] at hg
        intro h
        exact hg (MonoidHom.mem_ker.mpr (by simpa using h))
      have hns : ∀ c : F, ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
        intro c hc
        exact hgne (toPGL_eq_one_of_scalar (g : Matrix.SpecialLinearGroup (Fin 2) F) c hc)
      have hun : ¬ Work.L2F.Props.UnipotentMatrix
          ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
        hu (g : Matrix.SpecialLinearGroup (Fin 2) F) hgK
      have hsem : SemisimpleSL ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) :=
        semisimpleSL_of_nonScalar_not_unipotent
          (g : Matrix.SpecialLinearGroup (Fin 2) F) hns hun
      have hsem' : SemisimpleSL
          (((baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
              Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) :=
        (semisimpleSL_baseChange_iff (g : Matrix.SpecialLinearGroup (Fin 2) F)).mpr hsem
      have hcnt : (eigenPointSet
          (((baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
              Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))).ncard = 2 :=
        ncard_eigenPointSet_of_semisimple (AlgebraicClosure F) _
          (Matrix.SpecialLinearGroup.det_coe
            (baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F))) hsem'
      have hset : (MulAction.fixedBy (PLineFbar F) g).ncard =
          (eigenPointSet (((baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
              Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))).ncard := by
        congr 1
        ext p
        rw [MulAction.mem_fixedBy, hsmulG g p, ← MulAction.mem_fixedBy]
        exact mem_fixedBy_iff_mem_eigenPointSet
          (baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) p
      rw [hset]; exact hcnt
    -- the quotient `G ⧸ Z` is isomorphic to `K`
    have hKrange : ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
        G.subtype).range = K := by
      rw [MonoidHom.range_comp, Subgroup.subtype_range]
      exact Subgroup.map_comap_eq_self hK
    have hcard : Nat.card (G ⧸ Z) = Nat.card K := by
      have e : G ⧸ Z ≃* K := by
        have e0 := QuotientGroup.quotientKerEquivRange
          ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp G.subtype)
        rw [hKrange] at e0
        exact e0
      exact Nat.card_congr e.toEquiv
    have hodd' : Odd (Nat.card (G ⧸ Z)) := by rw [hcard]; exact hodd
    have hgt : 1 < Nat.card (G ⧸ Z) := by
      rw [hcard]
      exact (Finite.one_lt_card_iff_nontrivial (α := K)).mpr
        ((Subgroup.nontrivial_iff_ne_bot K).mpr hbot)
    -- counting: there are two global fixed points
    obtain ⟨p, q, hpq, hp, hq⟩ :=
      two_fixed_points_of_odd_quotient Z hZtriv hodd' hgt hfix
    haveI hcycG : IsCyclic G :=
      isCyclic_of_fixes_two_points F G p q hpq
        (fun g => by rw [← hsmulG g p]; exact hp g)
        (fun g => by rw [← hsmulG g q]; exact hq g)
    -- `K` is the image of `G`
    rw [← hKrange]
    exact isCyclic_of_surjective
      (MonoidHom.rangeRestrict ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
        G.subtype)) (MonoidHom.rangeRestrict_surjective _)

end

end Work.L2F.Props.oddsub
