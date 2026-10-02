import Mathlib
import Submission.Work.Thom.openThom_eq_zero_of_baseSet_rank
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.Coh_zero_cover_injective
import Submission.Work.Thom.Indicator
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Thom.pdCohMap_finInter_eq_zero
import Submission.Work.Thom.Coh_zero_cover_injective_gen
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Thom.localThomMap_cup_zero
import Submission.Work.Thom.localThom_eq_of_cover
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.sphereCohomologyOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# Auxiliary lemmas for `Work.Thom.chartCoeff_nonZeroDivisor`

Toolkit (point evaluations in `H⁰`, the pointwise form of the coefficient equation, the
"bad point" predicate and its local constancy along paths) used by the proof of
`Work.Thom.chartCoeff_nonZeroDivisor`.
-/

namespace Work.Thom

open Work.TangentClasses Work.Cohomology
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Evaluating a degree-zero class at a point -/

/-- **Evaluation of a degree-zero cohomology class at a point**, as a linear functional. -/
def ptEvLM {X : Type} [TopologicalSpace X] (p : X) : Coh ℤ 0 X →ₗ[ℤ] ℤ :=
  h0Ev (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSetObj₀Equiv.symm p)

/-- **Evaluation of a degree-zero cohomology class at a point**: the value at the `0`-simplex
corresponding to the point (`Work.Cohomology.h0Ev`). -/
def ptEv {X : Type} [TopologicalSpace X] (p : X) (x : Coh ℤ 0 X) : ℤ :=
  ptEvLM p x

theorem ptEv_apply {X : Type} [TopologicalSpace X] (p : X) (x : Coh ℤ 0 X) :
    ptEv p x = h0Ev (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSetObj₀Equiv.symm p) x := rfl

@[simp] theorem ptEv_zero {X : Type} [TopologicalSpace X] (p : X) :
    ptEv p (0 : Coh ℤ 0 X) = 0 := map_zero _

theorem ptEv_add {X : Type} [TopologicalSpace X] (p : X) (x y : Coh ℤ 0 X) :
    ptEv p (x + y) = ptEv p x + ptEv p y := (ptEvLM p).map_add x y

theorem ptEv_neg {X : Type} [TopologicalSpace X] (p : X) (x : Coh ℤ 0 X) :
    ptEv p (-x) = -ptEv p x := (ptEvLM p).map_neg x

theorem ptEv_sub {X : Type} [TopologicalSpace X] (p : X) (x y : Coh ℤ 0 X) :
    ptEv p (x - y) = ptEv p x - ptEv p y := (ptEvLM p).map_sub x y

/-- **`h0Ev` is linear for the integer action** (proved at the cochain level, to avoid the
clash between the `ZSMul`- and `Module ℤ`-structures on the homology). -/
theorem h0Ev_zsmul {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (k : ℤ) (x : Coh ℤ 0 X) :
    h0Ev (TopCat.toSSet.obj (TopCat.of X)) s (k • x) =
      k * h0Ev (TopCat.toSSet.obj (TopCat.of X)) s x := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 x
  have hkα : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) (k • α) = 0 := by
    have h := LinearMap.map_smul
      (Work.Cohomology.cochainDiffLM ℤ (TopCat.toSSet.obj (TopCat.of X)) 0) k α
    rw [show (Work.Cohomology.cochainDiffLM ℤ (TopCat.toSSet.obj (TopCat.of X)) 0) (k • α)
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) (k • α) from rfl] at h
    rw [show (Work.Cohomology.cochainDiffLM ℤ (TopCat.toSSet.obj (TopCat.of X)) 0) α
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) α from rfl, hα, smul_zero] at h
    exact h
  rw [← Work.Cohomology.Sph1.cohomologyClassOf_smul_int k α hkα hα, h0Ev_classOf, h0Ev_classOf]
  show genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) (k • α) s =
    k * genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) α s
  rw [Work.Cohomology.Sph1.genEval_zsmul, smul_eq_mul]

theorem ptEv_smul {X : Type} [TopologicalSpace X] (p : X) (k : ℤ) (x : Coh ℤ 0 X) :
    ptEv p (k • x) = k * ptEv p x := by
  rw [ptEv_apply, ptEv_apply, h0Ev_zsmul]

/-- **The evaluations at points jointly detect degree-zero classes.** -/
theorem ptEv_ext {X : Type} [TopologicalSpace X] {x y : Coh ℤ 0 X}
    (h : ∀ p : X, ptEv p x = ptEv p y) : x = y := by
  refine h0Ev_ext (fun s => ?_)
  have hs := h (TopCat.toSSetObj₀Equiv s)
  rwa [ptEv_apply, ptEv_apply, TopCat.toSSetObj₀Equiv.symm_apply_apply] at hs

theorem ptEv_eq_zero_iff {X : Type} [TopologicalSpace X] (x : Coh ℤ 0 X) :
    (∀ p : X, ptEv p x = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact ptEv_ext (fun p => by rw [h p, ptEv_zero])
  · rintro rfl p
    exact ptEv_zero p

theorem ptEv_ne_zero_iff {X : Type} [TopologicalSpace X] (x : Coh ℤ 0 X) :
    x ≠ 0 ↔ ∃ p : X, ptEv p x ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    exact h ((ptEv_eq_zero_iff x).mp (fun p => by
      by_contra hp
      exact hc ⟨p, hp⟩))
  · rintro ⟨p, hp⟩ rfl
    exact hp (ptEv_zero p)

/-- The `0`-simplex of the singular complex associated with a point is natural. -/
theorem toSSet_symm_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (p : X) :
    (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0))
      (TopCat.toSSetObj₀Equiv.symm p) = TopCat.toSSetObj₀Equiv.symm (f p) :=
  TopCat.toSSetObj₀Equiv.injective (by
    rw [toSSetObj₀Equiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- **Naturality of the pointwise evaluation under a pullback.** -/
theorem ptEv_pullback {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (p : X) (y : Coh ℤ 0 Y) :
    ptEv p ((CohMap f ℤ 0).hom y) = ptEv (f p) y := by
  show (h0Ev (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSetObj₀Equiv.symm p))
      ((CohMap f ℤ 0).hom y)
    = (h0Ev (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSetObj₀Equiv.symm (f p))) y
  rw [h0Ev_pullback f (TopCat.toSSetObj₀Equiv.symm p) y, toSSet_symm_map f p]

/-- The unit class evaluates to `1` at every point. -/
@[simp] theorem ptEv_one {X : Type} [TopologicalSpace X] (p : X) :
    ptEv p (oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) = 1 :=
  h0Ev_oneH _

/-- **The pointwise evaluations are multiplicative** in degree zero. -/
theorem h0Ev_cup {X : Type} [TopologicalSpace X]
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (x y : Coh ℤ 0 X) :
    h0Ev (TopCat.toSSet.obj (TopCat.of X)) s
        (cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 0 x y) =
      h0Ev (TopCat.toSSet.obj (TopCat.of X)) s x *
        h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y := by
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [cupH'_apply' ℤ _ α β hα hβ, h0Ev_classOf, h0Ev_classOf, h0Ev_classOf]
  show genEval ℤ (TopCat.toSSet.obj (TopCat.of X))
      (cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) s =
    genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) α s *
      genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) β s
  rw [cup_apply]
  rw [show frontFace (TopCat.toSSet.obj (TopCat.of X)) 0 (0 + 0) (Nat.le_add_right 0 0) s = s from by
    haveI : Subsingleton (⦋0⦌ ⟶ ⦋0+0⦌) := (inferInstance : Subsingleton (⦋0⦌ ⟶ ⦋0⦌))
    have h : frontIncl 0 (0+0) (Nat.le_add_right 0 0) = 𝟙 (⦋0⦌ : SimplexCategory) :=
      Subsingleton.elim _ _
    rw [frontFace, h, op_id]; simp]
  rw [show backFace (TopCat.toSSet.obj (TopCat.of X)) 0 0 s = s from by
    haveI : Subsingleton (⦋0⦌ ⟶ ⦋0+0⦌) := (inferInstance : Subsingleton (⦋0⦌ ⟶ ⦋0⦌))
    have h : backIncl 0 0 = 𝟙 (⦋0⦌ : SimplexCategory) := Subsingleton.elim _ _
    rw [backFace, h, op_id]; simp]

/-- **Multiplicativity of the pointwise evaluations.** -/
theorem ptEv_cup {X : Type} [TopologicalSpace X] (p : X) (x y : Coh ℤ 0 X) :
    ptEv p (cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 0 x y) = ptEv p x * ptEv p y :=
  h0Ev_cup _ x y

/-- **`H⁰(X;ℤ)` is torsion-free**: the module `H⁰(X;ℤ) ≅ ℤ^{π₀(X)}` has no torsion, so a
multiple `k • x` which vanishes is either zero because `k = 0` or because `x = 0`. -/
theorem zsmul_eq_zero_or {X : Type} [TopologicalSpace X] (k : ℤ) (x : Coh ℤ 0 X)
    (h : k • x = 0) : k = 0 ∨ x = 0 := by
  by_cases hk : k = 0
  · exact Or.inl hk
  · refine Or.inr ?_
    by_contra hx
    obtain ⟨p, hp⟩ := (ptEv_ne_zero_iff x).mp hx
    have h1 : ptEv p (k • x) = 0 := by rw [h, ptEv_zero]
    rw [ptEv_smul] at h1
    rcases mul_eq_zero.mp h1 with hk' | hx'
    · exact hk hk'
    · exact hp hx'


/-- **`H⁰` of a one-point space is generated by the unit class.** -/
theorem ptEv_eq_smul_oneH {X : Type} [TopologicalSpace X] [Subsingleton X]
    (p : X) (x : Coh ℤ 0 X) :
    x = (ptEv p x) • (oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) := by
  refine ptEv_ext (fun q => ?_)
  rw [ptEv_smul, ptEv_one, mul_one, Subsingleton.elim q p]

/-- The unit class of a non-empty space is non-zero. -/
theorem oneH_ne_zero {X : Type} [TopologicalSpace X] [Nonempty X] :
    (oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) ≠ 0 := by
  intro h
  obtain ⟨p⟩ := ‹Nonempty X›
  have hh := ptEv_one p
  rw [h, ptEv_zero] at hh
  exact one_ne_zero hh.symm

/-- The local Thom map sends the unit class to the class itself. -/
theorem localThomMap_oneH {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : PieceCoh Z W n) :
    localThomMap Z n W τ 0 (oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W)))
      = (Nat.zero_add n).symm ▸ τ := by
  rw [localThomMap_apply, CohMap_oneH]
  exact mixedCupC_oneH_zero ((Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' zeroComplement Z) n τ


/-- **Cast naturality for the restriction of a piece class.** -/
theorem cast_pdCohMap {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) {W V : Set B} (hWV : V ⊆ W)
    {m m' : ℕ} (h : m = m') (y : PieceCoh Z W m) :
    (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' W) (Z.proj ⁻¹' V)
        (Set.preimage_mono hWV) m') (h ▸ y)
      = h ▸ ((pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' W)
        (Z.proj ⁻¹' V) (Set.preimage_mono hWV) m) y) := by
  subst h
  rfl

/-- The restricted class over a chart piece, transported to degree `0 + n`. -/
def sigmaW (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (W : Set B) :
    PieceCoh Z W (0 + n) :=
  (Nat.zero_add n).symm ▸ ((PieceRes Z W n).hom T.τ)


/-! ## Pointwise bookkeeping -/

/-- The explicit chart class over a piece `U`, as a piece class. -/
abbrev chartCoh (Z : RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι)
    (U : Set B) (hU : U ⊆ Z.baseSet i) : PieceCoh Z U n :=
  (localThomOfChart Z n e i U hU).τ

/-- The unit class of the one-point space over `b`. -/
def onePt (b : B) : Coh ℤ 0 ↥({b} : Set B) :=
  oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))

/-- **If `b ∈ W` then the singleton `{b}` is contained in `W`.** -/
theorem singleton_subset_of_mem {b : B} {W : Set B} (hb : b ∈ W) : ({b} : Set B) ⊆ W :=
  fun _ hx => by rw [Set.mem_singleton_iff] at hx; exact hx ▸ hb

/-- The inclusion of the point `b` into a piece `U ∋ b`. -/
abbrev ptIncl (U : Set B) (b : B) (hb : b ∈ U) : C(↥({b} : Set B), ↥U) :=
  TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) U ({b} : Set B)
    (singleton_subset_of_mem hb))

/-- **Degree-cast compatibility of the restriction map `pdCohRes`** (specialised to the cast
`0 + n = n`). -/
theorem pdCohRes_cast (X : TopCat) (A U : Set X) (n : ℕ)
    (x : Work.Cohomology.pdCoh X A (0 + n)) :
    (Work.Cohomology.pdCohRes X A U n).hom ((Nat.zero_add n) ▸ x)
      = (Nat.zero_add n) ▸ ((Work.Cohomology.pdCohRes X A U (0 + n)).hom x) := by
  unfold Work.Cohomology.pdCohRes
  exact homologyMap_cast _ (Nat.zero_add n) x

/-- **The restriction of a degree-zero class to a point is the value at that point times the unit
class.**  Over the one-point space `↥{b}` the group `H⁰` is generated by `1`. -/
theorem CohMap_ptIncl_smul (U : Set B) (b : B) (hb : b ∈ U) (d : Coh ℤ 0 ↥U) :
    (CohMap (ptIncl U b hb) ℤ 0).hom d = (ptEv ⟨b, hb⟩ d) • (onePt b) := by
  have hpt : (Work.Cohomology.pdIncl (M := TopCat.of B) U ({b} : Set B)
      (singleton_subset_of_mem hb)) ⟨b, rfl⟩ = ⟨b, hb⟩ := Subtype.ext rfl
  show (CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) U ({b} : Set B)
      (singleton_subset_of_mem hb))) ℤ 0).hom d
    = (ptEv ⟨b, hb⟩ d) • (oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B))))
  rw [ptEv_eq_smul_oneH (X := ↥({b} : Set B)) ⟨b, rfl⟩
      ((CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) U ({b} : Set B)
        (singleton_subset_of_mem hb))) ℤ 0).hom d),
    ptEv_pullback, hpt]

/-- **The pointwise form of the local Thom map over a chart piece, restricted to a point.** -/
theorem localThomMap_piece_pt (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {U : Set B} (hU : U ⊆ Z.baseSet i)
    (b : B) (hb : b ∈ U) (hbsub : ({b} : Set B) ⊆ Z.baseSet i) (d : Coh ℤ 0 ↥U) :
    (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
        (Z.proj ⁻¹' ({b} : Set B)) (Set.preimage_mono (singleton_subset_of_mem hb)) (0 + n)).hom
        (localThomMap Z n U (chartCoh Z n e i U hU) 0 d)
      = localThomMap Z n ({b} : Set B) (chartCoh Z n e i ({b} : Set B) hbsub) 0
          ((CohMap (ptIncl U b hb) ℤ 0).hom d) := by
  have h := congrArg (fun (g : Coh ℤ 0 ↥U →ₗ[ℤ] PieceCoh Z ({b} : Set B) (0 + n)) => g d)
    (congrArg ModuleCat.Hom.hom
      (localThomMap_pdCohMap (Z := Z) (n := n) (U := U) (W := ({b} : Set B))
        (singleton_subset_of_mem hb) (chartCoh Z n e i U hU) 0))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at h
  rw [show (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
        (Z.proj ⁻¹' ({b} : Set B)) (Set.preimage_mono (singleton_subset_of_mem hb)) n).hom
        (chartCoh Z n e i U hU)
      = chartCoh Z n e i ({b} : Set B) hbsub from
    localThomOfChart_restrict Z n e i ({b} : Set B) U hbsub hU (singleton_subset_of_mem hb)] at h
  exact h.symm

/-- **The coefficient equation restricted to a point.** -/
theorem PieceRes_singleton_eq (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (i : ι)
    {U : Set B} (hU : U ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : Coh ℤ 0 ↥U)
    (hd : (PieceRes Z U n).hom T.τ = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d))
    (b : B) (hb : b ∈ U) (hbsub : ({b} : Set B) ⊆ Z.baseSet i) :
    (PieceRes Z ({b} : Set B) n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n ({b} : Set B) (chartCoh Z n e i ({b} : Set B) hbsub) 0
          ((CohMap (ptIncl U b hb) ℤ 0).hom d)) := by
  have h1 : (PieceRes Z ({b} : Set B) n).hom T.τ
      = (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
          (Z.proj ⁻¹' ({b} : Set B)) (Set.preimage_mono (singleton_subset_of_mem hb)) n).hom
          ((PieceRes Z U n).hom T.τ) := by
    rw [show (PieceRes Z ({b} : Set B) n)
        = (PieceRes Z U n) ≫ (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' ({b} : Set B))
            (Set.preimage_mono (singleton_subset_of_mem hb)) n) from
      Work.Cohomology.pdCohRes_comp (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' ({b} : Set B))
        (Set.preimage_mono (singleton_subset_of_mem hb)) n,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h1, hd,
    cast_pdCohMap Z (singleton_subset_of_mem hb) (Nat.zero_add n)
      (localThomMap Z n U (chartCoh Z n e i U hU) 0 d)]
  exact congrArg (fun y => (Nat.zero_add n) ▸ y) (localThomMap_piece_pt Z n e i hU b hb hbsub d)

/-- **A bad point**: the global Thom class dies on the fibre over `b` (equivalently, its restriction
to the piece over `{b}` vanishes). -/
abbrev bad (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (b : B) : Prop :=
  (PieceRes Z ({b} : Set B) n).hom T.τ = 0

/-- Cancelling a degree cast composed with its inverse. -/
theorem cast_symm_cast_self {α : Type} {P : α → Type} {a b : α} (h : a = b) (Y : P a) :
    h.symm ▸ (h ▸ Y) = Y := by cases h; rfl

/-- Cancelling the degree cast `0 + n = n`. -/
theorem zeroAdd_cancel (Z : RealBundle B F ι) (n : ℕ) {U : Set B}
    (Y : PieceCoh Z U (0 + n)) :
    (Nat.zero_add n).symm ▸ ((Nat.zero_add n) ▸ Y) = Y :=
  cast_symm_cast_self (P := fun k => PieceCoh Z U k) (Nat.zero_add n) Y

/-- Transporting zero along the degree cast `n → 0 + n`. -/
theorem zeroAdd_zero (Z : RealBundle B F ι) (n : ℕ) {U : Set B} :
    (Nat.zero_add n).symm ▸ (0 : PieceCoh Z U n) = 0 :=
  pdcz_cast_zero (P := fun k => PieceCoh Z U k) (h := (Nat.zero_add n).symm)

/-- Transporting zero along the degree cast `0 + n → n`. -/
theorem zeroAdd_cast_zero (Z : RealBundle B F ι) (n : ℕ) {U : Set B} :
    (Nat.zero_add n) ▸ (0 : PieceCoh Z U (0 + n)) = 0 :=
  pdcz_cast_zero (P := fun k => PieceCoh Z U k) (h := (Nat.zero_add n))

/-- Transporting zero along the degree cast `n → 0 + n` for the relative cohomology of the pair. -/
theorem pdCoh_zeroAdd_zero (X : TopCat) (A : Set X) (n : ℕ) :
    (Nat.zero_add n).symm ▸ (0 : Work.Cohomology.pdCoh X A n) = 0 :=
  pdcz_cast_zero (P := fun k => Work.Cohomology.pdCoh X A k) (h := (Nat.zero_add n).symm)

/-- **If the coefficient vanishes at `b`, the Thom class dies on the fibre over `b`.** -/
theorem bad_of_ptEv_eq_zero (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (i : ι)
    {U : Set B} (hU : U ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : Coh ℤ 0 ↥U)
    (hd : (PieceRes Z U n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d))
    (b : B) (hb : b ∈ U) (hbsub : ({b} : Set B) ⊆ Z.baseSet i)
    (hptev : ptEv ⟨b, hb⟩ d = 0) : bad Z n T b := by
  change (PieceRes Z ({b} : Set B) n).hom T.τ = 0
  rw [PieceRes_singleton_eq Z n T i hU e d hd b hb hbsub]
  have hdb : (CohMap (ptIncl U b hb) ℤ 0).hom d = 0 := by
    rw [CohMap_ptIncl_smul U b hb d, hptev]
    exact zero_smul ℤ (onePt b)
  rw [hdb]
  rw [show localThomMap Z n ({b} : Set B) (chartCoh Z n e i ({b} : Set B) hbsub) 0
      (0 : Coh ℤ 0 ↥({b} : Set B)) = 0 from map_zero _]
  exact pdcz_cast_zero (P := fun k => PieceCoh Z ({b} : Set B) k) (h := (Nat.zero_add n))

/-- **If the Thom class dies on the fibre over `b`, the coefficient vanishes at `b`.** -/
theorem ptEv_eq_zero_of_bad (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (i : ι)
    {U : Set B} (hU : U ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : Coh ℤ 0 ↥U)
    (hd : (PieceRes Z U n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d))
    (b : B) (hb : b ∈ U) (hbsub : ({b} : Set B) ⊆ Z.baseSet i)
    (hbad : bad Z n T b) : ptEv ⟨b, hb⟩ d = 0 := by
  have hbad' : (PieceRes Z ({b} : Set B) n).hom T.τ = 0 := hbad
  have hpt := PieceRes_singleton_eq Z n T i hU e d hd b hb hbsub
  have hY : localThomMap Z n ({b} : Set B) (chartCoh Z n e i ({b} : Set B) hbsub) 0
      ((CohMap (ptIncl U b hb) ℤ 0).hom d) = 0 := by
    have hh : (Nat.zero_add n) ▸ (localThomMap Z n ({b} : Set B)
        (chartCoh Z n e i ({b} : Set B) hbsub) 0
        ((CohMap (ptIncl U b hb) ℤ 0).hom d)) = 0 := by
      rw [← hpt]; exact hbad'
    have h1 : (Nat.zero_add n).symm ▸ ((Nat.zero_add n) ▸ (localThomMap Z n ({b} : Set B)
        (chartCoh Z n e i ({b} : Set B) hbsub) 0
        ((CohMap (ptIncl U b hb) ℤ 0).hom d)))
        = (Nat.zero_add n).symm ▸ (0 : PieceCoh Z ({b} : Set B) n) :=
      congrArg (fun y => (Nat.zero_add n).symm ▸ y) hh
    rw [zeroAdd_cancel Z n (localThomMap Z n ({b} : Set B)
      (chartCoh Z n e i ({b} : Set B) hbsub) 0 ((CohMap (ptIncl U b hb) ℤ 0).hom d)),
      zeroAdd_zero Z n] at h1
    exact h1
  have hdb : (CohMap (ptIncl U b hb) ℤ 0).hom d = 0 :=
    (localThomOfChart Z n e i ({b} : Set B) hbsub).isThom 0 |>.1 (by
      rw [hY]; exact (map_zero (localThomMap Z n ({b} : Set B)
        (chartCoh Z n e i ({b} : Set B) hbsub) 0)).symm)
  have h1 : ptEv (⟨b, rfl⟩ : ↥({b} : Set B)) ((CohMap (ptIncl U b hb) ℤ 0).hom d) = 0 := by
    rw [hdb, ptEv_zero]
  rw [ptEv_pullback] at h1
  rwa [show ptIncl U b hb ⟨b, rfl⟩ = ⟨b, hb⟩ from Subtype.ext rfl] at h1

/-- **The pointwise form of the coefficient equation.**  If the restriction of the global Thom class
to a chart piece `U` is the local Thom map of the chart class with coefficient `d`, then at a point
`b ∈ U` the class dies on the fibre over `b` if and only if `d` vanishes at `b`. -/
theorem bad_iff_ptEv (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (i : ι)
    {U : Set B} (hU : U ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : Coh ℤ 0 ↥U)
    (hd : (PieceRes Z U n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d))
    (b : B) (hb : b ∈ U) (hbsub : ({b} : Set B) ⊆ Z.baseSet i) :
    bad Z n T b ↔ ptEv ⟨b, hb⟩ d = 0 :=
  ⟨ptEv_eq_zero_of_bad Z n T i hU e d hd b hb hbsub,
    bad_of_ptEv_eq_zero Z n T i hU e d hd b hb hbsub⟩

/-- **`H⁰`-evaluations are constant along paths**: two points joined by a path have the same
evaluation on every degree-zero class. -/
theorem ptEv_eq_of_joined {X : Type} [TopologicalSpace X] {x y : X} (h : Joined x y)
    (d : Coh ℤ 0 X) : ptEv x d = ptEv y d := by
  have hα : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X))
      (((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of X))).iCycles 0).hom
        ((h0CycIso (TopCat.toSSet.obj (TopCat.of X))).hom d)) = 0 :=
    cochainDiff_iCycles ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 _
  have hd : d = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X))
      (((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of X))).iCycles 0).hom
        ((h0CycIso (TopCat.toSSet.obj (TopCat.of X))).hom d)) hα :=
    (h0ClassOf_iCycles (TopCat.toSSet.obj (TopCat.of X)) d).symm
  rw [ptEv_apply, ptEv_apply, hd, h0Ev_classOf, h0Ev_classOf]
  exact Work.Cohomology.Sph1.genEval_congr_of_joined hα h

/-- **A class of a chart piece which vanishes on every fibre is zero.** -/
theorem eq_zero_of_fibre_eq_zero (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {U : Set B} (hU : U ⊆ Z.baseSet i)
    (z : PieceCoh Z U (0 + n))
    (hz : ∀ (b : B) (hb : b ∈ U),
      (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
        (Z.proj ⁻¹' ({b} : Set B)) (Set.preimage_mono (singleton_subset_of_mem hb))
        (0 + n)).hom z = 0) :
    z = 0 := by
  obtain ⟨d, hd⟩ := (localThomOfChart Z n e i U hU).isThom 0 |>.2 z
  have hd' : z = localThomMap Z n U (chartCoh Z n e i U hU) 0 d := hd.symm
  rw [hd']
  suffices d = 0 by rw [this]; exact map_zero _
  refine ptEv_ext (fun p : ↥U => ?_)
  have hsub : ({p.1} : Set B) ⊆ Z.baseSet i := fun x hx => hU (singleton_subset_of_mem p.2 hx)
  have hb := hz p.1 p.2
  rw [hd'] at hb
  rw [localThomMap_piece_pt Z n e i hU p.1 p.2 hsub d] at hb
  have h0 : (CohMap (ptIncl U p.1 p.2) ℤ 0).hom d = 0 :=
    (localThomOfChart Z n e i ({p.1} : Set B) hsub).isThom 0 |>.1 (by
      rw [hb]; exact (map_zero (localThomMap Z n ({p.1} : Set B)
        (chartCoh Z n e i ({p.1} : Set B) hsub) 0)).symm)
  have h1 : ptEv p d = 0 := by
    have hpull := ptEv_pullback (ptIncl U p.1 p.2) (⟨p.1, rfl⟩ : ↥({p.1} : Set B)) d
    rw [h0, ptEv_zero] at hpull
    rw [show ptIncl U p.1 p.2 ⟨p.1, rfl⟩ = p from Subtype.ext rfl] at hpull
    exact hpull.symm
  rw [h1, ptEv_zero]

/-- **Existence of the coefficient of a Thom class over a chart piece.** -/
theorem exists_coeff (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) {U : Set B} (hU : U ⊆ Z.baseSet i) :
    ∃ d : Coh ℤ 0 ↥U, (PieceRes Z U n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d) := by
  obtain ⟨d, hd⟩ := (localThomOfChart Z n e i U hU).isThom 0 |>.2
    ((Nat.zero_add n).symm ▸ ((PieceRes Z U n).hom T.τ))
  refine ⟨d, ?_⟩
  have h2 := congrArg (fun y => (Nat.zero_add n) ▸ y) hd
  rw [pdcz_cast_symm_cast (P := fun k => PieceCoh Z U k) (h := (Nat.zero_add n)) _] at h2
  exact h2.symm

/-- **Separation in degree `0 + n`.**  A class of the Thom pair in degree `0 + n` (with `1 ≤ n`)
whose restriction to every chart piece vanishes is zero. -/
theorem openThom_zero_of_baseSet_zeroAdd [FiniteDimensional ℝ F]
    (Z : RealBundle B F ι) (n : ℕ) (hrank : Z.rank = n)
    (hn : 1 ≤ n) (z : OpenThom Z (0 + n))
    (hz : ∀ i : ι, (PieceRes Z (Z.baseSet i) (0 + n)).hom z = 0) : z = 0 := by
  have hmain : (Nat.zero_add n) ▸ z = 0 :=
    openThom_eq_zero_of_baseSet_rank Z hrank hn ((Nat.zero_add n) ▸ z) (fun i => by
      rw [show (PieceRes Z (Z.baseSet i) n).hom ((Nat.zero_add n) ▸ z)
          = (Nat.zero_add n) ▸ ((PieceRes Z (Z.baseSet i) (0 + n)).hom z) from
        pdCohRes_cast (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' (Z.baseSet i)) n z,
        hz i]
      exact pdcz_cast_zero (P := fun k => PieceCoh Z (Z.baseSet i) k) (h := (Nat.zero_add n)))
  have h1 : (Nat.zero_add n).symm ▸ ((Nat.zero_add n) ▸ z)
      = (Nat.zero_add n).symm ▸ (0 : OpenThom Z n) :=
    congrArg (fun y => (Nat.zero_add n).symm ▸ y) hmain
  rw [cast_symm_cast_self (P := fun k => OpenThom Z k) (Nat.zero_add n) z,
    pdCoh_zeroAdd_zero (TopCat.of Z.TotalSpace) (zeroComplement Z) n] at h1
  exact h1

/-- **A class restricted to a chart piece is constant along a path inside that piece.** -/
theorem bad_chord (Z : RealBundle B F ι) (n : ℕ) (T : ThomClass Z n) (i : ι) {U : Set B}
    (hU : U ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (d : Coh ℤ 0 ↥U)
    (hd : (PieceRes Z U n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n U (chartCoh Z n e i U hU) 0 d))
    (q : C(unitInterval, ↥U)) :
    (bad Z n T (q 0 : B) ↔ bad Z n T (q 1 : B)) := by
  have hsub0 : ({(q 0 : B)} : Set B) ⊆ Z.baseSet i :=
    fun x hx => hU (singleton_subset_of_mem (q 0).2 hx)
  have hsub1 : ({(q 1 : B)} : Set B) ⊆ Z.baseSet i :=
    fun x hx => hU (singleton_subset_of_mem (q 1).2 hx)
  have h0 := bad_iff_ptEv Z n T i hU e d hd (q 0 : B) (q 0).2 hsub0
  have h1 := bad_iff_ptEv Z n T i hU e d hd (q 1 : B) (q 1).2 hsub1
  have hconst : ptEv (q 0) d = ptEv (q 1) d := by
    have hjoin : Joined (0 : unitInterval) (1 : unitInterval) := by
      have h : JoinedIn (Set.Icc (0:ℝ) 1) (0:ℝ) 1 :=
        ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0, by norm_num⟩).joinedIn
          (0:ℝ) (by norm_num) (1:ℝ) (by norm_num)
      simpa using h.joined_subtype
    have hh := ptEv_eq_of_joined hjoin ((CohMap q ℤ 0).hom d)
    rwa [ptEv_pullback q 0 d, ptEv_pullback q 1 d] at hh
  rw [h0, h1]
  exact ⟨fun hh => by rw [← hconst]; exact hh, fun hh => by rw [hconst]; exact hh⟩

/-- **`bad` is constant along paths.**  Along a path in the base, the chart pieces form a cover on
which the coefficient is constant, so the predicate "the Thom class dies on the fibre" does not
change.

Proof: for each `t` in the interval there is a chart piece `U ∋ p t` and a coefficient `d` with
`T.τ|_U = localThomMap(τ''_U)(d)`; on a ball around `t` mapped into `U`, the chord from `p t` to
`p s` is a path in `U`, and `bad_chord` identifies `bad (p t)` with `bad (p s)`. -/
theorem bad_eq_of_joined [FiniteDimensional ℝ F] (Z : RealBundle B F ι) {n : ℕ}
    (hrank : Z.rank = n) (T : ThomClass Z n) {a b : B} (h : Joined a b) :
    (bad Z n T a ↔ bad Z n T b) := by
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]; exact hrank
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) := ContinuousLinearEquiv.ofFinrankEq hfr
  obtain ⟨p⟩ := h
  have key : ∀ t : unitInterval, ∃ ε > 0, ∀ s : unitInterval,
      dist s t < ε → bad Z n T (p s) = bad Z n T (p t) := by
    intro t
    obtain ⟨d, hd⟩ := exists_coeff (U := Z.baseSet (Z.indexAt (p t))) Z n T e
      (Z.indexAt (p t)) (fun _ hx => hx)
    have hopen : IsOpen ((p : C(unitInterval, B)) ⁻¹' (Z.baseSet (Z.indexAt (p t)))) :=
      (Z.isOpen_baseSet (Z.indexAt (p t))).preimage p.continuous
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t (Z.mem_baseSet_at (p t))
    refine ⟨ε / 2, by linarith, fun s hs => ?_⟩
    have hst : abs ((s : ℝ) - (t : ℝ)) < ε / 2 := by
      rw [Subtype.dist_eq, Real.dist_eq] at hs
      exact hs
    have hmemI : ∀ r : unitInterval,
        (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      intro r
      constructor <;> nlinarith [r.2.1, r.2.2, t.2.1, t.2.2, s.2.1, s.2.2]
    have hmemU : ∀ r : unitInterval,
        p ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (s : ℝ), hmemI r⟩
          ∈ Z.baseSet (Z.indexAt (p t)) := by
      intro r
      apply hball
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have hr : abs ((r : ℝ)) ≤ 1 := by rw [abs_of_nonneg r.2.1]; exact r.2.2
      have h2 : abs ((1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (s : ℝ) - (t : ℝ))
          = abs ((r : ℝ)) * abs ((s : ℝ) - (t : ℝ)) := by
        rw [← abs_mul]
        congr 1
        ring_nf
      rw [h2]
      calc abs ((r : ℝ)) * abs ((s : ℝ) - (t : ℝ))
            ≤ 1 * abs ((s : ℝ) - (t : ℝ)) := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
        _ = abs ((s : ℝ) - (t : ℝ)) := one_mul _
        _ < ε := by linarith
    let c : C(unitInterval, ↥(Z.baseSet (Z.indexAt (p t)))) :=
      ⟨fun r => ⟨p ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (s : ℝ), hmemI r⟩, hmemU r⟩, by
        apply Continuous.subtype_mk
        exact p.continuous.comp (Continuous.subtype_mk
          (by fun_prop : Continuous fun r : unitInterval =>
            (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (s : ℝ)) (fun r => hmemI r))⟩
    have hc0 : (c 0 : ↥(Z.baseSet (Z.indexAt (p t)))) = ⟨p t, Z.mem_baseSet_at (p t)⟩ := by
      apply Subtype.ext
      show p ⟨(1 - (0 : ℝ)) * (t : ℝ) + (0 : ℝ) * (s : ℝ), _⟩ = p t
      congr 1
      apply Subtype.ext
      norm_num
    have hc1 : (c 1 : ↥(Z.baseSet (Z.indexAt (p t)))) =
        ⟨p s, hball (by rw [Metric.mem_ball]; linarith)⟩ := by
      apply Subtype.ext
      show p ⟨(1 - (1 : ℝ)) * (t : ℝ) + (1 : ℝ) * (s : ℝ), _⟩ = p s
      congr 1
      apply Subtype.ext
      norm_num
    have hchord := propext (bad_chord Z n T (Z.indexAt (p t)) (fun _ hx => hx) e d hd c)
    rw [show (↑(c 1) : B) = p s from congrArg Subtype.val hc1,
      show (↑(c 0) : B) = p t from congrArg Subtype.val hc0] at hchord
    exact hchord.symm
  have hloc : IsLocallyConstant (fun t : unitInterval => bad Z n T (p t)) := by
    intro P
    refine Metric.isOpen_iff.mpr (fun t ht => ?_)
    obtain ⟨ε, hε, hconst⟩ := key t
    exact ⟨ε, hε, fun s hs => by
      change bad Z n T (p s) ∈ P
      rw [hconst s hs]
      exact ht⟩
  have hmain : bad Z n T (p 0) = bad Z n T (p 1) :=
    hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ (0 : unitInterval))
      (Set.mem_univ (1 : unitInterval))
  rw [p.source, p.target] at hmain
  exact ⟨fun hh => hmain ▸ hh, fun hh => hmain.symm ▸ hh⟩

/-- **The indicator class of the path component of `b`.** -/
noncomputable def ptIndicator (b : B) : Coh ℤ 0 B :=
  indicatorClass (TopCat.toSSet.obj (TopCat.of B))
    {SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)}

/-- **The path component of `b` in `B`, read in the singular simplicial set.** -/
theorem ptEv_ptIndicator_eq_one (b : B) : ptEv b (ptIndicator b) = 1 := by
  change h0Ev (TopCat.toSSet.obj (TopCat.of B))
    ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)
    (indicatorClass (TopCat.toSSet.obj (TopCat.of B))
      {SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)}) = 1
  rw [indicatorClass, h0Ev_classOf]
  exact genEval_indicatorCochain_of_mem _ _ _ (Set.mem_singleton _)

/-- **The singular `π₀`-class of a point determines its path component.** -/
theorem joined_of_pi0_mk_eq {b b' : B}
    (h : SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)
       = SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b')) :
    Joined b b' := by
  have h1 : (TopCat.zerothHomotopyEquiv (X := TopCat.of B)) (ZerothHomotopy.mk (X := B) b)
      = (TopCat.zerothHomotopyEquiv (X := TopCat.of B)) (ZerothHomotopy.mk (X := B) b') := by
    rw [TopCat.zerothHomotopyEquiv_mk, TopCat.zerothHomotopyEquiv_mk]
    exact h
  have h2 : ZerothHomotopy.mk (X := B) b = ZerothHomotopy.mk (X := B) b' :=
    (TopCat.zerothHomotopyEquiv (X := TopCat.of B)).injective h1
  exact Quotient.exact h2

/-- **Every point has a good neighbour in its path component.**  Given that a class of the Thom
pair in degree `0 + n` which dies on every chart piece is zero, the indicator class of the path
component of `b` produces — through the Thom isomorphism, the separation hypothesis and the
fibre-detection on a chart piece — a point `b'` joined to `b` at which the Thom class does not die
on the fibre. -/
theorem exists_good_point_of_separation (Z : RealBundle B F ι) (n : ℕ)
    (hsep : ∀ z : OpenThom Z (0 + n),
      (∀ i : ι, (PieceRes Z (Z.baseSet i) (0 + n)).hom z = 0) → z = 0)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ThomClass Z n) (b : B) :
    ∃ b' : B, Joined b b' ∧ ¬ bad Z n T b' := by
  classical
  have hαne : ptIndicator b ≠ 0 := by
    intro h
    have h1 := ptEv_ptIndicator_eq_one b
    rw [h, ptEv_zero] at h1
    exact one_ne_zero h1.symm
  have hγne : thomMap Z n T.τ 0 (ptIndicator b) ≠ 0 := by
    intro h
    exact hαne ((T.isThom 0).1 (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ : ∃ i : ι, (PieceRes Z (Z.baseSet i) (0 + n)).hom
      (thomMap Z n T.τ 0 (ptIndicator b)) ≠ 0 := by
    by_contra h
    refine hγne (hsep _ (fun i => ?_))
    by_contra hne
    exact h ⟨i, hne⟩
  obtain ⟨d, hd⟩ := exists_coeff (U := Z.baseSet i) Z n T e i (fun _ hx => hx)
  have hpiece : (PieceRes Z (Z.baseSet i) (0 + n)).hom (thomMap Z n T.τ 0 (ptIndicator b))
      = localThomMap Z n (Z.baseSet i) (chartCoh Z n e i (Z.baseSet i) (fun _ hx => hx)) 0
          (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
            ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d) := by
    rw [thomMap_restrict Z n 0 (Z.baseSet i) T.τ (ptIndicator b), hd]
    exact localThomMap_cup_zero Z n (Z.baseSet i)
      (chartCoh Z n e i (Z.baseSet i) (fun _ hx => hx))
      ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d
  obtain ⟨b', hb'U, hb'ne⟩ : ∃ b' : B, ∃ hb' : b' ∈ Z.baseSet i,
      (pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' (Z.baseSet i))
        (Z.proj ⁻¹' ({b'} : Set B)) (Set.preimage_mono (singleton_subset_of_mem hb'))
        (0 + n)).hom
        ((PieceRes Z (Z.baseSet i) (0 + n)).hom (thomMap Z n T.τ 0 (ptIndicator b))) ≠ 0 := by
    by_contra h
    refine hi (eq_zero_of_fibre_eq_zero Z n e i (fun _ hx => hx) _ (fun b' hb' => ?_))
    by_contra hne
    exact h ⟨b', hb', hne⟩
  have hsub : ({(b' : B)} : Set B) ⊆ Z.baseSet i := singleton_subset_of_mem hb'U
  have hy : localThomMap Z n ({(b' : B)} : Set B) (chartCoh Z n e i ({(b' : B)} : Set B) hsub) 0
      ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
        (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
          ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d)) ≠ 0 := by
    rw [← localThomMap_piece_pt (Z := Z) (n := n) e i (U := Z.baseSet i)
      (fun _ hx => hx) b' hb'U hsub
      (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
        ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d)]
    rw [← hpiece]
    exact hb'ne
  have hyne : (CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
      (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
        ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d) ≠ 0 :=
    fun h0 => hy (by rw [h0]; exact map_zero _)
  have hyprod : (CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
        (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
          ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d)
      = cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥({b'} : Set B))) 0 0
          ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
            ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)))
          ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom d) :=
    cupNaturalH ℤ (TopCat.ofHom (ptIncl (Z.baseSet i) b' hb'U)) 0 0 _ _
  have hptne : ptEv b' (ptIndicator b) ≠ 0 ∧ ptEv ⟨b', hb'U⟩ d ≠ 0 := by
    have h1 : ptEv (⟨b', rfl⟩ : ↥({b'} : Set B))
        ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
          (cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0
            ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)) d)) ≠ 0 := by
      intro h0
      exact hyne ((ptEv_eq_zero_iff _).mp (fun p => by
        rw [Subsingleton.elim p ⟨b', rfl⟩]; exact h0))
    have hA : ptEv (⟨b', rfl⟩ : ↥({b'} : Set B))
        ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom
          ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)))
        = ptEv b' (ptIndicator b) := by
      rw [ptEv_pullback (ptIncl (Z.baseSet i) b' hb'U) ⟨b', rfl⟩
          ((CohMap (subtypeMap (Z.baseSet i)) ℤ 0).hom (ptIndicator b)),
        show (ptIncl (Z.baseSet i) b' hb'U) ⟨b', rfl⟩ = ⟨b', hb'U⟩ from Subtype.ext rfl]
      exact ptEv_pullback (subtypeMap (Z.baseSet i)) ⟨b', hb'U⟩ (ptIndicator b)
    have hD : ptEv (⟨b', rfl⟩ : ↥({b'} : Set B))
        ((CohMap (ptIncl (Z.baseSet i) b' hb'U) ℤ 0).hom d) = ptEv ⟨b', hb'U⟩ d := by
      rw [ptEv_pullback (ptIncl (Z.baseSet i) b' hb'U) ⟨b', rfl⟩ d,
        show (ptIncl (Z.baseSet i) b' hb'U) ⟨b', rfl⟩ = ⟨b', hb'U⟩ from Subtype.ext rfl]
    rw [hyprod, ptEv_cup, hA, hD] at h1
    exact ⟨fun h0 => h1 (by rw [h0, zero_mul]), fun h0 => h1 (by rw [h0, mul_zero])⟩
  refine ⟨b', ?_, ?_⟩
  · have hpi : SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b')
        = SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b) := by
      by_contra hne
      have hmem : SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b')
          ∉ ({SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)} :
              Set (SSet.π₀ (TopCat.toSSet.obj (TopCat.of B)))) := by
        rw [Set.mem_singleton_iff]; exact hne
      refine hptne.1 ?_
      change h0Ev (TopCat.toSSet.obj (TopCat.of B))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b')
        (indicatorClass (TopCat.toSSet.obj (TopCat.of B))
          {SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of B)).symm b)}) = 0
      rw [indicatorClass, h0Ev_classOf]
      exact genEval_indicatorCochain_of_not_mem _ _ _ hmem
    exact joined_of_pi0_mk_eq hpi.symm
  · rw [bad_iff_ptEv Z n T i (fun _ hx => hx) e d hd b' hb'U hsub]
    exact hptne.2

/-- **The forgetful map of the pair `(X,∅)` is injective in degree `0`.** -/
theorem relToAbs_empty_injective (X : TopCat) :
    Function.Injective (relToAbs ℤ (∅ : Set X) 0).hom := by
  haveI := Work.Cohomology.relComplex_empty_homology_iso X 0
  exact (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X ∅) 0)).1

/-- **Separation in degree `0`.**  A degree-zero class of the pair `(X,A)`, with `A = ∅`, whose
restriction to each member of an open cover of `X` vanishes is zero. -/
theorem relCoh_zero_of_cover {X : Type} [TopologicalSpace X] {N : Type} (A : Set X) (hA : A = ∅)
    (V : N → Set X) (hV : ∀ i, IsOpen (V i)) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (z : RelCoh ℤ 0 X A)
    (hz : ∀ i, (Work.Cohomology.pdCohRes (TopCat.of X) A (V i) 0).hom z = 0) : z = 0 := by
  subst hA
  refine relToAbs_empty_injective (TopCat.of X) ?_
  rw [map_zero]
  refine Coh_zero_cover_injective_gen V hV hcov _ (fun j => ?_)
  have hsq := relCohMap_relToAbs (subtypeMap (V j))
    (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (V j)) (∅ : Set X)
    (fun x hx => show (x : X) ∈ (∅ : Set X) from hx) ℤ 0
  have hcomp : ((relCohMap (subtypeMap (V j))
        (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (V j))
        (∅ : Set X) (fun x hx => show (x : X) ∈ (∅ : Set X) from hx) ℤ 0)
        ≫ (relToAbs ℤ (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (V j)) 0)).hom z
      = ((relToAbs ℤ (∅ : Set X) 0) ≫ (CohMap (subtypeMap (V j)) ℤ 0)).hom z :=
    congrArg (fun (m : RelCoh ℤ 0 X (∅ : Set X) ⟶ Coh ℤ 0 ↥(V j)) => (ModuleCat.Hom.hom m) z)
      hsq
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  rw [show (relCohMap (subtypeMap (V j))
      (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (V j))
      (∅ : Set X) (fun x hx => show (x : X) ∈ (∅ : Set X) from hx) ℤ 0)
      = (Work.Cohomology.pdCohRes (TopCat.of X) (∅ : Set X) (V j) 0) from rfl] at hcomp
  have hfinal : (ModuleCat.Hom.hom (relToAbs ℤ (Work.Cohomology.interAU (X := TopCat.of X)
      (∅ : Set X) (V j)) 0))
      ((ModuleCat.Hom.hom (Work.Cohomology.pdCohRes (TopCat.of X) (∅ : Set X) (V j) 0)) z) = 0 := by
    rw [hz j]
    exact map_zero _
  exact hcomp.symm.trans hfinal

/-- **Separation for a rank-`0` bundle**: a degree-zero class of the Thom pair which dies on every
chart piece is zero. -/
theorem openThom_zero_of_baseSet_zero (Z : RealBundle B F ι) (hF : Subsingleton F)
    (z : OpenThom Z 0) (hz : ∀ i : ι, (PieceRes Z (Z.baseSet i) 0).hom z = 0) : z = 0 := by
  have hA : zeroComplement Z = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
    rw [mem_zeroComplement] at hp
    exact hp (Subsingleton.elim _ _)
  exact relCoh_zero_of_cover (zeroComplement Z) hA (fun i => Z.proj ⁻¹' (Z.baseSet i))
    (fun i => (Z.isOpen_baseSet i).preimage Z.continuous_proj)
    (fun x => ⟨Z.indexAt (Z.proj x), Z.mem_baseSet_at (Z.proj x)⟩) z hz

/-- **The coefficient of a Thom class over a chart piece is a non-zero-divisor**, given the
separating property of the Thom pair in degree `0 + n`. -/
theorem crux_of_separation [FiniteDimensional ℝ F] (Z : RealBundle B F ι) (n : ℕ)
    (hrank : Z.rank = n)
    (hsep : ∀ z : OpenThom Z (0 + n),
      (∀ i : ι, (PieceRes Z (Z.baseSet i) (0 + n)).hom z = 0) → z = 0)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ThomClass Z n) (i : ι) (W : Set B)
    (hW : W ⊆ Z.baseSet i) (c : Coh ℤ 0 ↥W)
    (hc : (PieceRes Z W n).hom T.τ
      = (Nat.zero_add n) ▸ (localThomMap Z n W (chartCoh Z n e i W hW) 0 c)) :
    ∀ x : Coh ℤ 0 ↥W,
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c = 0 → x = 0 := by
  intro x hx
  have hpt : ∀ (b : B) (hb : b ∈ W), ptEv ⟨b, hb⟩ c ≠ 0 := by
    intro b hb
    have hbsub : ({(b : B)} : Set B) ⊆ Z.baseSet i :=
      fun y hy => hW (singleton_subset_of_mem hb hy)
    have hgood : ¬ bad Z n T b := by
      obtain ⟨b', hjoin, hgbad⟩ := exists_good_point_of_separation Z n hsep e T b
      exact fun hb' => hgbad ((bad_eq_of_joined Z hrank T hjoin).mp hb')
    intro hzero
    exact hgood ((bad_iff_ptEv Z n T i hW e c hc b hb hbsub).mpr hzero)
  refine ptEv_ext (fun p : ↥W => ?_)
  rw [ptEv_zero]
  have h3 : ptEv p (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c) = 0 := by
    rw [hx, ptEv_zero]
  rw [ptEv_cup] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd h (hpt p.1 p.2)
