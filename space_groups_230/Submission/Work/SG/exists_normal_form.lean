import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.NormalForm
import Submission.Work.SG.transLattice_zlattice
import Submission.Work.SG.finite_ball_lattice
import Submission.Work.SG.exists_intMat_of_map_intVec
import Submission.Work.SG.exists_lattice_equiv
import Submission.Work.SG.finite_PtSet

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# exists_normal_form — lattice normal form (hard, ~1.5–2.5k lines)

**Claim.** For `G : CrystallographicGroup 3` there are an integral point group `P`, a cocycle
`τ`, and `φ ∈ Aff(ℝ³)` with `det φ.linear > 0` and `φ G φ⁻¹ = sgSet P τ` (as sets of affine maps).

**Route (no Bieberbach needed: the definition already provides 3 independent translations).**
1. `L := {v | ∃ g ∈ G, IsTranslationBy g v}` is an `AddSubgroup` of `E 3` (translations compose).
   *Discrete*: `IsDiscrete` at `x = 0` makes `{g ∈ G | ‖g 0‖ ≤ ε}` finite, so `L ∩ closedBall 0 ε`
   is finite ⇒ `DiscreteTopology L`. *Spanning*: `cocompact`. Hence `IsZLattice ℝ L`, so
   `Module.Free ℤ L` (`ZLattice.module_free`) and `finrank ℤ L = 3` (`ZLattice.rank`). Take a
   `ℤ`-basis `b : Basis (Fin 3) ℤ L`; if the real matrix `M` with columns `b i` has `det M < 0`,
   negate `b 0`.
2. For `g ∈ G` with linear part `O` (orthogonal): `g ∘ t_v ∘ g⁻¹ = t_{O v}` so `O L = L`.
   Put `A_g := M⁻¹ O M`: integer matrix (maps `ℤ³ → ℤ³`, and so does its inverse) ⇒ `det = ±1`.
3. `P := {A_g | g ∈ G}`. Finite: `O` is determined by `O (b i)`, which lie in the finite set
   `L ∩ sphere 0 ‖b i‖`. `1 ∈ P`, closed under products (`G` is a group).
4. `τ(A) := M⁻¹ (g 0)` for a chosen `g` with `A_g = A` (`Classical.choose`), `0` for `A ∉ P`.
   Two choices differ by a translation in `L`, i.e. by `ℤ³` after `M⁻¹`. The cocycle identity
   holds mod `ℤ³` from `(gh) 0 = g 0 + O_g (h 0)`.
5. `φ := x ↦ M⁻¹ x` (linear, `det = 1/det M > 0`). Then `φ g φ⁻¹ = (x ↦ A_g x + M⁻¹ g 0)`;
   both inclusions of `conjSet φ (affImage G) = sgSet P τ` follow from 4 (for `⊇`, compose the
   chosen `g` with the translation by `M n ∈ L`).

**Mathlib.** `IsZLattice`, `ZLattice.rank`, `ZLattice.module_free`, `Basis`,
`Module.finBasisOfFinrankEq`, `Metric.finite_isBounded_inter_isClosed` / `DiscreteTopology`,
`AffineIsometryEquiv.linearIsometryEquiv`, `LinearIsometryEquiv.norm_map`, `Matrix.toLin'`,
`LinearMap.toMatrix'`, `LinearMap.det_toLin'`.

**Pitfalls.** Coordinates: `E 3 = WithLp 2 (Fin 3 → ℝ)`; move with `WithLp.toLp 2` / `.ofLp`
(`sgSet` is stated that way). `IsTranslationBy g v : ∀ x, g x = x + v` — show it is equivalent to
`g.linear = id ∧ g 0 = v`. Do not try to prove `P` is a subgroup of `O(3)`; only integrality and
finiteness are needed.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

noncomputable section

/-! ## The construction

Given a crystallographic group `G` and a linear equivalence `T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3` carrying
`ℤ³` onto the translation lattice of `G`, we build the associated lattice normal form:
the integral point group, the cocycle, and the conjugating map. -/

/-- Two real-linear endomorphisms of `Fin 3 → ℝ` agreeing on all integer vectors are equal. -/
lemma eq_of_agrees_intVec {f g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)}
    (h : ∀ n : Fin 3 → ℤ, f (intVec n) = g (intVec n)) : f = g := by
  apply (Pi.basisFun ℝ (Fin 3)).ext
  intro j
  have h1 := h (Pi.single j (1 : ℤ))
  simpa [intVec_single_nf j] using h1

/-- `Matrix.toLin'` is injective. -/
lemma eq_of_toLin'_eq {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (h : Matrix.toLin' A = Matrix.toLin' B) : A = B := by
  have h1 := congrArg (LinearMap.toMatrix' (R := ℝ)) h
  simpa using h1

/-- A real linear map carrying `ℤ³` into `ℤ³` is multiplication by an integer matrix. -/
theorem exists_intMat_of_mapIntVec_aux (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hf : ∀ n : Fin 3 → ℤ, ∃ m : Fin 3 → ℤ, f (intVec n) = intVec m) :
    ∃ A : IMat, (∀ n : Fin 3 → ℤ, f (intVec n) = intVec (A.mulVec n)) ∧
      f = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ)) := by
  classical
  let A : IMat := fun i j => Classical.choose (hf (Pi.single j (1 : ℤ))) i
  have hA : ∀ j : Fin 3, f (Pi.single j (1 : ℝ)) = intVec (fun i => A i j) := by
    intro j
    have h := Classical.choose_spec (hf (Pi.single j (1 : ℤ)))
    rw [← intVec_single_nf j]
    exact h
  have hfl : f = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ)) := by
    apply (Pi.basisFun ℝ (Fin 3)).ext
    intro j
    rw [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one, hA j]
    funext i
    simp [intVec]
  refine ⟨A, fun n => ?_, hfl⟩
  rw [hfl, Matrix.toLin'_apply, matMulVec_intVec]

/-- Data for the lattice normal form: a linear equivalence `T` carrying `ℤ³` onto the
translation lattice of a crystallographic group `G`. -/
structure LatticeModel where
  G : CrystallographicGroup 3
  T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3
  hT1 : ∀ n : Fin 3 → ℤ, T (intVec n) ∈ transLattice G.1
  hT2 : ∀ v ∈ transLattice G.1, ∃ n : Fin 3 → ℤ, T.symm v = intVec n

namespace LatticeModel

lemma lmap_intVec_exists (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) :
    ∀ n : Fin 3 → ℤ, ∃ m : Fin 3 → ℤ, lmap M.T g (intVec n) = intVec m := by
  intro n
  obtain ⟨m, hm⟩ := M.hT2 _ (linPart_transLattice hg (M.hT1 n))
  exact ⟨m, by rw [lmap_apply, hm]⟩

lemma Aof_exists (M : LatticeModel) (g : EuclideanIsom 3) :
    ∃ A : IMat, (g ∈ M.G.1 → ∀ n : Fin 3 → ℤ,
        lmap M.T g (intVec n) = intVec (A.mulVec n)) ∧
      (g ∉ M.G.1 → A = 0) := by
  classical
  by_cases hg : g ∈ M.G.1
  · refine ⟨Classical.choose (exists_intMat_of_mapIntVec_aux
        ((lmap M.T g) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (M.lmap_intVec_exists g hg)), ?_, ?_⟩
    · intro _
      exact (Classical.choose_spec (exists_intMat_of_mapIntVec_aux
        ((lmap M.T g) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (M.lmap_intVec_exists g hg))).1
    · intro h; exact absurd hg h
  · exact ⟨0, fun h => absurd h hg, fun _ => rfl⟩

/-- The integer matrix of the linear part of `g` in the coordinates of `T`. -/
noncomputable def Aof (M : LatticeModel) (g : EuclideanIsom 3) : IMat :=
  Classical.choose (M.Aof_exists g)

lemma Aof_spec (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) :
    ∀ n : Fin 3 → ℤ, lmap M.T g (intVec n) = intVec ((M.Aof g).mulVec n) := by
  have h := (Classical.choose_spec (M.Aof_exists g)).1 hg
  rw [Aof]
  exact h

lemma Aof_toLin (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) :
    (lmap M.T g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
      = Matrix.toLin' ((M.Aof g).map (Int.cast : ℤ → ℝ)) := by
  apply eq_of_agrees_intVec
  intro n
  rw [Matrix.toLin'_apply, matMulVec_intVec]
  exact M.Aof_spec g hg n

lemma eq_Aof_of_toLin (M : LatticeModel) {g : EuclideanIsom 3} (hg : g ∈ M.G.1) {A : IMat}
    (h : (lmap M.T g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
      = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))) : A = M.Aof g := by
  have h1 : Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))
      = Matrix.toLin' ((M.Aof g).map (Int.cast : ℤ → ℝ)) := h.symm.trans (M.Aof_toLin g hg)
  exact Matrix.map_injective (fun _ _ hx => Int.cast_injective hx) (eq_of_toLin'_eq h1)

lemma lmap_eq_of_Aof_eq (M : LatticeModel) {g g' : EuclideanIsom 3} (hg : g ∈ M.G.1)
    (hg' : g' ∈ M.G.1) (h : M.Aof g = M.Aof g') :
    (lmap M.T g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
      = (lmap M.T g' : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
  rw [M.Aof_toLin g hg, M.Aof_toLin g' hg', h]

lemma linPart_eq_of_lmap_eq (M : LatticeModel) {g g' : EuclideanIsom 3}
    (h : lmap M.T g = lmap M.T g') : linPart g = linPart g' := by
  apply LinearEquiv.ext
  intro v
  have key : ∀ g : EuclideanIsom 3, linPart g v = M.T (lmap M.T g (M.T.symm v)) := by
    intro g
    rw [lmap_apply]
    simp
  rw [key g, key g', h]

/-- Two elements of `G` with the same matrix differ by a lattice translation. -/
lemma tau_diff (M : LatticeModel) {g g' : EuclideanIsom 3} (hg : g ∈ M.G.1)
    (hg' : g' ∈ M.G.1) (h : lmap M.T g = lmap M.T g') :
    ∃ n : Fin 3 → ℤ, M.T.symm (g 0) = M.T.symm (g' 0) + intVec n := by
  have hlin : linPart g = linPart g' := M.linPart_eq_of_lmap_eq h
  have h1 : linPart (g * g'⁻¹) = 1 := by
    rw [linPart_mul, hlin, linPart_inv, mul_inv_cancel]
  have h2 : IsTranslationBy (g * g'⁻¹) ((g * g'⁻¹) 0) :=
    (isTranslationBy_iff _ _).mpr ⟨h1, rfl⟩
  obtain ⟨n, hn⟩ := M.hT2 _ (mem_transLattice.mpr
    ⟨g * g'⁻¹, M.G.1.mul_mem hg (M.G.1.inv_mem hg'), h2⟩)
  have h5 : (g * g'⁻¹) (g' 0) = g 0 := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    simp
  have h3 : g 0 = g' 0 + (g * g'⁻¹) 0 := by
    have h4 : (g * g'⁻¹) (g' 0) = linPart (g * g'⁻¹) (g' 0) + (g * g'⁻¹) 0 :=
      linPart_apply (g * g'⁻¹) (g' 0)
    rw [h1] at h4
    simp only [LinearEquiv.coe_one, id_eq] at h4
    rw [h5] at h4
    exact h4
  exact ⟨n, by rw [h3, map_add, hn]⟩

end LatticeModel
namespace LatticeModel

/-- The point group of the model: the integer matrices of the linear parts of `G`. -/
def Pt (M : LatticeModel) : Set IMat := {A | ∃ g ∈ M.G.1, A = M.Aof g}

lemma Aof_mem_Pt (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) : M.Aof g ∈ M.Pt :=
  ⟨g, hg, rfl⟩

lemma eq_Aof_of_spec (M : LatticeModel) {g : EuclideanIsom 3} (hg : g ∈ M.G.1) {A : IMat}
    (h : ∀ n : Fin 3 → ℤ, lmap M.T g (intVec n) = intVec (A.mulVec n)) : A = M.Aof g := by
  refine M.eq_Aof_of_toLin hg ?_
  apply eq_of_agrees_intVec
  intro n
  rw [Matrix.toLin'_apply, matMulVec_intVec]
  exact h n

lemma eq_Aof_iff (M : LatticeModel) {g h : EuclideanIsom 3} (hg : g ∈ M.G.1) (hh : h ∈ M.G.1) :
    M.Aof g = M.Aof h ↔ lmap M.T g = lmap M.T h := by
  constructor
  · intro h'
    have h1 : (lmap M.T g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
        = (lmap M.T h : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := M.lmap_eq_of_Aof_eq hg hh h'
    exact LinearEquiv.ext fun x => LinearMap.congr_fun h1 x
  · intro h'
    refine M.eq_Aof_of_toLin hh ?_
    rw [← h']
    exact M.Aof_toLin g hg

lemma Aof_one (M : LatticeModel) : M.Aof 1 = 1 := by
  symm
  refine M.eq_Aof_of_spec M.G.1.one_mem ?_
  intro n
  rw [lmap_one]
  simp

lemma Aof_mul (M : LatticeModel) (g h : EuclideanIsom 3) (hg : g ∈ M.G.1) (hh : h ∈ M.G.1) :
    M.Aof (g * h) = M.Aof g * M.Aof h := by
  symm
  refine M.eq_Aof_of_toLin (M.G.1.mul_mem hg hh) ?_
  rw [toLin'_matMap_mul, ← M.Aof_toLin g hg, ← M.Aof_toLin h hh, lmap_mul]
  rfl

lemma Aof_mul_inv (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) :
    M.Aof g * M.Aof g⁻¹ = 1 := by
  rw [← M.Aof_mul g g⁻¹ hg (M.G.1.inv_mem hg), mul_inv_cancel, M.Aof_one]

lemma Pt_mul (M : LatticeModel) {A B : IMat} (hA : A ∈ M.Pt) (hB : B ∈ M.Pt) :
    A * B ∈ M.Pt := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨h, hh, rfl⟩ := hB
  exact ⟨g * h, M.G.1.mul_mem hg hh, (M.Aof_mul g h hg hh).symm⟩

lemma Pt_det_isUnit (M : LatticeModel) {A : IMat} (hA : A ∈ M.Pt) : IsUnit A.det := by
  obtain ⟨g, hg, rfl⟩ := hA
  refine IsUnit.of_mul_eq_one (M.Aof g⁻¹).det ?_
  rw [← Matrix.det_mul, M.Aof_mul_inv g hg, Matrix.det_one]

lemma Pt_finite (M : LatticeModel) : M.Pt.Finite := by
  refine (finite_PtSet M.G M.T M.hT1 M.hT2).subset ?_
  intro A hA
  obtain ⟨g, hg, rfl⟩ := hA
  exact ⟨g, hg, M.Aof_spec g hg⟩

lemma Pt_isIntPointGroup (M : LatticeModel) : IsIntPointGroup M.Pt :=
  ⟨M.Pt_finite, ⟨1, M.G.1.one_mem, M.Aof_one.symm⟩,
    fun _ hA _ hB => M.Pt_mul hA hB, fun _ hA => M.Pt_det_isUnit hA⟩

lemma tau_exists (M : LatticeModel) (A : IMat) :
    ∃ t : Fin 3 → ℝ, (A ∈ M.Pt → ∃ g ∈ M.G.1, A = M.Aof g ∧ t = M.T.symm (g 0)) ∧
      (A ∉ M.Pt → t = 0) := by
  classical
  by_cases hA : A ∈ M.Pt
  · obtain ⟨g, hg, hAg⟩ := hA
    exact ⟨M.T.symm (g 0), fun _ => ⟨g, hg, hAg, rfl⟩, fun h => absurd ⟨g, hg, hAg⟩ h⟩
  · exact ⟨0, fun h => absurd h hA, fun _ => rfl⟩

/-- The translation cocycle of the model. -/
noncomputable def tau (M : LatticeModel) : IMat → Fin 3 → ℝ :=
  fun A => Classical.choose (M.tau_exists A)

lemma tau_spec (M : LatticeModel) {A : IMat} (hA : A ∈ M.Pt) :
    ∃ g ∈ M.G.1, A = M.Aof g ∧ M.tau A = M.T.symm (g 0) :=
  (Classical.choose_spec (M.tau_exists A)).1 hA

/-- The cocycle identity for `tau`. -/
lemma tau_cocycle (M : LatticeModel) {A B : IMat} (hA : A ∈ M.Pt) (hB : B ∈ M.Pt) :
    ∃ n : Fin 3 → ℤ, M.tau (A * B) =
      M.tau A + (A.map (Int.cast : ℤ → ℝ)).mulVec (M.tau B) + intVec n := by
  obtain ⟨g, hg, hAg, htg⟩ := M.tau_spec hA
  obtain ⟨g', hg', hBg, htg'⟩ := M.tau_spec hB
  have hAB : A * B ∈ M.Pt := M.Pt_mul hA hB
  have hAB' : A * B = M.Aof (g * g') := by
    rw [hAg, hBg, M.Aof_mul g g' hg hg']
  obtain ⟨k, hk, hkAB, htk⟩ := M.tau_spec hAB
  have hAof : M.Aof k = M.Aof (g * g') := by
    rw [← hkAB, hAB']
  have hkl : lmap M.T k = lmap M.T (g * g') :=
    (M.eq_Aof_iff hk (M.G.1.mul_mem hg hg')).mp hAof
  obtain ⟨n₁, hn₁⟩ := M.tau_diff hk (M.G.1.mul_mem hg hg') hkl
  refine ⟨n₁, ?_⟩
  rw [htk, hn₁]
  have hgg : (g * g') 0 = linPart g (g' 0) + g 0 := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    exact linPart_apply g (g' 0)
  rw [hgg, map_add]
  have hkey : M.T.symm (linPart g (g' 0)) = (A.map (Int.cast : ℤ → ℝ)).mulVec (M.tau B) := by
    rw [htg', hAg, ← Matrix.toLin'_apply, ← M.Aof_toLin g hg]
    rw [lmap_coe_apply]
    simp
  rw [htg, hkey]
  abel

/-- The conjugating affine map `x ↦ T⁻¹ x`. -/
noncomputable def phiOf (M : LatticeModel) : AffineGroup 3 :=
  AffineEquiv.mk' (fun x => affLin M.T x) (affLin M.T) 0 (by intro x; simp [vsub_eq_sub])

lemma phiOf_apply (M : LatticeModel) (x : E 3) : M.phiOf x = affLin M.T x := rfl

lemma phiOf_zero (M : LatticeModel) : M.phiOf 0 = 0 := by
  rw [phiOf_apply, map_zero]

lemma phiOf_inv_apply (M : LatticeModel) (y : E 3) : M.phiOf⁻¹ y = (affLin M.T).symm y := by
  have h : M.phiOf ((affLin M.T).symm y) = y := by
    rw [phiOf_apply, LinearEquiv.apply_symm_apply]
  calc M.phiOf⁻¹ y = M.phiOf⁻¹ (M.phiOf ((affLin M.T).symm y)) := by rw [h]
    _ = (affLin M.T).symm y := AffineEquiv.symm_apply_apply M.phiOf _

lemma phiOf_linear (M : LatticeModel) : M.phiOf.linear = affLin M.T := rfl

/-- The conjugation formula for a single element of `G`. -/
lemma conj_eval (M : LatticeModel) (g : EuclideanIsom 3) (hg : g ∈ M.G.1) (x : E 3) :
    (M.phiOf * g.toAffineEquiv * M.phiOf⁻¹) x =
      WithLp.toLp 2 (((M.Aof g).map (Int.cast : ℤ → ℝ)).mulVec x.ofLp + M.T.symm (g 0)) := by
  rw [AffineEquiv.coe_mul, AffineEquiv.coe_mul, Function.comp_apply, Function.comp_apply]
  rw [M.phiOf_inv_apply, toAffineEquiv_apply_eq, linPart_apply, M.phiOf_apply, map_add]
  have h2 : affLin M.T (linPart g ((affLin M.T).symm x))
      = WithLp.toLp 2 (((M.Aof g).map (Int.cast : ℤ → ℝ)).mulVec x.ofLp) := by
    have h1 : (affLin M.T).symm x = M.T x.ofLp := by
      rw [affLin_symm_apply, coordLin_apply]
    rw [h1, affLin_apply]
    congr 1
    rw [← Matrix.toLin'_apply, ← M.Aof_toLin g hg]
    rfl
  have h3 : affLin M.T (g 0) = WithLp.toLp 2 (M.T.symm (g 0)) := rfl
  rw [h2, h3, ← toLp_add]

lemma conj_subset (M : LatticeModel) : conjSet M.phiOf (affImage M.G.1) ⊆ sgSet M.Pt M.tau := by
  rintro h ⟨g, ⟨g₀, hg₀, rfl⟩, rfl⟩
  obtain ⟨g₁, hg₁, hAg₁, htg₁⟩ := M.tau_spec (M.Aof_mem_Pt g₀ hg₀)
  have hll : lmap M.T g₀ = lmap M.T g₁ := (M.eq_Aof_iff hg₀ hg₁).mp hAg₁
  obtain ⟨n, hn⟩ := M.tau_diff hg₀ hg₁ hll
  refine ⟨M.Aof g₀, M.Aof_mem_Pt g₀ hg₀, n, fun x => ?_⟩
  rw [M.conj_eval g₀ hg₀ x, hn, ← htg₁, add_assoc]

lemma conj_affLin (M : LatticeModel) :
    coordLin.symm ≪≫ₗ affLin M.T ≪≫ₗ coordLin = (M.T.trans coordLin).symm := by
  rw [LinearEquiv.trans_symm]
  rfl

lemma det_affLin (M : LatticeModel) :
    LinearEquiv.det (affLin M.T) = LinearEquiv.det ((M.T.trans coordLin).symm) := by
  have h := LinearEquiv.det_conj (affLin M.T) coordLin
  rw [conj_affLin M] at h
  exact h.symm

lemma sgSet_subset_conj (M : LatticeModel) :
    sgSet M.Pt M.tau ⊆ conjSet M.phiOf (affImage M.G.1) := by
  rintro h ⟨A, hA, n, hx⟩
  obtain ⟨g', hg', hAg', htg'⟩ := M.tau_spec hA
  obtain ⟨t, ht, htt⟩ := mem_transLattice.mp (M.hT1 n)
  have hlin_t : linPart t = 1 := ((isTranslationBy_iff t (M.T (intVec n))).mp htt).1
  have ht0 : t 0 = M.T (intVec n) := by
    have h := htt 0
    simpa using h
  set g : EuclideanIsom 3 := t * g' with hgdef
  have hgmem : g ∈ M.G.1 := M.G.1.mul_mem ht hg'
  have hll : lmap M.T g = lmap M.T g' := by
    rw [hgdef, lmap_mul]
    have hlt : lmap M.T t = 1 := by
      rw [lmap, hlin_t]
      ext x
      simp
    rw [hlt]
    ext x
    simp [LinearEquiv.mul_apply]
  have hAof : M.Aof g = A := by
    rw [hAg']
    exact (M.eq_Aof_iff hgmem hg').mpr hll
  have hg0 : M.T.symm (g 0) = M.tau A + intVec n := by
    have h1 : g 0 = linPart t (g' 0) + t 0 := by
      rw [hgdef, AffineIsometryEquiv.coe_mul, Function.comp_apply]
      exact linPart_apply t (g' 0)
    calc M.T.symm (g 0) = M.T.symm (linPart t (g' 0) + t 0) := by rw [h1]
      _ = M.T.symm (g' 0 + t 0) := by rw [hlin_t]; simp
      _ = M.T.symm (g' 0 + M.T (intVec n)) := by rw [ht0]
      _ = M.T.symm (g' 0) + M.T.symm (M.T (intVec n)) := by rw [map_add]
      _ = M.T.symm (g' 0) + intVec n := by rw [LinearEquiv.symm_apply_apply]
      _ = M.tau A + intVec n := by rw [← htg']
  refine ⟨g.toAffineEquiv, ⟨g, hgmem, rfl⟩, ?_⟩
  ext x
  rw [hx x, M.conj_eval g hgmem x, hAof, hg0]
  simp only [add_assoc]

end LatticeModel

/-- Every lattice model produces a normal form. -/
theorem normal_form_of_lattice (M : LatticeModel)
    (hdet : 0 < (((LinearEquiv.det (M.T.trans coordLin)) : ℝˣ) : ℝ)) :
    ∃ P : Set IMat, ∃ τ : IMat → Fin 3 → ℝ, IsIntPointGroup P ∧ IsIntCocycle P τ ∧
      ∃ φ : AffineGroup 3, 0 < (φ.linear.det : ℝ) ∧ conjSet φ (affImage M.G.1) = sgSet P τ := by
  refine ⟨M.Pt, M.tau, M.Pt_isIntPointGroup, fun A hA B hB => M.tau_cocycle hA hB,
    M.phiOf, ?_, ?_⟩
  · rw [M.phiOf_linear, M.det_affLin, LinearEquiv.det_symm]
    have hprod : (((LinearEquiv.det ((M.T.trans coordLin)⁻¹)) : ℝˣ) : ℝ)
        * (((LinearEquiv.det (M.T.trans coordLin)) : ℝˣ) : ℝ) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have h1 : 0 < (((LinearEquiv.det ((M.T.trans coordLin)⁻¹)) : ℝˣ) : ℝ)
        * (((LinearEquiv.det (M.T.trans coordLin)) : ℝˣ) : ℝ) := by
      rw [hprod]
      norm_num
    exact pos_of_mul_pos_left h1 (le_of_lt hdet)
  · exact Set.Subset.antisymm M.conj_subset M.sgSet_subset_conj


/-- Lattice normal form: every crystallographic group is conjugate, by an affine map of positive
determinant, to `sgSet P τ` for an integral point group `P` and a cocycle `τ`
(translation lattice `ℤ³`). -/
theorem exists_normal_form (G : CrystallographicGroup 3) :
    ∃ P : Set IMat, ∃ τ : IMat → Fin 3 → ℝ, IsIntPointGroup P ∧ IsIntCocycle P τ ∧
      ∃ φ : AffineGroup 3, 0 < (φ.linear.det : ℝ) ∧ conjSet φ (affImage G.1) = sgSet P τ := by
  obtain ⟨hD, hZ, T, hT1, hT2, hdet⟩ := exists_lattice_equiv G
  exact normal_form_of_lattice ⟨G, T, hT1, hT2⟩ hdet

end

end Work.SG
