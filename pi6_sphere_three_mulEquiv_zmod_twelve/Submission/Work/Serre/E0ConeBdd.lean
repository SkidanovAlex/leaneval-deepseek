import Mathlib
import Submission.Work.Serre.E0Assembly
import Submission.Work.Serre.e0CubeBoundaryExtension
import Submission.Work.RatHurewicz.ConnectivityBridge

set_option synthInstance.maxHeartbeats 400000


local instance instSubsingletonStdSimplexZeroE0 : Subsingleton ↑(stdSimplex ℝ (Fin (0 + 1))) := by
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
  infer_instance

/-!
# SUBPROJECT SERRE — E0 in range form: cone data in degrees `≤ N`

This file constructs `Work.Serre.SSetConeDataBdd (singSSet X) N` from the vanishing of
`πᵢ(X,x₀)` for `i ≤ N`, i.e. the geometric half of `Work.Serre.SerreE0Range`.  Together with
`Work.Serre.e0ChainAlgebra` (the chain-algebra half) this gives `serreE0Range`.

## The construction

`SSetConeDataBdd K N` is the "cone data" of `Submission/Work/Serre/E0Assembly.lean`: for every
`n ≤ N` and every singular `n`-simplex `s` a filler `H n s : K_{n+1}` whose *last* face is `s`
and whose `i`-th face (`i < n+1`) is `H n' (δᵢ s)`.  It is built by induction on `N`:

* the key point is that the *prescribed* boundary of the filler of `s` is a map
  `∂Δ^{n+1} ≅ Sⁿ → X` which is null-homotopic as soon as `πₙ(X) = 0` (`π₀ = 0` supplies the
  path connectedness needed to move the basepoint), so it extends over `Δ^{n+1}`;
* concretely the extension is produced by `Work.Serre.exists_simplexFiller`, whose only input is
  the boundary-extension property of cubes, `Work.Serre.e0CubeBoundaryExtension`;
* the *matching* condition of `exists_simplexFiller` (that two faces of the filler agree on their
  common sub-face) is a formal consequence of the cone data at the previous level
  (`face_cast`, `face_last`) and the simplicial identity `SimplicialObject.δ_comp_δ'`;
* the induction starts at degree `1`, where the prescribed boundary of the filler of a path is
  consistent only if the degree-`0` fillers have a *constant* first face; this is why the degree
  `0` fillers are the chosen paths from a fixed basepoint `x₀`.
-/

set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

variable {X : Type} [TopologicalSpace X]

/-! ## The point of `Δ⁰` and the cofaces -/

/-- The unique point of the standard `0`-simplex `Δ⁰`. -/
def pt0 : ↥(stdSimplex ℝ (Fin 1)) := default

/-- `Δ⁰` is a single point, which is the vertex `0`. -/
theorem pt0_eq_vertex : pt0 = stdSimplex.vertex (0 : Fin 1) := by
  ext x
  rw [show x = (0 : Fin 1) from Subsingleton.elim x 0]
  simp only [pt0, stdSimplex.vertex_coe, Pi.single_eq_same]
  exact stdSimplex.eq_one_of_unique _ _

/-- The coface `δ⁰₀ : Δ⁰ → Δ¹` sends the point of `Δ⁰` to the vertex `1` of `Δ¹`. -/
theorem coface_zero_zero_pt0 : coface 0 (0 : Fin 2) pt0 = stdSimplex.vertex (1 : Fin 2) := by
  rw [coface_apply, pt0_eq_vertex, stdSimplex.map_vertex]
  congr 1

/-- The coface `δ⁰₁ : Δ⁰ → Δ¹` sends the point of `Δ⁰` to the vertex `0` of `Δ¹`. -/
theorem coface_zero_one_pt0 : coface 0 (1 : Fin 2) pt0 = stdSimplex.vertex (0 : Fin 2) := by
  rw [coface_apply, pt0_eq_vertex, stdSimplex.map_vertex]
  congr 1

/-! ## Paths as `1`-simplices -/

/-- The coordinate of `Δ¹` used by `pathToSimplex`: the point `z` is sent to `1 - z 1`. -/
theorem pathFun_mem (z : ↥(stdSimplex ℝ (Fin 2))) : 1 - z 1 ∈ unitInterval := by
  have h1 : (0 : ℝ) ≤ z 1 := z.2.1 1
  have h2 : z 0 + z 1 = 1 := stdSimplex.add_eq_one z
  have h0 : (0 : ℝ) ≤ z 0 := z.2.1 0
  exact ⟨by linarith, by linarith⟩

/-- The underlying map `Δ¹ → I` of `pathToSimplex`. -/
def pathFun (γ : C(unitInterval, X)) (z : ↥(stdSimplex ℝ (Fin 2))) : unitInterval :=
  ⟨1 - z 1, pathFun_mem z⟩

/-- The underlying map of `pathToSimplex` is continuous. -/
theorem pathFun_continuous (γ : C(unitInterval, X)) : Continuous (pathFun γ) := by
  refine Continuous.subtype_mk ?_ pathFun_mem
  exact continuous_const.sub ((continuous_apply 1).comp continuous_subtype_val)

/-- A path `γ : I → X` turned into a continuous map `Δ¹ → X` whose first face is `γ 0` and whose
last face is `γ 1`. -/
def pathToSimplex (γ : C(unitInterval, X)) : C(↥(stdSimplex ℝ (Fin 2)), X) :=
  γ.comp ⟨pathFun γ, pathFun_continuous γ⟩

/-- The value of `pathToSimplex γ`. -/
theorem pathToSimplex_apply (γ : C(unitInterval, X)) (z : ↥(stdSimplex ℝ (Fin 2))) :
    pathToSimplex γ z = γ (pathFun γ z) := rfl

/-- At the vertex `1` of `Δ¹` the parametrisation is `0`. -/
theorem pathFun_vertex_one (γ : C(unitInterval, X)) :
    pathFun γ (stdSimplex.vertex (1 : Fin 2)) = 0 := by
  apply Subtype.ext
  show 1 - (stdSimplex.vertex (1 : Fin 2) : Fin 2 → ℝ) 1 = ((0 : unitInterval) : ℝ)
  rw [stdSimplex.vertex_coe, Pi.single_eq_same]
  norm_num

/-- At the vertex `0` of `Δ¹` the parametrisation is `1`. -/
theorem pathFun_vertex_zero (γ : C(unitInterval, X)) :
    pathFun γ (stdSimplex.vertex (0 : Fin 2)) = 1 := by
  apply Subtype.ext
  show 1 - (stdSimplex.vertex (0 : Fin 2) : Fin 2 → ℝ) 1 = ((1 : unitInterval) : ℝ)
  rw [stdSimplex.vertex_coe, Pi.single_eq_of_ne (by decide)]
  norm_num

/-- The first face of `pathToSimplex γ` is the constant map at the initial point of `γ`. -/
theorem pathToSimplex_comp_coface_zero (γ : C(unitInterval, X)) :
    (pathToSimplex γ).comp (coface 0 (0 : Fin 2)) = ContinuousMap.const _ (γ 0) := by
  ext z
  have hz : z = pt0 := Subsingleton.elim z pt0
  rw [hz, ContinuousMap.comp_apply, coface_zero_zero_pt0, pathToSimplex_apply,
    pathFun_vertex_one]
  rfl

/-- The last face of `pathToSimplex γ` is the constant map at the final point of `γ`. -/
theorem pathToSimplex_comp_coface_one (γ : C(unitInterval, X)) :
    (pathToSimplex γ).comp (coface 0 (1 : Fin 2)) = ContinuousMap.const _ (γ 1) := by
  ext z
  have hz : z = pt0 := Subsingleton.elim z pt0
  rw [hz, ContinuousMap.comp_apply, coface_zero_one_pt0, pathToSimplex_apply,
    pathFun_vertex_zero]
  rfl


/-! ## The degree-zero filler: the paths from a basepoint -/

/-- The path from `x₀` to `y` chosen by `PathConnectedSpace.joined`, viewed as a map
`Δ¹ → X`.  Its first face is the constant map at `x₀` and its last face is the vertex `y`. -/
def baseEdge (x₀ : X) [PathConnectedSpace X] (y : X) : C(↥(stdSimplex ℝ (Fin 2)), X) :=
  pathToSimplex ((PathConnectedSpace.joined x₀ y).somePath : C(unitInterval, X))

/-- The first face of `baseEdge x₀ y` is the constant map at `x₀`. -/
theorem baseEdge_comp_coface_zero (x₀ : X) [PathConnectedSpace X] (y : X) :
    (baseEdge x₀ y).comp (coface 0 (0 : Fin 2)) = ContinuousMap.const _ x₀ := by
  rw [baseEdge, pathToSimplex_comp_coface_zero]
  congr 1
  exact Path.source _

/-- The last face of `baseEdge x₀ y` is the constant map at `y`. -/
theorem baseEdge_comp_coface_one (x₀ : X) [PathConnectedSpace X] (y : X) :
    (baseEdge x₀ y).comp (coface 0 (1 : Fin 2)) = ContinuousMap.const _ y := by
  rw [baseEdge, pathToSimplex_comp_coface_one]
  congr 1
  exact Path.target _

/-- **The degree-zero filler**: the chosen path from the basepoint to the point of a
`0`-simplex. -/
def cone0 (x₀ : X) [PathConnectedSpace X] :
    (singSSet X).obj (Opposite.op (⦋0⦌ : SimplexCategory)) →
      (singSSet X).obj (Opposite.op (⦋1⦌ : SimplexCategory)) :=
  fun s => simplexOf 1 (baseEdge x₀ ((concretize s) pt0))

/-- The concrete map of `cone0`. -/
theorem concretize_cone0 (x₀ : X) [PathConnectedSpace X]
    (s : (singSSet X).obj (Opposite.op (⦋0⦌ : SimplexCategory))) :
    concretize (cone0 x₀ s) = baseEdge x₀ ((concretize s) pt0) :=
  concretize_simplexOf (n := 1) _

/-- The two faces of `cone0`: the first is the constant map at the basepoint, the last is the
constant map at the point of `s`. -/
theorem concretize_face_cone0 (x₀ : X) [PathConnectedSpace X]
    (s : (singSSet X).obj (Opposite.op (⦋0⦌ : SimplexCategory))) :
    concretize ((singSSet X).δ (0 : Fin 2) (cone0 x₀ s)) = ContinuousMap.const _ x₀ ∧
      concretize ((singSSet X).δ (1 : Fin 2) (cone0 x₀ s)) =
        ContinuousMap.const _ ((concretize s) pt0) := by
  constructor
  · rw [concretize_face (cone0 x₀ s) (0 : Fin 2), concretize_cone0]
    exact baseEdge_comp_coface_zero x₀ ((concretize s) pt0)
  · rw [concretize_face (cone0 x₀ s) (1 : Fin 2), concretize_cone0]
    exact baseEdge_comp_coface_one x₀ ((concretize s) pt0)

/-! ## Abbreviations for the singular simplices -/

/-- The `n`-simplices of the singular simplicial set of `X`. -/
abbrev Simp (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  (singSSet X).obj (Opposite.op (SimplexCategory.mk n))

/-- The `i`-th face of a singular `(n+1)`-simplex. -/
abbrev simFace (X : Type) [TopologicalSpace X] (n : ℕ) (i : Fin (n + 2)) :
    Simp X (n + 1) → Simp X n :=
  CategoryTheory.SimplicialObject.δ (singSSet X) i

/-! ## The base of the induction -/

/-! ## Normalised simplicial identities -/

/-- The simplicial identity `dᵢ dⱼ = d_{j-1} dᵢ` for `i < j`, in the coordinates of the
simplicial set. -/
theorem delta_comp_delta_apply {K : SSet} {k : ℕ} (s : K _⦋k+2⦌) (i : Fin (k+2))
    (j : Fin (k+3)) (h : i.val < j.val) :
    K.δ i (K.δ j s) =
      K.δ (⟨j.val - 1, by omega⟩ : Fin (k+2)) (K.δ (⟨i.val, by omega⟩ : Fin (k+3)) s) := by
  have hh : i.castSucc < j := by
    show i.val < j.val
    exact h
  have h2 := congrArg (fun φ : K _⦋k+2⦌ ⟶ K _⦋k⦌ => (ConcreteCategory.hom φ) s)
    (SimplicialObject.δ_comp_δ' (X := K) (n := k) (i := i) (j := j) hh)
  simp only [ConcreteCategory.comp_apply] at h2
  simpa only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.pred, Fin.subNat] using h2

/-- The degeneracy identity `d_{i+1} σᵢ = id`. -/
theorem delta_comp_sigma_apply {K : SSet} {n : ℕ} (i : Fin (n+1)) (s : K _⦋n⦌) :
    K.δ (⟨i.val + 1, by omega⟩ : Fin (n+2)) (K.σ i s) = s := by
  have h2 := congrArg (fun φ : K _⦋n⦌ ⟶ K _⦋n⦌ => (ConcreteCategory.hom φ) s)
    (SimplicialObject.δ_comp_σ_succ (X := K) (n := n) (i := i))
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, Fin.succ] using h2

/-! ## Cheap index bounds -/

theorem fin3_lt2 (i j : Fin 3) (hij : i < j) : i.val < 2 := by
  have h : i.val < j.val := by simpa only [Fin.lt_def] using hij
  have := j.isLt
  omega

theorem fin3_pred_lt2 (j : Fin 3) : j.val - 1 < 2 := by
  have := j.isLt
  omega

theorem fin_lt_of_lt {k : ℕ} (i j : Fin (k+3)) (h : i.val < j.val) : i.val < k + 2 := by
  have := j.isLt
  omega

theorem fin_idx_lt {k : ℕ} (i : Fin (k+4)) (h : i.val ≠ k + 3) : i.val < k + 3 := by
  have := i.isLt
  omega

theorem fin_pred_lt {k : ℕ} (j : Fin (k+3)) : j.val - 1 < k + 2 := by
  have := j.isLt
  omega

theorem fin3_lt_of_pred {k : ℕ} (j : Fin (k+3)) : j.val - 1 < k + 3 := by
  have := j.isLt
  omega

theorem fin_lt_self {k : ℕ} (i : Fin (k+3)) : i.val < k + 3 := i.isLt

/-! ## The cone operator patched at one degree -/

/-- Replace the value of the cone operator `H` at degree `N` by `Hnew`. -/
def patchH {K : SSet} (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (N : ℕ)
    (Hnew : K _⦋N⦌ → K _⦋N+1⦌) : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌ :=
  fun n s => if hn : n = N then hn.symm ▸ (Hnew (hn ▸ s)) else H n s

theorem patchH_self {K : SSet} (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (N : ℕ)
    (Hnew : K _⦋N⦌ → K _⦋N+1⦌) (s : K _⦋N⦌) : patchH H N Hnew N s = Hnew s := by
  rw [patchH, dif_pos rfl]

theorem patchH_of_ne {K : SSet} (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (N : ℕ)
    (Hnew : K _⦋N⦌ → K _⦋N+1⦌) {n : ℕ} (hn : n ≠ N) (s : K _⦋n⦌) :
    patchH H N Hnew n s = H n s := by
  rw [patchH, dif_neg hn]

/-- The junk value of the cone operator in degrees above the range where it is constrained. -/
def junkH (K : SSet) : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌ :=
  fun n s => SimplicialObject.σ K (0 : Fin (n+1)) s

/-! ## The base of the induction: cone data in degree `1` -/

/-- The prescribed faces of the degree-`1` filler attached to `s`. -/
def coneFaceFamily (H0 : Simp X 0 → Simp X 1) (s : Simp X 1) :
    Fin 3 → C(↥(stdSimplex ℝ (Fin 2)), X) :=
  Fin.lastCases (concretize s) (fun k : Fin 2 => concretize (H0 (simFace X 0 k s)))

@[simp]
theorem coneFaceFamily_castSucc (H0 : Simp X 0 → Simp X 1) (s : Simp X 1) (k : Fin 2) :
    coneFaceFamily H0 s (Fin.castSucc k) = concretize (H0 (simFace X 0 k s)) := by
  change Fin.lastCases (concretize s) (fun k : Fin 2 => concretize (H0 (simFace X 0 k s)))
    (Fin.castSucc k) = concretize (H0 (simFace X 0 k s))
  exact Fin.lastCases_castSucc k

@[simp]
theorem coneFaceFamily_last (H0 : Simp X 0 → Simp X 1) (s : Simp X 1) :
    coneFaceFamily H0 s (Fin.last 2) = concretize s := by
  change Fin.lastCases (concretize s) (fun k : Fin 2 => concretize (H0 (simFace X 0 k s)))
    (Fin.last 2) = concretize s
  exact Fin.lastCases_last

/-- **Cone data in degree `1` from a family of paths whose first face is constant.** -/
theorem e0ConeDataBdd_one {X : Type} [TopologicalSpace X]
    (hpath : PathConnectedSpace X)
    (hπ : ∀ y : X, Subsingleton (HomotopyGroup (Fin 1) X y))
    (H0 : Simp X 0 → Simp X 1)
    (hlast0 : ∀ (i : Fin 2) (s : Simp X 0), i.val = 1 → simFace X 0 i (H0 s) = s)
    (hconst0 : ∀ (a b : Fin 2) (s t : Simp X 0), a.val = 0 → b.val = 0 →
      simFace X 0 a (H0 s) = simFace X 0 b (H0 t))
    (hx : ∀ (s : Simp X 1) (i j : Fin 3) (hij : i < j),
      (coneFaceFamily H0 s j).comp (coface 0 ⟨i.val, fin3_lt2 i j hij⟩) =
        (coneFaceFamily H0 s i).comp (coface 0 ⟨j.val - 1, fin3_pred_lt2 j⟩)) :
    Nonempty (SSetConeData (singSSet X) 1) := by
  have hcube : ∀ f : C(↥(Cube.boundary (Fin 2)), X),
      ∃ g : C(Fin 2 → unitInterval, X), ∀ z : ↥(Cube.boundary (Fin 2)), g z.1 = f z :=
    fun f => e0CubeBoundaryExtension (m := 2) (by norm_num) hpath (by simpa using hπ) f
  choose y hy using fun s : Simp X 1 => exists_simplexFiller 0 hcube (coneFaceFamily H0 s) (hx s)
  let H1 : Simp X 1 → Simp X 2 := fun s => simplexOf 2 (y s)
  have hH1c : ∀ s : Simp X 1, concretize (H1 s) = y s :=
    fun s => concretize_simplexOf (n := 2) (y s)
  let H' : ∀ n : ℕ, Simp X n → Simp X (n+1) :=
    patchH (patchH (junkH (singSSet X)) 0 H0) 1 H1
  have hH'1 : ∀ s : Simp X 1, H' 1 s = H1 s := fun s => patchH_self _ 1 H1 s
  have hH'0 : ∀ s : Simp X 0, H' 0 s = H0 s := fun s =>
    (patchH_of_ne (patchH (junkH (singSSet X)) 0 H0) 1 H1
      (by decide : (0 : ℕ) ≠ 1) s).trans (patchH_self _ 0 H0 s)
  refine ⟨{ H := H', face_cast := ?_, face_last := ?_ }⟩
  · intro m hm s i
    obtain rfl : m = 0 := by omega
    rw [hH'1, hH'0]
    apply concretize_injective
    rw [concretize_face (H1 s) (Fin.castSucc i), hH1c s, hy s (Fin.castSucc i),
      coneFaceFamily_castSucc]
  · intro m hm s
    interval_cases m
    · rw [hH'0]
      exact hlast0 (Fin.last 1) s (by rw [Fin.val_last])
    · rw [hH'1]
      apply concretize_injective
      rw [concretize_face (H1 s) (Fin.last 2), hH1c s, hy s (Fin.last 2)]
      rw [coneFaceFamily_last]

/-! ## The inductive step -/

/-- The prescribed faces of the degree-`(k+2)` filler attached to `s`. -/
def stepFaceFamily {X : Type} [TopologicalSpace X] (k : ℕ)
    (D : SSetConeData (singSSet X) (k+1)) (s : Simp X (k+2)) :
    Fin (k+4) → C(↥(stdSimplex ℝ (Fin (k+3))), X) :=
  Fin.lastCases (concretize s)
    (fun i : Fin (k+3) => concretize (D.H (k+1) (simFace X (k+1) i s)))

@[simp]
theorem stepFaceFamily_castSucc {X : Type} [TopologicalSpace X] (k : ℕ)
    (D : SSetConeData (singSSet X) (k+1)) (s : Simp X (k+2)) (i : Fin (k+3)) :
    stepFaceFamily k D s (Fin.castSucc i) = concretize (D.H (k+1) (simFace X (k+1) i s)) := by
  change Fin.lastCases (concretize s)
    (fun i : Fin (k+3) => concretize (D.H (k+1) (simFace X (k+1) i s)))
    (Fin.castSucc i) = concretize (D.H (k+1) (simFace X (k+1) i s))
  exact Fin.lastCases_castSucc i

@[simp]
theorem stepFaceFamily_last {X : Type} [TopologicalSpace X] (k : ℕ)
    (D : SSetConeData (singSSet X) (k+1)) (s : Simp X (k+2)) :
    stepFaceFamily k D s (Fin.last (k+3)) = concretize s := by
  change Fin.lastCases (concretize s)
    (fun i : Fin (k+3) => concretize (D.H (k+1) (simFace X (k+1) i s)))
    (Fin.last (k+3)) = concretize s
  exact Fin.lastCases_last

/-- **The inductive step of the cone construction.** -/
theorem e0ConeDataStep {X : Type} [TopologicalSpace X] (k : ℕ)
    (hpath : PathConnectedSpace X)
    (hπ : ∀ y : X, Subsingleton (HomotopyGroup (Fin (k+2)) X y))
    (D : SSetConeData (singSSet X) (k+1))
    (hx : ∀ (s : Simp X (k+2)) (i j : Fin (k+4)) (hij : i < j),
      (stepFaceFamily k D s j).comp (coface (k+1) ⟨i.val, fin_lt_of_lt i j hij⟩) =
        (stepFaceFamily k D s i).comp (coface (k+1) ⟨j.val - 1, fin_pred_lt j⟩)) :
    Nonempty (SSetConeData (singSSet X) (k+2)) := by
  have hcube : ∀ f : C(↥(Cube.boundary (Fin (k+3))), X),
      ∃ g : C(Fin (k+3) → unitInterval, X),
        ∀ z : ↥(Cube.boundary (Fin (k+3))), g z.1 = f z :=
    fun f => e0CubeBoundaryExtension (m := k+3) (by omega) hpath (by simpa using hπ) f
  choose y hy using fun s : Simp X (k+2) =>
    exists_simplexFiller (k+1) hcube (stepFaceFamily k D s) (hx s)
  let Hnew : Simp X (k+2) → Simp X (k+3) := fun s => simplexOf (k+3) (y s)
  have hHnewc : ∀ s : Simp X (k+2), concretize (Hnew s) = y s :=
    fun s => concretize_simplexOf (n := k+3) (y s)
  let H' : ∀ n : ℕ, Simp X n → Simp X (n+1) := patchH D.H (k+2) Hnew
  have hH'self : ∀ s : Simp X (k+2), H' (k+2) s = Hnew s :=
    fun s => patchH_self D.H (k+2) Hnew s
  have hH'ne : ∀ {n : ℕ}, n ≠ k+2 → ∀ s : Simp X n, H' n s = D.H n s :=
    fun hn s => patchH_of_ne D.H (k+2) Hnew hn s
  refine ⟨{ H := H', face_cast := ?_, face_last := ?_ }⟩
  · intro m hm s i
    by_cases hc : m + 1 ≤ k + 1
    · rw [hH'ne (by omega : m + 1 ≠ k + 2) s,
        hH'ne (by omega : m ≠ k + 2) (simFace X m i s)]
      exact D.face_cast m hc s i
    · have hmk : m = k + 1 := by omega
      subst hmk
      rw [hH'self, hH'ne (by omega : k + 1 ≠ k + 2)]
      apply concretize_injective
      rw [concretize_face (Hnew s) (Fin.castSucc i), hHnewc s, hy s (Fin.castSucc i),
        stepFaceFamily_castSucc]
  · intro m hm s
    by_cases hc : m ≤ k + 1
    · rw [hH'ne (by omega : m ≠ k + 2) s]
      exact D.face_last m hc s
    · have hmk : m = k + 2 := by omega
      subst hmk
      rw [hH'self]
      apply concretize_injective
      rw [concretize_face (Hnew s) (Fin.last (k+3)), hHnewc s, hy s (Fin.last (k+3))]
      rw [stepFaceFamily_last]

end

end Work.Serre
