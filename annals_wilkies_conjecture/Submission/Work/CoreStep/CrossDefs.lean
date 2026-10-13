/-
  Area `CoreStep`: the vocabulary of the **cross-piece** level dichotomy
  (`Work.CoreStep.persist_of_Zavoid_cross2`).

  The level-pair set `absLevelPairSet T T'` lives in the pair space `ℝ^{0 + pPair n m}` and its
  points are pairs `(u, v)` of points of `absSet T`, `absSet T'` over a common base and with a
  common *last* (vertical) coordinate.  This file fixes the maps that the dichotomy argument
  needs:

  * `pairBaseCLM n m` — the base projection `ℝ^{0+pPair n m} → ℝⁿ` sending a pair to the base of
    its first block (a continuous linear map);
  * `pairingCLM n m` — the pairing `(u,v) ↦ pairPtUp (absPtUp u) (absPtUp v)` of two
    `ℝ^{n+(m+1)}`-blocks, as a continuous linear map;
  * `graphMap φ φ'` — the "graph map" `x ↦ (Fin.append x (φ x), Fin.append x (φ' x))`: the pair
    of the two branch points over the base `x`;
  * `levDiff φ φ' x` — the difference of the last coordinates of the two branches over `x`.

  These are the objects in which the two geometric inputs of the proof are stated:
  `exists_analytic_branch_graph` (a `Good` stratum of full fibre codimension is, near each of its
  points, the graph of a function of the base), `exists_levelSet_chart` (a `Good` stratum has a
  chart of its level set through any of its points), and the two bookkeeping lemmas
  `exists_graphMap_of_mem_absLevelPairSet` / `fderiv_graphMap_comp`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE7.levelAgree_semiPf
import Submission.Work.CoreStep.persist_aux_pairPtUp_mem

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep

/-! ## §1. The base projection and the pairing of two blocks -/

/-- The base of the **first block** of a point of the pair space `ℝ^{0 + pPair n m}`.

`pPair n m = (n + (m+1)) + (n + (m+1))`, so a point of the pair space is a concatenation of two
`(n + (m+1))`-blocks; this map keeps the first `n` coordinates of the first block. -/
def pairBaseCLM (n m : ℕ) : (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add (pPair n m)).symm
      (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i))) :
        (Fin (0 + pPair n m) → ℝ) →L[ℝ] ℝ)

@[simp] theorem pairBaseCLM_apply (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) (i : Fin n) :
    pairBaseCLM n m w i = w (Fin.cast (Nat.zero_add (pPair n m)).symm
      (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i))) := rfl

/-- The pairing of two `(n + (m+1))`-blocks into the pair space `ℝ^{0 + pPair n m}`.

This is `(u, v) ↦ pairPtUp (absPtUp u) (absPtUp v)`, exhibited as a continuous linear map. -/
def pairingCLM (n m : ℕ) :
    ((Fin (n + (m + 1)) → ℝ) × (Fin (n + (m + 1)) → ℝ)) →L[ℝ]
      (Fin (0 + pPair n m) → ℝ) :=
  (ContinuousLinearMap.pi fun j : Fin (0 + pPair n m) =>
      (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add (pPair n m)) j) :
        (Fin (pPair n m) → ℝ) →L[ℝ] ℝ)).comp
    (Work.WilE9.Ift.appendCLM (n + (m + 1)) (n + (m + 1)))

theorem pairPtUp_absPtUp (n m : ℕ) (u v : Fin (n + (m + 1)) → ℝ) :
    pairPtUp (absPtUp (n := n) (m := m) u) (absPtUp v)
      = fun j => (Fin.append u v) (Fin.cast (Nat.zero_add (pPair n m)) j) := by
  funext j
  simp only [pairPtUp, pairPt, absPtInv_absPtUp]

@[simp] theorem pairingCLM_apply (n m : ℕ) (u v : Fin (n + (m + 1)) → ℝ) :
    pairingCLM n m (u, v) = pairPtUp (absPtUp u) (absPtUp v) := by
  rw [pairPtUp_absPtUp]
  ext j
  simp [pairingCLM]

/-- The base of the pairing of two blocks is the base of either block. -/
theorem pairBaseCLM_pairingCLM (n m : ℕ) (u v : Fin (n + (m + 1)) → ℝ) :
    pairBaseCLM n m (pairingCLM n m (u, v)) = projFirst n (m + 1) u := by
  rw [pairingCLM_apply, pairPtUp_absPtUp]
  ext i
  simp only [pairBaseCLM_apply, projFirst]
  rw [show Fin.cast (Nat.zero_add (pPair n m))
        (Fin.cast (Nat.zero_add (pPair n m)).symm
          (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i)))
      = Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i) from by ext; simp]
  exact Fin.append_left u v (Fin.castAdd (m + 1) i)

/-! ## §2. The graph map and the level difference -/

/-- The **graph map** of two branches: the pair of the two points over the base `x` whose
vertical blocks are given by `φ` and `φ'`. -/
def graphMap (n m : ℕ) (φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ)) :
    (Fin n → ℝ) → (Fin (0 + pPair n m) → ℝ) :=
  fun x => pairingCLM n m (Fin.append x (φ x), Fin.append x (φ' x))

@[simp] theorem graphMap_apply (n m : ℕ) (φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (x : Fin n → ℝ) :
    graphMap n m φ φ' x
      = pairPtUp (absPtUp (n := n) (m := m) (Fin.append x (φ x)))
          (absPtUp (Fin.append x (φ' x))) := by
  simp [graphMap]

/-- The base of a graph point is the base `x`. -/
@[simp] theorem pairBaseCLM_graphMap (n m : ℕ) (φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (x : Fin n → ℝ) : pairBaseCLM n m (graphMap n m φ φ' x) = x := by
  rw [graphMap, pairBaseCLM_pairingCLM]
  exact funext fun i => Fin.append_left _ _ i

/-- The **level difference** of two branches. -/
def levDiff (n m : ℕ) (φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ)) (x : Fin n → ℝ) : ℝ :=
  (φ x) (Fin.last m) - (φ' x) (Fin.last m)

/-- The graph map is differentiable wherever the two branches are. -/
theorem differentiableAt_graphMap (n m : ℕ) {φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ)}
    {x₀ : Fin n → ℝ} (hφ : DifferentiableAt ℝ φ x₀) (hφ' : DifferentiableAt ℝ φ' x₀) :
    DifferentiableAt ℝ (graphMap n m φ φ') x₀ := by
  have h1 : DifferentiableAt ℝ (fun x : Fin n → ℝ => Fin.append x (φ x)) x₀ := by
    simpa only [ContinuousLinearMap.coe_coe, Function.comp_def, Function.comp_apply, id_eq,
      Work.WilE9.Ift.appendCLM_apply] using
      ((Work.WilE9.Ift.appendCLM n (m + 1)).differentiableAt.comp x₀
        (differentiableAt_id.prodMk hφ))
  have h2 : DifferentiableAt ℝ (fun x : Fin n → ℝ => Fin.append x (φ' x)) x₀ := by
    simpa only [ContinuousLinearMap.coe_coe, Function.comp_def, Function.comp_apply, id_eq,
      Work.WilE9.Ift.appendCLM_apply] using
      ((Work.WilE9.Ift.appendCLM n (m + 1)).differentiableAt.comp x₀
        (differentiableAt_id.prodMk hφ'))
  exact (pairingCLM n m).differentiableAt.comp x₀ (h1.prodMk h2)

/-- The derivative of the graph map, in the form used by the chain rule. -/
theorem hasFDerivAt_graphMap (n m : ℕ) {φ φ' : (Fin n → ℝ) → (Fin (m + 1) → ℝ)}
    {x₀ : Fin n → ℝ} (hφ : DifferentiableAt ℝ φ x₀) (hφ' : DifferentiableAt ℝ φ' x₀) :
    HasFDerivAt (graphMap n m φ φ') (fderiv ℝ (graphMap n m φ φ') x₀) x₀ :=
  (differentiableAt_graphMap n m hφ hφ').hasFDerivAt

/-- Membership in `absSet T` in terms of `absPtInv`. -/
theorem mem_absSet_iff {N : ℕ} (T : WilkiesDesign.E.Stratum 0 N) (w : Fin N → ℝ) :
    w ∈ Work.WilE7.MainDesign.absSet T ↔ Work.WilE7.DimAPI.absPtInv N w ∈ T.X.set := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [Work.WilE7.DimAPI.absPtInv_absPt]
  · intro hw
    exact ⟨Work.WilE7.DimAPI.absPtInv N w, hw,
      Work.WilE7.DimAPI.absPt_absPtInv N w⟩

/-- The sheet point of a stratum, as a point of `absSet`. -/
theorem absPt_absPtUp_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    Work.WilE7.MainDesign.absPt
      (absPtUp (n := n) (m := m) (Fin.append x y)) = Fin.append x y := by
  have h : absPtUp (n := n) (m := m) (Fin.append x y)
      = Work.WilE7.DimAPI.absPtInv (n + (m + 1)) (Fin.append x y) := rfl
  rw [h, Work.WilE7.DimAPI.absPt_absPtInv]

/-! ## §3. The two blocks of a point of the pair space -/

/-- `absPtInv N` as a continuous linear map. -/
def absPtInvCLM (N : ℕ) : (Fin N → ℝ) →L[ℝ] (Fin (0 + N) → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin (0 + N) =>
    (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add N) i) : (Fin N → ℝ) →L[ℝ] ℝ)

@[simp] theorem absPtInvCLM_apply (N : ℕ) (w : Fin N → ℝ) :
    absPtInvCLM N w = Work.WilE7.DimAPI.absPtInv N w := rfl

/-- The first of the two `N`-blocks of `ℝ^{N+N}`. -/
def projFirstCLM (N : ℕ) : (Fin (N + N) → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin N =>
    (ContinuousLinearMap.proj (Fin.castAdd N i) : (Fin (N + N) → ℝ) →L[ℝ] ℝ)

/-- The second of the two `N`-blocks of `ℝ^{N+N}`. -/
def projSndCLM (N : ℕ) : (Fin (N + N) → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin N =>
    (ContinuousLinearMap.proj (Fin.natAdd N i) : (Fin (N + N) → ℝ) →L[ℝ] ℝ)

@[simp] theorem projFirstCLM_apply (N : ℕ) (w : Fin (N + N) → ℝ) :
    projFirstCLM N w = projFirst N N w := rfl

@[simp] theorem projSndCLM_apply (N : ℕ) (w : Fin (N + N) → ℝ) :
    projSndCLM N w = projSnd N N w := rfl

/-- The first block of a point of the pair space, as a point of `ℝ^{0+N}`. -/
def blockFirstCLM (n m : ℕ) :
    (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
  (absPtInvCLM (n + (m + 1))).comp
    ((projFirstCLM (n + (m + 1))).comp (Work.WilE7.DimAPI.absPtCLM (pPair n m)))

/-- The second block of a point of the pair space, as a point of `ℝ^{0+N}`. -/
def blockSndCLM (n m : ℕ) :
    (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
  (absPtInvCLM (n + (m + 1))).comp
    ((projSndCLM (n + (m + 1))).comp (Work.WilE7.DimAPI.absPtCLM (pPair n m)))

theorem blockFirstCLM_apply (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) :
    blockFirstCLM n m w
      = Work.WilE7.DimAPI.absPtInv (n + (m + 1))
          (projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w)) := rfl

theorem blockSndCLM_apply (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) :
    blockSndCLM n m w
      = Work.WilE7.DimAPI.absPtInv (n + (m + 1))
          (projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w)) := rfl

/-- The first block of `w`, read in `ℝ^{n+(m+1)}`. -/
theorem absPt_blockFirstCLM {n m : ℕ} (w : Fin (0 + pPair n m) → ℝ) :
    Work.WilE7.MainDesign.absPt (blockFirstCLM n m w)
      = projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w) := by
  rw [blockFirstCLM_apply, Work.WilE7.DimAPI.absPt_absPtInv]

/-- The second block of `w`, read in `ℝ^{n+(m+1)}`. -/
theorem absPt_blockSndCLM {n m : ℕ} (w : Fin (0 + pPair n m) → ℝ) :
    Work.WilE7.MainDesign.absPt (blockSndCLM n m w)
      = projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w) := by
  rw [blockSndCLM_apply, Work.WilE7.DimAPI.absPt_absPtInv]

/-- The base of the first block is the base of the pair point. -/
theorem projFirst_absPt_blockFirstCLM {n m : ℕ} (w : Fin (0 + pPair n m) → ℝ) :
    projFirst n (m + 1) (Work.WilE7.MainDesign.absPt (blockFirstCLM n m w))
      = pairBaseCLM n m w := by
  ext i
  rw [absPt_blockFirstCLM]
  rfl

theorem append_projFirst_projSnd_pair {N M : ℕ} (z : Fin (N + M) → ℝ) :
    Fin.append (projFirst N M z) (projSnd N M z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left, projFirst]
  · simp [Fin.append_right, projSnd]

/-- Every point of the pair space is the pairing of its two blocks. -/
theorem pairPtUp_block (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) :
    pairPtUp (blockFirstCLM n m w) (blockSndCLM n m w) = w := by
  funext j
  have h1 : Work.WilE7.CoreStep.absPtInv (n := n) (m := m) (blockFirstCLM n m w)
      = projFirst (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w) :=
    absPt_blockFirstCLM w
  have h2 : Work.WilE7.CoreStep.absPtInv (n := n) (m := m) (blockSndCLM n m w)
      = projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt w) :=
    absPt_blockSndCLM w
  show (Fin.append (Work.WilE7.CoreStep.absPtInv (blockFirstCLM n m w))
      (Work.WilE7.CoreStep.absPtInv (blockSndCLM n m w)))
      (Fin.cast (Nat.zero_add (pPair n m)) j) = w j
  rw [h1, h2, append_projFirst_projSnd_pair (N := n + (m + 1)) (M := n + (m + 1))]
  exact congrFun (Work.WilE7.DimAPI.absPtInv_absPt (pPair n m) w) j

/-! ## §4. Micro-lemmas about the pair structure -/

theorem fin_cast_symm_cast {N : ℕ} (i : Fin N) :
    Fin.cast (Nat.zero_add N) (Fin.cast (Nat.zero_add N).symm i) = i := by
  ext
  simp

theorem fin_cast_symm_cast' {N : ℕ} (i : Fin (0 + N)) :
    Fin.cast (Nat.zero_add N).symm (Fin.cast (Nat.zero_add N) i) = i := by
  ext
  simp

/-- `absPt` of a pair point is the concatenation of the two blocks. -/
theorem Cross_absPt_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    Work.WilE7.MainDesign.absPt (pairPtUp u v)
      = Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v) := by
  funext i
  show pairPtUp u v (Fin.cast (Nat.zero_add (pPair n m)).symm i)
    = Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v) i
  show pairPt u v (Fin.cast (Nat.zero_add (pPair n m))
      (Fin.cast (Nat.zero_add (pPair n m)).symm i)) = _
  rw [fin_cast_symm_cast]
  rfl

/-- The first block of a pair point. -/
theorem blockFirst_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    blockFirstCLM n m (pairPtUp u v) = u := by
  rw [blockFirstCLM_apply, Cross_absPt_pairPtUp]
  rw [show projFirst (n + (m + 1)) (n + (m + 1))
        (Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v))
      = Work.WilE7.MainDesign.absPt u from funext fun i => Fin.append_left _ _ i]
  exact Work.WilE7.DimAPI.absPtInv_absPt _ _

/-- The second block of a pair point. -/
theorem blockSnd_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    blockSndCLM n m (pairPtUp u v) = v := by
  rw [blockSndCLM_apply, Cross_absPt_pairPtUp]
  rw [show projSnd (n + (m + 1)) (n + (m + 1))
        (Fin.append (Work.WilE7.MainDesign.absPt u) (Work.WilE7.MainDesign.absPt v))
      = Work.WilE7.MainDesign.absPt v from funext fun i => Fin.append_right _ _ i]
  exact Work.WilE7.DimAPI.absPtInv_absPt _ _

/-- The pairing of the `absPt`-versions of two points is the pair point. -/
theorem pairingCLM_absPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    pairingCLM n m (Work.WilE7.MainDesign.absPt u, Work.WilE7.MainDesign.absPt v)
      = pairPtUp u v := by
  rw [pairingCLM_apply]
  rw [absPtUp_absPtInv, absPtUp_absPtInv]

/-- The last (vertical) coordinate of a point of the ambient space `ℝ^{0+(n+(m+1))}`. -/
def levelOf (n m : ℕ) (z : Fin (0 + (n + (m + 1))) → ℝ) : ℝ :=
  (WilkiesDesign.E.projSnd n (m + 1) (Work.WilE7.MainDesign.absPt z)) ⟨m, by omega⟩

theorem absPtUp_eq_absPtInv {n m : ℕ} (w : Fin (n + (m + 1)) → ℝ) :
    absPtUp (n := n) (m := m) w = Work.WilE7.DimAPI.absPtInv (n + (m + 1)) w := rfl

theorem levelOf_absPtUp_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    levelOf n m (absPtUp (n := n) (m := m) (Fin.append x y)) = y (Fin.last m) := by
  show (WilkiesDesign.E.projSnd n (m + 1)
    (Work.WilE7.MainDesign.absPt (absPtUp (n := n) (m := m) (Fin.append x y)))) ⟨m, by omega⟩
    = y (Fin.last m)
  rw [absPtUp_eq_absPtInv, Work.WilE7.DimAPI.absPt_absPtInv]
  simp only [WilkiesDesign.E.projSnd, Fin.append_right]
  congr 1

theorem projFirst_absPtInv_absPtUp_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    WilkiesDesign.E.projFirst n (m + 1)
      (Work.WilE7.CoreStep.absPtInv (n := n) (m := m)
        (absPtUp (n := n) (m := m) (Fin.append x y))) = x := by
  simp only [Work.WilE7.CoreStep.absPtInv, absPtUp_eq_absPtInv,
    Work.WilE7.DimAPI.absPt_absPtInv]
  funext i
  simp [WilkiesDesign.E.projFirst, Fin.append_left]

theorem projSnd_absPtInv_absPtUp_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    (WilkiesDesign.E.projSnd n (m + 1)
      (Work.WilE7.CoreStep.absPtInv (n := n) (m := m)
        (absPtUp (n := n) (m := m) (Fin.append x y)))) ⟨m, by omega⟩ = y (Fin.last m) := by
  simp only [Work.WilE7.CoreStep.absPtInv, absPtUp_eq_absPtInv,
    Work.WilE7.DimAPI.absPt_absPtInv]
  simp only [WilkiesDesign.E.projSnd, Fin.append_right]
  congr 1

theorem mem_absLevelPairSet_sheets {n m k k' : ℕ} (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (j : Fin k) (j' : Fin k')
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (s' : Fin k' → (Fin n → ℝ) → (Fin (m + 1) → ℝ)) (x₀ : Fin n → ℝ)
    (hpz : absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)) ∈ T.X.set)
    (hqz : absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)) ∈ T'.X.set)
    (hlev : (s j x₀) (Fin.last m) = (s' j' x₀) (Fin.last m)) :
    pairPtUp (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
      (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
      ∈ (absLevelPairSet T T').set :=
  mem_absLevelPairSet T T' _ _ hpz hqz
    (by rw [projFirst_absPtInv_absPtUp_append, projFirst_absPtInv_absPtUp_append])
    (by rw [projSnd_absPtInv_absPtUp_append, projSnd_absPtInv_absPtUp_append]; exact hlev)

/-- A map that has an analytic left inverse near a point has injective derivative there. -/
theorem injective_fderiv_of_eventually_leftInverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : E → F) (χ : F → E) (hγ : AnalyticAt ℝ γ 0) (hχ : AnalyticAt ℝ χ (γ 0))
    (h : (fun y => χ (γ y)) =ᶠ[nhds (0 : E)] fun y => y) :
    Function.Injective (fderiv ℝ γ 0) := by
  have hχ' : HasFDerivAt (fun y => χ (γ y)) ((fderiv ℝ χ (γ 0)).comp (fderiv ℝ γ 0)) 0 :=
    HasFDerivAt.comp 0 (g := χ) (g' := fderiv ℝ χ (γ 0)) (f := γ)
      (hχ.hasStrictFDerivAt.hasFDerivAt) (hγ.hasStrictFDerivAt.hasFDerivAt)
  have hcomp : (fderiv ℝ χ (γ 0)).comp (fderiv ℝ γ 0)
      = ContinuousLinearMap.id ℝ E := by
    rw [← hχ'.fderiv, EventuallyEq.fderiv_eq h, show (fun y : E => y) = id from rfl, fderiv_id]
  intro a b hab
  have h5 : (fderiv ℝ γ 0) (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h6 : (ContinuousLinearMap.id ℝ E) (a - b) = 0 := by
    rw [← hcomp, ContinuousLinearMap.comp_apply, h5, map_zero]
  exact sub_eq_zero.mp (by simpa using h6)

end Work.CoreStep
