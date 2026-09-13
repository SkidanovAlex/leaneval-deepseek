import Submission.Grassmann.SpectralSSE

/-!
# The BKS homomorphism `φ : V_ℓ(B₀) → Mat_{ℓ,k−ℓ}` (arXiv:1804.08662 §3)

The last missing step of route (B) is the Barak–Kothari–Steurer reduction: the Inverse Shortcode
Hypothesis (which is `SpectralSSE.HypSSE` contraposed) implies the Grassmann Expansion
Hypothesis (which is `Transfer.ExpStmt`).

BKS relate the two graphs by fixing a basis `B` of `𝔽₂^k` — here the standard basis — and mapping
a subspace `V ∈ V_ℓ(B₀)` (those `ℓ`-subspaces whose projection to the first `ℓ` coordinates is
full) to the `ℓ × (k−ℓ)` matrix whose `i`-th row is the projection of the `i`-th *canonical basis
vector* `v_i` of `V` (the unique `v ∈ V` with `first(v) = e_i`) to the last `k−ℓ` coordinates.

**Index convention.**  To avoid `Fin.cast`-proof-term gymnastics the two halves of the index type
`Fin k` are represented by *subtypes*:
`{i : Fin k // (i : ℕ) < ℓ}` (the "first `ℓ` coordinates") and
`{j : Fin k // ℓ ≤ (j : ℕ)}` (the "last `k - ℓ` coordinates").
They are canonically equivalent to `Fin ℓ` and `Fin (k - ℓ)` (`subLtEquiv`, `subGeEquiv`), and
matrices are transported along these equivalences when the shortcode SSE (`HypSSE`) is applied.
-/

open Finset BigOperators Matrix
open Classical
open PseudorandomGrassmann

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The coordinate projections -/

/-- Projection of `v : 𝔽₂^k` to the coordinates with index `< ℓ`. -/
def projFirst (ℓ k : ℕ) :
    (Fin k → 𝔽₂) →ₗ[𝔽₂] ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) :=
  LinearMap.pi fun i => LinearMap.proj i.1

@[simp] lemma projFirst_apply (ℓ k : ℕ) (v : Fin k → 𝔽₂) (i : {i : Fin k // (i : ℕ) < ℓ}) :
    projFirst ℓ k v i = v i.1 := rfl

@[simp] lemma projFirst_zero (ℓ k : ℕ) : projFirst ℓ k (0 : Fin k → 𝔽₂) = 0 := map_zero _

/-- Projection of `v : 𝔽₂^k` to the coordinates with index `≥ ℓ`. -/
def projLast (ℓ k : ℕ) :
    (Fin k → 𝔽₂) →ₗ[𝔽₂] ({j : Fin k // ℓ ≤ (j : ℕ)} → 𝔽₂) :=
  LinearMap.pi fun j => LinearMap.proj j.1

@[simp] lemma projLast_apply (ℓ k : ℕ) (v : Fin k → 𝔽₂) (j : {j : Fin k // ℓ ≤ (j : ℕ)}) :
    projLast ℓ k v j = v j.1 := rfl

/-- The two coordinate projections determine the vector. -/
lemma eq_of_proj_eq {ℓ k : ℕ} {v w : Fin k → 𝔽₂}
    (h1 : projFirst ℓ k v = projFirst ℓ k w) (h2 : projLast ℓ k v = projLast ℓ k w) : v = w := by
  funext i
  by_cases hi : (i : ℕ) < ℓ
  · have := congrFun h1 (⟨i, hi⟩ : {i : Fin k // (i : ℕ) < ℓ})
    simpa using this
  · have hge : ℓ ≤ (i : ℕ) := by omega
    have := congrFun h2 (⟨i, hge⟩ : {j : Fin k // ℓ ≤ (j : ℕ)})
    simpa using this

lemma projFirst_eq_zero_iff (ℓ k : ℕ) (v : Fin k → 𝔽₂) :
    projFirst ℓ k v = 0 ↔ ∀ i : {i : Fin k // (i : ℕ) < ℓ}, v i.1 = 0 := by
  constructor
  · intro hv i
    have := congrFun hv i
    simpa using this
  · intro hv
    funext i
    simpa using hv i

/-- The "last coordinates" of a difference that vanishes on the last coordinates. -/
lemma projLast_sub_eq_zero {ℓ k : ℕ} {v w : Fin k → 𝔽₂}
    (h : projLast ℓ k v = projLast ℓ k w) : projLast ℓ k (v - w) = 0 := by
  rw [map_sub, h, sub_self]

/-! ## The index equivalences -/

/-- `{i : Fin k // i < ℓ} ≃ Fin ℓ` for `ℓ ≤ k`. -/
def subLtEquiv {ℓ k : ℕ} (h : ℓ ≤ k) : {i : Fin k // (i : ℕ) < ℓ} ≃ Fin ℓ where
  toFun i := ⟨i.1.1, i.2⟩
  invFun j := ⟨⟨j.1, lt_of_lt_of_le j.2 h⟩, j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

/-- `{j : Fin k // ℓ ≤ j} ≃ Fin (k - ℓ)` for `ℓ ≤ k`. -/
def subGeEquiv {ℓ k : ℕ} (h : ℓ ≤ k) : {j : Fin k // ℓ ≤ (j : ℕ)} ≃ Fin (k - ℓ) where
  toFun j := ⟨(j.1.1 - ℓ), by have := j.1.2; omega⟩
  invFun j := ⟨⟨ℓ + j.1, by have := j.2; omega⟩, by simp⟩
  left_inv j := by
    ext
    simp
    have := j.1.2
    omega
  right_inv j := by
    ext
    simp

lemma card_subLt {ℓ k : ℕ} (h : ℓ ≤ k) : Fintype.card {i : Fin k // (i : ℕ) < ℓ} = ℓ := by
  rw [Fintype.card_congr (subLtEquiv h), Fintype.card_fin]

lemma card_subGe {ℓ k : ℕ} (h : ℓ ≤ k) : Fintype.card {j : Fin k // ℓ ≤ (j : ℕ)} = k - ℓ := by
  rw [Fintype.card_congr (subGeEquiv h), Fintype.card_fin]

/-! ## The good vertices, the canonical basis and `φ` -/

/-- The `ℓ`-subspaces of `𝔽₂^k` whose projection to the first `ℓ` coordinates is full. -/
structure VGood (k ℓ : ℕ) where
  carrier : Submodule 𝔽₂ (Fin k → 𝔽₂)
  finrank_eq : Module.finrank 𝔽₂ carrier = ℓ
  map_eq_top : Submodule.map (projFirst ℓ k) carrier = ⊤

/-- The vertex of the Grassmann graph underlying a good subspace. -/
def VGood.toVertex {k ℓ : ℕ} (L : VGood k ℓ) : GrVertex k ℓ := ⟨L.carrier, L.finrank_eq⟩

/-- The `i`-th canonical basis vector of `V ∈ V_ℓ(B₀)`: some `v ∈ V` with `first(v) = e_i`. -/
noncomputable def canonVec {k ℓ : ℕ} (L : VGood k ℓ)
    (i : {i : Fin k // (i : ℕ) < ℓ}) : Fin k → 𝔽₂ :=
  Classical.choose (Submodule.mem_map.mp
    (show (Pi.single i 1 : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂)
        ∈ Submodule.map (projFirst ℓ k) L.carrier by
      rw [L.map_eq_top]; exact Submodule.mem_top))

lemma canonVec_spec {k ℓ : ℕ} (L : VGood k ℓ) (i : {i : Fin k // (i : ℕ) < ℓ}) :
    canonVec L i ∈ L.carrier ∧ projFirst ℓ k (canonVec L i) = Pi.single i 1 :=
  Classical.choose_spec (Submodule.mem_map.mp
    (show (Pi.single i 1 : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂)
        ∈ Submodule.map (projFirst ℓ k) L.carrier by
      rw [L.map_eq_top]; exact Submodule.mem_top))

lemma canonVec_mem {k ℓ : ℕ} (L : VGood k ℓ) (i : {i : Fin k // (i : ℕ) < ℓ}) :
    canonVec L i ∈ L.carrier := (canonVec_spec L i).1

lemma projFirst_canonVec {k ℓ : ℕ} (L : VGood k ℓ) (i : {i : Fin k // (i : ℕ) < ℓ}) :
    projFirst ℓ k (canonVec L i) = Pi.single i 1 := (canonVec_spec L i).2

/-- The projection to the first `ℓ` coordinates is injective on `V ∈ V_ℓ(B₀)`. -/
lemma projFirst_injOn {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ) :
    ∀ v w : Fin k → 𝔽₂, v ∈ L.carrier → w ∈ L.carrier → projFirst ℓ k v = projFirst ℓ k w → v = w := by
  intro v w hv hw hvw
  have hker : LinearMap.ker ((projFirst ℓ k).comp L.carrier.subtype) = ⊥ := by
    have hrange : LinearMap.range ((projFirst ℓ k).comp L.carrier.subtype)
        = Submodule.map (projFirst ℓ k) L.carrier := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hfr : Module.finrank 𝔽₂ (LinearMap.range ((projFirst ℓ k).comp L.carrier.subtype)) = ℓ := by
      rw [hrange, L.map_eq_top]
      rw [Submodule.topEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, card_subLt h]
    have hrn := LinearMap.finrank_range_add_finrank_ker ((projFirst ℓ k).comp L.carrier.subtype)
    have hL : Module.finrank 𝔽₂ ↥L.carrier = ℓ := L.finrank_eq
    rw [hfr, hL] at hrn
    have : Module.finrank 𝔽₂ ↥(LinearMap.ker ((projFirst ℓ k).comp L.carrier.subtype)) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp this
  have h0 : (⟨v, hv⟩ : ↥L.carrier) - ⟨w, hw⟩ ∈ LinearMap.ker ((projFirst ℓ k).comp L.carrier.subtype) := by
    rw [LinearMap.mem_ker, map_sub]
    show (projFirst ℓ k) v - (projFirst ℓ k) w = 0
    rw [hvw, sub_self]
  rw [hker] at h0
  have h1 : (⟨v, hv⟩ : ↥L.carrier) = ⟨w, hw⟩ :=
    sub_eq_zero.mp (show (⟨v, hv⟩ : ↥L.carrier) - ⟨w, hw⟩ = 0 from h0)
  exact congrArg Subtype.val h1

/-- **The canonical basis is characterised by its projection.** -/
lemma canonVec_unique {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ)
    {i : {i : Fin k // (i : ℕ) < ℓ}} {v : Fin k → 𝔽₂}
    (hv : v ∈ L.carrier) (hv' : projFirst ℓ k v = Pi.single i 1) : v = canonVec L i :=
  projFirst_injOn h L v (canonVec L i) hv (canonVec_mem L i) (by rw [hv', projFirst_canonVec])

/-- The canonical basis vectors span `V`. -/
lemma mem_span_canonVec {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ) {v : Fin k → 𝔽₂}
    (hv : v ∈ L.carrier) : v ∈ Submodule.span 𝔽₂ (Set.range (canonVec L)) := by
  have hspan : (⊤ : Submodule 𝔽₂ ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂))
      = Submodule.span 𝔽₂ (Set.range (fun i => Pi.single i (1 : 𝔽₂))) := by
    refine le_antisymm ?_ le_top
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun 𝔽₂]
    exact ⟨x, by ext i; simp [Pi.single_apply]⟩
  have hmem : projFirst ℓ k v ∈ Submodule.span 𝔽₂
      (Set.range (fun i => Pi.single i (1 : 𝔽₂))) := by
    rw [← hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔽₂).mp hmem
  have hsum : (∑ i, c i • canonVec L i) ∈ L.carrier :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (canonVec_mem L i)
  have hproj : projFirst ℓ k (∑ i, c i • canonVec L i) = projFirst ℓ k v := by
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
    rw [map_smul, projFirst_canonVec]
  have hEq := projFirst_injOn h L (∑ i, c i • canonVec L i) v hsum hv hproj
  rw [← hEq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **BKS's homomorphism** `φ : V_ℓ(B₀) → Mat_{ℓ,k−ℓ}`. -/
noncomputable def phi {k ℓ : ℕ} (L : VGood k ℓ) :
    Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂ :=
  fun i j => projLast ℓ k (canonVec L i) j

/-- `φ` is injective: the canonical basis is recoverable from `φ`. -/
lemma phi_injective {k ℓ : ℕ} (h : ℓ ≤ k) : Function.Injective (phi (k := k) (ℓ := ℓ)) := by
  intro L L' hLL
  have hcanon : ∀ i : {i : Fin k // (i : ℕ) < ℓ}, canonVec L i = canonVec L' i := by
    intro i
    refine eq_of_proj_eq (ℓ := ℓ) ?_ ?_
    · rw [projFirst_canonVec, projFirst_canonVec]
    · funext j
      have := congrFun (congrFun hLL i) j
      simpa [phi] using this
  have hsub : L.carrier = L'.carrier := by
    refine le_antisymm ?_ ?_
    · intro v hv
      exact (Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        rw [hcanon i]
        exact canonVec_mem L' i)) (mem_span_canonVec h L hv)
    · intro v hv
      exact (Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        rw [← hcanon i]
        exact canonVec_mem L i)) (mem_span_canonVec h L' hv)
  have : L = L' := by
    cases L with
    | mk c f m =>
      cases L' with
      | mk c' f' m' =>
        simpa only [VGood.mk.injEq] using hsub
  exact this

/-! ## Surjectivity of `φ`: the graph of a matrix -/

/-- The vector `(e_i, M_{i·})` of `𝔽₂^k` whose "first half" is `e_i` and whose "last half" is the
`i`-th row of `M`. -/
noncomputable def graphVec {k ℓ : ℕ}
    (M : Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂)
    (i : {i : Fin k // (i : ℕ) < ℓ}) (x : Fin k) : 𝔽₂ :=
  if hx : (x : ℕ) < ℓ then (if (⟨x, hx⟩ : {i : Fin k // (i : ℕ) < ℓ}) = i then 1 else 0)
  else M i ⟨x, by omega⟩

lemma graphVec_of_lt {k ℓ : ℕ} (M : Matrix ({i : Fin k // (i : ℕ) < ℓ})
      ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂)
    (i : {i : Fin k // (i : ℕ) < ℓ}) (x : Fin k) (hx : (x : ℕ) < ℓ) :
    graphVec M i x = (if (⟨x, hx⟩ : {i : Fin k // (i : ℕ) < ℓ}) = i then 1 else 0) :=
  dif_pos hx

lemma graphVec_of_ge {k ℓ : ℕ} (M : Matrix ({i : Fin k // (i : ℕ) < ℓ})
      ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂)
    (i : {i : Fin k // (i : ℕ) < ℓ}) (x : Fin k) (hx : ¬ (x : ℕ) < ℓ) :
    graphVec M i x = M i ⟨x, by omega⟩ :=
  dif_neg hx

lemma projFirst_graphVec {k ℓ : ℕ} (M : Matrix ({i : Fin k // (i : ℕ) < ℓ})
      ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂)
    (i : {i : Fin k // (i : ℕ) < ℓ}) :
    projFirst ℓ k (graphVec M i) = Pi.single i 1 := by
  funext i'
  rw [projFirst_apply, graphVec_of_lt M i i'.1 i'.2, Pi.single_apply]

/-- The rows of the graph of `M` are linearly independent. -/
lemma graphVec_linearIndependent {k ℓ : ℕ} (M : Matrix ({i : Fin k // (i : ℕ) < ℓ})
      ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂) :
    LinearIndependent 𝔽₂ (graphVec M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : (∑ i, g i • (Pi.single i (1 : 𝔽₂) : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂)) = 0 := by
    have h2 := congrArg (projFirst ℓ k) hg
    simpa only [map_sum, map_smul, map_zero, projFirst_graphVec] using h2
  have h3 := (Fintype.linearIndependent_iff.mp
    (Pi.linearIndependent_single_one {i : Fin k // (i : ℕ) < ℓ} 𝔽₂)) g h1
  exact h3

lemma finrank_span_graphVec {k ℓ : ℕ} (h : ℓ ≤ k)
    (M : Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂) :
    Module.finrank 𝔽₂ (Submodule.span 𝔽₂ (Set.range (graphVec M))) = ℓ := by
  rw [finrank_span_eq_card (graphVec_linearIndependent M), card_subLt h]

lemma map_projFirst_span_graphVec {k ℓ : ℕ}
    (M : Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂) :
    Submodule.map (projFirst ℓ k) (Submodule.span 𝔽₂ (Set.range (graphVec M))) = ⊤ := by
  rw [Submodule.map_span]
  have hrange : projFirst ℓ k '' Set.range (graphVec M)
      = Set.range (fun i : {i : Fin k // (i : ℕ) < ℓ} => Pi.single i (1 : 𝔽₂)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (projFirst_graphVec M i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨graphVec M i, ⟨i, rfl⟩, projFirst_graphVec M i⟩
  rw [hrange]
  refine le_antisymm le_top ?_
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun 𝔽₂]
  exact ⟨x, by ext i; simp [Pi.single_apply]⟩

/-- The graph of `M`, as a good subspace. -/
noncomputable def graphGood {k ℓ : ℕ} (h : ℓ ≤ k)
    (M : Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂) :
    VGood k ℓ :=
  ⟨Submodule.span 𝔽₂ (Set.range (graphVec M)),
    finrank_span_graphVec h M, map_projFirst_span_graphVec M⟩

@[simp] lemma graphGood_carrier {k ℓ : ℕ} (h : ℓ ≤ k)
    (M : Matrix ({i : Fin k // (i : ℕ) < ℓ}) ({j : Fin k // ℓ ≤ (j : ℕ)}) 𝔽₂) :
    (graphGood h M).carrier = Submodule.span 𝔽₂ (Set.range (graphVec M)) := rfl

/-- **`φ` is onto**: the graph of `M` is the preimage. -/
theorem phi_surjective {k ℓ : ℕ} (h : ℓ ≤ k) : Function.Surjective (phi (k := k) (ℓ := ℓ)) := by
  intro M
  refine ⟨graphGood h M, ?_⟩
  funext i j
  have hvmem : graphVec M i ∈ (graphGood h M).carrier := by
    rw [graphGood_carrier]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcv : canonVec (graphGood h M) i = graphVec M i :=
    (canonVec_unique h (graphGood h M) hvmem (projFirst_graphVec M i)).symm
  simp only [phi]
  rw [hcv, projLast_apply, graphVec_of_ge M i j.1 (by have := j.2; omega)]


/-! ## `V` is the graph of `phiToLin L` -/

/-- The linear map whose graph is `V = L.carrier`. -/
noncomputable def phiToLin {k ℓ : ℕ} (L : VGood k ℓ) :
    ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) →ₗ[𝔽₂] ({j : Fin k // ℓ ≤ (j : ℕ)} → 𝔽₂) :=
  Matrix.vecMulLinear (phi L)

@[simp] lemma phiToLin_apply {k ℓ : ℕ} (L : VGood k ℓ)
    (y : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) (j : {j : Fin k // ℓ ≤ (j : ℕ)}) :
    phiToLin L y j = ∑ i, y i * phi L i j := by
  rw [phiToLin, Matrix.vecMulLinear_apply, Matrix.vecMul]
  rfl

@[simp] lemma projLast_canonVec {k ℓ : ℕ} (L : VGood k ℓ)
    (i : {i : Fin k // (i : ℕ) < ℓ}) :
    projLast ℓ k (canonVec L i) = phi L i := by
  funext j
  rfl

/-- **`V` is the graph of `phiToLin L`.** -/
lemma mem_iff_phiToLin {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ) (x : Fin k → 𝔽₂) :
    x ∈ L.carrier ↔ projLast ℓ k x = phiToLin L (projFirst ℓ k x) := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔽₂).mp
      (mem_span_canonVec h L hx)
    have hfirst : projFirst ℓ k x = c := by
      rw [← hc, map_sum]
      funext i
      simp only [Finset.sum_apply, map_smul, projFirst_canonVec, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hlast : projLast ℓ k x = phiToLin L c := by
      rw [← hc, map_sum]
      funext j
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, phiToLin_apply,
        projLast_canonVec]
    rw [hfirst, hlast]
  · intro hx
    set c : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂ := projFirst ℓ k x with hc
    have hmem : (∑ i, c i • canonVec L i) ∈ L.carrier :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (canonVec_mem L i)
    have hpe : projFirst ℓ k (∑ i, c i • canonVec L i) = projFirst ℓ k x := by
      rw [map_sum, ← hc]
      funext i
      simp only [Finset.sum_apply, map_smul, projFirst_canonVec, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hpl : projLast ℓ k (∑ i, c i • canonVec L i) = projLast ℓ k x := by
      rw [map_sum]
      simp only [map_smul]
      have h1 : (∑ i, c i • projLast ℓ k (canonVec L i)) = phiToLin L c := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, phiToLin_apply,
          projLast_canonVec]
      rw [h1]
      exact hx.symm
    rw [← eq_of_proj_eq hpe hpl]
    exact hmem


/-- **`φ` is a graph homomorphism**: the intersection dimension of `V, V'` is `ℓ` minus the
(fin)rank of `φ(V) - φ(V')`.  Equivalently, `V ~ V'` in the Grassmann graph iff `φ(V) - φ(V')`
has rank `1` in the shortcode graph. -/
lemma finrank_inf_eq {k ℓ : ℕ} (h : ℓ ≤ k) (L L' : VGood k ℓ) :
    Module.finrank 𝔽₂ ↥(L.carrier ⊓ L'.carrier)
      = ℓ - Module.finrank 𝔽₂ (LinearMap.range (phiToLin L - phiToLin L')) := by
  set f : ↥(L.carrier ⊓ L'.carrier) →ₗ[𝔽₂] ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) :=
    (projFirst ℓ k).comp (L.carrier ⊓ L'.carrier).subtype with hf
  have hsub : ∀ x : ↥(L.carrier ⊓ L'.carrier), f x = projFirst ℓ k (x : Fin k → 𝔽₂) :=
    fun x => rfl
  have hfirst : ∀ y : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂,
      projFirst ℓ k (∑ i, y i • canonVec L i) = y := by
    intro y
    rw [map_sum]
    funext i
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [projFirst_canonVec, Pi.single_eq_same, mul_one]
    · intro j _ hj
      rw [projFirst_canonVec, Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hlast : ∀ y : {i : Fin k // (i : ℕ) < ℓ} → 𝔽₂,
      projLast ℓ k (∑ i, y i • canonVec L i) = phiToLin L y := by
    intro y
    rw [map_sum]
    simp only [map_smul]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, phiToLin_apply, projLast_canonVec]
  have hker : LinearMap.ker f = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h5 : (x : Fin k → 𝔽₂) = 0 :=
      projFirst_injOn h L (x : Fin k → 𝔽₂) 0 x.2.1 (Submodule.zero_mem _)
        (by rw [← hsub x, hx, map_zero])
    exact Subtype.ext h5
  have hrange : LinearMap.range f = LinearMap.ker (phiToLin L - phiToLin L') := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hsub x]
      exact ((mem_iff_phiToLin h L (x : Fin k → 𝔽₂)).mp x.2.1).symm.trans
        ((mem_iff_phiToLin h L' (x : Fin k → 𝔽₂)).mp x.2.2)
    · intro hy
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hy
      refine ⟨⟨∑ i, y i • canonVec L i,
        ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (canonVec_mem L i),
         (mem_iff_phiToLin h L' _).mpr ?_⟩⟩, hfirst y⟩
      rw [hfirst y, hlast y]
      exact hy
  have h1 : Module.finrank 𝔽₂ ↥(L.carrier ⊓ L'.carrier)
      = Module.finrank 𝔽₂ (LinearMap.range f) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, finrank_bot 𝔽₂ ↥(L.carrier ⊓ L'.carrier), add_zero] at hrn
    exact hrn.symm
  have h3 : Module.finrank 𝔽₂ (LinearMap.ker (phiToLin L - phiToLin L'))
      = ℓ - Module.finrank 𝔽₂ (LinearMap.range (phiToLin L - phiToLin L')) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (phiToLin L - phiToLin L')
    have hdom : Module.finrank 𝔽₂ ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) = ℓ := by
      rw [Module.finrank_fintype_fun_eq_card, card_subLt h]
    omega
  rw [h1, hrange, h3]

/-! ## The `Matrix.rank` form of the homomorphism -/

/-- `Matrix.mulVecLin` is `Matrix.toLin` in the standard bases. -/
lemma mulVecLin_eq_toLin {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝔽₂) :
    A.mulVecLin = (Matrix.toLin (Pi.basisFun 𝔽₂ n) (Pi.basisFun 𝔽₂ m)) A := by
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin_apply, Matrix.mulVecLin_apply]
  have hrepr : ((Pi.basisFun 𝔽₂ n).repr v) = v := by funext i; rw [Pi.basisFun_repr]
  rw [hrepr]
  simpa [Pi.basisFun_apply, Pi.basisFun_repr] using
    ((Pi.basisFun 𝔽₂ m).sum_repr (A.mulVec v)).symm

/-- The rank of `Matrix.vecMulLinear A` is `A.rank`. -/
lemma finrank_range_vecMulLinear {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝔽₂) :
    Module.finrank 𝔽₂ (LinearMap.range (Matrix.vecMulLinear A)) = A.rank := by
  have h1 : Matrix.vecMulLinear A = A.transpose.mulVecLin := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.vecMulLinear_apply, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
  rw [h1, mulVecLin_eq_toLin A.transpose,
    ← Matrix.rank_eq_finrank_range_toLin A.transpose (Pi.basisFun 𝔽₂ n) (Pi.basisFun 𝔽₂ m),
    Matrix.rank_transpose]

lemma phiToLin_sub {k ℓ : ℕ} (L L' : VGood k ℓ) :
    phiToLin L - phiToLin L' = Matrix.vecMulLinear (phi L - phi L') := by
  rw [phiToLin, phiToLin, ← map_sub]

/-- **The graph homomorphism, `Matrix.rank` form**: the intersection dimension of `V, V'` is
`ℓ` minus the rank of `φ(V) − φ(V')`. -/
lemma finrank_inf_eq_rank {k ℓ : ℕ} (h : ℓ ≤ k) (L L' : VGood k ℓ) :
    Module.finrank 𝔽₂ ↥(L.carrier ⊓ L'.carrier) = ℓ - (phi L - phi L').rank := by
  rw [finrank_inf_eq h L L', phiToLin_sub L L', finrank_range_vecMulLinear]

/-- **`φ` maps the Grassmann graph to the shortcode graph**: two good vertices are adjacent in
`Gr k ℓ` iff their `φ`-images differ by a rank-one matrix. -/
lemma adj_iff_rank_one {k ℓ : ℕ} (h : ℓ ≤ k) (L L' : VGood k ℓ) (hℓ : 2 ≤ ℓ) :
    Module.finrank 𝔽₂ ↥(L.carrier ⊓ L'.carrier) = ℓ - 1 ↔ (phi L - phi L').rank = 1 := by
  rw [finrank_inf_eq_rank h L L']
  constructor <;> intro h1 <;> omega


/-! ## `φ` with the index types normalised to `Fin` -/

/-- BKS's `φ` with the index types normalised to `Fin ℓ` and `Fin (k - ℓ)`, so that it can be
fed to the shortcode `HypSSE` (which is stated for `Matrix (Fin m) (Fin n) 𝔽₂`). -/
noncomputable def phiFin {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ) :
    Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂ :=
  Matrix.reindex (subLtEquiv h) (subGeEquiv h) (phi L)

@[simp] lemma phiFin_apply {k ℓ : ℕ} (h : ℓ ≤ k) (L : VGood k ℓ)
    (i : Fin ℓ) (j : Fin (k - ℓ)) :
    phiFin h L i j = phi L ((subLtEquiv h).symm i) ((subGeEquiv h).symm j) := by
  rw [phiFin, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma phiFin_rank {k ℓ : ℕ} (h : ℓ ≤ k) (L L' : VGood k ℓ) :
    (phiFin h L - phiFin h L').rank = (phi L - phi L').rank := by
  have h1 : phiFin h L - phiFin h L'
      = (phi L - phi L').submatrix (subLtEquiv h).symm (subGeEquiv h).symm := by
    ext i j
    simp only [Matrix.sub_apply, phiFin_apply, Matrix.submatrix_apply]
  rw [h1]
  exact Matrix.rank_submatrix (phi L - phi L') (subLtEquiv h).symm (subGeEquiv h).symm

/-- **The graph homomorphism with `Fin` indices.** -/
lemma adj_iff_rank_one_fin {k ℓ : ℕ} (h : ℓ ≤ k) (L L' : VGood k ℓ) (hℓ : 2 ≤ ℓ) :
    Module.finrank 𝔽₂ ↥(L.carrier ⊓ L'.carrier) = ℓ - 1 ↔
      (phiFin h L - phiFin h L').rank = 1 := by
  rw [phiFin_rank h L L']
  exact adj_iff_rank_one h L L' hℓ


end
end Submission.Grassmann
