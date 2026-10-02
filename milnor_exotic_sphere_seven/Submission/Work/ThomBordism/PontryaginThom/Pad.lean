import Submission.Work.ThomBordism.PontryaginThom.Geometry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 1: the embedding, in the prescribed codimension

`Embedding.lean` records Mathlib's Whitney embedding theorem in the exact form available
(`exists_embedding_euclidean_of_compact`: a closed `C^∞` embedding with injective derivative into
`EuclideanSpace ℝ (Fin n)` for *some* `n`; the proof, via a bump covering, produces
`n = finrank ℝ (ι → E × ℝ)` for the covering's index type, which is not bounded by the dimension of
the manifold).

The chapter's model `PTRep V k D` is stated with a *fixed* codimension `k` (the rank of the
universal bundle whose Thom space is `D.T`), so what item 1 needs is an embedding of `V` into
`ℝ^{k+8}` — the weak Whitney embedding theorem *with the explicit bound* `k + 8 ≥ 2·8 + 1`.  This
file records what is provable here about it:

* `padCLM n t : ℝⁿ →L[ℝ] ℝ^{n+t}` — the coordinate-wise zero padding, an isometric (closed)
  embedding, hence the *padding of an embedding*: `EmbeddingData.pad E t : EmbeddingData V (n+t)`
  for `E : EmbeddingData V n`.  **This is the only direction in which Mathlib's theorem can be
  stretched: one may always enlarge the ambient space, never shrink it.**
* `WeakWhitney8 k` — the honest formulation of the remaining gap: *every* closed `C^∞`
  `8`-manifold embeds into `ℝ^{k+8}` (closed, `C^∞`, injective derivative).  This is the weak
  Whitney embedding theorem with the bound `k + 8 ≥ 17`, true for `k ≥ 9`; its statement is
  dimension-uniform, which is exactly what Mathlib's theorem does not give.  It is *not* a
  hypothesis of the chapter's main theorems in a form that hides anything: what it adds over
  `Embedding.lean` is only the *uniformity* of the codimension, and
  * `weakWhitney8_mono` (`WeakWhitney8 k → WeakWhitney8 k'` for `k ≤ k'`, by padding),
  * `exists_embeddingData_ge` (for every single `V` there *is* a `k ≥ 10` with an embedding into
    `ℝ^{k+8}`), and `exists_embeddingData_ge_family` (the same with one `k` for a finite family),
  prove that this uniformity is the *only* content: the codimension is not a mathematical gap, only
  an unboundedness of the construction Mathlib has.

So `WeakWhitney8 9` is the (true, classical — Whitney's weak embedding theorem for compact
manifolds) statement that has to be supplied by hand, and every `k ≥ 9` follows from it.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Function Topology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

/-- `ℝⁿ`, as a shorthand. -/
abbrev Euc (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **The zero padding `ℝⁿ → ℝ^{n+t}`**: the canonical inclusion of the first `n` coordinates.

It is the composite `ℝⁿ ≅ ℝⁿ × {0} ↪ ℝⁿ × ℝᵗ ≅ ℝ^{n+t}` of the canonical linear homeomorphism
`EuclideanSpace.finAddEquivProd` with the inclusion of the first factor. -/
def padCLM (n t : ℕ) : Euc n →L[ℝ] Euc (n + t) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := t)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Euc n) (Euc t))

/-- The defining equation of `padCLM`. -/
theorem padCLM_apply (n t : ℕ) (x : Euc n) :
    padCLM n t x
      = (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := t)).symm (x, 0) := rfl

/-- The padding is injective. -/
theorem padCLM_injective (n t : ℕ) : Function.Injective (padCLM n t) := by
  intro x y h
  have h2 : (x, (0 : Euc t)) = (y, 0) := by
    apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := t)).symm.injective
    simpa [padCLM] using h
  exact congrArg Prod.fst h2

/-- The padding is a closed embedding. -/
theorem isClosedEmbedding_padCLM (n t : ℕ) : IsClosedEmbedding (padCLM n t) := by
  have h1 : IsClosedEmbedding
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := t)).symm :
        Euc n × Euc t → Euc (n + t)) :=
    Homeomorph.isClosedEmbedding
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := t)).symm.toHomeomorph
  have h2 : IsClosedEmbedding (ContinuousLinearMap.inl ℝ (Euc n) (Euc t)) := by
    have h : IsClosedEmbedding (fun x : Euc n => (x, (0 : Euc t))) :=
      ⟨isEmbedding_prodMkLeft 0, by
        have hr : Set.range (fun x : Euc n => (x, (0 : Euc t))) = Set.univ ×ˢ {0} := by
          ext p
          constructor
          · rintro ⟨x, rfl⟩
            simp
          · rintro ⟨-, hp2⟩
            exact ⟨p.1, by rw [Prod.mk.injEq]; exact ⟨rfl, hp2.symm⟩⟩
        rw [hr]
        exact isClosed_univ.prod isClosed_singleton⟩
    exact h
  exact h1.comp h2

/-! ## Padding an embedding -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Euc 8) M] [IsManifold (𝓡 8) ∞ M]

/-- The padding of a smooth map. -/
theorem contMDiff_padCLM_comp {n t : ℕ} {e : M → Euc n}
    (he : ContMDiff (𝓡 8) 𝓘(ℝ, Euc n) ∞ e) :
    ContMDiff (𝓡 8) 𝓘(ℝ, Euc (n + t)) ∞ (fun x => padCLM n t (e x)) :=
  (padCLM n t).contMDiff.comp he

/-- The derivative of a padded map. -/
theorem mfderiv_padCLM_comp {n t : ℕ} {e : M → Euc n}
    (he : ContMDiff (𝓡 8) 𝓘(ℝ, Euc n) ∞ e) (x : M) :
    mfderiv (𝓡 8) 𝓘(ℝ, Euc (n + t)) (fun y => padCLM n t (e y)) x
      = (padCLM n t).comp (mfderiv (𝓡 8) 𝓘(ℝ, Euc n) e x) := by
  rw [show (fun y => padCLM n t (e y)) = ((padCLM n t) ∘ e) from rfl,
    mfderiv_comp x (padCLM n t).mdifferentiableAt (he.mdifferentiableAt (by simp)),
    (padCLM n t).mfderiv_eq]
  try rfl

/-- The derivative of a padded map is injective whenever the original one is. -/
theorem injective_mfderiv_padCLM_comp {n t : ℕ} {e : M → Euc n}
    (he : ContMDiff (𝓡 8) 𝓘(ℝ, Euc n) ∞ e) (x : M)
    (hinj : Function.Injective (mfderiv (𝓡 8) 𝓘(ℝ, Euc n) e x)) :
    Function.Injective (mfderiv (𝓡 8) 𝓘(ℝ, Euc (n + t)) (fun y => padCLM n t (e y)) x) := by
  rw [mfderiv_padCLM_comp he x]
  exact (padCLM_injective n t).comp hinj

/-- **Padding an embedding**: `EmbeddingData V n → EmbeddingData V (n + t)`, by adding `t` idle
coordinates. -/
def EmbeddingData.pad {V : Man8} {n : ℕ} (E : EmbeddingData V n) (t : ℕ) :
    EmbeddingData V (n + t) where
  e := fun x => padCLM n t (E.e x)
  smooth := contMDiff_padCLM_comp E.smooth
  closedEmbedding := (isClosedEmbedding_padCLM n t).comp E.closedEmbedding
  injective_mfderiv := fun x => injective_mfderiv_padCLM_comp E.smooth x (E.injective_mfderiv x)

/-! ## The uniform Whitney embedding bound -/

/-- **The uniform weak Whitney embedding bound**: every closed `C^∞` `8`-manifold admits a closed
`C^∞` embedding into `ℝ^{k+8}` with injective derivative.

This is the weak Whitney embedding theorem with the explicit bound `k + 8 ≥ 2·8 + 1`, i.e. it holds
for every `k ≥ 9`; it is stated as a `Prop` because Mathlib's Whitney embedding theorem
(`embeddingData_of_mathlib`) gives the codimension only manifold by manifold — see the file header. -/
def WeakWhitney8 (k : ℕ) : Prop := ∀ V : Man8, Nonempty (EmbeddingData V (k + 8))

/-- **The uniform bound is monotone in `k`**: an embedding into `ℝ^{k+8}` is one into `ℝ^{k'+8}`
for `k' ≥ k`, by padding.  (This is the *only* direction in which the codimension can be moved, and
it is why the uniformity of `WeakWhitney8` is the whole of its content.) -/
theorem weakWhitney8_mono {k k' : ℕ} (h : k ≤ k') (hk : WeakWhitney8 k) : WeakWhitney8 k' := by
  intro V
  obtain ⟨E⟩ := hk V
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : k + 8 ≤ k' + 8)
  rw [ht]
  exact ⟨E.pad t⟩

/-- **The one classical input of the embedding half of item 1**: Whitney's weak embedding theorem
with the explicit bound — every closed `C^∞` `8`-manifold embeds into `ℝ^{17} = ℝ^{9+8}`.  (Mathlib's
`exists_embedding_euclidean_of_compact` gives the embedding in an *unbounded* dimension; the bound
`2·8 + 1` is the classical weak Whitney theorem.) -/
def WeakWhitney8Nine : Prop := WeakWhitney8 9

/-- **The uniform bound for every `k ≥ 9`, from the classical input** (by padding). -/
theorem weakWhitney8_of_nine (h : WeakWhitney8Nine) {k : ℕ} (hk : 9 ≤ k) : WeakWhitney8 k :=
  weakWhitney8_mono hk h

/-- **For every single manifold there is a codimension `k ≥ 10` realising it**: Mathlib's embedding
theorem, padded to any larger ambient space. -/
theorem exists_embeddingData_ge (V : Man8) :
    ∃ k : ℕ, 10 ≤ k ∧ Nonempty (EmbeddingData V (k + 8)) := by
  obtain ⟨n, ⟨E⟩⟩ := embeddingData_of_mathlib V
  refine ⟨max 10 (n - 8), le_max_left _ _, ?_⟩
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ max 10 (n - 8) + 8)
  rw [ht]
  exact ⟨E.pad t⟩

/-- **The same with one codimension for a whole finite family**: the maximum of the codimensions of
the pieces.  (This is the form in which the uniformity of `WeakWhitney8` is *proved* per family, and
it is why no uniform bound is needed when the codimension may be chosen after the family — see
`README.md`.) -/
theorem exists_embeddingData_ge_family {ι : Type} [Fintype ι] (F : ι → Man8) :
    ∃ k : ℕ, 10 ≤ k ∧ ∀ i, Nonempty (EmbeddingData (F i) (k + 8)) := by
  classical
  choose n E using fun i => embeddingData_of_mathlib (F i)
  refine ⟨max 10 ((Finset.univ.sup n) - 8), le_max_left _ _, fun i => ?_⟩
  have hi : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : n i ≤ max 10 (Finset.univ.sup n - 8) + 8)
  rw [ht]
  obtain ⟨Ei⟩ := E i
  exact ⟨Ei.pad t⟩

/-! ## The immersion input of the normal-bundle construction -/

/-- **The classical immersion input**: every closed `C^∞` `8`-manifold immerses into `ℝ^{8+k}`
(a smooth map with injective derivative).

This is Whitney's immersion theorem with the bound (`2·8 = 16 ≤ 8 + k`, i.e. `k ≥ 8`), the
general-position/Sard-level statement that supplies the normal bundle of an embedding.  It is the
*single* classical input of the `NormalBundleExists` construction (see `README.md` §4.4): everything
else — the complement of the immersed plane, the complement bundle, its transitions and the splitting
`TV ⊕ ν ≅ ε^{8+k}` — is constructed in this chapter. -/
def WeakWhitneyImmersion (k : ℕ) : Prop :=
  ∀ V : Man8, ∃ f : V.pt → Euc (8 + k),
    ContMDiff (𝓡 8) 𝓘(ℝ, Euc (8 + k)) ∞ f ∧
      ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) 𝓘(ℝ, Euc (8 + k)) f x)

/-- The classical input in the form in which the literature states it: an immersion into `ℝ^{16}`
(Whitney's weak immersion theorem for a closed `8`-manifold). -/
def ImmersionBound : Prop := WeakWhitneyImmersion 8

/-- **The immersion bound is monotone in `k`**: an immersion into `ℝ^{8+k}` is one into `ℝ^{8+k'}`
for `k' ≥ k`, by padding the *target* (`padCLM`). -/
theorem weakWhitneyImmersion_mono {k k' : ℕ} (h : k ≤ k') (hk : WeakWhitneyImmersion k) :
    WeakWhitneyImmersion k' := by
  intro V
  obtain ⟨f, hsmooth, hinj⟩ := hk V
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : 8 + k ≤ 8 + k')
  rw [ht]
  exact ⟨fun x => padCLM (8 + k) t (f x),
    contMDiff_padCLM_comp (n := 8 + k) (t := t) hsmooth,
    fun x => injective_mfderiv_padCLM_comp (n := 8 + k) (t := t) hsmooth x (hinj x)⟩

/-- The classical input gives the immersion into `ℝ^{8+k}` for every `k ≥ 8`. -/
theorem weakWhitneyImmersion_of_bound {k : ℕ} (hk : 8 ≤ k) (h : ImmersionBound) :
    WeakWhitneyImmersion k :=
  weakWhitneyImmersion_mono hk h

end

end Work.ThomBordism.PontryaginThom
