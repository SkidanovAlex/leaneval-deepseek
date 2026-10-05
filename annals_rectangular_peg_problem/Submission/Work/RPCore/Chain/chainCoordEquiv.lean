import Mathlib
import Submission.Work.RPCore.Chain.C4Defs

/-!
# C4: coordinates on the chain space with `diagVec n` as a coordinate direction

The chain space `ChainSp n = (Fin (n+1) → ℝ²) × (Fin n → ℝ²)` is a real vector space of dimension
`4n+2`.  The reference quadratic form `BvForm n N δ` of the chain action has the line
`ℝ ∙ diagVec n` as its kernel, so for the saddle-point analysis one wants to regard `ChainSp n` as
"one distinguished coordinate `c` along `diagVec n` plus `4n+1` transversal coordinates".  This
file provides exactly that: a linear isomorphism

`(ℝ × EuclideanSpace ℝ (Fin M)) ≃ₗ[ℝ] ChainSp n`,  `M = 4n+1`,

sending the first coordinate axis `(1, 0)` to `diagVec n`.

The proof is abstract: two nonzero vectors in finite-dimensional vector spaces of the same
dimension over a field can always be matched by a linear isomorphism
(`exists_linearEquiv_apply_eq`), and the two spaces here have dimension `4n+2`
(`finrank_chainSp`, `finrank_prod_euclideanSpace`).
-/

namespace Work.RPCore.Chain

noncomputable section

/-! ### Matching nonzero vectors by a linear equivalence -/

/-- **Two nonzero vectors in spaces of the same (finite) dimension are linearly equivalent.**
Over a field, and for finite-dimensional `V`, `W` of equal dimension, any nonzero `v : V` can be
carried to any nonzero `w : W` by a linear isomorphism. -/
theorem exists_linearEquiv_apply_eq {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (v : V) (w : W) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Module.finrank K V = Module.finrank K W) :
    ∃ e : V ≃ₗ[K] W, e v = w := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (K ∙ v)
  obtain ⟨q', hq'⟩ := Submodule.exists_isCompl (K ∙ w)
  have hV := Submodule.finrank_add_eq_of_isCompl hq
  have hW := Submodule.finrank_add_eq_of_isCompl hq'
  have hkv : Module.finrank K (K ∙ v) = 1 := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.toSpanNonzeroSingleton K V v hv),
      Module.finrank_self]
  have hkw : Module.finrank K (K ∙ w) = 1 := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.toSpanNonzeroSingleton K W w hw),
      Module.finrank_self]
  have hdim : Module.finrank K q = Module.finrank K q' := by
    rw [hkv] at hV; rw [hkw] at hW; rw [h] at hV; omega
  -- `F v = (1, 0)` and `G w = (1, 0)`: split each space into the line through the special vector
  -- and a complement thereof.
  let F : V ≃ₗ[K] K × q :=
    (Submodule.prodEquivOfIsCompl (K ∙ v) q hq).symm.trans
      ((LinearEquiv.coord K V v hv).prodCongr (LinearEquiv.refl K q))
  let G : W ≃ₗ[K] K × q' :=
    (Submodule.prodEquivOfIsCompl (K ∙ w) q' hq').symm.trans
      ((LinearEquiv.coord K W w hw).prodCongr (LinearEquiv.refl K q'))
  have hF : F v = (1, 0) := by
    have h1 : (Submodule.prodEquivOfIsCompl (K ∙ v) q hq).symm v
        = (⟨v, Submodule.mem_span_singleton_self v⟩, 0) := by
      simpa using Submodule.prodEquivOfIsCompl_symm_apply_left (K ∙ v) q hq
        ⟨v, Submodule.mem_span_singleton_self v⟩
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
      LinearEquiv.coord_self, LinearEquiv.refl_apply]
  have hG : G w = (1, 0) := by
    have h1 : (Submodule.prodEquivOfIsCompl (K ∙ w) q' hq').symm w
        = (⟨w, Submodule.mem_span_singleton_self w⟩, 0) := by
      simpa using Submodule.prodEquivOfIsCompl_symm_apply_left (K ∙ w) q' hq'
        ⟨w, Submodule.mem_span_singleton_self w⟩
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
      LinearEquiv.coord_self, LinearEquiv.refl_apply]
  refine ⟨F.trans (((LinearEquiv.refl K K).prodCongr
    (LinearEquiv.ofFinrankEq (R := K) q q' hdim)).trans G.symm), ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hF, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, map_zero]
  rw [← hG, LinearEquiv.symm_apply_apply]

/-! ### Dimensions -/

/-- The chain space of `n + 1` positions and `n` momenta has dimension `4n + 2`. -/
theorem finrank_chainSp (n : ℕ) : Module.finrank ℝ (ChainSp n) = 4 * n + 2 := by
  simp only [ChainSp, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_prod,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- `ℝ × EuclideanSpace ℝ (Fin M)` has dimension `M + 1`. -/
theorem finrank_prod_euclideanSpace (M : ℕ) :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin M)) = M + 1 := by
  simp [Module.finrank_prod, Nat.add_comm]

/-- The diagonal direction is nonzero. -/
theorem diagVec_ne_zero (n : ℕ) : diagVec n ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : ChainSp n => (z.1 0).2) h
  exact one_ne_zero h1

/-! ### The coordinate isomorphism -/

theorem chainCoordEquiv (n : ℕ) :
    ∃ (M : ℕ) (e : (ℝ × EuclideanSpace ℝ (Fin M)) ≃ₗ[ℝ] Work.RPCore.Chain.ChainSp n),
      e (1, 0) = Work.RPCore.Chain.diagVec n := by
  refine ⟨4 * n + 1, ?_⟩
  refine exists_linearEquiv_apply_eq (1, 0) (diagVec n) ?_ (diagVec_ne_zero n) ?_
  · intro h
    exact one_ne_zero (congrArg Prod.fst h)
  · rw [finrank_prod_euclideanSpace, finrank_chainSp]

end

end Work.RPCore.Chain
