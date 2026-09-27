import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtProdB
import Submission.Work.KT.ExtAux.MilnorExact
import Submission.Work.KT.ExtAux.ext_lift_property

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md (the lead's design for the odd case: Adams–Atiyah via K₀ of rings of continuous functions, ψ² and ψ³ from symmetric-power eigenspaces, Bott periodicity via Atiyah–Bott clutching). Shared definitions: Submission/Work/KT/Defs.lean (do NOT edit). CONVENTION: use [Ring A] plus an explicit commutativity hypothesis, never [CommRing A] on subalgebras (unification timeouts). Siblings run in parallel.

# Node `ext_product`

**Statement** (`ext_product.lean`, harness format; imports: `Submission.Work.KT.Defs`; namespace `Work.KT`):

```lean
/ -- The reduced external product `K̃(S^a) × K̃(S^b) → K̃(S^a ∧ S^b)` exists, and
`K̃(S^a ∧ S^b)` injects into `K(S^a × S^b)`. - /
theorem ext_product (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) :
    (∃ μx, IsExtProd V W y0V y0W y0 μx) ∧
    ∀ w, K0.mapA (augPair (V × W) y0) w = 0 → K0.mapA (smashIncl V W) w = 0 → w = 0 := by sorry
```

**Size:** 3–6k lines. **Risk:** medium. **Depends on (statements):** k0_exact, k0_basic, homotopy_inv. **Day 1:** no.

## Route

* `prodAlg V W = C(S^a × S^b)` and `Kpair (V×W) = C(S^a ∧ S^b)`. The latter is literal, because
  with the sup norm `∂(D_V×D_W) = S_V×D_W ∪ D_V×S_W`.
* **Injectivity.** Apply k0_exact (1)+(2) to `π : prodAlg → C(S^a ∨ S^b)` (restriction to the
  wedge `= (S_V×D_W ∪ D_V×S_W)/~`), best realised as the pull-back algebra
  `Kpair V ×_ℂ Kpair W`. Every invertible `u = (u₁,u₂)` over the wedge algebra lifts *exactly*:
  `U(x,y) = u₁(x)·u₂(y)·u(pt)⁻¹`. Hence the kernel of `K̃(smash) → K(prod)` is zero.
* **Existence of `μx`.** For reduced `s`, `t`, the product `pullFst s · pullSnd t` restricts to
  `0` on the wedge: on `S^a × pt` it is `s·(rank-0 constant) = 0`, and similarly on the other
  factor.
  * Its image in `K₀(wedge) = K̃(S^a) ⊕ K̃(S^b) ⊕ ℤ` (Milnor square, k0_exact (3)) is therefore `0`.
  * By exactness (1) it lifts uniquely to `K̃(Kpair(V×W))`.
  * Define `μx` on `K₀ = ℤ·1 ⊕ K̃` (split by the augmentation) as zero on `ℤ·1`.
  * Additivity follows from uniqueness.
-/

namespace Work.KT

open Matrix

noncomputable section

-- The nested-subalgebra instances are expensive to synthesise.
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 20000000

/-! ## `K₀`-valued helpers -/

section Helpers

variable {A B C : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Ring C] [Algebra ℂ C]

lemma ep_mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  ExtAux.k0map_comp A B C φ.toRingHom ψ.toRingHom

lemma ep_mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  ExtAux.k0map_id A

/-- If `ψ ∘ φ = id` then `K₀(φ)` has a left inverse. -/
lemma ep_mapA_comp_id (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] A)
    (h : ψ.comp φ = AlgHom.id ℂ A) :
    (K0.mapA ψ).comp (K0.mapA φ) = AddMonoidHom.id (K0 A) := by
  rw [← ep_mapA_comp φ ψ, h, ep_mapA_id]

/-- If `ψ ∘ φ = id` then `K₀(φ)` is injective. -/
lemma ep_mapA_injective (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] A)
    (h : ψ.comp φ = AlgHom.id ℂ A) : Function.Injective (K0.mapA φ) := by
  intro a b hab
  have h1 : (K0.mapA ψ).comp (K0.mapA φ) = AddMonoidHom.id (K0 A) := ep_mapA_comp_id φ ψ h
  have h2 : K0.mapA ψ (K0.mapA φ a) = K0.mapA ψ (K0.mapA φ b) := by rw [hab]
  have h3 : ((K0.mapA ψ).comp (K0.mapA φ)) a = ((K0.mapA ψ).comp (K0.mapA φ)) b := h2
  rw [h1] at h3
  simpa using h3

/-- Naturality of the product of `K₀`. -/
lemma ep_mapA_mul (hcomm : ∀ x y : A, x * y = y * x) (φ : A →ₐ[ℂ] B)
    (μA : K0 A →+ K0 A →+ K0 A) (μB : K0 B →+ K0 B →+ K0 B)
    (hA : IsK0Mul μA) (hB : IsK0Mul μB) (x y : K0 A) :
    K0.mapA φ (μA x y) = μB (K0.mapA φ x) (K0.mapA φ y) :=
  ExtAux.k0Mul_natural A B hcomm φ.toRingHom μA μB hA hB x y

/-- The product on `K₀` is unique. -/
lemma ep_isK0Mul_unique (μ μ' : K0 A →+ K0 A →+ K0 A) (h : IsK0Mul μ) (h' : IsK0Mul μ') :
    μ = μ' := by
  refine ep_hom_ext_cls _ _ (fun p hp => ?_)
  refine ep_hom_ext_cls _ _ (fun q hq => ?_)
  rw [h p q, h' p q]

end Helpers

lemma ep_k0C_iso : ∃ e : K0 ℂ ≃+ ℤ, e (cls (Mat.one ℂ 1)) = 1 :=
  ExtAux.k0C_iso

/-- The identity matrix is idempotent. -/
lemma ep_Mat_one_isIdem {R : Type} [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  exact one_mul 1

/-- The identity matrix is mapped to the identity matrix. -/
lemma ep_Mat_one_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    (Mat.one R n).map φ = Mat.one S n := by
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Matrix.map_one (⇑φ) (map_zero φ) (_root_.map_one φ))

/-! ## The reduced external product -/

/-- The reduced external product `K̃(S^a) × K̃(S^b) → K̃(S^a ∧ S^b)` exists, and
`K̃(S^a ∧ S^b)` injects into `K(S^a × S^b)`. -/
theorem ext_product (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) :
    (∃ μx, IsExtProd V W y0V y0W y0 μx) ∧
    ∀ w, K0.mapA (augPair (V × W) y0) w = 0 → K0.mapA (smashIncl V W) w = 0 → w = 0 := by
  classical
  -- ## Nontriviality of the small algebras
  haveI hntV : Nontrivial (Kpair V) := ⟨⟨1, 0, by
    intro h
    have h2 : (1 : ℂ) = 0 := congrArg (fun g : Kpair V => (g : C(Ball V, ℂ)) 0) h
    exact one_ne_zero h2⟩⟩
  haveI hntB : Nontrivial (wedgeAlg V W y0V y0W) := ⟨⟨1, 0, by
    intro h
    have h2 : (1 : Kpair V) = 0 := by
      simpa using congrArg (wedgePr₁ V W y0V y0W) h
    exact one_ne_zero h2⟩⟩
  -- Explicit instances for the nested subalgebra `wedgeAlg` (type class search does not
  -- find the `Ring`/`Algebra` instances of a subalgebra of a subalgebra).
  letI hWring : Ring ↥(wedgeAlg V W y0V y0W) :=
    @Subalgebra.toRing ℂ (Kpair V × Kpair W) _ _ _ (wedgeAlg V W y0V y0W)
  letI hWalg : Algebra ℂ ↥(wedgeAlg V W y0V y0W) := (wedgeAlg V W y0V y0W).algebra
  -- ## The fibre of the constants along the restriction to the wedge
  set U : Subalgebra ℂ (prodAlg V W) := (smashIncl V W).range with hUdef
  -- The `Ring`/`Algebra` instances for a subalgebra of a subalgebra are not found by
  -- type class search, so they are supplied explicitly here.
  letI hUring : Ring U := @Subalgebra.toRing ℂ ↥(prodAlg V W) _ _ _ U
  letI hUalg : Algebra ℂ U := U.algebra
  have hinjS : Function.Injective (smashIncl V W) := smashIncl_injective V W
  let e : Kpair (V × W) ≃ₐ[ℂ] U := AlgEquiv.ofInjective (smashIncl V W) hinjS
  have he_apply : ∀ g : Kpair (V × W), (e g : prodAlg V W) = smashIncl V W g :=
    fun g => AlgEquiv.ofInjective_apply _ _ g
  let ε : U →ₐ[ℂ] ℂ := (augPair (V × W) y0).comp e.symm.toAlgHom
  have hUcond : ∀ r : prodAlg V W,
      r ∈ U ↔ ∃ c : ℂ, wedgeProj V W y0V y0W r = algebraMap ℂ (wedgeAlg V W y0V y0W) c := by
    intro r
    rw [hUdef]
    exact mem_range_smashIncl_iff V W y0V hV y0W hW y0 hy0 r
  have hεcond : ∀ u : U, wedgeProj V W y0V y0W u = algebraMap ℂ (wedgeAlg V W y0V y0W) (ε u) := by
    intro u
    have hu : (u : prodAlg V W) = smashIncl V W (e.symm u) := by
      rw [← he_apply (e.symm u), AlgEquiv.apply_symm_apply]
    rw [show ε u = augPair (V × W) y0 (e.symm u) from rfl, hu]
    exact wedgeProj_smashIncl V W y0V hV y0W hW y0 hy0 (e.symm u)
  have hexact := ExtAux.k0_exact_middle (prodAlg V W) (wedgeAlg V W y0V y0W)
    (wedgeProj V W y0V y0W) (wedgeProj_surjective V W y0V y0W) U hUcond ε hεcond
  have hinjPart := ExtAux.k0_exact_injective (prodAlg V W) (wedgeAlg V W y0V y0W)
    (wedgeProj V W y0V y0W) (wedgeProj_surjective V W y0V y0W) U hUcond ε hεcond
  have hcomp1 : ε.comp e.toAlgHom = augPair (V × W) y0 := by
    show ((augPair (V × W) y0).comp e.symm.toAlgHom).comp e.toAlgHom = augPair (V × W) y0
    rw [AlgHom.comp_assoc]
    rw [show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ (Kpair (V × W)) from by
      apply AlgHom.ext
      intro x
      exact e.symm_apply_apply x]
    rw [AlgHom.comp_id]
  have hcomp2 : U.val.comp e.toAlgHom = smashIncl V W := by
    apply AlgHom.ext
    intro g
    apply Subtype.ext
    simpa using he_apply g
  have hcomp3 : (smashIncl V W).comp e.symm.toAlgHom = U.val := by
    apply AlgHom.ext
    intro u
    have hu : (u : prodAlg V W) = smashIncl V W (e.symm u) := by
      rw [← he_apply (e.symm u), AlgEquiv.apply_symm_apply]
    exact hu.symm
  -- ## Injectivity of the smash inclusion on reduced classes (part 2)
  have part2 : ∀ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 →
      K0.mapA (smashIncl V W) w = 0 → w = 0 := by
    intro w hw1 hw2
    have hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) (wedgeAlg V W y0V y0W)), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) (prodAlg V W)), IsUnit v ∧
          v.map (wedgeProj V W y0V y0W) =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1) :=
      fun n u hu => ExtAux.ext_lift_property V W y0V hV y0W hW n u hu
    have key := hinjPart hlift
    have h1 : K0.mapA ε (K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w) = 0 := by
      rw [← AddMonoidHom.comp_apply, ← ep_mapA_comp (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) ε,
        hcomp1]
      exact hw1
    have h2 : K0.mapA U.val (K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w) = 0 := by
      rw [← AddMonoidHom.comp_apply, ← ep_mapA_comp (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) U.val,
        hcomp2]
      exact hw2
    have h3 : K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w = 0 := key _ h1 h2
    have h4 : K0.mapA (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W))
        (K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w) = w := by
      rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U)
          (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W))]
      rw [show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ (Kpair (V × W)) from by
        apply AlgHom.ext
        intro x
        exact e.symm_apply_apply x]
      rw [ep_mapA_id]
      rfl
    rw [← h4, h3]
    simp
  -- ## The classes in the wedge algebra
  have hwedge_inj : ∀ x : K0 (wedgeAlg V W y0V y0W),
      K0.mapA (wedgePr₁ V W y0V y0W) x = 0 → K0.mapA (wedgePr₂ V W y0V y0W) x = 0 → x = 0 := by
    letI hCring : Ring ↥(wedgeC V W y0V y0W) :=
      @Subalgebra.toRing ℂ ↥(wedgeAlg V W y0V y0W) _ _ _ (wedgeC V W y0V y0W)
    letI hCalg : Algebra ℂ ↥(wedgeC V W y0V y0W) := (wedgeC V W y0V y0W).algebra
    intro x hx1 hx2
    have hUc : ∀ r : wedgeAlg V W y0V y0W,
        r ∈ wedgeC V W y0V y0W ↔
          ∃ c : ℂ, wedgePr₁ V W y0V y0W r = algebraMap ℂ (Kpair V) c := fun r => Iff.rfl
    have hex' := ExtAux.k0_exact_middle (wedgeAlg V W y0V y0W) (Kpair V)
      (wedgePr₁ V W y0V y0W) (wedgePr₁_surjective V W y0V y0W) (wedgeC V W y0V y0W) hUc
      (wedgeCε V W y0V y0W) (wedgeC_eps_prop V W y0V y0W)
    obtain ⟨w, _hw1, hw2⟩ := hex' x hx1
    have hinj : Function.Injective (K0.mapA (wedgeCpr₂ V W y0V y0W)) :=
      ep_mapA_injective (wedgeCpr₂ V W y0V y0W) (wedgeCincl V W y0V y0W)
        (wedgeCincl_comp_cpr₂ V W y0V y0W)
    have hw0 : w = 0 := by
      refine hinj ?_
      rw [show K0.mapA (wedgeCpr₂ V W y0V y0W) w
          = K0.mapA (wedgePr₂ V W y0V y0W)
            (K0.mapA (wedgeC V W y0V y0W).val w) from by
        rw [show (wedgeCpr₂ V W y0V y0W)
            = (wedgePr₂ V W y0V y0W).comp (wedgeC V W y0V y0W).val from rfl]
        rw [ep_mapA_comp (wedgeC V W y0V y0W).val (wedgePr₂ V W y0V y0W)]
        rfl,
        hw2]
      exact hx2
    rw [← hw2, hw0, map_zero]
  -- ## The product on `prodAlg` and the vanishing of its image in the wedge
  have hcommA : ∀ x y : prodAlg V W, x * y = y * x := fun x y => Subtype.ext (mul_comm x.1 y.1)
  have hcommB : ∀ x y : wedgeAlg V W y0V y0W, x * y = y * x := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact mul_comm _ _
    · apply Subtype.ext
      exact mul_comm _ _
  have hcommV : ∀ x y : Kpair V, x * y = y * x := fun x y => Subtype.ext (mul_comm x.1 y.1)
  have hcommW : ∀ x y : Kpair W, x * y = y * x := fun x y => Subtype.ext (mul_comm x.1 y.1)
  obtain ⟨μA, hμA⟩ := ExtAux.k0Mul_exists (prodAlg V W) hcommA
  obtain ⟨μB, hμB⟩ := ExtAux.k0Mul_exists (wedgeAlg V W y0V y0W) hcommB
  obtain ⟨μV, hμV⟩ := ExtAux.k0Mul_exists (Kpair V) hcommV
  obtain ⟨μW, hμW⟩ := ExtAux.k0Mul_exists (Kpair W) hcommW
  have hwedge : ∀ s : K0 (Kpair V), K0.mapA (augPair V y0V) s = 0 →
      ∀ t : K0 (Kpair W), K0.mapA (augPair W y0W) t = 0 →
      K0.mapA (wedgeProj V W y0V y0W)
        (μA (K0.mapA (pullFst V W) s) (K0.mapA (pullSnd V W) t)) = 0 := by
    intro s hs t ht
    rw [ep_mapA_mul hcommA (wedgeProj V W y0V y0W) μA μB hμA hμB]
    rw [← AddMonoidHom.comp_apply (K0.mapA (wedgeProj V W y0V y0W)) (K0.mapA (pullFst V W)) s,
      ← ep_mapA_comp (pullFst V W) (wedgeProj V W y0V y0W),
      ← AddMonoidHom.comp_apply (K0.mapA (wedgeProj V W y0V y0W)) (K0.mapA (pullSnd V W)) t,
      ← ep_mapA_comp (pullSnd V W) (wedgeProj V W y0V y0W)]
    change μB (K0.mapA (wedgeIncl₁ V W y0V y0W) s) (K0.mapA (wedgeIncl₂ V W y0V y0W) t) = 0
    refine hwedge_inj _ ?_ ?_
    · rw [ep_mapA_mul hcommB (wedgePr₁ V W y0V y0W) μB μV hμB hμV]
      rw [← AddMonoidHom.comp_apply (K0.mapA (wedgePr₁ V W y0V y0W))
            (K0.mapA (wedgeIncl₁ V W y0V y0W)) s,
          ep_mapA_comp_id (wedgeIncl₁ V W y0V y0W) (wedgePr₁ V W y0V y0W)
            (wedgePr₁_comp_incl₁ V W y0V y0W)]
      rw [← AddMonoidHom.comp_apply (K0.mapA (wedgePr₁ V W y0V y0W))
            (K0.mapA (wedgeIncl₂ V W y0V y0W)) t,
          ← ep_mapA_comp (wedgeIncl₂ V W y0V y0W) (wedgePr₁ V W y0V y0W),
          wedgePr₁_comp_incl₂ V W y0V y0W]
      rw [ep_mapA_comp (augPair W y0W) (Algebra.ofId ℂ (Kpair V))]
      show (μV s) (K0.mapA (Algebra.ofId ℂ (Kpair V)) (K0.mapA (augPair W y0W) t)) = 0
      rw [ht, map_zero, map_zero]
    · rw [ep_mapA_mul hcommB (wedgePr₂ V W y0V y0W) μB μW hμB hμW]
      rw [← AddMonoidHom.comp_apply (K0.mapA (wedgePr₂ V W y0V y0W))
            (K0.mapA (wedgeIncl₂ V W y0V y0W)) t,
          ep_mapA_comp_id (wedgeIncl₂ V W y0V y0W) (wedgePr₂ V W y0V y0W)
            (wedgePr₂_comp_incl₂ V W y0V y0W)]
      rw [← AddMonoidHom.comp_apply (K0.mapA (wedgePr₂ V W y0V y0W))
            (K0.mapA (wedgeIncl₁ V W y0V y0W)) s,
          ← ep_mapA_comp (wedgeIncl₁ V W y0V y0W) (wedgePr₂ V W y0V y0W),
          wedgePr₂_comp_incl₁ V W y0V y0W]
      rw [ep_mapA_comp (augPair V y0V) (Algebra.ofId ℂ (Kpair W))]
      show (μW (K0.mapA (Algebra.ofId ℂ (Kpair W)) (K0.mapA (augPair V y0V) s))) t = 0
      rw [hs, map_zero, map_zero μW]
      simp
  -- ## Construction of the reduced external product
  obtain ⟨eC, heC⟩ := ep_k0C_iso
  let redV : K0 (Kpair V) → K0 (Kpair V) :=
    fun s => s - (eC (K0.mapA (augPair V y0V) s)) • cls (Mat.one (Kpair V) 1)
  let redW : K0 (Kpair W) → K0 (Kpair W) :=
    fun t => t - (eC (K0.mapA (augPair W y0W) t)) • cls (Mat.one (Kpair W) 1)
  have haugV : K0.mapA (augPair V y0V) (cls (Mat.one (Kpair V) 1)) = cls (Mat.one ℂ 1) := by
    rw [ep_map_cls_idem (augPair V y0V).toRingHom (Mat.one (Kpair V) 1)
      (ep_Mat_one_isIdem 1), ep_Mat_one_map]
  have haugW : K0.mapA (augPair W y0W) (cls (Mat.one (Kpair W) 1)) = cls (Mat.one ℂ 1) := by
    rw [ep_map_cls_idem (augPair W y0W).toRingHom (Mat.one (Kpair W) 1)
      (ep_Mat_one_isIdem 1), ep_Mat_one_map]
  have honeC : (cls (Mat.one ℂ 1) : K0 ℂ) = eC.symm 1 := by
    rw [← heC]
    simp
  have hzsmul (k : ℤ) : k • (cls (Mat.one ℂ 1) : K0 ℂ) = eC.symm k := by
    rw [honeC, ← map_zsmul]
    simp
  have hredV : ∀ s, K0.mapA (augPair V y0V) (redV s) = 0 := by
    intro s
    have h : (eC (K0.mapA (augPair V y0V) s)) • (cls (Mat.one ℂ 1) : K0 ℂ)
        = K0.mapA (augPair V y0V) s := by
      rw [hzsmul, AddEquiv.symm_apply_apply]
    have h2 : redV s = s - (eC (K0.mapA (augPair V y0V) s)) • cls (Mat.one (Kpair V) 1) :=
      rfl
    calc K0.mapA (augPair V y0V) (redV s)
        = K0.mapA (augPair V y0V)
            (s - (eC (K0.mapA (augPair V y0V) s)) • cls (Mat.one (Kpair V) 1)) := by
          rw [h2]
      _ = K0.mapA (augPair V y0V) s
            - K0.mapA (augPair V y0V)
              ((eC (K0.mapA (augPair V y0V) s)) • cls (Mat.one (Kpair V) 1)) := by
          rw [map_sub]
      _ = K0.mapA (augPair V y0V) s
            - (eC (K0.mapA (augPair V y0V) s)) • K0.mapA (augPair V y0V)
              (cls (Mat.one (Kpair V) 1)) := by
          rw [map_zsmul]
      _ = K0.mapA (augPair V y0V) s
            - (eC (K0.mapA (augPair V y0V) s)) • (cls (Mat.one ℂ 1) : K0 ℂ) := by
          rw [haugV]
      _ = K0.mapA (augPair V y0V) s - K0.mapA (augPair V y0V) s := by rw [h]
      _ = 0 := sub_self _
  have hredW : ∀ t, K0.mapA (augPair W y0W) (redW t) = 0 := by
    intro t
    have h : (eC (K0.mapA (augPair W y0W) t)) • (cls (Mat.one ℂ 1) : K0 ℂ)
        = K0.mapA (augPair W y0W) t := by
      rw [hzsmul, AddEquiv.symm_apply_apply]
    have h2 : redW t = t - (eC (K0.mapA (augPair W y0W) t)) • cls (Mat.one (Kpair W) 1) :=
      rfl
    calc K0.mapA (augPair W y0W) (redW t)
        = K0.mapA (augPair W y0W)
            (t - (eC (K0.mapA (augPair W y0W) t)) • cls (Mat.one (Kpair W) 1)) := by
          rw [h2]
      _ = K0.mapA (augPair W y0W) t
            - K0.mapA (augPair W y0W)
              ((eC (K0.mapA (augPair W y0W) t)) • cls (Mat.one (Kpair W) 1)) := by
          rw [map_sub]
      _ = K0.mapA (augPair W y0W) t
            - (eC (K0.mapA (augPair W y0W) t)) • K0.mapA (augPair W y0W)
              (cls (Mat.one (Kpair W) 1)) := by
          rw [map_zsmul]
      _ = K0.mapA (augPair W y0W) t
            - (eC (K0.mapA (augPair W y0W) t)) • (cls (Mat.one ℂ 1) : K0 ℂ) := by
          rw [haugW]
      _ = K0.mapA (augPair W y0W) t - K0.mapA (augPair W y0W) t := by rw [h]
      _ = 0 := sub_self _
  have hredV_add : ∀ s s', redV (s + s') = redV s + redV s' := by
    intro s s'
    simp only [redV, map_add, add_zsmul]
    abel
  have hredW_add : ∀ t t', redW (t + t') = redW t + redW t' := by
    intro t t'
    simp only [redW, map_add, add_zsmul]
    abel
  have hredV_eq : ∀ s, K0.mapA (augPair V y0V) s = 0 → redV s = s := by
    intro s hs
    simp only [redV, hs, map_zero, zero_smul, sub_zero]
  have hredW_eq : ∀ t, K0.mapA (augPair W y0W) t = 0 → redW t = t := by
    intro t ht
    simp only [redW, ht, map_zero, zero_smul, sub_zero]
  have hredV_zero : redV 0 = 0 := hredV_eq 0 (by simp)
  have hredW_zero : redW 0 = 0 := hredW_eq 0 (by simp)
  have hexists : ∀ (u : K0 (Kpair V)), K0.mapA (augPair V y0V) u = 0 →
      ∀ (v : K0 (Kpair W)), K0.mapA (augPair W y0W) v = 0 →
      ∃ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 ∧
        K0.mapA (smashIncl V W) w = μA (K0.mapA (pullFst V W) u) (K0.mapA (pullSnd V W) v) := by
    intro u hu v hv
    obtain ⟨w, hw1, hw2⟩ := hexact (μA (K0.mapA (pullFst V W) u) (K0.mapA (pullSnd V W) v))
      (hwedge u hu v hv)
    refine ⟨K0.mapA (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) w, ?_, ?_⟩
    · rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) (augPair (V × W) y0)]
      show K0.mapA ε w = 0
      exact hw1
    · rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) (smashIncl V W), hcomp3]
      exact hw2
  let ψ : K0 (Kpair V) → K0 (Kpair W) → K0 (Kpair (V × W)) :=
    fun u v => Classical.choose (hexists (redV u) (hredV u) (redW v) (hredW v))
  have hψ_aug : ∀ u v, K0.mapA (augPair (V × W) y0) (ψ u v) = 0 :=
    fun u v => (Classical.choose_spec (hexists (redV u) (hredV u) (redW v) (hredW v))).1
  have hψ_smash : ∀ u v, K0.mapA (smashIncl V W) (ψ u v)
      = μA (K0.mapA (pullFst V W) (redV u)) (K0.mapA (pullSnd V W) (redW v)) :=
    fun u v => (Classical.choose_spec (hexists (redV u) (hredV u) (redW v) (hredW v))).2
  have hψ_add₂ : ∀ u v v', ψ u (v + v') = ψ u v + ψ u v' := by
    intro u v v'
    have h0 : K0.mapA (smashIncl V W) (ψ u (v + v'))
        = K0.mapA (smashIncl V W) (ψ u v) + K0.mapA (smashIncl V W) (ψ u v') := by
      rw [hψ_smash u (v + v'), hψ_smash u v, hψ_smash u v', hredW_add,
        map_add (K0.mapA (pullSnd V W)),
        map_add (μA (K0.mapA (pullFst V W) (redV u)))]
    have key : K0.mapA (smashIncl V W) (ψ u (v + v') - ψ u v - ψ u v') = 0 := by
      rw [map_sub, map_sub, h0]
      abel
    have h1 : K0.mapA (augPair (V × W) y0) (ψ u (v + v') - ψ u v - ψ u v') = 0 := by
      rw [map_sub, map_sub, hψ_aug, hψ_aug, hψ_aug]
      abel
    have h2 := part2 _ h1 key
    rw [sub_sub] at h2
    exact sub_eq_zero.mp h2
  have hψ_add₁ : ∀ u u' v, ψ (u + u') v = ψ u v + ψ u' v := by
    intro u u' v
    have h0 : K0.mapA (smashIncl V W) (ψ (u + u') v)
        = K0.mapA (smashIncl V W) (ψ u v) + K0.mapA (smashIncl V W) (ψ u' v) := by
      rw [hψ_smash (u + u') v, hψ_smash u v, hψ_smash u' v, hredV_add,
        map_add (K0.mapA (pullFst V W)), map_add μA]
      simp
    have key : K0.mapA (smashIncl V W) (ψ (u + u') v - ψ u v - ψ u' v) = 0 := by
      rw [map_sub, map_sub, h0]
      abel
    have h1 : K0.mapA (augPair (V × W) y0) (ψ (u + u') v - ψ u v - ψ u' v) = 0 := by
      rw [map_sub, map_sub, hψ_aug, hψ_aug, hψ_aug]
      abel
    have h2 := part2 _ h1 key
    rw [sub_sub] at h2
    exact sub_eq_zero.mp h2
  have hinner_add : ∀ u u' : K0 (Kpair V),
      (fun u => AddMonoidHom.mk' (ψ u) (fun v v' => hψ_add₂ u v v')) (u + u')
        = (fun u => AddMonoidHom.mk' (ψ u) (fun v v' => hψ_add₂ u v v')) u
          + (fun u => AddMonoidHom.mk' (ψ u) (fun v v' => hψ_add₂ u v v')) u' := by
    intro u u'
    apply AddMonoidHom.ext
    intro v
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
    exact hψ_add₁ u u' v
  let mx : K0 (Kpair V) →+ K0 (Kpair W) →+ K0 (Kpair (V × W)) :=
    AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (ψ u) (fun v v' => hψ_add₂ u v v'))
      hinner_add
  have hmx_apply : ∀ s t, mx s t = ψ s t := by
    intro s t
    simp only [mx, AddMonoidHom.mk'_apply]
  refine ⟨⟨mx, ?_⟩, part2⟩
  intro s t hs ht
  refine ⟨hψ_aug s t, ?_⟩
  intro μ hμ
  rw [show mx s t = ψ s t from rfl, hψ_smash s t, hredV_eq s hs, hredW_eq t ht,
    ep_isK0Mul_unique μ μA hμ hμA]

end

end Work.KT
