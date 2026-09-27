import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtProdB
import Submission.Work.KT.Bott.k0_exact
import Submission.Work.KT.ExtAux.ext_lift_property
import Submission.Work.KT.K0map.map_comp
import Submission.Work.KT.K0map.map_id

namespace Work.KT.Bott

open Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 20000000

/-! ## Functoriality of `K₀` on algebra homomorphisms -/

lemma ep_mapA_comp {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  K0map.map_comp A B C φ.toRingHom ψ.toRingHom

lemma ep_mapA_id {A : Type} [Ring A] [Algebra ℂ A] :
    K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  K0map.map_id A

lemma ep_mapA_injective {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] A) (h : ψ.comp φ = AlgHom.id ℂ A) :
    Function.Injective (K0.mapA φ) := by
  intro a b hab
  have h1 : (K0.mapA ψ).comp (K0.mapA φ) = AddMonoidHom.id (K0 A) := by
    rw [← ep_mapA_comp φ ψ, h, ep_mapA_id]
  have h2 : ((K0.mapA ψ).comp (K0.mapA φ)) a = ((K0.mapA ψ).comp (K0.mapA φ)) b := by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hab]
  rw [h1] at h2
  simpa using h2

/-- ROUTE (dependency of the node `KT/Bott/prodAlg_free`).

**The kernel of the restriction to the wedge.**  For finite-dimensional real normed `V`, `W` and
boundary points, a class `z ∈ K₀(prodAlg V W) = K(S^a × S^b)` whose two restrictions to the wedge
`S^a ∨ S^b` vanish (`wedgeFst V W y0W z = 0` on `S^a × {y0W}` and `wedgeSnd V W y0V z = 0` on
`{y0V} × S^b`) comes from a *reduced* class over `Kpair (V × W) = C(S^a ∧ S^b)` by the smash
inclusion; and conversely a reduced class killed by `smashIncl` is zero.

ROUTE.  `Work.KT.ExtProdB` provides `wedgeProj : prodAlg V W →ₐ[ℂ] wedgeAlg V W y0V y0W` (the
restriction to the wedge, whose components are `wedgeFst` and `wedgeSnd`), `wedgeProj_surjective`,
`mem_range_smashIncl_iff` (the fibre of the constants along `wedgeProj` is exactly
`(smashIncl V W).range`) and `wedgeProj_smashIncl : wedgeProj (smashIncl g) = algebraMap (aug g)`.
Put `U := (smashIncl V W).range`, with `e : Kpair (V × W) ≃ₐ[ℂ] U` from `AlgEquiv.ofInjective`
(`smashIncl_injective`) and `ε := (augPair (V × W) y0).comp e.symm`.  Then the first conjunct is
conjunct (1)(a) of `Work.KT.Bott.k0_exact` applied to `π = wedgeProj` (using that
`K₀(wedgeAlg) → K₀(Kpair V) × K₀(Kpair W)` is injective, e.g. by the same exactness at
`π' = wedgePr₁` with the fibre of its constants `wedgeC`), and the second conjunct is conjunct
(1)(b)/(2) of the same theorem (injectivity on reduced classes under stable lifting), the lifting
hypothesis being `Work.KT.ExtAux.ext_lift_property` (every invertible matrix over `wedgeAlg V W`
lifts to `prodAlg V W`).  NOTE: the statement avoids mentioning `wedgeAlg`/`wedgeProj` because the
`Ring`/`Algebra` instance search for `↥(wedgeAlg V W y0V y0W)` times out; inside the proof use the
explicit `letI ... := @Subalgebra.toRing ℂ (Kpair V × Kpair W) _ _ _ (wedgeAlg V W y0V y0W)`
device as in `Submission/Work/KT/ext_product.lean`.

IMPORTS (please respect).  Use the clean `Work.KT.Bott.k0_exact` (proved, sorry-free) for the
Milnor exactness and the clean `Work.KT.ExtAux.ext_lift_property` for the lifting hypothesis
(imports `Mathlib`, `Defs`, `ExtProdB` only).  Do NOT import `Submission.Work.KT.k0_exact` or
`Submission.Work.KT.ExtAux.MilnorExact`: their node `Work.KT.k0_exact` is unproved, and the
"false" verdict recorded against it is wrong (it uses `K₀(C(S¹)) ≅ ℤ²`, whereas `K₀(C(S¹)) ≅ ℤ`,
the proved `Work.KT.ballK_dim1`).  Also do not import `Submission.Work.KT.ext_product` (it pulls in
that unproved node); if you need the injectivity half, prove it here as stated. -/
theorem wedge_ker_smash (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
    (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W)) :
    (∀ z : K0 (prodAlg V W), K0.mapA (wedgeFst V W y0W) z = 0 →
      K0.mapA (wedgeSnd V W y0V) z = 0 →
      ∃ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 ∧
        K0.mapA (smashIncl V W) w = z) ∧
    (∀ w : K0 (Kpair (V × W)), K0.mapA (augPair (V × W) y0) w = 0 →
      K0.mapA (smashIncl V W) w = 0 → w = 0) := by
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
  -- Explicit instances for the nested subalgebra `wedgeAlg`
  letI hWring : Ring ↥(wedgeAlg V W y0V y0W) :=
    @Subalgebra.toRing ℂ (Kpair V × Kpair W) _ _ _ (wedgeAlg V W y0V y0W)
  letI hWalg : Algebra ℂ ↥(wedgeAlg V W y0V y0W) := (wedgeAlg V W y0V y0W).algebra
  -- ## The composites `wedgePrᵢ ∘ wedgeProj` are `wedgeFst`/`wedgeSnd`
  have hcomp_wp₁ : (wedgePr₁ V W y0V y0W).comp (wedgeProj V W y0V y0W) = wedgeFst V W y0W := by
    apply AlgHom.ext
    intro F
    rfl
  have hcomp_wp₂ : (wedgePr₂ V W y0V y0W).comp (wedgeProj V W y0V y0W) = wedgeSnd V W y0V := by
    apply AlgHom.ext
    intro F
    rfl
  -- ## The fibre of the constants along `wedgeProj` and its augmentation
  set U : Subalgebra ℂ (prodAlg V W) := (smashIncl V W).range with hUdef
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
  have hk := Work.KT.Bott.k0_exact.1 (prodAlg V W) (wedgeAlg V W y0V y0W)
    (wedgeProj V W y0V y0W) (wedgeProj_surjective V W y0V y0W) U hUcond ε hεcond
  have hexact := hk.1
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
    have key := hk.2 hlift
    have h1 : K0.mapA ε (K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w) = 0 := by
      rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) ε, hcomp1]
      exact hw1
    have h2 : K0.mapA U.val (K0.mapA (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) w) = 0 := by
      rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (e.toAlgHom : Kpair (V × W) →ₐ[ℂ] U) U.val, hcomp2]
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
    rw [← h4, h3, map_zero]
  -- ## `K₀(wedgeAlg) → K₀(Kpair V) × K₀(Kpair W)` is injective
  have hwedge_inj : ∀ x : K0 (wedgeAlg V W y0V y0W),
      K0.mapA (wedgePr₁ V W y0V y0W) x = 0 →
      K0.mapA (wedgePr₂ V W y0V y0W) x = 0 → x = 0 := by
    letI hCring : Ring ↥(wedgeC V W y0V y0W) :=
      @Subalgebra.toRing ℂ ↥(wedgeAlg V W y0V y0W) _ _ _ (wedgeC V W y0V y0W)
    letI hCalg : Algebra ℂ ↥(wedgeC V W y0V y0W) := (wedgeC V W y0V y0W).algebra
    intro x hx1 hx2
    have hUc : ∀ r : wedgeAlg V W y0V y0W,
        r ∈ wedgeC V W y0V y0W ↔
          ∃ c : ℂ, wedgePr₁ V W y0V y0W r = algebraMap ℂ (Kpair V) c := fun r => Iff.rfl
    have hex' := (Work.KT.Bott.k0_exact.1 (wedgeAlg V W y0V y0W) (Kpair V)
      (wedgePr₁ V W y0V y0W) (wedgePr₁_surjective V W y0V y0W) (wedgeC V W y0V y0W) hUc
      (wedgeCε V W y0V y0W) (wedgeC_eps_prop V W y0V y0W)).1
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
  refine ⟨?_, part2⟩
  -- ## The first conjunct: exactness of `K₀(prodAlg) → K₀(wedgeAlg)`
  intro z hz1 hz2
  have hz0 : K0.mapA (wedgeProj V W y0V y0W) z = 0 := by
    refine hwedge_inj _ ?_ ?_
    · rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (wedgeProj V W y0V y0W) (wedgePr₁ V W y0V y0W), hcomp_wp₁]
      exact hz1
    · rw [← AddMonoidHom.comp_apply,
        ← ep_mapA_comp (wedgeProj V W y0V y0W) (wedgePr₂ V W y0V y0W), hcomp_wp₂]
      exact hz2
  obtain ⟨w0, hw0_eps, hw0_val⟩ := hexact z hz0
  refine ⟨K0.mapA (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) w0, ?_, ?_⟩
  · rw [← AddMonoidHom.comp_apply,
      ← ep_mapA_comp (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) (augPair (V × W) y0)]
    exact hw0_eps
  · rw [← AddMonoidHom.comp_apply,
      ← ep_mapA_comp (e.symm.toAlgHom : U →ₐ[ℂ] Kpair (V × W)) (smashIncl V W), hcomp3]
    exact hw0_val

end

end Work.KT.Bott
