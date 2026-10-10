import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.exists_linearMap_extend_sha1Descent
import Submission.Work.SSGRoute.tateDuality_hm2_dual_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# sha2_image_of_Hm2_of_dualControl  (assembly, provable NOW, no arithmetic)

**Statement.** The conclusion of `sha2_image_of_Hm2_fin`, given the dual-control hypothesis `hctrl`.
`hctrl` is exactly the conclusion of `sha2_dual_control` for this `c`. `T` is only required finite.

**Proof.** Put `M := DualMod p (E ⊗ T)` and `M₂ := DualMod p (E₂ ⊗ T)`.
1. **Descent is injective.** `descentHom p k Ω K M : Z1loc → H¹(G,M)` has kernel `B1top`
   (`descentHom_eq_zero_iff_mem_B1top`, sha1_descent_H1.lean, PROVED). So it induces an injective
   `ι : Sha1 → H¹(G,M)` (`Submodule.liftQ`; make it `ZMod p`-linear with `AddMonoidHom.toZModLinearMap`).
2. **Extend `l`.** Pick `l̃ : H¹(G,M) →ₗ 𝔽_p` with `l̃ ∘ ι = l`, using `LinearMap.exists_extend` over the
   field `ZMod p`.
3. **Define `x`.** Let `e` be the natural equivalence of `tateDuality_hm2_dual_natural`, and
   `ev : E⊗T ≃ DualMod p M` the evaluation equivalence (`Module.evalEquiv`, finite dimension; it is
   G-equivariant). Set `x := Hm2Map ev.symm (e M ⁻¹ l̃)`.
4. **Conclude.** Given `f`, set `f' := (f.rTensor T).dualMap`. Equivariance follows from `rTensor_equiv`,
   and `hff'` holds by `rfl`/`simp`.
   - From `Hm2Map (f⊗T) x = 0`: naturality of `e` (applied to `f' : M₂ → M`) and of `ev` give
     `l̃ ∘ mapH1 f' = 0`.
   - `descentHom_pushC1` then gives `l ∘ Sha1Map f' = 0`. Apply `hctrl`.

**Imports.** ShaCocycles, `sha1_descent_H1`, `tateDuality_hm2_dual_natural`, `CohomologicalShrinking.All`.
**Size.** Medium-small, about 150 lines. The only fiddly part is Hm2Map along `ev`.
-/

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct

/-! ## Auxiliary facts used in the assembly -/

/-- The tensor product of two finite modules over a finite (semi)ring is finite: it is the image
of the finite set of `𝔽_p`-linear combinations of the pure tensors. -/
noncomputable instance finite_tensorProduct (R M N : Type) [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Finite R] [Finite M] [Finite N] :
    Finite (M ⊗[R] N) := by
  classical
  haveI : Fintype (M × N) := Fintype.ofFinite _
  refine Finite.of_surjective
    (fun c : M × N → R => ∑ p : M × N, c p • (p.1 ⊗ₜ[R] p.2)) ?_
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m n => exact ⟨Pi.single (m, n) 1, by simp⟩
  | add x y hx hy =>
      obtain ⟨c, rfl⟩ := hx; obtain ⟨d, rfl⟩ := hy
      refine ⟨c + d, ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The transpose of a `G`-equivariant linear map is `G`-equivariant for the dual action. -/
theorem dualMap_equiv (p : ℕ) {G A B : Type} [Group G] [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B] [DistribMulAction G A] [DistribMulAction G B]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B]
    (f : A →ₗ[ZMod p] B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ∀ (g : G) (φ : DualMod p B), f.dualMap (g • φ) = g • f.dualMap φ := by
  intro g φ
  ext m
  simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply, hf]

/-- `Hm2Map` only depends on the underlying additive map, not on the proof of equivariance. -/
theorem Hm2Map_proof_irrel {G A B : Type} [Group G] [Fintype G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] (f : A →+ B)
    (h1 h2 : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Work.Tate.Hm2Map f h1 = Work.Tate.Hm2Map f h2 := by
  have h : h1 = h2 := Subsingleton.elim _ _
  rw [h]

/-- The evaluation map `M → M^{**}` is `G`-equivariant. -/
theorem dual_eval_equiv (p : ℕ) {G A : Type} [Group G] [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] :
    ∀ (g : G) (a : A), Module.Dual.eval (ZMod p) A (g • a)
      = g • Module.Dual.eval (ZMod p) A a := by
  intro g a
  ext φ
  simp only [Module.Dual.eval_apply, Work.SSGRoute.DualMod.dualSMul_apply, inv_inv]

/-- The double-dual equivalence is `G`-equivariant. -/
theorem evalEquiv_equiv (p : ℕ) {G A : Type} [Group G] [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] [Module.IsReflexive (ZMod p) A] :
    ∀ (g : G) (a : A), Module.evalEquiv (ZMod p) A (g • a)
      = g • Module.evalEquiv (ZMod p) A a := by
  simpa only [Module.evalEquiv_apply] using dual_eval_equiv (p := p) (G := G) (A := A)

/-- The inverse of the double-dual equivalence is `G`-equivariant. -/
theorem evalEquiv_symm_equiv (p : ℕ) {G A : Type} [Group G] [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] [Module.IsReflexive (ZMod p) A] :
    ∀ (g : G) (b : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p A)),
      (Module.evalEquiv (ZMod p) A).symm (g • b) = g • (Module.evalEquiv (ZMod p) A).symm b := by
  intro g b
  apply (Module.evalEquiv (ZMod p) A).injective
  rw [LinearEquiv.apply_symm_apply, evalEquiv_equiv (p := p) (G := G) (A := A),
    LinearEquiv.apply_symm_apply]

/-- **The element of `Ĥ⁻²(G, S)` dual to a functional on `H¹(G, S^∨)`.**

`Work.SSGRoute.dualE p G M : Ĥ⁻²(G, M^∨) ≃+ (H¹(G,M) →+ 𝔽_p)` identifies degree `-2` Tate
cohomology of the dual with the dual of `H¹`.  Applied at `M := S^∨`, it converts an additive
functional `L` on `H¹(G, S^∨)` into an element `x` of `Ĥ⁻²(G, S)` (via the equivariant double-dual
equivalence `S ≅ S^{**}`) with the following naturality property: for every `G`-equivariant
`𝔽_p`-linear `fT : S → S₂` with `S₂` finite, if `Hm2Map fT x = 0` then `L` vanishes on the image
of `(fT^∨)_* : H¹(G, S₂^∨) → H¹(G, S^∨)`. -/
theorem hm2_of_dualFunctional_exists (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (S : Type) [AddCommGroup S] [Module (ZMod p) S] [DistribMulAction G S]
    [SMulCommClass G (ZMod p) S] [Finite S]
    (L : Work.GroupCohomology.H1 G (Work.SSGRoute.DualMod p S) →+ ZMod p) :
    ∃ x : Work.Tate.Hm2 G S,
      ∀ (S₂ : Type) [AddCommGroup S₂] [Module (ZMod p) S₂] [DistribMulAction G S₂]
        [SMulCommClass G (ZMod p) S₂] [Finite S₂]
        (fT : S →ₗ[ZMod p] S₂) (hfT : ∀ (g : G) (z : S), fT (g • z) = g • fT z)
        (hfT' : ∀ (g : G) (φ : Work.SSGRoute.DualMod p S₂),
          fT.dualMap (g • φ) = g • fT.dualMap φ),
        Work.Tate.Hm2Map fT.toAddMonoidHom hfT x = 0 →
          ∀ z : Work.GroupCohomology.H1 G (Work.SSGRoute.DualMod p S₂),
            L (Work.GroupCohomology.mapH1 G fT.dualMap.toAddMonoidHom hfT' z) = 0 := by
  classical
  haveI : Finite (Work.SSGRoute.DualMod p S) := inferInstance
  haveI : Module.IsReflexive (ZMod p) S := inferInstance
  -- the double-dual equivalence and its equivariance
  let ev : S ≃ₗ[ZMod p] Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S) :=
    Module.evalEquiv (ZMod p) S
  have hevsymm := evalEquiv_symm_equiv (p := p) (G := G) (A := S)
  -- the element dual to `L`
  let y : Work.Tate.Hm2 G (Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)) :=
    (Work.SSGRoute.dualE p G (Work.SSGRoute.DualMod p S)).symm L
  refine ⟨Work.Tate.Hm2Map ev.symm.toAddMonoidHom hevsymm y, ?_⟩
  intro S₂ _ _ _ _ _ fT hfT hfT' h0 z
  haveI : Finite (Work.SSGRoute.DualMod p S₂) := inferInstance
  haveI : Module.IsReflexive (ZMod p) S₂ := inferInstance
  let ev₂ : S₂ ≃ₗ[ZMod p] Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S₂) :=
    Module.evalEquiv (ZMod p) S₂
  have hev₂ := evalEquiv_equiv (p := p) (G := G) (A := S₂)
  -- Step 1: `Hm2Map fT x = Hm2Map (fT ∘ ev.symm) y`
  have hfe : ∀ (g : G) (a : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)),
      (fT.toAddMonoidHom.comp ev.symm.toAddMonoidHom) (g • a)
        = g • (fT.toAddMonoidHom.comp ev.symm.toAddMonoidHom) a := fun g a => by
    show fT (ev.symm (g • a)) = g • fT (ev.symm a)
    rw [hevsymm g a, hfT g (ev.symm a)]
  have hcomp1 := Work.CohomologicalShrinking.tate.Hm2Map_comp (G := G)
    (A := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)) (B := S) (C := S₂)
    (e := ev.symm.toAddMonoidHom) (he := hevsymm) (f := fT.toAddMonoidHom) (hf := hfT)
    (hfe := hfe)
  have hAx : Work.Tate.Hm2Map (fT.toAddMonoidHom.comp ev.symm.toAddMonoidHom) hfe y = 0 := by
    rw [DFunLike.congr_fun hcomp1 y]
    exact h0
  -- Step 2: `(fT^∨)^∨` is the conjugate of `fT` by the double-dual equivalences
  have hevnat : fT.dualMap.dualMap.toAddMonoidHom
      = (ev₂.toAddMonoidHom).comp ((fT.toAddMonoidHom).comp (ev.symm.toAddMonoidHom)) := by
    have hlin : (fT.dualMap.dualMap :
          Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S) →ₗ[ZMod p]
            Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S₂))
        = (ev₂ : S₂ →ₗ[ZMod p] Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S₂)).comp
            (fT.comp (ev.symm : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S) →ₗ[ZMod p] S)) := by
      rw [← Module.Dual.eval_comp_comp_evalEquiv_eq (ZMod p) S (f := fT)]
      rw [Module.evalEquiv_toLinearMap]
    exact congrArg LinearMap.toAddMonoidHom hlin
  have hfe2 : ∀ (g : G) (w : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)),
      ((ev₂.toAddMonoidHom).comp ((fT.toAddMonoidHom).comp (ev.symm.toAddMonoidHom))) (g • w)
        = g • ((ev₂.toAddMonoidHom).comp
            ((fT.toAddMonoidHom).comp (ev.symm.toAddMonoidHom))) w :=
    fun g w => by
      show ev₂ (fT (ev.symm (g • w))) = g • (ev₂ (fT (ev.symm w)))
      rw [hevsymm g w, hfT g (ev.symm w), hev₂ g (fT (ev.symm w))]
  have hgg : ∀ (g : G) (w : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)),
      fT.dualMap.dualMap (g • w) = g • fT.dualMap.dualMap w :=
    dualMap_equiv p fT.dualMap hfT'
  have hy0 : Work.Tate.Hm2Map fT.dualMap.dualMap.toAddMonoidHom hgg y = 0 := by
    rw [Work.CohomologicalShrinking.operator.Hm2Map_congr (G := G) hgg hfe2 hevnat]
    rw [DFunLike.congr_fun (Work.CohomologicalShrinking.tate.Hm2Map_comp (G := G)
      (A := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S)) (B := S₂)
      (C := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S₂))
      (e := fT.toAddMonoidHom.comp ev.symm.toAddMonoidHom) (he := hfe)
      (f := ev₂.toAddMonoidHom) (hf := hev₂) (hfe := hfe2)) y]
    rw [AddMonoidHom.comp_apply, hAx]
    exact map_zero _
  -- Step 3: naturality of the Tate duality `dualE`
  have hnat_z : (Work.SSGRoute.dualE p G (Work.SSGRoute.DualMod p S₂))
        (Work.Tate.Hm2Map fT.dualMap.dualMap.toAddMonoidHom hgg y) z
      = L (Work.GroupCohomology.mapH1 G fT.dualMap.toAddMonoidHom hfT' z) := by
    rw [Hm2Map_proof_irrel (G := G) (A := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S))
      (B := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p S₂))
      fT.dualMap.dualMap.toAddMonoidHom hgg (fun g w => by
        show fT.dualMap.dualMap (g • w) = g • fT.dualMap.dualMap w
        ext m
        simp only [LinearMap.dualMap_apply, Work.SSGRoute.DualMod.dualSMul_apply, hfT'])]
    rw [DFunLike.congr_fun (Work.SSGRoute.dualE_natural p G (Work.SSGRoute.DualMod p S₂)
      (Work.SSGRoute.DualMod p S) fT.dualMap hfT' y) z]
    rw [show (Work.SSGRoute.dualE p G (Work.SSGRoute.DualMod p S)) y = L from
      AddEquiv.apply_symm_apply _ _]
    rfl
  rw [← hnat_z, hy0]
  simp

theorem sha2_image_of_Hm2_of_dualControl (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hctrl : ∃ l : Work.SSGRoute.Sha1 p k Ω K (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p]
        ZMod p,
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
          f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)) (e : E) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t)),
        l.comp (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) f' hf') = 0 →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ))) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  classical
  -- Step 1: extend `l` to a functional `L` on all of `H¹(Gal(K/k), M)`, `M = DualMod p (E ⊗ T)`.
  obtain ⟨l, hl⟩ := hctrl
  obtain ⟨instH1, hP2⟩ := exists_linearMap_extend_sha1Descent (p := p) k Ω K
    (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) l
  letI := instH1
  obtain ⟨L, hL⟩ := hP2
  -- Step 2: the element `x ∈ Ĥ⁻²(G, E ⊗ T)` dual to `L` (Tate duality + naturality).
  obtain ⟨x, hx⟩ := hm2_of_dualFunctional_exists (p := p) (K ≃ₐ[k] K)
    (E ⊗[ZMod p] T) L.toAddMonoidHom
  refine ⟨x, ?_⟩
  intro E₂ _ _ _ _ _ f hf h0
  -- Step 3: the `G`-equivariance of `f ⊗ id` and of its transpose.
  have hfT : ∀ (g : K ≃ₐ[k] K) (z : E ⊗[ZMod p] T),
      (f.rTensor T) (g • z) = g • (f.rTensor T) z :=
    fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z
  have hfT' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
      (f.rTensor T).dualMap (g • φ) = g • (f.rTensor T).dualMap φ :=
    dualMap_equiv p (f.rTensor T) hfT
  have hzero := hx (E₂ ⊗[ZMod p] T) (f.rTensor T) hfT hfT' h0
  -- Step 4: `l ∘ Sha1Map (f ⊗ id)^∨ = 0`, so that the dual control hypothesis applies.
  refine hl E₂ f hf (f.rTensor T).dualMap hfT' ?_ ?_
  · intro φ e t
    rfl
  · apply LinearMap.ext
    intro a
    have hkey : l (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
        (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) (f.rTensor T).dualMap hfT' a) = 0 := by
      -- `l = L ∘ (Hasse descent)` and the descent is natural.
      rw [← hL (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) (f.rTensor T).dualMap hfT' a)]
      simp only [AddMonoidHom.coe_toZModLinearMap]
      rw [Work.SSGRoute.sha1DescentHom_natural p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
        (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) (f.rTensor T).dualMap hfT' a]
      exact hzero _
    exact hkey


end Work.SSGRoute
