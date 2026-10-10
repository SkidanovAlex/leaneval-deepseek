import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Finiteness.Defs
import Submission.Work.CohomologicalShrinking.coindUpAddEquivTensor

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-! ## The associator and the diagonal action -/

/-- `actLinear` on a tensor product is the tensor product of the `actLinear`s. -/
theorem actLinear_tensor (p : ℕ) {G M N : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (γ : G) :
    Work.Shrinking.actLinear (p := p) (M := M ⊗[ZMod p] N) γ
      = TensorProduct.map (Work.Shrinking.actLinear (p := p) (M := M) γ)
          (Work.Shrinking.actLinear (p := p) (M := N) γ) := by
  refine LinearMap.ext fun x => ?_
  exact Work.Shrinking.diagTensor_smul_def (p := p) (M := M) (N := N) γ x

/-- The associator is equivariant for the diagonal `G`-action. -/
theorem tensorAssoc_smul (p : ℕ) {G M N P : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [AddCommGroup P] [Module (ZMod p) P] [DistribMulAction G P] [SMulCommClass G (ZMod p) P]
    (γ : G) (z : (M ⊗[ZMod p] N) ⊗[ZMod p] P) :
    TensorProduct.assoc (ZMod p) M N P (γ • z) = γ • TensorProduct.assoc (ZMod p) M N P z := by
  have h3 : TensorProduct.map (Work.Shrinking.actLinear (p := p) (M := M) γ)
        (TensorProduct.map (Work.Shrinking.actLinear (p := p) (M := N) γ)
          (Work.Shrinking.actLinear (p := p) (M := P) γ))
      = Work.Shrinking.actLinear (p := p) (M := M ⊗[ZMod p] (N ⊗[ZMod p] P)) γ := by
    rw [← actLinear_tensor (p := p) (M := N) (N := P) γ,
      ← actLinear_tensor (p := p) (M := M) (N := N ⊗[ZMod p] P) γ]
  rw [Work.Shrinking.diagTensor_smul_def (p := p) (M := M ⊗[ZMod p] N) (N := P) γ z,
    actLinear_tensor (p := p) (M := M) (N := N) γ,
    ← TensorProduct.map_map_assoc (Work.Shrinking.actLinear (p := p) (M := M) γ)
      (Work.Shrinking.actLinear (p := p) (M := N) γ)
      (Work.Shrinking.actLinear (p := p) (M := P) γ) z, h3]
  rfl

/-- Naturality of the associator, in the form used below: tensoring a linear map with the
identity on both `N` and `P` commutes with the associator. -/
theorem map_assoc_map (p : ℕ) {M N P Q : Type*}
    [AddCommGroup M] [Module (ZMod p) M] [AddCommGroup N] [Module (ZMod p) N]
    [AddCommGroup P] [Module (ZMod p) P] [AddCommGroup Q] [Module (ZMod p) Q]
    (f : M →ₗ[ZMod p] Q) (z : (M ⊗[ZMod p] N) ⊗[ZMod p] P) :
    (f.rTensor (N ⊗[ZMod p] P)) (TensorProduct.assoc (ZMod p) M N P z)
      = TensorProduct.assoc (ZMod p) Q N P ((f.rTensor N).rTensor P z) := by
  simpa only [LinearMap.rTensor_def, TensorProduct.map_id] using
    TensorProduct.map_map_assoc f (LinearMap.id : N →ₗ[ZMod p] N)
      (LinearMap.id : P →ₗ[ZMod p] P) z

/-- The map `coindUpMap f hf` does not depend on the (proof-valued) equivariance witness. -/
theorem coindUpMap_proof_irrel {G : Type*} {A B : Type*} [Group G] [Fintype G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf hf' : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (x : Work.Tate.coindUp G A) :
    Work.Tate.coindUpMap f hf x = Work.Tate.coindUpMap f hf' x := by
  rw [Subsingleton.elim hf hf']

section Hm2Tate

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
variable {i j : ℕ}
variable (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
  [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]

/-- The isomorphism `Ĥ⁻²(G, E(m,τ) ⊗ T) ≅ Ĥ⁻¹(G, E(m,τ) ⊗ (T ⊗ I_G))` induced by a family of
`G`-equivariant isomorphisms `es m : (E(m,τ) ⊗ T)^♯ ≅ E(m,τ) ⊗ (T ⊗ I_G)`. -/
noncomputable abbrev hm2Shift
    (es : ∀ m : ℕ, Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T) ≃+
        E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
    (es_smul : ∀ (m : ℕ) (γ : G) (x : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
        (es m).toAddMonoidHom (γ • x) = γ • (es m).toAddMonoidHom x)
    (m : ℕ) :
    Work.Tate.Hm2 G (E p G m i j ⊗[ZMod p] T) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) :=
  Work.Tate.Hm1Equiv (es m).toAddMonoidHom (es_smul m) (es m).bijective

/-- The shrinking map commutes with the dimension shift. -/
theorem hm2Shift_hshift
    (es : ∀ m : ℕ, Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T) ≃+
        E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
    (es_smul : ∀ (m : ℕ) (γ : G) (x : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
        (es m).toAddMonoidHom (γ • x) = γ • (es m).toAddMonoidHom x)
    (es_nat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
        (x : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
        es n ((Work.Tate.coindUpMap
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom
            (fun γ z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
              (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ z)) x)
          = ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
              (es m x))
    ⦃m n : ℕ⦄ (Φ : OperatorMap G m n) :
    (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)).comp
        (hm2Shift p G T es es_smul m).toAddMonoidHom
      = (hm2Shift p G T es es_smul n).toAddMonoidHom.comp (Φ.hm2Map p G T) := by
  have hφTI : ∀ (g : G) (a : E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)),
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G) :
        (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))) (g • a)
        = g • ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor
            (T ⊗[ZMod p] augIdeal p G) :
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
            (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))) a :=
    fun g a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g a
  have hc : ∀ (g : G) (a : E p G m i j ⊗[ZMod p] T),
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) (g • a)
        = g • ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) a :=
    fun g a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g a
  have hfe1 : ∀ (g : G) (a : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
      (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G) :
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
            (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))).comp
        (es m).toAddMonoidHom) (g • a)
        = g • (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G) :
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
            (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))).comp
          (es m).toAddMonoidHom) a := by
    intro g a
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, es_smul m g a]
    exact hφTI g ((es m).toAddMonoidHom a)
  have hfe2 : ∀ (g : G) (a : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
      ((es n).toAddMonoidHom.comp
        (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) hc)) (g • a)
        = g • ((es n).toAddMonoidHom.comp
          (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
            (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) hc)) a := by
    intro g a
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      Work.Tate.coindUpMap_equiv _ hc,
      es_smul n g (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) hc a)]
  show (Work.Tate.Hm1Map G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G) :
            (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
              (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)))
          hφTI).comp
        (Work.Tate.Hm1Map G (Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          (es m).toAddMonoidHom (es_smul m))
      = (Work.Tate.Hm1Map G (Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          (es n).toAddMonoidHom (es_smul n)).comp
        (Work.Tate.Hm1Map G (Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
          (Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
          (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
            (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) hc)
          (Work.Tate.coindUpMap_equiv _ hc))
  refine (Work.CohomologicalShrinking.tate.Hm1Map_comp (es m).toAddMonoidHom (es_smul m)
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G) :
        (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) →+
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))) hφTI hfe1).symm.trans
    ((Work.CohomologicalShrinking.operator.Hm1Map_congr _ _ (by
        ext x
        exact (es_nat Φ x).symm)).trans
      (Work.CohomologicalShrinking.tate.Hm1Map_comp
        (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) hc)
        (Work.Tate.coindUpMap_equiv _ hc) (es n).toAddMonoidHom (es_smul n) hfe2))

/-- **The shrinking lemma in degree `-2` for `Work.Tate.Hm2`**, given a family of dimension
shifting isomorphisms `(E(m,τ) ⊗ T)^♯ ≅ E(m,τ) ⊗ (T ⊗ I_G)` (natural in `E(m,τ)`). -/
theorem exists_shrinking_Hm2_tate_of_data
    (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (es : ∀ m : ℕ, Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T) ≃+
        E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
    (es_smul : ∀ (m : ℕ) (γ : G) (x : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
        (es m).toAddMonoidHom (γ • x) = γ • (es m).toAddMonoidHom x)
    (es_nat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
        (x : Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
        es n ((Work.Tate.coindUpMap
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom
            (fun γ z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
              (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ z)) x)
          = ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
              (es m x))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm2 G
        (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T),
      ∃ Φ : Work.CohomologicalShrinking.OperatorMap G m n, ∀ k : Fin t,
        Work.CohomologicalShrinking.OperatorMap.hm2Map p G T Φ (x k) = 0 := by
  haveI : Module.Finite (ZMod p) (augIdeal p G) := moduleFinite_augIdeal p G
  exact exists_shrinking_Hm2_of_shift p G hj D T (augIdeal p G)
    (fun m => hm2Shift p G T es es_smul m)
    (fun m n Φ => hm2Shift_hshift p G T es es_smul es_nat Φ) t hn

end Hm2Tate

/-! ## The dimension shift from `Work.CohomologicalShrinking.coindUpAddEquivTensor` -/

theorem exists_shrinking_Hm2_tate (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Work.CohomologicalShrinking.Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm2 G
        (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T),
      ∃ Φ : Work.CohomologicalShrinking.OperatorMap G m n, ∀ k : Fin t,
        Work.CohomologicalShrinking.OperatorMap.hm2Map p G T Φ (x k) = 0 := by
  obtain ⟨e, he_smul, he_nat⟩ := coindUpAddEquivTensor (p := p) (G := G)
  refine exists_shrinking_Hm2_tate_of_data p G T hj D ?es ?es_smul ?es_nat t hn
  case es =>
    intro m
    exact (e (E p G m i j ⊗[ZMod p] T)).trans
      (TensorProduct.assoc (ZMod p) (E p G m i j) T (augIdeal p G)).toAddEquiv
  case es_smul =>
    intro m γ x
    show TensorProduct.assoc (ZMod p) (E p G m i j) T (augIdeal p G)
          ((e (E p G m i j ⊗[ZMod p] T)) (γ • x))
        = γ • TensorProduct.assoc (ZMod p) (E p G m i j) T (augIdeal p G)
          ((e (E p G m i j ⊗[ZMod p] T)) x)
    rw [he_smul (E p G m i j ⊗[ZMod p] T) γ x]
    exact tensorAssoc_smul p γ ((e (E p G m i j ⊗[ZMod p] T)) x)
  case es_nat =>
    intro m n Φ x
    have hn' := DFunLike.congr_fun (he_nat (E p G m i j ⊗[ZMod p] T)
      (E p G n i j ⊗[ZMod p] T) ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
      (fun γ z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
        (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ z)) x
    change TensorProduct.assoc (ZMod p) (E p G n i j) T (augIdeal p G)
          ((e (E p G n i j ⊗[ZMod p] T))
            ((Work.Tate.coindUpMap
              ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom
              (fun γ z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
                (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ z)) x))
        = ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
          (TensorProduct.assoc (ZMod p) (E p G m i j) T (augIdeal p G)
            ((e (E p G m i j ⊗[ZMod p] T)) x))
    rw [map_assoc_map p (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (z := (e (E p G m i j ⊗[ZMod p] T)) x)]
    exact congrArg (fun z => (TensorProduct.assoc (ZMod p) (E p G n i j) T
      (augIdeal p G)) z) hn'

end Work.CohomologicalShrinking
