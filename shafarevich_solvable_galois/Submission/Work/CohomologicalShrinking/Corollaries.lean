import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.TensorProduct.Finite
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.GroupCohomology.ConnectingLift
import Submission.Work.GroupCohomology.CyclicTriv
import Submission.Work.GroupCohomology.Shapiro
import Submission.Work.GroupCohomology.TrivialGroup
import Submission.Work.GroupCohomology.Vanishing
import Submission.Work.Tate.CoindUp
import Submission.Work.Tate.ker_deltaH1_eq_range_mapH1
import Submission.Work.Tate.range_deltaH1_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-! ## The induced maps in the coefficient modules `E(m,τ) ⊗ N` and `E(m,τ) ⊗ T` -/

/-- The map induced by an operator map on `Ĥ⁻²(G, E(m,τ) ⊗ T) = Ĥ⁻¹(G, E(m,τ) ⊗ T)` in the
`coindUp` model of `Ĥ⁻²`. -/
noncomputable def OperatorMap.hm2Map (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] {m n : ℕ} (Φ : OperatorMap G m n) :
    Work.Tate.Hm2 G (E p G m i j ⊗[ZMod p] T) →+
      Work.Tate.Hm2 G (E p G n i j ⊗[ZMod p] T) :=
  Work.Tate.Hm2Map ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
    (fun g z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g z)

/-- The map induced by an operator map on `Ĥ²(G, E(m,τ) ⊗ T)`. -/
noncomputable def OperatorMap.h2Map (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] {m n : ℕ} (Φ : OperatorMap G m n) :
    GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T) →+
      GroupCohomology.H2 G (E p G n i j ⊗[ZMod p] T) :=
  GroupCohomology.mapH2 G ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
    (fun g z => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g z)

/-! ## The case `k = -2` -/

/-- **Proposition 6 of Schmidt–Wingberg, case `k = -2`** (i.e. the homology group `H₁`).

Let `T` be a finitely generated `𝔽_p[G]`-module, `τ = (i,j)` with `j ≥ 1` and `n ≥ 1`.  Then
there is `r₀` with: for all `r ≥ r₀` and all `x₁, …, x_t ∈ Ĥ⁻²(G, E(r·n,τ) ⊗ T)` there is a
surjective `G`-equivariant homomorphism `Φ : F(r·n) → F(n)` of free `G`-operator groups
killing all the `x_i`.

The dimension-shifting isomorphism `Ĥ⁻²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A_{-2})` (the paper's
`A_{-2} = I_G`) is taken as the explicit hypothesis `shift`, together with its compatibility
`hshift` with operator maps; for `A` one takes the `I_G`-twist of `G`-modules.  See `NOTES.md`. -/
theorem exists_shrinking_Hm2_of_shift_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [Module.Finite (ZMod p) A]
    (shift : ∀ m : ℕ, Work.Tate.Hm2 G (E p G m i j ⊗[ZMod p] T) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A)))
    (hshift : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
      (Φ.hm1Map p G (T ⊗[ZMod p] A)).comp (shift m).toAddMonoidHom
        = (shift n).toAddMonoidHom.comp (Φ.hm2Map p G T))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ x : Fin t → Work.Tate.Hm2 G (E p G (r * n) i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t, Φ.hm2Map p G T (x k) = 0 := by
  classical
  haveI : Module.Finite (ZMod p) (T ⊗[ZMod p] A) := inferInstance
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_Hm1_of_mult (p := p) G hj D (T ⊗[ZMod p] A) t hn
  refine ⟨r₀, fun r hr x => ?_⟩
  obtain ⟨Φ, hΦ⟩ := hr₀ r hr (fun k => shift (r * n) (x k))
  refine ⟨Φ, fun k => ?_⟩
  have h := hΦ k
  have h2 : (shift n) (Φ.hm2Map p G T (x k)) = 0 := by
    show ((shift n).toAddMonoidHom.comp (Φ.hm2Map p G T)) (x k) = 0
    rw [← hshift Φ, AddMonoidHom.comp_apply]
    exact h
  exact (shift n).injective (by rw [h2, map_zero])

/-! ## The case `k = 2` -/

/-- **Proposition 6 of Schmidt–Wingberg, case `k = 2`** — the case used in step 1 of the proof
of Theorem 15 (with `G` a decomposition group of the global field and `T` an induced module).

As in the `k = -2` case, the dimension-shifting isomorphism
`Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` (the paper's `A₂ = I_G^{-3}`) is an explicit hypothesis, together
with its compatibility with operator maps.  See `NOTES.md`. -/
theorem exists_shrinking_H2_of_shift_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [Module.Finite (ZMod p) A]
    (shift : ∀ m : ℕ, GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A)))
    (hshift : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
      (Φ.hm1Map p G (T ⊗[ZMod p] A)).comp (shift m).toAddMonoidHom
        = (shift n).toAddMonoidHom.comp (Φ.h2Map p G T))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ x : Fin t → GroupCohomology.H2 G (E p G (r * n) i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t, Φ.h2Map p G T (x k) = 0 := by
  classical
  haveI : Module.Finite (ZMod p) (T ⊗[ZMod p] A) := inferInstance
  obtain ⟨r₀, hr₀⟩ := exists_shrinking_Hm1_of_mult (p := p) G hj D (T ⊗[ZMod p] A) t hn
  refine ⟨r₀, fun r hr x => ?_⟩
  obtain ⟨Φ, hΦ⟩ := hr₀ r hr (fun k => shift (r * n) (x k))
  refine ⟨Φ, fun k => ?_⟩
  have h := hΦ k
  have h2 : (shift n) (Φ.h2Map p G T (x k)) = 0 := by
    show ((shift n).toAddMonoidHom.comp (Φ.h2Map p G T)) (x k) = 0
    rw [← hshift Φ, AddMonoidHom.comp_apply]
    exact h
  exact (shift n).injective (by rw [h2, map_zero])

end Work.CohomologicalShrinking
