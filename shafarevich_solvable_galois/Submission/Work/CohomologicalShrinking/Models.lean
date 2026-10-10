import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.CohomologicalShrinking.Shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v

variable {p : ℕ}

/-! ## The left regular action of `G` on `𝔽_p[G]` -/

/-- The left regular action of `G` on its group algebra `𝔽_p[G]`. -/
noncomputable instance instSMulMonoidAlgebra (p : ℕ) (G : Type*) [Group G] :
    SMul G (MonoidAlgebra (ZMod p) G) where
  smul g x := MonoidAlgebra.single g 1 * x

@[simp] theorem smul_monoidAlgebra (p : ℕ) (G : Type*) [Group G] (g : G)
    (x : MonoidAlgebra (ZMod p) G) : g • x = MonoidAlgebra.single g 1 * x := rfl

noncomputable instance instDistribMulActionMonoidAlgebra (p : ℕ) (G : Type*) [Group G] :
    DistribMulAction G (MonoidAlgebra (ZMod p) G) where
  one_smul x := by rw [smul_monoidAlgebra, ← MonoidAlgebra.one_def, one_mul]
  mul_smul g h x := by
    rw [smul_monoidAlgebra, smul_monoidAlgebra, smul_monoidAlgebra, ← mul_assoc,
      MonoidAlgebra.single_mul_single, mul_one]
  smul_zero g := by rw [smul_monoidAlgebra, mul_zero]
  smul_add g x y := by simp only [smul_monoidAlgebra, mul_add]

noncomputable instance instSMulCommClassMonoidAlgebra (p : ℕ) (G : Type*) [Group G] :
    SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) G) where
  smul_comm g c x := by
    simp only [smul_monoidAlgebra, Algebra.smul_def]
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes c (MonoidAlgebra.single g 1)]

/-! ## The augmentation ideal `I_G` -/

/-- The augmentation ideal `I_G ⊆ 𝔽_p[G]`, the span of the elements `g - 1`.  It is the
paper's `A_{-2} = I_G`. -/
noncomputable def augIdeal (p : ℕ) (G : Type*) [Group G] :
    Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Submodule.span (ZMod p) (Set.range fun g : G => MonoidAlgebra.single g (1 : ZMod p) - 1)

theorem subset_augIdeal (p : ℕ) (G : Type*) [Group G] (g : G) :
    MonoidAlgebra.single g (1 : ZMod p) - 1 ∈ augIdeal p G :=
  Submodule.subset_span ⟨g, rfl⟩

/-- The augmentation ideal is stable under the left regular action of `G`. -/
theorem smul_mem_augIdeal (p : ℕ) (G : Type*) [Group G] (g : G)
    {x : MonoidAlgebra (ZMod p) G} (hx : x ∈ augIdeal p G) : g • x ∈ augIdeal p G := by
  have hgen : ∀ h : G, g • (MonoidAlgebra.single h 1 - 1) ∈ augIdeal p G := by
    intro h
    rw [smul_monoidAlgebra, mul_sub, MonoidAlgebra.single_mul_single, mul_one, mul_one]
    rw [show MonoidAlgebra.single (g * h) (1 : ZMod p) - MonoidAlgebra.single g 1
        = (MonoidAlgebra.single (g * h) 1 - 1) - (MonoidAlgebra.single g 1 - 1) from by
      abel]
    exact Submodule.sub_mem _ (subset_augIdeal p G (g * h)) (subset_augIdeal p G g)
  have hsub : augIdeal p G ≤
      Submodule.comap (Work.Shrinking.actLinear (p := p) (G := G) g) (augIdeal p G) := by
    rw [augIdeal, Submodule.span_le]
    rintro y ⟨h, rfl⟩
    exact hgen h
  exact hsub hx

/-! ## `I_G` as an `𝔽_p[G]`-module -/

/-- The action of `G` on the augmentation ideal `I_G`. -/
noncomputable instance instSMulAugIdeal (p : ℕ) (G : Type*) [Group G] : SMul G (augIdeal p G) where
  smul g x := ⟨g • (x : MonoidAlgebra (ZMod p) G), smul_mem_augIdeal p G g x.2⟩

@[simp] theorem coe_smul_augIdeal (p : ℕ) (G : Type*) [Group G] (g : G) (x : augIdeal p G) :
    ((g • x : augIdeal p G) : MonoidAlgebra (ZMod p) G) = g • (x : MonoidAlgebra (ZMod p) G) :=
  rfl

noncomputable instance instDistribMulActionAugIdeal (p : ℕ) (G : Type*) [Group G] :
    DistribMulAction G (augIdeal p G) where
  one_smul x := Subtype.ext (by
    rw [coe_smul_augIdeal]
    exact one_smul G (x : MonoidAlgebra (ZMod p) G))
  mul_smul g h x := Subtype.ext (by
    rw [coe_smul_augIdeal, coe_smul_augIdeal, coe_smul_augIdeal]
    exact mul_smul g h (x : MonoidAlgebra (ZMod p) G))
  smul_zero g := Subtype.ext (by
    rw [coe_smul_augIdeal, show ((0 : augIdeal p G) : MonoidAlgebra (ZMod p) G) = 0 from rfl]
    exact smul_zero g)
  smul_add g x y := Subtype.ext (by
    rw [coe_smul_augIdeal,
      show ((x + y : augIdeal p G) : MonoidAlgebra (ZMod p) G)
        = (x : MonoidAlgebra (ZMod p) G) + (y : MonoidAlgebra (ZMod p) G) from rfl,
      show ((g • x + g • y : augIdeal p G) : MonoidAlgebra (ZMod p) G)
        = ((g • x : augIdeal p G) : MonoidAlgebra (ZMod p) G)
          + ((g • y : augIdeal p G) : MonoidAlgebra (ZMod p) G) from rfl,
      coe_smul_augIdeal, coe_smul_augIdeal]
    exact smul_add g (x : MonoidAlgebra (ZMod p) G) (y : MonoidAlgebra (ZMod p) G))

instance instSMulCommClassAugIdeal (p : ℕ) (G : Type*) [Group G] :
    SMulCommClass G (ZMod p) (augIdeal p G) where
  smul_comm g c x := Subtype.ext (by
    rw [coe_smul_augIdeal]
    exact smul_comm g c (x : MonoidAlgebra (ZMod p) G))

/-- The augmentation ideal is a finitely generated `𝔽_p[G]`-module (for `G` finite). -/
theorem moduleFinite_augIdeal (p : ℕ) (G : Type*) [Group G] [Fintype G] :
    Module.Finite (ZMod p) (augIdeal p G) := by
  rw [Module.Finite.iff_fg]
  exact Submodule.fg_span (Set.finite_range _)

/-! ## The dual `I_G^{-1}` and the paper's `A₂ = I_G^{-3}` -/

/-- The `𝔽_p`-dual `I_G^{-1} = Hom(I_G, 𝔽_p)` of the augmentation ideal. -/
noncomputable abbrev igDual (p : ℕ) (G : Type*) [Group G] : Type _ :=
  (augIdeal p G) →ₗ[ZMod p] ZMod p

/-- The dual action of `G` on `I_G^{-1}`, `(g • f)(x) = f(g⁻¹ • x)`. -/
noncomputable instance instSMulIgDual (p : ℕ) (G : Type*) [Group G] : SMul G (igDual p G) where
  smul g f := f.comp (Work.Shrinking.actLinear (p := p) (G := G) g⁻¹)

@[simp] theorem smul_igDual_apply (p : ℕ) (G : Type*) [Group G] (g : G) (f : igDual p G)
    (x : augIdeal p G) : (g • f) x = f (g⁻¹ • x) := by
  show (f.comp (Work.Shrinking.actLinear (p := p) (G := G) g⁻¹)) x = f (g⁻¹ • x)
  rw [LinearMap.comp_apply, Work.Shrinking.actLinear_apply]

noncomputable instance instDistribMulActionIgDual (p : ℕ) (G : Type*) [Group G] :
    DistribMulAction G (igDual p G) where
  one_smul f := by
    refine LinearMap.ext fun x => ?_
    rw [smul_igDual_apply]
    simp
  mul_smul g h f := by
    refine LinearMap.ext fun x => ?_
    rw [smul_igDual_apply, smul_igDual_apply, smul_igDual_apply, mul_inv_rev, mul_smul]
  smul_zero g := by
    refine LinearMap.ext fun x => ?_
    simp [smul_igDual_apply]
  smul_add g f f' := by
    refine LinearMap.ext fun x => ?_
    simp [smul_igDual_apply]

instance instSMulCommClassIgDual (p : ℕ) (G : Type*) [Group G] :
    SMulCommClass G (ZMod p) (igDual p G) where
  smul_comm g c f := by
    refine LinearMap.ext fun x => ?_
    rw [smul_igDual_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_igDual_apply]

/-- The paper's `A₂ = I_G^{-3}`, modelled as the third tensor power of the dual `I_G^{-1}`
(canonically isomorphic to `Hom_{𝔽_p}(I_G^3, 𝔽_p)` when `I_G` is finite dimensional).

This is a plain `def`, *not* an `abbrev`: the instances below are then found by type class search
without unfolding the nested tensor power, which is both slow and fragile.  The equation
`A2 p G = ⨂[ZMod p]^3 (igDual p G)` holds definitionally, so `A2` can always be unfolded by
hand (`show`, `change`, `rw [show A2 p G = _ from rfl]`). -/
noncomputable def A2 (p : ℕ) (G : Type*) [Group G] : Type _ := ⨂[ZMod p]^3 (igDual p G)

noncomputable instance instAddCommGroupA2 (p : ℕ) (G : Type*) [Group G] :
    AddCommGroup (A2 p G) :=
  inferInstanceAs (AddCommGroup (⨂[ZMod p]^3 (igDual p G)))

noncomputable instance instModuleA2 (p : ℕ) (G : Type*) [Group G] : Module (ZMod p) (A2 p G) :=
  inferInstanceAs (Module (ZMod p) (⨂[ZMod p]^3 (igDual p G)))

noncomputable instance instDistribMulActionA2 (p : ℕ) (G : Type*) [Group G] :
    DistribMulAction G (A2 p G) :=
  inferInstanceAs (DistribMulAction G (⨂[ZMod p]^3 (igDual p G)))

noncomputable instance instSMulCommClassA2 (p : ℕ) (G : Type*) [Group G] :
    SMulCommClass G (ZMod p) (A2 p G) :=
  inferInstanceAs (SMulCommClass G (ZMod p) (⨂[ZMod p]^3 (igDual p G)))

theorem moduleFinite_igDual (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] :
    Module.Finite (ZMod p) (igDual p G) :=
  haveI := moduleFinite_augIdeal p G
  Module.Finite.linearMap (ZMod p) (ZMod p) (augIdeal p G) (ZMod p)

/-- `A₂` is a finitely generated `𝔽_p`-module when `G` is finite. -/
theorem moduleFinite_A2 (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] :
    Module.Finite (ZMod p) (A2 p G) := by
  haveI := moduleFinite_igDual p G
  exact inferInstanceAs (Module.Finite (ZMod p) (⨂[ZMod p]^3 (igDual p G)))

/-! ## The cases `k = -2` and `k = 2` of Proposition 6 in these models -/

/-- **Proposition 6, case `k = -2`** (`= H₁`), in the paper's model
`Ĥ⁻²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A_{-2})` with `A_{-2} = I_G`:

for `G` finite, `p` prime, `τ = (i,j)` with `j ≥ 1`, `T` a f.g. `𝔽_p[G]`-module, `t ∈ ℕ` and
`n ≥ 1`, there is `r₀` such that for all `r ≥ r₀` and all
`x : Fin t → Ĥ⁻¹(G, E(r·n,τ) ⊗ (T ⊗ I_G))` there is a surjective `G`-equivariant
`Φ : F(r·n) → F(n)` killing all the classes.

This is Proposition 6 of Schmidt–Wingberg for `k = -2` (the case used in the proof of
Proposition 7 and in step 4 of Theorem 15), obtained from the case `k = -1` exactly as the paper
does, by "since `T` was arbitrary we may restrict to `k = -1`" with `T` replaced by
`T ⊗ I_G`.  **Unconditional** apart from `Prop5Data` (Proposition 5). -/
theorem exists_shrinking_Hm2IG_of_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ∀ x : Fin t → Work.Tate.Hm1 G
        (E p G (r * n) i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t,
        (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)) (x k) = 0 := by
  haveI := moduleFinite_augIdeal p G
  exact exists_shrinking_Hm1_of_mult (p := p) G hj D (T ⊗[ZMod p] augIdeal p G) t hn

/-- **Proposition 6, case `k = 2`**, in the paper's model
`Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` with `A₂ = I_G^{-3}`:

for `G` finite, `p` prime, `τ = (i,j)` with `j ≥ 1`, `T` a f.g. `𝔽_p[G]`-module, `t ∈ ℕ` and
`n ≥ 1`, there is `r₀` such that for all `r ≥ r₀` and all
`x : Fin t → Ĥ⁻¹(G, E(r·n,τ) ⊗ (T ⊗ A₂))` there is a surjective `G`-equivariant
`Φ : F(r·n) → F(n)` killing all the classes.

This is the case `k = 2` of Proposition 6 — the one used in steps 1 and 3 of the proof of
Theorem 15 (with `T = Ind_{G_p}^G 𝔽_p`, resp. a general `T`) — written in the paper's model of
`Ĥ²` given by the dimension shift `A₂ = I_G^{-3}`.  **Unconditional** apart from `Prop5Data`. -/
theorem exists_shrinking_H2IG_of_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ∀ x : Fin t → Work.Tate.Hm1 G
        (E p G (r * n) i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G)),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t,
        (Φ.hm1Map p G (T ⊗[ZMod p] A2 p G)) (x k) = 0 := by
  haveI := moduleFinite_A2 p G
  exact exists_shrinking_Hm1_of_mult (p := p) G hj D (T ⊗[ZMod p] A2 p G) t hn

end Work.CohomologicalShrinking
