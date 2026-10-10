import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for finite-group Tate duality in degree `0`

This file sets up the `𝔽_p`-linear-algebra vocabulary needed for the Tate duality
`Ĥ⁻¹(G, A) ≅ Ĥ⁰(G, A^∨)^∨` in the models of `Submission/Work/Tate`, where
`A^∨ = Work.SSGRoute.DualMod p A = Hom(A, 𝔽_p)` carries the dual action
`(g • φ) a = φ (g⁻¹ • a)`.

The point of the file is that all the objects of the statement are *definitionally*
the corresponding subspaces of `A` and of `A^∨`:

* `normLin p G A` is the norm `N a = ∑ g, g • a` as an `𝔽_p`-linear map;
* `augSub p G A` is the augmentation submodule `I_G · A`, as a submodule of `A`
  (its underlying additive subgroup is `Work.Tate.augmentation G A`, by `rfl`);
* `fixSub p G A` is the submodule `(A^∨)^G` of `G`-fixed functionals (its underlying
  additive subgroup is `Work.Tate.fixedSubgroup G (DualMod p A)`, by `rfl`);
* `V0 p G A` is the image of the dual norm `N_{A^∨}` inside `(A^∨)^G` (its underlying
  additive subgroup is `(Work.Tate.normToFixed G (DualMod p A)).range`, by `rfl`).

Consequently `Work.Tate.Hm1 G A = ↥(K p G A) ⧸ K0 p G A` and
`Work.Tate.H0 G (DualMod p A) = ↥(fixSub p G A) ⧸ V0 p G A` hold by `rfl`, which lets the
linear-algebra argument be run on submodule quotients (where `Module`, `FiniteDimensional`
and `LinearEquiv` are available) and then be transported back for free.

Finally `pairQ p G A : (↥K ⧸ K0) →ₗ (↥fixSub ⧸ V0) →ₗ 𝔽` is the descended evaluation
pairing `⟨a, φ⟩ = φ a`, with computation rule `pairQ_mk`.
-/

namespace Work.SSGRoute.TateDual

open Work.Tate
open scoped BigOperators

variable (p : ℕ) (G : Type) [Group G] [Fintype G] (A : Type) [AddCommGroup A]
  [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]

/-! ## The norm as a linear map -/

/-- The norm `N a = ∑_{g : G} g • a` of a finite group, as an `𝔽_p`-linear map. -/
noncomputable def normLin : A →ₗ[ZMod p] A where
  toFun := Work.Tate.norm G A
  map_add' := map_add (Work.Tate.norm G A)
  map_smul' c a := by
    show (∑ g : G, g • (c • a)) = c • (∑ g : G, g • a)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun g _ => smul_comm g c a)

theorem normLin_apply (a : A) : normLin p G A a = Work.Tate.norm G A a := rfl

/-! ## The augmentation submodule, as a submodule -/

theorem smul_mem_augmentation (c : ZMod p) {x : A} (hx : x ∈ Work.Tate.augmentation G A) :
    c • x ∈ Work.Tate.augmentation G A := by
  refine AddSubgroup.closure_induction
    (k := Set.range fun q : G × A => q.1 • q.2 - q.2)
    (p := fun y _ => c • y ∈ Work.Tate.augmentation G A) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨g, a⟩, rfl⟩
    rw [smul_sub, ← smul_comm g c a]
    exact smul_sub_self_mem_augmentation g (c • a)
  · simp
  · intro y z _ _ hy hz
    rw [smul_add]
    exact AddSubgroup.add_mem _ hy hz
  · intro y _ hy
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ hy

/-- The augmentation submodule `I_G · A = Work.Tate.augmentation G A`, as a submodule of `A`. -/
noncomputable def augSub : Submodule (ZMod p) A where
  carrier := ↑(Work.Tate.augmentation G A)
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' := fun c x hx => smul_mem_augmentation p G A c hx

theorem augSub_toAddSubgroup :
    (augSub p G A).toAddSubgroup = Work.Tate.augmentation G A := rfl

theorem mem_augSub {x : A} :
    x ∈ augSub p G A ↔ x ∈ Work.Tate.augmentation G A := Iff.rfl

/-! ## The submodule of fixed functionals -/

/-- The `G`-fixed functionals `(A^∨)^G`, as a submodule of `A^∨ = DualMod p A`. -/
noncomputable def fixSub : Submodule (ZMod p) (Work.SSGRoute.DualMod p A) where
  carrier := ↑(Work.Tate.fixedSubgroup G (Work.SSGRoute.DualMod p A))
  add_mem' := fun {a b} ha hb g => by rw [smul_add, ha g, hb g]
  zero_mem' := fun g => by simp
  smul_mem' := fun c x hx g => by rw [smul_comm g c x, hx g]

theorem fixSub_toAddSubgroup :
    (fixSub p G A).toAddSubgroup = Work.Tate.fixedSubgroup G (Work.SSGRoute.DualMod p A) :=
  rfl

theorem mem_fixSub {φ : Work.SSGRoute.DualMod p A} :
    φ ∈ fixSub p G A ↔ ∀ g : G, g • φ = φ :=
  Work.Tate.mem_fixedSubgroup

/-! ## The dual norm -/

/-- The norm on the dual module `A^∨`, as an `𝔽_p`-linear map. -/
noncomputable def dualNormLin :
    Work.SSGRoute.DualMod p A →ₗ[ZMod p] Work.SSGRoute.DualMod p A :=
  normLin p G (Work.SSGRoute.DualMod p A)

theorem dualNormLin_apply (ψ : Work.SSGRoute.DualMod p A) :
    dualNormLin p G A ψ = Work.Tate.norm G (Work.SSGRoute.DualMod p A) ψ := rfl

/-- Self-adjointness of the norm: `⟨N a, ψ⟩ = ⟨a, N ψ⟩`. -/
theorem dualNormLin_apply_eq (ψ : Work.SSGRoute.DualMod p A) (a : A) :
    (dualNormLin p G A ψ) a = ψ (normLin p G A a) := by
  have h1 : (dualNormLin p G A ψ) a = ∑ g : G, ψ (g⁻¹ • a) := by
    rw [dualNormLin_apply, Work.Tate.norm_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun g _ => Work.SSGRoute.DualMod.dualSMul_apply p g ψ a)
  have h2 : ψ (normLin p G A a) = ∑ g : G, ψ (g • a) := by
    rw [normLin_apply, Work.Tate.norm_apply, map_sum]
  rw [h1, h2]
  exact Equiv.sum_comp (Equiv.inv G) (fun h : G => ψ (h • a))

/-- The dual norm is the transpose of the norm. -/
theorem dualNormLin_eq_dualMap : dualNormLin p G A = (normLin p G A).dualMap := by
  ext ψ a
  rw [LinearMap.dualMap_apply]
  exact dualNormLin_apply_eq p G A ψ a

/-! ## The two annihilator computations -/

/-- A functional is `G`-fixed if and only if it kills the augmentation submodule. -/
theorem fixSub_eq_dualAnnihilator :
    fixSub p G A = (augSub p G A).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hφ x hx
    refine AddSubgroup.closure_induction
      (k := Set.range fun q : G × A => q.1 • q.2 - q.2)
      (p := fun y _ => (φ : Work.SSGRoute.DualMod p A) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨g, a⟩, rfl⟩
      have h1 : (g⁻¹ • (φ : Work.SSGRoute.DualMod p A)) a = φ (g • a) := by
        rw [Work.SSGRoute.DualMod.dualSMul_apply, inv_inv]
      have h : (φ : Work.SSGRoute.DualMod p A) (g • a) = φ a := by
        rw [← h1, hφ g⁻¹]
      rw [map_sub, h, sub_self]
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, add_zero]
    · intro y _ hy
      rw [map_neg, hy, neg_zero]
  · intro hφ g
    ext a
    rw [Work.SSGRoute.DualMod.dualSMul_apply]
    have h : (φ : Work.SSGRoute.DualMod p A) (g⁻¹ • a - a) = 0 :=
      hφ (g⁻¹ • a - a) (smul_sub_self_mem_augmentation g⁻¹ a)
    rw [map_sub, sub_eq_zero] at h
    exact h

/-- **First annihilator computation**: the double annihilator of the fixed functionals is the
augmentation submodule, i.e. the fixed functionals detect `I_G · A` exactly. -/
theorem fixSub_dualCoannihilator [Fact p.Prime] :
    (fixSub p G A).dualCoannihilator = augSub p G A := by
  rw [fixSub_eq_dualAnnihilator]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq (K := ZMod p) (V := A) (W := augSub p G A)

/-! ## The two spaces of the duality -/

/-- The kernel `ker N_A` of the norm, as a submodule of `A`. -/
noncomputable abbrev K : Submodule (ZMod p) A := (normLin p G A).ker

/-- The image `I_G · A` of the augmentation submodule, inside `ker N_A`. -/
noncomputable abbrev K0 : Submodule (ZMod p) ↥(K p G A) :=
  (augSub p G A).comap (K p G A).subtype

/-- The image `N_{A^∨}(A^∨)` of the dual norm, inside the fixed functionals `(A^∨)^G`. -/
noncomputable def V0 : Submodule (ZMod p) ↥(fixSub p G A) where
  carrier := (↑((Work.Tate.normToFixed G (Work.SSGRoute.DualMod p A)).range) :
      Set ↥(Work.Tate.fixedSubgroup G (Work.SSGRoute.DualMod p A)))
  add_mem' := fun {x y} hx hy => AddSubgroup.add_mem _ hx hy
  zero_mem' := AddSubgroup.zero_mem _
  smul_mem' := by
    intro c x hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨c • a, Subtype.ext ?_⟩
    rw [Work.Tate.normToFixed_apply, Submodule.coe_smul,
      congrArg Subtype.val ha.symm, Work.Tate.normToFixed_apply]
    exact map_smul (dualNormLin p G A) c a

theorem V0_toAddSubgroup :
    (V0 p G A).toAddSubgroup =
      (Work.Tate.normToFixed G (Work.SSGRoute.DualMod p A)).range := rfl

/-- **Second annihilator computation**: the range of the dual norm is the annihilator of the
kernel of the norm. -/
theorem ker_dualAnnihilator_eq_range [Fact p.Prime] :
    (K p G A).dualAnnihilator = (dualNormLin p G A).range := by
  rw [dualNormLin_eq_dualMap]
  exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker (f := normLin p G A)).symm

theorem mem_V0_iff {z : ↥(fixSub p G A)} :
    z ∈ V0 p G A ↔ (z : Work.SSGRoute.DualMod p A) ∈ (dualNormLin p G A).range := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, ?_⟩
    rw [← hψ]
    rfl
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, Subtype.ext ?_⟩
    rw [← hψ]
    rfl

/-- `V0` is the image of the kernel of the norm under the identification
`(A^∨)^G ⊆ A^∨` with the annihilator of `ker N`. -/
theorem mem_V0_iff_dualAnnihilator [Fact p.Prime] {z : ↥(fixSub p G A)} :
    z ∈ V0 p G A ↔ (z : Work.SSGRoute.DualMod p A) ∈ (K p G A).dualAnnihilator := by
  rw [mem_V0_iff, ker_dualAnnihilator_eq_range]

/-! ### Lean v4.35 port: explicit quotient instances

On Lean v4.35 / Mathlib 5e0c4e5, instance search can no longer build `HasQuotient`, `AddCommGroup`
or `Module` for a quotient of a submodule of the linear-map type `DualMod p A = A →ₗ[ZMod p] ZMod p`
(it fails to unify `AddCommGroup.toAddCommMonoid` with `Submodule.addCommMonoid` there). We supply
the standard Mathlib instances explicitly; they are the same terms instance search used to find. -/

noncomputable instance fixSubHasQuotient :
    HasQuotient (↥(fixSub p G A)) (Submodule (ZMod p) ↥(fixSub p G A)) :=
  @Submodule.hasQuotient (ZMod p) ↥(fixSub p G A) _ (Submodule.addCommGroup _) (fixSub p G A).module

noncomputable instance fixSubQuotAddCommGroup : AddCommGroup (↥(fixSub p G A) ⧸ V0 p G A) :=
  @Submodule.Quotient.addCommGroup (ZMod p) ↥(fixSub p G A) _ (Submodule.addCommGroup _)
    (fixSub p G A).module (V0 p G A)

noncomputable instance fixSubQuotModule : Module (ZMod p) (↥(fixSub p G A) ⧸ V0 p G A) :=
  @Submodule.Quotient.module (ZMod p) ↥(fixSub p G A) _ (Submodule.addCommGroup _)
    (fixSub p G A).module (V0 p G A)

theorem H0_eq_quotient :
    Work.Tate.H0 G (Work.SSGRoute.DualMod p A) =
      (↥(fixSub p G A) ⧸ V0 p G A) := rfl

theorem Hm1_eq_quotient :
    Work.Tate.Hm1 G A = (↥(K p G A) ⧸ K0 p G A) := rfl

theorem K0_toAddSubgroup : (K0 p G A).toAddSubgroup = Work.Tate.augInKer G A := rfl

theorem mem_K0_iff {x : ↥(K p G A)} :
    x ∈ K0 p G A ↔ (x : A) ∈ Work.Tate.augmentation G A := Iff.rfl

theorem mem_K_iff {a : A} : a ∈ K p G A ↔ Work.Tate.norm G A a = 0 :=
  LinearMap.mem_ker

/-! ## The descended evaluation pairing -/

/-- The evaluation pairing `⟨a, φ⟩ = φ a` on `ker N_A × (A^∨)^G`. -/
noncomputable def pairP :
    ↥(K p G A) →ₗ[ZMod p] (↥(fixSub p G A) →ₗ[ZMod p] ZMod p) where
  toFun x :=
    { toFun := fun φ => (φ : Work.SSGRoute.DualMod p A) x
      map_add' := fun φ ψ => by
        show ((φ + ψ : ↥(fixSub p G A)) : Work.SSGRoute.DualMod p A) x
          = (φ : Work.SSGRoute.DualMod p A) x + (ψ : Work.SSGRoute.DualMod p A) x
        rw [Submodule.coe_add, LinearMap.add_apply]
      map_smul' := fun c φ => by
        show ((c • φ : ↥(fixSub p G A)) : Work.SSGRoute.DualMod p A) x
          = c • ((φ : Work.SSGRoute.DualMod p A) x)
        rw [Submodule.coe_smul, LinearMap.smul_apply] }
  map_add' := fun x y => by
    ext φ
    show (φ : Work.SSGRoute.DualMod p A) ((x + y : ↥(K p G A)) : A)
      = (φ : Work.SSGRoute.DualMod p A) x + (φ : Work.SSGRoute.DualMod p A) y
    rw [Submodule.coe_add, map_add]
  map_smul' := fun c x => by
    ext φ
    show (φ : Work.SSGRoute.DualMod p A) ((c • x : ↥(K p G A)) : A)
      = c • ((φ : Work.SSGRoute.DualMod p A) x)
    rw [Submodule.coe_smul, map_smul]

theorem pairP_apply (x : ↥(K p G A)) (φ : ↥(fixSub p G A)) :
    pairP p G A x φ = (φ : Work.SSGRoute.DualMod p A) x := rfl

/-- The pairing kills `N_{A^∨}(A^∨)` in its second variable. -/
theorem pairP_mem_dualAnnihilator (x : ↥(K p G A)) :
    pairP p G A x ∈ (V0 p G A).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro z hz
  obtain ⟨ψ, hψ⟩ := hz
  have hval : (z : Work.SSGRoute.DualMod p A) = dualNormLin p G A ψ := by
    rw [← hψ, Work.Tate.normToFixed_apply]
    rfl
  rw [pairP_apply, hval, dualNormLin_apply_eq, LinearMap.mem_ker.mp x.2, map_zero]

/-- The pairing, viewed as a map into the annihilator of `V0`. -/
noncomputable abbrev pairPann : ↥(K p G A) →ₗ[ZMod p] ↥((V0 p G A).dualAnnihilator) :=
  (pairP p G A).codRestrict _ (pairP_mem_dualAnnihilator p G A)

/-- The pairing, with `(A^∨)^G` quotiented by `N_{A^∨}(A^∨)`. -/
noncomputable abbrev pairP2 :
    ↥(K p G A) →ₗ[ZMod p] (↥(fixSub p G A) ⧸ V0 p G A) →ₗ[ZMod p] ZMod p :=
  (@Submodule.dualQuotEquivDualAnnihilator (ZMod p) ↥(fixSub p G A) _ (Submodule.addCommGroup _)
    (fixSub p G A).module (V0 p G A)).symm.toLinearMap.comp (pairPann p G A)

theorem pairP2_mk (x : ↥(K p G A)) (φ : ↥(fixSub p G A)) :
    pairP2 p G A x (Submodule.Quotient.mk φ) = (φ : Work.SSGRoute.DualMod p A) x := by
  rfl

/-- The pairing kills the augmentation submodule in its first variable. -/
theorem pairP2_mem_ker : K0 p G A ≤ (pairP2 p G A).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun z => ?_
  induction z using Quotient.inductionOn' with | h φ => ?_
  erw [pairP2_mk, LinearMap.zero_apply]
  have hφ : (φ : Work.SSGRoute.DualMod p A) ∈ (augSub p G A).dualAnnihilator := by
    rw [← fixSub_eq_dualAnnihilator]
    exact φ.2
  exact ((Submodule.mem_dualAnnihilator (W := augSub p G A) _).mp hφ) (x : A) hx

/-- **The descended evaluation pairing**
`⟨·,·⟩ : Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p`, `⟨a, φ⟩ = φ a`. -/
noncomputable def pairQ :
    (↥(K p G A) ⧸ K0 p G A) →ₗ[ZMod p] (↥(fixSub p G A) ⧸ V0 p G A) →ₗ[ZMod p] ZMod p :=
  Submodule.liftQ (K0 p G A) (pairP2 p G A) (pairP2_mem_ker p G A)

theorem pairQ_mk (x : ↥(K p G A)) (φ : ↥(fixSub p G A)) :
    pairQ p G A (Submodule.Quotient.mk x) (Submodule.Quotient.mk φ)
      = (φ : Work.SSGRoute.DualMod p A) x := by
  rw [pairQ, Submodule.liftQ_apply, pairP2_mk]

end Work.SSGRoute.TateDual
