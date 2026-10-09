import Mathlib
import Submission.Work.SSGRoute.gradedStep_diagonal
import Submission.Work.SSGRoute.gradedStep_diagonal_zmodTwo_three
import Submission.Work.SSGRoute.gradedStep_two_two
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.isDelta_of_flow_quotient
import Submission.Work.SSGRoute.exists_equiv_fin_mul_zmodTwo
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `(3,3)` graded step at `p = 2` and arbitrary `G`

The target `Work.SSGRoute.gradedStep_three_three` is the diagonal instance `(3,3)` of
Schmidt–Wingberg's graded step at `p = 2`, for an arbitrary finite group `G` and an involution
`δ ∈ G`, `δ ≠ 1`:

> every `δ`-anti-fixed element of the kernel `E(3,3) = ker(Q_{(4,1)} → Q_{(3,3)})` of the free
> `G`-operator group `F(n) = FreeGroup (Fin n × G)` is a `δ`-difference in `Q_{(4,1)}`.

The graded piece `E(3,3)` is the top of `P_3/P_4`, i.e. the degree-three part of the associated
graded Lie ring, and the proof of the corresponding statement for the model group
`G = ℤ/2` (`Submission/Work/SSGRoute/gradedStep_diagonal_zmodTwo_three.lean`, via the
linear-algebra development in `Submission/Work/SSGRoute/zz3/`) uses that, for a *fixed-point-free*
involution `σ` of the free basis, the degree-`3` part of the free associative algebra is a free
`𝔽₂[C₂]`-module.

Here we observe that **the statement depends only on the free basis together with the involution**
induced on it: the refined terms are characteristic subgroups of `FreeGroup X`, and the operator
action of `δ` is the free-group automorphism induced by the basis permutation
`(i, g) ↦ (i, δ g)`.  So it suffices to transport the model statement across the equivariant
bijection `(Fin n × G, (i,g) ↦ (i, δ g)) ≃ (Fin d × ℤ/2, sheet swap)` supplied by
`Work.SSGRoute.exists_equiv_fin_mul_zmodTwo`.

The present file builds that transport:

* `hProj`, `hSig` : the honest quotient maps `F/F^{(τ+1)} → F/F^{(τ)}` and the involution
  `F/F^{(τ)} → F/F^{(τ)}` induced by `freeGroupCongr σ`;
* `HonestStep X σ i j` : the graded step at `(i,j)` phrased in the honest quotient `F/F^{(i,j)}`;
* `HonestStep_transport` : invariance of `HonestStep` under an equivariant isomorphism of the
  bases `e : X ≃ Y`;
* `flowStep_iff_honestStep` : the flow-quotient formulation (`flowQuotient`, `flowQuotSucc`,
  `flowAction`) is equivalent to the honest one.
-/

open scoped commutatorElement

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## A generic free group with a basis involution -/

section Generic

variable {X Y : Type*}

/-- The honest quotient `F ⧸ F^{(i,j)}` of a free group by the refined term. -/
abbrev HQ (X : Type*) (i j : ℕ) : Type _ :=
  FreeGroup X ⧸ Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j

/-- The honest projection `F/F^{(τ+1)} →* F/F^{(τ)}`. -/
noncomputable def hProj (X : Type*) (i j : ℕ) :
    HQ X (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 →* HQ X i j :=
  QuotientGroup.map
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X)
      (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2)
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j)
    (MonoidHom.id _) (by
      rw [Subgroup.comap_id]
      exact Work.SSGRoute.refinedTerm_tauSucc_le 2 (FreeGroup X) i j)

theorem hProj_mk (X : Type*) (i j : ℕ) (z : FreeGroup X) :
    hProj X i j (QuotientGroup.mk'
        (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X)
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2) z)
      = QuotientGroup.mk' (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j) z :=
  QuotientGroup.map_mk' _ _ _ _ z

/-- The involution of the honest quotient `F/F^{(i,j)}` induced by the basis involution `σ`. -/
noncomputable def hSig (X : Type*) (σ : X ≃ X) (i j : ℕ) : HQ X i j →* HQ X i j :=
  QuotientGroup.map
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j)
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j)
    (FreeGroup.freeGroupCongr σ).toMonoidHom (by
      intro y hy
      rw [Subgroup.mem_comap, ← Work.CohomologicalShrinking.map_refinedTerm_eq 2
        (FreeGroup.freeGroupCongr σ) i j]
      exact Subgroup.mem_map_of_mem _ hy)

theorem hSig_mk (X : Type*) (σ : X ≃ X) (i j : ℕ) (z : FreeGroup X) :
    hSig X σ i j (QuotientGroup.mk'
        (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j) z)
      = QuotientGroup.mk' (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j)
          ((FreeGroup.freeGroupCongr σ) z) :=
  QuotientGroup.map_mk' _ _ _ _ z

/-- **The graded step at `(i,j)`, in the honest quotient `F/F^{(i,j)}`.** -/
def HonestStep (X : Type*) (σ : X ≃ X) (i j : ℕ) : Prop :=
  ∀ c : HQ X (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2,
    hProj X i j c = 1 →
    hSig X σ (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2 c = c⁻¹ →
    ∃ e : HQ X (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2,
      c = (hSig X σ (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2 e)⁻¹ * e

end Generic

/-! ## Transport across an equivariant isomorphism of the bases -/

section Transport

variable {X Y : Type*}

/-- The free-group isomorphism induced by `e` intertwines the endomorphisms induced by `σ` and
`τ` whenever `e ∘ σ = τ ∘ e`. -/
theorem freeGroupCongr_comp_map (e : X ≃ Y) (σ : X ≃ X) (τ : Y ≃ Y)
    (hcomm : ∀ x, e (σ x) = τ (e x)) :
    (FreeGroup.freeGroupCongr e).toMonoidHom.comp (FreeGroup.freeGroupCongr σ).toMonoidHom
      = (FreeGroup.freeGroupCongr τ).toMonoidHom.comp (FreeGroup.freeGroupCongr e).toMonoidHom := by
  apply FreeGroup.ext_hom
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, FreeGroup.freeGroupCongr_apply,
    FreeGroup.map.of]
  exact congrArg FreeGroup.of (hcomm x)

/-- An isomorphism of groups maps the refined term onto the refined term. -/
theorem map_refinedTerm_eq_of_mulEquiv {P Q : Type*} [Group P] [Group Q]
    (Φ : P ≃* Q) (i j : ℕ) :
    (Work.CohomologicalShrinking.refinedTerm 2 P i j).map Φ.toMonoidHom
      = Work.CohomologicalShrinking.refinedTerm 2 Q i j := by
  refine le_antisymm
    (Work.CohomologicalShrinking.map_refinedTerm_le_of_surjective 2 Φ.toMonoidHom
      Φ.surjective i j) ?_
  have h2 : (Work.CohomologicalShrinking.refinedTerm 2 Q i j).map Φ.symm.toMonoidHom
      ≤ Work.CohomologicalShrinking.refinedTerm 2 P i j :=
    Work.CohomologicalShrinking.map_refinedTerm_le_of_surjective 2 Φ.symm.toMonoidHom
      Φ.symm.surjective i j
  have h3 := Subgroup.map_mono (f := Φ.toMonoidHom) h2
  rw [Subgroup.map_map] at h3
  have hcomp : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id Q := by
    ext z; simp
  rw [hcomp, Subgroup.map_id] at h3
  exact h3

/-- The isomorphism of the honest quotients `F/F^{(i,j)} ≃* F'/F'^{(i,j)}` induced by an
equivariant identification of the free bases. -/
noncomputable def quotCongrOfEquiv (e : X ≃ Y) (i j : ℕ) : HQ X i j ≃* HQ Y i j :=
  QuotientGroup.congr _ _ (FreeGroup.freeGroupCongr e) (map_refinedTerm_eq_of_mulEquiv _ i j)

theorem quotCongrOfEquiv_mk (e : X ≃ Y) (i j : ℕ) (z : FreeGroup X) :
    quotCongrOfEquiv e i j (QuotientGroup.mk'
        (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j) z)
      = QuotientGroup.mk' (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup Y) i j)
          ((FreeGroup.freeGroupCongr e) z) :=
  QuotientGroup.congr_mk' _ _ _ _ z

theorem quotCongrOfEquiv_hProj (e : X ≃ Y) (i j : ℕ)
    (z : HQ X (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2) :
    quotCongrOfEquiv e i j (hProj X i j z)
      = hProj Y i j (quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 z) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X)
      (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2) z
  rw [hProj_mk, quotCongrOfEquiv_mk, quotCongrOfEquiv_mk, hProj_mk]

theorem quotCongrOfEquiv_hSig (e : X ≃ Y) (σ : X ≃ X) (τ : Y ≃ Y)
    (hcomm : ∀ x, e (σ x) = τ (e x)) (i j : ℕ) (z : HQ X i j) :
    quotCongrOfEquiv e i j (hSig X σ i j z) = hSig Y τ i j (quotCongrOfEquiv e i j z) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) i j) z
  rw [hSig_mk, quotCongrOfEquiv_mk, quotCongrOfEquiv_mk, hSig_mk]
  exact congrArg (QuotientGroup.mk'
      (Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup Y) i j))
    (DFunLike.congr_fun (freeGroupCongr_comp_map e σ τ hcomm) w)

/-- **Invariance of the graded step under an equivariant isomorphism of the free bases.** -/
theorem HonestStep_transport (e : X ≃ Y) (σ : X ≃ X) (τ : Y ≃ Y)
    (hcomm : ∀ x, e (σ x) = τ (e x)) (i j : ℕ)
    (hY : HonestStep Y τ i j) : HonestStep X σ i j := by
  intro c hc hanti
  have hc' : hProj Y i j (quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 c) = 1 := by
    rw [← quotCongrOfEquiv_hProj e i j c, hc, map_one]
  have hanti' : hSig Y τ (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2
        (quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 c)
      = (quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 c)⁻¹ := by
    rw [← quotCongrOfEquiv_hSig e σ τ hcomm (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2 c, hanti, map_inv]
  obtain ⟨e', he'⟩ := hY _ hc' hanti'
  refine ⟨(quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).symm e', ?_⟩
  apply (quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
    (Work.CohomologicalShrinking.tauSucc i j).2).injective
  rw [map_mul, map_inv, MulEquiv.apply_symm_apply,
    quotCongrOfEquiv_hSig e σ τ hcomm (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2
      ((quotCongrOfEquiv e (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2).symm e'),
    MulEquiv.apply_symm_apply]
  exact he'

end Transport

/-! ## The flow-quotient formulation is the honest one -/

section Flow

variable (G : Type*) [Group G] (n : ℕ)

/-- The operator action `flowAction 2 G n i j δ` is the action of the basis involution
`freeOperatorGenPerm n δ` on the honest quotient. -/
theorem sigmaMap_eq_hSig (i j : ℕ) (δ : G) :
    sigmaMap G n i j δ
      = hSig (Fin n × G) (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) i j := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (flowTerm 2 G n i j) z
  rw [sigmaMap_apply_mk, hSig_mk]

/-- `flowQuotSucc` corresponds, under `flowIso`, to the honest projection `hProj`. -/
theorem flowIso_flowQuotSucc (i j : ℕ)
    (c : flowQuotient 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2) :
    flowIso G n i j (flowQuotSucc 2 G n i j c)
      = hProj (Fin n × G) i j
          (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2 c) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) c
  rw [flowQuotSucc_mk, flowIso_apply_mk, flowIso_apply_mk, hProj_mk]

/-- **The flow-quotient form of the graded step is the honest form.** -/
theorem flowStep_iff_honestStep (i j : ℕ) (δ : G) :
    (∀ c : flowQuotient 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2,
      flowQuotSucc 2 G n i j c = 1 →
      flowAction 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2,
        c = (flowAction 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2 δ e)⁻¹ * e)
      ↔ HonestStep (Fin n × G) (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) i j := by
  constructor
  · intro h c hc hanti
    set d := (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).symm c with hd
    have hcd : flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 d = c :=
      MulEquiv.apply_symm_apply _ _
    have h1 : flowQuotSucc 2 G n i j d = 1 := by
      apply (flowIso G n i j).injective
      rw [map_one, flowIso_flowQuotSucc, hcd, hc]
    have h2 : flowAction 2 G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 δ d = d⁻¹ := by
      apply (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2).injective
      rw [map_inv, flowIso_comm, hcd, sigmaMap_eq_hSig]
      exact hanti
    obtain ⟨e, he⟩ := h d h1 h2
    refine ⟨flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2 e, ?_⟩
    rw [← hcd, he, map_mul, map_inv, flowIso_comm, sigmaMap_eq_hSig]
  · intro h c hc hanti
    have h1 : hProj (Fin n × G) i j
        (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 c) = 1 := by
      rw [← flowIso_flowQuotSucc, hc, map_one]
    have h2 : hSig (Fin n × G) (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)
        (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2
        (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 c)
        = (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2 c)⁻¹ := by
      rw [← sigmaMap_eq_hSig, ← flowIso_comm, hanti, map_inv]
    obtain ⟨e, he⟩ := h _ h1 h2
    refine ⟨(flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).symm e, ?_⟩
    apply (flowIso G n (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).injective
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, flowIso_comm,
      MulEquiv.apply_symm_apply, sigmaMap_eq_hSig]
    exact he

end Flow

/-! ## The target -/

theorem gradedStep_three_three (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
        (Work.CohomologicalShrinking.tauSucc 3 3).1
        (Work.CohomologicalShrinking.tauSucc 3 3).2,
      Work.SSGRoute.flowQuotSucc 2 G n 3 3 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 G n
          (Work.CohomologicalShrinking.tauSucc 3 3).1
          (Work.CohomologicalShrinking.tauSucc 3 3).2 δ c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
            (Work.CohomologicalShrinking.tauSucc 3 3).1
            (Work.CohomologicalShrinking.tauSucc 3 3).2,
        c = (Work.CohomologicalShrinking.flowAction 2 G n
              (Work.CohomologicalShrinking.tauSucc 3 3).1
              (Work.CohomologicalShrinking.tauSucc 3 3).2 δ e)⁻¹ * e := by
  classical
  set σ : Fin n × G ≃ Fin n × G := Work.Shrinking.freeOperatorGenPerm (G := G) n δ with hσdef
  have hσinv : ∀ x : Fin n × G, σ (σ x) = x := basisPerm_involutive G n δ hδ
  have hσfree : ∀ x : Fin n × G, σ x ≠ x := basisPerm_ne_self G n δ hδ1
  obtain ⟨d, e, he⟩ := Work.SSGRoute.exists_equiv_fin_mul_zmodTwo σ hσinv hσfree
  set τ : Fin d × Multiplicative (ZMod 2) ≃ Fin d × Multiplicative (ZMod 2) :=
    Work.Shrinking.freeOperatorGenPerm (G := Multiplicative (ZMod 2)) d
      (Multiplicative.ofAdd 1) with hτdef
  have hmodel : HonestStep (Fin d × Multiplicative (ZMod 2)) τ 3 3 :=
    (flowStep_iff_honestStep (Multiplicative (ZMod 2)) d 3 3 (Multiplicative.ofAdd 1)).mp
      (gradedStep_diagonal_zmodTwo_three d)
  have hgen : HonestStep (Fin n × G) σ 3 3 :=
    HonestStep_transport e σ τ he 3 3 hmodel
  exact (flowStep_iff_honestStep G n 3 3 δ).mpr hgen

end Work.SSGRoute
