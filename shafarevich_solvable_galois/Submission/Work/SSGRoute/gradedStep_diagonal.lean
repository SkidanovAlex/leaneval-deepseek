import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
import Submission.Work.SSGRoute.freeGroup_antifixed_is_norm
import Submission.Work.SSGRoute.defectCore
import Submission.Work.SSGRoute.TwoTwoAssembly
import Submission.Work.SSGRoute.prop5.lemma4ii_filtration
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
import Submission.Work.SSGRoute.lcs_inter_pCentralSeries_eq
import Submission.Work.SSGRoute.freeGroup_refinedTerm_lifting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## The norm map of the `p = 2` graded step

For a group `Q` with an involution `δ`, the *norm* (or `δ`-difference) map is
`Ψ(u) = (δ • u)⁻¹ * u`; its image is contained in the anti-fixed set `{x | δ • x = x⁻¹}`, and the
`p = 2` graded step asks that, for `Q = F(n)/F(n)^{(τ+1)}`, this image should surject onto the
anti-fixed elements of the graded piece `E(τ) = ker(Q_{τ+1} → Q_τ)`.

The structural facts recorded here are

* `normMap_mul` : `Ψ(u v) = Ψ(v) * (v⁻¹ * Ψ(u) * v)` — multiplicativity up to conjugation;
* `normMap_inv_self` : `Ψ(δ • u) = Ψ(u)⁻¹`;
* `normMap_self_mul_self` : the norm of the "double" `A * (δ • A)` is the commutator
  `⁅A⁻¹, (δ • A)⁻¹⁆`; since `A` is arbitrary, this exhibits the commutators of an element with its
  `δ`-image as norms, witnessed by `A * (δ • A)`;
* `flowNorm_mul_of_mem_ker` : inside the graded piece (which is central in `Q_{τ+1}`, so that the
  conjugating factor above becomes trivial) the set of norms is closed under multiplication.
-/

section Generic

/-- **Multiplicativity of the norm up to conjugation**: `Ψ(u v) = Ψ(v) * (v⁻¹ * Ψ(u) * v)`. -/
theorem normMap_mul_generic {F : Type*} [Group F] (Φ : F ≃* F) (u v : F) :
    (Φ (u * v))⁻¹ * (u * v) = ((Φ v)⁻¹ * v) * (v⁻¹ * ((Φ u)⁻¹ * u) * v) := by
  rw [map_mul Φ u v]
  group

/-- `Ψ(Φ u) = Ψ(u)⁻¹` for an involution `Φ`. -/
theorem normMap_inv_generic {F : Type*} [Group F] (Φ : F ≃* F) (hΦ : Φ * Φ = 1) (u : F) :
    (Φ (Φ u))⁻¹ * (Φ u) = ((Φ u)⁻¹ * u)⁻¹ := by
  have h2 : Φ (Φ u) = u := by
    have h := congrArg (fun f : F ≃* F => f u) hΦ
    simpa using h
  rw [h2]
  group

/-- **The double**: `Ψ(A * Φ A) = ⁅A⁻¹, (Φ A)⁻¹⁆`. -/
theorem normMap_self_generic {F : Type*} [Group F] (Φ : F ≃* F) (hΦ : Φ * Φ = 1) (A : F) :
    (Φ (A * Φ A))⁻¹ * (A * Φ A) = ⁅A⁻¹, (Φ A)⁻¹⁆ := by
  have h2 : Φ (Φ A) = A := by
    have h := congrArg (fun f : F ≃* F => f A) hΦ
    simpa using h
  rw [map_mul Φ A (Φ A), h2, mul_inv_rev, commutatorElement_def]
  group

end Generic

section FreeOperator

variable {G : Type*} [Group G] {n : ℕ}

/-- **The norm map** `u ↦ (δ • u)⁻¹ * u` on the free `G`-operator group `F(n)`. -/
noncomputable def normMap_gsd (G : Type*) [Group G] (n : ℕ) (δ : G)
    (u : Work.Shrinking.freeOperatorGroup G n) : Work.Shrinking.freeOperatorGroup G n :=
  (δ • u)⁻¹ * u

/-- The action of `δ` on the free operator group is an involution when `δ * δ = 1`. -/
theorem freeOperatorActionHom_sq (δ : G) (hδ : δ * δ = 1) :
    Work.Shrinking.freeOperatorActionHom (G := G) n δ
      * Work.Shrinking.freeOperatorActionHom (G := G) n δ = 1 := by
  rw [← map_mul, hδ, map_one]

/-- **Multiplicativity of the norm up to conjugation** on the free operator group. -/
theorem normMap_mul (δ : G) (u v : Work.Shrinking.freeOperatorGroup G n) :
    normMap_gsd G n δ (u * v) = normMap_gsd G n δ v * (v⁻¹ * normMap_gsd G n δ u * v) :=
  normMap_mul_generic (Work.Shrinking.freeOperatorActionHom (G := G) n δ) u v

/-- `Ψ(δ • u) = Ψ(u)⁻¹`. -/
theorem normMap_inv_self (δ : G) (hδ : δ * δ = 1)
    (u : Work.Shrinking.freeOperatorGroup G n) :
    normMap_gsd G n δ (δ • u) = (normMap_gsd G n δ u)⁻¹ :=
  normMap_inv_generic (Work.Shrinking.freeOperatorActionHom (G := G) n δ)
    (freeOperatorActionHom_sq (G := G) (n := n) δ hδ) u

/-- **The double**: the norm of `A * (δ • A)` is the commutator `⁅A⁻¹, (δ • A)⁻¹⁆`. -/
theorem normMap_self_mul_self (δ : G) (hδ : δ * δ = 1)
    (A : Work.Shrinking.freeOperatorGroup G n) :
    normMap_gsd G n δ (A * (δ • A)) = ⁅A⁻¹, (δ • A)⁻¹⁆ :=
  normMap_self_generic (Work.Shrinking.freeOperatorActionHom (G := G) n δ)
    (freeOperatorActionHom_sq (G := G) (n := n) δ hδ) A

end FreeOperator

section Quotient

variable {G : Type*} [Group G] {n : ℕ}

/-- The generic multiplicativity formula on the quotient `Q_{(j+1,1)}`. -/
theorem flowNorm_mul (δ : G) (j : ℕ)
    (x y : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) :
    (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ (x * y))⁻¹ * (x * y)
      = ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y)
        * (y⁻¹ * ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ x)⁻¹ * x) * y) :=
  normMap_mul_generic (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ) x y

/-- **The norm image inside the graded piece is closed under multiplication.**  If `Ψ(x)` and
`Ψ(y)` both lie in the kernel of `flowQuotSucc` (which is central in `Q_{(j+1,1)}`), then
`Ψ(y * x) = Ψ(x) * Ψ(y)`; in particular the product of two norms-in-the-kernel is again a norm. -/
theorem flowNorm_mul_of_mem_ker (δ : G) (j : ℕ)
    (x y : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
    (hy : ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y)
      ∈ (flowQuotSucc 2 G n j j).ker) :
    (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ (y * x))⁻¹ * (y * x)
      = ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ x)⁻¹ * x)
        * ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y) := by
  rw [flowNorm_mul δ j y x]
  have hcy : x⁻¹ * ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y) * x
      = ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y) := by
    have h := flowQuotSucc_ker_central 2 G n j j x⁻¹
      ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ y)⁻¹ * y) hy
    simpa using h
  rw [hcy]

end Quotient

section Lifts

variable {G : Type*} [Group G] {n : ℕ}

/-! ## The reduction to the existence of anti-fixed lifts

The target is equivalent to a statement about the *free* group `F(n)`: every `x` whose class in
`Q_{(j+1,1)} = F(n)/F(n)^{(j+1,1)}` is anti-fixed can be adjusted by an element of
`F(n)^{(j+1,1)}` to an element which is anti-fixed *on the nose*.  Given such a lift, the
half-word lemma (`freeGroup_antifixed_is_norm`) produces the witness.
-/

/-- The permutation `(i, g) ↦ (i, δ * g)` of the basis of the free operator group. -/
abbrev basisPerm (G : Type*) [Group G] (n : ℕ) (δ : G) : (Fin n × G) ≃ (Fin n × G) :=
  Work.Shrinking.freeOperatorGenPerm (G := G) n δ

@[simp] theorem basisPerm_apply (δ : G) (x : Fin n × G) :
    basisPerm G n δ x = (x.1, δ * x.2) := rfl

theorem basisPerm_involutive (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (x : Fin n × G) : basisPerm G n δ (basisPerm G n δ x) = x := by
  simp only [basisPerm_apply]
  rw [← mul_assoc, hδ, one_mul]

theorem basisPerm_ne_self (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ1 : δ ≠ 1)
    (x : Fin n × G) : basisPerm G n δ x ≠ x := by
  intro h
  have h2 : δ * x.2 = x.2 := by
    simpa [basisPerm, Work.Shrinking.freeOperatorGenPerm] using congrArg Prod.snd h
  exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))

/-- The action of `δ` on `F(n)` is the automorphism induced by `basisPerm`. -/
theorem smul_eq_freeGroupCongr (δ : G) (x : Work.Shrinking.freeOperatorGroup G n) :
    δ • x = FreeGroup.freeGroupCongr (basisPerm G n δ) x := rfl

/-- The class of the `δ`-image is the `δ`-image of the class. -/
theorem flowAction_mk_top (δ : G) (j : ℕ)
    (y : Work.Shrinking.freeOperatorGroup G n) :
    (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨y, Subgroup.mem_top y⟩)
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨δ • y, Subgroup.mem_top _⟩ := by
  have hP : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) = ⊤ :=
    Subgroup.map_top_of_surjective _
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ).surjective
  have hK : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 :=
    map_refinedTerm_eq 2 _ (tauSucc j j).1 (tauSucc j j).2
  change Work.Shrinking.quotAut ⊤ (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2) δ hP hK
    (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) ⟨y, Subgroup.mem_top y⟩)
    = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤))
    (Subtype.ext (by simp [Work.Shrinking.subAut_coe]))

/-- Multiplication in `Q_{(j+1,1)}` on representatives. -/
theorem flowQuot_mk_top_mul (j : ℕ) (y z : Work.Shrinking.freeOperatorGroup G n) :
    (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      * QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨z, Subgroup.mem_top z⟩
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y * z, Subgroup.mem_top _⟩ := by
  rw [← map_mul]
  rfl

/-- Inversion in `Q_{(j+1,1)}` on representatives. -/
theorem flowQuot_mk_top_inv (j : ℕ) (y : Work.Shrinking.freeOperatorGroup G n) :
    ((QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩)⁻¹
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y⁻¹, Subgroup.mem_top _⟩ := by
  rw [← map_inv]
  rfl

/-- A class in `Q_{(j+1,1)}` is trivial exactly when the representative lies in the refined term. -/
theorem mk_top_eq_one_iff (j : ℕ) (y : Work.Shrinking.freeOperatorGroup G n) :
    (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1
    ↔ y ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

/-- **The reduction.**  If every coset of `F(n)^{(j+1,1)}` inside `F(n)` that is anti-fixed modulo
`F(n)^{(j+1,1)}` contains an anti-fixed element, then the diagonal graded step holds. -/
theorem diagonal_of_antifixed_lifts (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1)
    (hlift : ∀ j : ℕ, 2 ≤ j → ∀ x : Work.Shrinking.freeOperatorGroup G n,
      (δ • x) * x ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 →
      ∃ u : Work.Shrinking.freeOperatorGroup G n,
        u ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 ∧
        (δ • (x * u)) * (x * u) = 1) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  intro j hj c hc hanti
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) c
  set y : Work.Shrinking.freeOperatorGroup G n :=
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))).1 with hy
  have hxc : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) x
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = c := hx
  have hyc : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = c := by
    rw [← hxc]
  -- `(δ • y) * y` has trivial class, hence lies in the refined term
  have hmem : (δ • y) * y ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 := by
    rw [← mk_top_eq_one_iff j ((δ • y) * y), ← flowQuot_mk_top_mul j (δ • y) y,
      ← flowAction_mk_top δ j y, hyc, hanti, inv_mul_cancel]
  obtain ⟨u, hu, hfix⟩ := hlift j hj y hmem
  -- the half-word lemma
  have hanti' : FreeGroup.freeGroupCongr (basisPerm G n δ) (y * u) = (y * u)⁻¹ := by
    have h : (δ • (y * u)) * (y * u) = 1 := hfix
    rw [smul_eq_freeGroupCongr] at h
    exact eq_inv_iff_mul_eq_one.mpr h
  obtain ⟨v, hv⟩ := freeGroup_antifixed_is_norm (basisPerm G n δ)
    (basisPerm_involutive G n δ hδ) (basisPerm_ne_self G n δ hδ1) (y * u) hanti'
  refine ⟨QuotientGroup.mk'
    ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
    ⟨v, Subgroup.mem_top v⟩, ?_⟩
  -- the witness class is the class of the half-word, which is the class of `y * u = c`
  rw [flowAction_mk_top δ j v, flowQuot_mk_top_inv, flowQuot_mk_top_mul]
  rw [smul_eq_freeGroupCongr δ v, ← hv]
  -- the class of `y * u` is the class of `y`, i.e. `c`
  rw [← flowQuot_mk_top_mul, (mk_top_eq_one_iff j u).mpr hu, mul_one, hyc]



end Lifts


/-! ## The monomial norms (orbit sums)

For `w = prop5.commWord j x ∈ γ_j` the square `(δ • w)²` lies in `P_{j+1}`, so in
`Q_{(j+1,1)} = F(n)/P_{j+1}` the class of the norm `Ψ(w) = (δ • w)⁻¹ * w` equals the class of the
"orbit sum" `(δ • w) * w` of the monomial and its `δ`-transport. -/

private lemma smul_commWord_action {G : Type*} [Group G] {n : ℕ} (δ : G) (j : ℕ)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G n) :
    δ • Work.SSGRoute.prop5.commWord j x
      = Work.SSGRoute.prop5.commWord j (fun i => δ • x i) := by
  have h := Work.SSGRoute.prop5.commWord_map
    (Work.Shrinking.freeOperatorActionHom (G := G) n δ).toMonoidHom j x
  simpa [Work.Shrinking.smul_freeOperatorGroup_eq] using h.symm

private theorem commWord_norm_orbit_aux (G : Type*) [Group G] (n j : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hj : 1 ≤ j) (x : Fin j → Work.Shrinking.freeOperatorGroup G n) :
    ((flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j x, Subgroup.mem_top _⟩))⁻¹
      * (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j x, Subgroup.mem_top _⟩))
    = (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j (fun i => δ • x i), Subgroup.mem_top _⟩)
      * (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j x, Subgroup.mem_top _⟩) := by
  set u : Work.Shrinking.freeOperatorGroup G n := Work.SSGRoute.prop5.commWord j x with hu
  set w : Work.Shrinking.freeOperatorGroup G n :=
    Work.SSGRoute.prop5.commWord j (fun i => δ • x i) with hw
  have hW : w ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) :=
    Work.SSGRoute.prop5.commWord_mem_lowerCentralSeries j _
  have hw2 : w * w ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 := by
    have hT : flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
        = pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
      rw [tauSucc_of_le (le_refl j)]
      exact refinedTerm_one 2 _ (j + 1)
    rw [hT]
    have h := Work.SSGRoute.prop5.pow_mem_pSeries 2 j 1 hj w hW
    simpa [pow_two, pSeries] using h
  have hsu : δ • u = w := by
    rw [hu, hw]
    exact smul_commWord_action δ j x
  have hkey : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨w⁻¹ * u, Subgroup.mem_top _⟩ : flowQuotient 2 G n
          (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨w * u, Subgroup.mem_top _⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    refine Subgroup.mem_subgroupOf.mpr ?_
    show ((w⁻¹ * u) / (w * u) : Work.Shrinking.freeOperatorGroup G n) ∈ _
    rw [div_eq_mul_inv, show (w⁻¹ * u) * (w * u)⁻¹ = (w * w)⁻¹ from by group]
    exact Subgroup.inv_mem _ hw2
  rw [flowAction_mk_top δ j u, flowQuot_mk_top_inv j (δ • u), hsu,
    flowQuot_mk_top_mul j w⁻¹ u, flowQuot_mk_top_mul j w u]
  exact hkey


/-! ## Generation of the graded piece `E(j,j)` by the commutator-word monomials

`T(j,j) = γ_j · P_{j+1}` and `γ_j` is generated by the words `commWord j x`, so the graded piece
`E(j,j) = T(j,j)/P_{j+1}` is generated by their images. -/

private theorem refinedTerm_self_le_closure_commWord_sup (G : Type*) [Group G] (n j : ℕ)
    (hj : 1 ≤ j) :
    refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) j j ≤
      Subgroup.closure (Set.range (fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
        Work.SSGRoute.prop5.commWord j x)) ⊔
      refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) 1 := by
  rw [refinedTerm]
  refine sup_le ?_ ?_
  · refine le_trans inf_le_right ?_
    refine le_trans (Work.SSGRoute.prop5.lowerCentralSeries_le_closure_commWord j hj) ?_
    refine le_trans (Subgroup.closure_mono ?_) le_sup_left
    rintro y ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rw [refinedTerm_one]
    exact le_sup_right




/-- The projection to `Q_{(j+1,1)}` carries the closure of the commutator words to the closure of
their images. -/
private lemma closure_commWord_image (G : Type*) [Group G] (n j : ℕ)
    (z : Work.Shrinking.freeOperatorGroup G n)
    (hz : z ∈ Subgroup.closure (Set.range (fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
      Work.SSGRoute.prop5.commWord j x))) :
    (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨z, Subgroup.mem_top z⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) ∈
      Subgroup.closure (Set.range (fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
        QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j x, Subgroup.mem_top _⟩)) := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
      obtain ⟨x, hx⟩ := hw
      rw [← hx]
      exact Subgroup.subset_closure ⟨x, rfl⟩
  | one =>
      rw [show (⟨(1 : Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top 1⟩ :
          ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
  | mul u v hu hv ihu ihv =>
      rw [← flowQuot_mk_top_mul j u v]
      exact Subgroup.mul_mem _ ihu ihv
  | inv u hu ihu =>
      rw [← flowQuot_mk_top_inv j u]
      exact Subgroup.inv_mem _ ihu

/-- The kernel of the projection `Q_{(j+1,1)} → Q_{(j,j)}` — i.e. the graded piece `E(j,j)` — is
contained in the subgroup generated by the classes of the commutator words `commWord j x`. -/
private theorem ker_flowQuotSucc_le_closure_commWord (G : Type*) [Group G] (n j : ℕ)
    (hj : 1 ≤ j) :
    (flowQuotSucc 2 G n j j).ker ≤
      Subgroup.closure (Set.range (fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
        QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨Work.SSGRoute.prop5.commWord j x, Subgroup.mem_top _⟩)) := by
  intro c hc
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) c
  set y : Work.Shrinking.freeOperatorGroup G n :=
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))).1 with hy
  have hyc : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = c := by
    rw [← hx]
  have hymem : y ∈ flowTerm 2 G n j j := by
    have h : flowQuotSucc 2 G n j j (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩) = 1 := by
      rw [hyc]; exact hc
    rw [flowQuotSucc_mk] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  haveI : (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).Normal :=
    Work.CohomologicalShrinking.refinedTerm_normal 2 _ _ _
  have hdecomp : y ∈ refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) j j := hymem
  rw [refinedTerm] at hdecomp
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j ⊓
      centralSeries (Work.Shrinking.freeOperatorGroup G n) j)
      (t := pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1))).mp hdecomp
  have hb1 : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨b, Subgroup.mem_top b⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hT : flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
        = pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
      rw [tauSucc_of_le (le_refl j), flowTerm, refinedTerm_one]
    rw [hT]
    exact hb
  have hclosure : a ∈ Subgroup.closure (Set.range (fun x : Fin j →
      Work.Shrinking.freeOperatorGroup G n => Work.SSGRoute.prop5.commWord j x)) :=
    (Subgroup.closure_mono (by rintro z ⟨w, hw⟩; exact ⟨w, hw.symm⟩))
      (Work.SSGRoute.prop5.lowerCentralSeries_le_closure_commWord j hj ha.2)
  have hma := closure_commWord_image G n j a hclosure
  have hy_eq : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨a, Subgroup.mem_top a⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) := by
    rw [show y = a * b from hab.symm, ← flowQuot_mk_top_mul j a b, hb1, mul_one]
  rw [← hyc]
  rw [hy_eq]
  exact hma


/-! ## The `j = 2` instance of the diagonal graded step

This is `Work.SSGRoute.two_two_graded_step` (in `SSGRoute/TwoTwoAssembly`, sorry-free) rewritten
in the `tauSucc 2 2 = (3,1)` normal form used by the target. -/

private theorem gradedStep_diagonal_two (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 2 2).1 (tauSucc 2 2).2,
      flowQuotSucc 2 G n 2 2 c = 1 →
      flowAction 2 G n (tauSucc 2 2).1 (tauSucc 2 2).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 2 2).1 (tauSucc 2 2).2,
        c = (flowAction 2 G n (tauSucc 2 2).1 (tauSucc 2 2).2 δ e)⁻¹ * e := by
  intro c hc hanti
  exact Work.SSGRoute.two_two_graded_step (G := G) (n := n) δ hδ hδ1 c hc hanti



/-! ## State of the proof of the diagonal graded step

Everything above this point is proved (no `sorry`).  The chain of reductions is:

* `normMap_self_mul_self` : the commutator `⁅A⁻¹, (δ • A)⁻¹⁆` is a norm, witnessed by
  `A * (δ • A)`.  Since `A` is arbitrary, the norm image contains the commutators of every element
  with its `δ`-image.
* `flowNorm_mul_of_mem_ker` : inside the graded piece `E(j,j)` — which is central in `Q_{(j+1,1)}`
  by `flowQuotSucc_ker_central` — the norm image is closed under multiplication.
* `normMap_eq_sq` and `flowNorm_eq_of_sq` : `Ψ(v) = (v * (δ • v))⁻¹ * (v * v)`, so a "square root"
  `v` with `v * (δ • v) ≡ 1` and `v * v ≡ c` is a witness for `c`.
* `diagonal_of_antifixed_lifts` : the target follows from the *anti-fixed lift* property
  > for `x ∈ F(n)` with `(δ • x) * x ∈ F(n)^{(j+1,1)}` there is `u ∈ F(n)^{(j+1,1)}` with
  > `(δ • (x * u)) * (x * u) = 1`,
  together with the half-word lemma `freeGroup_antifixed_is_norm` (in the workspace) and the
  class-level computations `flowAction_mk_top`, `flowQuot_mk_top_mul`, `flowQuot_mk_top_inv`,
  `mk_top_eq_one_iff`.

The remaining crux is exactly the anti-fixed lift property; the two formulations are equivalent
(cf. `target_of_lifting` / `lifting_of_target` in
`Submission/Work/SSGRoute/freeGroup_quotient_antifixed_is_norm.lean`), so this reduction localises
the whole content: in the coordinates of the relatively free `2`-group `F(n)/P_{j+1}`, the
anti-fixedness equation of an element must be solvable for a lift inside the same coset.  The known
base case is `j = 2`, where the witness is the "half" of the monomial: for the orbit pair
`{x, δx}`, `(δ • (x * (δ x)))⁻¹ * (x * (δ x)) = ⁅x, δ x⁆`.

### Where the difficulty sits

Write `w := (δ • x) * x ∈ P_{j+1}` for a lift `x` of an anti-fixed class.  The *first* level of the
equation `(δ • (x * u)) * (x * u) = 1` (with `u ∈ P_{j+1}`) reads, modulo `P_{j+2}`,
`(δ • u) * u ≡ w⁻¹`, which is solvable iff the class of `w` in
`H¹(⟨δ⟩, P_{j+1}/P_{j+2}) = (P_{j+1}/P_{j+2})^δ / (1+δ)(P_{j+1}/P_{j+2})` vanishes.  This class is
quadratic in `x` and depends only on the class of `x` modulo `P_{j+1}`; the higher levels give
further conditions of the same shape one filtration step deeper.  So the content of the diagonal
graded step is that all these obstruction classes vanish on `E(j,j)^δ` (for `j = 2` this is the
classical quadratic-form computation of `TwoTwoStep.lean`), and it is *not* a formal consequence of
the centrality of the graded piece — the "strong" form with the witness inside `E(j,j)` is false.
-/

/-! ## The orbit-sum sub-case of the diagonal graded step

Every element of the subgroup of `Q_{(j+1,1)}` generated by the "orbit sums"
`[commWord j x] * [commWord j (δ • x)]` is a `δ`-difference in the ambient group.  This is the
whole content of the diagonal step for **odd** `j` (there the anti-fixed part of the graded piece
`E(j,j) ≅ (γ_j/γ_{j+1}) ⊗ 𝔽₂` *is* the image of `1 + δ`), and it is the "orbit-sum half" of the
general case; the residual is the "self-paired" part of `E(j,j)`. -/

theorem orbitSum_is_delta_difference (G : Type*) [Group G] (n j : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hj : 1 ≤ j) :
    ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
      c ∈ Subgroup.closure (Set.range fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
        (QuotientGroup.mk'
            ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
            ⟨prop5.commWord j (fun i => δ • x i), Subgroup.mem_top _⟩)
        * (QuotientGroup.mk'
            ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
            ⟨prop5.commWord j x, Subgroup.mem_top _⟩)) →
      ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  intro c hc
  have hK : ∀ y : Fin j → Work.Shrinking.freeOperatorGroup G n,
      (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨prop5.commWord j y, Subgroup.mem_top _⟩ :
        flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      ∈ (flowQuotSucc 2 G n j j).ker := by
    intro y
    have hmem : prop5.commWord j y ∈ refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) j j := by
      rw [refinedTerm]
      refine Subgroup.mem_sup_left ⟨?_, prop5.commWord_mem_lowerCentralSeries j y⟩
      have h := prop5.pow_mem_pSeries 2 j 0 hj (prop5.commWord j y)
        (prop5.commWord_mem_lowerCentralSeries j y)
      simpa using h
    have hm : (QuotientGroup.mk' ((flowTerm 2 G n j j).subgroupOf ⊤)
        ⟨prop5.commWord j y, Subgroup.mem_top _⟩ :
        flowQuotient 2 G n j j) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hmem
    rw [MonoidHom.mem_ker, flowQuotSucc_mk]
    exact hm
  have hconj : ∀ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
      flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e) = e := by
    intro e
    have h3 : (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        * flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ)
        = (1 : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2 ≃*
            flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) := by
      rw [← map_mul, hδ, map_one]
    calc flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
          (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)
        = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
            * flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ) e := rfl
      _ = (1 : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2 ≃*
            flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) e := by rw [h3]
      _ = e := rfl
  have aux : ∀ q ∈ Subgroup.closure (Set.range fun x : Fin j →
        Work.Shrinking.freeOperatorGroup G n =>
        (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
            ⟨prop5.commWord j (fun i => δ • x i), Subgroup.mem_top _⟩ :
          flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
        * (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
            ⟨prop5.commWord j x, Subgroup.mem_top _⟩)),
        (∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          q = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e)
        ∧ q ∈ (flowQuotSucc 2 G n j j).ker := by
      intro q hq
      induction hq using Subgroup.closure_induction with
      | mem w hw =>
          obtain ⟨x, rfl⟩ := hw
          exact ⟨⟨(QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
              ⟨prop5.commWord j x, Subgroup.mem_top _⟩ :
              flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2),
            (commWord_norm_orbit_aux G n j δ hδ (by omega : 1 ≤ j) x).symm⟩,
            Subgroup.mul_mem _ (hK (fun i => δ • x i)) (hK x)⟩
      | one =>
          exact ⟨⟨1, by simp⟩, Subgroup.one_mem _⟩
      | mul a b ha hb iha ihb =>
          obtain ⟨⟨ea, hea⟩, hka⟩ := iha
          obtain ⟨⟨eb, heb⟩, hkb⟩ := ihb
          refine ⟨⟨eb * ea, ?_⟩, Subgroup.mul_mem _ hka hkb⟩
          rw [flowNorm_mul_of_mem_ker δ j ea eb (by rw [← heb]; exact hkb), hea, heb]
      | inv a ha iha =>
          obtain ⟨⟨ea, hea⟩, hka⟩ := iha
          refine ⟨⟨flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ ea, ?_⟩,
            Subgroup.inv_mem _ hka⟩
          rw [hconj ea, hea]
          group
  exact (aux c hc).1


/-! ## The two witness families of the diagonal graded step, and the exact remaining gap

The two families of norms consumed by the diagonal graded step are

* the **orbit sums** `[commWord j (δ • x)] * [commWord j x]` of the weight-`j` commutator
  monomials (`orbitSum_is_delta_difference`), and
* the **`δ`-paired commutators** `⁅u⁻¹, (δ • u)⁻¹⁆ = Ψ(u * (δ • u))`
  (`pairedCommutator_is_delta_difference`);

their classes all lie in the graded piece `E(j,j) = ker(Q_{(j+1,1)} → Q_{(j,j)})`, where the norm
image is a subgroup (`closure_is_deltaDifference_of_mem_ker`).

The precise statement that remains open — the *only* gap left in this file — is that these two
families generate the anti-fixed part of `E(j,j)` multiplicatively (`DiagonalCore` below, and
`gradedStep_diagonal_of_core`, which deduces the target from it).

**CAVEAT (see `GRADEDSTEP_DIAGONAL_FOUR_DIAGNOSIS.md`).**  `DiagonalCore` is a *sufficient*
condition, not necessarily the sharp one, and for even `j` it is not obviously true: the abstract
(degree-graded) statement that the orbit sums together with the `δ`-paired family span
`E(j,j)^σ` is true and was verified in the `𝔽₂`-Magnus model `𝔽₂⟨X⟩/I^{j+1}`, but that model is
**not faithful** for the refined term `F(n)^{(j,j)}`: a `δ`-paired witness `ν(A·(δ•A)) = ⁅A⁻¹,(δA)⁻¹⁆`
with `A ∈ P_{j/2}` need not lie in `γ_j·P_{j+1}`, so its class need not be an element of `E(j,j)` at
all (e.g. `ν(a²b²) = [a²,b²] ∉ γ₄P₅` for `X = {a,b}`, `j = 4`).  The correct witnesses are
*level-`1`* words with an even extra factor, e.g. `A·[a⁻¹,b]·A` with `A = ab` for the residual class
of `E(4,4)`, and their construction for all `j` is the genuinely open input recorded in the
diagnosis file.  Everything proved in this file (the two norm families, the norm-closure lemma and
`gradedStep_diagonal_of_core` / `gradedStep_diagonal_of_odd_even`) remains correct and useful.

Mathematical shape of the gap.  Write `E(j,j) ≅ γ_j/(γ_j²γ_{j+1}) = (γ_j/γ_{j+1}) ⊗ 𝔽₂ =: L_j`,
the degree-`j` part of the free `𝔽₂`-Lie algebra on `X = Fin n × G`, on which `δ` acts through the
free involution `x ↦ δx` of `X`.

* For **odd** `j` the orbit sums alone suffice: `ker(1+δ) = im(1+δ)` on `L_j`.  (Reason: the
  left-normed-bracket map `T_j ↠ L_j` from the degree-`j` part of the free associative algebra is
  `δ`-equivariant, `T_j` is a permutation module for a fixed-point-free involution, and for odd `j`
  the Dynkin/Wever idempotent `j^{-1}Σ_{σ∈S_j}` exists over `𝔽₂` and exhibits `L_j` as a
  `δ`-equivariant retract of `T_j`; a retract of a free `𝔽₂[δ]/(δ-1)²`-module is free, so
  `ker(1+δ) = im(1+δ)`.)
* For **even** `j = 2m` the residual quotient `L_j^δ/(1+δ)L_j` is still non-zero
  (`dim = 1, 1, 1, 2` for `j = 2, 4, 6, 8` with `|X| = 2`), and it is *spanned* by the classes of
  the `δ`-paired commutators `⁅y⁻¹, (δ • y)⁻¹⁆` with `y ∈ P_m` (the `m`-th term of the descending
  `2`-central series `P_1 = F(n)`, `P_{m+1} = P_m²[P_m, F(n)]`, i.e. the Zassenhaus/restricted-Lie
  layer of weight `m`).  Equivalently, the corresponding witnesses `y * (δ • y)` have weight `2m`.

Verified computationally in the exact mod-2 Magnus model `𝔽₂⟨X⟩/I^{j+1}` for `j ≤ 8` and
`|X| ∈ {2,4}` (the two families reach `dim ker(1+δ)` exactly, and every `⁅y⁻¹,(δ•y)⁻¹⁆` with
`y ∈ P_{j/2}` has its degree-`j` component inside the Lie part).  It subsumes the known cases:
`j = 2` (witness `ab` for `x = a`, `δ • x = b`), and `j = 4`, `n = 1`, `G = ℤ/2`, where the
witness for the obstruction `e₂ = ⁅⁅⁅b,a⁆,a⁆,b⁆` is `a²b² = y * (δ • y)` with `y = a² ∈ P_2`. -/

/-- The **orbit-sum family** of the diagonal graded step: the classes in `Q_{(j+1,1)}` of the
products `commWord j (δ • x) * commWord j x` of the weight-`j` commutator monomials and their
`δ`-transports. -/
noncomputable def orbitSumFamily (G : Type*) [Group G] (n j : ℕ) (δ : G) :
    Set (flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) :=
  Set.range fun x : Fin j → Work.Shrinking.freeOperatorGroup G n =>
    (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨prop5.commWord j (fun i => δ • x i), Subgroup.mem_top _⟩)
      * (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨prop5.commWord j x, Subgroup.mem_top _⟩)

/-- The **`δ`-paired commutator family**: the classes in `Q_{(j+1,1)}` of the commutators
`⁅u⁻¹, (δ • u)⁻¹⁆ = Ψ(u * (δ • u))` for those `u ∈ F(n)` for which this element lies in the graded
piece `F(n)^{(j,j)}` (so that its class lies in `E(j,j)`). -/
noncomputable def pairedCommutatorFamily (G : Type*) [Group G] (n j : ℕ) (δ : G) :
    Set (flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) :=
  {c | ∃ u : Work.Shrinking.freeOperatorGroup G n,
      ⁅u⁻¹, (δ • u)⁻¹⁆ ∈ flowTerm 2 G n j j ∧
      c = QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
            ⟨⁅u⁻¹, (δ • u)⁻¹⁆, Subgroup.mem_top _⟩}

/-- **The remaining input of the diagonal graded step.**  Every anti-fixed element of the graded
piece `E(j,j) = ker(Q_{(j+1,1)} → Q_{(j,j)})` lies in the subgroup generated by the orbit sums of the
weight-`j` commutator monomials and the `δ`-paired commutators (see the discussion above; for odd
`j` the orbit sums alone suffice). -/
def DiagonalCore (G : Type*) [Group G] (n j : ℕ) (δ : G) : Prop :=
  ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
    flowQuotSucc 2 G n j j c = 1 →
    flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
    c ∈ Subgroup.closure (orbitSumFamily G n j δ ∪ pairedCommutatorFamily G n j δ)

/-- **`δ`-paired commutators are `δ`-differences.**  For every `u ∈ F(n)`, the class of
`⁅u⁻¹, (δ • u)⁻¹⁆` in `Q_{(j+1,1)}` is the norm of the class of the "`δ`-paired product"
`u * (δ • u)`, because `Ψ(u * (δ • u)) = ⁅u⁻¹, (δ • u)⁻¹⁆` (`normMap_self_mul_self`). -/
theorem pairedCommutator_is_delta_difference (G : Type*) [Group G] (n j : ℕ) (δ : G)
    (hδ : δ * δ = 1) (u : Work.Shrinking.freeOperatorGroup G n) :
    ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
      (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨⁅u⁻¹, (δ • u)⁻¹⁆, Subgroup.mem_top _⟩ :
          flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
        = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  refine ⟨QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
      ⟨u * (δ • u), Subgroup.mem_top _⟩, ?_⟩
  rw [flowAction_mk_top δ j (u * (δ • u)),
    flowQuot_mk_top_inv j (δ • (u * (δ • u))),
    flowQuot_mk_top_mul j (δ • (u * (δ • u)))⁻¹ (u * (δ • u)),
    ← normMap_self_mul_self δ hδ u]
  rfl

/-- **The subgroup generated by norms inside the graded piece consists of norms.**  If all elements
of a generating set `S ⊆ ker(flowQuotSucc 2 G n j j)` are `δ`-differences, then so is every element
of `Subgroup.closure S`: the kernel is central (`flowQuotSucc_ker_central`), so the exact defect
`flowNorm_mul_of_mem_ker` of the norm map vanishes there. -/
theorem closure_is_deltaDifference_of_mem_ker (G : Type*) [Group G] (n j : ℕ) (δ : G)
    (hδ : δ * δ = 1)
    (S : Set (flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2))
    (hker : ∀ s ∈ S, s ∈ (flowQuotSucc 2 G n j j).ker)
    (hnorm : ∀ s ∈ S, ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
      s = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e) :
    ∀ c ∈ Subgroup.closure S,
      ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  have hconj : ∀ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
      flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e) = e := by
    intro e
    have h3 : (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        * flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ)
        = (1 : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2 ≃*
            flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) := by
      rw [← map_mul, hδ, map_one]
    calc flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
          (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)
        = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
            * flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ) e := rfl
      _ = (1 : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2 ≃*
            flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) e := by rw [h3]
      _ = e := rfl
  intro c hc
  have aux : ∀ q ∈ Subgroup.closure S,
      (∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        q = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e)
      ∧ q ∈ (flowQuotSucc 2 G n j j).ker := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem w hw => exact ⟨hnorm w hw, hker w hw⟩
    | one => exact ⟨⟨1, by simp⟩, Subgroup.one_mem _⟩
    | mul a b ha hb iha ihb =>
        obtain ⟨⟨ea, hea⟩, hka⟩ := iha
        obtain ⟨⟨eb, heb⟩, hkb⟩ := ihb
        refine ⟨⟨eb * ea, ?_⟩, Subgroup.mul_mem _ hka hkb⟩
        rw [flowNorm_mul_of_mem_ker δ j ea eb (by rw [← heb]; exact hkb), hea, heb]
    | inv a ha iha =>
        obtain ⟨⟨ea, hea⟩, hka⟩ := iha
        refine ⟨⟨flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ ea, ?_⟩,
          Subgroup.inv_mem _ hka⟩
        rw [hconj ea, hea]
        group
  exact (aux c hc).1

/-- A class whose representative lies in the graded piece `F(n)^{(j,j)}` lies in the kernel of the
projection `Q_{(j+1,1)} → Q_{(j,j)}`. -/
theorem mem_ker_of_mem_flowTerm (G : Type*) [Group G] (n j : ℕ)
    (y : Work.Shrinking.freeOperatorGroup G n) (hy : y ∈ flowTerm 2 G n j j) :
    (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top _⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      ∈ (flowQuotSucc 2 G n j j).ker := by
  rw [MonoidHom.mem_ker, flowQuotSucc_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact hy

/-- The product of two classes represented in the graded piece again lies in the kernel. -/
theorem mem_ker_mul_of_mem_flowTerm (G : Type*) [Group G] (n j : ℕ)
    (a b : Work.Shrinking.freeOperatorGroup G n)
    (ha : a ∈ flowTerm 2 G n j j) (hb : b ∈ flowTerm 2 G n j j) :
    (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨a, Subgroup.mem_top _⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      * (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨b, Subgroup.mem_top _⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      ∈ (flowQuotSucc 2 G n j j).ker := by
  rw [← map_mul]
  have h : (⟨a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))
      * ⟨b, Subgroup.mem_top _⟩ = ⟨a * b, Subgroup.mem_top _⟩ := rfl
  rw [h]
  exact mem_ker_of_mem_flowTerm G n j (a * b) ((flowTerm 2 G n j j).mul_mem ha hb)

/-- **The diagonal graded step follows from `DiagonalCore`.**  This isolates the remaining input:
given that the two witness families generate the anti-fixed part of `E(j,j)`, the target holds,
because each generator is a norm lying in the central graded piece. -/
theorem gradedStep_diagonal_of_core (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hcore : ∀ j : ℕ, 2 ≤ j → DiagonalCore G n j δ) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  intro j hj c hc hanti
  refine closure_is_deltaDifference_of_mem_ker G n j δ hδ
    (orbitSumFamily G n j δ ∪ pairedCommutatorFamily G n j δ) ?_ ?_ c (hcore j hj c hc hanti)
  · rintro s (hs | hs)
    · obtain ⟨x, rfl⟩ := hs
      have hmem : ∀ (w : Fin j → Work.Shrinking.freeOperatorGroup G n),
          prop5.commWord j w ∈ flowTerm 2 G n j j := by
        intro w
        rw [flowTerm, refinedTerm]
        refine Subgroup.mem_sup_left ⟨?_, prop5.commWord_mem_lowerCentralSeries j w⟩
        have h := prop5.pow_mem_pSeries 2 j 0 (by omega : 1 ≤ j) (prop5.commWord j w)
          (prop5.commWord_mem_lowerCentralSeries j w)
        simpa using h
      exact mem_ker_mul_of_mem_flowTerm G n j (prop5.commWord j (fun i => δ • x i))
        (prop5.commWord j x) (hmem _) (hmem _)
    · obtain ⟨u, hu, rfl⟩ := hs
      exact mem_ker_of_mem_flowTerm G n j ⁅u⁻¹, (δ • u)⁻¹⁆ hu
  · rintro s (hs | hs)
    · obtain ⟨x, rfl⟩ := hs
      exact ⟨QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨prop5.commWord j x, Subgroup.mem_top _⟩, (commWord_norm_orbit_aux G n j δ hδ (by omega : 1 ≤ j) x).symm⟩
    · obtain ⟨u, -, rfl⟩ := hs
      exact pairedCommutator_is_delta_difference G n j δ hδ u

/-! ## The `δ`-paired commutators depend on `y ∈ P_m` only through `P_m/P_{m+1}`

The `δ`-paired witness `y * (δ • y)` of the graded step is attached to `y ∈ P_m` (the `m`-th term of
the descending `2`-central series, `P_i = pCentralSeries 2 F (i-1)`).  Here we record that
replacing `y` by `y * t` with `t ∈ P_{m+1}` changes `ν(y * (δ • y)) = ⁅y⁻¹, (δ • y)⁻¹⁆` only by an
element of `P_{2m+1}`, i.e. only by an element whose image in the graded layer
`γ_{2m}/(γ_{2m}²γ_{2m+1})` is trivial.  This is the "quadratic form" well-definedness of the pairing
`y ↦ ⁅y⁻¹, (δ • y)⁻¹⁆` on the layer `P_m/P_{m+1}`, and it is what allows the pairing to be indexed
by that layer. -/

/-- **`DiagonalCore` from its odd and even halves.**  For odd `j` the orbit-sum family alone generates
the anti-fixed part (see `SSGRoute/diagonalCore_odd`), and for even `j = 2m`, `m ≥ 1`, the two
witness families (orbit sums together with the `δ`-paired commutators) do. -/
theorem diagonalCore_of_odd_even (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hodd : ∀ j : ℕ, Odd j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        c ∈ Subgroup.closure (orbitSumFamily G n j δ))
    (heven : ∀ m : ℕ, 1 ≤ m → DiagonalCore G n (2 * m) δ) :
    ∀ j : ℕ, 2 ≤ j → DiagonalCore G n j δ := by
  intro j hj
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | hjodd
  · simpa [hm, two_mul] using heven m (by omega)
  · intro c hc hanti
    exact Subgroup.closure_mono Set.subset_union_left (hodd j hjodd c hc hanti)

/-- **The diagonal graded step from the odd and even halves of `DiagonalCore`.** -/
theorem gradedStep_diagonal_of_odd_even (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hodd : ∀ j : ℕ, Odd j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        c ∈ Subgroup.closure (orbitSumFamily G n j δ))
    (heven : ∀ m : ℕ, 1 ≤ m → DiagonalCore G n (2 * m) δ) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e :=
  gradedStep_diagonal_of_core G n δ hδ (diagonalCore_of_odd_even G n δ hδ hodd heven)

/-! ## The target from the workspace's designated remaining input

`Submission/Work/SSGRoute/freeGroup_refinedTerm_lifting.lean` assembles the *anti-fixed-lift*
property `hlift` of `diagonal_of_antifixed_lifts` from the single remaining input

`LiftingAux.GradedStep` : for `N ◁ F` fully invariant with `P_k ≤ N`, every anti-fixed element of
the image of `P_{k-1}` in `F ⧸ N` is a norm

(the cases `k ≤ 3` are proved in `Submission/Work/SSGRoute/refinedTerm_graded_norm.lean`, using the
abelian and class-`2` layers; `k ≥ 4` is open).  Combined with `diagonal_of_antifixed_lifts`, this
gives the target from `LiftingAux.GradedStep`. -/
universe u

theorem gradedStep_diagonal_of_liftingAux (G : Type u) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (hgraded : LiftingAux.GradedStep.{u}) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  classical
  refine diagonal_of_antifixed_lifts δ hδ hδ1 ?_
  intro j _ x hx
  have htau : tauSucc j j = (j + 1, 1) := tauSucc_of_le (le_refl j)
  have hflow : flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
      = refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) 1 := by
    rw [htau, flowTerm]
  have hσ : ∀ y : Fin n × G, basisPerm G n δ (basisPerm G n δ y) = y :=
    basisPerm_involutive G n δ hδ
  have hfree : ∀ y : Fin n × G, basisPerm G n δ y ≠ y := basisPerm_ne_self G n δ hδ1
  haveI hfin : Finite (Fin n × G) := inferInstance
  have hlift := LiftingAux.freeGroup_refinedTerm_lifting_finite (hgraded := hgraded)
    (X := Fin n × G) (basisPerm G n δ) hσ hfree (j + 1) 1
  rw [smul_eq_freeGroupCongr δ x, hflow] at hx
  obtain ⟨u, hu, hfix⟩ := hlift x hx
  refine ⟨u, ?_, ?_⟩
  · rwa [hflow]
  · rw [smul_eq_freeGroupCongr δ (x * u)]
    exact hfix

/-- **The diagonal graded step from the `p`-central (`unrefined`) anti-fixed lifting step.**

This isolates the *honest* surviving input of the diagonal graded step.  By
`Work.CohomologicalShrinking.refinedTerm_one` the refined term used by the diagonal instance is the
**unrefined** `2`-central term, `flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 = pSeries 2 F (j+1)`;
so the only input needed is the anti-fixed lifting statement for the terms `pSeries 2 F (j+1)`
(equivalently: the minimal-`N` form `Work.SSGRoute.LayerNormStatement (j-1)` of the layer
`P_{j-1}/P_j` — *not* the universal-`N` quantifier, and *not* the refined terms `(i,j)` with
`i > j`, both of which are refuted in the workspace).

Every `x` with `(δ • x) * x ∈ pSeries 2 F (j+1)` can be adjusted, inside that term, to an exactly
anti-fixed element `x * u`. -/
theorem gradedStep_diagonal_of_pSeries_lifting (G : Type*) [Group G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1)
    (hlift : ∀ j : ℕ, 2 ≤ j → ∀ x : Work.Shrinking.freeOperatorGroup G n,
      (δ • x) * x ∈ Work.CohomologicalShrinking.pSeries 2
          (Work.Shrinking.freeOperatorGroup G n) (j + 1) →
      ∃ u ∈ Work.CohomologicalShrinking.pSeries 2
          (Work.Shrinking.freeOperatorGroup G n) (j + 1),
        (δ • (x * u)) * (x * u) = 1) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
        flowQuotSucc 2 G n j j c = 1 →
        flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2,
          c = (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ e)⁻¹ * e := by
  classical
  refine diagonal_of_antifixed_lifts δ hδ hδ1 ?_
  intro j hj x hx
  have htau : tauSucc j j = (j + 1, 1) := tauSucc_of_le (le_refl j)
  have hflow : flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
      = refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) 1 := by
    rw [htau, flowTerm]
  rw [smul_eq_freeGroupCongr δ x, hflow] at hx
  rw [refinedTerm_one] at hx
  obtain ⟨u, hu, hfix⟩ := hlift j hj x hx
  refine ⟨u, ?_, ?_⟩
  · rw [hflow, refinedTerm_one]
    exact hu
  · rw [smul_eq_freeGroupCongr δ (x * u)]
    exact hfix

/-! ## The corrected weight of the `δ`-paired witnesses (the even case `j = 2k`)

For even `j = 2k` the relevant "paired" witnesses are `A * (δ • A)` with `A` of *weight* `k`, i.e.
`A ∈ γ_k = lowerCentralSeries (k-1)`, and **not** merely `A ∈ P_k` (the `k`-th `2`-central term).
With the weight-matched choice the norm

  `Ψ(A * δA) = ⁅A⁻¹, (δA)⁻¹⁆`

lies in `⁅γ_k, γ_k⁆ ≤ γ_{2k}`, hence in the graded piece `E(2k,2k) = γ_{2k}·P_{2k+1}/P_{2k+1}`: the
class of the witness is an honest element of the layer.  (For `A ∈ P_2 ∖ γ_2`, e.g. `A = a²b²`, the
norm lands in `[P_2,P_2] ⊆ P_3`, which is *not* contained in `γ_4·P_5`; this is the "correction"
recorded in `GRADEDSTEP_DIAGONAL_FOUR_DIAGNOSIS.md`.  For the pair of *different* `δ`-orbits the
weight-matched element `A = ⁅x,y⁆ ∈ γ_2` does give a valid witness, e.g. `A = ⁅a,c⁆` for the cross
pair `(a,c)` in `F(4)` with `δa = b`, `δc = d`.) -/

/-- **The `δ`-paired commutator of a weight-`k` element lies in the `2k`-th term of the lower
central series.**  For any endomorphism `Φ` of a group and `A ∈ γ_k`
(`lowerCentralSeries (k-1)` in Mathlib's indexing) the commutator `⁅A⁻¹, (ΦA)⁻¹⁆` lies in
`γ_{2k} = lowerCentralSeries (2k-1)`. -/
theorem commutator_paired_mem_lowerCentralSeries {F : Type*} [Group F] (Φ : F →* F) (k : ℕ)
    (hk : 1 ≤ k) (A : F) (hA : A ∈ (⊤ : Subgroup F).lowerCentralSeries (k - 1)) :
    ⁅A⁻¹, (Φ A)⁻¹⁆ ∈ (⊤ : Subgroup F).lowerCentralSeries (2 * k - 1) := by
  have hA' : A⁻¹ ∈ (⊤ : Subgroup F).lowerCentralSeries (k - 1) := Subgroup.inv_mem _ hA
  have hB' : (Φ A)⁻¹ ∈ (⊤ : Subgroup F).lowerCentralSeries (k - 1) :=
    Subgroup.inv_mem _ (LiftingAux.map_lowerCentralSeries_le Φ (k - 1)
      (Subgroup.mem_map_of_mem Φ hA))
  have h3 := Subgroup.commutator_mem_commutator hA' hB'
  have h4 := Work.SSGRoute.prop5.commutator_lowerCentralSeries_le F (k - 1) (k - 1) h3
  rwa [show (k - 1) + (k - 1) + 1 = 2 * k - 1 from by omega] at h4

/-- **The weight-matched `δ`-paired witness lies in the graded piece `E(2k,2k)`.**

For the free `2`-central operator group `F(n)` with involution `δ • ·` (`δ * δ = 1`) and
`A ∈ γ_k = lowerCentralSeries (k-1)`, the commutator `⁅A⁻¹, (δ • A)⁻¹⁆` — which is the norm
`Ψ(A * (δ • A))` of the paired element `A * (δ • A)` (`normMap_self_mul_self`) — lies in the refined
term `F(n)^{(2k,2k)} = (P_{2k} ∩ γ_{2k})P_{2k+1}`; hence its class lies in the graded piece
`E(2k,2k)`. -/
theorem pairedCommutator_mem_flowTerm_self {G : Type*} [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (k : ℕ) (hk : 1 ≤ k) (A : Work.Shrinking.freeOperatorGroup G n)
    (hA : A ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (k - 1)) :
    ⁅A⁻¹, (δ • A)⁻¹⁆ ∈ flowTerm 2 G n (2 * k) (2 * k) := by
  have hmem : ⁅A⁻¹, (δ • A)⁻¹⁆ ∈
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (2 * k - 1) :=
    commutator_paired_mem_lowerCentralSeries
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      k hk A hA
  have hps : ⁅A⁻¹, (δ • A)⁻¹⁆ ∈
      Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (2 * k) :=
    Work.ProP.lowerCentralSeries_le_pCentralSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (2 * k - 1) hmem
  have hcs : ⁅A⁻¹, (δ • A)⁻¹⁆ ∈
      Work.CohomologicalShrinking.centralSeries (Work.Shrinking.freeOperatorGroup G n) (2 * k) :=
    hmem
  exact Subgroup.mem_sup_left (show ⁅A⁻¹, (δ • A)⁻¹⁆ ∈
      Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (2 * k) ⊓
      Work.CohomologicalShrinking.centralSeries (Work.Shrinking.freeOperatorGroup G n) (2 * k)
      from ⟨hps, hcs⟩)

/-- **The weight-matched `δ`-paired witnesses are admissible witnesses of the diagonal step.**

For even `j = 2k`, `A ∈ γ_k = lowerCentralSeries (k-1)` gives
`⁅A⁻¹, (δ • A)⁻¹⁆ ∈ F(n)^{(2k,2k)}` (`pairedCommutator_mem_flowTerm_self`), so its class in
`Q_{(2k+1,1)}` belongs to the `δ`-paired commutator family `pairedCommutatorFamily`. -/
theorem weightMatched_paired_mem_family {G : Type*} [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (k : ℕ) (hk : 1 ≤ k) (A : Work.Shrinking.freeOperatorGroup G n)
    (hA : A ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (k - 1)) :
    (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc (2 * k) (2 * k)).1
          (tauSucc (2 * k) (2 * k)).2).subgroupOf ⊤)
        ⟨⁅A⁻¹, (δ • A)⁻¹⁆, Subgroup.mem_top _⟩ :
        flowQuotient 2 G n (tauSucc (2 * k) (2 * k)).1 (tauSucc (2 * k) (2 * k)).2)
      ∈ pairedCommutatorFamily G n (2 * k) δ := by
  exact ⟨A, pairedCommutator_mem_flowTerm_self (G := G) n δ hδ k hk A hA, rfl⟩

/-- **The even case of the diagonal graded step, from its layer statement with the weight-matched
`δ`-paired witnesses.**  For `j = 2k`, `k ≥ 1`: if every anti-fixed element `c` of the graded piece
`E(2k,2k)` lies in the subgroup generated by the orbit sums of the layer together with the classes of
the weight-matched paired commutators `⁅A⁻¹, (δ • A)⁻¹⁆`, `A ∈ γ_k`, then `DiagonalCore` holds at
`2k`, hence the diagonal step.  This isolates the layer computation (the hard input of the even
case) from the group-theoretic weight bookkeeping. -/
theorem diagonalCore_even_of_pairedWitness {G : Type*} [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (k : ℕ) (hk : 1 ≤ k)
    (hgen : ∀ c : flowQuotient 2 G n (tauSucc (2 * k) (2 * k)).1
          (tauSucc (2 * k) (2 * k)).2,
        flowQuotSucc 2 G n (2 * k) (2 * k) c = 1 →
        flowAction 2 G n (tauSucc (2 * k) (2 * k)).1 (tauSucc (2 * k) (2 * k)).2 δ c = c⁻¹ →
        c ∈ Subgroup.closure (orbitSumFamily G n (2 * k) δ ∪
          ((fun A => QuotientGroup.mk' ((flowTerm 2 G n (tauSucc (2 * k) (2 * k)).1
              (tauSucc (2 * k) (2 * k)).2).subgroupOf ⊤)
                ⟨⁅A⁻¹, (δ • A)⁻¹⁆, Subgroup.mem_top _⟩) ''
            ((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (k - 1))))) :
    DiagonalCore G n (2 * k) δ := by
  intro c hker hanti
  refine Subgroup.closure_mono ?_ (hgen c hker hanti)
  intro y hy
  rcases hy with h | ⟨A, hA, rfl⟩
  · exact Or.inl h
  · exact Or.inr (weightMatched_paired_mem_family (G := G) n δ hδ k hk A hA)

/-- **The diagonal instances `(j,j)`, `j ≥ 2`, of the `p = 2` graded step** (Schmidt–Wingberg
Step 1, clause (B) at `p = 2`).

For a finite group `G`, an involution `δ ∈ G` with `δ ≠ 1`, `n ∈ ℕ`, and every `j ≥ 2`: every
anti-fixed element `c` of the kernel `E(j,j) = ker(Q_{(j+1,1)} → Q_{(j,j)})` is a `δ`-difference in
the ambient group `Q_{(j+1,1)} = F(n)/P_{j+1}`.

This is the sub-family `i = j` of the family `Work.SSGRoute.gradedStep_j_ge_two`; the general member
`(i,j)`, `i > j`, is obtained from it through the `2^(i-j)`-power isomorphism
`E(j,j) → E(i,j)`, `[u] ↦ [u^(2^(i-j))]` (a separate reduction lemma, delegated in parallel).

Mathematical content. `E(j,j)` is the top graded piece of `P_j/P_{j+1}`, generated by the weight-`j`
commutators `⁅x₁,…⁅x_{j-1},x_j⁆…⁆` of the images of the free generators of `F(n)`, on which `δ`
acts by permuting the generators `(a,g) ↦ (a, δg)` in free orbits.  The witness is built from the
identity `[g·Φ(g), Φ] = [g, Φ(g)] = g·[g,[g,Φ]]·g^{-1}` (where `Φ` is the automorphism of `F(n)`
induced by `δ`), applied to the "halves" of the monomials.  The strong form, with the witness
required inside `E(j,j)`, is FALSE (for `j = 2`, `n = 1`, `G = ℤ/2`, the graded piece
`E(2,2) ≅ 𝔽₂` carries the trivial `δ`-action, so `(1+δ)E(2,2) = 0`, while `[a,b]` is anti-fixed and
is `(δ(ab))⁻¹(ab)` in `Q_{(3,1)}`). -/
theorem gradedStep_diagonal (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hδ1 : δ ≠ 1) :
    ∀ (j : ℕ), 2 ≤ j →
      ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
          (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2,
        Work.SSGRoute.flowQuotSucc 2 G n j j c = 1 →
        Work.CohomologicalShrinking.flowAction 2 G n
            (Work.CohomologicalShrinking.tauSucc j j).1
            (Work.CohomologicalShrinking.tauSucc j j).2 δ c = c⁻¹ →
        ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
              (Work.CohomologicalShrinking.tauSucc j j).1
              (Work.CohomologicalShrinking.tauSucc j j).2,
          c = (Work.CohomologicalShrinking.flowAction 2 G n
                (Work.CohomologicalShrinking.tauSucc j j).1
                (Work.CohomologicalShrinking.tauSucc j j).2 δ e)⁻¹ * e := by sorry

end Work.SSGRoute
