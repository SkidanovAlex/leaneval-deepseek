import Mathlib
import Submission.Work.CohomologicalShrinking.Semidirect
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

open Work.CohomologicalShrinking
open Work.Shrinking

/-!
# `F(m)/F(m)^2 ≅ N/N^p[N,N]` for `N = F(m)/F(m)^{(i,j)}`, `i ≥ 2`

Schmidt–Wingberg's Proposition 6 is proved for the quotients `F(m)/F(m)^{(i,j)} ⋊ G`, and the
coefficient module of the shrinking procedure at the bottom level `τ = (1,1)` is
`F(m)/F(m)^2 = F(m)/F(m)^p[F(m),F(m)]`.  In the semidirect-product setting that module has to
be compared with the bottom graded piece `N/N^p[N,N]` of the *normal subgroup*
`N = F(m)/F(m)^{(i,j)}` of `Γ = F(m)/F(m)^{(i,j)} ⋊ G` (this is the identification used for the
Hochschild–Serre computation of `H₁(Γ, E(m,τ) ⊗ T)` and of `Ĥ^{-2}(Γ, E(m,τ) ⊗ T)`).

The comparison rests on a general (and elementary) fact.  For *any* surjective homomorphism
`f : F ↠ N` whose kernel lies in `F^p[F,F] = F_2`, the induced map
`F/F^p[F,F] → N/N^p[N,N]` is an isomorphism: indeed `f(F^p[F,F]) = N^p[N,N]`
(`map_pCentralSeries_surjective`), and the kernel of the induced map is
`f^{-1}(N^p[N,N])/F^p[F,F] = (F^p[F,F]·ker f)/F^p[F,F] = F^p[F,F]/F^p[F,F]`, which is trivial
because `ker f ≤ F^p[F,F]`.

Here `N` is realized as the subgroup `flowNormal p G m i j ≤ Γ`, and the relevant surjection is
`F(m) →* N`, `x ↦` the class of `x` under the canonical identification
`F(m)/F(m)^{(i,j)} ≃* N` (`flowNormalEquiv`).  Its kernel is `F(m)^{(i,j)}`, which lies in
`F(m)^p[F(m),F(m)]` as soon as `i ≥ 2`: both `F(m)_i` and `F(m)_{i+1}` are contained in
`F(m)_2`, and `F(m)^{(i,j)} = (F(m)_i ∩ F(m)^j)F(m)_{i+1}`.

The two composite constructions are recorded separately:

* `pCentralQuotient_zero_mulEquiv_of_surjective` — the abstract isomorphism of the quotients
  `P/P^p[P,P]` for a surjection with kernel in `P^p[P,P]`;
* `flowNormalSurj`, `flowNormalSurj_surjective`, `flowNormalSurj_ker_le` — the concrete
  surjection `F(m) ↠ N` and its kernel;
* `flowNormalSquareEquiv` — the target statement.
-/

universe u

/-! ## The refined term lies in the second term of the `p`-central series when `i ≥ 2` -/

/-- For `i ≥ 2` the refined term `F(m)^{(i,j)} = (F(m)_i ∩ F(m)^j)F(m)_{i+1}` is contained in
`F(m)^p[F(m),F(m)] = pCentralSeries p F(m) 1`.  Both `F(m)_i` (using `i ≥ 2`) and `F(m)_{i+1}`
are contained in `F(m)_2 = pCentralSeries p F(m) 1` because the `p`-central series is
descending. -/
theorem flowTerm_le_pCentralSeries_one (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (hi : 2 ≤ i) :
    flowTerm p G m i j ≤ pCentralSeries p (freeOperatorGroup G m) 1 := by
  rw [flowTerm, refinedTerm, pSeries, pSeries]
  exact sup_le (inf_le_left.trans (pCentralSeries_antitone p _ (by omega)))
    (pCentralSeries_antitone p _ (by omega))

/-! ## The first isomorphism theorem for `P/P^p[P,P]` -/

/-- **The bottom graded piece is invariant under quotients with kernel in it.**

If `f : F ↠ N` is a surjective group homomorphism with `ker f ≤ F^p [F,F] = F_2`, then the map
induced by `f` on the bottom graded pieces `F/F^p[F,F] → N/N^p[N,N]` is an isomorphism.

Surjectivity: `f` maps the `p`-central series of `F` onto that of `N`
(`map_pCentralSeries_surjective`).  Injectivity: if `f x ∈ N^p[N,N] = f(F^p[F,F])`, say
`f x = f y` with `y ∈ F^p[F,F]`, then `x y⁻¹ ∈ ker f ≤ F^p[F,F]`, whence `x ∈ F^p[F,F]`. -/
theorem pCentralQuotient_zero_mulEquiv_of_surjective {p : ℕ} {F N : Type*} [Group F] [Group N]
    (f : F →* N) (hf : Function.Surjective f)
    (hker : f.ker ≤ pCentralSeries p F 1) :
    Nonempty (pCentralQuotient p F 0 ≃* pCentralQuotient p N 0) := by
  -- the map induced on `⊤ ≤ F` by `f`
  let f' : (⊤ : Subgroup F) →* (⊤ : Subgroup N) :=
    { toFun := fun x => ⟨f x, Subgroup.mem_top x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hmap : (pCentralSeries p F 1).map f = pCentralSeries p N 1 :=
    map_pCentralSeries_surjective p f hf 1
  have hle : (pCentralSeries p F 1).subgroupOf (⊤ : Subgroup F) ≤
      Subgroup.comap f' ((pCentralSeries p N 1).subgroupOf (⊤ : Subgroup N)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    have hx' : f ↑x ∈ Subgroup.map f (pCentralSeries p F 1) := Subgroup.mem_map_of_mem f hx
    rw [hmap] at hx'
    exact hx'
  refine ⟨MulEquiv.ofBijective (QuotientGroup.map _ _ f' hle) ⟨?_, ?_⟩⟩
  · -- injectivity
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
    have hproj : (↑(f' x) : (⊤ : Subgroup N) ⧸
        ((pCentralSeries p N 1).subgroupOf (⊤ : Subgroup N))) = ↑(f' y) :=
      (QuotientGroup.map_mk' _ _ f' hle x).symm.trans
        (hab.trans (QuotientGroup.map_mk' _ _ f' hle y))
    have hmem : (f' x)⁻¹ * f' y ∈ (pCentralSeries p N 1).subgroupOf (⊤ : Subgroup N) :=
      QuotientGroup.eq.mp hproj
    have hfxy : f ((x : F)⁻¹ * (y : F)) ∈ pCentralSeries p N 1 := by
      have h : ((f' x : (⊤ : Subgroup N)) : N)⁻¹ * ((f' y : (⊤ : Subgroup N)) : N)
          ∈ pCentralSeries p N 1 := Subgroup.mem_subgroupOf.mp hmem
      have h1 : ((f' x : (⊤ : Subgroup N)) : N) = f (x : F) := rfl
      have h2 : ((f' y : (⊤ : Subgroup N)) : N) = f (y : F) := rfl
      rw [h1, h2, ← map_inv, ← map_mul] at h
      exact h
    obtain ⟨z, hz, hzf⟩ : ∃ z ∈ pCentralSeries p F 1, f z = f ((x : F)⁻¹ * (y : F)) := by
      rw [← hmap] at hfxy
      exact Subgroup.mem_map.mp hfxy
    have hker2 : z⁻¹ * ((x : F)⁻¹ * (y : F)) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzf, inv_mul_cancel]
    have hmem2 : z⁻¹ * ((x : F)⁻¹ * (y : F)) ∈ pCentralSeries p F 1 := hker hker2
    have hmem3 : (x : F)⁻¹ * (y : F) ∈ pCentralSeries p F 1 := by
      have h3 : z * (z⁻¹ * ((x : F)⁻¹ * (y : F))) ∈ pCentralSeries p F 1 := mul_mem hz hmem2
      rwa [mul_inv_cancel_left] at h3
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((((x : (⊤ : Subgroup F))⁻¹ * y : (⊤ : Subgroup F))) : F) =
        (x : F)⁻¹ * (y : F) := rfl
    rw [h1]
    exact hmem3
  · -- surjectivity
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, hx⟩ := hf y₀.1
    refine ⟨QuotientGroup.mk' _ ⟨x, Subgroup.mem_top x⟩, ?_⟩
    exact (QuotientGroup.map_mk' _ _ f' hle ⟨x, Subgroup.mem_top x⟩).trans
      (congrArg (QuotientGroup.mk' ((pCentralSeries p N 1).subgroupOf (⊤ : Subgroup N)))
        (Subtype.ext hx))

/-! ## From `MulEquiv` to `LinearEquiv` over `𝔽_p`

Any additive homomorphism between `ℤ/pℤ`-modules is `ℤ/pℤ`-linear (`ZMod.map_smul`), because
`ℤ → ℤ/pℤ` is surjective; we only need this for the additive equivalence underlying the
`MulEquiv` above. -/

/-- An additive equivalence between `ℤ/pℤ`-modules is `ℤ/pℤ`-linear. -/
noncomputable def addEquivToZModLinearEquiv {p : ℕ} {M M₁ : Type*} [AddCommGroup M]
    [AddCommGroup M₁] [Module (ZMod p) M] [Module (ZMod p) M₁] (e : M ≃+ M₁) :
    M ≃ₗ[ZMod p] M₁ where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := fun c x => ZMod.map_smul (e : M →+ M₁) c x

/-- The isomorphism of the bottom graded pieces `F/F^p[F,F] ≅ N/N^p[N,N]` induced by a
surjective homomorphism `f : F ↠ N` with `ker f ≤ F^p[F,F]`, as an `𝔽_p`-linear equivalence. -/
theorem pCentralQuotient_zero_linearEquiv_of_surjective {p : ℕ} {F N : Type*} [Group F] [Group N]
    (f : F →* N) (hf : Function.Surjective f)
    (hker : f.ker ≤ pCentralSeries p F 1) :
    Nonempty (Additive (pCentralQuotient p F 0) ≃ₗ[ZMod p]
      Additive (pCentralQuotient p N 0)) := by
  obtain ⟨e⟩ := pCentralQuotient_zero_mulEquiv_of_surjective (p := p) f hf hker
  exact ⟨addEquivToZModLinearEquiv (MulEquiv.toAdditive e)⟩

/-! ## The surjection `F(m) ↠ F(m)/F(m)^{(i,j)}` -/

/-- The canonical surjection `F(m) ↠ N = F(m)/F(m)^{(i,j)}`, where `N` is realized as the normal
subgroup `flowNormal p G m i j` of `Γ = F(m)/F(m)^{(i,j)} ⋊ G`: it is the composite of the
quotient map `F(m) ↠ ⊤ ⧸ F(m)^{(i,j)} = flowQuotient p G m i j` with the identification
`flowNormalEquiv p G m i j` of that quotient with `N`. -/
noncomputable def flowNormalSurj (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    freeOperatorGroup G m →* ↥(flowNormal p G m i j) :=
  ((flowNormalEquiv p G m i j).toMonoidHom).comp <|
    (QuotientGroup.mk'
      ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (freeOperatorGroup G m)))).comp
      (Subgroup.topEquiv.symm : freeOperatorGroup G m ≃*
        (⊤ : Subgroup (freeOperatorGroup G m))).toMonoidHom

/-- The map `F(m) ↠ N` is surjective. -/
theorem flowNormalSurj_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowNormalSurj p G m i j) := by
  intro y
  obtain ⟨a, ha⟩ := (flowNormalEquiv p G m i j).surjective y
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (freeOperatorGroup G m))) a
  obtain ⟨c, hc⟩ := (Subgroup.topEquiv.symm : freeOperatorGroup G m ≃*
    (⊤ : Subgroup (freeOperatorGroup G m))).surjective b
  have hc' : (Subgroup.topEquiv.symm : freeOperatorGroup G m ≃*
      (⊤ : Subgroup (freeOperatorGroup G m))).toMonoidHom c = b := hc
  have ha' : (flowNormalEquiv p G m i j).toMonoidHom a = y := ha
  refine ⟨c, ?_⟩
  rw [flowNormalSurj, MonoidHom.comp_apply, MonoidHom.comp_apply, hc', hb, ha']

/-- The kernel of `F(m) ↠ N` is `F(m)^{(i,j)}`; for `i ≥ 2` this is contained in
`F(m)^p[F(m),F(m)]`, the hypothesis of `pCentralQuotient_zero_linearEquiv_of_surjective`. -/
theorem flowNormalSurj_ker_le (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (hi : 2 ≤ i) :
    (flowNormalSurj p G m i j).ker ≤ pCentralSeries p (freeOperatorGroup G m) 1 := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hmk : QuotientGroup.mk'
      ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (freeOperatorGroup G m)))
      ((Subgroup.topEquiv.symm : freeOperatorGroup G m ≃*
        (⊤ : Subgroup (freeOperatorGroup G m))) x) = 1 := by
    apply (flowNormalEquiv p G m i j).injective
    rw [map_one]
    simpa [flowNormalSurj] using hx
  have hmem : ((Subgroup.topEquiv.symm : freeOperatorGroup G m ≃*
      (⊤ : Subgroup (freeOperatorGroup G m))) x) ∈
      (flowTerm p G m i j).subgroupOf (⊤ : Subgroup (freeOperatorGroup G m)) :=
    (QuotientGroup.eq_one_iff _).mp hmk
  rw [Subgroup.mem_subgroupOf] at hmem
  rw [Subgroup.topEquiv_symm_apply_coe] at hmem
  exact flowTerm_le_pCentralSeries_one p G m i j hi hmem

/-! ## The target statement -/

theorem flowNormalSquareEquiv (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j m : ℕ)
    (hi : 2 ≤ i) :
    Nonempty (squareQuotient p G m ≃ₗ[ZMod p]
      Additive (Work.Shrinking.pCentralQuotient p (flowNormal p G m i j) 0)) := by
  obtain ⟨e⟩ := pCentralQuotient_zero_linearEquiv_of_surjective (p := p)
    (flowNormalSurj (G := G) p m i j)
    (flowNormalSurj_surjective p G m i j) (flowNormalSurj_ker_le p G m i j hi)
  exact ⟨e⟩

end Work.CohomologicalShrinking.flow
