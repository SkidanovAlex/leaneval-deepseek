import Mathlib
import Submission.Work.Whitney.capCycle
import Submission.Work.Whitney.ballPairMap
import Submission.Work.Whitney.ballPairMapDefs
import Submission.Work.Whitney.ballPairValSurj
import Submission.Work.Whitney.pushChain_ballPair_relativeCycle
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Whitney.coneMap_retraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The ball-pair map has degree one

The explicit cone map `Δᵖ → Y × Dᵖ` (the "distance to the boundary normalised" radial map of
`Submission/Work/Whitney/ballPairMapDefs.lean`) maps the boundary of the simplex onto the fibre
sphere `DiscB Y p = Y × Sᵖ⁻¹` and the interior into the interior of the ball.  The content of this
file is that its **pushed fundamental chain is not a relative boundary**:

  `¬ ∃ W Z, IsSmallChain (DiscB Y p) ∅ Z ∧ ∂W = f_* [idSimplex p] + Z`,

i.e. the relative fundamental class of the pair `(Δᵖ, ∂Δᵖ)` survives the map.  Equivalently: the map
of pairs `(Δᵖ, ∂Δᵖ) → (Y × Dᵖ, DiscB Y p)` is **essential**.

The argument is a *retraction*: if `r : (Y × Dᵖ, DiscB Y p) → (Δᵖ, ∂Δᵖ)` is a continuous map of
pairs with `r ∘ f = id`, then applying `r_*` to a hypothetical relative filling `∂W = f_*[id] + Z`
produces a relative filling of `[id]` in the *source* pair (because `r_* Z` is carried by `∂Δᵖ`),
contradicting the nonvanishing of the relative class of the identity simplex in `(Δᵖ, ∂Δᵖ)`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-- The (topological) boundary of the standard simplex `Δᵖ`, as a set of points. -/
def simplexBdry (p : ℕ) : Set (stdSimplex ℝ (Fin (p+1))) :=
  {z | ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0}

/-! ## The explicit cone map -/

/-- The value of the cone map `Δᵖ → Y × Dᵖ`: the second component is the radial cone map
`Work.Whitney.ballPairVal`. -/
def coneMapVal (Y : Type) [Nonempty Y] (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    Y × Work.Thom.MBall p :=
  (Classical.arbitrary Y, ⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩)

/-- The cone map is continuous. -/
theorem continuous_coneMapVal (Y : Type) [TopologicalSpace Y] [Nonempty Y] (p : ℕ) :
    Continuous fun z : stdSimplex ℝ (Fin (p+1)) => coneMapVal Y p z :=
  Continuous.prodMk continuous_const
    (Continuous.subtype_mk (continuous_ballPairVal_simplex p)
      (fun z => ballPairVal_mem_ball p z))

/-- **The cone map** `Δᵖ → Y × Dᵖ`: the explicit map of pairs used by `ballPairDegreeOne`. -/
def coneMap (Y : Type) [TopologicalSpace Y] [Nonempty Y] (p : ℕ) :
    C(stdSimplex ℝ (Fin (p+1)), TopCat.of (Y × Work.Thom.MBall p)) :=
  ⟨fun z => coneMapVal Y p z, continuous_coneMapVal Y p⟩

@[simp]
theorem coneMap_apply (Y : Type) [TopologicalSpace Y] [Nonempty Y] (p : ℕ)
    (z : stdSimplex ℝ (Fin (p+1))) :
    coneMap Y p z = coneMapVal Y p z := rfl

/-- The cone map sends the boundary of the simplex into the fibre sphere. -/
theorem coneMap_mem_discB (Y : Type) [TopologicalSpace Y] [Nonempty Y] (p : ℕ)
    {z : stdSimplex ℝ (Fin (p+1))} (hz : ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0) :
    coneMap Y p z ∈ DiscB Y p :=
  (ballPairVal_mem_sph_iff p z).mpr hz

/-- The cone map sends the interior of the simplex into the interior of the ball. -/
theorem coneMap_not_mem_discB (Y : Type) [TopologicalSpace Y] [Nonempty Y] (p : ℕ)
    {z : stdSimplex ℝ (Fin (p+1))} (hz : ∀ i : Fin (p+1), (z : Fin (p+1) → ℝ) i ≠ 0) :
    coneMap Y p z ∉ DiscB Y p := by
  intro h
  obtain ⟨i, hi⟩ := (ballPairVal_mem_sph_iff p z).mp h
  exact hz i hi

/-! ## Pushing small chains forward along a map carrying `U` into `V` -/

/-- **If every simplex supported in `U` is mapped into `V`, then the pushforward of a `U`-small
chain is `V`-small.**  (Variant of `Work.Cohomology.pushChain_isSmallChain` in which only the
image of `U` — and not the image of the whole map — is required to lie in `V`.) -/
theorem pushChain_isSmallChain_of_mem {X Z : TopCat} (g : X ⟶ Z) {U : Set X} {V : Set Z}
    (hUV : ∀ x, x ∈ U → g x ∈ V) {n : ℕ} (c : (singularChains ℤ X).X n)
    (hc : IsSmallChain U ∅ c) : IsSmallChain V ∅ (pushChain X Z g n c) := by
  obtain ⟨c', rfl⟩ := hc
  refine isSmallChain_of_gen (Y := smallSSet U ∅) (n := n)
    ((smallToSing U ∅).f n ≫ pushChainHom X Z g n) ?_ c'
  intro σ
  obtain ⟨σ₁, hσ₁⟩ := σ
  have hσ₁' : IsSmall U ∅ σ₁ := hσ₁
  rw [isSmall_iff] at hσ₁'
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, smallToSing_gen]
  show IsSmallChain V ∅ (pushChain X Z g n (gen X n σ₁))
  rw [pushChain_gen]
  apply isSmallChain_gen
  rw [isSmall_iff]
  refine Or.inl ?_
  rw [sdMap_map X Z g n σ₁]
  rintro y ⟨z, rfl⟩
  refine hUV _ ?_
  rcases hσ₁' with h | h
  · exact h ⟨z, rfl⟩
  · exact absurd (h ⟨z, rfl⟩) (Set.notMem_empty _)

/-! ## The pushforward commutes with the differential -/

/-- The pushforward of chains along a continuous map commutes with the differential. -/
theorem pushChain_d (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (c : (singularChains ℤ X).X (n+1)) :
    (singularChains ℤ Y).d (n+1) n (pushChain X Y f (n+1) c)
      = pushChain X Y f n ((singularChains ℤ X).d (n+1) n c) :=
  congrArg (fun (g : (singularChains ℤ X).X (n+1) ⟶ (singularChains ℤ Y).X n) => g.hom c)
    (HomologicalComplex.Hom.comm (SSet.chainComplexMap (TopCat.toSSet.map f)
      (ModuleCat.of ℤ ℤ)) (n+1) n)

/-! ## The reduction -/

/-- **The reduction.**  Suppose `f : Δᵖ → Y × Dᵖ` admits a continuous retraction of pairs
`r : (Y × Dᵖ, DiscB Y p) → (Δᵖ, ∂Δᵖ)` (i.e. `r ∘ f = id` and `r` carries `DiscB Y p` into the
boundary of the simplex).  If the relative class of the identity simplex of `Δᵖ` is nonzero, then
the pushed fundamental chain `f_* [idSimplex p]` is not a relative boundary of the pair
`(Y × Dᵖ, DiscB Y p)`. -/
theorem not_relativeBoundary_of_retraction (Y : Type) [TopologicalSpace Y] [Subsingleton Y]
    [Nonempty Y] (p : ℕ)
    (f : C(stdSimplex ℝ (Fin (p+1)), TopCat.of (Y × Work.Thom.MBall p)))
    (r : C(TopCat.of (Y × Work.Thom.MBall p), TopCat.of (stdSimplex ℝ (Fin (p+1)))))
    (hrf : ∀ z : stdSimplex ℝ (Fin (p+1)), r (f z) = z)
    (hrA : ∀ q : Y × Work.Thom.MBall p, (q ∈ DiscB Y p) → r q ∈ simplexBdry p)
    (hsrc : ¬ ∃ (W : (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).X (p+1))
       (Z : (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).X p),
      IsSmallChain (simplexBdry p) (∅ : Set (stdSimplex ℝ (Fin (p+1)))) Z ∧
      (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).d (p+1) p W
        = gen (TopCat.of (stdSimplex ℝ (Fin (p+1)))) p (idSimplex p) + Z) :
    ¬ ∃ (W : (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).X (p+1))
       (Z : (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).X p),
      IsSmallChain (DiscB Y p) (∅ : Set (Y × Work.Thom.MBall p)) Z ∧
      (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).d (p+1) p W
        = pushChain (Delta p) (TopCat.of (Y × Work.Thom.MBall p)) (TopCat.ofHom f) p
            (gen (Delta p) p (idSimplex p)) + Z := by
  intro h
  obtain ⟨W, Z, hZ, hW⟩ := h
  -- `r` composed with `f` is the identity on `Δᵖ`
  have hcomp : TopCat.ofHom f ≫ TopCat.ofHom r = 𝟙 (Delta p) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact hrf z
  -- `pushChain r ∘ pushChain f` is the identity on the fundamental simplex
  have hkey : pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p
        (pushChain (Delta p) (TopCat.of (Y × Work.Thom.MBall p)) (TopCat.ofHom f) p
          (gen (Delta p) p (idSimplex p))) = gen (Delta p) p (idSimplex p) := by
    rw [pushChain_comp (Delta p) (TopCat.of (Y × Work.Thom.MBall p)) (Delta p)
      (TopCat.ofHom f) (TopCat.ofHom r) p (gen (Delta p) p (idSimplex p)), hcomp,
      pushChain_gen]
    congr 1
  -- the two descriptions of `r_* (∂W)` agree
  have h4 : (singularChains ℤ (Delta p)).d (p+1) p
        (pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) (p+1) W)
      = gen (Delta p) p (idSimplex p)
          + pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p Z := by
    have h1 := (pushChain_d (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p W).symm
    have h3 := congrArg
      (pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p) hW
    rw [map_add, hkey] at h3
    exact h1.symm.trans h3
  -- the pushed `Z` is carried by the boundary of the simplex
  have hZ' : IsSmallChain (simplexBdry p) (∅ : Set (stdSimplex ℝ (Fin (p+1))))
        (pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p Z) :=
    pushChain_isSmallChain_of_mem (TopCat.ofHom r) hrA Z hZ
  exact hsrc ⟨pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) (p+1) W,
    pushChain (TopCat.of (Y × Work.Thom.MBall p)) (Delta p) (TopCat.ofHom r) p Z, hZ', h4⟩

/-! ## The cone map of `ballPairMapDefs` has degree one -/

/-- **The pushed fundamental chain of the explicit cone map is not a relative boundary**, given
the nonvanishing of the relative class of the identity simplex of `Δᵖ`. -/
theorem not_relativeBoundary_coneMap (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (p : ℕ) (hp : 1 ≤ p)
    (hsrc : ¬ ∃ (W : (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).X (p+1))
       (Z : (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).X p),
      IsSmallChain (simplexBdry p) (∅ : Set (stdSimplex ℝ (Fin (p+1)))) Z ∧
      (singularChains ℤ (TopCat.of (stdSimplex ℝ (Fin (p+1))))).d (p+1) p W
        = gen (TopCat.of (stdSimplex ℝ (Fin (p+1)))) p (idSimplex p) + Z) :
    ¬ ∃ (W : (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).X (p+1))
       (Z : (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).X p),
      IsSmallChain (DiscB Y p) (∅ : Set (Y × Work.Thom.MBall p)) Z ∧
      (singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).d (p+1) p W
        = pushChain (Delta p) (TopCat.of (Y × Work.Thom.MBall p))
            (TopCat.ofHom (coneMap Y p)) p (gen (Delta p) p (idSimplex p)) + Z := by
  obtain ⟨r, hrf, hrA⟩ := coneMap_retraction Y p hp
  refine not_relativeBoundary_of_retraction Y p (coneMap Y p) r ?_ ?_ hsrc
  · intro z
    simpa [coneMap, coneMapVal, coneMap_apply] using hrf z
  · intro q hq
    simpa [simplexBdry] using hrA q hq

end

end Work.Whitney
