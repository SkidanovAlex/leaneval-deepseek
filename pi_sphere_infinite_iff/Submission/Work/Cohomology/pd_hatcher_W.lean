import Mathlib
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.mem_range_inclChains_of_image

/-!
# The Hatcher decomposition in the ambient open set `U ∪ V` (Hatcher, Lemma 3.36)

The target `Work.Cohomology.pd_hatcher_W` is the form of the Hatcher decomposition that the crux
square of the gluing step needs.  Given a homology class `c ∈ H_N(M)` (`M` Hausdorff), open sets
`U, V ⊆ M` and compact `K ⊆ U`, `L ⊆ V`, it produces a *relative* cycle
`γ ∈ C_N(U∪V, (U∪V)∖(K∪L))` representing the local fundamental class
`localFundClass N c (U∪V) (K∪L)`, together with a lift `ξ` of its underlying relative chain which
splits as `α₁ + α₂ + α₃` with

* `α₁` supported in `U ∖ L` (within `U ∪ V`), with `dα₁` supported outside `L`,
* `α₂` supported in `U ∩ V`,
* `α₃` supported in `V ∖ K` (within `U ∪ V`), with `dα₃` supported outside `K`.

## The proof

`Work.Cohomology.pd_hatcher_data` supplies a cycle `w` with `[w] = c` whose underlying chain splits
as `a + b + d + j` with the four summands supported in `U∖L`, `U∩V`, `V∖K` and `(K∪L)ᶜ`.  The last
summand lies in the complement of `K ∪ L`, so it is invisible in the relative chain complex of the
pair `(U∪V, (U∪V)∖(K∪L))`.

Since `U∖L`, `U∩V` and `V∖K` are all contained in `W := U ∪ V`, the chains `a`, `b`, `d` are in the
range of `C_*(W) ⟶ C_*(M)`; descending them along the retraction `chainRetract` of that inclusion
gives chains `α₁, α₂, α₃ ∈ C_N(W)` with `α₁ + α₂ + α₃` mapping to `a + b + d`.  The chains are
supported where required (`C_*(W) ⟶ C_*(M)` is injective, and the support is visible on the image
in `C_*(M)`: `chainRetract_mem_range_of_subset`), and so are their boundaries
(`mem_range_inclChains_of_image`).  Finally `d(α₁+α₂+α₃)` maps to `d(a+b+d) = -dj`, which is
supported in `(K∪L)ᶜ` inside `W`, so `π(α₁+α₂+α₃)` is a relative cycle.

The class condition is `relCycle_homologyMap_eq_relLocClass`: the image of the relative cycle under
the excision isomorphism `H_N(W, W∖(K∪L)) ≅ H_N(M, M∖(K∪L))` has underlying chain the image of
`a+b+d`, and since `w = a+b+d+j` with `j` a relative cycle of `(M, M∖(K∪L))`, this is the local
class of `c`, i.e. precisely `relLocClass`; against the definition of `localFundClass` this gives
the class of `γ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Support plumbing for the descent to a subspace -/

/-- The retraction `chainRetract` of the inclusion of singular chains is a left inverse of the
inclusion, on the nose. -/
theorem chainRetract_inclChains_apply {X : TopCat} (A : Set X) (n : ℕ)
    (y : (singularChains ℤ (TopCat.of A)).X n) :
    (chainRetract ℤ X A n).hom (((inclChains X A).f n).hom y) = y := by
  have hspec : (ModuleCat.Hom.hom (chainRetract ℤ X A n)).comp
      (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n)) = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X A n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have h2 : ((ModuleCat.Hom.hom (chainRetract ℤ X A n)).comp
      (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n))) y = y := by
    rw [hspec]; rfl
  exact h2

/-- The inclusion of the singular chains of a subspace is injective. -/
theorem inclChains_f_injective (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((inclChains X A).f n)) := by
  intro x y hxy
  calc x = (chainRetract ℤ X A n).hom (((inclChains X A).f n).hom x) :=
        (chainRetract_inclChains_apply A n x).symm
    _ = (chainRetract ℤ X A n).hom (((inclChains X A).f n).hom y) := by rw [hxy]
    _ = y := chainRetract_inclChains_apply A n y

/-- The retraction of the inclusion is a section on the range of the inclusion. -/
theorem chainRetract_of_mem_range {X : TopCat} {A : Set X} {n : ℕ}
    {x : (singularChains ℤ X).X n}
    (hx : x ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains X A).f n))) :
    (inclChains X A).f n ((chainRetract ℤ X A n).hom x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [chainRetract_inclChains_apply A n y]

/-- **Descending a chain supported in `A ⊆ B` to the chains of `B`.**  If `x` is the image of a
chain of `C_*(A)` and `A ⊆ B`, then the descent of `x` to `C_*(B)` is a chain supported in the
trace of `A` on `B` (within the subspace `B`). -/
theorem chainRetract_mem_range_of_subset {X : TopCat} {A B : Set X} (hAB : A ⊆ B) {n : ℕ}
    {x : (singularChains ℤ X).X n}
    (hx : x ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains X A).f n))) :
    (chainRetract ℤ X B n).hom x
      ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains (TopCat.of B) (pdTr B A)).f n)) := by
  obtain ⟨y, rfl⟩ := hx
  rw [← inclChainsSub_comp X A B hAB, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [chainRetract_inclChains_apply B n (((inclChainsSub X A B hAB).f n).hom y)]
  exact inclChainsSub_mem_range hAB n y

/-! ## The cycle associated with a chain of zero boundary -/

/-- The element of `LinearMap.ker` of the differential associated with a chain of zero boundary. -/
noncomputable def cycleK {R : Type} [Ring R] {C : ChainComplex (ModuleCat R) ℕ} (n : ℕ) (x : C.X n)
    (hx : C.d n (n - 1) x = 0) : (C.sc n).moduleCatLeftHomologyData.K :=
  ⟨x, by
    have hnext : (ComplexShape.down ℕ).next n = n - 1 := by cases n <;> simp
    have hs : (C.sc n).g x = 0 := by
      show C.d n ((ComplexShape.down ℕ).next n) x = 0
      rw [hnext]; exact hx
    exact hs⟩

/-- **The cycle associated with a chain of zero boundary.** -/
noncomputable def cycleOf {R : Type} [Ring R] {C : ChainComplex (ModuleCat R) ℕ} (n : ℕ) (x : C.X n)
    (hx : C.d n (n - 1) x = 0) : C.cycles n :=
  (C.sc n).moduleCatCyclesIso.inv (cycleK n x hx)

/-- The underlying chain of `cycleOf` is the original chain. -/
theorem iCycles_cycleOf {R : Type} [Ring R] {C : ChainComplex (ModuleCat R) ℕ} (n : ℕ) (x : C.X n)
    (hx : C.d n (n - 1) x = 0) : C.iCycles n (cycleOf n x hx) = x := by
  show (C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv (cycleK n x hx)) = x
  rw [← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

/-- The projection to the relative chains kills the chains supported in the subspace. -/
theorem cokernel_π_f_apply_eq_zero {X : TopCat} {A : Set X} (n : ℕ)
    (y : (singularChains ℤ (TopCat.of A)).X n) :
    ((cokernel.π (inclChains X A)).f n) ((inclChains X A).f n y) = 0 := by
  rw [← ModuleCat.comp_apply ((inclChains X A).f n) ((cokernel.π (inclChains X A)).f n) y,
    ← HomologicalComplex.comp_f (inclChains X A) (cokernel.π (inclChains X A)) n,
    cokernel.condition]
  rfl

/-! ## The class of the relative cycle -/

/-- **The class of the relative cycle.**  Let `W ⊆ M`, `K ⊆ M`, `ξ ∈ C_N(W)` and `w ∈ Z_N(M)` with
`[w] = c`, and suppose that the image of `ξ` in `C_N(M)` is `iCycles w - j`, where `j` is killed by
the projection `C_*(M) ⟶ C_*(M, M∖K)`.  Then the image, under the excision map
`H_N(W, W∖K) → H_N(M, M∖K)`, of the class of the relative cycle `π ξ` is `relLocClass M N c K`. -/
theorem relCycle_homologyMap_eq_relLocClass {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {W : Set M} {K : Set M}
    (γ : (relChains (TopCat.of W) (pdRelSub W K)).cycles N)
    {ξ : (singularChains ℤ (TopCat.of W)).X N}
    (hγ : (relChains (TopCat.of W) (pdRelSub W K)).iCycles N γ
        = ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f N) ξ)
    {w : (singularChains ℤ M).cycles N}
    (hw : HomologicalComplex.homologyπ (singularChains ℤ M) N w = c)
    {j : (singularChains ℤ M).X N}
    (hξ : (inclChains M W).f N ξ = (singularChains ℤ M).iCycles N w - j)
    (hj0 : ((cokernel.π (inclChains M Kᶜ)).f N) j = 0) :
    HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N
        ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ N γ)
      = relLocClass M N c K := by
  -- the chain-level compatibility of the two projections
  have hstep : (relChainsMap M W Kᶜ).f N
        (((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f N) ξ)
      = ((cokernel.π (inclChains M Kᶜ)).f N) ((inclChains M W).f N ξ) := by
    have h := congrArg (fun (g : singularChains ℤ (TopCat.of W) ⟶ relChains M Kᶜ) =>
        (ModuleCat.Hom.hom (g.f N)) ξ) (cokernel_π_relChainsMap M W Kᶜ)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  -- naturality of `homologyπ` with respect to the excision map
  have hn1 : HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N
        ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ N γ)
      = (relChains M Kᶜ).homologyπ N
          (HomologicalComplex.cyclesMap (relChainsMap M W Kᶜ) N γ) := by
    rw [← ModuleCat.comp_apply
          (HomologicalComplex.homologyπ (relChains (TopCat.of W) (pdRelSub W K)) N)
          (HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N) γ,
        HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  -- naturality of `homologyπ` with respect to `C_*(M) ⟶ C_*(M, M∖K)`
  have hn2 : HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N
        (HomologicalComplex.homologyπ (singularChains ℤ M) N w)
      = (relChains M Kᶜ).homologyπ N
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w) := by
    show HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N
        (HomologicalComplex.homologyπ (singularChains ℤ M) N w)
      = (cokernel (inclChains M Kᶜ)).homologyπ N
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w)
    rw [← ModuleCat.comp_apply (HomologicalComplex.homologyπ (singularChains ℤ M) N)
          (HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N) w,
        HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  -- the underlying chains of the two relative cycles
  have hL : (relChains M Kᶜ).iCycles N
        (HomologicalComplex.cyclesMap (relChainsMap M W Kᶜ) N γ)
      = (relChainsMap M W Kᶜ).f N
          (((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f N) ξ) := by
    rw [← ModuleCat.comp_apply (HomologicalComplex.cyclesMap (relChainsMap M W Kᶜ) N)
          ((relChains M Kᶜ).iCycles N) γ, HomologicalComplex.cyclesMap_i,
        ModuleCat.comp_apply, hγ]
  have hR : (relChains M Kᶜ).iCycles N
        (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w)
      = (relChainsMap M W Kᶜ).f N
          (((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f N) ξ) := by
    show (cokernel (inclChains M Kᶜ)).iCycles N
        (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w) = _
    rw [← ModuleCat.comp_apply (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N)
          ((cokernel (inclChains M Kᶜ)).iCycles N) w, HomologicalComplex.cyclesMap_i,
        ModuleCat.comp_apply]
    have h1 : ((cokernel.π (inclChains M Kᶜ)).f N) ((singularChains ℤ M).iCycles N w)
        = ((cokernel.π (inclChains M Kᶜ)).f N) ((inclChains M W).f N ξ) := by
      have h2 : (singularChains ℤ M).iCycles N w = (inclChains M W).f N ξ + j := by
        rw [hξ]; abel
      rw [h2, map_add, hj0, add_zero]
    exact h1.trans hstep.symm
  -- the two relative cycles coincide
  have hcyc : HomologicalComplex.cyclesMap (relChainsMap M W Kᶜ) N γ
      = HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w := by
    apply (ModuleCat.mono_iff_injective ((relChains M Kᶜ).iCycles N)).mp inferInstance
    exact hL.trans hR.symm
  calc HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N
        ((relChains (TopCat.of W) (pdRelSub W K)).homologyπ N γ)
      = (relChains M Kᶜ).homologyπ N
          (HomologicalComplex.cyclesMap (relChainsMap M W Kᶜ) N γ) := hn1
    _ = (relChains M Kᶜ).homologyπ N
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains M Kᶜ)) N w) := by rw [hcyc]
    _ = HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N
          (HomologicalComplex.homologyπ (singularChains ℤ M) N w) := hn2.symm
    _ = HomologicalComplex.homologyMap (cokernel.π (inclChains M Kᶜ)) N c := by rw [hw]
    _ = relLocClass M N c K := rfl

/-! ## The main statement -/

theorem pd_hatcher_W {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V) :
    ∃ (α₁ α₂ α₃ : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N)
      (γ : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).cycles N)
      (ξ : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N),
      (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ
          = localFundClass N c (U ∪ V) (hU.union hV) (K ∪ L)
              (Set.union_subset (hKU.trans Set.subset_union_left)
                (hLV.trans Set.subset_union_right)) (hKc.union hLc) ∧
      (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).iCycles N γ
          = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V) (K ∪ L)))).f N).hom ξ ∧
      ξ = α₁ + α₂ + α₃ ∧
      (∃ a', (inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U \ L))).f N a' = α₁) ∧
      (∃ b', (inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U ∩ V))).f N b' = α₂) ∧
      (∃ d', (inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (V \ K))).f N d' = α₃) ∧
      (∃ e, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) L)).f (N - 1) e
        = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₁) ∧
      (∃ f, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K)).f (N - 1) f
        = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) α₃) := by
  classical
  -- the Hatcher decomposition over the four open sets `U∖L`, `U∩V`, `V∖K`, `(K∪L)ᶜ`
  obtain ⟨w, hw, a, b, d, j, hsum, ⟨a', ha'⟩, ⟨b', hb'⟩, ⟨d', hd'⟩, ⟨j', hj'⟩⟩ :=
    pd_hatcher_data (M := M) (N := N) (U := U) (V := V) (K := K) (L := L)
      c hU hV hKc hLc hKU hLV
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  have hK'c : IsCompact (K ∪ L) := hKc.union hLc
  have hK'W : K ∪ L ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hKU.trans Set.subset_union_left) (hLV.trans Set.subset_union_right)
  have h1 : U \ L ⊆ (U ∪ V : Set M) := Set.sdiff_subset.trans Set.subset_union_left
  have h2 : (U ∩ V : Set M) ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  have h3 : V \ K ⊆ (U ∪ V : Set M) := Set.sdiff_subset.trans Set.subset_union_right
  have hmemA : a ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := U \ L) (T := U ∪ V) h1 ⟨a', ha'⟩
  have hmemB : b ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := U ∩ V) (T := U ∪ V) h2 ⟨b', hb'⟩
  have hmemD : d ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M (U ∪ V)).f N)) :=
    mem_range_inclChains_of_subset (S := V \ K) (T := U ∪ V) h3 ⟨d', hd'⟩
  -- the three summands, descended to `C_*(U∪V)`
  let aW : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom a
  let bW : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom b
  let dW : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N :=
    (chainRetract ℤ M (U ∪ V) N).hom d
  have haWincl : (inclChains M (U ∪ V)).f N aW = a := chainRetract_of_mem_range hmemA
  have hbWincl : (inclChains M (U ∪ V)).f N bW = b := chainRetract_of_mem_range hmemB
  have hdWincl : (inclChains M (U ∪ V)).f N dW = d := chainRetract_of_mem_range hmemD
  have ha''mem : (chainRetract ℤ M (U ∪ V) N).hom a
      ∈ LinearMap.range (ModuleCat.Hom.hom
          ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U \ L))).f N)) :=
    chainRetract_mem_range_of_subset h1 ⟨a', ha'⟩
  have hb''mem : (chainRetract ℤ M (U ∪ V) N).hom b
      ∈ LinearMap.range (ModuleCat.Hom.hom
          ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (U ∩ V))).f N)) :=
    chainRetract_mem_range_of_subset h2 ⟨b', hb'⟩
  have he''mem : (chainRetract ℤ M (U ∪ V) N).hom d
      ∈ LinearMap.range (ModuleCat.Hom.hom
          ((inclChains (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V) (V \ K))).f N)) :=
    chainRetract_mem_range_of_subset h3 ⟨d', hd'⟩
  obtain ⟨a'', ha''⟩ := ha''mem
  obtain ⟨b'', hb''⟩ := hb''mem
  obtain ⟨e'', he''⟩ := he''mem
  have hξincl : (inclChains M (U ∪ V)).f N (aW + bW + dW) = a + b + d := by
    rw [map_add, map_add, haWincl, hbWincl, hdWincl]
  have hξw : (inclChains M (U ∪ V)).f N (aW + bW + dW)
      = (singularChains ℤ M).iCycles N w - j := by
    rw [hξincl, hsum]
    abel
  -- the discarded summand is killed by the projection to `C_*(M, M∖(K∪L))`
  have hj0 : ((cokernel.π (inclChains M (K ∪ L)ᶜ)).f N) j = 0 := by
    obtain ⟨y, rfl⟩ := (show j ∈ LinearMap.range
      (ModuleCat.Hom.hom ((inclChains M (K ∪ L)ᶜ).f N)) from ⟨j', hj'⟩)
    exact cokernel_π_f_apply_eq_zero N y
  -- the boundary of the descended sum is relatively small
  have hDξ : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) (aW + bW + dW)
      ∈ LinearMap.range (ModuleCat.Hom.hom
          ((inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).f (N - 1))) := by
    refine mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M)) (S := (K ∪ L)ᶜ)
      (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) (aW + bW + dW)) ?_
    have hnat : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) (aW + bW + dW))
        = (singularChains ℤ M).d N (N - 1)
            ((inclChains M (U ∪ V)).f N (aW + bW + dW)) := by
      have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
          (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) (aW + bW + dW))
        ((inclChains M (U ∪ V)).comm N (N - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h.symm
    rw [hnat, hξincl]
    have h0 : (singularChains ℤ M).d N (N - 1) (a + b + d)
        + (singularChains ℤ M).d N (N - 1) j = 0 := by
      have h1 : (singularChains ℤ M).d N (N - 1) (a + b + d + j) = 0 := by
        rw [← hsum, ← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
        simp
      rwa [map_add] at h1
    have hdj : (singularChains ℤ M).d N (N - 1) (a + b + d)
        = - ((singularChains ℤ M).d N (N - 1) j) := eq_neg_of_add_eq_zero_left h0
    rw [hdj]
    obtain ⟨g, hg⟩ := d_mem_range_inclChains (M := M) (S := (K ∪ L)ᶜ) (n := N) ⟨j', hj'⟩
    exact ⟨-g, by rw [map_neg, hg]⟩
  have hπξ : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).d N (N - 1)
      (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L)))).f N)
        (aW + bW + dW)) = 0 := by
    show ((cokernel (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).d N (N - 1))
      (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).f N) (aW + bW + dW)) = 0
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
        (cokernel (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V) (K ∪ L)))).X (N - 1)) =>
        (ModuleCat.Hom.hom g) (aW + bW + dW))
      ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V) (K ∪ L)))).comm N (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h]
    obtain ⟨y, hy⟩ := hDξ
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (N - 1) y
  -- the relative cycle
  let γ : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).cycles N :=
    cycleOf N (((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L)))).f N)
      (aW + bW + dW)) hπξ
  have hγi : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).iCycles N γ
      = ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L)))).f N).hom
          (aW + bW + dW) := iCycles_cycleOf N _ hπξ
  -- its class is the local fundamental class
  have hcl : HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
      ((relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ)
      = relLocClass M N c (K ∪ L) :=
    relCycle_homologyMap_eq_relLocClass c γ hγi hw hξw hj0
  have hcov : (U ∪ V : Set M) ∪ (K ∪ L)ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K ∪ L
    · exact Or.inl (hK'W hx)
    · exact Or.inr hx
  have hloc : (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ
      = localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c := by
    haveI : IsIso (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N) :=
      excision_relChainsMap_isIso M (U ∪ V) (K ∪ L)ᶜ hW hK'c.isClosed.isOpen_compl hcov N
    have hspec := localFundClass_spec N c (U ∪ V) hW (K ∪ L) hK'W hK'c
    calc (relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ
        = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
              ((relChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ)) :=
            (IsIso.hom_inv_id_apply _ _).symm
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (relLocClass M N c (K ∪ L)) := by rw [hcl]
      _ = inv (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N)
            (HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∪ L)ᶜ) N
              (localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c)) := by rw [hspec]
      _ = localFundClass N c (U ∪ V) hW (K ∪ L) hK'W hK'c := IsIso.hom_inv_id_apply _ _
  -- the boundaries of the first and third summands are small
  have hbd1 : ∃ e, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) L)).f (N - 1) e
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) aW := by
    have hmemd : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) aW)
        ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M Lᶜ).f (N - 1))) := by
      have hnat : (inclChains M (U ∪ V)).f (N - 1)
          ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) aW)
          = (singularChains ℤ M).d N (N - 1) ((inclChains M (U ∪ V)).f N aW) := by
        have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
            (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) aW)
          ((inclChains M (U ∪ V)).comm N (N - 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [hnat, haWincl]
      exact mem_range_inclChains_of_subset (S := U \ L) (T := Lᶜ) (fun x hx => hx.2)
        (d_mem_range_inclChains (M := M) (S := U \ L) ⟨a', ha'⟩)
    obtain ⟨e, he⟩ := mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M))
      (S := Lᶜ) (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) aW) hmemd
    exact ⟨e, he⟩
  have hbd2 : ∃ f, (inclChains (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V) K)).f (N - 1) f
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) dW := by
    have hmemd : (inclChains M (U ∪ V)).f (N - 1)
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) dW)
        ∈ LinearMap.range (ModuleCat.Hom.hom ((inclChains M Kᶜ).f (N - 1))) := by
      have hnat : (inclChains M (U ∪ V)).f (N - 1)
          ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) dW)
          = (singularChains ℤ M).d N (N - 1) ((inclChains M (U ∪ V)).f N dW) := by
        have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X N ⟶
            (singularChains ℤ M).X (N - 1)) => (ModuleCat.Hom.hom g) dW)
          ((inclChains M (U ∪ V)).comm N (N - 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [hnat, hdWincl]
      exact mem_range_inclChains_of_subset (S := V \ K) (T := Kᶜ) (fun x hx => hx.2)
        (d_mem_range_inclChains (M := M) (S := V \ K) ⟨d', hd'⟩)
    obtain ⟨f, hf⟩ := mem_range_inclChains_of_image (M := M) (W := (U ∪ V : Set M))
      (S := Kᶜ) (N - 1) (γ := (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d N (N - 1) dW) hmemd
    exact ⟨f, hf⟩
  exact ⟨aW, bW, dW, γ, aW + bW + dW, hloc, hγi, rfl, ⟨a'', ha''⟩, ⟨b'', hb''⟩,
    ⟨e'', he''⟩, hbd1, hbd2⟩

end

end Work.Cohomology
