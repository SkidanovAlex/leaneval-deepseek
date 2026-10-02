import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Milnor.ZeroSectionProj
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.vk_relCup_ne_zero_of_relCapPair_ne_zero
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Milnor.cohomology_Mk_minus_two
import Submission.Work.Milnor.mkToVkRangeHomeomorph
import Submission.Work.Milnor.homology_Vk
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.Crux.relCapPair_cup_adjunction
import Submission.Work.Milnor.capped_generator_pairings

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The square of the Thom class is a generator, from surjectivity of the duality map

If the Lefschetz-duality map `u ↦ u ⌢ c` of the pair `(Vk(-2), Mk(-2))` is surjective for some
relative homology class `c` in degree `8`, then the relative cup square of a *generator* of
`H⁴(Vk,Mk) ≅ ℤ` is a *generator* of `H⁸(Vk,Mk) ≅ ℤ`.

The argument: the duality map `Λ : u ↦ u ⌢ c` is onto `H₄(Vk(-2)) ≅ ℤ`, hence it sends the
generator `ug` of `H⁴(Vk,Mk) ≅ ℤ` to a generator of `H₄`; the absolute Kronecker pairing of
`Vk(-2)` is unimodular (`kronH_isIso`) and `relIncl ug` is a generator of `H⁴(Vk) ≅ ℤ`, so
`⟨relIncl ug, ug⌢c⟩ = ±1`.  By the value-level cap/cup adjunction `⟨1, (ug⌣ug)⌢c⟩ = ±1`, and
since the square is a multiple of the generator `ω` of `H⁸(Vk,Mk) ≅ ℤ`, that multiple is a unit:
the square generates.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology.Crux

noncomputable section

/-! ## Elementary linear algebra over `ℤ` -/

/-- The canonical generator `e.symm 1` of a `ℤ`-module isomorphic to `ℤ` spans everything. -/
private lemma span_symm_one {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ {e.symm 1} = ⊤ := by
  have h1 : Submodule.span ℤ {(1 : ℤ)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro m
    exact Submodule.mem_span_singleton.mpr ⟨m, by simp⟩
  have h2 : Submodule.map (e.symm : ℤ →ₗ[ℤ] M) (Submodule.span ℤ {(1 : ℤ)})
      = Submodule.span ℤ {e.symm 1} := by
    rw [Submodule.map_span]; simp
  rw [h1, Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective] at h2
  exact h2.symm

/-- `span {-y} = span {y}`. -/
private lemma span_neg_eq {M : Type*} [AddCommGroup M] [Module ℤ M] (y : M) :
    Submodule.span ℤ {-y} = Submodule.span ℤ {y} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton y))
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have : -y ∈ Submodule.span ℤ {-y} := Submodule.subset_span (Set.mem_singleton (-y))
    simpa using Submodule.neg_mem (Submodule.span ℤ {-y}) this

/-- Scaling a generator by a unit gives a generator. -/
private lemma span_zsmul_eq_top_of_eq_pm_one {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x y : M) (h : x = y ∨ x = -y) (hy : Submodule.span ℤ {y} = ⊤) :
    Submodule.span ℤ {x} = ⊤ := by
  rcases h with rfl | rfl
  · exact hy
  · rw [span_neg_eq]; exact hy

/-- `H⁴(Mk(-2); ℤ) = 0`. -/
private lemma isZero_singularCohomology_vkPairA_four :
    IsZero (singularCohomology ℤ 4 (TopCat.of vkPairA)) := by
  obtain ⟨hmk⟩ := Work.Milnor.mkToVkRangeHomeomorph (-2)
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv hmk.symm.toHomotopyEquiv 4
  obtain ⟨e2⟩ := Work.Milnor.cohomology_Mk_minus_two 4
  have hfin : (if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 7 then 1 else 0) = 0 := by norm_num
  have hz : IsZero (ModuleCat.of ℤ
      (Fin ((if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 7 then 1 else 0)) → ℤ)) := by
    rw [hfin, ModuleCat.isZero_iff_subsingleton]; infer_instance
  exact IsZero.of_iso hz (e ≪≫ e2)

/-- `relIncl : H⁴(Vk,Mk) → H⁴(Vk)` is surjective (its target equals its range because the next
map `H⁴(Vk) → H⁴(Mk)` has zero target). -/
private lemma relIncl_four_surj :
    Function.Surjective (fun x : relCohomology ℤ vkPairX vkPairA 4 =>
      (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) x) := by
  haveI hzA : IsZero (singularCohomology ℤ 4 (TopCat.of vkPairA)) :=
    isZero_singularCohomology_vkPairA_four
  have hzero : (HomologicalComplex.homologyMap (restr ℤ vkPairX vkPairA) 4) = 0 :=
    hzA.eq_of_tgt _ 0
  have hzeros : (HomologicalComplex.homologyMap (restr ℤ vkPairX vkPairA) 4).hom = 0 := by
    rw [hzero]; exact ModuleCat.hom_zero
  have hrk := ShortComplex.Exact.moduleCat_range_eq_ker
    (pair_exact₂ ℤ vkPairX vkPairA 4)
  rw [hzeros, LinearMap.ker_zero] at hrk
  exact LinearMap.range_eq_top.mp hrk

/-- The integral singular homology of `Vk(-2)` is degreewise free. -/
private lemma free_homology_vkPairX : ∀ n, Module.Free ℤ ↥((singularChains ℤ vkPairX).homology n) := by
  intro n
  obtain ⟨e⟩ := Work.Milnor.homology_Vk (-2) n
  haveI : Module.Free ℤ
      ↥(ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) → ℤ)) :=
    inferInstance
  exact Module.Free.of_equiv e.toLinearEquiv.symm

/-! ## Generic linear-algebra helpers

These are stated over an arbitrary commutative ring so that the `ℤ`-scalar actions are the ones
attached to the `Module` structures (and not the `zsmul`-derived ones Mathlib would otherwise
pick for `ℤ` in user-written notation).  This lets them interoperate with the Mathlib lemmas
`LinearMap.map_smul` and `LinearMap.smul_apply`. -/

/-- If `k • x = y` with `k = 1` then `y = x`. -/
private lemma eq_of_smul_eq_of_eq_one {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (k : R) (x y : M) (h : k • x = y) (hk : k = 1) : y = x := by
  rw [← h, hk, one_smul]

/-- If `k • x = y` with `k = -1` then `y = -x`. -/
private lemma eq_neg_of_smul_eq_of_eq_neg_one {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (k : R) (x y : M) (h : k • x = y) (hk : k = -1) : y = -x := by
  rw [← h, hk, neg_one_smul]

/-! ## The main reduction -/

/-- **The reduction.**  If the Lefschetz-duality map `u ↦ u ⌢ c` of the pair `(Vk(-2), Mk(-2))`
is surjective for some relative homology class `c`, then the relative cup square of a *generator*
of `H⁴(Vk,Mk) ≅ ℤ` is a *generator* of `H⁸(Vk,Mk) ≅ ℤ`. -/
theorem vk_relCupSquare_generates_of_surjective
    (hc : ∃ c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8,
      Function.Surjective (fun u : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX
        Work.Cohomology.vkPairA 4 =>
        Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 u c)) :
    ∃ u : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4,
      Submodule.span ℤ {u} = ⊤ ∧
      Submodule.span ℤ {(Work.Cohomology.relCupH' ℤ Work.Cohomology.vkPairX
        Work.Cohomology.vkPairA 4 4 u u)} = ⊤ := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨iso4⟩ := cohomologyPairVk 4
  obtain ⟨iso8⟩ := cohomologyPairVk 8
  obtain ⟨hom4⟩ := Work.Milnor.homology_Vk (-2) 4
  have h4 : ((if (4:ℕ) = 4 then 1 else 0) + (if (4:ℕ) = 8 then 1 else 0)) = 1 := by norm_num
  have h8 : ((if (8:ℕ) = 4 then 1 else 0) + (if (8:ℕ) = 8 then 1 else 0)) = 1 := by norm_num
  have hh4 : ((if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 4 then 1 else 0)) = 1 := by norm_num
  rw [h4] at iso4
  rw [h8] at iso8
  rw [hh4] at hom4
  let e4 : relCohomology ℤ vkPairX vkPairA 4 ≃ₗ[ℤ] ℤ :=
    (iso4.toLinearEquiv).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  let e8 : relCohomology ℤ vkPairX vkPairA 8 ≃ₗ[ℤ] ℤ :=
    (iso8.toLinearEquiv).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  let f4 : (singularChains ℤ vkPairX).homology 4 ≃ₗ[ℤ] ℤ :=
    (hom4.toLinearEquiv).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  let ug : relCohomology ℤ vkPairX vkPairA 4 := e4.symm 1
  have hspan_ug : Submodule.span ℤ {ug} = ⊤ := span_symm_one e4
  -- the duality map is onto, so `ug ⌢ c` generates `H₄(X) ≅ ℤ`
  have hspan_ugc : Submodule.span ℤ {(relCapPair vkPairX vkPairA 4 4 ug) c} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    obtain ⟨u, hu⟩ := hc v
    have hu' : (relCapPair vkPairX vkPairA 4 4 u) c = v := hu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show u ∈ Submodule.span ℤ {ug} by rw [hspan_ug]; trivial)
    have hv : v = a • ((relCapPair vkPairX vkPairA 4 4 ug) c) := by
      rw [← hu', ← ha, LinearMap.map_smul]
      rfl
    rw [hv]
    rw [← int_smul_eq_zsmul (inferInstance :
      Module ℤ ((singularChains ℤ vkPairX).homology 4)) a ((relCapPair vkPairX vkPairA 4 4 ug) c)]
    exact Submodule.smul_mem _ a (Submodule.subset_span
      (Set.mem_singleton ((relCapPair vkPairX vkPairA 4 4 ug) c)))
  -- `relIncl ug` generates `H⁴(X) ≅ ℤ`
  have hug_ne : ug ≠ 0 := by
    intro h0
    have h1 : (1 : ℤ) = 0 := by
      have h := congrArg e4 h0
      simpa [ug] using h
    exact one_ne_zero h1
  haveI hmono : Mono (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) :=
    mono_of_exact_of_isZero_src (pair_exact₁ ℤ vkPairX vkPairA 3)
      isZero_singularCohomology_vkPairA_three
  have hgen_rel : Submodule.span ℤ
      {((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4)).hom ug} = ⊤ := by
    have hmap : Submodule.map
        ((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4)).hom
        (Submodule.span ℤ {ug}) = Submodule.span ℤ
          {((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4)).hom ug} := by
      rw [Submodule.map_span]; simp
    rw [← hmap, hspan_ug, Submodule.map_top, LinearMap.range_eq_top.mpr relIncl_four_surj]
  have hsurj_kron : Function.Surjective (fun x :
      (singularCochainComplex ℤ vkPairX).homology 4 => kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x) :=
    (kronH_isIso vkPairX free_homology_vkPairX 4).2
  -- unimodularity of the absolute Kronecker pairing: `⟨relIncl ug, ug ⌢ c⟩ = ±1`
  have hval : kronH ℤ (TopCat.toSSet.obj vkPairX) 4
      ((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) ug)
      ((relCapPair vkPairX vkPairA 4 4 ug) c) = 1 ∨
      kronH ℤ (TopCat.toSSet.obj vkPairX) 4
        ((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) ug)
        ((relCapPair vkPairX vkPairA 4 4 ug) c) = -1 :=
    Work.Milnor.cgp_kronH_eval_generator (kronH ℤ (TopCat.toSSet.obj vkPairX) 4) hsurj_kron
      _ hgen_rel f4 _ hspan_ugc
  have hadj := relCapPair_cup_adjunction (X := vkPairX) (A := vkPairA) ug c
  -- the augmentation evaluation of the square
  let y := relCupH' ℤ vkPairX vkPairA 4 4 ug ug
  have hΦy : kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
      ((relCapPair vkPairX vkPairA 8 0 y) c) = 1 ∨
      kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
      ((relCapPair vkPairX vkPairA 8 0 y) c) = -1 := by
    have h0 : kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        (relCapPair vkPairX vkPairA 8 0 (relCupH' ℤ vkPairX vkPairA 4 4 ug ug) c) = 1 ∨
        kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        (relCapPair vkPairX vkPairA 8 0 (relCupH' ℤ vkPairX vkPairA 4 4 ug ug) c) = -1 := by
      rw [hadj]; exact hval
    simpa only [y] using h0
  -- write the square as a multiple of the generator `ω` of `H⁸`
  let ω : relCohomology ℤ vkPairX vkPairA 8 := e8.symm 1
  have hspan_ω : Submodule.span ℤ {ω} = ⊤ := span_symm_one e8
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (show y ∈ Submodule.span ℤ {ω} by rw [hspan_ω]; trivial)
  have hΦω : kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
      ((relCapPair vkPairX vkPairA 8 0 y) c)
      = k * kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        ((relCapPair vkPairX vkPairA 8 0 ω) c) := by
    have h1 : kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        ((relCapPair vkPairX vkPairA 8 0 y) c)
        = k • (kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
          ((relCapPair vkPairX vkPairA 8 0 ω) c)) := by
      have hA : (relCapPair vkPairX vkPairA 8 0 y) c
          = (k • (relCapPair vkPairX vkPairA 8 0 ω)) c := by
        rw [← hk, LinearMap.map_smul]
      have hB : (k • (relCapPair vkPairX vkPairA 8 0 ω)) c
          = k • ((relCapPair vkPairX vkPairA 8 0 ω) c) := rfl
      have hC : kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
          (k • ((relCapPair vkPairX vkPairA 8 0 ω) c))
          = k • (kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
            ((relCapPair vkPairX vkPairA 8 0 ω) c)) := map_zsmul _ k _
      exact ((congrArg (fun v => kronH ℤ (TopCat.toSSet.obj vkPairX) 0
          (oneH ℤ (TopCat.toSSet.obj vkPairX)) v) hA).trans
        (congrArg (fun v => kronH ℤ (TopCat.toSSet.obj vkPairX) 0
          (oneH ℤ (TopCat.toSSet.obj vkPairX)) v) hB)).trans hC
    exact h1.trans (zsmul_eq_mul _ k)
  have hprod : k * (kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        ((relCapPair vkPairX vkPairA 8 0 ω) c)) = 1 ∨
      k * (kronH ℤ (TopCat.toSSet.obj vkPairX) 0 (oneH ℤ (TopCat.toSSet.obj vkPairX))
        ((relCapPair vkPairX vkPairA 8 0 ω) c)) = -1 := by
    rcases hΦy with h | h
    · exact Or.inl (by rw [← hΦω, h])
    · exact Or.inr (by rw [← hΦω, h])
  have hk1 : k = 1 ∨ k = -1 := by
    rcases hprod with h | h
    · exact Int.eq_one_or_neg_one_of_mul_eq_one h
    · have h' : (-k) * (kronH ℤ (TopCat.toSSet.obj vkPairX) 0
          (oneH ℤ (TopCat.toSSet.obj vkPairX)) ((relCapPair vkPairX vkPairA 8 0 ω) c)) = 1 := by
        rw [neg_mul, h]; ring
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h' with h'' | h''
      · right; omega
      · left; omega
  have hyω : y = ω ∨ y = -ω := by
    rcases hk1 with h | h
    · left; exact eq_of_smul_eq_of_eq_one k ω y hk h
    · right; exact eq_neg_of_smul_eq_of_eq_neg_one k ω y hk h
  exact ⟨ug, hspan_ug, span_zsmul_eq_top_of_eq_pm_one y ω hyω hspan_ω⟩

end

end Work.Cohomology.Crux
