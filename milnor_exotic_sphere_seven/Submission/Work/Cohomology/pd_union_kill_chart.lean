import Mathlib
import Submission.Work.Cohomology.pd_union_kill_pos
import Submission.Work.Cohomology.pd_split_kc
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_glue2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `m = 0` case of the two-cover gluing for `Good`, under the vanishing hypothesis

`Work.Cohomology.pd_union_kill_chart` is the injectivity ("kill") clause of the gluing
`Good U → Good V → Good (U∩V) → Good (U∪V)` for a two-element open cover, in the case where the
*extra hypothesis* `H^k_c(U∩V) = 0` for `k > N` (encoded elementwise by `hvan`) is available.  For
`1 ≤ m` the statement is `Work.Cohomology.pd_union_kill_pos`; for `m = 0` (i.e. `k = N`) the
Mayer–Vietoris ladder needs the vanishing of `H^{N+1}_c(U∩V)`, and `hvan` supplies it.

The key observation for `m = 0` is that the `A+B` (Hatcher) complex of the enlarged pair of
compact sets `(K ∪ L, K' ∪ L)` has *vanishing* `H^{N+1}`: its homology in degree `N+1` agrees with
`H^{N+1}(W, W∖L)` (`pdABCoh_quasiIso`), and that group is isomorphic by excision to
`H^{N+1}(U∩V, (U∩V)∖L)`, which is trivial by `hvan`.  Hence the `A+B` connecting homomorphism of
the enlarged pair vanishes, and the exactness `pdAB_exact₃` of the `A+B` sequence produces the
splitting of `x` into pieces supported in `U` resp. `V`.

## Contents

* `pd_split_kc_zero` — the splitting of a class over the cover, for `m = 0`, under `hvan`;
* `pd_kill_of_split` — the injectivity clause, given the splitting as a hypothesis (this is the
  proof of `pd_union_kill_pos` with the splitting abstracted);
* `pd_union_kill_chart` — the target theorem, by case distinction on `m = 0` / `1 ≤ m`.
-/

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The splitting lemma in the case `m = 0` -/

/-- **The splitting of a killed class over a two-piece cover, in the case `m = 0`.**

Let `W = U ∪ V` with `U, V` open, `K₁ ⊆ U`, `K₂ ⊆ V` compact, and suppose that the relative
cohomology `H^k_c(U∩V)` vanishes in degrees `> N` (`hvan`).  Then every class
`x ∈ H^k(W, W∖(K₁∪K₂))` (with `k + 0 = N`) is, after enlarging the compact sets, the difference of
two classes supported in `U` resp. `V`.

The proof does not use the duality hypothesis `goodD … = 0`: with `L ⊇ K₁∩K₂` provided by `hvan`,
the `A+B` complex of `(W∖(K₁∪L), W∖(K₂∪L))` has trivial `H^{N+1}`, so its connecting homomorphism
vanishes on `x` and `pdAB_exact₃` exhibits the difference. -/
theorem pd_split_kc_zero {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (hvan : ∀ k, N < k → ∀ K : Set M, K ⊆ U ∩ V → IsCompact K →
        ∃ K' : Set M, K ⊆ K' ∧ K' ⊆ U ∩ V ∧ IsCompact K' ∧
          Subsingleton ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
            (pdRelSub (U ∩ V : Set M) K')).homology k))
    (k m : ℕ) (hkm : k + m = N) (hm : m = 0)
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k)
    (hx : goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm x = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂')
      (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ := by
  classical
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  -- the compact set `L ⊇ K₁ ∩ K₂` supplied by the vanishing hypothesis, in degree `k + 1 = N + 1`
  have hk1 : N < k + 1 := by omega
  obtain ⟨L, hK₁₂L, hLUV, hLc, hLsub⟩ :=
    hvan (k + 1) hk1 (K₁ ∩ K₂) (Set.inter_subset_inter hK₁U hK₂V) (hK₁c.inter hK₂c)
  -- the enlarged compact sets
  have hK₁'U : K₁ ∪ L ⊆ U := Set.union_subset hK₁U (hLUV.trans Set.inter_subset_left)
  have hK₂'V : K₂ ∪ L ⊆ V := Set.union_subset hK₂V (hLUV.trans Set.inter_subset_right)
  have hK₁'c : IsCompact (K₁ ∪ L) := hK₁c.union hLc
  have hK₂'c : IsCompact (K₂ ∪ L) := hK₂c.union hLc
  have hKint : (K₁ ∪ L) ∩ (K₂ ∪ L) = L := by
    ext y; constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact hK₁₂L ⟨h1, h2⟩
      · exact h2
      · exact h1
      · exact h2
    · intro hy; exact ⟨Or.inr hy, Or.inr hy⟩
  -- notation for the `A+B` complexes
  let X : TopCat := TopCat.of (U ∪ V : Set M)
  let A : Set X := pdRelSub (U ∪ V : Set M) K₁
  let B : Set X := pdRelSub (U ∪ V : Set M) K₂
  let A' : Set X := pdRelSub (U ∪ V : Set M) (K₁ ∪ L)
  let B' : Set X := pdRelSub (U ∪ V : Set M) (K₂ ∪ L)
  have hAB : pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂) = A ∩ B :=
    pdRelSub_union (U ∪ V : Set M) K₁ K₂
  have hInterAB : A' ∩ B' = pdRelSub (U ∪ V : Set M) ((K₁ ∪ L) ∪ (K₂ ∪ L)) :=
    (pdRelSub_union (U ∪ V : Set M) (K₁ ∪ L) (K₂ ∪ L)).symm
  have hA'mem : A' ⊆ A := pdRelSub_mono (Set.subset_union_left : K₁ ⊆ K₁ ∪ L)
  have hB'mem : B' ⊆ B := pdRelSub_mono (Set.subset_union_left : K₂ ⊆ K₂ ∪ L)
  have hMM' : K₁ ∪ K₂ ⊆ (K₁ ∪ L) ∪ (K₂ ∪ L) :=
    Set.union_subset (Set.subset_union_left.trans Set.subset_union_left)
      (Set.subset_union_left.trans Set.subset_union_right)
  have hA'op : IsOpen A' :=
    (hK₁'c.isClosed.isOpen_compl).preimage continuous_subtype_val
  have hB'op : IsOpen B' :=
    (hK₂'c.isClosed.isOpen_compl).preimage continuous_subtype_val
  -- `H^{k+1}(W, W∖L)` is trivial by excision and `hvan`
  have hIVW : (U ∩ V : Set M) ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  have hWsubL : Subsingleton ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) L)).homology (k + 1)) := by
    haveI hLsub' : Subsingleton ((relComplex ℤ (TopCat.of (U ∩ V : Set M))
        (pdRelSub (U ∩ V : Set M) L)).homology (k + 1)) := hLsub
    haveI hiso : IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ
        (pdRelSub (U ∩ V : Set M) L) (pdRelSub (U ∪ V : Set M) L)
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hIVW) (fun x hx => hx)) (k + 1)) :=
      pdCohExcision hIVW hI hW hLUV hLc (k + 1)
    have hinj : Function.Injective (HomologicalComplex.homologyMap (relComplexMap ℤ
        (pdRelSub (U ∩ V : Set M) L) (pdRelSub (U ∪ V : Set M) L)
        (pdIncl (U ∪ V : Set M) (U ∩ V : Set M) hIVW) (fun x hx => hx)) (k + 1)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  -- hence `H^{k+1}` of the `A+B` complex of the enlarged pair is trivial
  have hWsub : Subsingleton ((relComplex ℤ X (A' ∪ B')).homology (k + 1)) := by
    have hAuB' : A' ∪ B' = pdRelSub (U ∪ V : Set M) L := by
      rw [pdRelSub_union_sub (U ∪ V : Set M) (K₁ ∪ L) (K₂ ∪ L), hKint]
    exact hAuB'.symm ▸ hWsubL
  have hCohSub : Subsingleton ((pdABCoh X A' B').homology (k + 1)) := by
    haveI hsource : Subsingleton ((relComplex ℤ X (A' ∪ B')).homology (k + 1)) := hWsub
    haveI hq : IsIso (HomologicalComplex.homologyMap (pdABInclRel X A' B') (k + 1)) :=
      pdABCoh_quasiIso hA'op hB'op (k + 1)
    have hsurj : Function.Surjective
        (HomologicalComplex.homologyMap (pdABInclRel X A' B') (k + 1)).hom :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']
  -- the connecting homomorphism vanishes on the enlarged class
  let x' : (relComplex ℤ X (A' ∩ B')).homology k :=
    (HomologicalComplex.homologyMap (pdRelComplexEnlargeInter X hA'mem hB'mem) k) (hAB ▸ x)
  have hδ0 : PDABClean.pdABδ X A' B' k x' = 0 := by
    haveI hsc : Subsingleton ((pdABCoh X A' B').homology (k + 1)) := hCohSub
    exact Subsingleton.elim _ _
  have hmem : x' ∈ LinearMap.range
      ((HomologicalComplex.homologyMap (PDABClean.pdABg X A' B') k).hom) := by
    have hex := PDABClean.pdAB_exact₃ X A' B' k
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    rw [hex]
    exact LinearMap.mem_ker.mpr hδ0
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
  let x₁ : (relComplex ℤ X A').homology k :=
    (HomologicalComplex.homologyMap (biprod.fst : relComplex ℤ X A' ⊞
      relComplex ℤ X B' ⟶ relComplex ℤ X A') k) z
  let x₂ : (relComplex ℤ X B').homology k :=
    (HomologicalComplex.homologyMap (biprod.snd : relComplex ℤ X A' ⊞
      relComplex ℤ X B' ⟶ relComplex ℤ X B') k) z
  have hdecomp : x' = (HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁
      - (HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂ := by
    rw [← hz]
    have hdesc : PDABClean.pdABg X A' B' = biprod.fst ≫ pdToInterA X A' B'
        + biprod.snd ≫ (-(pdToInterB X A' B')) := biprod.desc_eq
    rw [hdesc, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg]
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_neg,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, sub_eq_add_neg]
    try rfl
  refine ⟨K₁ ∪ L, K₂ ∪ L, Set.subset_union_left, Set.subset_union_left,
    hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, ?_⟩
  have hc0 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hMM') k) x
      = hInterAB ▸ x' :=
    PDSplitKC.pd_kc_castApply hInterAB.symm hAB (𝟙 X) (pdRelSub_mono hMM')
      (Set.inter_subset_inter hA'mem hB'mem) k x
  have hc1 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.subset_union_left : K₁ ∪ L ⊆ (K₁ ∪ L) ∪ (K₂ ∪ L))) k) x₁
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁) :=
    PDSplitKC.pd_kc_castApply hInterAB.symm rfl (𝟙 X)
      (pdRelSub_mono (Set.subset_union_left : K₁ ∪ L ⊆ (K₁ ∪ L) ∪ (K₂ ∪ L)))
      (fun x hx => hx.1) k x₁
  have hc2 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.subset_union_right : K₂ ∪ L ⊆ (K₁ ∪ L) ∪ (K₂ ∪ L))) k) x₂
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂) :=
    PDSplitKC.pd_kc_castApply hInterAB.symm rfl (𝟙 X)
      (pdRelSub_mono (Set.subset_union_right : K₂ ∪ L ⊆ (K₁ ∪ L) ∪ (K₂ ∪ L)))
      (fun x hx => hx.2) k x₂
  rw [hc0, hc1, hc2]
  have htr : hInterAB ▸ x'
      = hInterAB ▸ ((HomologicalComplex.homologyMap (pdToInterA X A' B') k) x₁
          - (HomologicalComplex.homologyMap (pdToInterB X A' B') k) x₂) :=
    congrArg (fun w => hInterAB ▸ w) hdecomp
  rw [htr]
  exact PDSplitKC.pd_kc_cast_sub (P := fun i => (relComplex ℤ X i).homology k) hInterAB _ _

/-! ## The injectivity clause, given the splitting -/

/-- **The injectivity ("kill") clause of the gluing, given the splitting lemma.**

This is the proof of `pd_union_kill_pos` with the appeal to `pd_split_kc` abstracted into the
hypothesis `hsplit0`; it is used at `m = 0` with `pd_split_kc_zero`. -/
theorem pd_kill_of_split {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N)
    (hsplit0 : ∀ {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
        (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
        (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k),
        goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
          (Set.union_subset (hK₁U.trans Set.subset_union_left)
            (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm x = 0 →
        ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂')
          (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
          (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
          (x₁ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
                  (pdRelSub (U ∪ V : Set M) K₁')).homology k)
          (x₂ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
                  (pdRelSub (U ∪ V : Set M) K₂')).homology k),
          (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.union_subset (h₁.trans Set.subset_union_left)
              (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
            = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
              - (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂) :
    ∀ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
       (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K)).homology k),
       goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x = 0 →
       ∃ (K' : Set M) (hKK' : K ⊆ K') (hK'W : K' ⊆ U ∪ V) (hK'c : IsCompact K'),
         (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hKK') k) x = 0 := by
  intro K hKW hKc x hx
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  -- Step 1: split the compact set
  obtain ⟨K₁, K₂, hK₁U, hK₂V, hK₁c, hK₂c, hK12⟩ := pd_compact_pieces hU hV hKc hKW
  have hW12 : K₁ ∪ K₂ ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hK₁U.trans Set.subset_union_left) (hK₂V.trans Set.subset_union_right)
  have hW12c : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  set x₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k
    := (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK12) k) x with hx₀def
  have hx₀ : goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hW12 hW12c k m hkm x₀ = 0 := by
    rw [hx₀def, pd_goodD_natural N c (U ∪ V : Set M) hW hK12 hKW hW12 hKc hW12c k m hkm x, hx]
  -- Step 2: the splitting lemma
  obtain ⟨K₁', K₂', h₁, h₂, hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, hsplit⟩ :=
    hsplit0 hK₁U hK₂V hK₁c hK₂c x₀ hx₀
  -- Step 3: the two duality classes agree
  have hmid : K₁ ∪ K₂ ⊆ K₁' ∪ K₂' :=
    Set.union_subset (h₁.trans Set.subset_union_left) (h₂.trans Set.subset_union_right)
  have hW1 : K₁' ∪ K₂' ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hK₁'U.trans Set.subset_union_left) (hK₂'V.trans Set.subset_union_right)
  have hW1c : IsCompact (K₁' ∪ K₂') := hK₁'c.union hK₂'c
  have hK₁'W : K₁' ⊆ (U ∪ V : Set M) := hK₁'U.trans Set.subset_union_left
  have hK₂'W : K₂' ⊆ (U ∪ V : Set M) := hK₂'V.trans Set.subset_union_right
  have hD12 : goodD N c (U ∪ V : Set M) hW K₁' hK₁'W hK₁'c k m hkm x₁
      = goodD N c (U ∪ V : Set M) hW K₂' hK₂'W hK₂'c k m hkm x₂ := by
    have h := congrArg (goodD N c (U ∪ V : Set M) hW (K₁' ∪ K₂') hW1 hW1c k m hkm) hsplit
    rw [pd_goodD_natural N c (U ∪ V : Set M) hW hmid hW12 hW1 hW12c hW1c k m hkm x₀,
      hx₀] at h
    rw [goodD_sub c hW hW1 hW1c k m hkm] at h
    rw [pd_goodD_natural N c (U ∪ V : Set M) hW
          (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂') hK₁'W hW1 hK₁'c hW1c k m hkm x₁,
        pd_goodD_natural N c (U ∪ V : Set M) hW
          (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂') hK₂'W hW1 hK₂'c hW1c k m hkm x₂] at h
    exact sub_eq_zero.mp h.symm
  -- the restrictions to `U` and to `V`
  set rU : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁')).homology k
      ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁')).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₁') (pdRelSub (U ∪ V : Set M) K₁')
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrU
  set rV : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂')).homology k
      ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂')).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₂') (pdRelSub (U ∪ V : Set M) K₂')
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrV
  have hD1 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left)) m)
      (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
      = goodD N c (U ∪ V : Set M) hW K₁' hK₁'W hK₁'c k m hkm x₁ := by
    rw [hrU]
    exact pd_goodD_incl (W := (U ∪ V : Set M)) (V := U) (K := K₁') Set.subset_union_left
      hW hU hK₁'U hK₁'W hK₁'c N c k m hkm x₁
  have hD2 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) m)
      (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂))
      = goodD N c (U ∪ V : Set M) hW K₂' hK₂'W hK₂'c k m hkm x₂ := by
    rw [hrV]
    exact pd_goodD_incl (W := (U ∪ V : Set M)) (V := V) (K := K₂') Set.subset_union_right
      hW hV hK₂'V hK₂'W hK₂'c N c k m hkm x₂
  have hMV : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left)) m)
      (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
      = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) m)
      (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂)) := by
    rw [hD1, hD2, hD12]
  -- Step 4: exactness of the Mayer-Vietoris sequence
  obtain ⟨t, htU, htV⟩ := pdMV_exact_mid hU hV m
    (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
    (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂)) hMV
  clear hMV hD1 hD2 hD12
  -- Step 5: surjectivity of the duality map of `U ∩ V`
  obtain ⟨K₀, hK₀I, hK₀c, s, hs⟩ := hII.hit k m hkm t
  -- Step 6: extending a class on `U ∩ V` to `U ∪ V`
  obtain ⟨K₀₁, K₀₂, hK₀K₀₁, hK₀K₀₂, hK₀₁U, hK₀₂V, hK₀₁c, hK₀₂c, y₁, y₂, hy1, hy2, hy3⟩ :=
    pd_union_extend hU hV hI hUU hVV hII k m hkm hK₀I hK₀c s
  -- the restrictions of `yᵢ` to `U`, `V`
  set rU₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₀₁)).homology k
      ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₀₁)).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₀₁) (pdRelSub (U ∪ V : Set M) K₀₁)
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrU₀
  set rV₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₀₂)).homology k
      ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₀₂)).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₀₂) (pdRelSub (U ∪ V : Set M) K₀₂)
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrV₀
  have hy1' : goodD N c U hU K₀₁ hK₀₁U hK₀₁c k m hkm (rU₀ y₁)
      = goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁) := by
    rw [hrU₀, hy1, hs, htU]
  -- Step 7: injectivity of the duality map of `U`
  have hK₁p0U : K₁' ∪ K₀₁ ⊆ U := Set.union_subset hK₁'U hK₀₁U
  have hK₁p0c : IsCompact (K₁' ∪ K₀₁) := hK₁'c.union hK₀₁c
  have hkillU : goodD N c U hU (K₁' ∪ K₀₁) hK₁p0U hK₁p0c k m hkm
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
          (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁)) k) (rU x₁)
        - (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
          (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁)) k) (rU₀ y₁)) = 0 := by
    rw [goodD_sub c hU hK₁p0U hK₁p0c k m hkm]
    rw [pd_goodD_natural N c U hU (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁) hK₁'U hK₁p0U
          hK₁'c hK₁p0c k m hkm (rU x₁),
        pd_goodD_natural N c U hU (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁) hK₀₁U hK₁p0U
          hK₀₁c hK₁p0c k m hkm (rU₀ y₁),
        hy1']
    exact sub_self _
  obtain ⟨K₁'', hK₁p0K₁'', hK₁''U, hK₁''c, hkillU'⟩ :=
    hUU.kill k m hkm (K₁' ∪ K₀₁) hK₁p0U hK₁p0c _ hkillU
  -- the enlarged classes on `U` agree
  have hUcomp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of U) (pdRelSub U A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge U (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) U h h' k]
    rfl
  have hUeq : (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
        ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU x₁)
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
        ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU₀ y₁) := by
    have h : (HomologicalComplex.homologyMap (pdRelComplexEnlarge U hK₁p0K₁'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁)) k) (rU x₁))
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U hK₁p0K₁'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁)) k) (rU₀ y₁)) := by
      have hh := hkillU'
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    rw [← hUcomp (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁) hK₁p0K₁'' (rU x₁),
      ← hUcomp (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁) hK₁p0K₁'' (rU₀ y₁)] at h
    exact h
  clear hkillU hkillU' hK₀K₀₁ hK₀K₀₂ hy1
  -- Step 8: transport to `U ∪ V` using excision
  have hWeq1 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) x₁
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) y₁ := by
    set rjU := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₁'') (pdRelSub (U ∪ V : Set M) K₁'')
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrjU
    haveI : IsIso rjU := by
      rw [hrjU]
      exact pdCohExcision Set.subset_union_left hU hW hK₁''U hK₁''c k
    have hinj : Function.Injective (ConcreteCategory.hom rjU) :=
      (ModuleCat.mono_iff_injective rjU).mp inferInstance
    have hres1 : (ConcreteCategory.hom rjU)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) x₁)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU x₁) := by
      rw [hrjU, hrU]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₁')).homology k
          ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁'')).homology k) =>
        (ConcreteCategory.hom f) x₁)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := U) (K := K₁') (K' := K₁'')
          Set.subset_union_left hK₁'U hK₁''U
          ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'') k)
    have hres2 : (ConcreteCategory.hom rjU)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) y₁)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU₀ y₁) := by
      rw [hrjU, hrU₀]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₀₁)).homology k
          ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁'')).homology k) =>
        (ConcreteCategory.hom f) y₁)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := U) (K := K₀₁) (K' := K₁'')
          Set.subset_union_left hK₀₁U hK₁''U
          ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'') k)
    exact hinj (by rw [hres1, hres2, hUeq])
  clear hUeq
  -- Step 9: the same for `V`
  have hy2' : goodD N c V hV K₀₂ hK₀₂V hK₀₂c k m hkm (rV₀ y₂)
      = goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂) := by
    rw [hrV₀, hrV, hy2, hs, htV]
  have hK₂p0V : K₂' ∪ K₀₂ ⊆ V := Set.union_subset hK₂'V hK₀₂V
  have hK₂p0c : IsCompact (K₂' ∪ K₀₂) := hK₂'c.union hK₀₂c
  have hkillV : goodD N c V hV (K₂' ∪ K₀₂) hK₂p0V hK₂p0c k m hkm
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
          (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂)) k) (rV x₂)
        - (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
          (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂)) k) (rV₀ y₂)) = 0 := by
    rw [goodD_sub c hV hK₂p0V hK₂p0c k m hkm]
    rw [pd_goodD_natural N c V hV (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂) hK₂'V hK₂p0V
          hK₂'c hK₂p0c k m hkm (rV x₂),
        pd_goodD_natural N c V hV (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂) hK₀₂V hK₂p0V
          hK₀₂c hK₂p0c k m hkm (rV₀ y₂),
        hy2']
    exact sub_self _
  obtain ⟨K₂'', hK₂p0K₂'', hK₂''V, hK₂''c, hkillV'⟩ :=
    hVV.kill k m hkm (K₂' ∪ K₀₂) hK₂p0V hK₂p0c _ hkillV
  have hVcomp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of V) (pdRelSub V A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge V (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) V h h' k]
    rfl
  have hVeq : (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
        ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV x₂)
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
        ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV₀ y₂) := by
    have h : (HomologicalComplex.homologyMap (pdRelComplexEnlarge V hK₂p0K₂'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂)) k) (rV x₂))
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V hK₂p0K₂'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂)) k) (rV₀ y₂)) := by
      have hh := hkillV'
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    rw [← hVcomp (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂) hK₂p0K₂'' (rV x₂),
      ← hVcomp (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂) hK₂p0K₂'' (rV₀ y₂)] at h
    exact h
  have hWeq2 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) x₂
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) y₂ := by
    set rjV := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₂'') (pdRelSub (U ∪ V : Set M) K₂'')
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrjV
    haveI : IsIso rjV := by
      rw [hrjV]
      exact pdCohExcision Set.subset_union_right hV hW hK₂''V hK₂''c k
    have hinj : Function.Injective (ConcreteCategory.hom rjV) :=
      (ModuleCat.mono_iff_injective rjV).mp inferInstance
    have hres1 : (ConcreteCategory.hom rjV)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) x₂)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV x₂) := by
      rw [hrjV, hrV]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₂')).homology k
          ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂'')).homology k) =>
        (ConcreteCategory.hom f) x₂)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := V) (K := K₂') (K' := K₂'')
          Set.subset_union_right hK₂'V hK₂''V
          ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'') k)
    have hres2 : (ConcreteCategory.hom rjV)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) y₂)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV₀ y₂) := by
      rw [hrjV, hrV₀]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₀₂)).homology k
          ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂'')).homology k) =>
        (ConcreteCategory.hom f) y₂)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := V) (K := K₀₂) (K' := K₂'')
          Set.subset_union_right hK₀₂V hK₂''V
          ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'') k)
    exact hinj (by rw [hres1, hres2, hVeq])
  clear hVeq hkillV hkillV' hy2 hy2'
  -- Step 10: assembly
  have hin1 : K₁' ⊆ K₁'' :=
    (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁''
  have hin0 : K₀₁ ⊆ K₁'' :=
    (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁''
  have hin2 : K₂' ⊆ K₂'' :=
    (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂''
  have hin02 : K₀₂ ⊆ K₂'' :=
    (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂''
  have hsub1 : K₁'' ⊆ K₁'' ∪ K₂'' := Set.subset_union_left
  have hsub2 : K₂'' ⊆ K₁'' ∪ K₂'' := Set.subset_union_right
  have hK1'' : K₁' ⊆ K₁'' ∪ K₂'' := hin1.trans hsub1
  have hK0'' : K₀₁ ⊆ K₁'' ∪ K₂'' := hin0.trans hsub1
  have hK2'' : K₂' ⊆ K₁'' ∪ K₂'' := hin2.trans hsub2
  have hK02'' : K₀₂ ⊆ K₁'' ∪ K₂'' := hin02.trans hsub2
  have huni : K₀₁ ∪ K₀₂ ⊆ K₁'' ∪ K₂'' := Set.union_subset_union hin0 hin02
  have hmid2 : K₁' ∪ K₂' ⊆ K₁'' ∪ K₂'' := Set.union_subset_union hin1 hin2
  have hK'U : K₁'' ∪ K₂'' ⊆ (U ∪ V : Set M) := Set.union_subset_union hK₁''U hK₂''V
  have hK'c : IsCompact (K₁'' ∪ K₂'') := hK₁''c.union hK₂''c
  have hKK' : K ⊆ K₁'' ∪ K₂'' := hK12.trans (hmid.trans hmid2)
  -- evaluation forms of the enlargement identities
  have evCongr : ∀ {A B : Set M} (h h' : A ⊆ B)
      (z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h') k) z := by
    intro A B h h' z
    exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k
        ⟶ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) B)).homology k) => (ConcreteCategory.hom f) z)
      (congrArg (fun (g : relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) A) ⟶ relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) B)) => HomologicalComplex.homologyMap g k)
        (pdRelComplexEnlarge_congr_h (U ∪ V : Set M) h h'))
  have evComp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) (U ∪ V : Set M) h h' k]
    rfl
  -- the two `x`-sides agree
  have key : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK1'') k) x₁
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK2'') k) x₂ := by
    calc (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK1'') k) x₁
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub1) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin1) k) x₁) :=
          evComp hin1 hsub1 x₁
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub1) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin0) k) y₁) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin1) k) x₁
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin0) k) y₁
              from hWeq1]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK0'') k) y₁ :=
          (evComp hin0 hsub1 y₁).symm
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) huni) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
              (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂)) k) y₁) := by
          rw [evCongr hK0'' ((Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂).trans huni) y₁]
          exact evComp (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂) huni y₁
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) huni) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
              (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂)) k) y₂) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂)) k) y₁
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂)) k) y₂ from hy3]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK02'') k) y₂ := by
          rw [evCongr ((Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂).trans huni) hK02'' y₂]
          exact (evComp (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂) huni y₂).symm
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub2) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin02) k) y₂) := by
          rw [evCongr hK02'' (hin02.trans hsub2) y₂]
          exact evComp hin02 hsub2 y₂
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub2) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin2) k) x₂) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin02) k) y₂
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin2) k) x₂
              from hWeq2.symm]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK2'') k) x₂ :=
          (evComp hin2 hsub2 x₂).symm
  refine ⟨K₁'' ∪ K₂'', hKK', hK'U, hK'c, ?_⟩
  rw [evCongr hKK' (hK12.trans (hmid.trans hmid2))]
  rw [evComp hK12 (hmid.trans hmid2)]
  rw [evComp hmid hmid2]
  rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK12) k) x = x₀
      from hx₀def.symm]
  rw [hsplit, map_sub]
  rw [← evComp (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂') hmid2 x₁,
    ← evComp (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂') hmid2 x₂,
    evCongr ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂').trans hmid2) hK1'' x₁,
    evCongr ((Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂').trans hmid2) hK2'' x₂,
    key, sub_self]

/-! ## The target theorem -/

theorem pd_union_kill_chart {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (hvan : ∀ k, N < k → ∀ K : Set M, K ⊆ U ∩ V → IsCompact K →
        ∃ K' : Set M, K ⊆ K' ∧ K' ⊆ U ∩ V ∧ IsCompact K' ∧
          Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∩ V : Set M))
            (Work.Cohomology.pdRelSub (U ∩ V : Set M) K')).homology k))
    (k m : ℕ) (hkm : k + m = N) :
    ∀ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
       (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K)).homology k),
       Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x = 0 →
       ∃ (K' : Set M) (hKK' : K ⊆ K') (hK'W : K' ⊆ U ∪ V) (hK'c : IsCompact K'),
         (HomologicalComplex.homologyMap
            (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M) hKK') k) x = 0 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact pd_kill_of_split hU hV hI hUU hVV hII k m hkm
      (pd_split_kc_zero hU hV hI hUU hVV hII hvan k m hkm hm0)
  · exact pd_union_kill_pos hU hV hI hUU hVV hII k m hkm hmpos

end

end Work.Cohomology
