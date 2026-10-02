import Mathlib
import Submission.Work.Cohomology.pd_crux_weak2
import Submission.Work.Cohomology.pd_crux_weak3
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.mem_range_inclChains_of_image

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chain-level form of the crux square

The crux square of Hatcher's Lemma 3.36 (the third square of the Mayer–Vietoris diagram for
Poincaré duality) is, on the level of the *homology* of the two pieces, the statement that the
capping map commutes with the Mayer–Vietoris boundary.  This file proves the chain-level form
requested by the gluing step, `Work.Cohomology.pd_crux_chain`.

Setting: `W = U ∪ V`, and `φ = φA - φB` are degree-`k` cochains on `W` with
`φA ∈ C^k(W, W∖K)` and `φB ∈ C^k(W, W∖L)`, and `φ` a cocycle.  The chains
`α₁, α₂, α₃ ∈ C_{k+mj+1}(W)` are supported in `W ∩ (U∖L)`, `W ∩ (U∩V)` and `W ∩ (V∖K)`,
and their boundaries satisfy `dα₁ ∈ C_{k+mj}(W∖L)`, `dα₃ ∈ C_{k+mj}(W∖K)` and
`d(α₁+α₂+α₃) ∈ C_{k+mj}(W∖(K∪L))`.

The conclusion is that there are chains `a ∈ C_{mj+1}(U)`, `b ∈ C_{mj+1}(V)` and a cycle
`w ∈ Z_mj(U∩V)` such that

* `a` and `b` cap `φ` with `α₁` and with `-(α₂ + α₃)` respectively;
* `dw` is the common boundary of the two chains (`d a` in `U`, `d b` in `V`);
* the remaining discrepancy is the explicit boundary `d (φA ⌢ α₂)` (times `(-1)^{k+1}`), which
  is the image of the `∩`-slot of the square.

The mathematical content is the chain-level computation of the crux square
(`Work.Cohomology.pd_crux_key` below, the `key` identity of `pd_crux_weak3` with its witness),
together with the support statements.

## Main statements

* `chainMap_cast_apply` — a chain map commutes with the transport of chains along an equality of
  degrees;
* `inclChainsSub_injective` — the inclusion `C_*(A) ⟶ C_*(B)` for `A ⊆ B ⊆ X` is injective;
* `cast_mem_range_inclChains` — support is invariant under a change of degree;
* `d_mem_range_inclChains_succ`, `d_mem_range_inclChains_one` — the boundary of a chain
  supported in `S` is supported in `S` (in the two degree conventions used here);
* `pd_crux_key` — the chain identity `d(α₁⌢φ) - (-1)^{k+1} (δφA ⌢ α₂) = d(-(φA ⌢ α₂))`;
* `pd_crux_chain` — the goal.

Implementation note: the proofs are sensitive to *syntactic* form (Lean's `rw` matches terms up
to reducible equality only), so the arguments of `HomologicalComplex.Hom.comm` /
`inclChainsSub_comp` are transported to the presentation used in the statements through explicit
`have`s, and the lemmas about the ambient `TopCat.of W` are called with their space argument
given explicitly (`M := TopCat.of W`), which keeps type class synthesis cheap.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Elementary lemmas on chain maps -/

/-- **A chain map commutes with the transport of chains along a change of degrees.** -/
lemma chainMap_cast_apply {C D : ChainComplex (ModuleCat ℤ) ℕ} (g : C ⟶ D) {a b : ℕ} (h : a = b)
    (x : ↑(C.X a)) :
    (ModuleCat.Hom.hom (g.f b)) (h ▸ x) = h ▸ ((ModuleCat.Hom.hom (g.f a)) x) := by
  cases h
  simp

/-- **The inclusion of the chains of a smaller subset is injective.** -/
lemma inclChainsSub_injective {X : TopCat} {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    Function.Injective ((inclChainsSub X A B h).f n).hom := by
  intro x y hxy
  have h1 := congrArg (fun (g : singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ X) =>
    (ModuleCat.Hom.hom (g.f n)) x) (inclChainsSub_comp X A B h)
  have h2 := congrArg (fun (g : singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ X) =>
    (ModuleCat.Hom.hom (g.f n)) y) (inclChainsSub_comp X A B h)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  apply inclChains_f_injective X A n
  rw [← h1, ← h2, hxy]

/-- **Support is invariant under a change of degree.** -/
lemma cast_mem_range_inclChains {X : TopCat} {S : Set X} {a b : ℕ} (h : a = b)
    {x : (singularChains ℤ X).X a} (hx : x ∈ LinearMap.range ((inclChains X S).f a).hom) :
    (h ▸ x) ∈ LinearMap.range ((inclChains X S).f b).hom := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨h ▸ y, ?_⟩
  rw [chainMap_cast_apply, hy]

/-- **The boundary of a chain supported in `S` is supported in `S`**, in the degrees
`n + (m+1) → n + m` used by the crux square. -/
lemma d_mem_range_inclChains_succ {X : TopCat} (S : Set X) {n m : ℕ}
    {α : (singularChains ℤ X).X (n + (m + 1))}
    (hα : α ∈ LinearMap.range ((inclChains X S).f (n + (m + 1))).hom) :
    (singularChains ℤ X).d (n + (m + 1)) (n + m) α
      ∈ LinearMap.range ((inclChains X S).f (n + m)).hom := by
  obtain ⟨y, hy⟩ := hα
  refine ⟨(singularChains ℤ (TopCat.of S)).d (n + (m + 1)) (n + m) y, ?_⟩
  have hcomm := HomologicalComplex.Hom.comm (inclChains X S) (n + (m + 1)) (n + m)
  have h := congrArg (fun (g : (singularChains ℤ (TopCat.of S)).X (n + (m + 1)) ⟶
      (singularChains ℤ X).X (n + m)) => (ModuleCat.Hom.hom g) y) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hy] at h
  exact h.symm

/-- **The boundary of a chain supported in `S` is supported in `S`**, in the degrees
`n + 1 → n`. -/
lemma d_mem_range_inclChains_one {X : TopCat} (S : Set X) {n : ℕ}
    {α : (singularChains ℤ X).X (n + 1)}
    (hα : α ∈ LinearMap.range ((inclChains X S).f (n + 1)).hom) :
    (singularChains ℤ X).d (n + 1) n α ∈ LinearMap.range ((inclChains X S).f n).hom := by
  obtain ⟨y, hy⟩ := hα
  refine ⟨(singularChains ℤ (TopCat.of S)).d (n + 1) n y, ?_⟩
  have hcomm := HomologicalComplex.Hom.comm (inclChains X S) (n + 1) n
  have h := congrArg (fun (g : (singularChains ℤ (TopCat.of S)).X (n + 1) ⟶
      (singularChains ℤ X).X n) => (ModuleCat.Hom.hom g) y) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hy] at h
  exact h.symm

/-! ## The chain-level computation of the crux square -/

/-- **The chain identity of the crux square.**  With `W = U ∪ V`, a cocycle `φ = φA - φB` whose
parts are relative for `W∖K` and `W∖L`, and chains `α₁, α₂, α₃` supported in `W∩(U∖L)`, `W∩(U∩V)`
and `W∩(V∖K)` whose boundaries satisfy the support hypotheses of the crux square,

  `d(α₁ ⌢ φ) - (-1)^(k+1) · ((δφA) ⌢ α₂) = d (-(φA ⌢ α₂))`. -/
theorem pd_crux_key {M : TopCat} {U V K L : Set M} {k mj : ℕ}
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (hφA : φA ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) k)
    (hφB : φB ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) k)
    (hlift : φ = φA - φB)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φ = 0)
    (α₁ α₂ α₃ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hdα₁ : ∃ e, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) L)).f (k + mj) e
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁)
    (hdα₃ : ∃ f, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) K)).f (k + mj) f
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₃)
    (hd : ∃ g, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj) g
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj)
            (α₁ + α₂ + α₃)) :
    (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) • cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj
          ((capIdx k mj) ▸ α₂)
      = (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
          (- cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA (mj + 1) α₂) := by
  obtain ⟨e, he⟩ := hdα₁
  obtain ⟨f, hf⟩ := hdα₃
  obtain ⟨g, hg⟩ := hd
  have hzeroB : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φB mj
      ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he]
    exact cap_inclChains_eq_zero (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) φB hφB mj e
  have hzeroA3 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
      ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf]
    exact cap_inclChains_eq_zero (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) φA hφA mj f
  have hzeroAtot : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
      ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj)
        (α₁ + α₂ + α₃)) = 0 := by
    rw [← hg]
    exact cap_eq_zero_of_supported (M := TopCat.of ↥(U ∪ V))
      (pdRelSub_mono (Set.subset_union_left : K ⊆ K ∪ L)) φA hφA ⟨g, rfl⟩
  have hdT : (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj)
        (α₁ + α₂ + α₃)
      = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [map_add, map_add]
  have hcapA1 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
      ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
          ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂) := by
    have h : (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
          - (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂
          - (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₃ := by
      rw [hdT]; abel
    rw [h, map_sub, map_sub, hzeroAtot, hzeroA3, zero_sub, sub_zero]
  have hP : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ mj
      ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
          ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hcapA1]
  have hA : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ mj
          ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans (int_smul_eq_zsmul (inferInstance : Module ℤ
      (↑((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X mj))) ((-1 : ℤ) ^ k) _)
  have hB : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
            ((singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
              (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj
              ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) (m := mj) φA α₂
    exact h.trans (int_smul_eq_zsmul (inferInstance : Module ℤ
      (↑((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X mj))) ((-1 : ℤ) ^ k) _)
  rw [map_neg, hA, hP, hB]
  rw [zsmul_neg]
  rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
  abel

/-! ## The gluing statement -/

theorem pd_crux_chain {M : TopCat} {U V : Set M} {K L : Set M} {k mj : ℕ}
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (hφA : φA ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) K) k)
    (hφB : φB ∈ relKern ℤ (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) L) k)
    (hlift : φ = φA - φB)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φ = 0)
    (α₁ α₂ α₃ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hα₁ : ∃ a', (inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U \ L))).f (k + (mj + 1)) a' = α₁)
    (hα₂ : ∃ b', (inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1)) b' = α₂)
    (hα₃ : ∃ d', (inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (V \ K))).f (k + (mj + 1)) d' = α₃)
    (hdα₁ : ∃ e, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) L)).f (k + mj) e
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₁)
    (hdα₃ : ∃ f, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) K)).f (k + mj) f
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj) α₃)
    (hd : ∃ g, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj) g
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d (k + (mj + 1)) (k + mj)
            (α₁ + α₂ + α₃)) :
    ∃ (a : (singularChains ℤ (TopCat.of ↥U)).X (mj + 1))
      (b : (singularChains ℤ (TopCat.of ↥V)).X (mj + 1))
      (w : (singularChains ℤ (TopCat.of ↥(U ∩ V))).cycles mj),
      (chainMap ℤ (TopCat.of ↥U) (TopCat.of ↥(U ∪ V))
          (pdIncl (U ∪ V) U Set.subset_union_left)).f (mj + 1) a
        = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁
      ∧ (chainMap ℤ (TopCat.of ↥V) (TopCat.of ↥(U ∪ V))
          (pdIncl (U ∪ V) V Set.subset_union_right)).f (mj + 1) b
        = - (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂
             + cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃)
      ∧ (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V)).f mj
            ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles mj w)
          = (singularChains ℤ (TopCat.of ↥U)).d (mj + 1) mj a
      ∧ (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)).f mj
            ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles mj w)
          = (singularChains ℤ (TopCat.of ↥V)).d (mj + 1) mj b
      ∧ (∃ (s : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X (mj + 1)),
          (inclChains M (U ∩ V)).f mj ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles mj w)
            = (inclChains M (U ∩ V)).f mj
                ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (mj + 1) mj s)
              + (-1 : ℤ) ^ (k + 1) • (inclChains M (U ∪ V)).f mj
                  (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
                    (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
                      (n := k) φA) mj ((capIdx k mj) ▸ α₂))) := by
  classical
  -- copies, kept for the later application of `pd_crux_key` (`obtain` consumes the originals)
  have hdcopy₁ := hdα₁
  have hdcopy₃ := hdα₃
  have hdcopy := hd
  obtain ⟨e, he⟩ := hdα₁
  obtain ⟨f, hf⟩ := hdα₃
  obtain ⟨g, hg⟩ := hd
  have hgC : (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) (K ∪ L))).f (k + mj) g
      = (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (k + (mj + 1)) (k + mj)
          (α₁ + α₂ + α₃) := hg
  have hzeroT : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ mj
      ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (k + (mj + 1)) (k + mj)
        (α₁ + α₂ + α₃)) = 0 := by
    rw [hlift, cap_sub_apply]
    have h1 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
        ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (k + (mj + 1)) (k + mj)
          (α₁ + α₂ + α₃)) = 0 := by
      rw [← hgC]
      exact cap_eq_zero_of_supported (M := TopCat.of ↥(U ∪ V))
        (pdRelSub_mono (Set.subset_union_left : K ⊆ K ∪ L)) φA hφA ⟨g, rfl⟩
    have h2 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φB mj
        ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (k + (mj + 1)) (k + mj)
          (α₁ + α₂ + α₃)) = 0 := by
      rw [← hgC]
      exact cap_eq_zero_of_supported (M := TopCat.of ↥(U ∪ V))
        (pdRelSub_mono (Set.subset_union_right : L ⊆ K ∪ L)) φB hφB ⟨g, rfl⟩
    rw [h1, h2, sub_zero]
  have hcons : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁)
      = (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
          (- (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂
            + cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃)) := by
    have h0 : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
        (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) (α₁ + α₂ + α₃)) = 0 := by
      have h := cap_d ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) (m := mj) φ
        (α₁ + α₂ + α₃)
      rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
      rw [h, hzeroT, smul_zero]
    have hsplit : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
          (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) (α₁ + α₂ + α₃))
        = (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
            (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁)
          + (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
            (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂)
          + (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
            (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃) := by
      rw [show cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) (α₁ + α₂ + α₃)
          = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁
            + cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂
            + cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃ by
        rw [map_add, map_add]]
      rw [map_add, map_add]
    rw [hsplit] at h0
    rw [map_neg, map_add]
    exact eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact h0)
  have hcap1supp : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U \ L))).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U \ L)) k (mj + 1) φ hα₁
  have hcap1U : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) U)).f (mj + 1)).hom :=
    range_inclChains_mono (X := TopCat.of ↥(U ∪ V)) (pdTr_mono (Set.sdiff_subset : U \ L ⊆ U)) (mj + 1) hcap1supp
  obtain ⟨a, ha⟩ := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := U)
    (Set.subset_union_left) hcap1U
  have hcap2supp : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) k (mj + 1) φ hα₂
  have hcap3supp : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (V \ K))).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (V \ K)) k (mj + 1) φ hα₃
  have hsumV : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₂
        + cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₃
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) V)).f (mj + 1)).hom :=
    add_mem (range_inclChains_mono (X := TopCat.of ↥(U ∪ V)) (pdTr_mono (Set.inter_subset_right : U ∩ V ⊆ V))
        (mj + 1) hcap2supp)
      (range_inclChains_mono (X := TopCat.of ↥(U ∪ V)) (pdTr_mono (Set.sdiff_subset : V \ K ⊆ V)) (mj + 1) hcap3supp)
  obtain ⟨b, hb⟩ := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := V)
    (Set.subset_union_right) (neg_mem hsumV)
  have hcapA2supp : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA mj
      ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (k + (mj + 1)) (k + mj) α₂)
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f mj).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) k mj φA
      (d_mem_range_inclChains_succ (X := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) hα₂)
  have hcast : ((capIdx k mj) ▸ α₂)
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f ((k + 1) + mj)).hom :=
    cast_mem_range_inclChains (X := TopCat.of ↥(U ∪ V)) (S := pdTr (U ∪ V) (U ∩ V))
      (a := k + (mj + 1)) (b := (k + 1) + mj) (capIdx k mj) hα₂
  have hcapδsupp : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj
        ((capIdx k mj) ▸ α₂)
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f mj).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) (k + 1) mj
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) hcast
  have hnegA2supp : - cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA (mj + 1) α₂
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f (mj + 1)).hom :=
    neg_mem (cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) k (mj + 1) φA hα₂)
  have hdneg : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
      (- cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φA (mj + 1) α₂)
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f mj).hom :=
    d_mem_range_inclChains_one (X := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V)) hnegA2supp
  have hkey := pd_crux_key (M := M) (U := U) (V := V) (K := K) (L := L)
    (k := k) (mj := mj) φ φA φB hφA hφB hlift hφd α₁ α₂ α₃ hdcopy₁ hdcopy₃ hdcopy
  have hbnd : (chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj
      (cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) φ (mj + 1) α₁)
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U ∩ V))).f mj).hom := by
    rw [sub_eq_iff_eq_add] at hkey
    rw [hkey]
    refine add_mem hdneg ?_
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ _) ((-1 : ℤ) ^ (k + 1)) _]
    exact Submodule.smul_mem _ _ hcapδsupp
  have hUV : (U ∩ V : Set M) ⊆ U ∪ V := Set.inter_subset_left.trans Set.subset_union_left
  obtain ⟨x, hx⟩ := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := U ∩ V) hUV hbnd
  have hxW : (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x
      = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1) α₁) := hx
  have hxcyc : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d mj (mj - 1))) x = 0 := by
    apply inclChainsSub_injective hUV (mj - 1)
    show (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj - 1)))
        ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d mj (mj - 1))) x)
      = (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj - 1))) 0
    rw [map_zero]
    have hc := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).X mj) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X (mj - 1))) =>
        (ConcreteCategory.hom g) x)
      (HomologicalComplex.Hom.comm (inclChainsSub M (U ∩ V) (U ∪ V) hUV) mj (mj - 1))
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hc
    have hc' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d mj (mj - 1)))
          ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x)
        = (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj - 1)))
            ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d mj (mj - 1))) x) := hc
    rw [← hc', hxW]
    have hdd : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d mj (mj - 1)))
        ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁)) = 0 := by
      have h := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X (mj + 1)) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X (mj - 1))) =>
          (ConcreteCategory.hom g) (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁))
        (((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))))).d_comp_d (mj + 1) mj (mj - 1))
      rw [ModuleCat.comp_apply] at h
      exact h
    exact hdd
  obtain ⟨s, hs⟩ := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := U ∩ V)
    hUV hnegA2supp
  refine ⟨a, b, cycleOf mj x hxcyc, ha, hb, ?_, ?_, ?_⟩
  · -- the `U`-component
    rw [iCycles_cycleOf]
    have hcomp : (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V))
        ≫ (chainMap ℤ (TopCat.of ↥U) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) U (Set.subset_union_left : U ⊆ U ∪ V)))
        = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V))
            (pdIncl (U ∪ V) (U ∩ V) hUV) := by
      rw [chainMap_compPD]
      congr 1
    have h1 := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))))) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))))) =>
        (ConcreteCategory.hom (g.f mj)) x) hcomp
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h1
    have h1b : (ConcreteCategory.hom (((inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))).f mj))
          ((ConcreteCategory.hom ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U)
            (inclUVU U V)).f mj)) x)
        = (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x := h1
    have hL := h1b.trans hxW
    have ha' : (ConcreteCategory.hom (((inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))).f (mj + 1))) a
        = ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁ := ha
    have hc := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥U))).X (mj + 1)) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X mj)) =>
        (ConcreteCategory.hom g) a)
      (HomologicalComplex.Hom.comm (inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))
        (mj + 1) mj)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hc
    have hc' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
          ((ConcreteCategory.hom (((inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))).f (mj + 1))) a)
        = (ConcreteCategory.hom (((inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))).f mj)) ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥U))).d (mj + 1) mj)) a) := hc
    have hR : (ConcreteCategory.hom (((inclChainsSub M U (U ∪ V) (Set.subset_union_left : U ⊆ U ∪ V))).f mj)) ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥U))).d (mj + 1) mj)) a)
        = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁) :=
      hc'.symm.trans (congrArg (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) ha')
    exact inclChainsSub_injective (Set.subset_union_left : U ⊆ U ∪ V) mj (hL.trans hR.symm)
  · -- the `V`-component
    rw [iCycles_cycleOf]
    have hcomp : (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V))
        ≫ (chainMap ℤ (TopCat.of ↥V) (TopCat.of ↥(U ∪ V)) (pdIncl (U ∪ V) V (Set.subset_union_right : V ⊆ U ∪ V)))
        = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V))
            (pdIncl (U ∪ V) (U ∩ V) hUV) := by
      rw [chainMap_compPD]
      congr 1
    have h1 := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))))) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))))) =>
        (ConcreteCategory.hom (g.f mj)) x) hcomp
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h1
    have h1b : (ConcreteCategory.hom (((inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))).f mj))
          ((ConcreteCategory.hom ((chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V)
            (inclUVV U V)).f mj)) x)
        = (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x := h1
    have hL := h1b.trans hxW
    have hb' : (ConcreteCategory.hom (((inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))).f (mj + 1))) b
        = - (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₂ + ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₃) := hb
    have hc := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥V))).X (mj + 1)) ⟶ ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X mj)) =>
        (ConcreteCategory.hom g) b)
      (HomologicalComplex.Hom.comm (inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))
        (mj + 1) mj)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hc
    have hc' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
          ((ConcreteCategory.hom (((inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))).f (mj + 1))) b)
        = (ConcreteCategory.hom (((inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))).f mj)) ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥V))).d (mj + 1) mj)) b) := hc
    have hcons' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
          (- (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₂ + ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₃))
        = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁) := hcons.symm
    have hR : (ConcreteCategory.hom (((inclChainsSub M V (U ∪ V) (Set.subset_union_right : V ⊆ U ∪ V))).f mj)) ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥V))).d (mj + 1) mj)) b)
        = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φ (mj + 1)) α₁) :=
      hc'.symm.trans ((congrArg (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj)) hb').trans hcons')
    exact inclChainsSub_injective (Set.subset_union_right : V ⊆ U ∪ V) mj (hL.trans hR.symm)
  · -- the discrepancy is a boundary coming from `U ∩ V`
    rw [iCycles_cycleOf]
    refine ⟨s, ?_⟩
    have hs' : (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s
        = - ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) φA (mj + 1)) α₂ := hs
    have hWeq : (ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x
        = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
            ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s)
          + (-1 : ℤ) ^ (k + 1) • ((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))))
              (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) (n := k) φA) mj)
              ((capIdx k mj) ▸ α₂) := by
      rw [hxW, hs']
      rw [sub_eq_iff_eq_add] at hkey
      exact hkey
    have happ := congrArg (fun y =>
      (ConcreteCategory.hom ((inclChains M (U ∪ V)).f mj)) y) hWeq
    rw [map_add, map_zsmul] at happ
    have h1 : (ConcreteCategory.hom ((inclChains M (U ∪ V)).f mj))
        ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f mj)) x)
        = (ConcreteCategory.hom ((inclChains M (U ∩ V)).f mj)) x := by
      have h := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))))) ⟶ ((chainC ℤ (TopCat.toSSet.obj M)))) =>
          (ConcreteCategory.hom (g.f mj)) x) (inclChainsSub_comp M (U ∩ V) (U ∪ V) hUV)
      rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
      exact h
    have hpair : (ConcreteCategory.hom ((inclChains M (U ∪ V)).f (mj + 1)))
          ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s)
        = (ConcreteCategory.hom ((inclChains M (U ∩ V)).f (mj + 1))) s := by
      have h := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))))) ⟶ ((chainC ℤ (TopCat.toSSet.obj M)))) =>
          (ConcreteCategory.hom (g.f (mj + 1))) s) (inclChainsSub_comp M (U ∩ V) (U ∪ V) hUV)
      rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
      exact h
    have hW := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).X (mj + 1)) ⟶ ((chainC ℤ (TopCat.toSSet.obj M)).X mj)) =>
        (ConcreteCategory.hom g) ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s))
      (HomologicalComplex.Hom.comm (inclChains M (U ∪ V)) (mj + 1) mj)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hW
    have h2 : (ConcreteCategory.hom ((inclChains M (U ∪ V)).f mj))
        ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
          ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s))
        = (ConcreteCategory.hom ((inclChains M (U ∩ V)).f mj))
            ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj)) s) := by
      have hW' : (ConcreteCategory.hom ((inclChains M (U ∪ V)).f mj))
            ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))).d (mj + 1) mj))
              ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s))
          = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
              ((ConcreteCategory.hom ((inclChains M (U ∪ V)).f (mj + 1)))
                ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s)) := hW.symm
      have hW'' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
              ((ConcreteCategory.hom ((inclChains M (U ∪ V)).f (mj + 1)))
                ((ConcreteCategory.hom (((inclChainsSub M (U ∩ V) (U ∪ V) hUV)).f (mj + 1))) s))
          = (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
              ((ConcreteCategory.hom ((inclChains M (U ∩ V)).f (mj + 1))) s) :=
        congrArg (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)) hpair
      have h2' : (ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
              ((ConcreteCategory.hom ((inclChains M (U ∩ V)).f (mj + 1))) s)
          = (ConcreteCategory.hom ((inclChains M (U ∩ V)).f mj))
              ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj)) s) := by
        have h := congrArg (fun (g : ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).X (mj + 1)) ⟶ ((chainC ℤ (TopCat.toSSet.obj M)).X mj)) =>
            (ConcreteCategory.hom g) s)
          (HomologicalComplex.Hom.comm (inclChains M (U ∩ V)) (mj + 1) mj)
        rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
        exact h
      exact hW'.trans (hW''.trans h2')
    have hfin : (ConcreteCategory.hom ((inclChains M (U ∩ V)).f mj)) x
        = (ConcreteCategory.hom ((inclChains M (U ∩ V)).f mj))
            ((ConcreteCategory.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))).d (mj + 1) mj)) s)
          + (-1 : ℤ) ^ (k + 1) • (ConcreteCategory.hom ((inclChains M (U ∪ V)).f mj))
              (((cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V)))
                (n := k) φA) mj) ((capIdx k mj) ▸ α₂)) :=
      h1.symm.trans (happ.trans (by rw [h2]))
    exact hfin

end

end Work.Cohomology
