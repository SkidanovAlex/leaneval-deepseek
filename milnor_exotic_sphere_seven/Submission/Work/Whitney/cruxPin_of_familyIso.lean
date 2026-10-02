import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Gen.eSymClass
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.Thom.Iso
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.LerayHirsch.WhitneySumAssoc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# `Work.Whitney.cruxPin_of_familyIso`

If the "delta form" of the top Chern class of an `N`-fold sum of line bundles holds for a family `M`
(`hδ`), and the corresponding "crux" identity
`c_{N-1}(lineSumCore N M₀) = eSym N M₀ (N-1)` is *known* for a family `M₀` that is *fibrewise
isomorphic* to `M` (`hiso`, `hM₀`), then the degree-`0` class `δ` of the delta form is forced to be
the unit class `1 ∈ H⁰(B;ℤ)`, provided

* `eSym N M₀ (N-1)` is not a torsion class (`hfree`), and
* `H⁰(B;ℤ) = ℤ·1` (`hspan`).

The mathematics is a two-line computation: isomorphism invariance of the Chern classes
(`Work.Thom.chernClass_BundleIso`) transports the crux from `M₀` to `M`, fibrewise isomorphism
invariance of `eSym` (`Work.Gen.eSymC_congr` + `Work.Thom.chernClass_BundleIso`) identifies
`eSym N M (N-1)` with `eSym N M₀ (N-1)`, and the delta form `c_{N-1}W = δ ⌣ eSym N M (N-1)`
combined with `δ = k·1` (from `hspan`) and the unit law `1 ⌣ x = x` gives
`k · eSym N M₀ (N-1) = eSym N M₀ (N-1)`, so `(k-1) · eSym N M₀ (N-1) = 0` and `k = 1` by `hfree`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **Congruence of the iterated sum of line bundles in its family of summands.**  Isomorphisms of
the summands induce an isomorphism of the iterated sums; the two families may live over *different*
covers.  (The statement of `Work.LerayHirsch.nonempty_bundleIso_lineSumCore_cover`, reproduced here
so that this module does not have to import the flag-bundle and Leray–Hirsch machinery.) -/
theorem nonempty_bundleIso_lineSumCore_family {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (n : ℕ)
    (L : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (L' : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι')
    (h : ∀ i, Nonempty (Work.Thom.BundleIso (L i) (L' i))) :
    Nonempty (Work.Thom.BundleIso (Work.LerayHirsch.lineSumCore n L)
      (Work.LerayHirsch.lineSumCore n L')) := by
  induction n with
  | zero =>
      rw [Work.LerayHirsch.lineSumCore_zero, Work.LerayHirsch.lineSumCore_zero]
      exact ⟨Work.Thom.BundleIso.refl _⟩
  | succ n ih =>
      rw [Work.LerayHirsch.lineSumCore_succ, Work.LerayHirsch.lineSumCore_succ]
      obtain ⟨e₁⟩ := ih (L ∘ Fin.castSucc) (L' ∘ Fin.castSucc) (fun i => h i.castSucc)
      obtain ⟨e₂⟩ := h (Fin.last n)
      obtain ⟨e₃⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_first
        (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc))
        (Work.LerayHirsch.lineSumCore n (L' ∘ Fin.castSucc)) (L' (Fin.last n)) e₁
      obtain ⟨e₄⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
        (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n))
        (L' (Fin.last n)) e₂
      exact ⟨e₄.trans e₃⟩

/-- **Congruence of `Work.Gen.eSym` under a fibrewise isomorphism of the families.**  Both sides
are `Work.Gen.eSymC` of the first Chern classes (`Work.Gen.eSym_eq_eSymC`), and those agree by
isomorphism invariance of the Chern classes. -/
theorem eSym_familyIso {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {n : ℕ}
    (L : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (L' : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι')
    (h : ∀ i, Nonempty (Work.Thom.BundleIso (L i) (L' i))) (k : ℕ) :
    Work.Gen.eSym n L k = Work.Gen.eSym n L' k := by
  rw [Work.Gen.eSym_eq_eSymC, Work.Gen.eSym_eq_eSymC]
  refine Work.Gen.eSymC_congr (fun i => ?_) k
  exact Work.Thom.chernClass_BundleIso (L i) (L' i) (Classical.choice (h i))

/-- **`Work.Cohomology.cupH'` is `ℤ`-linear in its first variable**, in the normalisation of the
`•` notation of `Work.Thom.Coh` (the two scalar multiplications on `Coh` are bridged by
`int_smul_eq_zsmul`, exactly as in `Work.Gen.cupH'_zsmul_right`). -/
theorem cupH'_zsmul_left {P : Type} [TopologicalSpace P] {n m : ℕ} (c : ℤ)
    (x : Work.Thom.Coh ℤ n P) (y : Work.Thom.Coh ℤ m P) :
    Work.Cohomology.cupH' ℤ (ssB P) n m (c • x) y
      = c • (Work.Cohomology.cupH' ℤ (ssB P) n m x y) := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ n P)) c x]
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ (n + m) P)) c
        (Work.Cohomology.cupH' ℤ (ssB P) n m x y)]
  exact Work.Cohomology.cupH'_smul_left ℤ (ssB P) n m c x y

/-- **The left unit law of the cup product, with the degree bookkeeping `0 + d = d` collapsed**:
`cohTransport (0 + d = d) (1 ⌣ x) = x`. -/
theorem cohTransport_cupH'_oneH_left {B : Type} [TopologicalSpace B] {d : ℕ} (h : 0 + d = d)
    (x : Work.Thom.Coh ℤ d B) :
    Work.Thom.cohTransport h
      (Work.Cohomology.cupH' ℤ (ssB B) 0 d (Work.Cohomology.oneH ℤ (ssB B)) x) = x := by
  rw [Work.Cohomology.cupH'_one_left, Work.LerayHirsch.eqRec_eq_cohTransport,
    Work.Whitney.cohTransport_trans]
  exact Work.Thom.cohTransport_self _ x

/-- **The left unit law for an integer multiple of the unit class**:
`cohTransport (0 + d = d) ((k·1) ⌣ x) = k • x`. -/
theorem cohTransport_cupH'_zsmul_oneH_left {B : Type} [TopologicalSpace B] {d : ℕ}
    (h : 0 + d = d) (k : ℤ) (x : Work.Thom.Coh ℤ d B) :
    Work.Thom.cohTransport h
      (Work.Cohomology.cupH' ℤ (ssB B) 0 d (k • Work.Cohomology.oneH ℤ (ssB B)) x)
      = k • x := by
  rw [cupH'_zsmul_left k (Work.Cohomology.oneH ℤ (ssB B)) x,
    Work.Thom.cohTransport_zsmul, cohTransport_cupH'_oneH_left h x]

/-- **The pinning of the constant in the delta form of the crux.**  Under the hypotheses of
`Work.Whitney.cruxPin_of_familyIso` the class `δ` of the delta form of the top Chern class of
`lineSumCore N M` is the unit class of `H⁰(B;ℤ)`. -/
theorem cruxPin_of_familyIso (N : ℕ) (hN : 2 ≤ N)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι ι₀ : Type} [Fintype ι] [Fintype ι₀]
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (M₀ : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)
    (hiso : ∀ i, Nonempty (Work.Thom.BundleIso (M i) (M₀ i)))
    (hM₀ : Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M₀)
        = Work.Gen.eSym N M₀ (N - 1))
    (hfree : ∀ k : ℤ, k • Work.Gen.eSym N M₀ (N - 1) = 0 → k = 0)
    (hspan : ∀ x : Work.Thom.Coh ℤ 0 B, ∃ k : ℤ,
        x = k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
    (δ : Work.Thom.Coh ℤ 0 B)
    (hδ : Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
        = Work.Whitney.deltaCup N M δ) :
    δ = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
  -- the crux for `M`, by isomorphism invariance of the top Chern class
  obtain ⟨eIso⟩ := nonempty_bundleIso_lineSumCore_family N M M₀ hiso
  have hChern : Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M)
      = Work.Gen.eSym N M₀ (N - 1) :=
    (Work.Thom.chernClass_BundleIso (Work.LerayHirsch.lineSumCore N M)
      (Work.LerayHirsch.lineSumCore N M₀) eIso).trans hM₀
  -- `eSym` is fibrewise-isomorphism invariant
  have hEM : Work.Gen.eSym N M (N - 1) = Work.Gen.eSym N M₀ (N - 1) :=
    eSym_familyIso M M₀ hiso (N - 1)
  -- `δ = k·1`, and the delta form evaluated on `k·1`
  obtain ⟨k, hk⟩ := hspan δ
  have hdelta : Work.Whitney.deltaCup N M δ = k • Work.Gen.eSym N M₀ (N - 1) := by
    have h1 : Work.Whitney.deltaCup N M δ = k • Work.Gen.eSym N M (N - 1) := by
      rw [Work.Whitney.deltaCup, hk]
      exact cohTransport_cupH'_zsmul_oneH_left _ k (Work.Gen.eSym N M (N - 1))
    rw [h1, hEM]
  have hkE : k • Work.Gen.eSym N M₀ (N - 1) = Work.Gen.eSym N M₀ (N - 1) :=
    hdelta.symm.trans (hδ.symm.trans hChern)
  -- hence `(k-1) • eSym = 0`, so `k = 1` by freeness
  have hk1 : k = 1 := by
    have hzero : (k - 1) • Work.Gen.eSym N M₀ (N - 1) = 0 := by
      rw [sub_zsmul, hkE, one_zsmul, add_neg_cancel]
    have h' := hfree (k - 1) hzero
    omega
  rw [hk, hk1]
  exact one_smul ℤ (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))

end

end Work.Whitney
