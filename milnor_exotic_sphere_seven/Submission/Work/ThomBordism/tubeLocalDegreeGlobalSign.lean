import Mathlib
import Submission.Work.Tubular.LocalStep
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Tubular.tubeCollapseClass_span_top
import Submission.Work.Tubular.thomClass_span_top
import Submission.Work.Tubular.Unimodular
import Submission.Work.ThomBordism.openThomTopIso
import Submission.Work.ThomBordism.thomPairTopHomologyIsoV2
import Submission.Work.ThomBordism.totalSpaceHomologyEightIso
import Submission.Work.ThomBordism.zeroSectionFundClassSpan
import Submission.Work.ThomBordism.relKronH_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local degree of the Thom class, up to a global sign (the abstract normal bundle)

This file proves `Work.ThomBordism.tubeLocalDegreeGlobalSign`: for a rank-`k` real bundle
`Z` over a path-connected closed oriented smooth `8`-manifold `V` carrying an integral Thom class
(`Work.Thom.ThomClass`), the local degree identity

  `⟨x ⌣ U, c⟩ = s · ⟨x, z^*[V]⟩`  for all `x ∈ H⁸(Z.TotalSpace)`,

holds with `s = ±1`, `U` a generator of `H^k(Z.TotalSpace, Z.TotalSpace∖0)` and `c` a generator of
`H_{k+8}(Z.TotalSpace, Z.TotalSpace∖0)`.

The classical content is the **local degree up to sign**: the Thom class is Poincaré dual to the
zero section.  Write `X = Z.TotalSpace`, `A = X∖0`, `N = k+8`.

## The reduction

1. **`exists_relCapPair_surjective`** (proved in this file): there is `c ∈ H_N(X,A)` for which the
   partially applied cap product `u ↦ u ⌢ c : H^k(X,A) → H₈(X)` is *surjective*.  This is the only
   place where geometry enters, and only through
   * `Work.ThomBordism.thomPairTopHomologyIsoV2`: `H_N(X,A) ≅ ℤ` (the top relative homology of the
     Thom pair — the Thom isomorphism in the top degree), and
   * `Work.ThomBordism.relKronH_surjective`: the *surjectivity half of the universal coefficient
     theorem* for the pair, `H^N(X,A) ↠ Hom(H_N(X,A),ℤ)` (with the degreewise freeness of the
     relative chains `Work.Cohomology.relChains_free`), which is what upgrades `H_N ≅ ℤ` to the
     *unimodularity* of the pairing.
   Everything else is the Thom isomorphism (`T.isThom 8`), the mixed cap/cup adjunction
   `Work.Cohomology.kronH_mixedCup_relKronH`, and `Work.ThomBordism.totalSpaceHomologyEightIso`
   (`H₈(X) ≅ ℤ`, so a functional which is `1` on one nonzero class is injective).
2. **The `ℤ`-linear algebra** `exists_generators_of_surjective` then produces a pair `(U, c)` of
   *generators* whose cap product is a generator of `H₈(X)`; comparing with the generator `z_*[V]`
   (`Work.ThomBordism.zeroSectionFundClassSpan`) gives `U ⌢ c = ± z_*[V]`, and
   `Work.Cohomology.kronH_natural` converts the identity into the statement of the target.  The
   cyclicity facts `H^k ≅ ℤ`, `H_{k+8} ≅ ℤ` are `openThomTopIso` and `thomPairTopHomologyIsoV2`.

Thus the *sign* `s` is not determined here (the constructions are sign-free), which is exactly the
`∃ s, s = 1 ∨ s = -1` in the statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-- The cast-cancellation `h ▸ (h.symm ▸ x) = x`. -/
private lemma cast_symm_cast {A : Sort*} {P : A → Sort*} {a b : A} (h : a = b) (x : P b) :
    h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

/-- A class of a module isomorphic to `ℤ` is the multiple of its value at the generator given by
the isomorphism. -/
private lemma eq_mul_of_eval_symm_one {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (θ : M →ₗ[ℤ] ℤ) (x : M) :
    θ x = (e x) * (θ (e.symm 1)) := by
  have hy : (e x) • e.symm 1 = x := e.injective (by simp [map_smul])
  rw [← hy]
  simp [map_smul]

/-! ## The local degree up to sign

The whole geometric content of the local degree is isolated as the statement that the top relative
homology of the Thom pair is `ℤ` (`Work.ThomBordism.thomPairTopHomologyIso`).  Everything else is
universal coefficients: the relative Kronecker pairing `relKronH : H^{k+8}(X,A) → Hom(H_{k+8}(X,A),ℤ)`
is *surjective* (`Work.ThomBordism.relKronH_surjective`, from `relChains_free` and `uctPsi_surj`), so
some class `α ∈ H^{k+8}(X,A)` pairs to `1` with a generator `c₀` of `H_{k+8}(X,A) ≅ ℤ`; the Thom
isomorphism realises `α = π^*x ⌣ τ`, and the mixed cap/cup adjunction turns the statement into
`⟨x, τ ⌢ c₀⟩ = 1`.  Since `H₈(X) ≅ ℤ` (`totalSpaceHomologyEightIso`) the functional `⟨x,·⟩` is
injective, and every class of `H₈(X)` is a multiple of `τ ⌢ c₀`. -/

theorem exists_relCapPair_surjective {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type} {hk : 1 ≤ k}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt]
    (hZ : Nonempty (Work.Thom.ThomClass Z k)) :
    ∃ c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8),
      Function.Surjective (fun u : Work.Thom.OpenThom Z k =>
        relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 u c) := by
  classical
  obtain ⟨eB⟩ := totalSpaceHomologyEightIso Z
  obtain ⟨eC⟩ := thomPairTopHomologyIsoV2 (hk := hk) Z hZ
  obtain ⟨T⟩ := hZ
  let eCL : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)
      ≃ₗ[ℤ] ℤ := eC.toLinearEquiv
  let eBL : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8 ≃ₗ[ℤ] ℤ := eB.toLinearEquiv
  -- **(i)** the relative Kronecker pairing is surjective (universal coefficients for the pair,
  -- using that the relative chains are degreewise free).
  have hsurj : Function.Surjective (Work.Tubular.relKronH (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (k + 8)) :=
    Work.ThomBordism.relKronH_surjective (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
      (fun m => Work.Cohomology.relChains_free (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) m)
  obtain ⟨α, hα⟩ := hsurj (eCL : _ →ₗ[ℤ] ℤ)
  have hαc0 : Work.Tubular.relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (k + 8) α (eCL.symm 1) = 1 := by
    have h := LinearMap.congr_fun hα (eCL.symm 1)
    rw [h]
    exact eCL.apply_symm_apply 1
  -- **(ii)** the Thom isomorphism produces `α` as the mixed product of the Thom class with a
  -- degree-`8` class of the total space.
  have hcomm : 8 + k = k + 8 := Nat.add_comm 8 k
  obtain ⟨x, hx⟩ := (T.isThom 8).2 (hcomm.symm ▸ α)
  let x' : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace) :=
    (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ 8).hom x
  have hmixed : mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) 8 k x' T.τ
      = hcomm.symm ▸ α := hx
  have hcast : hcomm ▸ (mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) 8 k
      x' T.τ) = α := by
    rw [hmixed]
    exact cast_symm_cast (P := fun n => ↑(relCohomology ℤ (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) n)) hcomm α
  -- **(iii)** the mixed cap/cup adjunction turns the pairing into a single integer.
  have hw : kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8 x'
      (relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 T.τ
        (eCL.symm 1)) = 1 := by
    have hadj := Work.Tubular.kronH_mixedCup_relKronH (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) k 8 hk (by norm_num) (⟨4 * k, by ring⟩ : Even (k * 8))
      x' T.τ (eCL.symm 1)
    rw [hadj, hcast, hαc0]
  let w : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8 :=
    relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 T.τ (eCL.symm 1)
  let θ : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8 →ₗ[ℤ] ℤ :=
    kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8 x'
  let s : ℤ := θ (eBL.symm 1)
  have hwθ : θ w = 1 := hw
  have hgen : ∀ y : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8,
      θ y = (eBL y) * s := fun y => eq_mul_of_eval_symm_one eBL θ y
  have hs_ne : s ≠ 0 := by
    intro h0
    have h1 : (eBL w) * s = 1 := by
      rw [← hgen w]
      exact hwθ
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  -- **(iv)** surjectivity
  refine ⟨eCL.symm 1, ?_⟩
  intro d
  refine ⟨(θ d) • T.τ, ?_⟩
  have hstep : relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8
      ((θ d) • T.τ) (eCL.symm 1) = (θ d) • w := by
    rw [map_zsmul]
    rfl
  have key : (θ d) • w = d := by
    apply eBL.injective
    have h1 : eBL ((θ d) • w) = (θ d) * (eBL w) := by
      rw [map_zsmul]
      simp
    have hws : (eBL w) * s = 1 := by
      rw [← hgen w]
      exact hwθ
    rw [h1, hgen d, mul_assoc, mul_comm s (eBL w), hws, mul_one]
  have hfin : relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8
      ((θ d) • T.τ) (eCL.symm 1) = d := by
    rw [hstep]
    exact key
  exact hfin

/-! ## Elementary `ℤ`-linear algebra -/

/-- Evaluation at `c`, as an additive homomorphism of the additive group of linear maps.  (Only
additivity is used, so that `AddMonoidHom.map_zsmul` applies without meeting the two competing
`ℤ`-scalar multiplications on a `ℤ`-module.) -/
def evalLinHom {C B : Type*} [AddCommGroup C] [Module ℤ C] [AddCommGroup B] [Module ℤ B]
    (c : C) : (C →ₗ[ℤ] B) →+ B where
  toFun f := f c
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical generator `e.symm 1` of a `ℤ`-module isomorphic to `ℤ` spans everything. -/
lemma span_symm_one {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ) :
    Submodule.span ℤ ({e.symm 1} : Set M) = ⊤ := by
  have htop : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rw [Submodule.mem_span_singleton]
    exact ⟨y, by rw [smul_eq_mul, mul_one]⟩
  have hmap : Submodule.map (e.symm : ℤ →ₗ[ℤ] M) (⊤ : Submodule ℤ ℤ)
      = Submodule.span ℤ ({e.symm 1} : Set M) := by
    rw [← htop, Submodule.map_span, Set.image_singleton]
    rfl
  rw [← hmap, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.symm.surjective

/-- `span {-y} = span {y}`. -/
lemma span_neg_eq {M : Type*} [AddCommGroup M] [Module ℤ M] (y : M) :
    Submodule.span ℤ ({-y} : Set M) = Submodule.span ℤ ({y} : Set M) := by
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
    have h : -y ∈ Submodule.span ℤ ({-y} : Set M) :=
      Submodule.subset_span (Set.mem_singleton (-y))
    simpa using Submodule.neg_mem (Submodule.span ℤ ({-y} : Set M)) h

/-- Scaling a generator by a unit gives a generator. -/
lemma span_zsmul_eq_top_of_eq_pm_one {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x y : M) (h : x = y ∨ x = -y) (hy : Submodule.span ℤ {y} = ⊤) :
    Submodule.span ℤ {x} = ⊤ := by
  rcases h with rfl | rfl
  · exact hy
  · rw [span_neg_eq]
    exact hy

/-- **The main linear-algebra step.**  Let `P : A →ₗ[ℤ] (C →ₗ[ℤ] B)` be a `ℤ`-bilinear pairing with
`A ≅ C ≅ B ≅ ℤ`, and suppose the partially applied pairing `u ↦ P u c` is surjective for some
`c ∈ C`.  Then there are generators `u` of `A` and `c` of `C` whose pairing `P u c` is a generator
of `B`. -/
theorem exists_generators_of_surjective {A C B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup C] [Module ℤ C] [AddCommGroup B] [Module ℤ B]
    (P : A →ₗ[ℤ] (C →ₗ[ℤ] B)) (eA : A ≃ₗ[ℤ] ℤ) (eC : C ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ)
    (h : ∃ c : C, Function.Surjective (fun u : A => P u c)) :
    ∃ u c, Submodule.span ℤ {u} = ⊤ ∧ Submodule.span ℤ {c} = ⊤ ∧
      Submodule.span ℤ {P u c} = ⊤ := by
  obtain ⟨c, hc⟩ := h
  -- Step 1: `eB (P (eA.symm 1) c) = ±1`.
  have hB : eB (P (eA.symm 1) c) = 1 ∨ eB (P (eA.symm 1) c) = -1 := by
    set eta : A →+ ℤ := eB.toAddMonoidHom.comp ((evalLinHom c).comp P.toAddMonoidHom) with heta
    have heta_surj : Function.Surjective eta := by
      intro y
      obtain ⟨a, ha⟩ := eB.surjective y
      obtain ⟨u, hu⟩ := hc a
      exact ⟨u, by show eB (P u c) = y; rw [show P u c = a from hu, ha]⟩
    set psi : ℤ →+ ℤ := eta.comp eA.symm.toAddMonoidHom with hpsi
    have hpsi_surj : Function.Surjective psi := by
      intro y
      obtain ⟨a, ha⟩ := heta_surj y
      exact ⟨eA a, by
        rw [show psi (eA a) = eta (eA.symm (eA a)) from rfl, eA.symm_apply_apply, ha]⟩
    obtain ⟨t, ht⟩ := hpsi_surj 1
    have hpsi_one : psi 1 = eB (P (eA.symm 1) c) := rfl
    have hkey : psi t = t • psi 1 := by
      have h := AddMonoidHom.map_zsmul psi t (1 : ℤ)
      simpa using h
    have hpsi1 : IsUnit (psi 1) := by
      refine isUnit_iff_exists_inv.mpr ⟨t, ?_⟩
      have h : t • psi 1 = 1 := by rw [← hkey]; exact ht
      have h2 : t * psi 1 = 1 := by simpa [zsmul_eq_mul] using h
      rw [mul_comm]
      exact h2
    have h : psi 1 = 1 ∨ psi 1 = -1 := by
      rwa [Int.isUnit_iff] at hpsi1
    rwa [hpsi_one] at h
  -- Step 2: `P (eA.symm 1) c` is a generator of `B`.
  have hspanP : Submodule.span ℤ ({P (eA.symm 1) c} : Set B) = ⊤ := by
    refine span_zsmul_eq_top_of_eq_pm_one _ (eB.symm 1) ?_ (span_symm_one eB)
    rcases hB with h1 | h1
    · left
      have h2 : eB.symm (eB (P (eA.symm 1) c)) = eB.symm 1 := by rw [h1]
      rwa [eB.symm_apply_apply] at h2
    · right
      have h2 : eB.symm (eB (P (eA.symm 1) c)) = eB.symm (-1) := by rw [h1]
      rw [eB.symm_apply_apply, map_neg] at h2
      exact h2
  -- Step 3: the witness `c` is a generator, using that `P` is `ℤ`-linear in its second variable.
  set chi : C →+ ℤ := eB.toAddMonoidHom.comp (P (eA.symm 1)).toAddMonoidHom with hchi
  have hchi_c : chi c = eB (P (eA.symm 1) c) := rfl
  have hchi_one : chi (eC.symm 1) = eB (P (eA.symm 1) (eC.symm 1)) := rfl
  have hc_eq : c = (eC c) • (eC.symm 1) := by
    rw [← map_zsmul, smul_eq_mul, mul_one, eC.symm_apply_apply]
  have hchi' : chi c = (eC c) • chi (eC.symm 1) := by
    conv_lhs => rw [hc_eq]
    exact AddMonoidHom.map_zsmul chi (eC c) (eC.symm 1)
  have hval : (eC c) * (eB (P (eA.symm 1) (eC.symm 1))) = eB (P (eA.symm 1) c) := by
    rw [← hchi_one, ← hchi_c, ← smul_eq_mul]
    exact hchi'.symm
  have hCc : eC c = 1 ∨ eC c = -1 := by
    rcases hB with h1 | h1
    · exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [hval, h1])
    · have h2 : (eC c) * (eB (P (eA.symm 1) (eC.symm 1))) = -1 := by rw [hval, h1]
      have h3 : (eC c) * (-(eB (P (eA.symm 1) (eC.symm 1)))) = 1 := by
        rw [mul_neg, h2]; ring
      exact Int.eq_one_or_neg_one_of_mul_eq_one h3
  refine ⟨eA.symm 1, c, span_symm_one eA, ?_, hspanP⟩
  refine span_zsmul_eq_top_of_eq_pm_one c (eC.symm 1) ?_ (span_symm_one eC)
  rcases hCc with h1 | h1
  · left
    have h2 : eC.symm (eC c) = eC.symm 1 := by rw [h1]
    rwa [eC.symm_apply_apply] at h2
  · right
    have h2 : eC.symm (eC c) = eC.symm (-1) := by rw [h1]
    rw [eC.symm_apply_apply, map_neg] at h2
    exact h2

/-- **A generator of a module isomorphic to `ℤ` maps to `±1`.** -/
lemma map_eq_pm_one_of_span_eq_top {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) {z : M} (hz : Submodule.span ℤ ({z} : Set M) = ⊤) :
    e z = 1 ∨ e z = -1 := by
  have hspan : Submodule.span ℤ ({e z} : Set ℤ) = ⊤ := by
    have hmap : Submodule.map (e : M →ₗ[ℤ] ℤ) (Submodule.span ℤ ({z} : Set M))
        = Submodule.span ℤ ({e z} : Set ℤ) := by
      rw [Submodule.map_span, Set.image_singleton]
      ext w
      simp
    rw [← hmap, hz, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ ({e z} : Set ℤ) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp h1
  have hunit : IsUnit (e z) := by
    refine isUnit_iff_exists_inv.mpr ⟨m, ?_⟩
    rw [mul_comm]
    simpa [zsmul_eq_mul] using hm
  rwa [Int.isUnit_iff] at hunit

/-- **Two generators of a module isomorphic to `ℤ` are `±` each other.** -/
lemma eq_pm_of_span_eq_top_of_iso {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ)
    {x y : M} (hx : Submodule.span ℤ ({x} : Set M) = ⊤) (hy : Submodule.span ℤ ({y} : Set M) = ⊤) :
    x = y ∨ x = -y := by
  have hx1 := map_eq_pm_one_of_span_eq_top e hx
  have hy1 := map_eq_pm_one_of_span_eq_top e hy
  have hneg : e (-y) = - e y := map_neg (f := (e : M →ₗ[ℤ] ℤ)) y
  rcases hx1 with hx1 | hx1 <;> rcases hy1 with hy1 | hy1
  · left
    exact e.injective (by rw [hx1, hy1])
  · right
    have h : e x = - e y := by rw [hx1, hy1]; norm_num
    rw [← hneg] at h
    exact e.injective h
  · right
    have h : e x = - e y := by rw [hx1, hy1]
    rw [← hneg] at h
    exact e.injective h
  · left
    exact e.injective (by rw [hx1, hy1])

/-! ## The target -/

theorem tubeLocalDegreeGlobalSign {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type} {hk : 1 ≤ k}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt]
    (hZ : Nonempty (Work.Thom.ThomClass Z k)) :
    ∃ (U : Work.Thom.OpenThom Z k)
      (c : (Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z)).homology (k + 8))
      (s : ℤ),
      (s = 1 ∨ s = -1) ∧
      Submodule.span ℤ ({U} : Set _) = ⊤ ∧
      Submodule.span ℤ ({c} : Set _) = ⊤ ∧
      (∀ x : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace),
        Work.Tubular.relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
            ((Nat.add_comm 8 k) ▸
              (Work.Cohomology.mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
                8 k x U)) c
          = s * Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
              ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x) V.c) := by
  classical
  obtain ⟨eA⟩ := openThomTopIso (hk := hk) Z hZ
  obtain ⟨eC⟩ := thomPairTopHomologyIsoV2 (hk := hk) Z hZ
  obtain ⟨eB⟩ := totalSpaceHomologyEightIso Z
  let EA : Work.Thom.OpenThom Z k ≃ₗ[ℤ] ℤ := eA.toLinearEquiv
  let EC : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8) ≃ₗ[ℤ] ℤ :=
    eC.toLinearEquiv
  let EB : (Work.Cohomology.singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8 ≃ₗ[ℤ] ℤ :=
    eB.toLinearEquiv
  obtain ⟨c₀, hc₀⟩ := exists_relCapPair_surjective (hk := hk) Z hZ
  obtain ⟨U, c, hU, hc, hUc⟩ := exists_generators_of_surjective
    (relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8) EA EC EB ⟨c₀, hc₀⟩
  have hz : Submodule.span ℤ ({((HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
        (Work.Tubular.zeroSectionTop Z)) 8) V.c)} : Set _) = ⊤ := zeroSectionFundClassSpan Z
  have hpm := eq_pm_of_span_eq_top_of_iso EB hUc hz
  have hnat := kronH_natural (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
    (Work.Tubular.zeroSectionTop Z) 8
  rcases hpm with h | h
  · refine ⟨U, c, 1, Or.inl rfl, hU, hc, ?_⟩
    intro x
    have hpq : Even (k * 8) := ⟨4 * k, by ring⟩
    rw [← Work.Tubular.kronH_mixedCup_relKronH (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) k 8 hk (by norm_num) hpq x U c, h, hnat x V.c]
    simp only [Work.Tubular.zeroSectionTop, one_mul]
  · refine ⟨U, c, -1, Or.inr rfl, hU, hc, ?_⟩
    intro x
    have hpq : Even (k * 8) := ⟨4 * k, by ring⟩
    rw [← Work.Tubular.kronH_mixedCup_relKronH (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) k 8 hk (by norm_num) hpq x U c, h]
    have hmneg : ((kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8) x)
        (- ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of V.pt)
            (TopCat.of Z.TotalSpace) (Work.Tubular.zeroSectionTop Z)) 8) V.c))
        = - (((kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8) x)
            ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of V.pt)
              (TopCat.of Z.TotalSpace) (Work.Tubular.zeroSectionTop Z)) 8) V.c)) :=
      map_neg (((kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8) x).toAddMonoidHom)
        (((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of V.pt)
          (TopCat.of Z.TotalSpace) (Work.Tubular.zeroSectionTop Z)) 8) V.c))
    rw [hmneg, hnat x V.c]
    simp only [Work.Tubular.zeroSectionTop]
    ring

end

end Work.ThomBordism
