import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.exists_zeroSection_pairing_one
import Submission.Work.ThomBordism.chartModelClass_span_top

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The pairing of the chart model class with the collapse class is `± 1`

This file proves `Work.ThomBordism.chartModelClass_pairing_eq_pm_one`.

## The argument

Let `ν = NormalTotal E`, `A = normalNonzero E = ν ∖ 0`, `n = 8 + k`, `c = collapseRelK8`
(the Pontryagin–Thom collapse class, in `H_{k+8}(ν, A)`), and
`τ := (Nat.add_comm 8 k) ▸ chartModelClass E C x hcont ∈ H^{k+8}(ν, A)`.

* **(1) `τ` is detected by a primitive cohomology class.**  `Work.ThomBordism.localDegreeGenExists`
  supplies a class `U₀ ∈ H^k(ν,A)` which *is a local-degree class*
  (`Work.ThomBordism.IsLocalDegreeClass`) and generates `H^k(ν,A)`, i.e.
  `⟨(Nat.add_comm 8 k) ▸ (x ⌣ U₀), c⟩ = ⟨(zeroSection)^* x, V.c⟩` for every `x ∈ H^8(ν)`
  (`Submission/Work/Tubular/LocalDegreeAll.lean`).  Choosing `w` with
  `⟨(zeroSection)^* w, V.c⟩ = 1` (`Work.ThomBordism.exists_zeroSection_pairing_one`) and applying
  the local-degree identity to `x = w` gives `φ := ⟨β, −⟩` with
  `β := (Nat.add_comm 8 k) ▸ (w ⌣ U₀)` and `φ c = 1`.  In particular the functional
  `φ : H_{k+8}(ν,A) → ℤ` is *primitive* at `c` (it is `1` there).

* **(2) `τ` generates.**  This is the geometric input
  `Work.ThomBordism.chartModelClass_span_top`: the chart model class is the pullback of the
  generator `Work.ThomBordism.stdModelGen (8+k)` of `H^{8+k}(ℝ^{8+k}, {0}ᶜ)` along the map of pairs
  `chartAffine E x ∘ cap E ε`, which is a local homeomorphism of pairs at the zero-section point
  `0_x`; by excision this identifies the *local* cohomology at `0_x` with that at `0`, and
  `stdModelGen` is a generator of that local group.  Hence `τ` generates `H^{k+8}(ν,A)` (whose
  rank-one-ness is the Thom isomorphism).
  (Stated separately, because its proof uses only the tubular chart and the model class — it never
  mentions the collapse map.)

* **(3) The algebra.**  `Work.Tubular.relKronH X A n : H^n(X,A) →ₗ (H_n(X,A) →ₗ ℤ)` is surjective
  (`Work.ThomBordism.relKronH_surjective`, from the degreewise freeness of the relative chains),
  so the functional `ψ := ⟨τ, −⟩` *generates* the dual of `H_n(X,A)`, because `τ` generates
  `H^n(X,A)` and the pairing is `ℤ`-linear.  A generator of the dual module which attains the value
  `1` at `c` is primitive at `c`, and `φ = m • ψ` with `1 = φ c = m · ψ c` forces
  `ψ c = ±1`.
-/

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The capped chart map is a map of pairs on the *local* pair too -/

/-- **The capped chart map is nonzero away from the base zero-section point.**  This is
`Work.ThomBordism.chartAffine_cap_ne_zero` with the hypothesis `p ∈ ν ∖ 0` weakened to
`p ≠ 0_x`: the only point of `ν` mapped to `0` by `chartAffine E x ∘ cap E ε` on a neighbourhood
of the zero section is `0_x` itself.

Indeed, `chartAffine E x (cap E ε p) = 0` forces `tubeMap E (cap E ε p) = E.e x`, hence (the capping
lands in the closed disc bundle, where `tubeMap` is injective with inverse `C.inv`)
`cap E ε p = 0_x`, i.e. `p` lies over `x` with zero normal vector, i.e. `p = 0_x`.

Consequently `chartAffine E x ∘ cap E ε` restricts to a map of pairs
`(ν, ν ∖ {0_x}) → (ℝ^{8+k}, {0}ᶜ)`, i.e. it defines a class on the *local* pair at `0_x`. -/
theorem chartAffine_cap_ne_zero_of_ne_zeroSection
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) {p : Work.Tubular.NormalTotal E}
    (hp : p ≠ Work.Tubular.zeroSectionNormal E x) :
    Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0 := by
  intro h0
  have htube : Work.Tubular.tubeMap E (Work.ThomBordism.cap E ε p) = E.e x := by
    have h := congrArg (fun z : Work.Tubular.Euc (8 + k) => z + E.e x) h0
    rw [Work.ThomBordism.chartAffine_apply] at h
    rw [sub_add_cancel] at h
    simpa [Work.Tubular.tubeMap] using h
  have hzero : Work.Tubular.tubeMap E (Work.Tubular.zeroSectionNormal E x) = E.e x :=
    Work.ThomBordism.tubeMap_zeroSectionNormal E x
  have hle : Work.Tubular.normalNorm E (Work.ThomBordism.cap E ε p) ≤ ε :=
    Work.ThomBordism.cap_mem_disc E C.eps_pos.le p
  have hnorm0 : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
    rw [Work.Tubular.zeroSectionNormal]; simp
  have heq : Work.ThomBordism.cap E ε p = Work.Tubular.zeroSectionNormal E x := by
    have h1 := congrArg C.inv (htube.trans hzero.symm)
    rw [C.inv_tubeMap _ hle, C.inv_tubeMap _ (by rw [hnorm0]; exact C.eps_pos.le)] at h1
    exact h1
  have hproj : (p : V.pt × Work.Tubular.Euc (8 + k)).1 = x := by
    have h := congrArg (fun q : Work.Tubular.NormalTotal E =>
      (q : V.pt × Work.Tubular.Euc (8 + k)).1) heq
    unfold Work.ThomBordism.cap at h
    rw [Work.ThomBordism.radialRescale_proj] at h
    simpa using h
  have hvec : (p : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
    have h := congrArg (fun q : Work.Tubular.NormalTotal E =>
      (q : V.pt × Work.Tubular.Euc (8 + k)).2) heq
    unfold Work.ThomBordism.cap at h
    rw [Work.ThomBordism.radialRescale_coe] at h
    have hzero' : (Work.Tubular.zeroSectionNormal E x :
        V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
      rw [Work.Tubular.zeroSectionNormal_apply]
    rw [hzero'] at h
    have hpos : 0 < Work.ThomBordism.capCoeff ε (Work.Tubular.normalNorm E p) :=
      Work.ThomBordism.capCoeff_pos C.eps_pos _ (Work.Tubular.normalNorm_nonneg E p)
    exact (smul_eq_zero.mp h).resolve_left (ne_of_gt hpos)
  refine hp (Subtype.ext ?_)
  rw [Work.Tubular.zeroSectionNormal_apply]
  exact Prod.ext hproj hvec

/-! ## The algebraic core: a generating class whose dual functional is primitive at `c` -/

/-- **A generator pairs to a unit with a primitive class.**  Let `τ ∈ H^n(X,A)` generate
(`Submodule.span ℤ {τ} = ⊤`) and let `φ : H_n(X,A) →ₗ[ℤ] ℤ` satisfy `φ c = 1`.  Then the relative
Kronecker pairing of `τ` with `c` is `±1`.

Proof.  `relKronH X A n` is surjective (`Work.ThomBordism.relKronH_surjective`, which needs only
that the relative chains are degreewise free, `Work.Cohomology.relChains_free`), so the image of
`span{τ} = ⊤` under it is `⊤`; i.e. `ψ := ⟨τ, −⟩` generates the `ℤ`-dual of `H_n(X,A)`.  Hence
`φ = m • ψ` for some `m ∈ ℤ`, and `1 = φ c = m · ψ c` in `ℤ` forces `ψ c = ±1`. -/
theorem relKronH_pm_one_of_span_top_of_primitive {X : TopCat} {A : Set X} {n : ℕ}
    (τ : Work.Thom.RelCoh ℤ n X A)
    (hτ : Submodule.span ℤ ({τ} : Set (Work.Thom.RelCoh ℤ n X A)) = ⊤)
    (c : ↥((Work.Cohomology.relChains X A).homology n))
    (φ : ↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ) (hφ : φ c = 1) :
    Work.Tubular.relKronH X A n τ c = 1 ∨ Work.Tubular.relKronH X A n τ c = -1 := by
  have hsurj : Function.Surjective (Work.Tubular.relKronH X A n) :=
    Work.ThomBordism.relKronH_surjective X A n
      (fun m => Work.Cohomology.relChains_free X A m)
  -- the functional `ψ = ⟨τ,−⟩` generates the dual
  have hspanψ : Submodule.span ℤ
      ({Work.Tubular.relKronH X A n τ} :
        Set (↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ)) = ⊤ := by
    have hmap : Submodule.span ℤ
        ({Work.Tubular.relKronH X A n τ} :
          Set (↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ))
        = (Work.Tubular.relKronH X A n).range := by
      rw [← Set.image_singleton, ← Submodule.map_span, hτ, Submodule.map_top]
    rw [hmap, LinearMap.range_eq_top.mpr hsurj]
  -- hence `φ` is a multiple of `ψ`
  have hmem : φ ∈ Submodule.span ℤ ({Work.Tubular.relKronH X A n τ} :
      Set (↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ)) := by
    rw [hspanψ]; exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hmem
  -- evaluate at `c`
  have h1 : m * (Work.Tubular.relKronH X A n τ c) = 1 := by
    have h := congrArg (fun (g : ↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ) => g c) hm
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [hφ] at h
    exact h.symm.symm
  have hunit : IsUnit (Work.Tubular.relKronH X A n τ c) :=
    isUnit_iff_exists_inv.mpr ⟨m, by rw [mul_comm]; exact h1⟩
  rcases Int.isUnit_iff.mp hunit with h | h
  · exact Or.inl h
  · exact Or.inr h


/-! ## The target -/


theorem chartModelClass_pairing_eq_pm_one {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε) (hU : IsCompact C.U)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x hcont)
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = 1 ∨
      Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x hcont)
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = -1 := by
  classical
  -- a generating local-degree class `U₀`
  obtain ⟨U₀, hU₀span, hU₀ld⟩ :=
    Work.ThomBordism.localDegreeGenExists (V := V) (k := k) hk E C.eps_pos C q hU hR hbox g hg hg2
  -- a class `w` whose zero-section pullback pairs to `1` with the fundamental class
  obtain ⟨w, hw⟩ := Work.ThomBordism.exists_zeroSection_pairing_one (V := V) k E
  -- the primitive functional `φ = ⟨(Nat.add_comm 8 k) ▸ (w ⌣ U₀), −⟩`
  refine relKronH_pm_one_of_span_top_of_primitive
    ((Nat.add_comm 8 k) ▸ Work.ThomBordism.chartModelClass E C x hcont)
    (Work.Tubular.span_cast_singleton_eq_top
      (M := fun nn => Work.Thom.RelCoh ℤ nn (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E))
      (Nat.add_comm 8 k) (chartModelClass_span_top hk E C x hcont))
    (Work.Tubular.collapseRelK8 C g hg hR hbox)
    (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (k + 8)
      ((Nat.add_comm 8 k) ▸
        (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) 8 k w U₀)))
    (by rw [hU₀ld w, hw])

end

end Work.ThomBordism
