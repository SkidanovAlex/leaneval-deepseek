import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Milnor.homology_capped_compact
import Submission.Work.Milnor.capped_kronH_isIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Kronecker pairings of generators of the capped manifold `X = D(ξ) ∪_F D⁸`

Let `X = cappedSpace (cappedDatum F hF)` be the closed `8`-manifold obtained by gluing the disc
bundle `ξ = Vk (-2)` to a disc along a capping diffeomorphism `F : Mk (-2) ≃ S⁷`.  Its integral
(co)homology is `ℤ` in degrees `0`, `4`, `8` and `0` otherwise
(`Work.Milnor.cohomology_capped_datum`, `Work.Milnor.homology_capped_datum`), and the Kronecker
pairing `Hⁿ(X) → Hom(Hₙ(X), ℤ)` is an isomorphism (`Work.Milnor.capped_kronH_isIso`).

This file proves `Work.Milnor.capped_generator_pairings`: if `u ∈ H⁴(X)`, `v ∈ H₄(X)`,
`w ∈ H⁸(X)`, `z ∈ H₈(X)` are *generators* (i.e. their spans are everything — automatic since the
groups are `ℤ`), then

`⟨u, v⟩ = ±1`  and  `⟨w, z⟩ = ±1`.

This is the input that fixes the normalisation of the fundamental class in degree `8`: it says
that a pair of generators is a *unimodular* pair of the perfect pairing, so that the choice of
orientation is the only freedom.

The mathematical content is the following elementary linear algebra over `ℤ`.

* If `L : A →ₗ[ℤ] (B →ₗ[ℤ] ℤ)` is surjective and `u` generates `A`, then `L u` generates
  `Hom(B, ℤ)` (the image of `span {u} = ⊤` under a surjective map is `⊤`).
* If `B ≅ ℤ` (here: `H₄(X) ≅ ℤ` and `H₈(X) ≅ ℤ`) and `v` generates `B`, there is `f : B →ₗ[ℤ] ℤ`
  with `f v = 1`; hence `f = m • (L u)` and `1 = f v = m · ⟨L u, v⟩`, so `⟨L u, v⟩ = ±1`.
-/

namespace Work.Milnor

open CategoryTheory

noncomputable section

/-! ## Elementary linear algebra over `ℤ`

We first prove the abstract statement: for a surjective `ℤ`-linear map `L : A →ₗ (B →ₗ ℤ)` and
generators `u` of `A`, `v` of `B` (with `B ≅ ℤ`) one has `(L u) v = ±1`. -/

/-- If `v` generates a `ℤ`-module `B` isomorphic to `ℤ`, then there is a linear functional `f` on
`B` with `f v = 1`: take the given isomorphism (or its negative), normalised so that `v ↦ 1`. -/
lemma cgp_dual_eq_one_of_span_top {B : Type*} [AddCommGroup B] [Module ℤ B]
    (e : B ≃ₗ[ℤ] ℤ) (v : B) (hv : Submodule.span ℤ {v} = ⊤) :
    ∃ f : B →ₗ[ℤ] ℤ, f v = 1 := by
  -- `e v` generates `ℤ`, so `e v = ±1`
  have hspan : Submodule.span ℤ {(e : B →ₗ[ℤ] ℤ) v} = ⊤ := by
    have h1 : Submodule.map (e : B →ₗ[ℤ] ℤ) (Submodule.span ℤ {v})
        = Submodule.span ℤ {(e : B →ₗ[ℤ] ℤ) v} := by
      rw [Submodule.map_span]; simp
    rw [← h1, hv, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  have hmem : (1 : ℤ) ∈ Submodule.span ℤ {(e : B →ₗ[ℤ] ℤ) v} := by rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨m, hm⟩ := hmem
  have h2 : m * ((e : B →ₗ[ℤ] ℤ) v) = 1 := by simpa [smul_eq_mul] using hm
  have h3 : (e : B →ₗ[ℤ] ℤ) v = 1 ∨ (e : B →ₗ[ℤ] ℤ) v = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h2)
  rcases h3 with h | h
  · exact ⟨(e : B →ₗ[ℤ] ℤ), h⟩
  · exact ⟨-(e : B →ₗ[ℤ] ℤ), by rw [LinearMap.neg_apply, h]; norm_num⟩

/-- **The main linear-algebra step.**  If `L : A →ₗ[ℤ] (B →ₗ[ℤ] ℤ)` is surjective, `u` generates
`A` and `f ∈ Hom(B, ℤ)` takes the value `1` at `v`, then `(L u) v = ±1`. -/
lemma cgp_eval_eq_pm_one_of_generator {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (L : A →ₗ[ℤ] (B →ₗ[ℤ] ℤ))
    (hL : Function.Surjective L) (u : A) (hu : Submodule.span ℤ {u} = ⊤)
    (v : B) (f : B →ₗ[ℤ] ℤ) (hf : f v = 1) :
    (L u) v = 1 ∨ (L u) v = -1 := by
  -- `L u` generates `Hom(B, ℤ)` because `L` is surjective and `u` generates `A`
  have hspan : Submodule.span ℤ {L u} = ⊤ := by
    have h1 : Submodule.map L (Submodule.span ℤ {u}) = Submodule.span ℤ {L u} := by
      rw [Submodule.map_span]; simp
    rw [← h1, hu, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hL
  -- so `f = m • (L u)`, and evaluating at `v` gives `m * ((L u) v) = 1`
  have hmem : f ∈ Submodule.span ℤ {L u} := by rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hval : (L u) v * m = 1 := by
    have h := congrArg (fun g : B →ₗ[ℤ] ℤ => g v) hm
    rw [LinearMap.smul_apply] at h
    simp only [smul_eq_mul, hf] at h
    rw [mul_comm]; exact h
  exact Int.eq_one_or_neg_one_of_mul_eq_one hval

/-- The combination of the two steps above: a surjective Kronecker-type pairing sends a pair of
generators (`B ≅ ℤ`) to `±1`. -/
lemma cgp_kronH_eval_generator {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (L : A →ₗ[ℤ] (B →ₗ[ℤ] ℤ))
    (hL : Function.Surjective L) (u : A) (hu : Submodule.span ℤ {u} = ⊤)
    (e : B ≃ₗ[ℤ] ℤ) (v : B) (hv : Submodule.span ℤ {v} = ⊤) :
    (L u) v = 1 ∨ (L u) v = -1 := by
  obtain ⟨f, hf⟩ := cgp_dual_eq_one_of_span_top e v hv
  exact cgp_eval_eq_pm_one_of_generator L hL u hu v f hf

/-! ## The homology of `X` in degrees `4` and `8` is `ℤ`

`Work.Milnor.homology_capped_datum` computes `Hₙ(X) ≅ ℤ` for `n ∈ {0,4,8}`; we spell out the
`ℤ`-linear equivalence `Hₙ(X) ≃ₗ[ℤ] ℤ` in those degrees, which is what the linear algebra above
needs. -/

/-- In a degree `n` with `Hₙ(X) ≅ ℤ`, the `ℤ`-module `Hₙ(X)` is linearly isomorphic to `ℤ`. -/
lemma cgp_homology_linEquiv_one (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) {n : ℕ}
    (hn : (((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) +
      (if n = 8 then 1 else 0)) = 1) :
    Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology n) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := Work.Milnor.homology_capped_datum F hF n
  rw [hn] at e
  exact ⟨(Work.Cohomology.redH0_linEquivOfIso e).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)⟩

/-! ## The pairings of generators -/

theorem capped_generator_pairings (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F)
    (u : ↥((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology 4))
    (v : ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology 4))
    (w : ↥((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology 8))
    (z : ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))).homology 8))
    (hu : Submodule.span ℤ {u} = ⊤) (hv : Submodule.span ℤ {v} = ⊤)
    (hw : Submodule.span ℤ {w} = ⊤) (hz : Submodule.span ℤ {z} = ⊤) :
    (Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))) 4
        u v = 1 ∨
      Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))) 4
        u v = -1) ∧
    (Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))) 8
        w z = 1 ∨
      Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))) 8
        w z = -1) := by
  constructor
  · -- degree `4`: `H⁴(X) ≅ ℤ ≅ H₄(X)` and the Kronecker pairing is an isomorphism
    obtain ⟨e⟩ := cgp_homology_linEquiv_one F hF (n := 4) (by norm_num)
    exact cgp_kronH_eval_generator _
      (Work.Milnor.capped_kronH_isIso F hF 4).2 u hu e v hv
  · -- degree `8`
    obtain ⟨e⟩ := cgp_homology_linEquiv_one F hF (n := 8) (by norm_num)
    exact cgp_kronH_eval_generator _
      (Work.Milnor.capped_kronH_isIso F hF 8).2 w hw e z hz

end

end Work.Milnor
