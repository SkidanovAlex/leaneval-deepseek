import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.MotK.TwRuling.KleinNondeg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwRuling.sdRankQuad12`

The quadratic form `p κ₁² + q κ₀κ₂ ∈ K̄(E)` is nonzero as soon as `(p, q) ≠ 0`.

This is a rank statement for the two quadratic monomials `κ₁κ₁` and `κ₀κ₂` of `L(10·O)`:
it says that these two products are linearly independent modulo the space of quadratic relations
among the Klein coordinates, i.e. modulo the five Klein Pfaffians.

The proof is the same linear-algebra argument as `Work.MotK.TwRuling.KleinNondeg` (which handles
`2aκ₀² − bκ₁κ₄`):

* `kPhi : (Fin 15 → L) →ₗ[L] L(E)` sends a symmetric coefficient vector `c` to
  `∑_{i ≤ j} c_{ij} κ_i κ_j`; its range is the quadratic span of the Klein coordinates;
* the ten monomials of `L(10·O)` are `L`-independent and lie in the range, so `finrank range ≥ 10`;
* the five Pfaffian quadrics `kleinP a b κ` give five independent relations, so
  `finrank ker ≥ 5`; rank--nullity forces `finrank range = 10`, `finrank ker = 5`, hence
  `ker kPhi = span{lamVec k}`;
* the coefficient vector `cW p q` of `p X₁² + q X₀X₂` is **not** in that span: its support
  `{5, 2}` (the pairs `(1,1)` and `(0,2)`) is contained in the support `{5, 13, 2}` of the third
  Pfaffian vector `lamVec a b 3`, so `cW = μ • lamVec a b 3`; comparing the coefficient at the pair
  `(3,4)` (index `13`, where `cW` vanishes and `lamVec a b 3` equals `a²`) gives `μ = 0`, whence
  `p = q = 0`, contradicting `(p, q) ≠ 0`;
* hence `kPhi (cW p q) = p κ₁² + q κ₀κ₂ ≠ 0`.

The statement `sdRankQuad12` is the specialisation `L = K̄ = AlgebraicClosure K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators

namespace Work.MotK.TwRuling

/-! ## §1 The coefficient vector of `p X₁² + q X₀X₂` -/

/-- The coefficient vector of the quadric `p x₁² + q x₀x₂`, in the fifteen products
`κ_i κ_j` (`i ≤ j`) indexed by `idxPair`.  The pairs `(1,1)` and `(0,2)` are the indices
`5` and `2` respectively. -/
noncomputable def cW {L : Type*} [CommRing L] (p q : L) : Fin 15 → L :=
  p • Pi.single (5 : Fin 15) (1 : L) + q • Pi.single (2 : Fin 15) (1 : L)

lemma cW_apply_5 {L : Type*} [CommRing L] (p q : L) : cW p q 5 = p := by
  simp [cW, Pi.single, Fin.ext_iff]

lemma cW_apply_2 {L : Type*} [CommRing L] (p q : L) : cW p q 2 = q := by
  simp [cW, Pi.single, Fin.ext_iff]

lemma cW_apply_13 {L : Type*} [CommRing L] (p q : L) : cW p q 13 = 0 := by
  simp [cW, Pi.single, Fin.ext_iff]

/-! ## §2 The three relevant components of the Pfaffian vectors -/

/-- The coefficient at the pair `(1,1)` (index `5`) of the `k`-th Pfaffian vector: this pair
occurs only in the third Pfaffian, where the coefficient is `-ab`. -/
lemma lamVec_apply_5 {L : Type*} [CommRing L] (a b : L) (k : Fin 5) :
    lamVec a b k 5 = if k = 3 then -(a * b) else 0 := by
  fin_cases k <;> simp [lamVec, lamIdx, Pi.single, Fin.ext_iff]

/-- The coefficient at the pair `(3,4)` (index `13`) of the `k`-th Pfaffian vector: this pair
occurs only in the third Pfaffian, where the coefficient is `a²`. -/
lemma lamVec_apply_13 {L : Type*} [CommRing L] (a b : L) (k : Fin 5) :
    lamVec a b k 13 = if k = 3 then a ^ 2 else 0 := by
  fin_cases k <;> simp [lamVec, lamIdx, Pi.single, Fin.ext_iff]

/-- The coefficient at the pair `(0,2)` (index `2`) of the `k`-th Pfaffian vector: this pair
occurs only in the third Pfaffian, where the coefficient is `-b²`. -/
lemma lamVec_apply_2 {L : Type*} [CommRing L] (a b : L) (k : Fin 5) :
    lamVec a b k 2 = if k = 3 then -(b ^ 2) else 0 := by
  fin_cases k <;> simp [lamVec, lamIdx, Pi.single, Fin.ext_iff]

lemma sum_lamVec_5 {L : Type*} [CommRing L] (a b : L) (μ : Fin 5 → L) :
    (∑ i : Fin 5, μ i • lamVec a b i) 5 = μ 3 * (-(a * b)) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single 3]
  · rw [lamVec_apply_5]; simp
  · intro k _ hk; rw [lamVec_apply_5]; simp [hk]
  · intro h; exact absurd (Finset.mem_univ 3) h

lemma sum_lamVec_13 {L : Type*} [CommRing L] (a b : L) (μ : Fin 5 → L) :
    (∑ i : Fin 5, μ i • lamVec a b i) 13 = μ 3 * a ^ 2 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single 3]
  · rw [lamVec_apply_13]; simp
  · intro k _ hk; rw [lamVec_apply_13]; simp [hk]
  · intro h; exact absurd (Finset.mem_univ 3) h

lemma sum_lamVec_2 {L : Type*} [CommRing L] (a b : L) (μ : Fin 5 → L) :
    (∑ i : Fin 5, μ i • lamVec a b i) 2 = μ 3 * (-(b ^ 2)) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single 3]
  · rw [lamVec_apply_2]; simp
  · intro k _ hk; rw [lamVec_apply_2]; simp [hk]
  · intro h; exact absurd (Finset.mem_univ 3) h

/-! ## §3 `kPhi` applied to the candidate vector -/

lemma kPhi_cW {𝕜 : Type*} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type*) [Field L] [Algebra 𝕜 L] (pL qL : L) :
    kPhi D L (cW pL qL)
      = algebraMap L (Affine.FunctionField (D.E.baseChange L)) pL
          * (Work.MotV.kleinCoord D L 1 * Work.MotV.kleinCoord D L 1)
        + algebraMap L (Affine.FunctionField (D.E.baseChange L)) qL
          * (Work.MotV.kleinCoord D L 0 * Work.MotV.kleinCoord D L 2) := by
  show kPhi D L (pL • Pi.single (5 : Fin 15) (1 : L) + qL • Pi.single (2 : Fin 15) (1 : L)) = _
  rw [map_add, map_smul, map_smul, kPhi_single, kPhi_single]
  have h5 : idxPair (5 : Fin 15) = ((1 : Fin 5), (1 : Fin 5)) := by decide
  have h2 : idxPair (2 : Fin 15) = ((0 : Fin 5), (2 : Fin 5)) := by decide
  rw [h5, h2]
  simp only [Algebra.smul_def]

/-! ## §4 The general non-degeneracy statement -/

theorem kleinQuad12_ne_zero {𝕜 : Type*} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type*) [Field L] [Algebra 𝕜 L] (aL bL pL qL : L)
    (haL : aL = algebraMap 𝕜 L D.a) (hbL : bL = algebraMap 𝕜 L D.b)
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m : Fin 5, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (Affine.FunctionField (D.E.baseChange L))
        (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (hklein : ∀ k : Fin 5, Work.MotK.kleinP
      (algebraMap 𝕜 (Affine.FunctionField (D.E.baseChange L)) D.a)
      (algebraMap 𝕜 (Affine.FunctionField (D.E.baseChange L)) D.b)
      (Work.MotV.kleinCoord D L) k = 0)
    (hab : aL * bL ≠ 0) (hpq : pL ≠ 0 ∨ qL ≠ 0) :
    algebraMap L (Affine.FunctionField (D.E.baseChange L)) pL
        * (Work.MotV.kleinCoord D L 1 * Work.MotV.kleinCoord D L 1)
      + algebraMap L (Affine.FunctionField (D.E.baseChange L)) qL
        * (Work.MotV.kleinCoord D L 0 * Work.MotV.kleinCoord D L 2) ≠ 0 := by
  classical
  have ha : aL ≠ 0 := fun h => hab (by rw [h, zero_mul])
  have hb : bL ≠ 0 := fun h => hab (by rw [h, mul_zero])
  have hfr : FiniteDimensional L ↥(kPhi D L).range :=
    FiniteDimensional.of_surjective (LinearMap.rangeRestrict (kPhi D L))
      (LinearMap.surjective_rangeRestrict _)
  haveI := hfr
  -- the ten monomials lie in the range, which therefore has dimension `≥ 10`
  have hspan_le : Submodule.span L (Set.range (Work.MotTDG.tenMon (D.E.baseChange L)))
      ≤ (kPhi D L).range := by
    rw [Submodule.span_le]
    rintro x ⟨t, rfl⟩
    exact tenMon_mem_range D L e he t
  have hfin10 : Module.finrank L ↥(Submodule.span L
      (Set.range (Work.MotTDG.tenMon (D.E.baseChange L)))) = 10 := by
    rw [finrank_span_eq_card (Work.MotTDG.tenMon_linearIndependent (D.E.baseChange L))]
    simp
  -- the five Pfaffian relations lie in the kernel, which therefore has dimension `≥ 5`
  have hlam_le : Submodule.span L (Set.range (lamVec aL bL))
      ≤ LinearMap.ker (kPhi D L) := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact lamVec_mem_ker D L aL bL haL hbL hklein k
  have hfin_lam : Module.finrank L ↥(Submodule.span L (Set.range (lamVec aL bL))) = 5 := by
    rw [finrank_span_eq_card (lamVec_linearIndependent aL bL hab)]
    simp
  -- rank--nullity
  have hrn : Module.finrank L ↥(kPhi D L).range
      + Module.finrank L ↥(LinearMap.ker (kPhi D L)) = 15 := by
    have h := LinearMap.finrank_range_add_finrank_ker (kPhi D L)
    rwa [Module.finrank_fin_fun] at h
  have hker5 : 5 ≤ Module.finrank L ↥(LinearMap.ker (kPhi D L)) := by
    have h := Submodule.finrank_mono hlam_le
    rwa [hfin_lam] at h
  have hQ10 : Module.finrank L ↥(kPhi D L).range = 10 := by
    have h := Submodule.finrank_mono hspan_le
    rw [hfin10] at h
    omega
  have hker5' : Module.finrank L ↥(LinearMap.ker (kPhi D L)) = 5 := by omega
  have hker_eq : LinearMap.ker (kPhi D L) = Submodule.span L (Set.range (lamVec aL bL)) :=
    (Submodule.eq_of_le_of_finrank_le hlam_le (by rw [hker5', hfin_lam])).symm
  -- `cW` is not a relation: its support lies in that of the third Pfaffian vector, and the
  -- `(3,4)`-component (which `cW` misses) isolates that vector
  have hcW : cW pL qL ∉ Submodule.span L (Set.range (lamVec aL bL)) := by
    intro hmem
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    have h13 := congrFun hμ (13 : Fin 15)
    have h5 := congrFun hμ (5 : Fin 15)
    have h2 := congrFun hμ (2 : Fin 15)
    rw [sum_lamVec_13 aL bL μ, cW_apply_13] at h13
    rw [sum_lamVec_5 aL bL μ, cW_apply_5] at h5
    rw [sum_lamVec_2 aL bL μ, cW_apply_2] at h2
    have hmu3 : μ 3 = 0 := (mul_eq_zero.mp h13).resolve_right (pow_ne_zero 2 ha)
    rw [hmu3, zero_mul] at h5 h2
    rcases hpq with hp | hq
    · exact hp h5.symm
    · exact hq h2.symm
  have hne : kPhi D L (cW pL qL) ≠ 0 := by
    intro h0
    exact hcW (by rw [← hker_eq]; exact h0)
  rw [kPhi_cW D L pL qL] at hne
  exact hne

/-! ## §5 The target statement -/

theorem sdRankQuad12 (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (p q : K) (hc : p ≠ 0 ∨ q ≠ 0) :
    algebraMap K (Work.MotK.OmG K D) p
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 1 * Work.MotV.kleinCoord D (Work.MotK.KbG K) 1)
      + algebraMap K (Work.MotK.OmG K D) q
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 * Work.MotV.kleinCoord D (Work.MotK.KbG K) 2)
      ≠ 0 := by
  obtain ⟨e, he⟩ := hD.spans
  have hab : algebraMap K (Work.MotK.KbG K) D.a * algebraMap K (Work.MotK.KbG K) D.b ≠ 0 := by
    rw [← map_mul]
    intro h0
    have h1 : algebraMap K (Work.MotK.KbG K) ((D.a * D.b)⁻¹)
        * algebraMap K (Work.MotK.KbG K) (D.a * D.b) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hD.ab_ne, map_one]
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  have hpq : algebraMap K (Work.MotK.KbG K) p ≠ 0 ∨ algebraMap K (Work.MotK.KbG K) q ≠ 0 := by
    rcases hc with hp | hq
    · left
      intro h0
      exact hp (RingHom.injective (algebraMap K (Work.MotK.KbG K)) (by rw [h0, map_zero]))
    · right
      intro h0
      exact hq (RingHom.injective (algebraMap K (Work.MotK.KbG K)) (by rw [h0, map_zero]))
  have h := kleinQuad12_ne_zero D (Work.MotK.KbG K) (algebraMap K (Work.MotK.KbG K) D.a)
      (algebraMap K (Work.MotK.KbG K) D.b) (algebraMap K (Work.MotK.KbG K) p)
      (algebraMap K (Work.MotK.KbG K) q) rfl rfl e (he (Work.MotK.KbG K))
      (fun k => hD.klein_eq (Work.MotK.KbG K) k) hab hpq
  simpa only [IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)] using h

end Work.MotK.TwRuling
