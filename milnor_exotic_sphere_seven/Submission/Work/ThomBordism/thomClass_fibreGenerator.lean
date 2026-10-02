import Mathlib
import Submission.Work.Thom.chartCoeff_nonZeroDivisor
import Submission.Work.ThomBordism.h0SignUnit
import Submission.Work.ThomBordism.chartDataDescent
import Submission.Work.ThomBordism.coeff_pm_one_of_normalized
import Submission.Work.ThomBordism.normalized_chartData_compatible
import Submission.Work.ThomBordism.pieceRes_singleton_eq_smul
import Submission.Work.ThomBordism.span_localThom_singleton
import Submission.Work.ThomBordism.localThom_of_involution_smul
import Submission.Work.ThomBordism.fibreRes_span_iff
import Submission.Work.ThomBordism.fibreGenerator_zero_rank
import Submission.Work.ThomBordism.thomClassFibreDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# A Thom class at the rank degree restricts to a generator on every fibre

`Work.ThomBordism.thomClass_fibreGenerator`: for a real bundle `Z → B` and a Thom class `T` of `Z`
in the degree `n = finrank ℝ F` of the fibre, the restriction of `T.τ` to the fibre pair
`(Z_b, Z_b ∖ 0)` generates `H^n(Z_b, Z_b∖0; ℤ)` — the "exercise" direction of Hatcher 4D.10.

The proof (for `n ≥ 1`) has three parts.

* Over each chart piece `U = Z.baseSet i` the restriction of `T.τ` is `d_i ⌣ τ_i` for the explicit
  chart class `τ_i = (localThomOfChart ...).τ` (`exists_coeff`), and `d_i` is nowhere vanishing
  (`coeff_ptEv_ne_zero`).
* Normalising by the sign class `s_i` of `d_i` (`h0SignUnit`) gives compatible local Thom data
  (`normalized_chartData_compatible`, `localThom_of_involution_smul`), which glues to a global class
  `σ` (`chartDataDescent`); by the Thom isomorphism in degree `0`, `σ = x ⌣ T.τ`, and comparing over
  `U` shows that `d_i` is a unit — so `d_i` takes the values `±1`
  (`coeff_pm_one_of_normalized`).
* Hence `(PieceRes Z {b} n) T.τ = ± τ_i|_{{b}}` (`pieceRes_singleton_eq_smul`), which generates
  (`span_localThom_singleton`), and the fibre and piece spans agree (`fibreRes_span_iff`).

The case `n = 0` is `fibreGenerator_zero_rank`.
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- The **explicit chart class** of `Z` over `U ⊆ Z.baseSet i` (the pullback of the model class
`Mpun n ↥U` along the chart homeomorphism, `Work.Thom.localThomOfChart`). -/
abbrev chartClass (Z : RealBundle B F ι) (n : ℕ) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i : ι) (U : Set B) (hU : U ⊆ Z.baseSet i) : Work.Thom.PieceCoh Z U n :=
  (Work.Thom.localThomOfChart Z n e i U hU).τ

/-- **The coefficient of a Thom class over a chart piece never vanishes pointwise.** -/
theorem coeff_ptEv_ne_zero [FiniteDimensional ℝ F] (Z : RealBundle B F ι) {n : ℕ}
    (hrank : Z.rank = n) (hn1 : 1 ≤ n) (T : Work.Thom.ThomClass Z n)
    (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z W n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W (chartClass Z n e i W hW) 0 c)) :
    ∀ p : ↥W, Work.Thom.ptEv p c ≠ 0 := by
  intro p hpzero
  have hsep : ∀ z : Work.Thom.OpenThom Z (0 + n),
      (∀ i : ι, (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i) (0 + n))) z = 0) → z = 0 :=
    fun z hz => Work.Thom.openThom_zero_of_baseSet_zeroAdd Z n hrank hn1 z hz
  have hgood : ¬ Work.Thom.bad Z n T p.1 := by
    obtain ⟨b', hjoin, hgbad⟩ := Work.Thom.exists_good_point_of_separation Z n hsep e T p.1
    exact fun hb' => hgbad ((Work.Thom.bad_eq_of_joined Z hrank T hjoin).mp hb')
  have hsub : ({(p.1 : B)} : Set B) ⊆ Z.baseSet i :=
    fun y hy => hW (Work.Thom.singleton_subset_of_mem p.2 hy)
  exact hgood ((Work.Thom.bad_iff_ptEv Z n T i hW e c hc p.1 p.2 hsub).mpr hpzero)

/-- An integer whose product with another integer is `±1` is itself `±1`. -/
theorem int_pm_one_of_mul_pm_one {a b : ℤ} (h : a * b = 1 ∨ a * b = -1) :
    a = 1 ∨ a = -1 := by
  rcases h with h | h
  · exact Int.eq_one_or_neg_one_of_mul_eq_one h
  · have h2 : a * (-b) = 1 := by rw [mul_neg, h, neg_neg]
    exact Int.eq_one_or_neg_one_of_mul_eq_one h2

/-- **If `c ∈ H⁰` is inverted by `s`, then `c` evaluates to `±1` at every point.** -/
theorem ptEv_eq_one_or_neg_one_of_unit {W : Type} [TopologicalSpace W]
    {c s : Work.Thom.Coh ℤ 0 W}
    (hs : ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of W)) 0 0) s c)
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of W))) :
    ∀ p : W, Work.Thom.ptEv p c = 1 ∨ Work.Thom.ptEv p c = -1 := by
  intro p
  have h := Work.Thom.ptEv_cup p s c
  rw [hs, Work.Thom.ptEv_one] at h
  have h2 : Work.Thom.ptEv p c * Work.Thom.ptEv p s = 1 := by
    rw [mul_comm]; exact h.symm
  exact Int.eq_one_or_neg_one_of_mul_eq_one h2

theorem thomClass_fibreGenerator {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (hn : n = Module.finrank ℝ F) :
    Work.ThomBordism.IsFibreGenerator Z n T.τ := by
  classical
  by_cases h0 : n = 0
  · exact fibreGenerator_zero_rank Z T hn h0
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
    have hrank : Z.rank = n := by
      show Module.finrank ℝ F = n
      exact hn.symm
    have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [finrank_euclideanSpace_fin]
      exact hn.symm
    let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) hfr
    -- the chart coefficients of `T.τ`
    choose d hd using fun i : ι =>
      Work.Thom.exists_coeff Z n T e i (subset_rfl : Z.baseSet i ⊆ Z.baseSet i)
    have hdv : ∀ (i : ι) (p : ↥(Z.baseSet i)), Work.Thom.ptEv p (d i) ≠ 0 :=
      fun i p => coeff_ptEv_ne_zero Z hrank hn1 T i (Z.baseSet i) subset_rfl e (d i) (hd i) p
    -- the sign classes
    choose s hs using fun i : ι => h0SignUnit (d i) (fun p => hdv i p)
    -- the sign classes are involutions
    have hss : ∀ i : ι, ((Work.Cohomology.cupH' ℤ
        (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0) (s i) (s i))
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) :=
      fun i => Work.Thom.ptEv_ext (fun p => by
        rw [(hs i).1 p, Work.Thom.ptEv_one])
    -- the normalised data is local Thom data
    have hc : ∀ (i : ι) (k : ℕ), Function.Bijective (Work.Thom.localThomMap Z n (Z.baseSet i)
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
          (chartClass Z n e i (Z.baseSet i) subset_rfl) 0 (s i))) k) :=
      fun i k => localThom_of_involution_smul Z
        (chartClass Z n e i (Z.baseSet i) subset_rfl)
        ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) subset_rfl).isThom) (s i) (hss i) k
    -- and it is compatible on the overlaps
    have hcompat : ∀ i j : ι,
        (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Z.baseSet i))
            (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j)) (Set.preimage_mono Set.inter_subset_left) n))
            ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
              (chartClass Z n e i (Z.baseSet i) subset_rfl) 0 (s i)))
          = (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Z.baseSet j))
            (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j)) (Set.preimage_mono Set.inter_subset_right) n))
            ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet j)
              (chartClass Z n e j (Z.baseSet j) subset_rfl) 0 (s j))) :=
      fun i j => normalized_chartData_compatible Z T e d hd hdv s (fun i p => (hs i).2 p) i j
    -- the low-degree vanishing
    have hlow : ∀ W : Set B, Subsingleton (Work.Thom.PieceCoh Z W (n - 1)) :=
      fun W => Work.Thom.subsingleton_PieceCoh_of_lt_finrank Z W (by rw [← hn]; omega)
    -- the descent
    obtain ⟨σ, hσ⟩ := chartDataDescent Z n hn1 (fun i : ι => (Nat.zero_add n) ▸
        (Work.Thom.localThomMap Z n (Z.baseSet i) (chartClass Z n e i (Z.baseSet i) subset_rfl) 0
          (s i))) hc hcompat hlow
    -- the coefficients are `±1`
    have hpm := coeff_pm_one_of_normalized Z T e d s hd hss σ hσ
    intro b
    have hb : b ∈ Z.baseSet (Z.indexAt b) := Z.mem_baseSet_at b
    have hbsub : ({(b : B)} : Set B) ⊆ Z.baseSet (Z.indexAt b) := fun _ hy =>
      (Set.mem_singleton_iff.mp hy) ▸ Z.mem_baseSet_at b
    have hpiece : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z ({(b : B)} : Set B) n)) T.τ
        = (Work.Thom.ptEv ⟨b, hb⟩ (d (Z.indexAt b))) •
            ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({(b : B)} : Set B) hbsub).τ) :=
      pieceRes_singleton_eq_smul Z T e b (Z.baseSet (Z.indexAt b)) subset_rfl hb
        (d (Z.indexAt b)) (hd (Z.indexAt b))
    have hgen : Submodule.span ℤ {((Work.Thom.localThomOfChart Z n e (Z.indexAt b)
        ({(b : B)} : Set B) hbsub).τ)} = ⊤ :=
      span_localThom_singleton Z b _
        ((Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({(b : B)} : Set B) hbsub).isThom)
    set cτ : Work.Thom.PieceCoh Z ({(b : B)} : Set B) n :=
      (Work.Thom.localThomOfChart Z n e (Z.indexAt b) ({(b : B)} : Set B) hbsub).τ with hcτ
    have hneg : Submodule.span ℤ {(-1 : ℤ) • cτ} = Submodule.span ℤ {cτ} := by
      have hcoe : (-1 : ℤ) • cτ = -cτ := by simp
      rw [hcoe]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        show -cτ ∈ Submodule.span ℤ {cτ}
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton cτ))
      · rw [Submodule.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        show cτ ∈ Submodule.span ℤ {(-cτ)}
        simpa only [neg_neg] using
          (Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton (-cτ))))
    have hspan : Submodule.span ℤ
        {(ModuleCat.Hom.hom (Work.Thom.PieceRes Z ({(b : B)} : Set B) n)) T.τ} = ⊤ := by
      rw [hpiece]
      rcases hpm (Z.indexAt b) ⟨b, hb⟩ with h1 | h1
      · rw [h1, one_smul]
        exact hgen
      · rw [h1, hneg]
        exact hgen
    exact (fibreRes_span_iff Z b T.τ).mpr hspan

end

end Work.ThomBordism
