/-
# The sharp ray-class count for a congruence subgroup, from the dictionary identity

The dictionary identity (`NK.NUV2.RouteB.HeckeTheta.rayClassCnt_eq_coset_sum`) expresses the
number of ideals in a ray class of the congruence subgroup `U(𝔪)` as a sum of lattice-coset counts
`cosetConeCnt` over a transversal of the units modulo `congUnit 𝔪`.  The lattice-coset counts are
asymptotic to `t · vol(sign region)/covol` with a power-saving error
(`NK.NUV2.RouteB.HeckeTheta.cosetConeCnt_sharp`, in `DictTools`).

This file sums those asymptotics over the finitely many ray classes.  The main terms are independent
of the class because `N𝔡 · covol(𝔪𝔡⁻¹)` is (`absNorm_mul_dictCovol`), so the main terms cancel in
the difference of two class counts, leaving `O(X^{1-1/[K:ℚ]})`.  This is the statement `SharpSub`
consumed by `NK.NUV2.RouteB.uniform_of_sharp_aux`.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.RouteB.HeckeTheta.DictTools
import Submission.NK.NUV2.RouteB.RayModulus.exists_ideal_of_class
import Submission.NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup
import Submission.NK.NUV2.RouteB.Unif.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors BigOperators

noncomputable section

namespace NK.NUV2.RouteB.HeckeTheta

variable {K : Type} [Field K] [NumberField K]

theorem mem_supportFinset_iff (𝔪 : NK.NUV2.RouteB.Modulus K)
    (q : HeightOneSpectrum (𝓞 K)) :
    q ∈ 𝔪.supportFinset ↔ 𝔪.exps q ≠ 0 := by
  rw [NK.NUV2.RouteB.Modulus.supportFinset, Set.Finite.mem_toFinset]
  exact Iff.rfl

theorem div_mul_div_eq (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b * c / d = a * c / (b * d) := by
  field_simp

/-- A ray-class count with norm bound below `M` is bounded by the number of all nonzero ideals of
norm `≤ M`. -/
theorem rayClassCnt_le_card_absNorm_le (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔡 : Ideal (𝓞 K)) (M : ℕ) {X : ℝ} (hX : X ≤ (M : ℝ)) :
    NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X
      ≤ Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ M} := by
  haveI : Finite {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ M} :=
    ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) M).subset
      (fun I hI => hI.2)).to_subtype
  refine Nat.card_le_card_of_injective
    (fun a : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧
        (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ 𝔞) ∧
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔞 =
          NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔡 ∧
        (Ideal.absNorm 𝔞 : ℝ) ≤ X} => ⟨a.1, a.2.1, Nat.cast_le.mp (le_trans a.2.2.2.2 hX)⟩) ?_
  intro a b h
  exact Subtype.ext (congrArg (fun t => t.1) h)

/-- The `Nat.card` count of the ideals in a fixed ray class of `U(𝔪)` is `rayClassCnt`. -/
theorem natCard_class_eq_rayClassCnt (𝔪 : NK.NUV2.RouteB.Modulus K)
    (𝔡 : Ideal (𝓞 K)) (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪))
    (hcl : NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔡 = c) (X : ℝ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧
        (∀ 𝔭 ∈ 𝔪.supportFinset, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔞 = c ∧
        Ideal.absNorm 𝔞 ≤ X}
      = NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X := by
  rw [NK.NUV2.RouteB.rayClassCnt]
  refine Nat.card_congr (Equiv.subtypeEquivProp (funext fun 𝔞 => propext ?_))
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun q hq => h2 q ((mem_supportFinset_iff 𝔪 q).mpr hq), by rw [h3, hcl], by
      exact_mod_cast h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun 𝔭 h𝔭 => h2 𝔭 ((mem_supportFinset_iff 𝔪 𝔭).mp h𝔭), by rw [h3, hcl], by
      exact_mod_cast h4⟩

/-- **The sharp ray-class count for a congruence subgroup, from the dictionary identity.** -/
theorem sharpSub_of_dictionary (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    (hDict : ∀ (𝔡 : Ideal (𝓞 K)) (h𝔡 : 𝔡 ≠ 0),
      (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ 𝔡) → ∀ X : ℝ,
      (NumberField.Units.torsionOrder K : ℝ) * (NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X : ℝ)
        = ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
            (NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 ⟨𝔡, mem_nonZeroDivisors_of_ne_zero h𝔡⟩
              (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹) (X / (Ideal.absNorm 𝔡 : ℝ)) : ℝ)) :
    NK.NUV2.RouteB.SharpSub K (NK.NUV2.RouteB.CongSubgroup K 𝔪) 𝔪.supportFinset
      (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  classical
  haveI hfinR : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) :=
    NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup K 𝔪
  letI : Fintype (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) := Fintype.ofFinite _
  letI : Fintype ((𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪) := instFintypeQuotCongUnit 𝔪
  set θ : ℝ := 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    have h1 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne')
    linarith
  -- the main-term data
  set σ : ℝ := ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
    sgnRegionVol 𝔪 (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹) with hσ
  set κ₀ : ℝ := (Ideal.absNorm 𝔪.ideal : ℝ) *
    (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|) with hκ
  have hκpos : 0 < κ₀ := by
    rw [hκ]
    refine mul_pos (by exact_mod_cast (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      ((mem_nonZeroDivisors_iff_ne_zero).mpr 𝔪.ideal_ne_zero))) ?_
    refine mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr ?_)
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  -- representatives of the ray classes, coprime to the modulus
  choose 𝔡 h𝔡ne h𝔡cop h𝔡cl using fun c =>
    NK.NUV2.RouteB.RayModulus.exists_ideal_of_class K 𝔪 c
  -- the per-(class, unit coset) constants of the coset count
  have hex2 : ∀ p : (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
        (NK.NUV2.RouteB.CongSubgroup K 𝔪)) × ((𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪),
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
        |((NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪
            ⟨𝔡 p.1, mem_nonZeroDivisors_of_ne_zero (h𝔡ne p.1)⟩
            (((Quotient.out p.2 : (𝓞 K)ˣ) : K)⁻¹) t : ℝ)
          - t * sgnRegionVol 𝔪 (((Quotient.out p.2 : (𝓞 K)ˣ) : K)⁻¹)
              / dictCovol 𝔪 ⟨𝔡 p.1, mem_nonZeroDivisors_of_ne_zero (h𝔡ne p.1)⟩)|
        ≤ C * t ^ θ := by
    rintro ⟨c, q⟩
    exact cosetConeCnt_sharp 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩ _
  choose Cq hCqpos hCqbd using hex2
  set Ctot : (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)) → ℝ :=
    fun c => 1 + ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪, Cq (c, q) with hCtot
  -- bookkeeping constants
  set M : ℕ := ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪), Ideal.absNorm (𝔡 c) with hM
  set T : ℝ := (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ M} : ℝ) with hT
  have hTnn : 0 ≤ T := Nat.cast_nonneg _
  have hTorsionPos : (0 : ℝ) < (NumberField.Units.torsionOrder K : ℝ) := by
    exact_mod_cast NumberField.Units.torsionOrder_pos K
  have hNM : ∀ c, Ideal.absNorm (𝔡 c) ≤ M := by
    intro c
    rw [hM]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun c => Ideal.absNorm (𝔡 c))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ c)
  have hNpos : ∀ c, (0 : ℝ) < (Ideal.absNorm (𝔡 c) : ℝ) := by
    intro c
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => h𝔡ne c (Ideal.absNorm_eq_zero_iff.mp h0)
  -- the bookkeeping constant for the small-`X` range
  set K₀ : ℝ := (NumberField.Units.torsionOrder K : ℝ) * T + (M : ℝ) * (|σ| / κ₀) with hKdef
  have hK₀nn : 0 ≤ K₀ := by
    rw [hKdef]
    exact add_nonneg (mul_nonneg hTorsionPos.le hTnn)
      (mul_nonneg (Nat.cast_nonneg M) (div_nonneg (abs_nonneg σ) hκpos.le))
  have hCc_nn : ∀ c, 0 ≤ Ctot c + K₀ := by
    intro c
    rw [hCtot]
    have : 0 ≤ ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪, Cq (c, q) :=
      Finset.sum_nonneg (fun q _ => (hCqpos (c, q)).le)
    linarith
  have hN1 : ∀ c, (1 : ℝ) ≤ (Ideal.absNorm (𝔡 c) : ℝ) := by
    intro c
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h0 => h𝔡ne c (Ideal.absNorm_eq_zero_iff.mp h0)
  have hCtot_eq : ∀ c, Ctot c = 1 + ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
      Cq (c, q) := fun c => rfl
  have hCtotnn : ∀ c, 0 ≤ Ctot c := by
    intro c
    rw [hCtot_eq c]
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun q _ => (hCqpos (c, q)).le))
  -- per class bound
  have hclass : ∀ c, ∀ X : ℝ, 1 ≤ X →
      |(NumberField.Units.torsionOrder K : ℝ) * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ)
          - X * (σ / κ₀)|
        ≤ (Ctot c + K₀) * X ^ θ := by
    intro c X hX
    have hXθ1 : 1 ≤ X ^ θ := Real.one_le_rpow hX hθ0
    have hXθnn : 0 ≤ X ^ θ := le_trans zero_le_one hXθ1
    have hXpos : 0 ≤ X := le_trans zero_le_one hX
    by_cases hXM : (M : ℝ) ≤ X
    · -- large `X`: the dictionary identity plus the sharp coset counts
      have ht1 : ∀ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
          1 ≤ X / (Ideal.absNorm (𝔡 c) : ℝ) := by
        intro q
        rw [le_div_iff₀ (hNpos c), one_mul]
        exact le_trans (by exact_mod_cast hNM c) hXM
      have hcov : (Ideal.absNorm (𝔡 c) : ℝ)
          * dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩ = κ₀ := by
        rw [hκ]
        exact absNorm_mul_dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩
      have hDne : dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hcov
        exact hκpos.ne' hcov.symm
      have hmain : X * (σ / κ₀)
          = ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
              (X / (Ideal.absNorm (𝔡 c) : ℝ)) * sgnRegionVol 𝔪
                  (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹)
                / dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩ := by
        rw [hσ, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [← mul_div_assoc, div_mul_div_eq X (Ideal.absNorm (𝔡 c) : ℝ)
          (sgnRegionVol 𝔪 (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹))
          (dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩)
          (hNpos c).ne' hDne, ← hcov]
      rw [hDict (𝔡 c) (h𝔡ne c) (h𝔡cop c) X, hmain, ← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hstep : ∀ q ∈ (Finset.univ : Finset ((𝓞 K)ˣ ⧸
            NK.NUV2.HeckeAnalytic.congUnit 𝔪)),
          |(NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪
              ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩
              (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹) (X / (Ideal.absNorm (𝔡 c) : ℝ)) : ℝ)
            - (X / (Ideal.absNorm (𝔡 c) : ℝ)) * sgnRegionVol 𝔪
                (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹)
              / dictCovol 𝔪 ⟨𝔡 c, mem_nonZeroDivisors_of_ne_zero (h𝔡ne c)⟩|
          ≤ Cq (c, q) * X ^ θ := by
        intro q _
        refine le_trans (hCqbd (c, q) _ (ht1 q)) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCqpos (c, q)).le
        exact Real.rpow_le_rpow (le_trans zero_le_one (ht1 q))
          (div_le_self (le_trans zero_le_one hX) (hN1 c)) hθ0
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hXθnn
      have hsum_le : (∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪, Cq (c, q)) ≤ Ctot c + K₀ := by
        have h1 : (∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪, Cq (c, q)) ≤ Ctot c := by
          rw [hCtot_eq c]
          exact le_add_of_nonneg_left zero_le_one
        linarith [hK₀nn]
      exact hsum_le
    · -- small `X`: the crude bound
      push Not at hXM
      have hXMle : X ≤ (M : ℝ) := le_of_lt hXM
      have hA : (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) ≤ T := by
        rw [hT]
        exact_mod_cast rayClassCnt_le_card_absNorm_le 𝔪 (𝔡 c) M hXMle
      have hσκ : 0 ≤ |σ| / κ₀ := div_nonneg (abs_nonneg σ) hκpos.le
      have hbound : |(NumberField.Units.torsionOrder K : ℝ)
            * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) - X * (σ / κ₀)| ≤ K₀ := by
        have hA' : (NumberField.Units.torsionOrder K : ℝ)
            * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ)
            ≤ (NumberField.Units.torsionOrder K : ℝ) * T :=
          mul_le_mul_of_nonneg_left hA hTorsionPos.le
        have h1 : (NumberField.Units.torsionOrder K : ℝ)
              * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) - X * (σ / κ₀) ≤ K₀ := by
          rw [hKdef]
          have hsumσκ : 0 ≤ σ / κ₀ + |σ| / κ₀ := by
            rw [← add_div]
            exact div_nonneg (by linarith [neg_le_abs σ]) hκpos.le
          have hXσ : -X * (|σ| / κ₀) ≤ X * (σ / κ₀) := by
            nlinarith [hsumσκ, hXpos]
          have hMX : X * (|σ| / κ₀) ≤ (M : ℝ) * (|σ| / κ₀) :=
            mul_le_mul_of_nonneg_right hXMle hσκ
          linarith
        have h2 : X * (σ / κ₀) - (NumberField.Units.torsionOrder K : ℝ)
              * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) ≤ K₀ := by
          rw [hKdef]
          have h4 : σ / κ₀ ≤ |σ| / κ₀ := div_le_div_of_nonneg_right (le_abs_self σ) hκpos.le
          have hXσ : X * (σ / κ₀) ≤ X * (|σ| / κ₀) := mul_le_mul_of_nonneg_left h4 hXpos
          have hMX : X * (|σ| / κ₀) ≤ (M : ℝ) * (|σ| / κ₀) :=
            mul_le_mul_of_nonneg_right hXMle hσκ
          have hA0 : 0 ≤ (NumberField.Units.torsionOrder K : ℝ)
              * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) :=
            mul_nonneg hTorsionPos.le (Nat.cast_nonneg _)
          have hTnn' : 0 ≤ (NumberField.Units.torsionOrder K : ℝ) * T :=
            mul_nonneg hTorsionPos.le hTnn
          linarith
        exact abs_sub_le_iff.mpr ⟨h1, h2⟩
      calc |(NumberField.Units.torsionOrder K : ℝ)
            * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c) X : ℝ) - X * (σ / κ₀)| ≤ K₀ := hbound
        _ ≤ (Ctot c + K₀) * X ^ θ := by
          calc K₀ = K₀ * 1 := (mul_one K₀).symm
            _ ≤ K₀ * X ^ θ := mul_le_mul_of_nonneg_left hXθ1 hK₀nn
            _ ≤ (Ctot c + K₀) * X ^ θ :=
                mul_le_mul_of_nonneg_right (by linarith [hCtotnn c]) hXθnn
  -- the total constant is positive
  have hsum_pos : 0 < ∑ c, (Ctot c + K₀) := by
    obtain ⟨c₀⟩ := (inferInstance : Nonempty (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔪)))
    have h1 : Ctot c₀ + K₀ ≤ ∑ c, (Ctot c + K₀) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun c => Ctot c + K₀)
        (fun i _ => hCc_nn i) (Finset.mem_univ c₀)
    have h2 : 1 ≤ Ctot c₀ := by
      rw [hCtot_eq c₀]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun q _ => (hCqpos (c₀, q)).le))
    linarith [hK₀nn]
  have hCc_le : ∀ c, Ctot c + K₀ ≤ ∑ c, (Ctot c + K₀) := fun c =>
    Finset.single_le_sum (s := Finset.univ) (f := fun c => Ctot c + K₀)
      (fun i _ => hCc_nn i) (Finset.mem_univ c)
  have hsum_nn : 0 ≤ ∑ c, (Ctot c + K₀) := le_of_lt hsum_pos
  -- the difference of two class counts
  refine ⟨(2 * ∑ c, (Ctot c + K₀)) / (NumberField.Units.torsionOrder K : ℝ),
    div_pos (mul_pos two_pos hsum_pos) hTorsionPos, fun X hX c₁ c₂ => ?_⟩
  rw [natCard_class_eq_rayClassCnt 𝔪 (𝔡 c₁) c₁ (h𝔡cl c₁) X,
    natCard_class_eq_rayClassCnt 𝔪 (𝔡 c₂) c₂ (h𝔡cl c₂) X]
  have hXθnn : 0 ≤ X ^ θ := Real.rpow_nonneg (le_trans zero_le_one hX) θ
  set u : ℝ := (NumberField.Units.torsionOrder K : ℝ)
    * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c₁) X : ℝ) - X * (σ / κ₀) with hu_def
  set v : ℝ := (NumberField.Units.torsionOrder K : ℝ)
    * (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c₂) X : ℝ) - X * (σ / κ₀) with hv_def
  have hu : |u| ≤ (Ctot c₁ + K₀) * X ^ θ := hclass c₁ X hX
  have hv : |v| ≤ (Ctot c₂ + K₀) * X ^ θ := hclass c₂ X hX
  have hkey : |(NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c₁) X : ℝ)
        - (NK.NUV2.RouteB.rayClassCnt K 𝔪 (𝔡 c₂) X : ℝ)| = |u - v|
          / (NumberField.Units.torsionOrder K : ℝ) := by
    rw [hu_def, hv_def]
    rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_pos hTorsionPos,
      mul_div_cancel_left₀ _ hTorsionPos.ne']
  rw [hkey]
  have huv : |u - v| ≤ (Ctot c₁ + K₀) * X ^ θ + (Ctot c₂ + K₀) * X ^ θ := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith [hu, hv, le_abs_self u, neg_le_abs v]
    · linarith [hu, hv, le_abs_self v, neg_le_abs u]
  have hsum2 : (Ctot c₁ + K₀) * X ^ θ + (Ctot c₂ + K₀) * X ^ θ
      ≤ (2 * ∑ c, (Ctot c + K₀)) * X ^ θ := by
    have h1 : (Ctot c₁ + K₀) * X ^ θ ≤ (∑ c, (Ctot c + K₀)) * X ^ θ :=
      mul_le_mul_of_nonneg_right (hCc_le c₁) hXθnn
    have h2 : (Ctot c₂ + K₀) * X ^ θ ≤ (∑ c, (Ctot c + K₀)) * X ^ θ :=
      mul_le_mul_of_nonneg_right (hCc_le c₂) hXθnn
    have h3 : (2 * ∑ c, (Ctot c + K₀)) * X ^ θ
        = (∑ c, (Ctot c + K₀)) * X ^ θ + (∑ c, (Ctot c + K₀)) * X ^ θ := by ring
    linarith
  calc |u - v| / (NumberField.Units.torsionOrder K : ℝ)
      ≤ ((2 * ∑ c, (Ctot c + K₀)) * X ^ θ) / (NumberField.Units.torsionOrder K : ℝ) :=
        div_le_div_of_nonneg_right (le_trans huv hsum2) hTorsionPos.le
    _ = (2 * ∑ c, (Ctot c + K₀)) / (NumberField.Units.torsionOrder K : ℝ) * X ^ θ := by ring

end NK.NUV2.RouteB.HeckeTheta
