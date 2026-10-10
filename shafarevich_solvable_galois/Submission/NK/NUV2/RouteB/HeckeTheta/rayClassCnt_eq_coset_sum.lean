import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.NUV2.RouteB.CongCount.CongConeCount
import Submission.NK.NUV2.RouteB.HeckeTheta.DictLemma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ray-class/lattice dictionary

For a number field `K`, a modulus `𝔪` and a nonzero ideal `𝔡` coprime to the support of `𝔪`, the
number `rayClassCnt K 𝔪 𝔡 X` of ideals of `𝓞 K` which are nonzero, coprime to `𝔪`, in the ray class
of `𝔡` modulo `U(𝔪)` and of norm `≤ X`, counted with multiplicity `torsionOrder K`, is the sum,
over the unit cosets `q : (𝓞 K)ˣ ⧸ congUnit 𝔪`, of the lattice-coset counts
`cosetConeCnt 𝔪 𝔡 (out q)⁻¹ (X / N𝔡)`.

The proof glues three bijections:

* per coset, the lattice points of `(out q)⁻¹ + 𝔪𝔡⁻¹` in the fundamental cone are the admissible
  generators `piece 𝔪 𝔡 T (out q)` (`card_piece_eq_cosetConeCnt`);
* the pairs `(q, β)` of `piece`-elements are the generators in the fundamental cone
  (`coneCarrier_of_piece`, `piece_of_coneCarrier`, `piece_coset_eq`);
* the generators in the fundamental cone are `torsionOrder K` times the ideals of the ray class
  (`NK.NUV2.RouteB.CongCount.natCard_coneCarrier_eq_torsion_mul_idealCarrier`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors BigOperators
open NK.NUV2.RouteB

noncomputable section

namespace NK.NUV2.RouteB.HeckeTheta

variable {K : Type} [Field K] [NumberField K]

/-! ## Elementary real and sign lemmas -/

/-- The sign condition of `piece`, in terms of the product being positive. -/
theorem sign_iff_mul_pos (w : InfinitePlace K) (hw : w.IsReal) (γ β : K)
    (hγ : NumberField.InfinitePlace.embedding_of_isReal hw γ ≠ 0) :
    ((NumberField.InfinitePlace.embedding_of_isReal hw γ > 0 ∧
        NumberField.InfinitePlace.embedding_of_isReal hw β > 0) ∨
      (NumberField.InfinitePlace.embedding_of_isReal hw γ < 0 ∧
        NumberField.InfinitePlace.embedding_of_isReal hw β < 0))
      ↔ 0 < NumberField.InfinitePlace.embedding_of_isReal hw γ
          * NumberField.InfinitePlace.embedding_of_isReal hw β := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mul_pos h1 h2
    · exact mul_pos_of_neg_of_neg h1 h2
  · intro h
    rcases lt_trichotomy (NumberField.InfinitePlace.embedding_of_isReal hw γ) 0 with h1 | h1 | h1
    · exact Or.inr ⟨h1, by nlinarith [h1, h]⟩
    · exact absurd h1 hγ
    · exact Or.inl ⟨h1, by nlinarith [h1, h]⟩

/-- A real positivity computation. -/
theorem pos_inv_mul_of_pos_inv_mul {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : 0 < x⁻¹ * y) (h2 : 0 < z⁻¹ * y) : 0 < x⁻¹ * z := by
  have h3 : 0 < (x⁻¹ * y) * (z⁻¹ * y) := mul_pos h1 h2
  have h4 : (x⁻¹ * y) * (z⁻¹ * y) = (x⁻¹ * z⁻¹) * (y * y) := by ring
  rw [h4] at h3
  have h5 : 0 < x⁻¹ * z⁻¹ := (mul_pos_iff_of_pos_right (mul_self_pos.mpr hy)).mp h3
  have h6 : 0 < (x⁻¹ * z⁻¹) * (z * z) := mul_pos h5 (mul_self_pos.mpr hz)
  have h7 : (x⁻¹ * z⁻¹) * (z * z) = x⁻¹ * z := by field_simp
  rwa [h7] at h6

/-- A real positivity computation. -/
theorem pos_mul_of_pos_inv_mul {x y : ℝ} (hx : x ≠ 0) (h : 0 < x⁻¹ * y) : 0 < x * y := by
  have h2 : 0 < (x⁻¹ * y) * (x * x) := mul_pos h (mul_self_pos.mpr hx)
  have h3 : (x⁻¹ * y) * (x * x) = x * y := by field_simp
  rwa [h3] at h2

/-- The positivity condition of `piece` at a real place, as a product positivity. -/
theorem piece_sign_mul_pos (𝔪 : Modulus K) {𝔡 : (Ideal (𝓞 K))⁰} {T : ℝ}
    {u : (𝓞 K)ˣ} {β : K} (hu : piece 𝔪 𝔡 T u β)
    (w : NK.NUV2.HeckeAnalytic.posRealPlace 𝔪) :
    0 < NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((u : (𝓞 K)ˣ) : K)⁻¹)
        * NumberField.InfinitePlace.embedding_of_isReal w.2.2 β := by
  have h := hu.2.2.1 w
  rw [mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal] at h
  exact (sign_iff_mul_pos w.1 w.2.2 _ β
    (by
      rw [map_inv₀]
      exact inv_ne_zero (embedding_unit_ne_zero w.1 w.2.2 u))).mp h

/-! ## The two directions of the cone-character dictionary -/

/-- **Two `piece` conditions on the same element determine the same unit coset.** -/
theorem piece_coset_eq (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (T : ℝ)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {u u' : (𝓞 K)ˣ} {β : K}
    (hu : piece 𝔪 𝔡 T u β)
    (hu' : piece 𝔪 𝔡 T u' β) :
    (QuotientGroup.mk u : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪)
      = QuotientGroup.mk u' := by
  rw [QuotientGroup.eq, NK.NUV2.HeckeAnalytic.congUnit, Subgroup.mem_inf]
  constructor
  · -- the congruence part
    have h1 : β - (((u : (𝓞 K)ˣ) : K))⁻¹
        ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 :=
      NK.NUV2.RouteB.CongCount.mem_magSet_iff 𝔪 𝔡 |>.mpr hu.1
    have h2 : β - (((u' : (𝓞 K)ˣ) : K))⁻¹
        ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 :=
      NK.NUV2.RouteB.CongCount.mem_magSet_iff 𝔪 𝔡 |>.mpr hu'.1
    have hdiff : (β - (((u' : (𝓞 K)ˣ) : K))⁻¹) - (β - (((u : (𝓞 K)ˣ) : K))⁻¹)
        ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 :=
      NK.NUV2.RouteB.CongCount.sub_mem_magSet 𝔪 𝔡 h2 h1
    have hprod : ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K)
        = ((((u : (𝓞 K)ˣ)) : K))⁻¹ * ((((u' : (𝓞 K)ˣ)) : K)) := by
      rw [show ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K)
          = ((((u⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) : K) * ((((u' : (𝓞 K)ˣ)) : 𝓞 K) : K) from by
            push_cast; ring,
        unit_coe_inv u]
    have hkey : ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K) - 1
        = ((β - (((u' : (𝓞 K)ˣ) : K))⁻¹) - (β - (((u : (𝓞 K)ˣ) : K))⁻¹))
          * (((u' : (𝓞 K)ˣ) : K)) := by
      rw [hprod]
      have h0 : ((((u : (𝓞 K)ˣ)) : K)) ≠ 0 := unit_carrier_ne_zero u
      field_simp
      ring
    have hν : ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K) - 1
        ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 := by
      rw [hkey]
      exact NK.NUV2.RouteB.CongCount.smul_mem_magSet 𝔪 𝔡 (u' : 𝓞 K) hdiff
    rw [NK.NUV2.RouteB.CongCount.mem_magSet_iff] at hν
    exact (NK.NUV2.RouteB.CongCount.coe_sub_one_mem_iff 𝔪 𝔡 hcop (u⁻¹ * u')).mp hν
  · -- the positivity part
    rw [NK.NUV2.HeckeAnalytic.posUnits, Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_comap, Units.mem_posSubgroup]
    show (0 : ℝ) < ((NK.NUV2.HeckeAnalytic.unitToReal K w.1 w.2.2 (u⁻¹ * u') : ℝˣ) : ℝ)
    have hmain : ((NK.NUV2.HeckeAnalytic.unitToReal K w.1 w.2.2 (u⁻¹ * u') : ℝˣ) : ℝ)
        = (mixedEmbedding K ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K)).1 ⟨w.1, w.2.2⟩ :=
      ringEquivReal_alg_eq_mixed w.1 w.2.2 _
    rw [hmain, mixedEmbedding_apply_isReal]
    have hprod : ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K)
        = ((((u : (𝓞 K)ˣ)) : K))⁻¹ * ((((u' : (𝓞 K)ˣ)) : K)) := by
      rw [show ((((u⁻¹ * u' : (𝓞 K)ˣ)) : 𝓞 K) : K)
          = ((((u⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) : K) * ((((u' : (𝓞 K)ˣ)) : 𝓞 K) : K) from by
            push_cast; ring,
        unit_coe_inv u]
    rw [hprod, map_mul, map_inv₀]
    have h1 : 0 < (NumberField.InfinitePlace.embedding_of_isReal w.2.2 ((((u : (𝓞 K)ˣ)) : K)))⁻¹
        * NumberField.InfinitePlace.embedding_of_isReal w.2.2 β := by
      have h := piece_sign_mul_pos 𝔪 hu w
      rwa [show NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((u : (𝓞 K)ˣ) : K)⁻¹)
          = ((NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((u : (𝓞 K)ˣ) : K))))⁻¹ from by
            rw [map_inv₀]] at h
    have h2 : 0 < (NumberField.InfinitePlace.embedding_of_isReal w.2.2 ((((u' : (𝓞 K)ˣ)) : K)))⁻¹
        * NumberField.InfinitePlace.embedding_of_isReal w.2.2 β := by
      have h := piece_sign_mul_pos 𝔪 hu' w
      rwa [show NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((u' : (𝓞 K)ˣ) : K)⁻¹)
          = ((NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((u' : (𝓞 K)ˣ) : K))))⁻¹ from by
            rw [map_inv₀]] at h
    refine pos_inv_mul_of_pos_inv_mul
      (y := NumberField.InfinitePlace.embedding_of_isReal w.2.2 β) ?_ ?_ h1 h2
    · intro h0
      rw [h0, mul_zero] at h1
      exact lt_irrefl 0 h1
    · exact embedding_unit_ne_zero w.1 w.2.2 u'




variable {K : Type} [Field K] [NumberField K]

/-- **A `piece` element generates an ideal of the counted ray class.** -/
theorem coneCarrier_of_piece (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) {u : (𝓞 K)ˣ} {β : K}
    (hu : piece 𝔪 𝔡
      (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ)) u β) :
    β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡 X := by
  have hβmem : β ∈ (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set K) := by
    have h1 : β - (((u : (𝓞 K)ˣ) : K))⁻¹ ∈ (((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) := hu.1
    have h2 : β - (((u : (𝓞 K)ˣ) : K))⁻¹
        ∈ (((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :=
      NK.NUV2.RouteB.CongCount.magIdeal_le_inv_base 𝔪 𝔡 h1
    have h3 : (((u : (𝓞 K)ˣ) : K))⁻¹ ∈ (((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :=
      (NK.NUV2.RouteB.CongCount.one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K))
        (NK.NUV2.RouteB.CongCount.baseIdeal_ne_zero 𝔡))
        (inv_unit_mem_one u)
    have h4 : β ∈ (((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      have := Submodule.add_mem ((((((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) h2 h3
      simpa using this
    simpa using h4
  refine ⟨hβmem, ?_, hu.2.1, ⟨u, ?_, ?_⟩, ?_⟩
  · intro h0
    have hnorm : mixedEmbedding.norm (mixedEmbedding K β) = 0 := by rw [h0]; simp
    exact absurd hnorm (ne_of_gt (fundamentalCone.norm_pos_of_mem hu.2.1))
  · -- the congruence part of `IsCongElem`
    intro q hq
    have hval := (sub_inv_mem_magIdeal_iff 𝔪 𝔡 hcop u hβmem).mp hu.1
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hval q hq
  · -- the positivity part of `IsCongElem`
    intro w hw hwpos
    have h := piece_sign_mul_pos 𝔪 hu ⟨w, hwpos, hw⟩
    have hcoe : (algebraMap K w.Completion ((((u : (𝓞 K)ˣ)) : K) * β) : w.Completion)
        = ((((((u : (𝓞 K)ˣ)) : K) * β : K)) : w.Completion) := rfl
    rw [hcoe, ringEquivReal_alg_eq_mixed w hw,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    have hunit : (NumberField.InfinitePlace.embedding_of_isReal hw ((((u : (𝓞 K)ˣ)) : K)))
        * (NumberField.InfinitePlace.embedding_of_isReal hw ((((u : (𝓞 K)ˣ)) : K)⁻¹)) = 1 := by
      rw [← map_mul]
      rw [mul_inv_cancel₀ (unit_carrier_ne_zero u)]
      exact map_one _
    have hCeq : (NumberField.InfinitePlace.embedding_of_isReal hw ((((u : (𝓞 K)ˣ)) : K)⁻¹))
        = ((NumberField.InfinitePlace.embedding_of_isReal hw ((((u : (𝓞 K)ˣ)) : K))))⁻¹ :=
      eq_inv_of_mul_eq_one_right hunit
    have hAne : (NumberField.InfinitePlace.embedding_of_isReal hw ((((u : (𝓞 K)ˣ)) : K))) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hunit
      exact one_ne_zero hunit.symm
    rw [hCeq] at h
    have hgoal := pos_mul_of_pos_inv_mul hAne h
    rwa [← map_mul] at hgoal
  · -- the norm bound
    have hnorm : mixedEmbedding.norm (mixedEmbedding K β)
        ≤ X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := hu.2.2.2
    have hpos : (0 : ℝ) < (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h0 =>
        NK.NUV2.RouteB.CongCount.baseIdeal_ne_zero 𝔡 (Ideal.absNorm_eq_zero_iff.mp h0))
    calc mixedEmbedding.norm (mixedEmbedding K β) * (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ)
        ≤ (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ))
          * (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := mul_le_mul_of_nonneg_right hnorm hpos.le
      _ = X := div_mul_cancel₀ X hpos.ne'


/-- **A cone generator admits a `piece` presentation at the representative of the coset of a
witnessing unit.** -/
theorem piece_of_coneCarrier (𝔪 : NK.NUV2.RouteB.Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) {β : K} (hβ : β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡 X) :
    piece 𝔪 𝔡
      (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ))
      (Quotient.out (QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪)
        (Classical.choose hβ.2.2.2.1))) β := by
  classical
  set hv : (𝓞 K)ˣ := Classical.choose hβ.2.2.2.1 with hvdef
  have hcong : NK.NUV2.RouteB.IsCongElem K 𝔪 (((hv : (𝓞 K)ˣ) : K) * β) :=
    Classical.choose_spec hβ.2.2.2.1
  set u : (𝓞 K)ˣ := Quotient.out (QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪) hv)
    with hudef
  set c : (𝓞 K)ˣ := u⁻¹ * hv with hcdef
  have hβmem : β ∈ (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set K) := by
    simpa [FractionalIdeal.coe_mk0] using hβ.1
  have hc : c ∈ NK.NUV2.HeckeAnalytic.congUnit 𝔪 := by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' (QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪) hv)
  obtain ⟨hcunit, hcpos⟩ := Subgroup.mem_inf.mp hc
  -- (1) the lattice membership
  have hcong' : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
      (q.valuation K) ((((hv : (𝓞 K)ˣ)) : K) * β - 1) ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
    intro q hq
    have h := hcong.1 q hq
    rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q
      ((((hv : (𝓞 K)ˣ)) : K) * β - 1)] at h
  have h1 : β - (((hv : (𝓞 K)ˣ)) : K)⁻¹
      ∈ ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) :=
    (sub_inv_mem_magIdeal_iff 𝔪 𝔡 hcop hv hβmem).mpr hcong'
  have hz : (((c : 𝓞 K) : K) - 1)
      ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 :=
    (NK.NUV2.RouteB.CongCount.coe_sub_one_mem_iff 𝔪 𝔡 hcop c).mpr hcunit
  have h2 : (((hv : (𝓞 K)ˣ)) : K)⁻¹ - (((u : (𝓞 K)ˣ)) : K)⁻¹
      ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 := by
    have hq : (QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪) u)
        = QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪) hv :=
      QuotientGroup.out_eq' _
    have h1 : u⁻¹ * hv ∈ NK.NUV2.HeckeAnalytic.congUnit 𝔪 := (QuotientGroup.eq).mp hq
    have h1' : u⁻¹ * hv ∈ NK.NUV2.RouteB.unitCongOne 𝔪.ideal := by
      have h := h1
      rw [NK.NUV2.HeckeAnalytic.congUnit] at h
      exact (Subgroup.mem_inf.mp h).1
    have hmem : NK.NUV2.RouteB.CongCount.unitInvK u - NK.NUV2.RouteB.CongCount.unitInvK hv
        ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡 :=
      (NK.NUV2.RouteB.CongCount.inv_sub_inv_mem_iff 𝔪 𝔡 hcop u hv).mpr
        ((QuotientGroup.eq).mpr h1')
    have hbridge : (((hv : (𝓞 K)ˣ)) : K)⁻¹ - (((u : (𝓞 K)ˣ)) : K)⁻¹
        = -(NK.NUV2.RouteB.CongCount.unitInvK u - NK.NUV2.RouteB.CongCount.unitInvK hv) := by
      rw [NK.NUV2.RouteB.CongCount.unitInvK_def, NK.NUV2.RouteB.CongCount.unitInvK_def,
        unit_coe_inv u, unit_coe_inv hv]
      ring
    rw [hbridge]
    exact NK.NUV2.RouteB.CongCount.neg_mem_magSet 𝔪 𝔡 hmem
  have hlat : β - (((u : (𝓞 K)ˣ)) : K)⁻¹
      ∈ ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
    have hsum : (β - (((hv : (𝓞 K)ˣ)) : K)⁻¹)
        + ((((hv : (𝓞 K)ˣ)) : K)⁻¹ - (((u : (𝓞 K)ˣ)) : K)⁻¹)
        = β - (((u : (𝓞 K)ˣ)) : K)⁻¹ := by ring
    rw [← hsum]
    exact Submodule.add_mem ((((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) : Submodule (𝓞 K) K) h1
      (NK.NUV2.RouteB.CongCount.mem_magSet_iff 𝔪 𝔡 |>.mp h2)
  -- the two unit identities used in the sign conditions
  have hmul : ((u : (𝓞 K)ˣ) * c : (𝓞 K)ˣ) = hv := by
    rw [hcdef, hudef]
    group
  have huval : (((u : (𝓞 K)ˣ)) : K) * (((c : (𝓞 K)ˣ)) : K) = (((hv : (𝓞 K)ˣ)) : K) := by
    rw [← map_mul, ← Units.val_mul, hmul]
  have huinv : (((u : (𝓞 K)ˣ)) : K)⁻¹
      = (((c : (𝓞 K)ˣ)) : K) * ((((hv : (𝓞 K)ˣ)) : K))⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, huval, mul_inv_cancel₀ (unit_carrier_ne_zero hv)]
  refine ⟨hlat, hβ.2.2.1, ?_, ?_⟩
  · -- the sign conditions
    intro w
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
      NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    have hposv : 0 < (NumberField.InfinitePlace.embedding_of_isReal w.2.2
          (((hv : (𝓞 K)ˣ) : K))) * (NumberField.InfinitePlace.embedding_of_isReal w.2.2 β) := by
      have h := hcong.2 w.1 w.2.2 w.2.1
      have hcoe : (algebraMap K w.1.Completion ((((hv : (𝓞 K)ˣ)) : K) * β) : w.1.Completion)
          = ((((((hv : (𝓞 K)ˣ)) : K) * β : K)) : w.1.Completion) := rfl
      rw [hcoe, ringEquivReal_alg_eq_mixed w.1 w.2.2,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, map_mul] at h
      exact h
    have hcpos' : 0 < NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((c : 𝓞 K) : K)) :=
      (mem_posUnits_iff 𝔪 c).mp hcpos w
    have hvne : (NumberField.InfinitePlace.embedding_of_isReal w.2.2
        (((hv : (𝓞 K)ˣ) : K))) ≠ 0 := embedding_unit_ne_zero w.1 w.2.2 hv
    have hEY : (NumberField.InfinitePlace.embedding_of_isReal w.2.2
          (((u : (𝓞 K)ˣ) : K)⁻¹))
        = NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((c : 𝓞 K) : K))
          * (NumberField.InfinitePlace.embedding_of_isReal w.2.2 (((hv : (𝓞 K)ˣ) : K)))⁻¹ := by
      rw [huinv, map_mul, map_inv₀]
    rw [hEY]
    have hcase := (sign_iff_mul_pos w.1 w.2.2 (((hv : (𝓞 K)ˣ) : K)) β hvne).mpr hposv
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, h2⟩
      exact mul_pos hcpos' (inv_pos.mpr h1)
    · right
      refine ⟨?_, h2⟩
      exact mul_neg_of_pos_of_neg hcpos' (inv_lt_zero.mpr h1)
  · -- the norm bound
    have hpos : (0 : ℝ) < (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h0 =>
        NK.NUV2.RouteB.CongCount.baseIdeal_ne_zero 𝔡 (Ideal.absNorm_eq_zero_iff.mp h0))
    rw [le_div_iff₀ hpos]
    exact hβ.2.2.2.2


/-! ## The gluing -/

/-- The pieces attached to the representatives of the unit cosets are the generators in the
fundamental cone. -/
theorem natCard_pieces_eq_natCard_coneCarrier (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (X : ℝ) :
    Nat.card (Σ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
        {β : K // piece 𝔪 𝔡 (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ))
          (Quotient.out q) β})
      = Nat.card {β : K // β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡 X} := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : (Σ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
        {β : K // piece 𝔪 𝔡 (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ))
          (Quotient.out q) β}) =>
      (⟨p.2.1, coneCarrier_of_piece 𝔪 𝔡 hcop X p.2.2⟩ :
        {β : K // β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡 X})) ?_)
  constructor
  · -- injectivity
    rintro ⟨q, β, hβ⟩ ⟨q', β', hβ'⟩ heq
    have hval : β = β' := congrArg (fun y => y.1) heq
    subst hval
    have hqq : q = q' := by
      have h := piece_coset_eq 𝔪 𝔡 (X / (Ideal.absNorm (𝔡 : Ideal (𝓞 K)) : ℝ)) hcop hβ hβ'
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    subst hqq
    rfl
  · -- surjectivity
    rintro ⟨β, hβ⟩
    exact ⟨⟨QuotientGroup.mk (s := NK.NUV2.HeckeAnalytic.congUnit 𝔪)
      (Classical.choose hβ.2.2.2.1),
      ⟨β, piece_of_coneCarrier 𝔪 𝔡 hcop X hβ⟩⟩, rfl⟩

/-! ## The theorem -/

theorem rayClassCnt_eq_coset_sum (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    [Fintype ((NumberField.RingOfIntegers K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪)]
    (𝔡 : Ideal (NumberField.RingOfIntegers K)) (h𝔡 : 𝔡 ≠ 0)
    (hcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ 𝔡)
    (X : ℝ) :
    (NumberField.Units.torsionOrder K : ℝ) *
        (NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X : ℝ)
      = ∑ q : (NumberField.RingOfIntegers K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
          (NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 ⟨𝔡, mem_nonZeroDivisors_of_ne_zero h𝔡⟩
            (((Quotient.out q : (NumberField.RingOfIntegers K)ˣ) : K)⁻¹)
            (X / (Ideal.absNorm 𝔡 : ℝ)) : ℝ) := by
  classical
  set 𝔡0 : (Ideal (𝓞 K))⁰ := ⟨𝔡, mem_nonZeroDivisors_of_ne_zero h𝔡⟩ with h𝔡0
  set T : ℝ := X / (Ideal.absNorm 𝔡 : ℝ) with hT
  -- step 1: each summand is the cardinality of the corresponding piece
  have hstep1 : ∀ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
      NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡0
        (((Quotient.out q : (𝓞 K)ˣ) : K)⁻¹) T
        = Nat.card {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β} := by
    intro q
    exact (card_piece_eq_cosetConeCnt 𝔪 𝔡0 T (Quotient.out q)).symm
  -- step 2: finiteness of the pieces
  have hfin : ∀ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
      Finite {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β} := by
    intro q
    have hF : ({β : K | β - (((Quotient.out q : (𝓞 K)ˣ) : 𝓞 K) : K)⁻¹
          ∈ NK.NUV2.RouteB.CongCount.magSet 𝔪 𝔡0 ∧
        mixedEmbedding K β ∈ fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding K β) ≤ T}).Finite :=
      NK.NUV2.RouteB.CongCount.finite_cosetFiber 𝔪 𝔡0
        (((Quotient.out q : (𝓞 K)ˣ) : 𝓞 K) : K)⁻¹ T
    exact (hF.subset (fun β hβ =>
      ⟨(NK.NUV2.RouteB.CongCount.mem_magSet_iff 𝔪 𝔡0).mpr hβ.1, hβ.2.1, hβ.2.2.2⟩)).to_subtype
  -- step 3: the sum is the cardinality of the disjoint union, which is the cone carrier
  have hstep3 : (∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
      (Nat.card {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β} : ℝ))
      = (Nat.card {β : K // β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡0 X} : ℝ) := by
    have h1 : (Nat.card (Σ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
        {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β}) : ℝ)
        = ∑ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
            (Nat.card {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β} : ℝ) := by
      rw [Nat.card_sigma]
      push_cast
      rfl
    have h2 : Nat.card (Σ q : (𝓞 K)ˣ ⧸ NK.NUV2.HeckeAnalytic.congUnit 𝔪,
        {β : K // piece 𝔪 𝔡0 T (Quotient.out q) β})
        = Nat.card {β : K // β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡0 X} :=
      natCard_pieces_eq_natCard_coneCarrier 𝔪 𝔡0 hcop X
    rw [← h1, h2]
  -- step 4: the cone carrier is `torsionOrder K` times the ray class count
  have hstep4 : (Nat.card {β : K // β ∈ NK.NUV2.RouteB.CongCount.coneCarrier 𝔪 𝔡0 X} : ℝ)
      = (NumberField.Units.torsionOrder K : ℝ) * (NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X : ℝ) := by
    rw [NK.NUV2.RouteB.CongCount.natCard_coneCarrier_eq_torsion_mul_idealCarrier 𝔪 𝔡0 hcop X]
    have : Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ∈ NK.NUV2.RouteB.CongCount.idealCarrier 𝔪 𝔡0 X}
        = NK.NUV2.RouteB.rayClassCnt K 𝔪 𝔡 X := rfl
    rw [this]
    push_cast
    ring
  -- assemble
  rw [← hstep4, ← hstep3]
  exact Finset.sum_congr rfl fun q _ => by rw [hstep1 q]

end NK.NUV2.RouteB.HeckeTheta
