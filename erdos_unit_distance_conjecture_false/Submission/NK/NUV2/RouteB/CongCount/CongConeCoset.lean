import Mathlib
import Submission.NK.NUV2.RouteB.CongCount.CongConeSetup
import Submission.NK.NUV2.RouteB.CongCount.finite_cosetConeSet

/-!
# The coset decomposition of the lattice of the ray class

For a modulus `𝔪`, a nonzero integral ideal `𝔡` coprime to the support of `𝔪` and the lattice
`M = 𝔪.ideal · 𝔡⁻¹`, this file proves that the union of the cosets `u⁻¹ + M` over the units
`u : (𝓞 K)ˣ` is the *disjoint* union of the cosets `(Quotient.out v)⁻¹ + M` indexed by the finite
quotient `(𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal`, and that each such coset is in bijection with the
corresponding lattice coset of the mixed space (so that the `Nat.card` of the set of its points in
the fundamental cone of norm `≤ Y` is `cosetConeCountF`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.CongCount

open NK.NUV2.RouteB

variable {K : Type} [Field K] [NumberField K]

/-- The lattice `𝔪.ideal · 𝔡⁻¹` as a (nonzero) fractional ideal. -/
def magFrac (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) : FractionalIdeal (𝓞 K)⁰ K :=
  ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

/-- The lattice `𝔪.ideal · 𝔡⁻¹`, as a set of elements of `K`. -/
def magSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) : Set K := magFrac 𝔪 𝔡

@[simp]
theorem mem_magSet_iff (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) {x : K} :
    x ∈ magSet 𝔪 𝔡 ↔
      x ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
  Iff.rfl

/-- The union of the lattice cosets `u⁻¹ + (𝔪.ideal · 𝔡⁻¹)` over the units `u : (𝓞 K)ˣ`. -/
def cosetUnion (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) : Set K :=
  {β : K | ∃ u : (𝓞 K)ˣ, β - unitInvK u ∈ magSet 𝔪 𝔡}

/-- The fibre of the coset decomposition over a unit class `v`. -/
abbrev cosetFiber (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (P : K → Prop)
    (v : (𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal) : Type _ :=
  {β : K // β - unitInvK (Quotient.out v) ∈ magSet 𝔪 𝔡 ∧ P β}

/-! ## Elementary facts about the lattice -/

theorem add_mem_magSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) {x y : K}
    (hx : x ∈ magSet 𝔪 𝔡) (hy : y ∈ magSet 𝔪 𝔡) : x + y ∈ magSet 𝔪 𝔡 :=
  Submodule.add_mem (magFrac 𝔪 𝔡 : Submodule (𝓞 K) K) hx hy

theorem neg_mem_magSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) {x : K}
    (hx : x ∈ magSet 𝔪 𝔡) : -x ∈ magSet 𝔪 𝔡 :=
  Submodule.neg_mem (magFrac 𝔪 𝔡 : Submodule (𝓞 K) K) hx

theorem sub_mem_magSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) {x y : K}
    (hx : x ∈ magSet 𝔪 𝔡) (hy : y ∈ magSet 𝔪 𝔡) : x - y ∈ magSet 𝔪 𝔡 :=
  Submodule.sub_mem (magFrac 𝔪 𝔡 : Submodule (𝓞 K) K) hx hy

theorem smul_mem_magSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (a : 𝓞 K) {x : K}
    (hx : x ∈ magSet 𝔪 𝔡) : x * ((a : 𝓞 K) : K) ∈ magSet 𝔪 𝔡 := by
  have h := Submodule.smul_mem (magFrac 𝔪 𝔡 : Submodule (𝓞 K) K) a hx
  rwa [Algebra.smul_def, mul_comm] at h

/-- Multiplication by a unit of `𝓞 K` preserves the lattice. -/
theorem unit_mul_mem_magSet_iff (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (u : (𝓞 K)ˣ) {y : K} :
    ((u : 𝓞 K) : K) * y ∈ magSet 𝔪 𝔡 ↔ y ∈ magSet 𝔪 𝔡 :=
  unit_mul_mem_iff (magFrac 𝔪 𝔡) u

/-! ## The coset decomposition -/

/-- Multiplication of the difference of two inverse units by a unit. -/
theorem unit_mul_unitInvK_sub (u u' : (𝓞 K)ˣ) :
    ((u' : 𝓞 K) : K) * (unitInvK u - unitInvK u')
      = (((u' * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) - 1 := by
  have hid : ((u' : 𝓞 K) : K) * (((u'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
    simp only [RingOfIntegers.coe_eq_algebraMap]
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [unitInvK_def, unitInvK_def, mul_sub, hid]
  simp only [RingOfIntegers.coe_eq_algebraMap]
  rw [← map_mul, Units.val_mul]

/-- An algebraic integer lies in the lattice iff its class is a congruence unit. -/
theorem coe_sub_one_mem_iff (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (v : (𝓞 K)ˣ) :
    ((((v : 𝓞 K) : K) - 1) ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K)) ↔ v ∈ unitCongOne 𝔪.ideal := by
  rw [show (((v : 𝓞 K) : K) - 1) = ((((v : 𝓞 K) - 1 : 𝓞 K)) : K) by push_cast; ring]
  rw [mem_magIdeal_iff_mem_ideal 𝔪 𝔡 hcop ((v : 𝓞 K) - 1), mem_unitCongOne_iff]

/-- **The cosets of the unit group and the lattice cosets agree.**  For units `u`, `u'` of `𝓞 K`,
the cosets `u⁻¹ + M` and `u'⁻¹ + M` coincide if and only if `u` and `u'` have the same class modulo
the congruence units `unitCongOne 𝔪.ideal`. -/
theorem inv_sub_inv_mem_iff (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (u u' : (𝓞 K)ˣ) :
    unitInvK u - unitInvK u' ∈ magSet 𝔪 𝔡 ↔
      (QuotientGroup.mk (s := unitCongOne 𝔪.ideal) u
        = QuotientGroup.mk (s := unitCongOne 𝔪.ideal) u') := by
  constructor
  · intro h
    have h1 : ((((u' * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) - 1) ∈ magSet 𝔪 𝔡 := by
      rw [← unit_mul_unitInvK_sub u u']
      exact (unit_mul_mem_magSet_iff 𝔪 𝔡 u').mpr h
    have h2 : (u' * u⁻¹ : (𝓞 K)ˣ) ∈ unitCongOne 𝔪.ideal :=
      (coe_sub_one_mem_iff 𝔪 𝔡 hcop _).mp (by rwa [mem_magSet_iff] at h1)
    rw [QuotientGroup.eq]
    rw [show (u⁻¹ * u' : (𝓞 K)ˣ) = u' * u⁻¹ from mul_comm _ _]
    exact h2
  · intro h
    rw [QuotientGroup.eq] at h
    have h2 : (u' * u⁻¹ : (𝓞 K)ˣ) ∈ unitCongOne 𝔪.ideal := by
      rw [← mul_comm u⁻¹ u']; exact h
    have h1 : ((((u' * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) - 1) ∈ magSet 𝔪 𝔡 := by
      rw [mem_magSet_iff]
      exact (coe_sub_one_mem_iff 𝔪 𝔡 hcop _).mpr h2
    rw [← unit_mul_unitInvK_sub u u'] at h1
    exact (unit_mul_mem_magSet_iff 𝔪 𝔡 u').mp h1

/-- **The coset decomposition.**  The union of the lattice cosets `u⁻¹ + M` over all units is the
disjoint union of the cosets indexed by the unit classes modulo `unitCongOne 𝔪.ideal`. -/
def equiv_cosetUnion_sigma (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (P : K → Prop) :
    {β : K // β ∈ cosetUnion 𝔪 𝔡 ∧ P β} ≃ Σ v, cosetFiber 𝔪 𝔡 P v := by
  classical
  refine Equiv.ofBijective (fun β => ?_) ⟨?_, ?_⟩
  · have hex : ∃ u : (𝓞 K)ˣ, β.1 - unitInvK u ∈ magSet 𝔪 𝔡 := β.2.1
    refine ⟨QuotientGroup.mk (s := unitCongOne 𝔪.ideal) (Classical.choose hex),
      ⟨β.1, ?_, β.2.2⟩⟩
    have hch : β.1 - unitInvK (Classical.choose hex) ∈ magSet 𝔪 𝔡 := Classical.choose_spec hex
    have hout : (QuotientGroup.mk (s := unitCongOne 𝔪.ideal) (Quotient.out (QuotientGroup.mk
        (s := unitCongOne 𝔪.ideal) (Classical.choose hex))))
        = QuotientGroup.mk (s := unitCongOne 𝔪.ideal) (Classical.choose hex) :=
      QuotientGroup.out_eq' _
    have h1 : unitInvK (Classical.choose hex)
        - unitInvK (Quotient.out (QuotientGroup.mk (s := unitCongOne 𝔪.ideal)
            (Classical.choose hex))) ∈ magSet 𝔪 𝔡 :=
      (inv_sub_inv_mem_iff 𝔪 𝔡 hcop _ _).mpr hout.symm
    have hsum : β.1 - unitInvK (Quotient.out (QuotientGroup.mk (s := unitCongOne 𝔪.ideal)
        (Classical.choose hex)))
        = (β.1 - unitInvK (Classical.choose hex))
          + (unitInvK (Classical.choose hex)
            - unitInvK (Quotient.out (QuotientGroup.mk (s := unitCongOne 𝔪.ideal)
                (Classical.choose hex)))) := by ring
    rw [hsum]
    exact add_mem_magSet 𝔪 𝔡 hch h1
  · intro β γ h
    exact Subtype.ext (congrArg (fun y => y.2.1) h)
  · rintro ⟨v, γ, hγmem, hP⟩
    have hex : ∃ u : (𝓞 K)ˣ, γ - unitInvK u ∈ magSet 𝔪 𝔡 := ⟨Quotient.out v, hγmem⟩
    refine ⟨⟨γ, hex, hP⟩, ?_⟩
    have hq : (QuotientGroup.mk (s := unitCongOne 𝔪.ideal) (Classical.choose hex)
        : (𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal) = v := by
      have hdiff : unitInvK (Quotient.out v) - unitInvK (Classical.choose hex) ∈ magSet 𝔪 𝔡 := by
        have heq : unitInvK (Quotient.out v) - unitInvK (Classical.choose hex)
            = (γ - unitInvK (Classical.choose hex)) - (γ - unitInvK (Quotient.out v)) := by ring
        rw [heq]
        exact sub_mem_magSet 𝔪 𝔡 (Classical.choose_spec hex) hγmem
      have h := (inv_sub_inv_mem_iff 𝔪 𝔡 hcop (Quotient.out v) (Classical.choose hex)).mp hdiff
      rw [QuotientGroup.out_eq'] at h
      exact h.symm
    refine Sigma.ext_iff.mpr ⟨hq, ?_⟩
    cases hq
    exact heq_iff_eq.mpr (Subtype.ext rfl)

/-- **The coset decomposition as an identity of natural numbers.** -/
theorem natCard_cosetUnion_eq_sum (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (P : K → Prop)
    (hfin : ∀ v : (𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal, Finite (cosetFiber 𝔪 𝔡 P v)) :
    Nat.card {β : K // β ∈ cosetUnion 𝔪 𝔡 ∧ P β}
      = ∑ v : (𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal, Nat.card (cosetFiber 𝔪 𝔡 P v) := by
  classical
  haveI : ∀ v : (𝓞 K)ˣ ⧸ unitCongOne 𝔪.ideal, Finite (cosetFiber 𝔪 𝔡 P v) := hfin
  rw [Nat.card_congr (equiv_cosetUnion_sigma 𝔪 𝔡 hcop P), Nat.card_sigma]

/-! ## The lattice cosets of the mixed space -/

/-- **A lattice coset of `K` is a lattice coset of the mixed space.** -/
def equiv_fiber_mixedSpace (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (c : K) (Y : ℝ) :
    {β : K // β - c ∈ magSet 𝔪 𝔡 ∧
        mixedEmbedding K β ∈ fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding K β) ≤ Y} ≃
      {a : mixedSpace K // a - mixedEmbedding K c ∈
          (idealLattice K (magIdeal 𝔪 𝔡) : Set (mixedSpace K)) ∧
        a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ Y} := by
  refine Equiv.ofBijective (fun β => ?_) ⟨?_, ?_⟩
  · refine ⟨mixedEmbedding K β.1, ?_, β.2.2.1, β.2.2.2⟩
    rw [← map_sub]
    exact (mem_idealLattice K (magIdeal 𝔪 𝔡)).mpr ⟨β.1 - c, β.2.1, rfl⟩
  · intro β γ h
    refine Subtype.ext ?_
    exact mixedEmbedding_injective K (congrArg (fun y => y.1) h)
  · rintro ⟨a, ha, hacon, hanorm⟩
    obtain ⟨y, hy, hys⟩ := (mem_idealLattice K (magIdeal 𝔪 𝔡)).mp ha
    have hEq : mixedEmbedding K (c + y) = a := by
      rw [map_add, hys]; abel
    refine ⟨⟨c + y, ?_, ?_, ?_⟩, ?_⟩
    · show (c + y) - c ∈ magSet 𝔪 𝔡
      rw [add_sub_cancel_left]
      exact hy
    · show mixedEmbedding K (c + y) ∈ fundamentalCone K
      rw [hEq]; exact hacon
    · show mixedEmbedding.norm (mixedEmbedding K (c + y)) ≤ Y
      rw [hEq]; exact hanorm
    · apply Subtype.ext
      show mixedEmbedding K (c + y) = a
      exact hEq

/-- **A lattice coset of `K` is finite in the fundamental cone of bounded norm.** -/
theorem finite_cosetFiber (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (c : K) (Y : ℝ) :
    {β : K | β - c ∈ magSet 𝔪 𝔡 ∧ mixedEmbedding K β ∈ fundamentalCone K ∧
      mixedEmbedding.norm (mixedEmbedding K β) ≤ Y}.Finite := by
  classical
  set L : Submodule ℤ (mixedSpace K) := idealLattice K (magIdeal 𝔪 𝔡) with hL
  haveI hdisc : DiscreteTopology L := by rw [hL]; infer_instance
  have hbd : Bornology.IsBounded {x : mixedSpace K | x ∈ fundamentalCone K ∧
      mixedEmbedding.norm x ≤ Y} := isBounded_fundamentalCone_norm_le K Y
  have hbd' : Bornology.IsBounded {y : mixedSpace K | y + mixedEmbedding K c ∈
      {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ Y}} := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbd
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖mixedEmbedding K c‖, fun y hy => ?_⟩
    have h1 : ‖y + mixedEmbedding K c‖ ≤ C := hC _ hy
    have h2 : ‖y‖ = ‖(y + mixedEmbedding K c) - mixedEmbedding K c‖ := by
      rw [add_sub_cancel_right]
    rw [h2]
    exact le_trans (norm_sub_le _ _) (by linarith [norm_nonneg (mixedEmbedding K c)])
  have hfin := NK.NUV2.Geom.coset_finite_setOf_coe_mem L hbd'
  have hfin' : ((Subtype.val '' {l : L | ((l : L) : mixedSpace K) ∈
      {y : mixedSpace K | y + mixedEmbedding K c ∈
        {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ Y}}}) :
      Set (mixedSpace K)).Finite :=
    hfin.image Subtype.val
  refine Set.Finite.of_finite_image (f := fun β : K => mixedEmbedding K β - mixedEmbedding K c)
    ?_ ?_
  · refine hfin'.subset ?_
    rintro y ⟨β, hβ, rfl⟩
    refine ⟨⟨mixedEmbedding K β - mixedEmbedding K c, ?_⟩, ?_, rfl⟩
    · rw [mem_idealLattice]
      exact ⟨β - c, hβ.1, map_sub _ _ _⟩
    · show (mixedEmbedding K β - mixedEmbedding K c) + mixedEmbedding K c
          ∈ fundamentalCone K ∧ mixedEmbedding.norm _ ≤ Y
      rw [sub_add_cancel]
      exact ⟨hβ.2.1, hβ.2.2⟩
  · intro β₁ _ β₂ _ heq
    refine mixedEmbedding_injective K ?_
    have h := congrArg (fun z => z + mixedEmbedding K c) heq
    simpa using h

end NK.NUV2.RouteB.CongCount
