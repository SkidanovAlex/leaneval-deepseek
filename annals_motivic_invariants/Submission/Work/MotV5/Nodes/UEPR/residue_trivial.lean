import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.algebraMap_ofField_range_le
import Submission.Work.MotV5.Nodes.UEPR.integralClosure_le_valuationSubring
import Submission.Work.MotV5.Nodes.UEPR.lt_one_iff
import Submission.Work.MotV5.Nodes.UEPR.inertiaDeg_one_sub_mem
import Submission.Work.MotV5.Nodes.UEPR.mem_prime_iff_valuation_lt_one
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.MotV5.Nodes.UEPR

/-
**Trivial inertia degree forces a trivial residue extension.**  In the setting of the bridge
(`V = w.valuationSubring =` the localization `Vloc` of `B = integralClosure A Ω` at `P`, with
`A = v.valuationSubring`), if the inertia degree of `P` over `m_A` is `1`, then every element of the
valuation ring `V` of `w` is congruent modulo its maximal ideal to an element of the base valuation
ring `A` — i.e. the residue field of `w` is that of `v`.

Proof route:
1. `P` is maximal (`Ideal.IsMaximal.of_liesOver_isMaximal`, `Mathlib/RingTheory/Ideal/GoingUp.lean`
   line 428, for the integral extension `↥A ⊆ ↥B`), so `Ideal.inertiaDeg_eq_of_isMaximal` gives
   `P.inertiaDeg ↥A = Module.finrank (↥A ⧸ m_A) (↥B ⧸ P)`, hence this finrank is `1` by the
   hypothesis, hence the structure map `↥A ⧸ m_A →+* ↥B ⧸ P` is surjective (use
   `Module.Free.bijective_algebraMap_of_finrank_eq_one` or
   `Algebra.finrank_eq_one_iff_bijective_algebraMap`).
2. Since `P ⊆ m_w` (the hypothesis `hbridge` identifies `Vloc`, whose maximal ideal is `P·Vloc`,
   with `V` and `m_w`), the inclusion `↥B → ↥V` induces a ring hom `↥B ⧸ P →+* ↥V ⧸ m_w`, and the
   composite `↥A ⧸ m_A →+* ↥B ⧸ P →+* ↥V ⧸ m_w` is the natural map (in particular surjective).
3. Given `y : Ω` with `w y ≤ 1`, i.e. `y ∈ V` (`Valuation.mem_valuationSubring_iff`), the residue
   class of `y` in `↥V ⧸ m_w` is the image of the class of some `x : ↥A`; then
   `w (y - algebraMap F Ω x) < 1` (`ValuationSubring.valuation_lt_one_iff`) and `v x ≤ 1`.

Related proved material: `Submission/Work/ClassA/Place/exists_int_sub_mem_p.lean` proves the
`ℤ`-adic version of this statement and is a good model.

The argument below is the "fraction" form of the route: an element `y ∈ V = B_P` is written as
`b / s` with `b ∈ B`, `s ∉ P`; the approximations `xb`, `xs ∈ A` of `b` and `s` modulo `P` are
supplied by `inertiaDeg_one_sub_mem`, `xs` is then a unit of `A`, and the element
`x = xb * xs⁻¹ ∈ A ⊆ F` is the required representative.  The key input `P = m_w ∩ B` is
`mem_prime_iff_valuation_lt_one`.
-/
theorem residue_trivial {F Ω Γ : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω] (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : v.IsNontrivial) [LinearOrderedCommGroupWithZero Γ] (w : Valuation Ω Γ) (hsub : ∀ x : F, w (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1) (P : Ideal ↥(integralClosure ↥(v.valuationSubring) Ω)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ↥(v.valuationSubring))] (hP : P.primeCompl ≤ nonZeroDivisors ↥(integralClosure ↥(v.valuationSubring) Ω)) [IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω] (hbridge : w.valuationSubring.toSubring = (Localization.subalgebra.ofField Ω P.primeCompl hP).toSubring) (hf : P.inertiaDeg ↥(v.valuationSubring) = 1) : ∀ y : Ω, w y ≤ 1 → ∃ x : F, v x ≤ 1 ∧ w (y - algebraMap F Ω x) < 1 := by
  classical
  intro y hy
  haveI hv' : v.IsNontrivial := hv
  haveI hIntB : Algebra.IsIntegral ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    ⟨fun x => IsIntegralClosure.isIntegral ↥(v.valuationSubring) Ω x⟩
  have hBW : (integralClosure ↥(v.valuationSubring) Ω).toSubring ≤
      w.valuationSubring.toSubring := integralClosure_le_valuationSubring v w hsub
  have hiff := mem_prime_iff_valuation_lt_one w P hP hbridge
  -- every element of `B` lies in `V` and has valuation `≤ 1`
  have hB_le : ∀ z : ↥(integralClosure ↥(v.valuationSubring) Ω),
      w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω z) ≤ 1 := fun z =>
    (Valuation.mem_valuationSubring_iff w _).mp
      ((ValuationSubring.mem_toSubring w.valuationSubring _).mp
        (hBW (Subalgebra.mem_toSubring.mpr z.2)))
  -- ### 1. `y ∈ V` and `y = b / s` with `s ∉ P`
  have hyV : y ∈ w.valuationSubring := (Valuation.mem_valuationSubring_iff w y).mpr hy
  have hyVloc : y ∈ (Localization.subalgebra.ofField Ω P.primeCompl hP).toSubring := by
    rw [← hbridge]
    exact (ValuationSubring.mem_toSubring w.valuationSubring y).mpr hyV
  obtain ⟨b, s, hs, hys⟩ :=
    (mem_ofField_iff' P.primeCompl hP y).mp (Subalgebra.mem_toSubring.mp hyVloc)
  -- ### 2. approximations of `b` and `s` by elements of `A` modulo `P`
  obtain ⟨xb, hxb⟩ := inertiaDeg_one_sub_mem (R := ↥(v.valuationSubring))
    (S := ↥(integralClosure ↥(v.valuationSubring) Ω)) P
    (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) hf b
  obtain ⟨xs, hxs⟩ := inertiaDeg_one_sub_mem (R := ↥(v.valuationSubring))
    (S := ↥(integralClosure ↥(v.valuationSubring) Ω)) P
    (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) hf s
  -- ### 3. `xs` is a unit of `A`, so `v xs = 1`
  have hxs_notMem : xs ∉ IsLocalRing.maximalIdeal ↥(v.valuationSubring) := by
    intro hmem
    have h1 : algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xs ∈ P :=
      (Ideal.mem_of_liesOver P (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) xs).mp hmem
    have h2 : s ∈ P := by
      have h3 := P.add_mem hxs h1
      simpa [sub_add_cancel] using h3
    exact hs h2
  have hxs_le : v (xs : F) ≤ 1 := (Valuation.mem_valuationSubring_iff v (xs : F)).mp xs.2
  have hxs_val : v (xs : F) = 1 := by
    refine le_antisymm hxs_le ?_
    by_contra hcon
    exact hxs_notMem ((Valuation.mem_maximalIdeal_iff (v := v)).mpr (lt_of_not_ge hcon))
  have hxs0 : (xs : F) ≠ 0 := fun h =>
    hxs_notMem (by
      have h0 : xs = 0 := Subtype.ext h
      rw [h0]
      exact (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).zero_mem)
  -- ### 4. valuations of the ingredients
  have hs_notP : s ∉ P := hs
  have hs_gt : ¬ w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s) < 1 :=
    fun hlt => hs_notP ((hiff s).mpr hlt)
  have hs_val : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s) = 1 :=
    le_antisymm (hB_le s) (le_of_not_gt hs_gt)
  -- the two approximating elements of `B`
  let bp : ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xb
  let sp : ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xs
  have hpb_mem : b - bp ∈ P := by
    show b - algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xb ∈ P
    exact hxb
  have hps_mem : s - sp ∈ P := by
    show s - algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xs ∈ P
    exact hxs
  have hpb_lt : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp)) < 1 :=
    (hiff (b - bp)).mp hpb_mem
  have hps_lt : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp)) < 1 :=
    (hiff (s - sp)).mp hps_mem
  -- `sp` is the image of `xs`, whose value is `1`
  have hsp_coe : algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp
      = algebraMap F Ω (xs : F) := by
    show algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω
        (algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xs)
      = algebraMap F Ω (xs : F)
    rw [← IsScalarTower.algebraMap_apply ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) Ω xs]
    rfl
  have hsp_val : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp) = 1 := by
    rw [hsp_coe]
    have hle : w (algebraMap F Ω (xs : F)) ≤ 1 := (hsub (xs : F)).mpr hxs_le
    have hge : ¬ w (algebraMap F Ω (xs : F)) < 1 := fun hlt =>
      absurd ((lt_one_iff v w hsub (xs : F)).mp hlt) (by rw [hxs_val]; exact lt_irrefl 1)
    exact le_antisymm hle (le_of_not_gt hge)
  have hbp_le : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp) ≤ 1 := hB_le bp
  have hsp_le : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp) ≤ 1 :=
    le_of_eq hsp_val
  -- nonzero denominators
  have hunit : Function.Injective (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω) :=
    IsFractionRing.injective ↥(integralClosure ↥(v.valuationSubring) Ω) Ω
  have hs0 : algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s ≠ 0 := by
    intro h
    have h0 : s = 0 := hunit (by rw [h, map_zero])
    exact hs_notP (h0 ▸ P.zero_mem)
  have hsp0 : algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp ≠ 0 := by
    rw [hsp_coe]
    intro h
    exact hxs0 ((algebraMap F Ω).injective (by simpa using h))
  -- ### 5. the algebraic identity expressing `y - x` as a fraction
  have hxb_coe : algebraMap F Ω (xb : F)
      = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp := by
    show algebraMap F Ω (xb : F)
      = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω
        (algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xb)
    rw [← IsScalarTower.algebraMap_apply ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) Ω xb]
    rfl
  have hxs_coe : algebraMap F Ω (xs : F)
      = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp := by
    show algebraMap F Ω (xs : F)
      = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω
        (algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) xs)
    rw [← IsScalarTower.algebraMap_apply ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω) Ω xs]
    rfl
  have hx_eq : algebraMap F Ω ((xb : F) * (xs : F)⁻¹)
      = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp *
        (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp)⁻¹ := by
    rw [map_mul, map_inv₀, hxb_coe, hxs_coe]
  have hmain : y - algebraMap F Ω ((xb : F) * (xs : F)⁻¹)
      = (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp) *
            algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp -
          algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp *
            algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp)) *
        (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s *
          algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp)⁻¹ := by
    rw [hys, hx_eq]
    have hb_split : algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω b
        = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp +
          algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp) := by
      rw [map_sub]; abel
    have hs_split : algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s
        = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp +
          algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp) := by
      rw [map_sub]; abel
    field_simp
    rw [hb_split, hs_split]
    first | refl_ring1 | ring
  -- ### 6. the estimate
  have hD_val : w ((algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω s *
      algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp)⁻¹) = 1 := by
    rw [Valuation.map_inv, Valuation.map_mul, hs_val, hsp_val, mul_one, inv_one]
  have hA1 : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp) *
      algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp) < 1 := by
    rw [Valuation.map_mul]
    have h := mul_le_mul_right hsp_le
      (w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp)))
    rw [mul_one] at h
    exact lt_of_le_of_lt h hpb_lt
  have hA2 : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp *
      algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp)) < 1 := by
    rw [Valuation.map_mul]
    have h := mul_le_mul_left hbp_le
      (w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp)))
    rw [one_mul] at h
    exact lt_of_le_of_lt h hps_lt
  have hN_lt : w (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (b - bp) *
        algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω sp -
      algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω bp *
        algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω (s - sp)) < 1 :=
    lt_of_le_of_lt (Valuation.map_sub w _ _) (max_lt hA1 hA2)
  refine ⟨(xb : F) * (xs : F)⁻¹, ?_, ?_⟩
  · have h1 : v (xb : F) ≤ 1 := (Valuation.mem_valuationSubring_iff v (xb : F)).mp xb.2
    have h2 : v ((xs : F)⁻¹) = 1 := by rw [Valuation.map_inv, hxs_val, inv_one]
    rw [Valuation.map_mul, h2, mul_one]
    exact h1
  · rw [hmain, Valuation.map_mul, hD_val, mul_one]
    exact hN_lt

end Work.MotV5.Nodes.UEPR
