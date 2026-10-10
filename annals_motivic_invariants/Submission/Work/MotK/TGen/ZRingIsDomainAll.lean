import Mathlib
import Submission.Work.MotK.TGen.ZPlaneModel
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.MotK.TGen.zIdealMem
import Submission.Work.MotK.TGen.RadSatDefs
import Submission.Work.MotK.TGen.zJ_inter_rename
import Submission.Work.MotK.TGen.zF1Div
import Submission.Work.MotK.TGen.starLem
import Submission.Work.MotK.TGen.zA_cancel_zg
import Submission.Work.MotK.TGen.ZElim2IrredCharAll
import Submission.Work.MotK.TwCensus.GoodDiscNe
import Submission.Work.MotK.TwRuling.good_bFive_ne_charFive
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IsDomain (K[x₀,x₁,x₂] ⧸ √(ZI a b h))` for an arbitrary field

## The mathematics (found 2026-10-05)

Write `R = K[x₀,x₁,x₂]`, `P = K[x₁,x₂]`, `zA = b³h x₁ − a³h x₂²`, `zC = a²b − ab²h x₁²x₂`,
`zB = zA x₀ − zC`, `zg = rename ZElim2`, and

* `zAl = a²b⁴h`, `zBet = −a⁶h x₂³`,
  `zGam = a⁴b²h x₁²x₂² + ab⁵h x₁³ − (a⁵b+b⁶) x₂`, `zF1 = zAl x₀² + zBet x₀ + zGam`.

Then (`zElim_quad_id`):  `zAl·zC² + zBet·zC·zA + zGam·zA² = (b⁴h)·zg`.   (†)

**Key point: `√(ZI) = J := (zF1, zB)`, and `zA` is a non-zero-divisor modulo `J`.**

1. `zg ∈ (zF1, zB)`:  from (†),
   `zA²·zF1 − (b⁴h)·zg = zB·(zAl·(zA x₀ + zC) + zBet·zA)`,   and `b⁴h` is a unit.
2. `zF1, zB, zg ∈ ZI` (proved in the workspace), so `J ⊆ ZI`; conversely `ZI ⊆ ker zPsi` and
   `ker zPsi ⊆ J : zA^∞`, hence `√ZI ⊆ J : zA^∞`.  So everything reduces to the saturation
   `J : zA^∞ = J`, proved via `zA_mul_mem_zJ` below.
3. `√ZI = J` and `J = ker zPsi` is prime, so `R/√ZI = R/J ↪ Frac(ZD)` is a domain.

The four elementary leaves (`zF1Div`, `starLem` = (★), `zA_cancel_zg`, `zJ_inter_rename`) are
delegated; the assembly (`zA_mul_mem_zJ`) is below.
-/

set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]





/-- **`zg ∈ (zF1, zB)`.**  Direct consequence of `zElim_quad_id`. -/
theorem zg_mem_zJ (K : Type) [Field K] (a b h : K) (hb : b ≠ 0) (hh : h ≠ 0) :
    zg K a b h ∈ zJ K a b h := by
  have hb4h : b ^ 4 * h ≠ 0 := mul_ne_zero (pow_ne_zero 4 hb) hh
  have hkey : zA K a b h ^ 2 * zF1 K a b h - C (b ^ 4 * h) * zg K a b h
      = zB K a b h * (zAl K a b h * (zA K a b h * X 0 + zC K a b h)
          + zBet K a b h * zA K a b h) := by
    simp only [zF1, zAl, zBet, zGam, zA, zB, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim,
      C_mul, C_pow, C_add, map_neg, map_ofNat]
    first | refl_ring1 | ring
  have hmem : C (b ^ 4 * h) * zg K a b h ∈ zJ K a b h := by
    rw [zJ]
    have h1 : zF1 K a b h
        ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
      Ideal.subset_span (by simp)
    have h2 : zB K a b h
        ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
      Ideal.subset_span (by simp)
    have h3 : zA K a b h ^ 2 * zF1 K a b h
        ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
      Ideal.mul_mem_left _ (zA K a b h ^ 2) h1
    have h4 : zB K a b h * (zAl K a b h * (zA K a b h * X 0 + zC K a b h)
          + zBet K a b h * zA K a b h)
        ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
      Ideal.mul_mem_right (zAl K a b h * (zA K a b h * X 0 + zC K a b h)
        + zBet K a b h * zA K a b h) _ h2
    have heq : C (b ^ 4 * h) * zg K a b h
        = zA K a b h ^ 2 * zF1 K a b h
          - zB K a b h * (zAl K a b h * (zA K a b h * X 0 + zC K a b h)
              + zBet K a b h * zA K a b h) := by
      have hh' := hkey
      rw [sub_eq_iff_eq_add] at hh'
      rw [hh']
      first | refl_ring1 | ring
    rw [heq]
    exact Ideal.sub_mem _ h3 h4
  have hunit : (C ((b ^ 4 * h)⁻¹) : MvPolynomial (Fin 3) K) * C (b ^ 4 * h) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb4h, C_1]
  have hthis := Ideal.mul_mem_left (zJ K a b h) (C ((b ^ 4 * h)⁻¹)) hmem
  have hassoc : (C ((b ^ 4 * h)⁻¹) : MvPolynomial (Fin 3) K) * (C (b ^ 4 * h) * zg K a b h)
      = C ((b ^ 4 * h)⁻¹) * C (b ^ 4 * h) * zg K a b h := (mul_assoc _ _ _).symm
  rw [hassoc, hunit, one_mul] at hthis
  exact hthis

/-- The "certificate" (♣): `α·(zC x₀) + zBet zC + zGam zA ∈ J`, i.e.
`α·(x₀ zC + (zBet zC + zGam zA)/α) ∈ J`. -/
theorem cert_mem_zJ (K : Type) [Field K] (a b h : K) :
    zAl K a b h * (zC K a b h * X 0) + zBet K a b h * zC K a b h
      + zGam K a b h * zA K a b h ∈ zJ K a b h := by
  have hkey : zAl K a b h * (zC K a b h * X 0) + zBet K a b h * zC K a b h
      + zGam K a b h * zA K a b h
      = -(zAl K a b h * X 0 + zBet K a b h) * zB K a b h
        + zA K a b h * zF1 K a b h := by
    simp only [zF1, zAl, zBet, zGam, zA, zB, zC, C_mul, C_pow, C_add, map_neg, map_ofNat]
    first | refl_ring1 | ring
  rw [hkey, zJ]
  have h1 : zB K a b h ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
    Ideal.subset_span (by simp)
  have h2 : zF1 K a b h ∈ Ideal.span ({zF1 K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
    Ideal.subset_span (by simp)
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ (-(zAl K a b h * X 0 + zBet K a b h)) h1)
    (Ideal.mul_mem_left _ (zA K a b h) h2)

/-- **The crux**: `zA` is a non-zero-divisor modulo `zJ = (zF1, zB)`, i.e. `zJ : zA^∞ = zJ`. -/
theorem zA_mul_mem_zJ (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (ZD K a b h)] (f : MvPolynomial (Fin 3) K) :
    zA K a b h * f ∈ zJ K a b h → f ∈ zJ K a b h := by
  intro hf
  obtain ⟨f₀, f₁, q, hfdec⟩ := zF1Div K a b h ha hb hh f
  rw [hfdec] at hf ⊢
  have hF1 : zF1 K a b h ∈ zJ K a b h := Ideal.subset_span (by simp)
  have hB : zB K a b h ∈ zJ K a b h := Ideal.subset_span (by simp)
  have hZg : zg K a b h ∈ zJ K a b h := zg_mem_zJ K a b h hb hh
  -- Step A: reduce to `f = rename f₀ + rename f₁ * X 0`
  have main : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0) ∈ zJ K a b h := by
    have hqF1 : zA K a b h * (q * zF1 K a b h) ∈ zJ K a b h :=
      Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ (q) hF1)
    have hsub := Ideal.sub_mem (zJ K a b h) hf hqF1
    rwa [show zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0 + q * zF1 K a b h)
        - zA K a b h * (q * zF1 K a b h)
        = zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0) from by ring] at hsub
  -- Step B: `zA * X 0 = zB + zC`
  have hAX : zA K a b h * X 0 = zB K a b h + zC K a b h := by rw [zB]; ring
  have hkey1 : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
      = rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h) + rename zEmb f₁ * zB K a b h := by
    have h1 : rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h)
        = zA K a b h * rename zEmb f₀ + rename zEmb f₁ * zC K a b h := by
      rw [map_add, map_mul, map_mul, zA_eq_rename, zC_eq_rename]
    have h2 : zA K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        = zA K a b h * rename zEmb f₀ + rename zEmb f₁ * (zA K a b h * X 0) := by ring
    rw [h1, h2, hAX, zB]
    first | refl_ring1 | ring
  have hB2 : rename zEmb f₁ * zB K a b h ∈ zJ K a b h := Ideal.mul_mem_left _ (rename zEmb f₁) hB
  have hmem1 : rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h) ∈ zJ K a b h := by
    have hthis := Ideal.sub_mem (zJ K a b h) main hB2
    rw [hkey1] at hthis
    simpa using hthis
  -- Step C: land in `(ZElim2)`
  have hdiv : zpA K a b h * f₀ + f₁ * zpC K a b h
      ∈ Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)) :=
    zJ_inter_rename K a b h ha hb hh _ hmem1
  -- Step D: `rename f₁ * zC ∈ (zA, zg)`, hence `rename f₁ ∈ (zA, zC)`
  have hZgm : rename zEmb (zpA K a b h * f₀ + f₁ * zpC K a b h) ∈ Ideal.span {zg K a b h} := by
    rw [Ideal.mem_span_singleton] at hdiv ⊢
    obtain ⟨c, hc⟩ := hdiv
    exact ⟨rename zEmb c, by rw [hc, map_mul, zg]⟩
  have hZg2 : zA K a b h * rename zEmb f₀ + rename zEmb f₁ * zC K a b h
      ∈ Ideal.span {zg K a b h} := by
    rw [zA_eq_rename, zC_eq_rename, ← map_mul, ← map_mul, ← map_add]
    exact hZgm
  have hstar : rename zEmb f₁ * zC K a b h ∈ Ideal.span ({zA K a b h, zg K a b h} : Set _) := by
    have hA : zA K a b h * rename zEmb f₀
        ∈ Ideal.span ({zA K a b h, zg K a b h} : Set _) :=
      Ideal.mul_mem_right (rename zEmb f₀) _ (Ideal.subset_span (by simp))
    have hZ : zA K a b h * rename zEmb f₀ + rename zEmb f₁ * zC K a b h
        ∈ Ideal.span ({zA K a b h, zg K a b h} : Set _) :=
      Ideal.span_mono (by simp) hZg2
    have hsub := Ideal.sub_mem _ hZ hA
    rwa [add_sub_cancel_left] at hsub
  have hfin : rename zEmb f₁ ∈ Ideal.span ({zA K a b h, zC K a b h} : Set _) :=
    starLem K a b h ha hb hh _ hstar
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hfin
  -- now `huv : u * zA + v * zC = rename f₁`
  -- Step E: `zA * rename f₀ + (u zA + v zC) zC ∈ (zg)`
  have hstepA : zA K a b h * rename zEmb f₀ + (u * zA K a b h + v * zC K a b h) * zC K a b h
      ∈ Ideal.span {zg K a b h} := by
    rw [huv]
    exact hZg2
  have hstepB : zA K a b h * (rename zEmb f₀ + u * zC K a b h) + v * zC K a b h ^ 2
      ∈ Ideal.span {zg K a b h} := by
    have hthis := hstepA
    rwa [show zA K a b h * rename zEmb f₀ + (u * zA K a b h + v * zC K a b h) * zC K a b h
        = zA K a b h * (rename zEmb f₀ + u * zC K a b h) + v * zC K a b h ^ 2 from by ring] at hthis
  -- Step F: eliminate `zC^2` with (†)
  have hquad : zAl K a b h * zC K a b h ^ 2 + zBet K a b h * zC K a b h * zA K a b h
      + zGam K a b h * zA K a b h ^ 2 ∈ Ideal.span {zg K a b h} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨C (b ^ 4 * h), by rw [zElim_quad_id, mul_comm]⟩
  have hstepC : zA K a b h * (zAl K a b h * (rename zEmb f₀ + u * zC K a b h)
        - v * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h))
      ∈ Ideal.span {zg K a b h} := by
    have h1 : zAl K a b h * (zA K a b h * (rename zEmb f₀ + u * zC K a b h)
          + v * zC K a b h ^ 2) ∈ Ideal.span {zg K a b h} :=
      Ideal.mul_mem_left _ _ hstepB
    have h2 : v * (zAl K a b h * zC K a b h ^ 2 + zBet K a b h * zC K a b h * zA K a b h
          + zGam K a b h * zA K a b h ^ 2) ∈ Ideal.span {zg K a b h} :=
      Ideal.mul_mem_left _ _ hquad
    have hthis := Ideal.sub_mem _ h1 h2
    have heq : zAl K a b h * (zA K a b h * (rename zEmb f₀ + u * zC K a b h)
          + v * zC K a b h ^ 2)
        - v * (zAl K a b h * zC K a b h ^ 2 + zBet K a b h * zC K a b h * zA K a b h
          + zGam K a b h * zA K a b h ^ 2)
        = zA K a b h * (zAl K a b h * (rename zEmb f₀ + u * zC K a b h)
          - v * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h)) := by
      first | refl_ring1 | ring
    rwa [heq] at hthis
  have hstepD : zAl K a b h * (rename zEmb f₀ + u * zC K a b h)
      - v * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h)
      ∈ Ideal.span {zg K a b h} :=
    zA_cancel_zg K a b h ha hb hh _ hstepC
  have hle : Ideal.span {zg K a b h} ≤ zJ K a b h :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hZg)
  have hstepD' : zAl K a b h * (rename zEmb f₀ + u * zC K a b h)
      - v * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h) ∈ zJ K a b h :=
    hle hstepD
  have hcert := cert_mem_zJ K a b h
  -- Step G: multiply the goal by the unit `zAl`
  have hgoal : zAl K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0) ∈ zJ K a b h := by
    have heq : zAl K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)
        = (zAl K a b h * (rename zEmb f₀ + u * zC K a b h)
            - v * (zBet K a b h * zC K a b h + zGam K a b h * zA K a b h))
          + zAl K a b h * (u * (zA K a b h * X 0 - zC K a b h))
          + v * (zAl K a b h * (zC K a b h * X 0) + zBet K a b h * zC K a b h
              + zGam K a b h * zA K a b h) := by
      rw [← huv]
      first | refl_ring1 | ring
    rw [heq]
    refine Ideal.add_mem _ (Ideal.add_mem _ hstepD' ?_) ?_
    · rw [show zAl K a b h * (u * (zA K a b h * X 0 - zC K a b h))
          = (zAl K a b h * u) * (zA K a b h * X 0 - zC K a b h) from by ring]
      rw [zB] at hB
      exact Ideal.mul_mem_left _ (zAl K a b h * u) hB
    · exact Ideal.mul_mem_left _ _ hcert
  -- Step H: divide by the unit `zAl`
  have hcarith : a ^ 2 * b ^ 4 * h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 4 hb)) hh
  have hcAl : (C ((a ^ 2 * b ^ 4 * h)⁻¹) : MvPolynomial (Fin 3) K) * zAl K a b h = 1 := by
    rw [zAl, ← C_mul, inv_mul_cancel₀ hcarith, C_1]
  have hfinal : rename zEmb f₀ + rename zEmb f₁ * X 0
      = C ((a ^ 2 * b ^ 4 * h)⁻¹)
          * (zAl K a b h * (rename zEmb f₀ + rename zEmb f₁ * X 0)) := by
    rw [← mul_assoc, hcAl, one_mul]
  rw [hfinal]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hgoal) ?_
  exact Ideal.mul_mem_left _ (q) hF1

theorem ZRingIsDomainAll (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) :
    IsDomain (MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) := by
  have ha : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, mul_zero])
  -- `ZD` is a domain
  haveI hZD : IsDomain (ZD K D.a D.b h) := by
    have hdisc : D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 ≠ 0 := by
      by_cases h5 : ringChar K = 5
      · have hb5 : D.b ^ 5 ≠ 2 * D.a ^ 5 := Work.MotK.TwRuling.good_bFive_ne_charFive K D hD h5
        haveI hchar : CharP K 5 := ringChar.eq_iff.mp h5
        haveI hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have h5K : (5 : K) = 0 := CharP.cast_eq_zero K 5
        have h11 : (11 : K) = 1 := by
          have h10 : (10 : K) = 0 := by
            rw [show (10 : K) = 2 * 5 by norm_num, h5K, mul_zero]
          rw [show (11 : K) = 10 + 1 by norm_num, h10, zero_add]
        have h4 : (4 : K) = -1 := by
          rw [show (4 : K) = 5 - 1 by norm_num, h5K, zero_sub]
        have h1 : (D.a ^ 2 - D.a * D.b) ^ 5 = D.a ^ 10 - D.a ^ 5 * D.b ^ 5 := by
          have h := sub_pow_char (R := K) (x := D.a ^ 2) (y := D.a * D.b) (p := 5)
          rw [h]
          first | refl_ring1 | ring
        have h2 : (D.a ^ 2 - D.a * D.b - D.b ^ 2) ^ 5
            = (D.a ^ 2 - D.a * D.b) ^ 5 - D.b ^ 10 := by
          have h := sub_pow_char (R := K) (x := D.a ^ 2 - D.a * D.b) (y := D.b ^ 2) (p := 5)
          rw [h]
          first | refl_ring1 | ring
        have hexp : (D.a ^ 2 - D.a * D.b - D.b ^ 2) ^ 5
            = D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 := by
          rw [h2, h1, h11, one_mul]
        have hsq : (D.a ^ 2 - D.a * D.b - D.b ^ 2) = -(D.b - 2 * D.a) ^ 2 := by
          have hsqe : (D.b - 2 * D.a) ^ 2 = D.b ^ 2 - 4 * D.b * D.a + 4 * D.a ^ 2 := by ring
          rw [hsqe, h4]
          first | refl_ring1 | ring
        intro h0
        have hz : (D.a ^ 2 - D.a * D.b - D.b ^ 2) ^ 5 = 0 := by rw [hexp, h0]
        rw [hsq] at hz
        have hz2 : ((D.b - 2 * D.a) ^ 2) ^ 5 = 0 := by
          have hodd : (-((D.b - 2 * D.a) ^ 2)) ^ 5 = -((D.b - 2 * D.a) ^ 2) ^ 5 := by ring
          rw [hodd] at hz
          exact neg_eq_zero.mp hz
        have hsq0 : (D.b - 2 * D.a) ^ 2 = 0 :=
          (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hz2
        have hbz : D.b = 2 * D.a := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq0)
        apply hb5
        have h32 : (32 : K) = 2 := by
          have h30 : (30 : K) = 0 := by
            rw [show (30 : K) = 6 * 5 by norm_num, h5K, mul_zero]
          rw [show (32 : K) = 30 + 2 by norm_num, h30, zero_add]
        rw [hbz, show (2 * D.a) ^ 5 = 32 * D.a ^ 5 from by ring, h32]
      · exact Work.MotK.TwCensus.goodDisc_extension K h5 D hD (AlgebraicClosure K) (Work.MotK.TwCensus.GoodDiscZeta K h5)
    have hirr := ZElim2IrredCharAll K D.a D.b h ha hb hh hdisc
    have hp : Prime (Work.MotK.TwCensus.ZElim2 D.a D.b h) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    show IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TwCensus.ZElim2 D.a D.b h})
    rw [Ideal.Quotient.isDomain_iff_prime]
    exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  -- `zJ ≤ ZI`
  have hJZI : zJ K D.a D.b h ≤ Work.MotK.TwCensus.ZI D.a D.b h := by
    rw [zJ, Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact zF1_mem_ZI (K := K) D.a D.b h ha hb
    · exact zB_mem_ZI (K := K) D.a D.b h hb
  -- `√ZI ⊆ ker zPsi`
  have hker_prime : (RingHom.ker (zPsi K D.a D.b h)).IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin 3) K) ∈ RingHom.ker (zPsi K D.a D.b h) := by
        rw [htop]; trivial
      simpa using h1
    · intro x y hxy
      have h : zPsi K D.a D.b h x * zPsi K D.a D.b h y = 0 := by
        have := hxy
        simpa using this
      rcases mul_eq_zero.mp h with h' | h'
      · exact Or.inl (RingHom.mem_ker.mpr h')
      · exact Or.inr (RingHom.mem_ker.mpr h')
  have hrad_le : Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h) ≤ RingHom.ker (zPsi K D.a D.b h) := by
    intro x hx
    rw [Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker]
    have h0 : (zPsi K D.a D.b h x) ^ n = 0 := by
      have h1 := ZI_le_ker_zPsi K D.a D.b h ha hb hh hn
      rw [RingHom.mem_ker] at h1
      simpa using h1
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have h1 : (1 : MvPolynomial (Fin 3) K) ∈ Work.MotK.TwCensus.ZI D.a D.b h := by simpa using hn
      have h2 := ZI_le_ker_zPsi K D.a D.b h ha hb hh h1
      rw [RingHom.mem_ker] at h2
      exact absurd h2 (by simp)
    · exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hnpos)).mp h0
  -- `ker zPsi ≤ zJ`
  have hker_le : RingHom.ker (zPsi K D.a D.b h) ≤ zJ K D.a D.b h := by
    intro f hf
    obtain ⟨N, hN⟩ := (ker_zPsi_eq_saturation K D.a D.b h ha hb hh f).mp hf
    have hsub : Ideal.span ({zg K D.a D.b h, zB K D.a D.b h} : Set (MvPolynomial (Fin 3) K))
        ≤ zJ K D.a D.b h := by
      rw [zJ, Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact zg_mem_zJ K D.a D.b h hb hh
      · exact Ideal.subset_span (by simp)
    have hsat : ∀ n (g : MvPolynomial (Fin 3) K),
        (zA K D.a D.b h) ^ n * g ∈ zJ K D.a D.b h → g ∈ zJ K D.a D.b h := by
      intro n
      induction n with
      | zero => intro g hg; simpa using hg
      | succ m ih =>
          intro g hg
          rw [pow_succ, mul_assoc] at hg
          exact zA_mul_mem_zJ K D.a D.b h ha hb hh g (ih _ hg)
    exact hsat N f (hsub hN)
  have hkerJ : RingHom.ker (zPsi K D.a D.b h) = zJ K D.a D.b h :=
    le_antisymm hker_le (le_trans hJZI (ZI_le_ker_zPsi K D.a D.b h ha hb hh))
  have hradJ : Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h) = zJ K D.a D.b h := by
    refine le_antisymm ?_ ?_
    · rw [← hkerJ]
      exact hrad_le
    · exact le_trans hJZI Ideal.le_radical
  rw [hradJ, ← hkerJ]
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact hker_prime

end Work.MotK.TGen
