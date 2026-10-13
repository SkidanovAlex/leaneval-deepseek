import Mathlib
import Submission.Work.DSM5c.Eta.Setup
import Submission.Work.DSM5c.Eta.gLoc_fracU
import Submission.Work.DSM5c.Eta.vS_eq_teich_prod
import Submission.Work.DSM5c.Eta.isSMulRegular_uProd
import Submission.Work.DSM5c.Eta.EtaMap
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntilt

/-!
# DSM5c / Eta — the crux of gap G1: `vS` is a non-zero-divisor of the chart untilt

This file reduces the remaining input of the chart map `η` of the M5c node (gap G1,
`Submission/Work/DSM5c/NOTES.md` §20.3) to the single statement
`Work.DSM5c.Eta.isSMulRegular_teich`: regularity lifts through the untilt of a chart.

* `Work.DSM5c.Eta.isSMulRegular_vS_of_teich`: `vS S = teich S (∏_{i∈S} u_i)` is a non-zero-divisor
  of `D_S`, where the input `∏_{i∈S} u_i` is a non-zero-divisor of `R_S`
  (`Work.DSM5c.Eta.isSMulRegular_uProd`) and `vS S = teich S (∏_{i∈S} u_i)` is
  `Work.DSM5c.Eta.vS_eq_teich_prod`;
* `Work.DSM5c.Eta.injective_locD_of_isSMulRegular_vS`: the localisation map
  `locD S : D_S →+* D_S[1/v_S]` is injective, i.e. `Work.DSM5c.Eta.etaNat` of `EtaMap.lean` can be
  built.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

section Crux

variable {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
  (Q : DSMap.PerfectoidData p W)
  (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **A power of `x` a non-zero-divisor makes `x` one** (`N > 0`). -/
theorem isSMulRegular_of_isSMulRegular_pow {A : Type*} [CommRing A] {x : A} {N : ℕ} (hN : 0 < N)
    (h : IsSMulRegular A (x ^ N)) : IsSMulRegular A x := by
  intro a b hab
  have hab' : x * a = x * b := by simpa [smul_eq_mul] using hab
  have h0 : x * (a - b) = 0 := by rw [mul_sub, hab', sub_self]
  have h1 : x ^ N * (a - b) = 0 := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [pow_succ, mul_assoc, h0, mul_zero]
  have h2 : x ^ N • (a - b) = x ^ N • (0 : A) := by
    rw [smul_eq_mul, smul_eq_mul, h1, mul_zero]
  exact sub_eq_zero.mp (h h2)

/-- **The crux of gap G1, reduced to `isSMulRegular_teich`.**  The localisation element
`vS S = ♯(u_S) = teich S (∏_{i∈S} u_i)` is a non-zero-divisor of the chart untilt `D_S`, as soon as
regularity lifts through the untilt along Teichmüller (`Work.DSM5c.Eta.isSMulRegular_teich`), using
that `∏_{i∈S} u_i` is a non-zero-divisor of `R_S` (`Work.DSM5c.Eta.isSMulRegular_uProd`). -/
theorem isSMulRegular_vS_of_teich
    (hTeich : ∀ (S : Finset ι) (y : tiltChart' Q t tr htr0 htr j₀ e S),
      (∀ z, y * z = 0 → z = 0) →
      ∀ z : DS Q t tr htr0 htr j₀ e S, teich Q t tr htr0 htr j₀ e S y * z = 0 → z = 0)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) :
    IsSMulRegular (DS Q t tr htr0 htr j₀ e S) (vS Q hθ t tr htr0 htr j₀ e S) := by
  have htz : IsSMulRegular (DS Q t tr htr0 htr j₀ e S)
      (teich Q t tr htr0 htr j₀ e S
        (∏ i ∈ S, uEl Q t tr htr0 htr j₀ e S i)) := by
    rw [IsSMulRegular]
    intro x y hxy
    have hmul : teich Q t tr htr0 htr j₀ e S
          (∏ i ∈ S, uEl Q t tr htr0 htr j₀ e S i) * (x - y) = 0 := by
      rw [mul_sub, sub_eq_zero]
      simpa [smul_eq_mul] using hxy
    exact sub_eq_zero.mp
      (hTeich S (∏ i ∈ S, uEl Q t tr htr0 htr j₀ e S i)
        (isSMulRegular_uProd Q t tr htr0 htr j₀ e S) (x - y) hmul)
  simpa only [vS_eq_teich_prod Q hθ t tr htr0 htr j₀ e hj₀ S] using htz

/-- **Injectivity of `locD S` from the crux**: if `vS S` is a non-zero-divisor of `D_S`, then the
localisation map `D_S →+* D_S[1/v_S]` is injective.  This is the hypothesis of
`Work.DSM5c.Eta.etaNat` of `EtaMap.lean`. -/
theorem injective_locD_of_isSMulRegular_vS
    (h : ∀ S : Finset ι,
      IsSMulRegular (DS Q t tr htr0 htr j₀ e S) (vS Q hθ t tr htr0 htr j₀ e S)) :
    ∀ S : Finset ι, Function.Injective (locD Q hθ t tr htr0 htr j₀ e S) := by
  intro S
  have hmem : vS Q hθ t tr htr0 htr j₀ e S
      ∈ nonZeroDivisors (DS Q t tr htr0 htr j₀ e S) := by
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      have hx' : vS Q hθ t tr htr0 htr j₀ e S * x = 0 := hx
      have h1 : vS Q hθ t tr htr0 htr j₀ e S • x
          = vS Q hθ t tr htr0 htr j₀ e S • (0 : DS Q t tr htr0 htr j₀ e S) := by
        rw [smul_eq_mul, smul_eq_mul, hx', mul_zero]
      exact h S h1
    · intro x hx
      have hx' : vS Q hθ t tr htr0 htr j₀ e S * x = 0 := by
        rw [mul_comm]; exact hx
      have h1 : vS Q hθ t tr htr0 htr j₀ e S • x
          = vS Q hθ t tr htr0 htr j₀ e S • (0 : DS Q t tr htr0 htr j₀ e S) := by
        rw [smul_eq_mul, smul_eq_mul, hx', mul_zero]
      exact h S h1
  exact IsLocalization.injective (S := DSloc Q hθ t tr htr0 htr j₀ e S)
    (M := Submonoid.powers (vS Q hθ t tr htr0 htr j₀ e S))
    (Submonoid.powers_le.mpr hmem)

/-- A unit is a non-zero-divisor. -/
theorem isSMulRegular_of_isUnit {A : Type*} [CommRing A] {u : A} (hu : IsUnit u) :
    IsSMulRegular A u := by
  obtain ⟨w, hw⟩ := hu
  intro a b hab
  have hab' : u * a = u * b := by simpa [smul_eq_mul] using hab
  have h0 : u * (a - b) = 0 := by rw [mul_sub, hab', sub_self]
  have h1 : ((w⁻¹ : Aˣ) : A) * (u * (a - b)) = 0 := by rw [h0, mul_zero]
  have h2 : a - b = 0 := by
    calc a - b = ((w⁻¹ : Aˣ) : A) * (↑w : A) * (a - b) := by
          rw [Units.inv_mul, one_mul]
      _ = ((w⁻¹ : Aˣ) : A) * (u * (a - b)) := by rw [mul_assoc, hw]
      _ = 0 := h1
  exact sub_eq_zero.mp h2

/-- **The `j₀`-part of the crux of gap G1.**  The image in the chart untilt `D_S` of the
distinguished generator `t j₀ = Q.ϖ 0 ^ e` is a non-zero-divisor.

Reason: with `w := untiltOf.algebraMap hθ φ (Q.ϖ 0)` one has `w ^ p = p · (unit)` (because
`Q.ϖ 0 ^ p = p · v` with `v : Wˣ`, and `untiltOf.algebraMap` is a ring homomorphism), so
`algebraMap (t j₀) ^ p = (w ^ e) ^ p = (w ^ p) ^ e = p ^ e · (unit)`; and `p` is a non-zero-divisor of
`D_S` (`Work.DSM5c.G2.isSMulRegular_chartUntilt`, gap G2). -/
theorem isSMulRegular_algebraMap_tj₀ (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) :
    IsSMulRegular (DS Q t tr htr0 htr j₀ e S)
      (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀)) := by
  obtain ⟨v, hv⟩ := Q.unit
  -- `p` is a non-zero-divisor of `D_S` (gap G2)
  have hp : IsSMulRegular (DS Q t tr htr0 htr j₀ e S)
      (p : DS Q t tr htr0 htr j₀ e S) :=
    Work.DSM5c.G2.isSMulRegular_chartUntilt (p := p) (W := W) Q t tr htr0 htr j₀ e hj₀ S
  -- the auxiliary unit `u = algebraMap v` and its power
  have hunit : IsUnit ((untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (v : W)) ^ e) := by
    have hmap : IsUnit (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (v : W)) :=
      IsUnit.map (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S))
        (show IsUnit (v : W) from v.isUnit)
    exact hmap.pow e
  -- the power relation `algebraMap (t j₀) ^ p = p ^ e · u ^ e`
  have hpow : (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀)) ^ p
      = (p : DS Q t tr htr0 htr j₀ e S) ^ e
        * (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (v : W)) ^ e := by
    have h2 : (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (Q.ϖ 0)) ^ p
        = (p : DS Q t tr htr0 htr j₀ e S)
          * untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (v : W) := by
      rw [← map_pow, hv, map_mul, map_natCast]
    have h1 : untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀)
        = (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (Q.ϖ 0)) ^ e := by
      rw [hj₀, map_pow]
    rw [h1, ← pow_mul, Nat.mul_comm e p, pow_mul, h2, mul_pow]
  have hmain : IsSMulRegular (DS Q t tr htr0 htr j₀ e S)
      ((untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀)) ^ p) := by
    rw [hpow]
    exact (hp.pow e).mul (isSMulRegular_of_isUnit hunit)
  exact isSMulRegular_of_isSMulRegular_pow (Fact.out : p.Prime).pos hmain

/-- **The chart generators are non-zero-divisors in the chart untilt `D_S`** — the crux of gap G1,
in the form actually needed.  The key point is the *factorisation*

  `algebraMap (t j₀) = teich (u_{j₀}/u_i) · teich (u_i) = teich (u_{j₀}/u_i) · algebraMap (t i)`

in `D_S` (`u_{j₀} = (u_{j₀}/u_i)·u_i` in `R_S` — this is `fracU_mul_uEl` with the *numerator*
index `j₀`, which is allowed for any `i ∈ S` since the chart generators are `u_k/u_i` with `i ∈ S`
and `k` arbitrary —, multiplicativity of `teich`, and `teich (u_k) = algebraMap (t k)`): since
`algebraMap (t j₀)` is a non-zero-divisor (`Work.DSM5c.Eta.isSMulRegular_algebraMap_tj₀`), so is
`algebraMap (t i)`. -/
theorem isSMulRegular_untilt_algebraMap_t (hj₀ : t j₀ = Q.ϖ 0 ^ e) {S : Finset ι}
    {i : ι} (hi : i ∈ S) :
    IsSMulRegular (DS Q t tr htr0 htr j₀ e S)
      (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i)) := by
  -- `algebraMap (t j₀) = teich (u_{j₀}/u_i) * algebraMap (t i)`
  have hsplit : untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀)
      = teich Q t tr htr0 htr j₀ e S (fracU Q t tr htr0 htr j₀ e S i j₀ hi)
        * untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i) := by
    rw [← teich_uEl (hj₀ := hj₀) (k := j₀), ← teich_uEl (hj₀ := hj₀) (k := i), ← teich_mul,
      fracU_mul_uEl]
  rw [IsSMulRegular]
  intro z z' hzz
  have hzz' : untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i) • z
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i) • z' := hzz
  have h0 : untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀) • z
      = untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t j₀) • z' := by
    rw [hsplit, mul_smul, mul_smul, hzz']
  exact isSMulRegular_algebraMap_tj₀ Q hθ t tr htr0 htr j₀ e hj₀ S h0

/-- **The localisation element `vS S` is a non-zero-divisor of the chart untilt `D_S`** — the crux
of gap G1 in the form needed by the construction of the chart map `η`.  Indeed
`vS S = ∏_{i∈S} algebraMap W D_S (t i)` (`vS S = untiltOf.algebraMap hθ φ_S (tS t S)` and
`tS t S = ∏_{i∈S} t i`), and each factor is a non-zero-divisor by
`Work.DSM5c.Eta.isSMulRegular_untilt_algebraMap_t`, as is their product. -/
theorem isSMulRegular_vS (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) :
    IsSMulRegular (DS Q t tr htr0 htr j₀ e S) (vS Q hθ t tr htr0 htr j₀ e S) := by
  have hv : vS Q hθ t tr htr0 htr j₀ e S
      = ∏ i ∈ S, untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i) := by
    show untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (tS t S) = _
    rw [show tS t S = ∏ i ∈ S, t i from rfl, map_prod]
  rw [hv]
  refine Finset.prod_induction
    (fun i => untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (t i))
    (fun x => IsSMulRegular (DS Q t tr htr0 htr j₀ e S) x) ?_ ?_ ?_
  · intro x y hx hy
    exact hx.mul hy
  · intro a b hab
    simpa using hab
  · intro i hi
    exact isSMulRegular_untilt_algebraMap_t Q hθ t tr htr0 htr j₀ e hj₀ hi

end Crux

end Work.DSM5c.Eta
