import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

/-
Route (for the prover): let `S = MvPolynomial (Fin 5) K`, `J = I ⊔ Ideal.span {X 0 - 1}`, `A = S ⧸ I`
(reduced since `I` is radical), `x := Ideal.Quotient.mk I (X 0)`, `L := Localization.Away x` (reduced,
being a localization of `A`).  Put `y := IsLocalization.Away.invSelf x`; then
`algebraMap A L x * y = 1` (`IsLocalization.Away.mul_invSelf`).  Define
`δ : S →ₐ[K] L := MvPolynomial.aeval (fun i => algebraMap A L (Ideal.Quotient.mk I (X i)) * y)`
(so `δ (X 0) = 1`).
Key computation: for `p` homogeneous of degree `d` (`MvPolynomial.IsHomogeneous p d`) one has
`δ p = algebraMap A L (Ideal.Quotient.mk I p) * y ^ d`; reduce to monomials with
`MvPolynomial.aeval_monomial` (`aeval g (monomial m c) = C c * ∏ i, g i ^ (m i)`) and use
`algebraMap x * y = 1` plus multiplicativity of `algebraMap`.
Hence `δ p = 0` for `p ∈ I` (write `p = ∑_{d ≤ p.totalDegree} homogeneousComponent d p`,
`MvPolynomial.sum_homogeneousComponent`, and use `hIhom`), so `δ` kills `J` and induces
`δ̄ : S ⧸ J →ₐ[K] L`.
Injectivity of `δ̄`: suppose `δ p = 0`.  With `N := p.totalDegree`, `p_d := homogeneousComponent d p`
and `z := ∑_{d ≤ N} p_d * (MvPolynomial.X 0) ^ (N - d)`, the key computation gives
`δ p = algebraMap A L (Ideal.Quotient.mk I z) * y ^ N`, so `algebraMap A L (mk z) = 0` (as `y` is a
unit in `L`); by the description of the kernel of a localization map this means `(X 0) ^ M * z ∈ I`
for some `M`.  Since `X 0 ≡ 1` modulo `(X 0 - 1)` one has `z - (X 0)^M * z ∈ (X 0 - 1)`, so `z ∈ J`;
and `p - z ∈ (X 0 - 1)` (as `X 0 ^ (N-d) ≡ 1`), so `p ∈ J`, i.e. `mk_J p = 0`.
Conclude with `isReduced_of_injective δ̄` (the target `L` is reduced).
-/
theorem ReducedChartQuot (K : Type) [Field K]
    (I : Ideal (MvPolynomial (Fin 5) K)) (hIrad : I.IsRadical)
    (hIhom : ∀ p ∈ I, ∀ d, MvPolynomial.homogeneousComponent d p ∈ I) :
    IsReduced (MvPolynomial (Fin 5) K ⧸ (I ⊔ Ideal.span {MvPolynomial.X 0 - 1})) := by
  classical
  let S := MvPolynomial (Fin 5) K
  let J : Ideal S := I ⊔ Ideal.span {MvPolynomial.X 0 - 1}
  let A := S ⧸ I
  let x : A := Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 5))
  let L := Localization.Away x
  let y : L := IsLocalization.Away.invSelf x
  have hyx : algebraMap A L x * y = 1 := IsLocalization.Away.mul_invSelf x
  let δ : S →ₐ[K] L :=
    MvPolynomial.aeval (fun i => algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i)) * y)
  have hδX0 : δ (MvPolynomial.X (0:Fin 5)) = 1 := by
    have h : δ (MvPolynomial.X (0:Fin 5)) =
        algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X 0)) * y := MvPolynomial.aeval_X _ 0
    rw [h]
    simpa [x] using hyx
  -- product of the `y ^ k` over a finsupp
  have hy : ∀ dd : Fin 5 →₀ ℕ,
      dd.prod (fun i k => y ^ k) = y ^ Finsupp.weight (fun _ : Fin 5 => 1) dd := by
    intro dd
    rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finsupp.weight_eq_sum]
    simp
  have hu : ∀ dd : Fin 5 →₀ ℕ,
      dd.prod (fun i k => (algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))) ^ k)
        = ∏ i ∈ dd.support, (algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))) ^ (dd i) := by
    intro dd
    rfl
  have hR : ∀ dd : Fin 5 →₀ ℕ,
      algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.monomial dd 1))
        = ∏ i ∈ dd.support, (algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))) ^ (dd i) := by
    intro dd
    rw [← MvPolynomial.prod_X_pow_eq_monomial (s := dd), map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow, map_pow]
  have hC : ∀ r : K, Ideal.Quotient.mk I (MvPolynomial.C r) = algebraMap K A r := by
    intro r
    rw [← MvPolynomial.algebraMap_eq]
    exact AlgHom.commutes (Ideal.Quotient.mkₐ K I) r
  -- the monomial (Key computation)
  have mono : ∀ (dd : Fin 5 →₀ ℕ) (r : K),
      δ (MvPolynomial.monomial dd r) =
        algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.monomial dd r)) *
          y ^ Finsupp.weight (fun _ : Fin 5 => 1) dd := by
    intro dd r
    rw [MvPolynomial.aeval_monomial]
    have hmono : MvPolynomial.monomial dd r = MvPolynomial.C r * MvPolynomial.monomial dd 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    have hL : dd.prod (fun i k =>
          ((algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))) * y) ^ k)
        = (∏ i ∈ dd.support, (algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))) ^ (dd i))
            * y ^ Finsupp.weight (fun _ : Fin 5 => 1) dd := by
      rw [Finsupp.prod_congr (g2 := fun i k =>
        (algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i)))^k * y^k)
        (fun i _ => mul_pow _ _ _)]
      rw [Finsupp.prod_mul, hu dd, hy dd]
    rw [hL]
    rw [hmono, map_mul, map_mul, hC r, ← IsScalarTower.algebraMap_apply K A L r, hR dd]
    refl_ring1
  -- the Key computation for homogeneous `p`
  have key : ∀ (p : S) (d : ℕ), MvPolynomial.IsHomogeneous p d →
      δ p = algebraMap A L (Ideal.Quotient.mk I p) * y ^ d := by
    intro p d hp
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq =>
        simp only [map_add, ihp, ihq, add_mul]
    | monomial dd r hr =>
        have hr' : Finsupp.weight (fun _ : Fin 5 => 1) dd = d := hr
        rw [mono dd r, hr']
  -- `δ` vanishes on `I`
  have hδI : ∀ p ∈ I, δ p = 0 := by
    intro p hp
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [key _ i (MvPolynomial.homogeneousComponent_isHomogeneous i p),
      Ideal.Quotient.eq_zero_iff_mem.mpr (hIhom p hp i), map_zero, zero_mul]
  have hδX01 : δ (MvPolynomial.X (0:Fin 5) - 1) = 0 := by
    rw [map_sub, hδX0, map_one, sub_self]
  have hJle : (J : Ideal S) ≤ RingHom.ker δ.toRingHom := by
    change (I ⊔ Ideal.span {MvPolynomial.X 0 - 1}) ≤ RingHom.ker δ.toRingHom
    refine sup_le ?_ ?_
    · intro p hp
      exact RingHom.mem_ker.mpr (hδI p hp)
    · rw [Ideal.span_le]
      intro q hq
      obtain rfl : q = MvPolynomial.X 0 - 1 := by simpa using hq
      exact RingHom.mem_ker.mpr hδX01
  let δbar : S ⧸ J →+* L :=
    Ideal.Quotient.lift J δ.toRingHom (fun a ha => RingHom.mem_ker.mp (hJle ha))
  have hlifth : ∀ q : S, δbar (Ideal.Quotient.mk J q) = δ q := fun q =>
    Ideal.Quotient.lift_mk J δ.toRingHom (fun a ha => RingHom.mem_ker.mp (hJle ha))
  have hXJ : Ideal.Quotient.mk J (MvPolynomial.X (0:Fin 5)) = 1 := by
    have h : Ideal.Quotient.mk J (MvPolynomial.X (0:Fin 5) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one] at h
    exact sub_eq_zero.mp h
  have hq : ∀ q : S, δbar (Ideal.Quotient.mk J q) = 0 → Ideal.Quotient.mk J q = 0 := by
    intro q hq0
    have hδq : δ q = 0 := by rw [← hlifth q]; exact hq0
    let N := q.totalDegree
    let z : S := ∑ d ∈ Finset.range (N + 1),
      MvPolynomial.homogeneousComponent d q * MvPolynomial.X 0 ^ (N - d)
    have hz : z.IsHomogeneous N := by
      apply MvPolynomial.IsHomogeneous.sum
      intro d hd
      have h1 : ((MvPolynomial.X (0:Fin 5) : S) ^ (N - d)).IsHomogeneous (N - d) := by
        simpa using (MvPolynomial.isHomogeneous_X K (0:Fin 5)).pow (N - d)
      have h2 := (MvPolynomial.homogeneousComponent_isHomogeneous d q).mul h1
      rwa [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))] at h2
    have hδz : δ z = 0 := by
      have h1 : δ z = ∑ d ∈ Finset.range (N + 1),
          δ (MvPolynomial.homogeneousComponent d q) := by
        simp only [z, map_sum, map_mul, map_pow, hδX0, one_pow, mul_one]
      rw [h1, ← map_sum, MvPolynomial.sum_homogeneousComponent q, hδq]
    have hkey : algebraMap A L (Ideal.Quotient.mk I z) * y ^ N = 0 := by
      have h := key z N hz
      rw [hδz] at h
      exact h.symm
    have hyunit : IsUnit y :=
      IsUnit.of_mul_eq_one (algebraMap A L x) (by rw [mul_comm]; exact hyx)
    have hzero : algebraMap A L (Ideal.Quotient.mk I z) = 0 :=
      (IsUnit.mul_left_eq_zero (hyunit.pow N)).mp hkey
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers x) L (Ideal.Quotient.mk I z)).mp hzero
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (m : A) x).mp m.2
    have hmemI : MvPolynomial.X 0 ^ k * z ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 : Ideal.Quotient.mk I (MvPolynomial.X 0 ^ k * z)
          = x ^ k * Ideal.Quotient.mk I z := by
        rw [map_mul, map_pow]
      rw [h1, hk]
      exact hm
    have hmkJ : Ideal.Quotient.mk J (MvPolynomial.X 0 ^ k * z) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hmemI)
    have hmkz : Ideal.Quotient.mk J z = 0 := by
      rw [← hmkJ, map_mul, map_pow, hXJ, one_pow, one_mul]
    have hzp : Ideal.Quotient.mk J z = Ideal.Quotient.mk J q := by
      have h1 : Ideal.Quotient.mk J z = ∑ d ∈ Finset.range (N + 1),
          Ideal.Quotient.mk J (MvPolynomial.homogeneousComponent d q) := by
        simp only [z, map_sum, map_mul, map_pow, hXJ, one_pow, mul_one]
      rw [h1, ← map_sum, MvPolynomial.sum_homogeneousComponent q]
    rw [← hzp]
    exact hmkz
  have hinj : Function.Injective δbar := by
    intro a b hab
    have hab' : δbar (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨q, hq_eq⟩ := Ideal.Quotient.mk_surjective (a - b)
    have h0 : Ideal.Quotient.mk J q = 0 := hq q (by rw [hq_eq]; exact hab')
    exact sub_eq_zero.mp (hq_eq.symm.trans h0)
  haveI hAred : IsReduced A := (Ideal.isRadical_iff_quotient_reduced I).mp hIrad
  haveI : IsReduced L := inferInstance
  exact isReduced_of_injective δbar hinj

end Work.MotK.TGen
