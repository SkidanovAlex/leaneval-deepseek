import Mathlib
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.KummerAux

open scoped Classical
open IntermediateField

/-- Bézout in the form needed below: if `p` is prime and `p ∤ n`, there are `t c : ℤ`
with `t * n + c * p = 1`.  Obtained by inverting `n` in the field `ZMod p`. -/
private lemma exists_bezout_of_not_dvd (p : ℕ) (hp : p.Prime) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) : ∃ t c : ℤ, t * n + c * (p : ℤ) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h)
  obtain ⟨T, hT⟩ : ∃ T : ℤ, (T : ZMod p) = (n : ZMod p)⁻¹ := ZMod.intCast_surjective _
  have hTn : ((T * n : ℤ) : ZMod p) = 1 := by
    rw [Int.cast_mul, hT, inv_mul_cancel₀ hn0]
  have hdvd : (p : ℤ) ∣ 1 - T * n := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub (T * n) 1 p).mp
    simpa using hTn
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨T, c, ?_⟩
  rw [mul_comm T n] at hc
  linarith

/-- **Key computation.**  If `A ≠ 0` in `K'` and `α ^ p = A ^ n`, then with `t * n + c * p = 1`
the element `β = α ^ t * A ^ c` is a `p`-th root of `A`:  `β ^ p = A`. -/
private lemma zpow_mul_zpow_pow_eq {K' : Type*} [Field K'] {A α : K'} (hA : A ≠ 0)
    {p : ℕ} {n t c : ℤ} (hα : α ^ p = A ^ n) (htc : t * n + c * (p : ℤ) = 1) :
    (α ^ t * A ^ c) ^ p = A := by
  calc (α ^ t * A ^ c) ^ p
      = (α ^ t * A ^ c) ^ (p : ℤ) := by rw [zpow_natCast]
    _ = (α ^ t) ^ (p : ℤ) * (A ^ c) ^ (p : ℤ) := mul_zpow _ _ _
    _ = α ^ (t * (p : ℤ)) * A ^ (c * (p : ℤ)) := by rw [← zpow_mul, ← zpow_mul]
    _ = (α ^ (p : ℤ)) ^ t * A ^ (c * (p : ℤ)) := by
          rw [mul_comm t (p : ℤ),
              show α ^ ((p : ℤ) * t) = (α ^ (p : ℤ)) ^ t from zpow_mul α (p : ℤ) t]
    _ = (A ^ n) ^ t * A ^ (c * (p : ℤ)) := by
          rw [show α ^ (p : ℤ) = A ^ n from by rw [zpow_natCast, hα]]
    _ = A ^ (n * t) * A ^ (c * (p : ℤ)) := by
          rw [show (A ^ n) ^ t = A ^ (n * t) from (zpow_mul A n t).symm]
    _ = A ^ (n * t + c * (p : ℤ)) := by rw [← zpow_add₀ hA]
    _ = A := by rw [show n * t + c * (p : ℤ) = 1 from by rw [mul_comm n t]; exact htc, zpow_one]

/-- **Key computation, second form.**  If `α ≠ 0` in `K'` and `α ^ p = A ^ n`, then with
`t * n + c * p = 1` the element `β = α ^ t * A ^ c` satisfies `α = β ^ n`:  the
`n`-th power map is inverse to the construction above, so `α` is a rational
expression in the `p`-th root `β` of `A` and in `A`. -/
private lemma zpow_eq_pow_of_zpow_mul_zpow {K' : Type*} [Field K'] {A α : K'} (hα0 : α ≠ 0)
    {p : ℕ} {n t c : ℤ} (hα : α ^ p = A ^ n) (htc : t * n + c * (p : ℤ) = 1) :
    α = (α ^ t * A ^ c) ^ n := by
  have hb : (α ^ t * A ^ c) ^ n = α := by
    calc (α ^ t * A ^ c) ^ n
        = (α ^ t) ^ n * (A ^ c) ^ n := mul_zpow _ _ _
      _ = α ^ (t * n) * A ^ (c * n) := by rw [← zpow_mul, ← zpow_mul]
      _ = α ^ (t * n) * A ^ (n * c) := by rw [mul_comm c n]
      _ = α ^ (t * n) * (A ^ n) ^ c := by
            rw [show A ^ (n * c) = (A ^ n) ^ c from zpow_mul A n c]
      _ = α ^ (t * n) * (α ^ (p : ℤ)) ^ c := by
            rw [show A ^ n = α ^ (p : ℤ) from by rw [zpow_natCast, hα]]
      _ = α ^ (t * n) * α ^ ((p : ℤ) * c) := by
            rw [show (α ^ (p : ℤ)) ^ c = α ^ ((p : ℤ) * c) from (zpow_mul α (p : ℤ) c).symm]
      _ = α ^ (t * n) * α ^ (c * (p : ℤ)) := by rw [mul_comm (p : ℤ) c]
      _ = α ^ (t * n + c * (p : ℤ)) := by rw [← zpow_add₀ hα0]
      _ = α := by rw [htc, zpow_one]
  exact hb.symm

theorem kummerField_zpow_eq_of_not_dvd {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {a : kˣ} {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) :
    kummerField (K' := K') p (a ^ n) = kummerField (K' := K') p a := by
  obtain ⟨t, c, htc⟩ := exists_bezout_of_not_dvd p hp n hn
  set A : K' := algebraMap k K' (a : k) with hA_def
  have hA0 : A ≠ 0 := by
    rw [hA_def]
    exact (map_ne_zero (algebraMap k K')).mpr (Units.ne_zero a)
  have hAzn : ∀ m : ℤ, algebraMap k K' ((a ^ m : kˣ) : k) = A ^ m := by
    intro m
    rw [hA_def, Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ (algebraMap k K') (a : k) m
  refine le_antisymm ?_ ?_
  · -- `kummerField p (a ^ n) ≤ kummerField p a`
    rw [NK.LocalAnabelian.kummerField_le_iff]
    intro α hα
    rw [hAzn n] at hα
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, zero_pow hp.pos.ne'] at hα
      exact zpow_ne_zero n hA0 hα.symm
    have hβp : (α ^ t * A ^ c) ^ p = A :=
      zpow_mul_zpow_pow_eq hA0 hα htc
    have hβmem : (α ^ t * A ^ c) ∈ kummerField (K' := K') p a :=
      NK.LocalAnabelian.mem_kummerField_of_pow_eq hβp
    have hαeq : α = (α ^ t * A ^ c) ^ n :=
      zpow_eq_pow_of_zpow_mul_zpow hα0 hα htc
    rw [hαeq]
    exact IntermediateField.pow_mem _ hβmem n
  · -- `kummerField p a ≤ kummerField p (a ^ n)`
    rw [NK.LocalAnabelian.kummerField_le_iff]
    intro α hα
    have hαA : α ^ p = A := by rw [hA_def]; exact hα
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, zero_pow hp.pos.ne'] at hαA
      exact hA0 hαA.symm
    have hγpow : (α ^ n) ^ p = A ^ n := by
      calc (α ^ n) ^ p
          = (α ^ n) ^ (p : ℤ) := by rw [zpow_natCast]
        _ = α ^ (n * (p : ℤ)) := (zpow_mul α n (p : ℤ)).symm
        _ = α ^ ((p : ℤ) * n) := by rw [mul_comm n (p : ℤ)]
        _ = (α ^ (p : ℤ)) ^ n := zpow_mul α (p : ℤ) n
        _ = A ^ n := by rw [show α ^ (p : ℤ) = A from by rw [zpow_natCast, hαA]]
    have hγmem : α ^ n ∈ kummerField (K' := K') p (a ^ n) :=
      NK.LocalAnabelian.mem_kummerField_of_pow_eq (by rw [hγpow, hAzn n])
    have hαeq : α = (α ^ n) ^ t * A ^ c := by
      calc α = α ^ (t * n + c * (p : ℤ)) := by rw [htc, zpow_one]
        _ = α ^ (t * n) * α ^ (c * (p : ℤ)) := zpow_add₀ hα0 _ _
        _ = (α ^ n) ^ t * (α ^ (p : ℤ)) ^ c := by
              rw [mul_comm t n, show α ^ (n * t) = (α ^ n) ^ t from zpow_mul α n t,
                  show α ^ (c * (p : ℤ)) = (α ^ (p : ℤ)) ^ c from by
                    rw [mul_comm c (p : ℤ), zpow_mul]]
        _ = (α ^ n) ^ t * A ^ c := by
              rw [show α ^ (p : ℤ) = A from by rw [zpow_natCast, hαA]]
    rw [hαeq]
    refine IntermediateField.mul_mem _ (IntermediateField.pow_mem _ hγmem t) ?_
    rw [hA_def]
    exact IntermediateField.pow_mem _ (IntermediateField.algebraMap_mem _ _) c

end NK.LocalAnabelian.KummerAux
