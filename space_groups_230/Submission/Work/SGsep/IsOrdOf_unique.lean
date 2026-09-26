import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.zsmul_gcd_mem
import Submission.Work.SGsep.IsOrdOf_eq_of_dvd_smul_mem

namespace Work.SGsep

open Work.SG

/-- The set `{k : ℤ | k • u ∈ L}` is an additive subgroup of `ℤ`, and `IsOrdOf L u m` says that
`m` generates it positively.  Consequently `m` is the *least* positive element of that subgroup:
for every positive `k` with `k • u ∈ L` we have `m ≤ k`.

Proof: with `d = gcd m |k|`, Bézout writes `d = a·m + b·|k|`, so `d • u ∈ L`
(`zsmul_gcd_mem`); if `d` were a proper divisor of `m` we would get an element strictly between
`0` and `m` (`IsOrdOf_eq_of_dvd_smul_mem`), so `d = m` divides `k` and `m ≤ k`. -/
theorem IsOrdOf_unique {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {o o' : ℕ}
    (h : IsOrdOf L v o) (h' : IsOrdOf L v o') : o = o' := by
  have key : ∀ (m : ℕ) (u : Fin 3 → ℝ), IsOrdOf L u m → ∀ k : ℤ, 0 < k → k • u ∈ L →
      (m : ℤ) ≤ k := by
    intro m u hm k hkpos hk
    have hmpos : 0 < m := by have := hm.1; omega
    -- Bézout: `gcd m |k|` still scales `u` into `L`
    have hdS : ((Nat.gcd m k.natAbs : ℕ) : ℤ) • u ∈ L := zsmul_gcd_mem hm.2.1 hk
    -- a positive divisor `d` of `m` with `d • u ∈ L` must be `m` itself
    have hdvd : Nat.gcd m k.natAbs ∣ m := Nat.gcd_dvd_left m k.natAbs
    have hdpos : 0 < Nat.gcd m k.natAbs := Nat.gcd_pos_of_pos_left k.natAbs hmpos
    have hdm : Nat.gcd m k.natAbs = m := IsOrdOf_eq_of_dvd_smul_mem hm hdvd hdpos hdS
    have hmdv : m ∣ k.natAbs := hdm ▸ Nat.gcd_dvd_right m k.natAbs
    have hkle : m ≤ k.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt hkpos)) hmdv
    calc (m : ℤ) ≤ (k.natAbs : ℤ) := by exact_mod_cast hkle
      _ = k := Int.natAbs_of_nonneg (le_of_lt hkpos)
  have hle1 : (o : ℤ) ≤ (o' : ℤ) := key o v h (o' : ℤ) (by have := h'.1; omega) h'.2.1
  have hle2 : (o' : ℤ) ≤ (o : ℤ) := key o' v h' (o : ℤ) (by have := h.1; omega) h.2.1
  exact Int.ofNat_inj.mp (le_antisymm hle1 hle2)

end Work.SGsep
