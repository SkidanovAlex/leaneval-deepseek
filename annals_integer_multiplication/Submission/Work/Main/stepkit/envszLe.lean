import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.stepkit.paramSizes
import Submission.Work.Main.stepkit.ssprodLeTpar

namespace Work.Main.stepkit

/-- `isz` of a natural number, in terms of `Nat.size`. -/
theorem isz_natCast (m : ℕ) : HvdH.isz ((m : ℤ)) = m.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

/-- The total size of the parameter environment, expanded into its nine terms. -/
theorem envsz_eq (sp : SP) : envsz sp = HvdH.isz sp.S + HvdH.isz sp.N' + HvdH.isz sp.b + HvdH.isz sp.p
    + HvdH.isz sp.α + HvdH.vsz (HvdH.intList sp.ts) + HvdH.vsz (HvdH.intList sp.ss)
    + HvdH.isz sp.x + HvdH.isz sp.y := by
  simp [envsz, env]
  ring

theorem envszLe {n : ℕ} {sp : SP} (h : HvdH.ParamOK n sp.ts sp.ss)
    (hb : sp.b = HvdH.bpar n) (hp : sp.p = HvdH.ppar n) (ha : sp.α = HvdH.apar n)
    (hS : sp.S = sp.ss.prod) (hN : sp.N' = Work.Main.nchunks n (HvdH.bpar n))
    (hx : sp.x.size ≤ n) (hy : sp.y.size ≤ n)
    (hts : HvdH.vsz (HvdH.intList sp.ts) ≤ 115200 * (n.size + 1))
    (hss : HvdH.vsz (HvdH.intList sp.ss) ≤ 115200 * (n.size + 1)) :
    envsz sp ≤ 300000 * (n.size + 1) + 3 * n := by
  obtain ⟨hbs, hps, has_, hT, hncs⟩ := paramSizes n
  have hssT : sp.ss.prod ≤ HvdH.Tpar n := ssprodLeTpar h
  -- the size of `sp.S = ss.prod`, bounded by `Tpar n ≤ 2^(n.size+2)`
  have h1 : HvdH.isz sp.S ≤ n.size + 5 := by
    rw [hS, HvdH.isz, Int.natAbs_natCast]
    have hlt : sp.ss.prod < 2 ^ (n.size + 3) := by
      have hle : sp.ss.prod ≤ 2 ^ (n.size + 2) := le_trans hssT hT
      have hp2 : (2 : ℕ) ^ (n.size + 2) < 2 ^ (n.size + 3) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := (Nat.size_le).mpr hlt
    omega
  -- the size of `sp.N' = nchunks n b`
  have h2 : HvdH.isz sp.N' ≤ n.size + 3 := by
    rw [hN, HvdH.isz, Int.natAbs_natCast]
    omega
  -- the sizes of `b`, `p = 6b`, `α = apar n`
  have h3 : HvdH.isz sp.b ≤ n.size + 2 := by
    rw [hb, HvdH.isz, Int.natAbs_natCast]
    omega
  have h4 : HvdH.isz sp.p ≤ n.size + 6 := by
    rw [hp, HvdH.isz, Int.natAbs_natCast]
    omega
  have h5 : HvdH.isz sp.α ≤ n.size + 32 := by
    rw [ha, HvdH.isz, Int.natAbs_natCast]
    omega
  -- the operands: `sp.x` and `sp.y` have at most `n` bits
  have h6 : HvdH.isz sp.x ≤ n + 2 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    omega
  have h7 : HvdH.isz sp.y ≤ n + 2 := by
    rw [HvdH.isz, Int.natAbs_natCast]
    omega
  rw [envsz_eq]
  omega

end Work.Main.stepkit
