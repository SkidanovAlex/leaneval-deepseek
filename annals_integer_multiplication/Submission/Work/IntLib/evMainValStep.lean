import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunksAPI
import Submission.Work.IntLib.evalChunksArith

namespace Work.IntLib

theorem evMainValStep {hs : List ℕ} {b j h : ℕ} {tl : List ℕ} {W LO W' LO' : List Bool}
    (hd : hs.drop j = h :: tl) (hval : evVal hs b j W LO)
    (hLO : LO'.length = LO.length + b)
    (hLOv : ofBits LO' = ofBits LO + 2 ^ LO.length * ((ofBits W + h) % 2 ^ b))
    (hWv : ofBits W' = (ofBits W + h) / 2 ^ b)
    (hWlen : W'.length ≤ 3 * b + 1) : evVal hs b (j + 1) W' LO' := by
  obtain ⟨hLOlen, hWlen0, hmain⟩ := hval
  have hj : j < hs.length := by
    have h2 : (hs.drop j).length = hs.length - j := List.length_drop
    have h1 : 1 ≤ (hs.drop j).length := by rw [hd]; simp
    omega
  have hgetD : hs.getD j 0 = h := by
    have h1 : (hs.drop j).getD 0 0 = h := by rw [hd]; simp
    rw [ecArith_getD_drop hs j] at h1
    exact h1
  have htake : HvdH.evalChunks (hs.take (j + 1)) b
      = HvdH.evalChunks (hs.take j) b + 2 ^ (b * j) * h := by
    rw [ecArith_take_succ hs b j hj, hgetD]
  have hpm : (ofBits W + h) % 2 ^ b + 2 ^ b * ((ofBits W + h) / 2 ^ b) = ofBits W + h := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod _ _
  rw [hLOlen] at hmain
  refine ⟨?_, hWlen, ?_⟩
  · rw [hLO, hLOlen]
    ring
  · rw [htake, hLOv, hWv, hLO, pow_add, hLOlen, ← hmain]
    calc (ofBits LO + 2 ^ (b * j) * ((ofBits W + h) % 2 ^ b))
          + (2 ^ (b * j) * 2 ^ b) * ((ofBits W + h) / 2 ^ b)
        = ofBits LO + (2 ^ (b * j) * ((ofBits W + h) % 2 ^ b)
            + 2 ^ (b * j) * (2 ^ b * ((ofBits W + h) / 2 ^ b))) := by ring
      _ = ofBits LO + 2 ^ (b * j) *
            ((ofBits W + h) % 2 ^ b + 2 ^ b * ((ofBits W + h) / 2 ^ b)) := by
            rw [Nat.mul_add]
      _ = ofBits LO + 2 ^ (b * j) * (ofBits W + h) := by rw [hpm]
      _ = ofBits LO + (2 ^ (b * j) * ofBits W + 2 ^ (b * j) * h) := by rw [Nat.mul_add]
      _ = (ofBits LO + 2 ^ (b * j) * ofBits W) + 2 ^ (b * j) * h := by ring

end Work.IntLib
