import Mathlib
import Submission.Work.SGsep.symAux.defs

/-!
# `Work.SGsep.symAux.symChk_dvd`

The coordinate form of the first (soundness) half of the `sym` certificate check of
`Data.SymCert.chk`: if `chk k a` holds, then `1 ≤ a.o` and for every generator `g` of the
arithmetic class of `k` the *integer* vector

`σ - A_g σ - (a.o · n) · z_g`   (`σ = a.sig`, `A_g = GK k g`, `z_g = zK k (geni k g)`,
`n = nK k`) is divisible by `n²` coordinatewise.  Here `a.sig` is the numerator of the
coboundary potential `σ/n² = symSig k a`, `z_g = n · τ(g)` and `a.o · τ` is the coboundary:
the check certifies `a.sig - A_g a.sig = a.o · n · z_g  (mod n²)`.
-/

namespace Work.SGsep.symAux

open Work.SG Work.SGsep

/-- Coordinate form of `Data.V3.dvd`. -/
theorem V3_dvd_iff (m : ℤ) (v : Data.V3) :
    Data.V3.dvd m v = true ↔ m ∣ v.x ∧ m ∣ v.y ∧ m ∣ v.z := by
  simp only [Data.V3.dvd, Bool.and_eq_true, beq_iff_eq, Int.dvd_iff_emod_eq_zero]
  tauto

theorem symChk_dvd (k : Fin 230) (a : Data.SymCert) (ha : Data.SymCert.chk k.val a = true) :
    1 ≤ a.o ∧ ∀ g, g < kK k → ∀ c : Fin 3,
      ((nK k : ℤ)) ^ 2 ∣
        (a.sig.toFun c - ((GK k g).mulVec a.sig.toFun) c)
          - (((a.o : ℤ) * (nK k)) * (zK k (geni k g)).toFun c) := by
  -- `1 ≤ a.o` and the divisibility are the first two conjuncts of `Data.SymCert.chk`.
  have hpos : 1 ≤ a.o := by
    have h := ha
    unfold Data.SymCert.chk at h
    simp only [Bool.and_eq_true] at h
    exact of_decide_eq_true h.1.1.1
  refine ⟨hpos, ?_⟩
  have hh := ha
  unfold Data.SymCert.chk at hh
  simp only [Bool.and_eq_true] at hh
  have hall := hh.1.1.2
  intro g hg c
  have hmem : g < (Data.repArith k.val).gens.length := by simpa only [kK, Dk] using hg
  have hd := (List.all_eq_true.mp hall) g (List.mem_range.mpr hmem)
  rw [V3_dvd_iff] at hd
  -- the `Data.V3` obstruction is the one of the certificate, read in coordinates:
  -- `A_g.toIMat.mulVec σ = (A_g.mulV σ).toFun`, `V3.smul` is multiplication, and `σ = a.sig`.
  have key : (Data.V3.sub (Data.V3.sub a.sig (Data.M3.mulV ((Data.repArith k.val).gens.getD g Data.M3.one) a.sig))
      (Data.V3.smul ((a.o : ℤ) * (Data.repArith k.val).n)
        ((Data.repZ.getD k.val []).getD ((Data.repArith k.val).genIdx.getD g 0) Data.V3.zero))).toFun c
      = (a.sig.toFun c - ((GK k g).mulVec a.sig.toFun) c)
          - (((a.o : ℤ) * (nK k)) * (zK k (geni k g)).toFun c) := by
    rw [Data.V3.toFun_sub, Data.V3.toFun_sub, Data.V3.toFun_smul, ← Data.M3.toIMat_mulV]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← key, pow_two]
  fin_cases c
  · exact hd.1
  · exact hd.2.1
  · exact hd.2.2

end Work.SGsep.symAux
