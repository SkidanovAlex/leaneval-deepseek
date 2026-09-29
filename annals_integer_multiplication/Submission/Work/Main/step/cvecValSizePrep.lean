import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.bridge
import Submission.Work.MainP.crtBijection
import Submission.Work.MainP.crtDefs
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.step.crtExtract

/-!
# Size of the prepared coefficient vector of the main step

`Work.Main.step.prep` produces, for `x` (and similarly `y`), a coefficient vector
`F : List (ℤ × ℤ)` of length `S = ∏ ss` such that

`F.getD (crtIdx ss m) (0,0) = pchunkZ x b N' S (p - b) m = (cᵐ · 2^{p-b}, 0)`

for every `m < S`, where `cᵐ = pchunk x b N' m < 2^b` is the `m`-th base-`2^b` chunk of `x`.

Since `crtIdx ss : [0, S) → [0, S)` is a bijection (the moduli are pairwise coprime and positive,
`Work.Main.step.crtIdx_surj`), *every* entry of `F` has the shape `(c · 2^{p-b}, 0)` with
`c < 2^b`, hence a real part of bit size `≤ b + (p - b) = p` (`b ≤ p`) and an imaginary part `0`.

Summing the per-entry sizes `vsz (cfxVal z) = isz z.1 + isz z.2 + 1 ≤ (p+2) + 2 + 1 = p + 5`
over the `S` entries and adding the `cons`-chain overhead gives

`vsz (cvecVal F) = Σ vsz (cfxVal z) + S + 1 ≤ S (p + 6) + 1 ≤ S (2p + 6) + 1`.
-/

set_option autoImplicit false

namespace Work.Main.step

open HvdH

/-- A base-`2^b` chunk (including the padding value `0`) is `< 2^b`. -/
theorem cvecValSize_pchunk_lt (x b N m : ℕ) : pchunk x b N m < 2 ^ b := by
  unfold pchunk
  split_ifs with h
  · exact Nat.mod_lt _ (pow_pos (by norm_num) _)
  · exact pow_pos (by norm_num) _

/-- `isz ((c : ℤ) * 2^k) ≤ p + 2` when `c < 2^b` and `b ≤ p`: the integer `c · 2^k` is the natural
number `c * 2^k < 2^b * 2^{p-b} = 2^p`, whose bit size is `≤ p`. -/
theorem cvecValSize_isz_mul_pow_le (c b p : ℕ) (hb : b ≤ p) (hc : c < 2 ^ b) :
    isz (((c : ℤ) * (2 : ℤ) ^ (p - b))) ≤ p + 2 := by
  have hnat : isz (((c : ℤ) * (2 : ℤ) ^ (p - b))) = (c * 2 ^ (p - b)).size + 2 := by
    simp [isz, Int.natAbs_mul, Int.natAbs_pow]
  rw [hnat]
  have hsize : (c * 2 ^ (p - b)).size ≤ p := by
    rw [Nat.size_le]
    calc c * 2 ^ (p - b) < 2 ^ b * 2 ^ (p - b) :=
          Nat.mul_lt_mul_of_pos_right hc (pow_pos (by norm_num) _)
      _ = 2 ^ p := by rw [← pow_add]; congr 1; omega
  omega

/-- Pointwise size bounds on a coefficient vector: if `isz z.1 ≤ p + 2` and `isz z.2 ≤ p + 2` for
every entry `z`, then `vsz (cvecVal zs) ≤ zs.length * (2 * p + 6) + 1`. -/
theorem cvecValSize_vsz_le (zs : List (ℤ × ℤ)) (p : ℕ)
    (h : ∀ z ∈ zs, isz z.1 ≤ p + 2 ∧ isz z.2 ≤ p + 2) :
    vsz (cvecVal zs) ≤ zs.length * (2 * p + 6) + 1 := by
  have hpt : ∀ z ∈ zs, vsz (cfxVal z) ≤ 2 * p + 5 := by
    intro z hz
    have h1 := (h z hz).1
    have h2 := (h z hz).2
    simp only [cfxVal]
    rw [Work.MainP.vsz_cons, Work.MainP.vsz_int, Work.MainP.vsz_int]
    omega
  rw [cvecVal, Work.MainP.vsz_ofList, List.length_map, List.map_map]
  have hsum : (zs.map (vsz ∘ cfxVal)).sum ≤ zs.length * (2 * p + 5) := by
    have hb := List.sum_le_length_nsmul (l := zs.map (vsz ∘ cfxVal)) (2 * p + 5) ?_
    · simpa using hb
    · intro a ha
      rw [List.mem_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      exact hpt z hz
  have key : zs.length * (2 * p + 6) = zs.length * (2 * p + 5) + zs.length := by ring
  rw [key]
  omega

theorem cvecValSizePrep {S N' b p : ℕ} {ss : List ℕ} {x : ℕ} {F : List (ℤ × ℤ)}
    (h1 : ∀ s ∈ ss, 1 ≤ s) (hcop : ss.Pairwise Nat.Coprime) (hS : S = ss.prod)
    (hbp : b ≤ p) (hFl : F.length = S)
    (hF : ∀ m < S, F.getD (HvdH.crtIdx ss m) (0,0) = Work.Main.pchunkZ x b N' S (p - b) m) :
    HvdH.vsz (HvdH.cvecVal F) ≤ S * (2 * p + 6) + 1 := by
  have hpos : ∀ s ∈ ss, 0 < s := fun s hs => Nat.lt_of_lt_of_le Nat.zero_lt_one (h1 s hs)
  -- every entry of `F` sits at a CRT index, hence is a scaled chunk
  have hpt : ∀ z ∈ F, isz z.1 ≤ p + 2 ∧ isz z.2 ≤ p + 2 := by
    intro z hz
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hz
    have hjS : j < S := by omega
    obtain ⟨m, hmS, hmj⟩ := crtIdx_surj hcop hpos (q := j) (by omega)
    have hmS' : m < S := by omega
    have hFj : F.getD j (0,0) = pchunkZ x b N' S (p - b) m := by
      rw [← hmj]
      exact hF m hmS'
    have hget : F.getD j (0,0) = z := by
      rw [List.getD_eq_getElem F (0,0) hj, hje]
    rw [hget.symm.trans hFj]
    simp only [pchunkZ]
    exact ⟨cvecValSize_isz_mul_pow_le _ b p hbp (cvecValSize_pchunk_lt x b N' m),
      by simp [isz]⟩
  have hgen := cvecValSize_vsz_le F p hpt
  rwa [hFl] at hgen

end Work.Main.step
