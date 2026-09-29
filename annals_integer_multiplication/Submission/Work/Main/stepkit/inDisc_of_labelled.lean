import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.bridge
import Submission.Work.Main.crt.Pinv_spec

/-!
# Every entry of the labelled chunk list lies in the disc

The preparation stage of the main step writes the fixed-point values of the chunks of `x` into
the flat (Agarwal–Cooley) order: the entry at flat index `HvdH.crtIdx ss m` is the `m`-th padded
chunk, scaled by `2 ^ (p - b)`.  This file shows that *every* entry of the resulting list `F` of
length `∏ ss` is a point of the disc `HvdH.inDisc p` (i.e. `z.1 ^ 2 + z.2 ^ 2 ≤ 4 ^ p`), which is
the side condition of all the transform/library specs downstream.

Two ingredients:

* `inDisc_pchunkZ'` — a labelled chunk `((c : ℤ) * 2 ^ (p - b), 0)` with `c < 2 ^ b` and `b ≤ p`
  satisfies `z.1 ^ 2 + z.2 ^ 2 ≤ 4 ^ p`, because `z.1 = c * 2 ^ (p - b) < 2 ^ p`;
* `exists_crtIdx_eq` — the flat CRT reindexing is surjective on `[0, ∏ ss)`
  (`Pinv_spec`: `crtIdx` is a bijection of `Fin ss.prod` for pairwise coprime positive moduli),
  so the index `i < F.length` of any member `z` of `F` is of the form `crtIdx ss m` with
  `m < ss.prod`; the labelling hypothesis `hF` then identifies `z` with the `m`-th chunk.
-/

set_option autoImplicit false

namespace Work.Main.stepkit

open Work.Main

/-- A chunk is a `b`-bit number. -/
lemma pchunk_lt_two_pow (x b N m : ℕ) : pchunk x b N m < 2 ^ b := by
  unfold pchunk
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos b)
  · exact Nat.two_pow_pos b

/-- `(a * 2 ^ k) ^ 2 ≤ 4 ^ (b + k)` for a `b`-bit number `a`. -/
lemma sq_mul_pow_two_le (a b k : ℕ) (ha : a < 2^b) : (a * 2^k)^2 ≤ 4^(b+k) := by
  have ha' : a^2 ≤ 2^(2*b) := by
    calc a^2 ≤ (2^b)^2 := Nat.pow_le_pow_left (le_of_lt ha) 2
      _ = 2^(b*2) := by rw [pow_mul]
      _ = 2^(2*b) := by ring_nf
  calc (a * 2^k)^2 = a^2 * (2^k)^2 := by rw [mul_pow]
    _ = a^2 * 2^(k*2) := by rw [pow_mul]
    _ ≤ 2^(2*b) * 2^(k*2) := Nat.mul_le_mul_right _ ha'
    _ = 2^(2*b + k*2) := (pow_add 2 (2*b) (k*2)).symm
    _ = 2^(2*(b+k)) := by congr 1; ring
    _ = 4^(b+k) := by rw [show (4:ℕ) = 2^2 from rfl, pow_mul]

/-- The labelled chunk of `x` at scale `2 ^ (p - b)` is a point of the disc `inDisc p`. -/
lemma inDisc_pchunkZ' {x b N' S p m : ℕ} (hb : b ≤ p) :
    HvdH.inDisc p (pchunkZ x b N' S (p - b) m) := by
  have ha : pchunk x b N' m < 2^b := pchunk_lt_two_pow x b N' m
  have key : (pchunk x b N' m * 2^(p-b))^2 ≤ 4^p := by
    have h := sq_mul_pow_two_le (pchunk x b N' m) b (p-b) ha
    rwa [Nat.add_sub_of_le hb] at h
  have h1 : ((pchunk x b N' m : ℤ) * (2:ℤ)^(p-b))
      = ((pchunk x b N' m * 2^(p-b) : ℕ) : ℤ) := by push_cast; ring
  have h2 : ((4:ℤ)^p) = ((4^p : ℕ) : ℤ) := by push_cast; ring
  unfold HvdH.inDisc pchunkZ pchunkN
  rw [h1, h2]
  norm_num
  exact_mod_cast key

/-- The flat CRT reindexing is surjective on `[0, ∏ ss)` for positive pairwise coprime moduli. -/
lemma exists_crtIdx_eq {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {i : ℕ} (hi : i < ss.prod) :
    ∃ m < ss.prod, HvdH.crtIdx ss m = i := by
  obtain ⟨h1, h2⟩ := crt.Pinv_spec hcop hpos hi
  refine ⟨Pinv ss i, h1, ?_⟩
  rw [← Pcr_eq_crtIdx ss (Pinv ss i), h2]

/-- **Every entry of the labelled chunk list is in the disc.**  `F` is a list of `∏ ss` fixed
point values whose `HvdH.crtIdx ss m`-th entry is the `m`-th padded chunk of `x` scaled by
`2 ^ (p - b)`; then all its entries satisfy `inDisc p`. -/
theorem inDisc_of_labelled {ss : List ℕ} {F : List (ℤ × ℤ)} {p b N' x : ℕ}
    (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    (hlen : F.length = ss.prod) (hb : b ≤ p)
    (hF : ∀ m < ss.prod, F.getD (HvdH.crtIdx ss m) (0,0) = pchunkZ x b N' ss.prod (p - b) m) :
    ∀ z ∈ F, HvdH.inDisc p z := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hi' : i < ss.prod := by rw [← hlen]; exact hi
  obtain ⟨m, hm, hcm⟩ := exists_crtIdx_eq hcop hpos hi'
  have hget : F.getD i (0,0) = F[i] := List.getD_eq_getElem F (0,0) hi
  rw [← hget, ← hcm, hF m hm]
  exact inDisc_pchunkZ' hb

end Work.Main.stepkit
