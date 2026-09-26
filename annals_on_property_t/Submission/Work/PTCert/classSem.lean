import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.CSAux
import Submission.Work.PTCert.CS.grepEDigits
import Submission.Work.PTCert.CS.gclsWitOKAll
import Submission.Work.PTCert.CS.tclsWitOKAll
import Submission.Work.PTCert.CS.iclsWitOKAll
import Submission.Work.PTCert.CS.classListFacts
import Submission.Work.PTCert.CS.multEKeyOf
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.cert1Aux

/-!
# PTCert — the semantics of the class-sum data (`ClassSem`)

`ClassSem` is the conjunction of nine facts about the emitted class data: the canonical words
(`canonW`), the class witnesses of the group keys / target pairs / inverses (`gcls`, `tcls`,
`icls`), the two class-grouped partitions of the keys and target pairs (`klist`, `tlist`), the
number of rows, and the multiplicities.

The witnesses come from the kernel checks `clsWitOK` (`Work.PTCert.clsWitSound` below turns a
passing check on a 4-letter word into a conjugacy statement), the partitions and the symbol bounds
from the `classKeysOK` / `isPermOf` / `canonOK` checks, and the multiplicities from `multOK`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable section

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## Soundness of the class-witness check -/

/-- **Soundness of the class-witness check.**  If the check passes on a 4-letter word `w` of letters
`< 81` and a packed witness `v` whose class index is a valid class, then the product of the letters
of `w` is conjugated into the canonical word of the class. -/
theorem clsWitSound (hCF : CodeFacts) (w : List ℕ) (v : ℕ)
    (hw4 : w.length = 4) (hw81 : ∀ k ∈ w, k < 81) (hv : v / 1048576 < 7229)
    (h : clsWitOK canonT w v = true) :
    ∃ σ ∈ SigmaSet 5, σ * lprod 5 w * σ⁻¹ = lprod 5 (canonW (v / 1048576)) := by
  have h' := h
  simp only [clsWitOK] at h'
  set code := v % 1048576 with hcode
  set cw := kG canonT (v / 1048576) with hcw
  set sw := w.map (fun k => actL 5 (code / 32) (code % 32) k) with hsw
  rw [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h'
  obtain ⟨hvalid, hor⟩ := h'
  have hsw81 : ∀ k ∈ sw, k < 81 := by
    intro k hk
    rw [hsw, List.mem_map] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    exact ((hCF.1 code hvalid).2 a (hw81 a ha)).1
  have hunpcw : unpack4 cw = canonW (v / 1048576) := rfl
  have hcw81 : ∀ k ∈ unpack4 cw, k < 81 := by
    intro k hk
    rw [hunpcw] at hk
    exact canonW_lt (v / 1048576) hv k hk
  have hconj : codeElt code * lprod 5 w * (codeElt code)⁻¹ = lprod 5 sw :=
    lprod_conj hCF code hvalid w hw81
  refine ⟨codeElt code, (hCF.1 code hvalid).1, ?_⟩
  rw [hconj]
  rcases hor with hpack | hmodel
  · have hsw4 : sw.length = 4 := by rw [hsw, List.length_map, hw4]
    have hunp : canonW (v / 1048576) = sw := by
      rw [show canonW (v / 1048576) = unpack4 cw from rfl, ← hpack]
      exact unpack4_pack4 sw hsw4 (fun k hk => by have h := hsw81 k hk; omega)
    rw [hunp]
  · exact modelSound 5 sw (unpack4 cw)
      (fun k hk => by rw [NB1_five]; exact hsw81 k hk)
      (fun k hk => by rw [NB1_five]; exact hcw81 k hk) hmodel

/-! ## Small data facts -/

theorem ngL_length : ngL.length = 18 := by decide +kernel

theorem mem_allKeys_iff {k : ℕ} : k ∈ allKeys ngL ↔ ∃ r < 18, ∃ g < ngE r, k = keyOf r g := by
  have hlen : ngL.length = 18 := ngL_length
  unfold allKeys
  rw [hlen, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hg⟩
    rw [List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    rw [List.mem_range] at hr hg
    exact ⟨r, hr, g, hg, rfl⟩
  · rintro ⟨r, hr, g, hg, rfl⟩
    exact ⟨r, List.mem_range.mpr hr, List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩⟩

/-- The two digits of a row code are `< 81`. -/
theorem x0c_digits (r : ℕ) (hr : r < 18) : x0c r / 128 < 81 ∧ x0c r % 128 < 81 := by
  rw [show x0c r = x0cL.getD r 0 from x0c_val r hr]
  interval_cases r <;> decide +kernel

theorem keyWord_len (r g : ℕ) : (keyWord r g).length = 4 := rfl

/-- The letters of a key word are `< 81`. -/
theorem keyWord_lt (r g : ℕ) (hr : r < 18) (hg : g < ngE r) :
    ∀ k ∈ keyWord r g, k < 81 := by
  have hx := x0c_digits r hr
  have hgd := CS.grepEDigits r hr g hg
  intro k hk
  have hk' : k = invL (x0c r % 128) ∨ k = invL (x0c r / 128) ∨
      k = grepE r g / 128 ∨ k = grepE r g % 128 := by
    simpa [keyWord] using hk
  rcases hk' with rfl | rfl | rfl | rfl
  · exact invL_lt_81 _ hx.2
  · exact invL_lt_81 _ hx.1
  · exact hgd.2.2
  · exact hgd.2.1

/-- Every class of `iclT` is a class index `< ncls`. -/
theorem icls_bound : ∀ c < 7229, w34 iclT c / 1048576 < 7229 := by decide +kernel

/-! ## Assembling `ClassSem` -/

theorem classSem (hCF : CodeFacts) : ClassSem := by
  obtain ⟨hklen, htlen, hkperm, htperm, hkgcls, httcls⟩ := CS.classListFacts
  have hgcls_lt : ∀ r < 18, ∀ g < ngE r, gcls (keyOf r g) < ncls := by
    intro r hr g hg
    have hk : keyOf r g ∈ allKeys ngL := mem_allKeys_iff.mpr ⟨r, hr, g, hg, rfl⟩
    have hk' : keyOf r g ∈ klist.flatten := hkperm.mem_iff.mpr hk
    obtain ⟨c, hc, hmem⟩ := mem_flatten_getD hk'
    have hcn : c < ncls := by rwa [hklen] at hc
    rw [hkgcls c hcn (keyOf r g) hmem]
    exact hcn
  have htcls_lt : ∀ p < 6561, tcls p < ncls := by
    intro p hp
    have hp' : p ∈ tlist.flatten := htperm.mem_iff.mpr (List.mem_range.mpr hp)
    obtain ⟨c, hc, hmem⟩ := mem_flatten_getD hp'
    have hcn : c < ncls := by rwa [htlen] at hc
    rw [httcls c hcn p hmem]
    exact hcn
  refine ⟨?_, ?_, ?_, ?_, hklen, htlen, hkperm, htperm, hkgcls, httcls, ngL_length, ?_⟩
  · intro c hc
    exact ⟨canonW_len c, canonW_lt c (by simpa [ncls] using hc)⟩
  · intro r hr g hg
    have hlt := hgcls_lt r hr g hg
    refine ⟨hlt, ?_⟩
    obtain ⟨σ, hσ, heq⟩ := clsWitSound hCF (keyWord r g) (w34 gclT (keyOf r g))
      (keyWord_len r g) (keyWord_lt r g hr hg) (by simpa [gcls, ncls] using hlt)
      (CS.gclsWitOKAll r hr g hg)
    exact ⟨σ, hσ, heq⟩
  · intro p hp
    have hlt := htcls_lt p hp
    refine ⟨hlt, ?_⟩
    have hw : ∀ k ∈ ([invL (p / 81), p % 81, 0, 0] : List ℕ), k < 81 := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact invL_lt_81 _ (by rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 81)]; omega)
      · exact Nat.mod_lt _ (by norm_num)
      · exact by norm_num
      · exact by norm_num
    have hlen : (([invL (p / 81), p % 81, 0, 0] : List ℕ)).length = 4 := rfl
    obtain ⟨σ, hσ, heq⟩ := clsWitSound hCF _ (w34 tclT p) hlen hw
      (by simpa [tcls, ncls] using hlt) (CS.tclsWitOKAll p hp)
    exact ⟨σ, hσ, heq⟩
  · intro c hc
    have hc7 : c < 7229 := by simpa [ncls] using hc
    have hlt : icls c < ncls := by simpa [icls, ncls] using icls_bound c hc7
    refine ⟨hlt, ?_⟩
    have hw : ∀ k ∈ ((canonW c).reverse.map invL), k < 81 := by
      intro k hk
      rw [List.mem_map] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [List.mem_reverse] at ha
      exact invL_lt_81 a (canonW_lt c hc7 a ha)
    have hlen : ((canonW c).reverse.map invL).length = 4 := by
      rw [List.length_map, List.length_reverse, canonW_len c]
    obtain ⟨σ, hσ, heq⟩ := clsWitSound hCF _ (w34 iclT c) hlen hw
      (by simpa [icls, ncls] using hlt) (CS.iclsWitOKAll c hc)
    rw [lprod_inv (canonW c) (canonW_lt c hc7)] at heq
    exact ⟨σ, hσ, heq⟩
  · intro r hr g hg
    exact CS.multEKeyOf r hr g hg

end Work.PTCert

end
