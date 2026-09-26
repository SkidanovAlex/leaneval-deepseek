import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellStabDefs
import Submission.Work.SG.SellStabData
import Submission.Work.SG.Data.SellCheck
import Submission.Work.SG.arithRep_eq_data
import Submission.Work.SG.mem_stabCands
import Submission.Work.SG.mem_boxVecs
import Submission.Work.SG.chkJoin_full
import Submission.Work.SG.chkJoin_ref
import Submission.Work.SG.joinReps_mem
import Submission.Work.SG.isIntPointGroup_inv

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md and Submission/Work/SG/Data/DATA.md first (orchestrator design + certificate data). Shared defs: Submission/Work/SG/Defs.lean (namespace Work.SG); data modules Submission/Work/SG/Data/* -- do NOT edit any of them. Certificate checks use kernel decide only (no native_decide). Siblings run in parallel.

# conj_to_arithRep -- 73 arithmetic classes (computational)

**Claim.** Every point group `H ⊆ sellingStab (sellingGraph i)` is `SL₃(ℤ)`-conjugate to some
`arithRep j`.

The proof goes through the kernel-checked Selling certificate `Work.SG.Data.sellData`:
* `Work.SG.CZ.sellingStab_eq`: the stabiliser is exactly the image of the table `stab`;
* the index set `F = {a | mat a ∈ H}` is closed under the table product `gmul` and contains
  `one`, so by the completeness certificate `joins` (unpacked in
  `Work.SG.chkJoin_full`/`Work.SG.chkJoin_ref`, consumed by `Work.SG.joinReps_mem`) it is
  *exactly* one of the listed subgroups `subs`;
* the conjugator `conj[s]` of that subgroup (`Work.SG.CZ.chkConj_zip`) then exhibits `H` as
  `U (arithRep j) U⁻¹` with `U` of determinant `1`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

namespace CZ

theorem sell_vecs_all (i : Fin 6) : (Sof i).chkVecs i.val = true := by
  fin_cases i
  · exact Data.sell_vecs_0
  · exact Data.sell_vecs_1
  · exact Data.sell_vecs_2
  · exact Data.sell_vecs_3
  · exact Data.sell_vecs_4
  · exact Data.sell_vecs_5

theorem sell_stab_all (i : Fin 6) : (Sof i).chkStab = true := by
  fin_cases i
  · exact Data.sell_stab_0
  · exact Data.sell_stab_1
  · exact Data.sell_stab_2
  · exact Data.sell_stab_3
  · exact Data.sell_stab_4
  · exact Data.sell_stab_5

theorem sell_conj_all (i : Fin 6) : (Sof i).chkConj = true := by
  fin_cases i
  · exact Data.sell_conj_0
  · exact Data.sell_conj_1
  · exact Data.sell_conj_2
  · exact Data.sell_conj_3
  · exact Data.sell_conj_4
  · exact Data.sell_conj_5

theorem vecs_eq (i : Fin 6) : (Sof i).vecs = Data.boxVecs (sellingGraph i) := by
  have h := sell_vecs_all i
  simp only [Data.SellData.chkVecs] at h
  exact beq_iff_eq.mp h

theorem stab_eq_cands (i : Fin 6) : (Sof i).stab = Data.stabCands (Sof i).vecs := by
  have h := sell_stab_all i
  simp only [Data.SellData.chkStab] at h
  exact beq_iff_eq.mp h

/-- Auxiliary bound: the superbase coordinates of a standard basis vector differ by at most 1
on any pair of vertices. -/
theorem abs_cons0_single_le (e : Fin 4 × Fin 4) (k : Fin 3) :
    |(Fin.cons (0 : ℤ) (Pi.single k (1 : ℤ)) : Fin 4 → ℤ) e.1 -
      (Fin.cons (0 : ℤ) (Pi.single k (1 : ℤ)) : Fin 4 → ℤ) e.2| ≤ 1 := by
  revert e
  fin_cases k <;> decide

/-- The standard basis vectors are coset-minimal for every graph. -/
theorem single_mem_sellingVecs (E : List (Fin 4 × Fin 4)) (k : Fin 3) :
    (Pi.single k (1 : ℤ)) ∈ sellingVecs E := by
  constructor
  · intro h
    have hk : (1 : ℤ) = 0 := by simpa using congrFun h k
    exact one_ne_zero hk
  · intro e _
    exact abs_cons0_single_le e k

theorem cols_toM3_toFun (A : IMat) (k : Fin 3) :
    ((Data.M3.cols (toM3 A)).getD k.val Data.V3.zero).toFun =
      A.mulVec (Pi.single k (1 : ℤ)) := by
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [Data.M3.cols, Data.V3.toFun, toM3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.single_eq_same]

/-- Forward direction of the bridge: a selling-stabiliser element gives an entry of the table. -/
theorem toM3_mem_stabCands {i : Fin 6} {A : IMat} (h : A ∈ sellingStab (sellingGraph i)) :
    toM3 A ∈ Data.stabCands (Sof i).vecs := by
  rw [mem_stabCands]
  refine ⟨?_, ?_, ?_⟩
  · rw [← toIMat_det (toM3 A), toM3_toIMat]
    exact Int.isUnit_iff.mp h.1
  · intro k
    rw [vecs_eq i, mem_boxVecs, cols_toM3_toFun]
    exact h.2 _ (single_mem_sellingVecs _ k)
  · intro y hy
    have hy' : y.toFun ∈ sellingVecs (sellingGraph i) := by
      rw [vecs_eq i] at hy
      rwa [mem_boxVecs] at hy
    have hgoal : (Data.M3.mulV (toM3 A) y).toFun ∈ sellingVecs (sellingGraph i) := by
      rw [toIMat_mulV, toM3_toIMat]
      exact h.2 _ hy'
    rw [vecs_eq i, mem_boxVecs]
    exact hgoal

/-- Backward direction of the bridge: every table entry is in the selling stabiliser. -/
theorem of_mem_stabCands {i : Fin 6} {x : Data.M3} (hx : x ∈ (Sof i).stab) :
    x.toIMat ∈ sellingStab (sellingGraph i) := by
  rw [stab_eq_cands i] at hx
  obtain ⟨hdet, _hcols, hmap⟩ := mem_stabCands.mp hx
  refine ⟨?_, ?_⟩
  · rw [toIMat_det]
    rcases hdet with h | h <;> rw [h]
    · exact isUnit_one
    · exact Int.isUnit_iff.mpr (Or.inr rfl)
  · intro y hy
    have hy' : ofFun y ∈ (Sof i).vecs := by
      rw [vecs_eq i, mem_boxVecs]
      rwa [ofFun_toFun]
    have h1 := hmap _ hy'
    rw [vecs_eq i, mem_boxVecs, toIMat_mulV, ofFun_toFun] at h1
    exact h1

/-- **The selling stabiliser is exactly the table of the certificate.** -/
theorem sellingStab_eq (i : Fin 6) :
    sellingStab (sellingGraph i) = {A : IMat | ∃ x ∈ (Sof i).stab, A = x.toIMat} := by
  ext A
  constructor
  · intro hA
    have hmem : toM3 A ∈ (Sof i).stab := by
      rw [stab_eq_cands i]
      exact toM3_mem_stabCands hA
    exact ⟨toM3 A, hmem, (toM3_toIMat A).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact of_mem_stabCands hx

/-! ## The join-certificate row -/

theorem chkJoins_row {S : Data.SellData} {lo cnt : ℕ} (h : S.chkJoins lo cnt = true) :
    ∀ s ∈ List.range' lo cnt,
      (S.joins.getD s []).length = S.stab.length ∧
      (∀ g < S.stab.length, S.chkJoin s g ((S.joins.getD s []).getD g none) = true) := by
  intro s hs
  have h' := List.all_eq_true.mp h s hs
  have h'' : ((S.joins.getD s []).length == S.stab.length &&
      (List.range S.stab.length).all (fun g => S.chkJoin s g ((S.joins.getD s []).getD g none)))
      = true := h'
  rw [Bool.and_eq_true] at h''
  exact ⟨beq_iff_eq.mp h''.1, fun g hg => List.all_eq_true.mp h''.2 g (List.mem_range.mpr hg)⟩

theorem mem_range'_of_le_lt {m lo cnt : ℕ} (h1 : lo ≤ m) (h2 : m < lo + cnt) :
    m ∈ List.range' lo cnt := by
  rw [List.mem_range']
  exact ⟨m - lo, by omega, by omega⟩

/-- The four checked blocks of the joins table cover a whole row. -/
theorem joins_row_of {S : Data.SellData} {a b c s : ℕ}
    (h0 : S.chkJoins 0 25 = true) (h1 : S.chkJoins 25 a = true)
    (h2 : S.chkJoins (25 + a) b = true) (h3 : S.chkJoins (25 + a + b) c = true)
    (hlen : S.subs.length = 25 + a + b + c) (hs : s < S.subs.length) :
    (S.joins.getD s []).length = S.stab.length ∧
    (∀ g < S.stab.length, S.chkJoin s g ((S.joins.getD s []).getD g none) = true) := by
  rcases Nat.lt_or_ge s 25 with h | h
  · exact chkJoins_row h0 s (mem_range'_of_le_lt (by omega) (by omega))
  rcases Nat.lt_or_ge s (25 + a) with h' | h'
  · exact chkJoins_row h1 s (mem_range'_of_le_lt (by omega) (by omega))
  rcases Nat.lt_or_ge s (25 + a + b) with h'' | h''
  · exact chkJoins_row h2 s (mem_range'_of_le_lt (by omega) (by omega))
  · exact chkJoins_row h3 s (mem_range'_of_le_lt (by omega) (by omega))

/-- The full row of the joins table for graph `i`. -/
theorem joins_row_all (i : Fin 6) {s : ℕ} (hs : s < (Sof i).subs.length) :
    ((Sof i).joins.getD s []).length = (Sof i).stab.length ∧
    (∀ g < (Sof i).stab.length,
      (Sof i).chkJoin s g ((Sof i).joins.getD s [] |>.getD g none) = true) := by
  fin_cases i
  · exact joins_row_of (a := 25) (b := 25) (c := 23) Data.sell_joins_0_0 Data.sell_joins_0_25
      Data.sell_joins_0_50 Data.sell_joins_0_75 (by decide +kernel) hs
  · exact joins_row_of (a := 10) (b := 0) (c := 0) Data.sell_joins_1_0 Data.sell_joins_1_25
      rfl rfl (by decide +kernel) hs
  · exact joins_row_of (a := 25) (b := 25) (c := 23) Data.sell_joins_2_0 Data.sell_joins_2_25
      Data.sell_joins_2_50 Data.sell_joins_2_75 (by decide +kernel) hs
  · exact joins_row_of (a := 25) (b := 4) (c := 0) Data.sell_joins_3_0 Data.sell_joins_3_25
      Data.sell_joins_3_50 rfl (by decide +kernel) hs
  · exact joins_row_of (a := 25) (b := 25) (c := 23) Data.sell_joins_4_0 Data.sell_joins_4_25
      Data.sell_joins_4_50 Data.sell_joins_4_75 (by decide +kernel) hs
  · exact joins_row_of (a := 25) (b := 25) (c := 23) Data.sell_joins_5_0 Data.sell_joins_5_25
      Data.sell_joins_5_50 Data.sell_joins_5_75 (by decide +kernel) hs

/-- The joins check at a single element of a listed subgroup. -/
theorem joins_row (i : Fin 6) {s g : ℕ} (hs : s < (Sof i).subs.length)
    (hg : g < (Sof i).stab.length) :
    (Sof i).chkJoin s g ((Sof i).joins.getD s [] |>.getD g none) = true :=
  (joins_row_all i hs).2 g hg


def conjXs (S : Data.SellData) (s : ℕ) : List ℕ :=
  (List.range S.stab.length).filter (S.subs.getD s 0).testBit

theorem conjXs_mem {S : Data.SellData} {s a : ℕ} (h : a ∈ conjXs S s) :
    a < S.stab.length ∧ (S.subs.getD s 0).testBit a = true := by
  rw [conjXs, List.mem_filter] at h
  exact ⟨List.mem_range.mp h.1, h.2⟩

/-- Bit extraction from a mask inclusion `T ⊆ T'` written as `T ||| U ||| T' = T'`. -/
theorem testBit_of_lor_mask_eq {T U T' : ℕ} (h : (T ||| U ||| T') = T') {a : ℕ}
    (ha : T.testBit a = true) : T'.testBit a = true := by
  have h1 := congrArg (fun m : ℕ => m.testBit a) h
  simp only [Nat.testBit_lor] at h1
  simpa [ha] using h1


/-- The `zipWith` component of `chkConj`, unpacked. -/
theorem chkConj_zip {S : Data.SellData} (h : S.chkConj = true) {s p : ℕ}
    (hs : s < S.subs.length) (hp : p < (S.conj.getD s default).img.length) :
    Data.M3.mul (Data.M3.mul (S.conj.getD s default).U
        (S.stab.getD ((conjXs S s).getD p 0) Data.M3.one))
        (S.conj.getD s default).Uinv =
      (Data.arithData.getD (S.conj.getD s default).j default).elems.getD
        ((S.conj.getD s default).img.getD p 0) Data.M3.one ∧
    (S.conj.getD s default).img.getD p 0 <
      (Data.arithData.getD (S.conj.getD s default).j default).n := by
  rw [Data.SellData.chkConj] at h
  have h' := List.all_eq_true.mp h s (List.mem_range.mpr hs)
  set c : Data.SubConj := S.conj.getD s default with hc
  set D : Data.ArithData := Data.arithData.getD c.j default with hD
  set xs : List ℕ := conjXs S s with hxs
  have hxs' : xs = (List.range S.stab.length).filter (S.subs.getD s 0).testBit := by
    rw [hxs, conjXs]
  have hlen_eq : c.img.length = xs.length := by
    have h2 := h'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h2
    exact h2.1.1.1.2
  have hzip : ∀ z ∈ List.zipWith (fun x q => decide (q < D.n) &&
      (Data.M3.mul (Data.M3.mul c.U (S.stab.getD x Data.M3.one)) c.Uinv ==
        D.elems.getD q Data.M3.one)) xs c.img, z = true := by
    have h2 := h'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h2
    exact h2.2
  have hpmem : p < (List.zipWith (fun x q => decide (q < D.n) &&
      (Data.M3.mul (Data.M3.mul c.U (S.stab.getD x Data.M3.one)) c.Uinv ==
        D.elems.getD q Data.M3.one)) xs c.img).length := by
    rw [List.length_zipWith, ← hlen_eq, Nat.min_self]
    exact hp
  have hz := hzip _ (List.getElem_mem (l := List.zipWith (fun x q => decide (q < D.n) &&
      (Data.M3.mul (Data.M3.mul c.U (S.stab.getD x Data.M3.one)) c.Uinv ==
        D.elems.getD q Data.M3.one)) xs c.img) hpmem)
  rw [List.getElem_zipWith] at hz
  simp only [Bool.and_eq_true] at hz
  have hqd : c.img.getD p 0 < D.n := by
    rw [show c.img.getD p 0 = c.img[p] from List.getD_eq_getElem c.img 0 hp]
    exact decide_eq_true_eq.mp hz.1
  have h4 := hz.2
  rw [beq_iff_eq] at h4
  refine ⟨?_, hqd⟩
  rw [show xs.getD p 0 = xs[p] from List.getD_eq_getElem xs 0 (by rw [← hlen_eq]; exact hp)]
  rw [show c.img.getD p 0 = c.img[p] from List.getD_eq_getElem c.img 0 hp]
  exact h4


/-- Unpacked `chkConj` head components. -/
theorem chkConj_head {S : Data.SellData} (h : S.chkConj = true) {s : ℕ} (hs : s < S.subs.length) :
    (S.conj.getD s default).j < 73 ∧ Data.M3.det (S.conj.getD s default).U = 1 ∧
    Data.M3.mul (S.conj.getD s default).U (S.conj.getD s default).Uinv = Data.M3.one ∧
    (S.conj.getD s default).img.length = (conjXs S s).length ∧
    (conjXs S s).length = (Data.arithData.getD (S.conj.getD s default).j default).n ∧
    (S.conj.getD s default).img.Nodup := by
  rw [Data.SellData.chkConj] at h
  have h' := List.all_eq_true.mp h s (List.mem_range.mpr hs)
  have h2 := h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h2
  exact ⟨h2.1.1.1.1.1.1, h2.1.1.1.1.1.2, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, h2.1.2⟩


theorem arith_elems_nodup : ∀ j : Fin 73,
    (Data.arithData.getD j.val default).elems.Nodup := by decide +kernel

theorem chkJoin_none_spec {S : Data.SellData} {s g : ℕ} (h : S.chkJoin s g none = true) :
    (S.subs.getD s 0).testBit g = true := by
  simpa [Data.SellData.chkJoin] using h

/-- The joined element is a bit of the target mask. -/
theorem testBit_self_of_lor_mask {T T' g : ℕ} (h : (T ||| (1 <<< g) ||| T') = T') :
    T'.testBit g = true := by
  have h1 := congrArg (fun m : ℕ => m.testBit g) h
  simp only [Nat.testBit_lor, testBit_shiftLeft_one] at h1
  simpa using h1

/-- The `ref` case of the checker exposes the inner `full` certificate it consults. -/
theorem chkJoin_ref_inner {S : Data.SellData} {s g g0 k1 k2 : ℕ}
    (h : S.chkJoin s g (some (Data.JoinCert.ref g0 k1 k2)) = true) :
    ∃ t cos, (S.joins.getD s []).getD g0 none = some (Data.JoinCert.full t cos) ∧
      (S.subs.getD t 0).testBit g = true := by
  rcases he : ((S.joins.getD s []).getD g0 none) with _ | cert
  · have h' : S.chkJoin s g (some (Data.JoinCert.ref g0 k1 k2)) = false := by
      simp only [Data.SellData.chkJoin]
      rw [he]
      simp
    rw [h'] at h
    exact absurd h (by simp)
  · rcases cert with ⟨t, cos⟩ | ⟨g0', k1', k2'⟩
    · refine ⟨t, cos, rfl, ?_⟩
      have h'' := h
      simp only [Data.SellData.chkJoin] at h''
      rw [he] at h''
      simp only [Bool.and_eq_true, beq_iff_eq] at h''
      exact h''.2
    · have h' : S.chkJoin s g (some (Data.JoinCert.ref g0 k1 k2)) = false := by
        simp only [Data.SellData.chkJoin]
        rw [he]
        simp
      rw [h'] at h
      exact absurd h (by simp)

end CZ

open CZ

/-- Arithmetic classification (computational): every subgroup of a Selling stabiliser is
`SL₃(ℤ)`-conjugate to one of the 73 listed arithmetic-class representatives. -/
theorem conj_to_arithRep {i : Fin 6} {H : Set IMat} (hH : IsIntPointGroup H)
    (hsub : ∀ A ∈ H, A ∈ sellingStab (sellingGraph i)) :
    ∃ j : Fin 73, ∃ U : IMat, U.det = 1 ∧ ∀ A, A ∈ arithRep j ↔ ∃ B ∈ H, A = U * B * U⁻¹ := by
  classical
  obtain ⟨hHfin, hHone, hHmul, hHunit⟩ := hH
  have hsub' : ∀ A ∈ H, ∃ x ∈ (Sof i).stab, A = x.toIMat := by
    intro A hA
    have h : A ∈ ({A : IMat | ∃ x ∈ (Sof i).stab, A = x.toIMat} : Set IMat) := by
      rw [← sellingStab_eq i]
      exact hsub A hA
    simpa using h
  let F : Finset ℕ := (List.range (Sof i).stab.length).toFinset.filter
      (fun a => (mat (Sof i) a).toIMat ∈ H)
  have hFmem : ∀ a, a ∈ F ↔ a < (Sof i).stab.length ∧ (mat (Sof i) a).toIMat ∈ H := by
    intro a
    simp only [F, Finset.mem_filter, List.mem_toFinset, List.mem_range]
  have hFclos : ∀ a ∈ F, ∀ b ∈ F, gmul (Sof i) a b ∈ F := by
    intro a ha b hb
    rw [hFmem] at ha hb ⊢
    refine ⟨mul_lt i ha.1 hb.1, ?_⟩
    rw [mul_spec i ha.1 hb.1, toIMat_mul]
    exact hHmul _ ha.2 _ hb.2
  have hFone : (Sof i).one ∈ F := by
    rw [hFmem]
    exact ⟨one_lt i, by rw [one_spec i, toIMat_one]; exact hHone⟩
  -- the certificate step
  have step : ∀ T : ℕ, T ∈ (Sof i).subs → bitsOf (Sof i) T ⊂ F →
      ∃ T' ∈ (Sof i).subs, bitsOf (Sof i) T ⊂ bitsOf (Sof i) T' ∧
        bitsOf (Sof i) T' ⊆ F := by
    intro T hT hss
    have hsubT : bitsOf (Sof i) T ⊆ F := hss.1
    obtain ⟨g, hgF, hgT⟩ := Finset.exists_of_ssubset hss
    have hgN : g < (Sof i).stab.length := ((hFmem g).mp hgF).1
    have hgbit : T.testBit g = false := by
      by_contra hc
      have hc' : T.testBit g = true := by simpa using hc
      exact hgT ((mem_bitsOf (S := Sof i)).mpr ⟨hgN, hc'⟩)
    obtain ⟨s, hs⟩ := List.mem_iff_get.mp hT
    have hTs : (Sof i).subs.getD s.val 0 = T := by
      rw [List.getD_eq_getElem _ _ s.isLt, ← List.get_eq_getElem]
      exact hs
    obtain ⟨hrowlen, hrowcheck⟩ := joins_row_all i s.isLt
    have hJ := hrowcheck g hgN
    rcases hcert : ((Sof i).joins.getD s.val []).getD g none with _ | cert
    · rw [hcert] at hJ
      have hb := chkJoin_none_spec hJ
      rw [hTs] at hb
      rw [hb] at hgbit
      exact absurd hgbit (by simp)
    · rcases cert with ⟨t, cos⟩ | ⟨g0, k1, k2⟩
      · -- `full` case
        rw [hcert] at hJ
        obtain ⟨hgb, htlt, hmask, hcos, hidx, hdisj⟩ := chkJoin_full hJ
        rw [hTs] at hmask
        refine ⟨(Sof i).subs.getD t 0, ?_, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ htlt]; exact List.getElem_mem ..
        · refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro a ha
            rw [mem_bitsOf] at ha ⊢
            exact ⟨ha.1, testBit_of_lor_mask_eq hmask ha.2⟩
          · intro heq
            have hgT' : g ∈ bitsOf (Sof i) ((Sof i).subs.getD t 0) :=
              (mem_bitsOf (S := Sof i)).mpr ⟨hgN, testBit_self_of_lor_mask hmask⟩
            rw [← heq] at hgT'
            exact hgT hgT'
        · intro a ha
          rw [mem_bitsOf] at ha
          obtain ⟨haN, hab⟩ := ha
          obtain ⟨r, hr, k, hkN, hkb, hrk⟩ := hdisj a hab
          rw [hTs] at hkb
          have hkF : k ∈ F := hsubT ((mem_bitsOf (S := Sof i)).mpr ⟨hkN, hkb⟩)
          have hrF : r ∈ F :=
            joinReps_mem hFone hFclos hidx (fun q hq => by
              have hmem : cos.getD q (0, 0) ∈ cos := by
                rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem ..
              rcases hcos _ hmem with h | h
              · rw [h]; exact hgF
              · rw [hTs] at h
                exact hsubT ((mem_bitsOf (S := Sof i)).mpr
                  ⟨testBit_lt_two_pow (subs_lt i T hT) h, h⟩)) r hr
          rw [← hrk]
          exact hFclos k hkF r hrF
      · -- `ref` case
        rw [hcert] at hJ
        obtain ⟨t', cos', hinnereq, hgtbit⟩ := chkJoin_ref_inner hJ
        have hg0lt : g0 < ((Sof i).joins.getD s.val []).length := by
          have h1 : ((Sof i).joins.getD s.val [])[g0]? ≠ none := by
            intro hnone
            rw [List.getD_eq_getElem?_getD, hnone] at hinnereq
            simp at hinnereq
          exact lt_of_not_ge (fun hle => h1 (List.getElem?_eq_none_iff.mpr hle))
        have hg0N : g0 < (Sof i).stab.length := by rw [← hrowlen]; exact hg0lt
        have h2 : (Sof i).chkJoin s.val g0 (some (Data.JoinCert.full t' cos')) = true := by
          rw [← hinnereq]
          exact hrowcheck g0 hg0N
        obtain ⟨hgb, hk1, hk2, hgeq, hgt', hmask, htlt, hcos, hidx, hdisj⟩ :=
          chkJoin_ref hJ hinnereq h2
        rw [hTs] at hmask hk1 hk2
        have hk1N : k1 < (Sof i).stab.length := testBit_lt_two_pow (subs_lt i T hT) hk1
        have hk2N : k2 < (Sof i).stab.length := testBit_lt_two_pow (subs_lt i T hT) hk2
        have hk1F : k1 ∈ F := hsubT ((mem_bitsOf (S := Sof i)).mpr ⟨hk1N, hk1⟩)
        have hk2F : k2 ∈ F := hsubT ((mem_bitsOf (S := Sof i)).mpr ⟨hk2N, hk2⟩)
        -- `g0 ∈ F`, through the group structure of `H`
        have hg0F : g0 ∈ F := by
          rw [hFmem]
          refine ⟨hg0N, ?_⟩
          have hmat : mat (Sof i) g =
              Data.M3.mul (Data.M3.mul (mat (Sof i) k1) (mat (Sof i) g0)) (mat (Sof i) k2) := by
            rw [hgeq, mul_spec i (mul_lt i hk1N hg0N) hk2N, mul_spec i hk1N hg0N]
          have hAg : (mat (Sof i) g).toIMat ∈ H := ((hFmem g).mp hgF).2
          have hA1 : (mat (Sof i) k1).toIMat ∈ H := ((hFmem k1).mp hk1F).2
          have hA2 : (mat (Sof i) k2).toIMat ∈ H := ((hFmem k2).mp hk2F).2
          obtain ⟨B1, hB1H, hB1A, _⟩ := isIntPointGroup_inv ⟨hHfin, hHone, hHmul, hHunit⟩ hA1
          obtain ⟨B2, hB2H, _, hAB2⟩ := isIntPointGroup_inv ⟨hHfin, hHone, hHmul, hHunit⟩ hA2
          have hYeq : (mat (Sof i) g).toIMat =
              (mat (Sof i) k1).toIMat * (mat (Sof i) g0).toIMat * (mat (Sof i) k2).toIMat := by
            rw [hmat, toIMat_mul, toIMat_mul]
          have hYe : (mat (Sof i) g0).toIMat = B1 * (mat (Sof i) g).toIMat * B2 := by
            rw [hYeq]
            rw [show B1 * ((mat (Sof i) k1).toIMat * (mat (Sof i) g0).toIMat *
                  (mat (Sof i) k2).toIMat) * B2
                = (B1 * (mat (Sof i) k1).toIMat) * (mat (Sof i) g0).toIMat *
                  ((mat (Sof i) k2).toIMat * B2) from by noncomm_ring,
              hB1A, hAB2, one_mul, mul_one]
          rw [hYe]
          exact hHmul (B1 * (mat (Sof i) g).toIMat) (hHmul B1 hB1H _ hAg) B2 hB2H
        refine ⟨(Sof i).subs.getD t' 0, ?_, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ htlt]; exact List.getElem_mem ..
        · refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro a ha
            rw [mem_bitsOf] at ha ⊢
            exact ⟨ha.1, testBit_of_lor_mask_eq hmask ha.2⟩
          · intro heq
            have hgT' : g ∈ bitsOf (Sof i) ((Sof i).subs.getD t' 0) :=
              (mem_bitsOf (S := Sof i)).mpr ⟨hgN, hgt'⟩
            rw [← heq] at hgT'
            exact hgT hgT'
        · intro a ha
          rw [mem_bitsOf] at ha
          obtain ⟨haN, hab⟩ := ha
          obtain ⟨r, hr, k, hkN, hkb, hrk⟩ := hdisj a hab
          rw [hTs] at hkb
          have hkF : k ∈ F := hsubT ((mem_bitsOf (S := Sof i)).mpr ⟨hkN, hkb⟩)
          have hrF : r ∈ F :=
            joinReps_mem hFone hFclos hidx (fun q hq => by
              have hmem : cos'.getD q (0, 0) ∈ cos' := by
                rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem ..
              rcases hcos _ hmem with h | h
              · rw [h]; exact hg0F
              · rw [hTs] at h
                exact hsubT ((mem_bitsOf (S := Sof i)).mpr
                  ⟨testBit_lt_two_pow (subs_lt i T hT) h, h⟩)) r hr
          rw [← hrk]
          exact hFclos k hkF r hrF
  -- the induction
  have aux : ∀ k : ℕ, ∀ T : ℕ, T ∈ (Sof i).subs → bitsOf (Sof i) T ⊆ F →
      F.card ≤ (bitsOf (Sof i) T).card + k → ∃ T' ∈ (Sof i).subs, bitsOf (Sof i) T' = F := by
    intro k
    induction k with
    | zero =>
      intro T hT hsubT hle
      exact ⟨T, hT, Finset.eq_of_subset_of_card_le hsubT (by omega)⟩
    | succ k ih =>
      intro T hT hsubT hle
      by_cases heq : bitsOf (Sof i) T = F
      · exact ⟨T, hT, heq⟩
      · obtain ⟨T', hT'mem, hss, hsub''⟩ :=
          step T hT (Finset.ssubset_iff_subset_ne.mpr ⟨hsubT, heq⟩)
        refine ih T' hT'mem hsub'' ?_
        have h1 : (bitsOf (Sof i) T).card < (bitsOf (Sof i) T').card := Finset.card_lt_card hss
        have h2 : (bitsOf (Sof i) T').card ≤ F.card := Finset.card_le_card hsub''
        omega
  have hinit1 : bitsOf (Sof i) (1 <<< (Sof i).one) ⊆ F := by
    rw [mem_bitsOf_one (one_lt i)]
    exact Finset.singleton_subset_iff.mpr hFone
  have hinit2 : F.card ≤ (bitsOf (Sof i) (1 <<< (Sof i).one)).card + F.card := by
    rw [mem_bitsOf_one (one_lt i)]
    simp
  obtain ⟨T, hTmem, hTeq⟩ := aux F.card (1 <<< (Sof i).one) (one_mask_mem i) hinit1 hinit2
  -- assembly
  obtain ⟨s, hs⟩ := List.mem_iff_get.mp hTmem
  have hTs : (Sof i).subs.getD s.val 0 = T := by
    rw [List.getD_eq_getElem _ _ s.isLt, ← List.get_eq_getElem]
    exact hs
  obtain ⟨hj73, hdet, hmulc, hlen1, hlen2, hnodup⟩ := chkConj_head (sell_conj_all i) s.isLt
  set c : Data.SubConj := (Sof i).conj.getD s.val default with hc
  set D : Data.ArithData := Data.arithData.getD c.j default with hD
  have hDnodup : D.elems.Nodup := arith_elems_nodup ⟨_, hj73⟩
  have hDlen : D.elems.length = D.n := arith_elems_len ⟨_, hj73⟩
  refine ⟨⟨c.j, hj73⟩, c.U.toIMat, ?_, ?_⟩
  · rw [toIMat_det]
    exact hdet
  · intro A
    constructor
    · -- forward: every representative element is a conjugate of a table element
      intro hA
      rw [arithRep_eq_data] at hA
      obtain ⟨e, he, rfl⟩ := hA
      set imgf : Fin c.img.length → Data.M3 :=
        fun p => D.elems.getD (c.img.getD p.val 0) Data.M3.one with himgf
      have hinj : Function.Injective imgf := by
        intro p q hpq
        simp only [imgf] at hpq
        have hp : c.img.getD p.val 0 < D.elems.length := by
          rw [hDlen]; exact (chkConj_zip (sell_conj_all i) s.isLt p.isLt).2
        have hq : c.img.getD q.val 0 < D.elems.length := by
          rw [hDlen]; exact (chkConj_zip (sell_conj_all i) s.isLt q.isLt).2
        rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at hpq
        have h1 := (List.Nodup.getElem_inj_iff hDnodup).mp hpq
        have hp' : c.img.getD p.val 0 = c.img[p.val] := List.getD_eq_getElem _ _ p.isLt
        have hq' : c.img.getD q.val 0 = c.img[q.val] := List.getD_eq_getElem _ _ q.isLt
        rw [hp', hq'] at h1
        exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h1)
      have hcard : (Finset.univ.image imgf).card = c.img.length := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hsubimg : Finset.univ.image imgf ⊆ D.elems.toFinset := by
        intro z hz
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hz
        simp only [imgf]
        rw [List.mem_toFinset]
        rw [List.getD_eq_getElem _ _
          (by rw [hDlen]; exact (chkConj_zip (sell_conj_all i) s.isLt p.isLt).2)]
        exact List.getElem_mem ..
      have hseteq : Finset.univ.image imgf = D.elems.toFinset :=
        Finset.eq_of_subset_of_card_le hsubimg (by
          rw [hcard, List.toFinset_card_of_nodup hDnodup, hDlen, ← hlen2, hlen1])
      have he' : e ∈ Finset.univ.image imgf := by
        rw [hseteq, List.mem_toFinset]; exact he
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp he'
      simp only [imgf] at hp
      have hpconj : p.val < (conjXs (Sof i) s.val).length := by have := p.isLt; omega
      have hmem : (conjXs (Sof i) s.val).getD p.val 0 ∈ conjXs (Sof i) s.val := by
        rw [List.getD_eq_getElem _ _ hpconj]; exact List.getElem_mem ..
      obtain ⟨hlt, hbit⟩ := conjXs_mem hmem
      have hmatH : (mat (Sof i) ((conjXs (Sof i) s.val).getD p.val 0)).toIMat ∈ H := by
        have hFp : (conjXs (Sof i) s.val).getD p.val 0 ∈ F := by
          rw [← hTeq, mem_bitsOf]
          exact ⟨hlt, by rw [hTs] at hbit; exact hbit⟩
        exact ((hFmem _).mp hFp).2
      refine ⟨(mat (Sof i) ((conjXs (Sof i) s.val).getD p.val 0)).toIMat, hmatH, ?_⟩
      have hzip := chkConj_zip (sell_conj_all i) s.isLt p.isLt
      have hUinv : (c.U.toIMat)⁻¹ = c.Uinv.toIMat := by
        rw [Matrix.inv_eq_right_inv]
        rw [← toIMat_mul, hmulc, toIMat_one]
      have hident : Data.M3.mul (Data.M3.mul c.U
            (mat (Sof i) ((conjXs (Sof i) s.val).getD p.val 0))) c.Uinv =
          D.elems.getD (c.img.getD p.val 0) Data.M3.one := hzip.1
      rw [hUinv, ← hp, ← hident, ← toIMat_mul, ← toIMat_mul]
    · -- backward: a conjugate of a table element is a representative element
      rintro ⟨B, hB, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hsub' B hB
      obtain ⟨b, hb⟩ := List.get_of_mem hx
      have hmatbx : mat (Sof i) b.val = x := by
        rw [mat, List.getD_eq_getElem _ _ b.isLt, ← List.get_eq_getElem]
        exact hb
      have hbF : b.val ∈ F := (hFmem b.val).mpr ⟨b.isLt, by rw [hmatbx]; exact hB⟩
      have hbit : T.testBit b.val = true := by
        have h := (Finset.ext_iff.mp hTeq b.val).mpr hbF
        rw [mem_bitsOf] at h
        exact h.2
      have hbmem : b.val ∈ conjXs (Sof i) s.val := by
        rw [conjXs, List.mem_filter]
        exact ⟨List.mem_range.mpr b.isLt, by rw [hTs]; exact hbit⟩
      obtain ⟨p, hp⟩ := List.get_of_mem hbmem
      have hpval : (conjXs (Sof i) s.val).getD p.val 0 = b.val := by
        rw [List.getD_eq_getElem _ _ p.isLt]
        rw [← List.get_eq_getElem]
        exact hp
      have hpz : p.val < c.img.length := by have := p.isLt; omega
      have hzip := chkConj_zip (sell_conj_all i) s.isLt hpz
      have hql : c.img.getD p.val 0 < D.elems.length := by rw [hDlen]; exact hzip.2
      rw [arithRep_eq_data]
      refine ⟨D.elems.getD (c.img.getD p.val 0) Data.M3.one, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hql]; exact List.getElem_mem ..
      · have hUinv : (c.U.toIMat)⁻¹ = c.Uinv.toIMat := by
          rw [Matrix.inv_eq_right_inv]
          rw [← toIMat_mul, hmulc, toIMat_one]
        have hident : Data.M3.mul (Data.M3.mul c.U
              (mat (Sof i) ((conjXs (Sof i) s.val).getD p.val 0))) c.Uinv =
            D.elems.getD (c.img.getD p.val 0) Data.M3.one := hzip.1
        rw [hUinv, ← hmatbx, ← hpval, ← hident, ← toIMat_mul, ← toIMat_mul]




end Work.SG
