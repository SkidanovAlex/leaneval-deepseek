import Mathlib
import Submission.Work.PTCert.Checks.SharedAll

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects and the semantic Props of the data) and
`Glue3.lean` (math steps), `KernelShared.lean`/`KernelCert.lean` (the Bool check functions), the data
modules `Data/*.lean` (namespace `Submission.PTCert.D`) and the kernel theorems `Checks/*.lean`
(namespace `Submission.PTCert.C`, each `theorem xxx : <check> = true := by decide +kernel`, ALREADY BUILT).
Design notes: `NOTES_LEAD_glue.md` at the workspace root.

This file proves `kleinSem : ∀ k ≤ 5, KleinSem k`: the Kleim data of each base character `k ≤ 5` are the
plain meaning of the kernel checks `kltab_ok{k}`, `klcov_ok{k}_{0,1,2}`, `kldist_ok{k}`, `klcols_ok{k}`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable section

/-! ## Generic `Bool`-soundness lemmas for the kernel combinators -/

lemma allL_iff_kleinSem (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => refine ⟨fun _ a ha => by simp at ha, fun _ => rfl⟩
  | cons a l ih =>
    have h : allL (a :: l) p = (p a && allL l p) := rfl
    rw [h, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · exact h2 b hb
    · intro h
      exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem a hb)⟩

lemma allR_iff_kleinSem (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero =>
    rw [show allR 0 p = true from rfl]
    exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    have h : allR (n + 1) p = (p n && allR n p) := rfl
    rw [h, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact h2 k hk'
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

lemma allIdx_iff (l : List ℕ) (p : ℕ → ℕ → Bool) (i : ℕ) :
    allIdx l p i = true ↔ ∀ j < l.length, p (i + j) (l.getD j 0) = true := by
  induction l generalizing i with
  | nil => refine ⟨fun _ j hj => absurd hj (by simp), fun _ => rfl⟩
  | cons a l ih =>
    have h : allIdx (a :: l) p i = (p i a && allIdx l p (i + 1)) := rfl
    rw [h, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      cases j with
      | zero => simpa using h1
      | succ k =>
        have hk : k < l.length := by simpa using hj
        have h2' := h2 k hk
        have hik : i + (k + 1) = (i + 1) + k := by omega
        rw [hik]; simpa using h2'
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
      have h1' := h (j + 1) (by rw [List.length_cons]; omega)
      have hij : i + (j + 1) = (i + 1) + j := by omega
      simpa [hij] using h1'

lemma eqL_eq (l m : List ℕ) (h : eqL l m = true) : l = m := by
  induction l generalizing m with
  | nil => cases m with
          | nil => rfl
          | cons b t => simp [eqL] at h
  | cons a l ih =>
    cases m with
    | nil => simp [eqL] at h
    | cons b t =>
      have h' : (Nat.beq a b && eqL l t) = true := h
      rw [Bool.and_eq_true, Nat.beq_eq] at h'
      rw [ih t h'.2, h'.1]

/-- Case analysis of a `bif (Nat.beq kw 0) then a else b` check. -/
lemma bif_zero_true_iff (kw : ℕ) (a b : Bool) :
    (bif Nat.beq kw 0 then a else b) = true ↔ (kw = 0 ∧ a = true) ∨ (kw ≠ 0 ∧ b = true) := by
  by_cases h : kw = 0
  · subst h; simp
  · have h2 : Nat.beq kw 0 = false := by
      rw [Bool.eq_false_iff]; intro hh; exact h (Nat.beq_eq.mp hh)
    simp [h2, h]

/-- `bif (decide P) then a else b = if P then a else b`. -/
lemma bif_decide_ite {P : Prop} [Decidable P] (a b : ℕ) :
    (bif decide P then a else b) = (if P then a else b) := by
  by_cases h : P
  · rw [if_pos h, show decide P = true from by simp [h]]; rfl
  · rw [if_neg h, show decide P = false from by simp [h]]; rfl

/-! ## The three chunks of the Klein cover checks -/

def klChunk0 : List ℕ := List.range 206
def klChunk1 : List ℕ := (List.range 206).map (fun i => i + 206)
def klChunk2 : List ℕ := (List.range 199).map (fun i => i + 412)

lemma mem_chunks {t : ℕ} (h : t < 611) : t ∈ klChunk0 ∨ t ∈ klChunk1 ∨ t ∈ klChunk2 := by
  rw [klChunk0, klChunk1, klChunk2]
  simp only [List.mem_range, List.mem_map]
  rcases lt_or_ge t 206 with h1 | h1
  · exact Or.inl h1
  · rcases lt_or_ge t 412 with h2 | h2
    · exact Or.inr (Or.inl ⟨t - 206, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨t - 412, by omega, by omega⟩)

/-! ## Soundness of the five families of Klein checks -/

/-- The predicate checked by `inROK`. -/
def inROKF (cm nT repT : NT) (S t : ℕ) : ℕ → Bool :=
  fun sc => !(Nat.beq (actC cm (nT.get sc) (cG repT t)) (cG repT t)) || decide (chiS5 S sc = 1)

lemma inROK_eq (cm nT repT : NT) (S t : ℕ) :
    inROK cm nT repT S t = allR 32 (inROKF cm nT repT S t) := rfl

/-- `tabsOK`: the table of letters of `pcOf (kleinPerm k b)`. -/
lemma tabsOK_sound {codes : List ℕ} {T : NT} {k : ℕ}
    (h : tabsOK codes T = true) (h4 : 4 ≤ codes.length)
    (hcodes : ∀ b < 4, codes.getD b 0 = 32 * pcOf (kleinPerm k b)) :
    ∀ b < 4, ∀ j < 81, lk (T.get b) j = actL 5 (pcOf (kleinPerm k b)) 0 j := by
  intro b hb j hj
  have hb' : b < codes.length := by omega
  have h1 := (allIdx_iff codes (fun i c => tabOK (c / 32) (c % 32) (T.get i)) 0).mp h b hb'
  simp only [Nat.zero_add] at h1
  rw [hcodes b hb] at h1
  simp only [Nat.mul_div_right _ (by norm_num : 0 < 32), Nat.mul_mod_right] at h1
  simp only [tabOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Nat.reduceLT] at h1
  have h2 := h1.2 j (by simpa using hj)
  rwa [Nat.beq_eq] at h2

/-- `kleinCoverOK` on the three chunks: every `N`-rep is either non-admissible (with a vanishing
witness), or a Klein translate of a listed representative. -/
lemma kleinCover_sound {k : ℕ} {klT kwT vwT : NT} {ks : List ℕ}
    (hcovA : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk0 = true)
    (hcovB : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk1 = true)
    (hcovC : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk2 = true) :
    ∀ t < 611,
      (cG kwT t = 0 →
        actC cmT (ntab (rG vwT t)) (rp t) = rp t ∧ chiS5 (Sk k) (rG vwT t) = -1) ∧
      (cG kwT t ≠ 0 →
        (∀ sc < 32, actC cmT (ntab sc) (rp t) = rp t → chiS5 (Sk k) sc = 1) ∧
        (cG kwT t - 1) / 4 < ks.length ∧
        (em (actC cmT (klT.get ((cG kwT t - 1) % 4)) (rp (ks.getD ((cG kwT t - 1) / 4) 0))) - 1) / 32
          = t) := by
  intro t ht
  let Q : ℕ → Bool := fun t =>
      bif Nat.beq (cG kwT t) 0 then
        (let sc := rG vwT t
         Nat.beq (actC cmT (nT.get sc) (cG repT t)) (cG repT t) && decide (chiS5 (Sk k) sc = -1))
      else
        (let i := (cG kwT t - 1) / 4
         let b := (cG kwT t - 1) % 4
         inROK cmT nT repT (Sk k) t && Nat.blt i ks.length &&
         Nat.beq ((eG eM (actC cmT (klT.get b) (cG repT (ks.getD i 0))) - 1) / 32) t)
  have hpt : Q t = true := by
    rcases mem_chunks ht with h | h | h
    · exact (allL_iff_kleinSem klChunk0 Q).mp hcovA t h
    · exact (allL_iff_kleinSem klChunk1 Q).mp hcovB t h
    · exact (allL_iff_kleinSem klChunk2 Q).mp hcovC t h
  refine ⟨?_, ?_⟩
  · intro hk
    rcases (bif_zero_true_iff (cG kwT t) _ _).mp hpt with ⟨hk0, ha⟩ | ⟨hk0, _⟩
    · dsimp only at ha
      rw [Bool.and_eq_true] at ha
      exact ⟨Nat.beq_eq.mp ha.1, of_decide_eq_true ha.2⟩
    · exact absurd hk hk0
  · intro hk
    rcases (bif_zero_true_iff (cG kwT t) _ _).mp hpt with ⟨hk0, _⟩ | ⟨hk0, hb⟩
    · exact absurd hk0 hk
    · dsimp only at hb
      rw [Bool.and_eq_true] at hb
      have hin := hb.1
      rw [Bool.and_eq_true] at hin
      refine ⟨?_, Nat.blt_eq.mp hin.2, Nat.beq_eq.mp hb.2⟩
      intro sc hsc hfix
      have hh := (allR_iff_kleinSem 32 (inROKF cmT nT repT (Sk k) t)).mp (by rw [← inROK_eq]; exact hin.1)
        sc hsc
      rcases (Bool.or_eq_true ..).mp hh with hh | hh
      · have hh' : Nat.beq (actC cmT (nT.get sc) (cG repT t)) (cG repT t) = false := by
          simpa using hh
        exact absurd (show Nat.beq (actC cmT (nT.get sc) (cG repT t)) (cG repT t) = true by
          rw [show actC cmT (nT.get sc) (cG repT t) = cG repT t from hfix, Nat.beq_refl])
          (by simp [hh'])
      · exact of_decide_eq_true hh

/-- `kleinDistinctOK`: the Klein translates of distinct listed representatives lie in distinct
`N`-orbits. -/
lemma kleinDistinct_sound {klT kwT : NT} {ks : List ℕ}
    (h : kleinDistinctOK cmT eM repT klT kwT ks = true) :
    ∀ i < ks.length, cG kwT (ks.getD i 0) = 1 + 4 * i ∧ ∀ b < 4,
      (cG kwT ((em (actC cmT (klT.get b) (rp (ks.getD i 0))) - 1) / 32) - 1) / 4 = i := by
  intro i hi
  have h1 := (allIdx_iff ks (fun i t => Nat.beq (cG kwT t) (1 + 4 * i) && allR 4 (fun b =>
      Nat.beq ((cG kwT ((eG eM (actC cmT (klT.get b) (cG repT t)) - 1) / 32) - 1) / 4) i))
      0).mp h i hi
  simp only [Nat.zero_add] at h1
  rw [Bool.and_eq_true] at h1
  refine ⟨Nat.beq_eq.mp h1.1, fun b hb => ?_⟩
  have h2 := (allR_iff_kleinSem 4 (fun b => Nat.beq ((cG kwT ((eG eM (actC cmT (klT.get b)
      (cG repT (ks.getD i 0))) - 1) / 32) - 1) / 4) i)).mp h1.2 b hb
  exact Nat.beq_eq.mp h2

/-- `klColsOK`: the column data of the Klein translates (length agreement and the packing of the
signed `A`-action on the columns). -/
lemma klCols_sound {k : ℕ} {klT : NT} {ks ys : List ℕ}
    (h : klColsOK cmT eM repT klT (Sk k) ks ys = true) :
    ys.length = ks.length ∧
    ∀ j < ks.length, ∀ b < 4,
      ((ys.getD j 0 >>> (11 * b)) &&& 2047) =
        2 * ((em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1) / 32) +
          (if chiS5 (Sk k) ((em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1) % 32) = -1
            then 1 else 0) := by
  have h1 : eqL (ks.map (fun _ => 0)) (ys.map (fun _ => 0)) = true := by
    have hh := h; rw [klColsOK, Bool.and_eq_true] at hh; exact hh.1
  have h2 : allIdx ys (fun j yv => allR 4 (fun b => Nat.beq ((yv >>> (11 * b)) &&& 2047)
      (2 * ((eG eM (actC cmT (klT.get b) (cG repT (ks.getD j 0))) - 1) / 32) +
        (bif decide (chiS5 (Sk k) ((eG eM (actC cmT (klT.get b) (cG repT (ks.getD j 0))) - 1) % 32) = -1)
          then 1 else 0)))) 0 = true := by
    have hh := h; rw [klColsOK, Bool.and_eq_true] at hh; exact hh.2
  have hlen : ys.length = ks.length := by
    have he := congrArg List.length (eqL_eq _ _ h1)
    simp only [List.length_map] at he
    omega
  refine ⟨hlen, fun j hj b hb => ?_⟩
  have h3 := (allIdx_iff ys _ 0).mp h2 j (by omega)
  simp only [Nat.zero_add] at h3
  have h4 := (allR_iff_kleinSem 4 _).mp h3 b hb
  rw [Nat.beq_eq] at h4
  have h5 : (bif decide (chiS5 (Sk k)
        ((em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1) % 32) = -1) then (1 : ℕ) else 0) =
      (if chiS5 (Sk k) ((em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1) % 32) = -1
        then 1 else 0) :=
    bif_decide_ite _ _
  exact h4.trans (congrArg (fun x => 2 *
    ((em (actC cmT (klT.get b) (rp (ks.getD j 0))) - 1) / 32) + x) h5)

/-! ## Assembly -/

/-- The five clauses of `KleinSem k` from the five families of kernel checks on the data of
`k ≤ 5`. -/
lemma kleinSem_generic (k : ℕ) (klT kwT vwT : NT) (ks ys codes : List ℕ)
    (hklT : klT = klTs.getD k (NT.leaf 0)) (hks : ks = ksL.getD k [])
    (hys : ys = ysL.getD k []) (hkwT : kwT = kwTs.getD k (NT.leaf 0))
    (hvwT : vwT = vwTs.getD k (NT.leaf 0)) (h4c : 4 ≤ codes.length)
    (hcodes : ∀ b < 4, codes.getD b 0 = 32 * pcOf (kleinPerm k b))
    (htab : tabsOK codes klT = true)
    (hcovA : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk0 = true)
    (hcovB : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk1 = true)
    (hcovC : kleinCoverOK cmT eM nT repT klT kwT vwT (Sk k) ks klChunk2 = true)
    (hdist : kleinDistinctOK cmT eM repT klT kwT ks = true)
    (hcols : klColsOK cmT eM repT klT (Sk k) ks ys = true) :
    KleinSem k := by
  have h1 := tabsOK_sound htab h4c hcodes
  have h2 := kleinCover_sound hcovA hcovB hcovC
  have h3 := kleinDistinct_sound hdist
  obtain ⟨h4, h5⟩ := klCols_sound hcols
  unfold KleinSem
  dsimp only
  rw [← hklT, ← hks, ← hys, ← hkwT, ← hvwT]
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## The six base characters -/

lemma klCodes_spec0 (b : ℕ) (hb : b < 4) : klCodes0.getD b 0 = 32 * pcOf (kleinPerm 0 b) := by
  interval_cases b <;> decide +kernel
lemma klCodes_spec1 (b : ℕ) (hb : b < 4) : klCodes1.getD b 0 = 32 * pcOf (kleinPerm 1 b) := by
  interval_cases b <;> decide +kernel
lemma klCodes_spec2 (b : ℕ) (hb : b < 4) : klCodes2.getD b 0 = 32 * pcOf (kleinPerm 2 b) := by
  interval_cases b <;> decide +kernel
lemma klCodes_spec3 (b : ℕ) (hb : b < 4) : klCodes3.getD b 0 = 32 * pcOf (kleinPerm 3 b) := by
  interval_cases b <;> decide +kernel
lemma klCodes_spec4 (b : ℕ) (hb : b < 4) : klCodes4.getD b 0 = 32 * pcOf (kleinPerm 4 b) := by
  interval_cases b <;> decide +kernel
lemma klCodes_spec5 (b : ℕ) (hb : b < 4) : klCodes5.getD b 0 = 32 * pcOf (kleinPerm 5 b) := by
  interval_cases b <;> decide +kernel

lemma kleinSem0 : KleinSem 0 :=
  kleinSem_generic 0 klT0 kwT0 vwT0 ks0 ys0 klCodes0 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec0 C.kltab_ok0 C.klcov_ok0_0 C.klcov_ok0_1 C.klcov_ok0_2 C.kldist_ok0 C.klcols_ok0

lemma kleinSem1 : KleinSem 1 :=
  kleinSem_generic 1 klT1 kwT1 vwT1 ks1 ys1 klCodes1 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec1 C.kltab_ok1 C.klcov_ok1_0 C.klcov_ok1_1 C.klcov_ok1_2 C.kldist_ok1 C.klcols_ok1

lemma kleinSem2 : KleinSem 2 :=
  kleinSem_generic 2 klT2 kwT2 vwT2 ks2 ys2 klCodes2 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec2 C.kltab_ok2 C.klcov_ok2_0 C.klcov_ok2_1 C.klcov_ok2_2 C.kldist_ok2 C.klcols_ok2

lemma kleinSem3 : KleinSem 3 :=
  kleinSem_generic 3 klT3 kwT3 vwT3 ks3 ys3 klCodes3 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec3 C.kltab_ok3 C.klcov_ok3_0 C.klcov_ok3_1 C.klcov_ok3_2 C.kldist_ok3 C.klcols_ok3

lemma kleinSem4 : KleinSem 4 :=
  kleinSem_generic 4 klT4 kwT4 vwT4 ks4 ys4 klCodes4 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec4 C.kltab_ok4 C.klcov_ok4_0 C.klcov_ok4_1 C.klcov_ok4_2 C.kldist_ok4 C.klcols_ok4

lemma kleinSem5 : KleinSem 5 :=
  kleinSem_generic 5 klT5 kwT5 vwT5 ks5 ys5 klCodes5 rfl rfl rfl rfl rfl (by decide)
    klCodes_spec5 C.kltab_ok5 C.klcov_ok5_0 C.klcov_ok5_1 C.klcov_ok5_2 C.kldist_ok5 C.klcols_ok5

theorem kleinSem : ∀ k ≤ 5, KleinSem k := by
  intro k hk
  interval_cases k
  · exact kleinSem0
  · exact kleinSem1
  · exact kleinSem2
  · exact kleinSem3
  · exact kleinSem4
  · exact kleinSem5

end

end Work.PTCert
