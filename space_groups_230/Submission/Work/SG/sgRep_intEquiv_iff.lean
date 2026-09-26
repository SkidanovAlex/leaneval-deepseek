import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.Data.SepCheck
import Submission.Work.SG.arithRep_conj_eq
import Submission.Work.SG.arithRep_eq_data
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.sepList_lookup
import Submission.Work.SGsep.mergeList_lookup
import Submission.Work.SGsep.affIdx_lt
import Submission.Work.SGsep.sepOK_of_chk
import Submission.Work.SGsep.elem_separates
import Submission.Work.SGsep.sym_separates
import Submission.Work.SGsep.pair_separates
import Submission.Work.SGsep.hand_separates
import Submission.Work.SGsep.mergeList_sound
import Submission.Work.SGsep.IntEquiv_symm
import Submission.Work.SG.sgTau_eq_data
import Submission.Work.SGsep.repClass_eq_of_affIdx_eq

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md and Submission/Work/SG/Data/DATA.md first (orchestrator design + certificate data). Shared defs: Submission/Work/SG/Defs.lean (namespace Work.SG); data modules Submission/Work/SG/Data/* — do NOT edit any of them. Certificate checks use kernel decide only (no native_decide). Siblings run in parallel.

# sgRep_intEquiv_iff — the 230 are distinct; the 11 enantiomorphic merges (hard, ~1.5–2.5k lines)

**Claim.** For representatives `k, l`: an `IntEquiv` with `det U = 1` exists iff `k = l`, and one
with `det U = ±1` exists iff `sgAffClass k = sgAffClass l`.

**← directions.** OP: `U = 1`, `s = 0`. Affine: for each of the 11 merged pairs, an explicit
`det −1` normaliser element (from the `det ±1` orbits in `scripts/s4.py`).

**→ directions.** By `arithRep_conj_eq`, `sgArith k = sgArith l =: j`, so `U ∈ N(arithRep j)`.
Then separate with an invariant of `(P, τ)` under `(U, s)`. **Validated** in
`scripts/s5_invariants.py` (it separates all orbits of all 73 classes, both `det 1` and `±1`).
For each `A ∈ P` let `N_A := ∑_{i<ord A} Aⁱ` and let `v_A := N_A τ(A) ∈ ℤ³` (the intrinsic
screw/glide vector), well defined mod `N_A ℤ³`. The invariant has three parts:
* **Pair statistics.** The multiset over ordered pairs `(A, B) ∈ P²` of:
  * `det A`, `tr A`, `det B`, `tr B`;
  * the order of `v_A` in `ℤ³/N_Aℤ³`, and the same for `v_B`;
  * for `L_B ∈ {Λ^B, Λ^{−B}, (B−1)ℤ³, (B+1)ℤ³, N_Bℤ³}` (`Λ^B := ker(B−1) ∩ ℤ³`): the bit
    `v_A ∈ L_B + N_Aℤ³`;
  * for `X ∈ {Λ^A, Λ^{−A}}` and the same five `L_B`: `(rank(X ∩ L_B), saturation index of
    X ∩ L_B in X)`. This part is τ-free.
* **Symmorphy order.** The order of `[τ]` in `H¹(P, ℝ³/ℤ³)`, i.e. the least `o` with `oτ` a
  coboundary. Test it with integer left-kernel vectors `u` of the stacked `(1 − A)`:
  `oτ` is a coboundary iff `∑ u·(oτ) ∈ ℤ` for all such `u`.
* **Handedness** (only for `det U = 1`). For each rotation `A` (`det 1`, order `k ≥ 3`): let
  `c` be the primitive axis vector oriented so that `det(u, Au, c) > 0`, write `v_A = j c`, and
  let `h` be defined by `N_Aℤ³ = hℤc`. Record `(k, h, j mod h)`. For the `±1` version use
  `{j, −j} mod h`.

Each part is natural under `A ↦ UAU⁻¹`, `τ ↦ Uτ(U⁻¹·U) + (1 − ·)s`: `v_{UAU⁻¹} = U v_A` mod
`N_{UAU⁻¹}ℤ³`, since the coboundary term is killed by `N`. All lattices transform by `U`.
Orientation of `c` is preserved exactly when `det U > 0`. Prove invariance once, generically.
Then for each pair `k ≠ l` of representatives in the same class, compute only **one**
distinguishing component. Membership bits need certificates: the combination for "yes", a dual
functional for "no". Checking these is cheap in the kernel.

**Dropping parts fails.** Without the symmorphy order: I222/I2₁2₁2₁ and I23/I2₁3 collide.
Without the τ-free pair data: P6₃cm/P6₃mc and P6₃/mcm/P6₃/mmc collide. Without the partner's
glide order: Pbcn collides with its partner in the Pmmm family.


**Data (built, kernel-checked).** Import `Submission.Work.SG.Data.SepCheck`, which provides `sepList_cover`, `sepList_chk`, `mergeList_chk` and `elemTab_chk`. The invariant menu in the data is `.elem`/`.sym`/`.pair`/`.hand` (see `data/DATA.md` §Separation); it supersedes the feature list above. Prove one invariance lemma per family.
-/

namespace Work.SG


/-- The tabulated values of `sgTau` (the sibling deliverable `sgTau_eq_data` rephrased). -/
theorem Work.SGsep.TauOnTable_all (k : Fin 230) : TauOnTable k := by
  intro i hi
  exact sgTau_eq_data k i hi

/-! ## Assembly lemmas for `sgRep_intEquiv_iff`

The four invariant families (`elem`/`sym`/`pair`/`hand`) are proved to separate in the sibling
modules under `Submission/Work/SGsep/`; here we assemble them. -/

open LeanEval.Geometry.SpaceGroupsProblem

/-- Reindexing the affine class. -/
theorem sgAffClass_eq_of_affIdx_eq {k l : Fin 230} (h : Data.affIdx k = Data.affIdx l) :
    sgAffClass k = sgAffClass l := by
  have h' : (sgDataList.getD k.val (0, 1, [], 0)).2.2.2 =
      (sgDataList.getD l.val (0, 1, [], 0)).2.2.2 := h
  refine Fin.ext ?_
  simp only [sgAffClass]
  rw [h']

/-- The stored class index of `sgArith k` is `Data.repClass k`. -/
theorem sgArith_val_eq (k : Fin 230) : (sgArith k).val = Data.repClass k := by
  have h := (Work.SGsep.table_facts k).1
  simp only [sgArith, Data.repClass] at h ⊢
  exact Nat.mod_eq_of_lt h

/-- Equal arithmetic class gives equal stored class index. -/
theorem repClass_eq_of_sgArith_eq {k l : Fin 230} (h : sgArith k = sgArith l) :
    Data.repClass k = Data.repClass l := by
  rw [← sgArith_val_eq k, ← sgArith_val_eq l, h]

/-- The two entries of `Data.mergeList` have `Data.M3.det = -1` (certified by `mergeList_chk`). -/
theorem mergeList_det (k : ℕ) (c : Data.ConjCert) (hc : (k, c) ∈ Data.mergeList) :
    Data.M3.det c.U = -1 := by
  obtain ⟨-, h2⟩ := Data.mergeList_chk
  have h := List.all_eq_true.mp h2 (k, c) hc
  simp only [Bool.and_eq_true] at h
  simpa using h.1

/-- Reflexivity of integral equivalence. -/
theorem IntEquiv_refl (P : Set IMat) (τ : IMat → Fin 3 → ℝ) : IntEquiv P τ P τ 1 0 := by
  constructor
  · intro A
    simp
  · intro B _
    refine ⟨0, ?_⟩
    simp only [Matrix.one_mulVec, intVec, Pi.zero_apply, sub_zero, add_zero]
    funext i
    simp [intVec]

/-- The separation lemmas exclude integral equivalence with `det U = 1` for a `sepList` pair
`a < b` of the same arithmetic class. -/
theorem sep_not_intEquiv_det_one_lt {a b : Fin 230} (hab : a.val < b.val)
    (hclass : Data.repClass a = Data.repClass b)
    (ha : TauOnTable a) (hb : TauOnTable b) :
    ¬ ∃ U : IMat, U.det = 1 ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith a)) (sgTau a) (arithRep (sgArith b)) (sgTau b) U s := by
  obtain ⟨e, he, hekl, hechk⟩ := Work.SGsep.sepList_lookup a.isLt b.isLt hab hclass
  have hOK := Work.SGsep.sepOK_of_chk e he hechk
  cases e with
  | elem k l d t o =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      rintro ⟨U, hU1, s, hInt⟩
      have hU : IsUnit U.det := by rw [hU1]; exact isUnit_one
      exact Work.SGsep.elem_separates a b d t o ha hb hOK ⟨U, hU, s, hInt⟩
  | sym k l x y =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      rintro ⟨U, hU1, s, hInt⟩
      have hU : IsUnit U.det := by rw [hU1]; exact isUnit_one
      exact Work.SGsep.sym_separates a b x y ha hb hOK.1 hOK.2.1 hOK.2.2.1 hOK.2.2.2.1
        hOK.2.2.2.2 ⟨U, hU, s, hInt⟩
  | hand k l o h jm ta tb =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      rintro ⟨U, hU1, s, hInt⟩
      exact Work.SGsep.hand_separates a b o h jm ta tb ha hb hOK.2.1 hOK.2.2.1
        (fun i hi => hOK.2.2.2.1 i hi) (fun i hi => hOK.2.2.2.2.1 i hi) hOK.2.2.2.2.2
        ⟨U, hU1, s, hInt⟩
  | pair k l dA tA oA dB tB oB bits la lb =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      rintro ⟨U, hU1, s, hInt⟩
      have hU : IsUnit U.det := by rw [hU1]; exact isUnit_one
      obtain ⟨ca, cb, hca, hcb, hne⟩ := hOK
      exact Work.SGsep.pair_separates a b dA tA oA dB tB oB bits la lb ca cb ha hb
        hca hcb hne ⟨U, hU, s, hInt⟩

/-- For a `sepList` pair `a < b`, an integral equivalence forces equal affine classes (only the
`hand` entries allow an equivalence, and they carry `affIdx a = affIdx b`). -/
theorem affClass_eq_of_intEquiv_lt {a b : Fin 230} (hab : a.val < b.val)
    (hclass : Data.repClass a = Data.repClass b)
    (ha : TauOnTable a) (hb : TauOnTable b)
    (U : IMat) (s : Fin 3 → ℝ) (hU : IsUnit U.det)
    (h : IntEquiv (arithRep (sgArith a)) (sgTau a) (arithRep (sgArith b)) (sgTau b) U s) :
    sgAffClass a = sgAffClass b := by
  obtain ⟨e, he, hekl, hechk⟩ := Work.SGsep.sepList_lookup a.isLt b.isLt hab hclass
  have hOK := Work.SGsep.sepOK_of_chk e he hechk
  cases e with
  | elem k l d t o =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      exact absurd ⟨U, hU, s, h⟩ (Work.SGsep.elem_separates a b d t o ha hb hOK)
  | sym k l x y =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      exact absurd ⟨U, hU, s, h⟩
        (Work.SGsep.sym_separates a b x y ha hb hOK.1 hOK.2.1 hOK.2.2.1 hOK.2.2.2.1 hOK.2.2.2.2)
  | hand k l o hh jm ta tb =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      exact sgAffClass_eq_of_affIdx_eq hOK.1
  | pair k l dA tA oA dB tB oB bits la lb =>
      have h1 : k = a.val := by simpa [Data.Sep.kl] using congrArg Prod.fst hekl
      have h2 : l = b.val := by simpa [Data.Sep.kl] using congrArg Prod.snd hekl
      subst h1; subst h2
      simp only [SepOK] at hOK
      obtain ⟨ca, cb, hca, hcb, hne⟩ := hOK
      exact absurd ⟨U, hU, s, h⟩
        (Work.SGsep.pair_separates a b dA tA oA dB tB oB bits la lb ca cb ha hb hca hcb hne)

/-- Forward direction for `det U = 1`: only equal representatives are related. -/
theorem fwd_det_one (k l : Fin 230) (U : IMat) (s : Fin 3 → ℝ) (hUdet : U.det = 1)
    (h : IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s) :
    k = l := by
  by_contra hne
  have hU : IsUnit U.det := by rw [hUdet]; exact isUnit_one
  have hjk : sgArith k = sgArith l := arithRep_conj_eq hU h.1
  have hclass : Data.repClass k = Data.repClass l := repClass_eq_of_sgArith_eq hjk
  have hne' : k.val ≠ l.val := fun h' => hne (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact sep_not_intEquiv_det_one_lt (a := k) (b := l) hlt hclass
      (Work.SGsep.TauOnTable_all k) (Work.SGsep.TauOnTable_all l) ⟨U, hUdet, s, h⟩
  · exact sep_not_intEquiv_det_one_lt (a := l) (b := k) hlt hclass.symm
      (Work.SGsep.TauOnTable_all l) (Work.SGsep.TauOnTable_all k)
      ⟨invMat U, by rw [det_invMat hU, hUdet], _,
        Work.SGsep.IntEquiv_symm hU h⟩

/-- Forward direction for `det U = ±1`. -/
theorem fwd_unit (k l : Fin 230) (U : IMat) (s : Fin 3 → ℝ) (hU : IsUnit U.det)
    (h : IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s) :
    sgAffClass k = sgAffClass l := by
  by_cases hkl : k = l
  · subst hkl; rfl
  have hjk : sgArith k = sgArith l := arithRep_conj_eq hU h.1
  have hclass : Data.repClass k = Data.repClass l := repClass_eq_of_sgArith_eq hjk
  have hne' : k.val ≠ l.val := fun h' => hkl (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact affClass_eq_of_intEquiv_lt (a := k) (b := l) hlt hclass
      (Work.SGsep.TauOnTable_all k) (Work.SGsep.TauOnTable_all l) U s hU h
  · exact (affClass_eq_of_intEquiv_lt (a := l) (b := k) hlt hclass.symm
      (Work.SGsep.TauOnTable_all l) (Work.SGsep.TauOnTable_all k) (invMat U) _
      (isUnit_det_invMat hU) (Work.SGsep.IntEquiv_symm hU h)).symm

/-- Backward direction: an affine-class equality is realised by an integral equivalence. -/
theorem bwd_unit (k l : Fin 230) (h : sgAffClass k = sgAffClass l) :
    ∃ U : IMat, IsUnit U.det ∧ ∃ s : Fin 3 → ℝ,
      IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s := by
  by_cases hkl : k = l
  · subst hkl
    exact ⟨1, isUnit_one, 0, IntEquiv_refl _ _⟩
  have hmod : Data.affIdx k % 219 = Data.affIdx l % 219 := by
    have := congrArg Fin.val h
    simpa [sgAffClass, Data.affIdx] using this
  have haff : Data.affIdx k = Data.affIdx l := by
    rw [← Nat.mod_eq_of_lt (Work.SGsep.affIdx_lt k),
      ← Nat.mod_eq_of_lt (Work.SGsep.affIdx_lt l)]
    exact hmod
  have hclass : Data.repClass k = Data.repClass l := Work.SGsep.repClass_eq_of_affIdx_eq haff
  have hne' : k.val ≠ l.val := fun h' => hkl (Fin.ext h')
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · obtain ⟨c, hc, hck⟩ := Work.SGsep.mergeList_lookup k.isLt l.isLt hlt hclass haff
    obtain ⟨s, hs⟩ := Work.SGsep.mergeList_sound k l c (Work.SGsep.TauOnTable_all k)
      (Work.SGsep.TauOnTable_all l) hc hck.symm
    exact ⟨Data.M3.toIMat c.U, by
      rw [Data.M3.toIMat_det, mergeList_det k c hc]
      exact isUnit_neg_one, s, hs⟩
  · obtain ⟨c, hc, hck⟩ := Work.SGsep.mergeList_lookup l.isLt k.isLt hlt hclass.symm haff.symm
    obtain ⟨s, hs⟩ := Work.SGsep.mergeList_sound l k c (Work.SGsep.TauOnTable_all l)
      (Work.SGsep.TauOnTable_all k) hc hck.symm
    exact ⟨invMat (Data.M3.toIMat c.U), isUnit_det_invMat (by
        rw [Data.M3.toIMat_det, mergeList_det l c hc]
        exact isUnit_neg_one), _,
      Work.SGsep.IntEquiv_symm (by
        rw [Data.M3.toIMat_det, mergeList_det l c hc]
        exact isUnit_neg_one) hs⟩

/-- Separation of the 230 representatives: integral equivalence with `det U = 1` identifies
exactly equal indices, and with `det U = ±1` exactly equal affine classes. -/
theorem sgRep_intEquiv_iff (k l : Fin 230) :
    ((∃ U : IMat, U.det = 1 ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s) ↔
      k = l) ∧
    ((∃ U : IMat, IsUnit U.det ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s) ↔
      sgAffClass k = sgAffClass l) := by
  constructor
  · constructor
    · rintro ⟨U, hU1, s, h⟩
      exact fwd_det_one k l U s hU1 h
    · intro hkl
      subst hkl
      exact ⟨1, rfl, 0, IntEquiv_refl _ _⟩
  · constructor
    · rintro ⟨U, hU, s, h⟩
      exact fwd_unit k l U s hU h
    · intro h
      exact bwd_unit k l h

end Work.SG
