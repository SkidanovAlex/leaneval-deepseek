import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SGinfra
import Submission.Work.SG.SGfacts
import Submission.Work.SG.SGgens
import Submission.Work.SG.imatOfList_inj
import Submission.Work.SG.det9_spec
import Submission.Work.SG.det9_mul
import Submission.Work.SG.mulVec_imatOfList
import Submission.Work.SG.m9vec_apply
import Submission.Work.SG.sgMulPair_toPair
import Submission.Work.SG.sgClose_map_toPair
import Submission.Work.SG.sgClose_map_fst
import Submission.Work.SG.zClose_map_fst
import Submission.Work.SG.zMul_assoc
import Submission.Work.SG.zMul_zOne
import Submission.Work.SG.find_some_of_unique
import Submission.Work.SG.isWordProd_of_mem_mClose
import Submission.Work.SG.det9_foldl_m9mul

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# sg_data_facts — sanity of the generated tables (computational, ~200–500 lines)

**Claims.** (1) Each `arithRep j` is an integral point group. (2) Each `sgTau k` is a cocycle on
its class. (3) `sgAffClass` is onto `Fin 219`. (4) Exactly 65 representatives have all
`det = 1`.

The proof strategy (this file) is:
* all computations are carried out on `ℤ`-data (`SGprelude`/`SGdata`), because the kernel cannot
  evaluate `ℚ` arithmetic (`Rat` operations are `irreducible`);
* a general bridge (`sgClose_map_toPair`, `sgMulPair_toPair`) transfers the `ℤ` closure to the
  `ℚ`-side `sgTable` of `Defs`, and the certificate data (`SGdata`) is checked by `decide`.
-/

open LeanEval.Geometry.SpaceGroupsProblem

namespace Work.SG

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## The `ℚ`-side table is the `toPair`-image of the certified `ℤ`-side table -/

/-- The image of the certified integer table in the `ℚ`-side affine pairs. -/
def S₀ (k : Fin 230) : Set (List ℤ × List ℚ) :=
  {x | ∃ t ∈ TZ k, toPair (sgDen k) t = x}

/-- The denominators occurring in the data are positive. -/
theorem TZpos (k : Fin 230) : 0 < sgDen k := by
  have h := TZred k zOne (TZone k) 0 (by simp [zOne])
  have h2 : (0 : ℤ) < (sgDen k : ℤ) := h.2
  omega

/-- `S₀` is closed under right multiplication by the generators. -/
theorem S₀_closed (k : Fin 230) : ∀ a ∈ S₀ k, ∀ g ∈ gensQ k, sgMulPair a g ∈ S₀ k := by
  rintro a ⟨t, ht, rfl⟩ g hg
  rw [gensQ_eq_gensZ k] at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  exact ⟨zMul (sgDen k) t g0, TZclo k t ht g0 hg0, (sgMulPair_toPair (sgDen k) t g0).symm⟩

/-- The `ℚ`-side table is contained in `S₀` (the closed-set lemma). -/
theorem sgTable_subset_S₀ (k : Fin 230) : ∀ x ∈ sgTable k, x ∈ S₀ k := by
  rw [sgTable_eq]
  intro x hx
  refine sgClose_subset_of_closed ?_ (fun a ha g hg => S₀_closed k a ha g hg) 48 hx
  intro y hy
  rw [List.mem_singleton] at hy
  subst hy
  exact ⟨zOne, TZone k, toPair_zOne (sgDen k)⟩

/-- The certified `ℤ`-side table contains no more elements than its closure. -/
theorem zClose_subset_TZ (k : Fin 230) :
    ∀ t, t ∈ zClose (gensZ k) (sgDen k) 48 [zOne] → t ∈ TZ k := by
  intro t ht
  exact zClose_subset_of_closed (S := {x : List ℤ × List ℤ | x ∈ TZ k})
    (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact TZone k)
    (fun a ha g hg => TZclo k a ha g hg) 48 (acc := [zOne]) ht

/-- `S₀` is contained in the `ℚ`-side table: the transfer lemma for the closures. -/
theorem S₀_subset_sgTable (k : Fin 230) : ∀ x ∈ S₀ k, x ∈ sgTable k := by
  rintro x ⟨t, ht, rfl⟩
  rw [sgTable_eq, gensQ_eq_gensZ k]
  rw [show ([sgOne] : List (List ℤ × List ℚ)) = [zOne].map (toPair (sgDen k)) from by
    simp [toPair_zOne]]
  rw [sgClose_map_toPair (TZpos k) (gensZ k) [zOne] 48]
  exact List.mem_map.mpr ⟨t, TZ_subset_zClose k t ht, rfl⟩

/-- The `ℚ`-side table coincides with the image of the integer table. -/
theorem sgTable_eq_S₀ (k : Fin 230) : ∀ x, x ∈ sgTable k ↔ x ∈ S₀ k :=
  fun x => ⟨sgTable_subset_S₀ k x, S₀_subset_sgTable k x⟩

/-! ## Algebra in `S₀` -/

/-- Multiplication of `toPair`-elements is associative. -/
theorem sgMulPair_assoc_S₀ (k : Fin 230) : ∀ a ∈ S₀ k, ∀ b ∈ S₀ k, ∀ c ∈ S₀ k,
    sgMulPair a (sgMulPair b c) = sgMulPair (sgMulPair a b) c := by
  rintro a ⟨ta, hta, rfl⟩ b ⟨tb, htb, rfl⟩ c ⟨tc, htc, rfl⟩
  rw [sgMulPair_toPair, sgMulPair_toPair, sgMulPair_toPair, sgMulPair_toPair]
  exact congrArg (toPair (sgDen k))
    (zMul_assoc (TZshape k ta hta).2 (TZshape k tb htb).2 (TZshape k tc htc).2).symm

/-- The identity is neutral on the right. -/
theorem sgMulPair_one_S₀ (k : Fin 230) : ∀ a ∈ S₀ k, sgMulPair a sgOne = a := by
  rintro a ⟨t, ht, rfl⟩
  rw [← toPair_zOne (sgDen k), sgMulPair_toPair,
    zMul_zOne (TZshape k t ht).1 (TZshape k t ht).2 (TZred k t ht)]

/-! ## Generators of the certified tables -/

/-- Membership in a zip gives membership of both components. -/
theorem mem_zip_shape {α β : Type*} {l : List α} {m : List β} {p : α × β}
    (hp : p ∈ l.zip m) : p.1 ∈ l ∧ p.2 ∈ m := by
  induction l generalizing m with
  | nil => simp at hp
  | cons a l ih =>
      cases m with
      | nil => simp at hp
      | cons b m =>
          rw [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨by simp, by simp⟩
          · obtain ⟨h1, h2⟩ := ih hp
            exact ⟨by simp [h1], by simp [h2]⟩

/-- The generators have the right shape. -/
theorem gensZ_shape (k : Fin 230) : ∀ g ∈ gensZ k, g.1.length = 9 ∧ g.2.length = 3 := by
  intro g hg
  rw [gensZ] at hg
  obtain ⟨h1, h2⟩ := mem_zip_shape hg
  refine ⟨?_, ?_⟩
  · simp only [arithGens, List.mem_map] at h1
    obtain ⟨c, -, hceq⟩ := h1
    rw [← hceq]
    simp [codeToList]
  · simp only [sgGenTransZ, List.mem_map] at h2
    obtain ⟨i, -, hieq⟩ := h2
    rw [← hieq]
    simp

/-- Associativity for an arbitrary element on the right (a generator). -/
theorem sgMulPair_assoc_gens (k : Fin 230) : ∀ a ∈ S₀ k, ∀ c ∈ S₀ k, ∀ g ∈ gensQ k,
    sgMulPair a (sgMulPair c g) = sgMulPair (sgMulPair a c) g := by
  rintro a ⟨ta, hta, rfl⟩ c ⟨tc, htc, rfl⟩ g hg
  rw [gensQ_eq_gensZ k] at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  rw [sgMulPair_toPair, sgMulPair_toPair, sgMulPair_toPair, sgMulPair_toPair]
  exact congrArg (toPair (sgDen k))
    (zMul_assoc (TZshape k ta hta).2 (TZshape k tc htc).2 (gensZ_shape k g0 hg0).2).symm

/-! ## The table is a subsemigroup -/

/-- Membership in the `ℚ`-side table, in closure form. -/
theorem sgTable_eq_sgClose_apply (k : Fin 230) {x : List ℤ × List ℚ} :
    x ∈ sgTable k ↔ x ∈ sgClose (gensQ k) 48 [sgOne] := by
  rw [sgTable_eq]

/-- `S₀` is contained in the closure. -/
theorem S₀_subset_sgClose (k : Fin 230) : ∀ x ∈ S₀ k, x ∈ sgClose (gensQ k) 48 [sgOne] := by
  intro x hx
  rw [← sgTable_eq k]
  exact (sgTable_eq_S₀ k x).mpr hx

/-- Full closure of `S₀` (the `ℤ`-table image) under multiplication. -/
theorem S₀_mul (k : Fin 230) : ∀ a ∈ S₀ k, ∀ b ∈ S₀ k, sgMulPair a b ∈ S₀ k := by
  intro a haS b hbS
  have hbC : b ∈ sgClose (gensQ k) 48 [sgOne] := S₀_subset_sgClose k b hbS
  have key : ∀ c, c ∈ sgClose (gensQ k) 48 [sgOne] →
      c ∈ S₀ k ∧ sgMulPair a c ∈ S₀ k := by
    intro c hc
    refine sgClose_subset_of_closed (gens := gensQ k) (acc := [sgOne])
      (S := {c : List ℤ × List ℚ | c ∈ S₀ k ∧ sgMulPair a c ∈ S₀ k}) ?_ ?_ 48 hc
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      refine ⟨⟨zOne, TZone k, toPair_zOne (sgDen k)⟩, ?_⟩
      rw [sgMulPair_one_S₀ k a haS]
      exact haS
    · intro c' hc' g hg
      obtain ⟨hcS₀, hcp⟩ := hc'
      refine ⟨S₀_closed k c' hcS₀ g hg, ?_⟩
      rw [sgMulPair_assoc_gens k a haS c' hcS₀ g hg]
      exact S₀_closed k (sgMulPair a c') hcp g hg
  exact (key b hbC).2

/-- Multiplication by a generator stays in the table. -/
theorem sgTable_mul_gen (k : Fin 230) : ∀ a ∈ sgTable k, ∀ g ∈ gensQ k, sgMulPair a g ∈ sgTable k := by
  intro a ha g hg
  exact (sgTable_eq_sgClose_apply k).mpr
    (S₀_subset_sgClose k _ (S₀_closed k a ((sgTable_eq_S₀ k a).mp ha) g hg))

/-- The table is closed under multiplication. -/
theorem sgTable_mul (k : Fin 230) : ∀ a ∈ sgTable k, ∀ b ∈ sgTable k, sgMulPair a b ∈ sgTable k := by
  intro a ha b hb
  exact (sgTable_eq_sgClose_apply k).mpr
    (S₀_subset_sgClose k _ (S₀_mul k a ((sgTable_eq_S₀ k a).mp ha) b ((sgTable_eq_S₀ k b).mp hb)))

/-- The identity belongs to the table. -/
theorem sgOne_mem_sgTable (k : Fin 230) : sgOne ∈ sgTable k := by
  rw [sgTable_eq]
  exact sgOne_mem_sgClose (gensQ k) 48

/-! ## The translation cocycle -/

/-- Two table entries with the same matrix are equal. -/
theorem sgTable_eq_of_mat (k : Fin 230) : ∀ a ∈ sgTable k, ∀ b ∈ sgTable k,
    imatOfList a.1 = imatOfList b.1 → a = b := by
  intro a ha b hb hM
  obtain ⟨ta, hta, rfl⟩ := (sgTable_eq_S₀ k a).mp ha
  obtain ⟨tb, htb, rfl⟩ := (sgTable_eq_S₀ k b).mp hb
  have h1 : ta.1 = tb.1 :=
    imatOfList_inj (TZshape k ta hta).1 (TZshape k tb htb).1 hM
  have h2 : ta = tb := List.inj_on_of_nodup_map (TZnodup k) hta htb h1
  rw [h2]

/-- The value of `sgTau` on a matrix which occurs in the table. -/
theorem sgTau_eq_of_mat (k : Fin 230) : ∀ a ∈ sgTable k, ∀ i : Fin 3,
    sgTau k (imatOfList a.1) i = ((a.2.getD i.val 0 : ℚ) : ℝ) := by
  intro a ha i
  have hfind : (sgTable k).find? (fun p => decide (imatOfList p.1 = imatOfList a.1)) = some a :=
    find_some_of_unique ha (by simp)
      (fun b hb hpb => sgTable_eq_of_mat k b hb a ha (of_decide_eq_true hpb))
  simp only [sgTau, hfind, Option.map_some, Option.getD_some]

/-- `divQ` is additive. -/
theorem divQ_add (d : ℕ) (x y : ℤ) : divQ d x + divQ d y = divQ d (x + y) := by
  simp only [divQ, Int.cast_add, add_div]

/-- `Int.fract` of `q/d` is `(q % d)/d`. -/
theorem fract_divQ (d : ℕ) (n : ℤ) : Int.fract (divQ d n) = divQ d (n % (d : ℤ)) := by
  simp only [divQ]
  rw [Int.fract_div_intCast_eq_div_intCast_mod]

/-- `getD` of a scaled list. -/
theorem getD_toPairL (d : ℕ) (v : List ℤ) (i : Fin 3) :
    (toPairL d v).getD i.val 0 = divQ d (v.getD i.val 0) := by
  have h0 : divQ d 0 = 0 := by simp [divQ]
  rw [toPairL, ← h0, List.getD_map, divQ]

/-- `getD` of a reduced list. -/
theorem getD_emodList (d : ℕ) (v : List ℤ) (i : Fin 3) :
    (emodList d v).getD i.val 0 = v.getD i.val 0 % (d : ℤ) := by
  have h := List.getD_map v (0 : ℤ) (n := i.val) (f := fun x : ℤ => x % (d : ℤ))
  simpa [emodList] using h

/-- The component form of `m9vecZ`. -/
theorem m9vecZ_apply (a v : List ℤ) (i : Fin 3) :
    (m9vecZ a v).getD i.val 0 =
      ((List.finRange 3).map fun k => a.getD (3 * i.val + k.val) 0 * v.getD k.val 0).sum := by
  fin_cases i <;> simp [m9vecZ, List.finRange, List.range_succ]

/-- `m9vecZ` produces three entries. -/
theorem m9vecZ_length (a v : List ℤ) : (m9vecZ a v).length = 3 := by
  simp [m9vecZ, List.finRange, List.range_succ]

/-- `getD` of a pointwise sum of two lists of length `3`. -/
theorem getD_zipWith_add {u w : List ℤ} (hu : u.length = 3) (hw : w.length = 3) (i : Fin 3) :
    (u.zipWith (· + ·) w).getD i.val 0 = u.getD i.val 0 + w.getD i.val 0 := by
  obtain ⟨u0, u1, u2, rfl⟩ := List.length_eq_three.mp hu
  obtain ⟨w0, w1, w2, rfl⟩ := List.length_eq_three.mp hw
  fin_cases i <;> rfl

/-- Casting a sum of rationals to `ℝ`. -/
theorem sum_cast (l : List ℚ) : ((l.sum : ℚ) : ℝ) = (l.map (fun q => (q : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- `divQ` distributes over a sum. -/
theorem divQ_list_sum (d : ℕ) (l : List ℤ) : divQ d l.sum = (l.map (divQ d)).sum := by
  induction l with
  | nil => simp [divQ]
  | cons a l ih => rw [List.sum_cons, ← divQ_add, ih]; simp [List.map_cons, List.sum_cons]

/-- Scaling a sum of products by `1/d`. -/
theorem divQ_finRange_sum (d : ℕ) (u w : ℕ → ℤ) :
    ((divQ d (((List.finRange 3).map fun k : Fin 3 => u k.val * w k.val).sum) : ℚ) : ℝ)
      = ((List.finRange 3).map fun k : Fin 3 =>
          (u k.val : ℝ) * ((divQ d (w k.val) : ℚ) : ℝ)).sum := by
  induction (List.finRange 3) with
  | nil => simp [divQ]
  | cons k l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        ← divQ_add d (u k.val * w k.val) ((l.map fun j => u j.val * w j.val).sum)]
      push_cast
      rw [ih]
      simp only [divQ, div_eq_mul_inv, Int.cast_mul, Int.cast_natCast]
      push_cast
      ring

/-! ### The cocycle identity, componentwise

The cocycle identity is proved by first computing the value of `sgTau` on a table matrix
(`sgTau_eq_of_mat`) and then comparing, component by component, the two rational numbers
described by the two sides: on the `ℤ`-side `sgMulPair` reduces the translation with
`Int.fract`, and `Int.fract x = x - ⌊x⌋` converts this into exactly the correction term of the
cocycle identity. -/

/-- `Int.fract` as subtraction of the integer part. -/
theorem fract_add_neg_floor (x : ℚ) : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℚ) := by
  rw [Int.fract]
  push_cast
  ring

/-- Componentwise `getD` of a pointwise sum of two length-`3` rational lists. -/
theorem getD_zipWith_add_rat {u w : List ℚ} (hu : u.length = 3) (hw : w.length = 3) (i : Fin 3) :
    (List.zipWith (· + ·) u w).getD i.val 0 = u.getD i.val 0 + w.getD i.val 0 := by
  obtain ⟨u0, u1, u2, rfl⟩ := List.length_eq_three.mp hu
  obtain ⟨w0, w1, w2, rfl⟩ := List.length_eq_three.mp hw
  fin_cases i <;> rfl

/-- The fractional part of a pointwise sum of two length-`3` rational lists. -/
theorem getD_map_fract_zipWith {u w : List ℚ} (hu : u.length = 3) (hw : w.length = 3)
    (i : Fin 3) :
    ((List.zipWith (· + ·) u w).map Int.fract).getD i.val 0
      = Int.fract (u.getD i.val 0 + w.getD i.val 0) := by
  obtain ⟨u0, u1, u2, rfl⟩ := List.length_eq_three.mp hu
  obtain ⟨w0, w1, w2, rfl⟩ := List.length_eq_three.mp hw
  fin_cases i <;> rfl

/-- `toPairL` preserves the length. -/
theorem toPairL_length (d : ℕ) (v : List ℤ) : (toPairL d v).length = v.length := by
  simp [toPairL]

/-- `m9vec` produces three entries. -/
theorem m9vec_length (a : List ℤ) (v : List ℚ) : (m9vec a v).length = 3 := by
  simp only [m9vec, List.length_map, List.length_range]

/-- Casting a sum of rationals along an arbitrary list. -/
theorem cast_sum_map {α : Type*} (l : List α) (f : α → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = ((l.map (fun a => ((f a : ℚ) : ℝ))).sum) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- `mulVec` of a cast flat matrix against the cast of a rational vector, computed as a
rational number. -/
theorem mulVec_cast_getD (a : List ℤ) (v : List ℚ) (i : Fin 3) :
    ((imatOfList a).map (Int.cast : ℤ → ℝ)).mulVec (fun j => ((v.getD j.val 0 : ℚ) : ℝ)) i
      = (((m9vec a v).getD i.val 0 : ℚ) : ℝ) := by
  rw [mulVec_imatOfList, m9vec_apply a v i, cast_sum_map]
  congr 1
  apply List.map_congr_left
  intro k _
  push_cast
  ring

/-- The cocycle identity for a pair of table entries, componentwise. -/
theorem sgTau_cocycle_of_mem_apply (k : Fin 230) (a : List ℤ × List ℚ) (ha : a ∈ sgTable k)
    (b : List ℤ × List ℚ) (hb : b ∈ sgTable k) (i : Fin 3) :
    sgTau k (imatOfList a.1 * imatOfList b.1) i
      = sgTau k (imatOfList a.1) i
        + (((imatOfList a.1).map (Int.cast : ℤ → ℝ)).mulVec (sgTau k (imatOfList b.1))) i
        + (intVec (fun i => -⌊(a.2.getD i.val 0 + (m9vec a.1 b.2).getD i.val 0 : ℚ)⌋)) i := by
  obtain ⟨ta, hta, haeq⟩ := (sgTable_eq_S₀ k a).mp ha
  obtain ⟨tb, htb, hbeq⟩ := (sgTable_eq_S₀ k b).mp hb
  have ha2len : a.2.length = 3 := by
    rw [← haeq, toPair_snd, toPairL_length]
    exact (TZshape k ta hta).2
  have hmul : sgMulPair a b ∈ sgTable k := sgTable_mul k a ha b hb
  have hsb' : sgTau k (imatOfList b.1) = (fun j : Fin 3 => ((b.2.getD j.val 0 : ℚ) : ℝ)) :=
    funext fun j => sgTau_eq_of_mat k b hb j
  have hprod : sgTau k (imatOfList a.1 * imatOfList b.1)
      = (fun i : Fin 3 => (((sgMulPair a b).2.getD i.val 0 : ℚ) : ℝ)) := by
    funext i
    rw [← imatOfList_mul]
    have h := sgTau_eq_of_mat k (sgMulPair a b) hmul i
    rwa [show (sgMulPair a b).1 = m9mul a.1 b.1 from rfl] at h
  rw [hprod, hsb', sgTau_eq_of_mat k a ha i]
  show (((sgMulPair a b).2.getD i.val 0 : ℚ) : ℝ)
      = ((a.2.getD i.val 0 : ℚ) : ℝ)
        + (((imatOfList a.1).map (Int.cast : ℤ → ℝ)).mulVec
            (fun j : Fin 3 => ((b.2.getD j.val 0 : ℚ) : ℝ)) i)
        + ((-⌊(a.2.getD i.val 0 + (m9vec a.1 b.2).getD i.val 0 : ℚ)⌋ : ℤ) : ℝ)
  have hL : ((sgMulPair a b).2.getD i.val 0 : ℚ)
      = Int.fract (a.2.getD i.val 0 + (m9vec a.1 b.2).getD i.val 0) := by
    show ((List.zipWith (· + ·) a.2 (m9vec a.1 b.2)).map Int.fract).getD i.val 0
      = Int.fract (a.2.getD i.val 0 + (m9vec a.1 b.2).getD i.val 0)
    exact getD_map_fract_zipWith ha2len (m9vec_length a.1 b.2) i
  have hY : (((imatOfList a.1).map (Int.cast : ℤ → ℝ)).mulVec
        (fun j : Fin 3 => ((b.2.getD j.val 0 : ℚ) : ℝ)) i)
      = (((m9vec a.1 b.2).getD i.val 0 : ℚ) : ℝ) := mulVec_cast_getD a.1 b.2 i
  rw [hL, hY, fract_add_neg_floor]
  push_cast
  ring

/-- The cocycle identity for a pair of table entries. -/
theorem sgTau_cocycle_of_mem (k : Fin 230) : ∀ a ∈ sgTable k, ∀ b ∈ sgTable k,
    sgTau k (imatOfList a.1 * imatOfList b.1)
      = sgTau k (imatOfList a.1)
        + ((imatOfList a.1).map (Int.cast : ℤ → ℝ)).mulVec (sgTau k (imatOfList b.1))
        + intVec (fun i => -⌊(a.2.getD i.val 0 + (m9vec a.1 b.2).getD i.val 0 : ℚ)⌋) := by
  intro a ha b hb
  funext i
  exact sgTau_cocycle_of_mem_apply k a ha b hb i

/-! ## The classes as images of table matrices -/

/-- The first components of the arithmetic generators. -/
theorem fst_arithGensQ (j : Fin 73) : (arithGensQ j).map (·.1) = arithGens j := by
  simp only [arithGensQ]
  induction arithGens j with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The first component of the identity pair. -/
theorem fst_sgOne :
    ([sgOne] : List (List ℤ × List ℚ)).map (·.1) = [[1, 0, 0, 0, 1, 0, 0, 0, 1]] := by
  simp [sgOne]

/-- `arithRep j` as the image of the matrix closure of the generators. -/
theorem arithRep_eq_mem (j : Fin 73) :
    arithRep j = {A : IMat |
      ∃ l, l ∈ mClose (arithGens j) 48 [[1, 0, 0, 0, 1, 0, 0, 0, 1]] ∧ A = imatOfList l} := by
  rw [arithRep_eq]
  ext A
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ mClose ((arithGensQ j).map (·.1)) 48 ([sgOne].map (·.1)) :=
      (sgClose_map_fst 48 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [fst_arithGensQ j, fst_sgOne] at hp'
    exact ⟨p.1, hp', rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have hl' : l ∈ mClose ((arithGensQ j).map (·.1)) 48 ([sgOne].map (·.1)) := by
      rw [fst_arithGensQ j, fst_sgOne]
      exact hl
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp ((sgClose_map_fst 48 l).mpr hl')
    exact ⟨p, hp, by rw [hp1]⟩

/-- The matrices of the `ℚ`-side table of representative `k`, as an image. -/
theorem sgTable_eq_mem (k : Fin 230) :
    {A : IMat | ∃ p ∈ sgTable k, A = imatOfList p.1}
      = {A : IMat |
          ∃ l, l ∈ mClose (arithGens (sgArith k)) 48 [[1, 0, 0, 0, 1, 0, 0, 0, 1]] ∧
            A = imatOfList l} := by
  ext A
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ mClose ((gensQ k).map (·.1)) 48 ([sgOne].map (·.1)) :=
      (sgClose_map_fst 48 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [fst_gensQ k, fst_sgOne] at hp'
    exact ⟨p.1, hp', rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have hl' : l ∈ mClose ((gensQ k).map (·.1)) 48 ([sgOne].map (·.1)) := by
      rw [fst_gensQ k, fst_sgOne]
      exact hl
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp ((sgClose_map_fst 48 l).mpr hl')
    exact ⟨p, hp, by rw [hp1]⟩

/-- The arithmetic class of `k` is the image of its table under `imatOfList`. -/
theorem arithRep_eq_image (k : Fin 230) :
    arithRep (sgArith k) = {A : IMat | ∃ p ∈ sgTable k, A = imatOfList p.1} := by
  rw [arithRep_eq_mem, sgTable_eq_mem]

/-! ## The four sanity claims -/

/-- Every arithmetic representative is an integral point group. -/
theorem isIntPointGroup_image (k : Fin 230) :
    IsIntPointGroup {A : IMat | ∃ p ∈ sgTable k, A = imatOfList p.1} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- finite
    refine Set.Finite.subset
      (Finset.finite_toSet ((sgTable k).toFinset.image fun p => imatOfList p.1)) ?_
    rintro A ⟨p, hp, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_image, List.mem_toFinset]
    exact ⟨p, hp, rfl⟩
  · -- contains the identity
    exact ⟨sgOne, sgOne_mem_sgTable k, imatOfList_one.symm⟩
  · -- closed under multiplication
    rintro A ⟨a, ha, rfl⟩ B ⟨b, hb, rfl⟩
    refine ⟨sgMulPair a b, sgTable_mul k a ha b hb, ?_⟩
    rw [show (sgMulPair a b).1 = m9mul a.1 b.1 from rfl, imatOfList_mul]
  · -- determinants are units
    rintro A ⟨a, ha, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (sgTable_eq_S₀ k a).mp ha
    rw [show (toPair (sgDen k) t).1 = t.1 from rfl, det9_spec]
    rcases TZdet k t ht with h | h
    · rw [h]; exact isUnit_one
    · rw [h]; exact isUnit_one.neg

/-- `sgArith` is onto. -/
theorem sgArith_surjective : Function.Surjective sgArith := by
  have hcard : (Finset.univ.image sgArith : Finset (Fin 73)).card = 73 := by decide
  have huniv : (Finset.univ.image sgArith : Finset (Fin 73)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
  intro j
  have hj : j ∈ (Finset.univ.image sgArith : Finset (Fin 73)) := by
    rw [huniv]
    exact Finset.mem_univ j
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hj
  exact ⟨k, hk⟩

/-- `sgAffClass` is onto. -/
theorem sgAffClass_surjective : Function.Surjective sgAffClass := by
  have hcard : (Finset.univ.image sgAffClass : Finset (Fin 219)).card = 219 := by decide
  have huniv : (Finset.univ.image sgAffClass : Finset (Fin 219)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
  intro j
  have hj : j ∈ (Finset.univ.image sgAffClass : Finset (Fin 219)) := by
    rw [huniv]
    exact Finset.mem_univ j
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hj
  exact ⟨k, hk⟩

/-- An accumulator is contained in the closure it generates. -/
theorem acc_subset_mClose (gensM : List (List ℤ)) :
    ∀ (j : ℕ) (acc : List (List ℤ)), ∀ x ∈ acc, x ∈ mClose gensM j acc := by
  intro j
  induction j with
  | zero => intro acc x hx; exact hx
  | succ j ih =>
      intro acc x hx
      have h1 : x ∈ mF gensM acc := by
        rw [mF, List.mem_dedup, List.mem_append]
        exact Or.inl hx
      exact ih (mF gensM acc) x h1

/-- Generators occur in the matrix closure. -/
theorem gens_mem_mClose {gensM : List (List ℤ)} {g : List ℤ} (hg : g ∈ gensM)
    (h9 : g.length = 9) (k : ℕ) :
    g ∈ mClose gensM (k + 1) [[1, 0, 0, 0, 1, 0, 0, 0, 1]] := by
  have h1 : g ∈ mF gensM [[1, 0, 0, 0, 1, 0, 0, 0, 1]] := by
    rw [mF, List.mem_dedup, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨[1, 0, 0, 0, 1, 0, 0, 0, 1], List.mem_singleton_self _, ?_⟩
    rw [List.mem_map]
    refine ⟨g, hg, ?_⟩
    have hone : imatOfList (m9mul [1, 0, 0, 0, 1, 0, 0, 0, 1] g) = imatOfList g := by
      rw [imatOfList_mul, imatOfList_one, one_mul]
    exact imatOfList_inj (length_m9mul _ _) h9 hone
  have h2 := acc_subset_mClose gensM k (mF gensM [[1, 0, 0, 0, 1, 0, 0, 0, 1]]) g h1
  rwa [show mClose gensM k (mF gensM [[1, 0, 0, 0, 1, 0, 0, 0, 1]])
      = mClose gensM (k + 1) [[1, 0, 0, 0, 1, 0, 0, 0, 1]] from rfl] at h2

/-- The flat matrices of the arithmetic generators have nine entries. -/
theorem arithGens_shape (j : Fin 73) : ∀ g ∈ arithGens j, g.length = 9 := by
  intro g hg
  simp only [arithGens, List.mem_map] at hg
  obtain ⟨c, -, hceq⟩ := hg
  rw [← hceq]
  rfl

/-- A list of ones has product one. -/
theorem list_prod_eq_one {l : List ℤ} (h : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.prod_cons, h a (by simp), ih (fun x hx => h x (by simp [hx])), one_mul]

/-- The determinant-one condition, as a computable predicate on the generators. -/
theorem arithRep_det_one_iff (k : Fin 230) :
    (∀ A ∈ arithRep (sgArith k), A.det = 1) ↔
      (arithGens (sgArith k)).all (fun g => decide (det9 g = 1)) = true := by
  rw [arithRep_eq_mem (sgArith k)]
  constructor
  · intro h
    rw [List.all_eq_true]
    intro g hg
    rw [decide_eq_true_eq]
    have hA : imatOfList g ∈ {A : IMat |
        ∃ l, l ∈ mClose (arithGens (sgArith k)) 48 [[1, 0, 0, 0, 1, 0, 0, 0, 1]] ∧
          A = imatOfList l} :=
      ⟨g, gens_mem_mClose hg (arithGens_shape (sgArith k) g hg) 47, rfl⟩
    have := h _ hA
    rw [det9_spec] at this
    exact this
  · intro h
    rw [List.all_eq_true] at h
    have hgen : ∀ g ∈ arithGens (sgArith k), det9 g = 1 :=
      fun g hg => of_decide_eq_true (h g hg)
    rintro A ⟨l, hl, rfl⟩
    obtain ⟨w, hw, hwfold⟩ :=
      isWordProd_of_mem_mClose (gensM := arithGens (sgArith k))
        (accM := [[1, 0, 0, 0, 1, 0, 0, 0, 1]])
        (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact ⟨[], by simp, rfl⟩) 48 l hl
    rw [det9_spec, ← hwfold,
      det9_foldl_m9mul w (fun g hg => arithGens_shape (sgArith k) g (hw g hg))]
    refine list_prod_eq_one (fun x hx => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact hgen g (hw g hg)

/-- **Sanity of the generated tables**: the arithmetic representatives are point groups, the
representative translations are cocycles, every affine class occurs, and exactly 65
representatives have all linear parts of determinant `1`. -/
theorem sg_data_facts :
    (∀ j : Fin 73, IsIntPointGroup (arithRep j)) ∧
    (∀ k : Fin 230, IsIntCocycle (arithRep (sgArith k)) (sgTau k)) ∧
    Function.Surjective sgAffClass ∧
    Set.ncard {k : Fin 230 | ∀ A ∈ arithRep (sgArith k), A.det = 1} = 65 := by
  refine ⟨?_, ?_, sgAffClass_surjective, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := sgArith_surjective j
    rw [← hk, arithRep_eq_image k]
    exact isIntPointGroup_image k
  · intro k A hA B hB
    rw [arithRep_eq_image k] at hA hB
    obtain ⟨a, ha, rfl⟩ := hA
    obtain ⟨b, hb, rfl⟩ := hB
    exact ⟨_, sgTau_cocycle_of_mem k a ha b hb⟩
  · have hset : {k : Fin 230 | ∀ A ∈ arithRep (sgArith k), A.det = 1}
        = {k : Fin 230 |
            (arithGens (sgArith k)).all (fun g => decide (det9 g = 1)) = true} := by
      ext k
      exact arithRep_det_one_iff k
    rw [hset]
    have hfin : {k : Fin 230 |
          (arithGens (sgArith k)).all (fun g => decide (det9 g = 1)) = true}
        = (↑(Finset.univ.filter fun k : Fin 230 =>
            (arithGens (sgArith k)).all (fun g => decide (det9 g = 1))) : Set (Fin 230)) := by
      ext k
      simp [Finset.mem_filter]
    rw [hfin, Set.ncard_coe_finset]
    decide

end Work.SG
