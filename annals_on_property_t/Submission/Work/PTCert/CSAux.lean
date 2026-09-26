import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.modelSound
import Submission.Work.PTCert.letterAction
import Submission.Work.PTCert.permCheckKSound

/-!
# PTCert — helpers for the class-sum semantics (`ClassSem`)

Generic soundness lemmas for the kernel Bool checkers (`allL`, `allR`, `allIdx`, `eqL`), the
group-theoretic facts about `lprod` needed to turn `clsWitOK` into a conjugacy statement, and the
base-128 packing arithmetic.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C
open Submission.FreeGroupAut

/-! ## Unfolding the Bool checkers -/

theorem allL_iff_CSAux (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    rw [show allL (a :: t) p = (p a && allL t p) from rfl, Bool.and_eq_true, ih]
    simp

theorem allR_iff_CSAux (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n + 1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact h2 k h
      · subst h; exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem allIdx_iff_CSAux (l : List ℕ) (p : ℕ → ℕ → Bool) (i0 : ℕ) :
    allIdx l p i0 = true ↔ ∀ j (hj : j < l.length), p (i0 + j) l[j] = true := by
  induction l generalizing i0 with
  | nil => simp [allIdx]
  | cons a t ih =>
    rw [show allIdx (a :: t) p i0 = (p i0 a && allIdx t p (i0 + 1)) from rfl,
      Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      cases j with
      | zero => simpa using h1
      | succ j =>
        have hjt : j < t.length := by simpa using hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2 j hjt
    · intro h
      refine ⟨h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem eqL_iff (l m : List ℕ) : eqL l m = true ↔ l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => simp [eqL]
    | cons b s => simp [eqL]
  | cons a t ih =>
    cases m with
    | nil => simp [eqL]
    | cons b s =>
      rw [show eqL (a :: t) (b :: s) = (Nat.beq a b && eqL t s) from rfl,
        Bool.and_eq_true, Nat.beq_eq, ih]
      constructor
      · rintro ⟨h1, h2⟩; rw [h1, h2]
      · intro h; cases h; exact ⟨rfl, rfl⟩

theorem allL_append (l m : List ℕ) (p : ℕ → Bool) :
    allL (l ++ m) p = (allL l p && allL m p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.cons_append,
      show allL (a :: (t ++ m)) p = (p a && allL (t ++ m) p) from rfl, ih,
      show allL (a :: t) p = (p a && allL t p) from rfl]
    simp [Bool.and_assoc]

/-- `allL` on `List.range' 0 N` is a universal statement over `[0, N)`. -/
theorem allL_range' (N : ℕ) (p : ℕ → Bool) (h : allL (List.range' 0 N) p = true) :
    ∀ g < N, p g = true := by
  intro g hg
  exact (allL_iff_CSAux _ p).mp h g (List.mem_range'.mpr ⟨g, hg, by ring⟩)

/-- `getD` of an append, in terms of the two parts. -/
theorem getD_append' (l m : List ℕ) (d n : ℕ) :
    (l ++ m).getD n d = if n < l.length then l.getD n d else m.getD (n - l.length) d := by
  simp only [List.getD, List.getElem?_append]; split_ifs <;> rfl

/-- A member of a flattened list of lists lies in one of the components. -/
theorem mem_flatten_getD {L : List (List ℕ)} {k : ℕ} (h : k ∈ L.flatten) :
    ∃ i, i < L.length ∧ k ∈ L.getD i [] := by
  obtain ⟨l, hl, hkl⟩ := List.mem_flatten.mp h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hl
  exact ⟨n, hn, by rwa [List.getD_eq_getElem _ _ hn]⟩

/-! ## Letters -/

theorem NB1_five : NB1 5 = 81 := by norm_num [NB1]

theorem invLk_eq_invL (k : ℕ) : invLk k = invL k := by
  rw [invLk, invL]
  by_cases h : k = 0
  · rw [if_pos h, show (k.beq 0 : Bool) = true from by rw [Nat.beq_eq]; exact h]
    rfl
  · rw [if_neg h, show (k.beq 0 : Bool) = false from by
        rw [Bool.eq_false_iff]; intro hc; exact h (Nat.beq_eq.mp hc)]
    rfl

theorem b1_inv_81 (k : ℕ) (hk : k < 81) : (b1 5 k)⁻¹ = b1 5 (invL k) :=
  b1_inv 5 k (by rw [NB1_five]; exact hk)

theorem invL_lt_81 (k : ℕ) (hk : k < 81) : invL k < 81 :=
  invL_lt 5 k (by rw [NB1_five]; exact hk)

/-! ## Products of letters -/

theorem map_prod_conj {G : Type} [Group G] (σ : G) (l : List G) :
    σ * l.prod * σ⁻¹ = (l.map (fun x => σ * x * σ⁻¹)).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons,
      show σ * (a * t.prod) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * t.prod * σ⁻¹) by group, ih]

theorem prod_reverse_inv {G : Type} [Group G] (l : List G) :
    (l.reverse.prod)⁻¹ = (l.map (fun x => x⁻¹)).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      List.map_cons, List.prod_cons, mul_inv_rev, ih]

/-- Conjugating a product of letters by the element of a valid code acts letterwise by `actL`. -/
theorem lprod_conj (hCF : CodeFacts) (c : ℕ) (hc : validPC 5 (c / 32) = true)
    (w : List ℕ) (hw : ∀ k ∈ w, k < 81) :
    codeElt c * lprod 5 w * (codeElt c)⁻¹
      = lprod 5 (w.map (fun k => actL 5 (c / 32) (c % 32) k)) := by
  have hconj : ∀ k ∈ w, codeElt c * b1 5 k * (codeElt c)⁻¹
      = b1 5 (actL 5 (c / 32) (c % 32) k) := fun k hk => ((hCF.1 c hc).2 k (hw k hk)).2
  rw [show lprod 5 w = (w.map (b1 5)).prod from rfl,
      show lprod 5 (w.map (fun k => actL 5 (c / 32) (c % 32) k))
        = ((w.map (fun k => actL 5 (c / 32) (c % 32) k)).map (b1 5)).prod from rfl,
      map_prod_conj, List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left (fun k hk => hconj k hk))

/-- The letterwise inverse of a product of letters. -/
theorem lprod_inv (w : List ℕ) (hw : ∀ k ∈ w, k < 81) :
    lprod 5 (w.reverse.map invL) = (lprod 5 w)⁻¹ := by
  have hl : lprod 5 (w.reverse.map invL)
      = ((w.map (fun k => (b1 5 k)⁻¹)).reverse).prod := by
    rw [show lprod 5 (w.reverse.map invL) = ((w.reverse.map invL).map (b1 5)).prod from rfl,
      List.map_map, List.map_reverse]
    exact congrArg (fun l => l.reverse.prod)
      (List.map_congr_left (fun k hk => (b1_inv_81 k (hw k hk)).symm))
  rw [hl]
  have h := prod_reverse_inv (w.map (fun k => (b1 5 k)⁻¹))
  have hmap : (w.map (fun k => (b1 5 k)⁻¹)).map (fun x => x⁻¹) = w.map (b1 5) := by
    rw [List.map_map]; exact List.map_congr_left (fun k hk => inv_inv _)
  rw [hmap, show (w.map (b1 5)).prod = lprod 5 w from rfl] at h
  rw [← h, inv_inv]

/-! ## Base-128 packing -/

theorem unpack4_pack4_abcd (a b c d : ℕ) (ha : a < 128) (hb : b < 128) (hc : c < 128)
    (hd : d < 128) : unpack4 (pack4 [a, b, c, d]) = [a, b, c, d] := by
  have h128 : 0 < (128 : ℕ) := by norm_num
  set Y := b + 128 * (c + 128 * d) with hY
  set Z := c + 128 * d with hZ
  have hX : pack4 [a, b, c, d] = a + 128 * Y := by
    simp only [pack4, List.foldr_cons, List.foldr_nil, hY, hZ]; ring
  have hmod1 : (a + 128 * Y) % 128 = a := by
    rw [Nat.add_comm a (128 * Y), Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ha]
  have hdiv1 : (a + 128 * Y) / 128 = Y := by
    rw [Nat.add_comm a (128 * Y), Nat.mul_add_div h128, Nat.div_eq_of_lt ha, Nat.add_zero]
  have hmodY : Y % 128 = b := by
    rw [hY, Nat.add_comm b (128 * Z), Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hb]
  have hdivY : Y / 128 = Z := by
    rw [hY, Nat.add_comm b (128 * Z), Nat.mul_add_div h128, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmodZ : Z % 128 = c := by
    rw [hZ, Nat.add_comm c (128 * d), Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hc]
  have hdivZ : Z / 128 = d := by
    rw [hZ, Nat.add_comm c (128 * d), Nat.mul_add_div h128, Nat.div_eq_of_lt hc, Nat.add_zero]
  have e3 : (a + 128 * Y) / 16384 = Z := by
    rw [show (16384 : ℕ) = 128 * 128 by norm_num, ← Nat.div_div_eq_div_mul, hdiv1, hdivY]
  have e4 : (a + 128 * Y) / 2097152 = d := by
    rw [show (2097152 : ℕ) = 128 * 128 * 128 by norm_num, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, hdiv1, hdivY, hdivZ]
  rw [hX]; simp only [unpack4]
  rw [hmod1, hdiv1, hmodY, e3, e4, hmodZ, Nat.mod_eq_of_lt hd]

theorem unpack4_pack4 (w : List ℕ) (hw : w.length = 4) (h : ∀ k ∈ w, k < 128) :
    unpack4 (pack4 w) = w := by
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact unpack4_pack4_abcd a b c d (h a (Or.inl rfl)) (h b (Or.inr (Or.inl rfl)))
    (h c (Or.inr (Or.inr (Or.inl rfl)))) (h d (Or.inr (Or.inr (Or.inr rfl))))

/-! ## The canonical words -/

theorem canonW_len (c : ℕ) : (canonW c).length = 4 := rfl

theorem canonW_lt (c : ℕ) (hc : c < 7229) : ∀ k ∈ canonW c, k < 81 := by
  intro k hk
  have hcanon : allR 7229
      (fun c => allL (unpack4 (kG canonT c)) (fun k => Nat.blt k 81)) = true := C.canon_ok
  have h1 := (allR_iff_CSAux 7229 _).mp hcanon c hc
  have h2 := (allL_iff_CSAux _ _).mp h1 k (by simpa [canonW] using hk)
  simpa [Nat.blt_eq] using h2

/-! ## Bounds on the codes of `B₂` -/

theorem unpack4_lt (v : ℕ) : ∀ k ∈ unpack4 v, k < 128 := by
  intro k hk
  simp only [unpack4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by norm_num)

end Work.PTCert

end
