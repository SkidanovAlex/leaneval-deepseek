/-
# The `z`-run criterion for `K = (rootHom t p).range`

This file proves

`x ∈ (rootHom t p).range ↔ Good t p (FreeGroup.toWord x)`,

where `Good t p L` (defined in `rootHomConjSetup.lean`) says that every maximal run of
`z = Sum.inr ()`-letters of the word `L` has exponent divisible by `p`.

The two directions are proved separately:

* `Good t p (toWord x) → x ∈ K` is an induction on the word (`goodAux_mem_range`);
* `x ∈ K → Good t p (toWord x)` shows that `{x | Good t p (toWord x)}` is a subgroup containing
  the generators `z ^ p` and `of (Sum.inl a)`; this needs that `Good` is closed under
  concatenation, under inversion and under free reduction (the latter via the one-step reduction
  relation `FreeGroup.Red.Step`).
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.rootHomConjSetup

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.CohenLyndon

variable {α : Type u} [DecidableEq α]

/-- The exponent of the trailing (possibly incomplete) run of `z`-letters of the word
`virtual run n ++ L`. -/
def pend (t : α) : ℤ → List (RootIdx α t × Bool) → ℤ
  | n, [] => n
  | n, (l, b) :: tl => if l = zLetter t then pend t (n + (if b then 1 else -1)) tl else pend t 0 tl

/-- `goodAuxT t p n L`: the word `L`, preceded by a virtual run of `z`-letters of exponent `n`,
has all its maximal runs of `z`-letters of exponent divisible by `p` **except possibly the
last one** (which may be continued). -/
def goodAuxT (t : α) (p : ℤ) : ℤ → List (RootIdx α t × Bool) → Prop
  | n, [] => True
  | n, (l, b) :: tl =>
      if l = zLetter t then goodAuxT t p (n + (if b then 1 else -1)) tl
      else (p ∣ n) ∧ goodAuxT t p 0 tl

@[simp] theorem pend_nil (t : α) (n : ℤ) : pend t n ([] : List (RootIdx α t × Bool)) = n := rfl

theorem pend_cons_z (t : α) (n : ℤ) (b : Bool) (tl : List (RootIdx α t × Bool)) :
    pend t n ((zLetter t, b) :: tl) = pend t (n + (if b then 1 else -1)) tl := by
  rw [pend]; simp

theorem pend_cons_other (t : α) (n : ℤ) {l : RootIdx α t} (b : Bool)
    (tl : List (RootIdx α t × Bool)) (h : l ≠ zLetter t) :
    pend t n ((l, b) :: tl) = pend t 0 tl := by
  rw [pend]; simp [h]

@[simp] theorem goodAuxT_nil (t : α) (p : ℤ) (n : ℤ) :
    goodAuxT t p n ([] : List (RootIdx α t × Bool)) := trivial

theorem goodAuxT_cons_z (t : α) (p : ℤ) (n : ℤ) (b : Bool) (tl : List (RootIdx α t × Bool)) :
    goodAuxT t p n ((zLetter t, b) :: tl) ↔ goodAuxT t p (n + (if b then 1 else -1)) tl := by
  rw [goodAuxT]; simp

theorem goodAuxT_cons_other (t : α) (p : ℤ) (n : ℤ) {l : RootIdx α t} (b : Bool)
    (tl : List (RootIdx α t × Bool)) (h : l ≠ zLetter t) :
    goodAuxT t p n ((l, b) :: tl) ↔ p ∣ n ∧ goodAuxT t p 0 tl := by
  rw [goodAuxT]; simp [h]

/-- `goodAux` is `goodAuxT` together with divisibility of the trailing run. -/
theorem goodAux_iff (t : α) (p : ℤ) (n : ℤ) (L : List (RootIdx α t × Bool)) :
    goodAux t p n L ↔ goodAuxT t p n L ∧ p ∣ pend t n L := by
  induction L generalizing n with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨l, b⟩ := hd
    by_cases h : l = zLetter t
    · subst h
      show goodAux t p (n + (if b then 1 else -1)) tl ↔ _
      rw [ih, goodAuxT_cons_z, pend_cons_z]
    · rw [goodAux, if_neg h, goodAuxT_cons_other t p n b tl h, pend_cons_other t n b tl h, ih]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩

theorem pend_append (t : α) (L M : List (RootIdx α t × Bool)) (n : ℤ) :
    pend t n (L ++ M) = pend t (pend t n L) M := by
  induction L generalizing n with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨l, b⟩ := hd
    by_cases h : l = zLetter t
    · subst h
      rw [List.cons_append, pend_cons_z, pend_cons_z, ih]
    · rw [List.cons_append, pend_cons_other t n b tl h,
          pend_cons_other t n b (tl ++ M) h, ih]

/-- The runs of `L ++ M` (with a virtual run `n`) before the trailing one split as the runs of
`L` (before its trailing one) and the runs of `M` (with virtual run `pend t n L`) before its
trailing one. -/
theorem goodAuxT_append (t : α) (p : ℤ) (n : ℤ) (L M : List (RootIdx α t × Bool)) :
    goodAuxT t p n (L ++ M) ↔ goodAuxT t p n L ∧ goodAuxT t p (pend t n L) M := by
  induction L generalizing n with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨l, b⟩ := hd
    by_cases h : l = zLetter t
    · subst h
      rw [List.cons_append, goodAuxT_cons_z, goodAuxT_cons_z, pend_cons_z, ih]
    · rw [List.cons_append, goodAuxT_cons_other t p n b tl h,
        goodAuxT_cons_other t p n b (tl ++ M) h, pend_cons_other t n b tl h, ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.1⟩, h2.2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩

/-- `goodAux` splits over a concatenation: the runs of `L` (all but the trailing one) and the
runs of `M` with the incoming run `pend t n L`. -/
theorem goodAux_append (t : α) (p : ℤ) (n : ℤ) (L M : List (RootIdx α t × Bool)) :
    goodAux t p n (L ++ M) ↔ goodAuxT t p n L ∧ goodAux t p (pend t n L) M := by
  rw [goodAux_iff, goodAuxT_append, pend_append, goodAux_iff]
  tauto

/-- A shift of the incoming run preserves `goodAuxT` when the shift is a multiple of `p`. -/
theorem goodAuxT_add (t : α) (p : ℤ) (n : ℤ) (hm : p ∣ n) :
    ∀ (m : ℤ) (L : List (RootIdx α t × Bool)), goodAuxT t p m L → goodAuxT t p (m + n) L := by
  intro m L
  induction L generalizing m with
  | nil => intro _; trivial
  | cons hd tl ih =>
    intro h
    obtain ⟨l, b⟩ := hd
    by_cases hz : l = zLetter t
    · subst hz
      rw [goodAuxT_cons_z] at h ⊢
      have he : m + n + (if b then 1 else -1) = (m + (if b then 1 else -1)) + n := by ring
      rw [he]
      exact ih (m + (if b then 1 else -1)) h
    · rw [goodAuxT_cons_other t p m b tl hz] at h
      rw [goodAuxT_cons_other t p (m + n) b tl hz]
      exact ⟨by rw [add_comm]; exact dvd_add hm h.1, h.2⟩

/-- The trailing run of the virtual extension `n ++ L` differs from the trailing run of `L`
either by `n` or not at all. -/
theorem pend_add (t : α) (L : List (RootIdx α t × Bool)) (n m : ℤ) :
    pend t (n + m) L = pend t m L ∨ pend t (n + m) L = n + pend t m L := by
  induction L generalizing m with
  | nil => exact Or.inr (by simp)
  | cons hd tl ih =>
    obtain ⟨l, b⟩ := hd
    by_cases h : l = zLetter t
    · subst h
      rw [pend_cons_z, pend_cons_z]
      have he : n + m + (if b then 1 else -1) = n + (m + (if b then 1 else -1)) := by ring
      rw [he]
      exact ih (m + (if b then 1 else -1))
    · rw [pend_cons_other t (n + m) b tl h, pend_cons_other t m b tl h]
      exact Or.inl rfl

/-- Shifting the incoming run by a multiple of `p` does not change `goodAux`. -/
theorem goodAux_shift (t : α) (p : ℤ) {n : ℤ} (hn : p ∣ n) (L : List (RootIdx α t × Bool)) :
    goodAux t p 0 L → goodAux t p n L := by
  intro h
  rw [goodAux_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · have := goodAuxT_add t p n hn 0 L h.1
    simpa using this
  · rcases pend_add t L n 0 with h' | h'
    · have h2 : pend t n L = pend t 0 L := by simpa using h'
      rw [h2]; exact h.2
    · have h2 : pend t n L = n + pend t 0 L := by simpa using h'
      rw [h2]
      exact dvd_add hn h.2

/-- `Good t p (L ++ M)` from `Good t p L` and `Good t p M`. -/
theorem good_append (t : α) (p : ℤ) {L M : List (RootIdx α t × Bool)}
    (hL : Good t p L) (hM : Good t p M) : Good t p (L ++ M) := by
  rw [Good] at hL hM ⊢
  rw [goodAux_append]
  refine ⟨(goodAux_iff t p 0 L).mp hL |>.1, goodAux_shift t p ?_ M hM⟩
  exact (goodAux_iff t p 0 L).mp hL |>.2

/-- `goodAuxT` of a single letter. -/
theorem goodAuxT_singleton (t : α) (p : ℤ) (m : ℤ) (l : RootIdx α t) (b : Bool) :
    goodAuxT t p m [(l, b)] ↔ (l ≠ zLetter t → p ∣ m) := by
  by_cases h : l = zLetter t
  · subst h
    rw [goodAuxT_cons_z]
    simp
  · rw [goodAuxT_cons_other t p m b [] h]
    simp [h]

/-- `pend` of a single letter. -/
theorem pend_singleton (t : α) (m : ℤ) (l : RootIdx α t) (b : Bool) :
    pend t m [(l, b)] = if l = zLetter t then m + (if b then 1 else -1) else 0 := by
  by_cases h : l = zLetter t
  · subst h
    rw [pend_cons_z]
    simp
  · rw [pend_cons_other t m b [] h]
    simp [h]

/-- `goodAux` is preserved by deleting an adjacent inverse pair. -/
theorem goodAux_del (t : α) (p : ℤ) (n : ℤ) (L₁ L₂ : List (RootIdx α t × Bool))
    (x : RootIdx α t) (b : Bool) :
    goodAux t p n (L₁ ++ (x, b) :: (x, !b) :: L₂) → goodAux t p n (L₁ ++ L₂) := by
  induction L₁ generalizing n with
  | nil =>
    intro h
    have h' : goodAux t p n ([(x, b)] ++ ([(x, !b)] ++ L₂)) := by simpa using h
    rw [goodAux_append] at h'
    obtain ⟨h1, h2⟩ := h'
    rw [goodAuxT_singleton] at h1
    rw [pend_singleton] at h2
    have h2' : goodAux t p (if x = zLetter t then n + (if b then 1 else -1) else 0)
        ([(x, !b)] ++ L₂) := h2
    rw [goodAux_append] at h2'
    obtain ⟨h3, h4⟩ := h2'
    rw [goodAuxT_singleton] at h3
    rw [pend_singleton] at h4
    by_cases hx : x = zLetter t
    · subst hx
      have hab : (if zLetter t = zLetter t then n + (if b then 1 else -1) else 0) =
          n + (if b then 1 else -1) := if_pos rfl
      rw [hab] at h4
      have heq : n + (if b then 1 else -1) + (if !b then 1 else -1) = n := by
        cases b <;> simp
      rw [heq] at h4
      simpa using h4
    · have hin : (if x = zLetter t then n + (if b then 1 else -1) else 0) = 0 := if_neg hx
      rw [hin] at h4
      have hab : (if x = zLetter t then 0 + (if !b then 1 else -1) else 0) = 0 := if_neg hx
      rw [hab] at h4
      exact goodAux_shift t p (h1 hx) L₂ h4
  | cons hd tl ih =>
    obtain ⟨l, bb⟩ := hd
    intro h
    have h' : goodAux t p n ([(l, bb)] ++ (tl ++ (x, b) :: (x, !b) :: L₂)) := by simpa using h
    rw [goodAux_append] at h'
    obtain ⟨h1, h2⟩ := h'
    have goal : goodAux t p n ([(l, bb)] ++ (tl ++ L₂)) := by
      rw [goodAux_append]
      exact ⟨h1, ih _ h2⟩
    simpa using goal

/-- `Good` is preserved by one step of free reduction. -/
theorem red_step_good (t : α) (p : ℤ) {L M : List (RootIdx α t × Bool)}
    (h : FreeGroup.Red.Step L M) (hL : Good t p L) : Good t p M := by
  cases h with
  | not => exact goodAux_del t p 0 _ _ _ _ hL

/-- `Good` is preserved by free reduction. -/
theorem good_reduce (t : α) (p : ℤ) {L : List (RootIdx α t × Bool)} (h : Good t p L) :
    Good t p (FreeGroup.reduce L) := by
  generalize hM : FreeGroup.reduce L = M
  have hred : FreeGroup.Red L M := hM ▸ FreeGroup.reduce.red
  clear hM
  induction hred with
  | refl => exact h
  | tail _ hstep ih => exact red_step_good t p hstep ih

/-! ## The criterion -/

/-- `mk` of a cons. -/
theorem mk_cons (t : α) (l : RootIdx α t) (b : Bool) (tl : List (RootIdx α t × Bool)) :
    FreeGroup.mk ((l, b) :: tl) =
      (if b then FreeGroup.of l else (FreeGroup.of l)⁻¹) * FreeGroup.mk tl := by
  have h1 : ((l, b) :: tl : List _) = [(l, b)] ++ tl := rfl
  rw [h1, ← FreeGroup.mul_mk]
  congr 1
  have hof : FreeGroup.mk [(l, true)] = FreeGroup.of l := by
    apply FreeGroup.toWord_injective
    rw [FreeGroup.toWord_mk, FreeGroup.toWord_of]
    rfl
  have hinv : FreeGroup.invRev [(l, true)] = [(l, false)] := rfl
  by_cases hb : b
  · subst hb; rw [if_pos rfl]; exact hof
  · have hbf : b = false := by cases b <;> simp_all
    rw [hbf, if_neg (by simp), ← hof, FreeGroup.inv_mk, hinv]

/-- A word consisting of `m` copies of a `z`-letter. -/
theorem goodAux_replicate_z (t : α) (p : ℤ) (n : ℤ) (m : ℕ) (b : Bool) :
    goodAux t p n (List.replicate m (zLetter t, b)) ↔
      p ∣ n + (if b then (m : ℤ) else -(m : ℤ)) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, goodAux_cons_z, ih]
    congr 1
    cases b <;> simp <;> ring

/-- A word consisting of `m` copies of a non-`z`-letter. -/
theorem goodAux_replicate_other (t : α) (p : ℤ) {l : RootIdx α t} (h : l ≠ zLetter t)
    (b : Bool) (n : ℤ) (m : ℕ) :
    goodAux t p n (List.replicate m (l, b)) ↔ p ∣ n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, goodAux, if_neg h, ih]
    exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, dvd_zero p⟩⟩

/-- The reverse-flip of a run of equal letters. -/
theorem invRev_replicate (t : α) (l : RootIdx α t) (b : Bool) (m : ℕ) :
    FreeGroup.invRev (List.replicate m (l, b)) = List.replicate m (l, !b) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, FreeGroup.invRev_cons, ih,
      show FreeGroup.invRev [(l, b)] = [(l, !b)] from rfl,
      List.replicate_succ']

/-- The reduced word of `of l ^ m` for `m : ℕ`. -/
theorem toWord_zpow_nat (t : α) (l : RootIdx α t) (m : ℕ) :
    FreeGroup.toWord (FreeGroup.of l ^ ((m : ℕ) : ℤ)) =
      List.replicate m (l, true) := by
  rw [zpow_natCast, FreeGroup.toWord_pow, FreeGroup.toWord_of,
    List.flatten_replicate_singleton, FreeGroup.reduce_replicate]

/-- The reduced word of `of l ^ (-m)` for `m : ℕ`. -/
theorem toWord_zpow_neg_nat (t : α) (l : RootIdx α t) (m : ℕ) :
    FreeGroup.toWord (FreeGroup.of l ^ (-((m : ℕ) : ℤ))) =
      List.replicate m (l, false) := by
  rw [zpow_neg, zpow_natCast, FreeGroup.toWord_inv, FreeGroup.toWord_pow, FreeGroup.toWord_of,
    List.flatten_replicate_singleton, FreeGroup.reduce_replicate, invRev_replicate]
  rfl

/-- `of l ^ k` has a `Good` reduced word, provided that `p ∣ k` when `l = z`. -/
theorem good_toWord_zpow (t : α) (p : ℤ) (l : RootIdx α t) (k : ℤ)
    (h : l = zLetter t → p ∣ k) : Good t p (FreeGroup.toWord (FreeGroup.of l ^ k)) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · subst hm
    rw [toWord_zpow_nat]
    by_cases hz : l = zLetter t
    · subst hz
      rw [Good, goodAux_replicate_z, zero_add]
      simpa using h rfl
    · rw [Good, goodAux_replicate_other t p hz]
      exact dvd_zero p
  · subst hm
    rw [toWord_zpow_neg_nat]
    by_cases hz : l = zLetter t
    · subst hz
      rw [Good, goodAux_replicate_z, zero_add]
      simpa using h rfl
    · rw [Good, goodAux_replicate_other t p hz]
      exact dvd_zero p

/-! ## The two directions -/

/-- `of z ^ p` lies in `K`. -/
theorem of_z_pow_mem_range (t : α) (p : ℤ) :
    FreeGroup.of (Sum.inr ()) ^ p ∈ (rootHom t p).range := by
  rw [range_rootHom_eq_closure]
  exact Subgroup.subset_closure (Or.inl rfl)

/-- A power of `of z ^ p` lies in `K`. -/
theorem of_z_zpow_mem_range (t : α) (p k : ℤ) :
    FreeGroup.of (Sum.inr ()) ^ (p * k) ∈ (rootHom t p).range := by
  rw [zpow_mul]
  exact Subgroup.zpow_mem _ (of_z_pow_mem_range t p) k

/-- `of z ^ n * mk L ∈ K` whenever the runs of `L` (with incoming run `n`) are divisible. -/
theorem goodAux_mem_range (t : α) (p : ℤ) (L : List (RootIdx α t × Bool)) (n : ℤ)
    (h : goodAux t p n L) :
    FreeGroup.of (Sum.inr ()) ^ n * FreeGroup.mk L ∈ (rootHom t p).range := by
  induction L generalizing n with
  | nil =>
    obtain ⟨k, hk⟩ := h
    rw [hk, ← FreeGroup.one_eq_mk, mul_one]
    exact of_z_zpow_mem_range t p k
  | cons hd tl ih =>
    obtain ⟨l, b⟩ := hd
    by_cases hz : l = zLetter t
    · subst hz
      have h' : goodAux t p (n + (if b then 1 else -1)) tl := by
        rw [goodAux, if_pos rfl] at h
        exact h
      have ih' := ih (n + (if b then 1 else -1)) h'
      rw [mk_cons]
      have hzpow : (if b then FreeGroup.of (zLetter t) else (FreeGroup.of (zLetter t))⁻¹) =
          FreeGroup.of (Sum.inr ()) ^ (if b then (1 : ℤ) else -1) := by
        cases b <;> simp
      rw [hzpow]
      have : FreeGroup.of (Sum.inr ()) ^ n *
          (FreeGroup.of (Sum.inr ()) ^ (if b then (1 : ℤ) else -1) * FreeGroup.mk tl) =
          FreeGroup.of (Sum.inr ()) ^ (n + (if b then 1 else -1)) * FreeGroup.mk tl := by
        group
      rw [this]
      exact ih'
    · have h' : p ∣ n ∧ goodAux t p 0 tl := by
        rw [goodAux, if_neg hz] at h
        exact h
      have hzmem : FreeGroup.of (Sum.inr ()) ^ n ∈ (rootHom t p).range := by
        obtain ⟨k, hk⟩ := h'.1
        rw [hk]
        exact of_z_zpow_mem_range t p k
      have hlmem : FreeGroup.of l ∈ (rootHom t p).range := by
        cases l with
        | inl a =>
          rw [range_rootHom_eq_closure]
          exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
        | inr u => exact absurd rfl hz
      have ihtl := ih 0 h'.2
      rw [mk_cons]
      have hb : (if b then FreeGroup.of l else (FreeGroup.of l)⁻¹) ∈ (rootHom t p).range := by
        cases b
        · exact Subgroup.inv_mem _ hlmem
        · exact hlmem
      have ihtl' : FreeGroup.mk tl ∈ (rootHom t p).range := by simpa using ihtl
      have hprod := Subgroup.mul_mem _ (Subgroup.mul_mem _ hzmem hb) ihtl'
      simpa only [mul_assoc] using hprod

/-- The submonoid of elements whose reduced word is `Good`. -/
def goodSub (t : α) (p : ℤ) : Submonoid (FreeGroup (RootIdx α t)) where
  carrier := {x | Good t p (FreeGroup.toWord x)}
  one_mem' := by
    show Good t p (FreeGroup.toWord (1 : FreeGroup (RootIdx α t)))
    simpa using (good_nil (t := t) (p := p))
  mul_mem' := by
    intro x y hx hy
    show Good t p (FreeGroup.toWord (x * y))
    rw [FreeGroup.toWord_mul]
    exact good_reduce t p (good_append t p hx hy)

/-- The generating set `{z ^ p} ∪ {a : a ≠ t}` of `K`. -/
def genSet (t : α) (p : ℤ) : Set (FreeGroup (RootIdx α t)) :=
  {rootLetter t ^ p} ∪ Set.range (fun a : {a : α // a ≠ t} => FreeGroup.of (Sum.inl a))

theorem inv_mem_genSet_closure (t : α) (p : ℤ) :
    ∀ x ∈ Submonoid.closure (genSet t p ∪ (fun g => g⁻¹) '' genSet t p),
      x⁻¹ ∈ Submonoid.closure (genSet t p ∪ (fun g => g⁻¹) '' genSet t p) := by
  intro x hx
  refine Submonoid.closure_induction ?_ ?_ ?_ hx
  · intro y hy
    refine Submonoid.subset_closure ?_
    rcases hy with h | ⟨h, hh, rfl⟩
    · exact Or.inr ⟨y, h, rfl⟩
    · simpa using Or.inl hh
  · exact Submonoid.one_mem _
  · intro a b _ _ iha ihb
    rw [mul_inv_rev]
    exact Submonoid.mul_mem _ ihb iha

/-- `(rootHom t p).range` lies in the submonoid generated by `genSet ∪ genSet⁻¹`. -/
theorem range_le_submonoid (t : α) (p : ℤ) :
    ((rootHom t p).range : Set (FreeGroup (RootIdx α t))) ⊆
      (Submonoid.closure (genSet t p ∪ (fun g => g⁻¹) '' genSet t p) : Set _) := by
  intro x hx
  rw [show (rootHom t p).range = Subgroup.closure (genSet t p) from range_rootHom_eq_closure t p]
    at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Submonoid.subset_closure (Or.inl hy)
  · exact Submonoid.one_mem _
  · intro a b _ _ iha ihb
    exact Submonoid.mul_mem _ iha ihb
  · intro a _ iha
    exact inv_mem_genSet_closure t p a iha

/-- Membership in `K` implies that the reduced word is `Good`. -/
theorem good_of_mem_range (t : α) (p : ℤ) {x : FreeGroup (RootIdx α t)}
    (hx : x ∈ (rootHom t p).range) : Good t p (FreeGroup.toWord x) := by
  have hgen : (genSet t p ∪ (fun g => g⁻¹) '' genSet t p) ⊆ (goodSub t p : Set _) := by
    rintro g (hg | ⟨h, hh, rfl⟩)
    · rcases hg with rfl | ⟨a, rfl⟩
      · show Good t p (FreeGroup.toWord (rootLetter t ^ p))
        simpa [rootLetter, zLetter] using good_toWord_zpow t p (zLetter t) p (fun _ => dvd_refl p)
      · show Good t p (FreeGroup.toWord (FreeGroup.of (Sum.inl a)))
        simpa using good_toWord_zpow t p (Sum.inl a) 1 (by simp [zLetter])
    · rcases hh with rfl | ⟨a, rfl⟩
      · show Good t p (FreeGroup.toWord ((rootLetter t ^ p)⁻¹))
        simpa [rootLetter, zLetter] using
          good_toWord_zpow t p (zLetter t) (-p) (fun _ => dvd_neg.mpr (dvd_refl p))
      · show Good t p (FreeGroup.toWord ((FreeGroup.of (Sum.inl a))⁻¹))
        simpa using good_toWord_zpow t p (Sum.inl a) (-1) (by simp [zLetter])
  have hmon : Submonoid.closure (genSet t p ∪ (fun g => g⁻¹) '' genSet t p) ≤ goodSub t p :=
    Submonoid.closure_le.mpr hgen
  exact hmon (range_le_submonoid t p hx)

/-- **The `z`-run criterion**: `x` lies in `K = (rootHom t p).range` if and only if every
maximal run of `z`-letters of its reduced word has exponent divisible by `p`. -/
theorem rootHom_mem_iff_good (t : α) (p : ℤ) (x : FreeGroup (RootIdx α t)) :
    x ∈ (rootHom t p).range ↔ Good t p (FreeGroup.toWord x) := by
  constructor
  · exact good_of_mem_range t p
  · intro h
    have h' := goodAux_mem_range t p (FreeGroup.toWord x) 0 (by simpa [Good] using h)
    simpa [FreeGroup.mk_toWord] using h'

end Work.ORLocInd.CohenLyndon
