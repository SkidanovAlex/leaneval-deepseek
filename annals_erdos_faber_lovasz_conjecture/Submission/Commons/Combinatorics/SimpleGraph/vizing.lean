import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.LineGraph

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-!
# Vizing's theorem

Every finite simple graph `G` has a proper edge colouring with `G.maxDegree + 1` colours,
i.e. the line graph of `G` is `(maxDegree + 1)`-colourable.

The proof is the classical fan argument with Kempe chains (see e.g. Diestel, *Graph Theory*,
Proposition 5.3.2), formalised here in a "maximal partial colouring" setting.
-/

namespace Commons.Combinatorics.SimpleGraph

namespace Vizing


variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Basic definitions -/

/-- The colour `a` is **missing** at the vertex `x` for the colouring `c` of the edge set `S`:
no edge of `S` incident with `x` has colour `a`. -/
def MissingAt {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x : V) (a : Fin k) : Prop :=
  ∀ e ∈ S, x ∈ e → c e ≠ a

/-- `c` is a proper edge colouring of the finite edge set `S`. -/
def IsProper {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → c e ≠ c e'

lemma IsProper.mono {k : ℕ} {S S' : Finset (Sym2 V)} {c : Sym2 V → Fin k} (h : IsProper S c)
    (hsub : S' ⊆ S) : IsProper S' c :=
  fun e he e' he' hne hadj => h e (hsub he) e' (hsub he') hne hadj

lemma MissingAt.mono {k : ℕ} {S S' : Finset (Sym2 V)} {c : Sym2 V → Fin k} {x : V} {a : Fin k}
    (h : MissingAt S c x a) (hsub : S' ⊆ S) : MissingAt S' c x a :=
  fun e he hx => h e (hsub he) hx

/-- The map `y ↦ s(x,y)` is injective. -/
lemma sym2_mk_left_injective (x : V) : Function.Injective (fun y : V => s(x, y)) := by
  intro a b h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

lemma sym2_getElem_congr {yl : List V} {x : V} {i j : ℕ} (h : i = j) (hi : i < yl.length)
    (hj : j < yl.length) : s(x, yl[i]'hi) = s(x, yl[j]'hj) := by
  subst h; rfl

/-- There is a colour of `Fin k` missing at `x`, provided the graph has maximum degree `< k`. -/
theorem exists_missingAt (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hΔ : G.maxDegree < k) {S : Finset (Sym2 V)} (hS : ↑S ⊆ G.edgeSet)
    (c : Sym2 V → Fin k) (x : V) : ∃ a : Fin k, MissingAt S c x a := by
  classical
  set T : Finset (Fin k) := (S.filter (fun e => x ∈ e)).image c with hT
  have hcard1 : T.card ≤ (S.filter (fun e => x ∈ e)).card := Finset.card_image_le
  have hsub : S.filter (fun e => x ∈ e) ⊆ (G.neighborFinset x).image (fun y => s(x, y)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heS, hxe⟩ := he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    rw [G.mem_neighborFinset]
    have := hS heS
    rwa [SimpleGraph.mem_edgeSet] at this
  have hcard2 : (S.filter (fun e => x ∈ e)).card ≤ G.degree x := by
    calc (S.filter (fun e => x ∈ e)).card
        ≤ ((G.neighborFinset x).image (fun y => s(x, y))).card := Finset.card_le_card hsub
      _ = (G.neighborFinset x).card := Finset.card_image_of_injective _ (sym2_mk_left_injective x)
      _ = G.degree x := G.card_neighborFinset_eq_degree x
  have hlt : T.card < k := by
    have := G.degree_le_maxDegree x
    omega
  have huniv : T.card < (Finset.univ : Finset (Fin k)).card := by
    simpa using hlt
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card huniv
  refine ⟨a, fun e he hx hcea => ha ?_⟩
  exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, hcea⟩

/-! ### Parity -/

/-- The colour used at step `i` of an alternating path: `α` on even steps, `β` on odd steps. -/
def colAt {k : ℕ} (α β : Fin k) : ℕ → Fin k
  | 0 => α
  | (n + 1) => if colAt α β n = α then β else α

lemma colAt_zero {k : ℕ} (α β : Fin k) : colAt α β 0 = α := rfl

lemma colAt_succ {k : ℕ} (α β : Fin k) (n : ℕ) :
    colAt α β (n + 1) = if colAt α β n = α then β else α := rfl

lemma colAt_mem {k : ℕ} (α β : Fin k) (n : ℕ) :
    colAt α β n = α ∨ colAt α β n = β := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih => rw [colAt_succ]; split <;> simp

lemma colAt_succ_ne {k : ℕ} {α β : Fin k} (h : α ≠ β) (n : ℕ) :
    colAt α β (n + 1) ≠ colAt α β n := by
  rw [colAt_succ]
  rcases colAt_mem α β n with hh | hh
  · rw [if_pos hh]
    exact fun hc => h (hc.trans hh).symm
  · rw [if_neg (by rw [hh]; exact fun hc => h hc.symm)]
    exact fun hc => h (hc.trans hh)

lemma colAt_add_two {k : ℕ} (α β : Fin k) (n : ℕ) :
    colAt α β (n + 2) = colAt α β n := by
  by_cases hab : α = β
  · subst hab
    have hconst : ∀ m, colAt α α m = α := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [colAt_succ, ih]; simp
    rw [hconst, hconst]
  · rw [show n + 2 = (n + 1) + 1 by omega, colAt_succ, colAt_succ]
    rcases colAt_mem α β n with hh | hh
    · have h1 : (if colAt α β n = α then β else α) = β := if_pos hh
      rw [h1, if_neg (by intro hc; exact hab hc.symm), hh]
    · have h1 : ¬(colAt α β n = α) := by rw [hh]; exact fun hc => hab hc.symm
      rw [if_neg h1, if_pos rfl]
      exact hh.symm

/-- In an alternating path with distinct colours, the colour of the previous edge is `α` whenever
the current edge has colour `β`. -/
lemma colAt_of_succ_eq {k : ℕ} {α β : Fin k} (h : α ≠ β) {n : ℕ}
    (hβ : colAt α β (n + 1) = β) : colAt α β n = α := by
  rcases colAt_mem α β n with hh | hh
  · exact hh
  · exact absurd (hβ ▸ hh ▸ colAt_succ_ne h n) (by simp)

/-! ### Shifting colours along a fan -/

/-- `shiftAlong x c l` recolours the edge `s(x, l[m])` with the colour of `s(x, l[m+1])`
(for `m + 1 < l.length`) and leaves all other edges unchanged. -/
noncomputable def shiftAlong (x : V) {k : ℕ} (c : Sym2 V → Fin k) : List V → (Sym2 V → Fin k)
  | [] => c
  | [_] => c
  | a :: b :: rest => fun e => if e = s(x, a) then c (s(x, b)) else shiftAlong x c (b :: rest) e

lemma shiftAlong_cons_cons {k : ℕ} (c : Sym2 V → Fin k) (x a b : V) (rest : List V) :
    shiftAlong x c (a :: b :: rest) =
      fun e => if e = s(x, a) then c (s(x, b)) else shiftAlong x c (b :: rest) e := rfl

lemma shiftAlong_eq_of_not {k : ℕ} (c : Sym2 V → Fin k) (x : V) :
    ∀ (l : List V), l.Nodup → ∀ e : Sym2 V,
      (∀ (i : ℕ) (_hi : i + 1 < l.length), e ≠ s(x, l[i])) → shiftAlong x c l e = c e := by
  intro l
  induction l with
  | nil => intro _ e _; rfl
  | cons a t ih =>
    intro hnd e h
    cases t with
    | nil => rfl
    | cons b rest =>
      rw [shiftAlong_cons_cons]
      beta_reduce
      rw [if_neg]
      · apply ih hnd.of_cons
        intro i hi
        exact h (i+1) (by have h2 := hi; simp only [List.length_cons] at h2 ⊢; omega)
      · simpa using h 0 (by simp)

lemma shiftAlong_getElem {k : ℕ} (c : Sym2 V → Fin k) (x : V) :
    ∀ (l : List V), l.Nodup → ∀ (i : ℕ) (_hi : i + 1 < l.length),
      shiftAlong x c l (s(x, l[i])) = c (s(x, l[i+1])) := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons a t ih =>
    intro hnd i hi
    cases t with
    | nil => simp at hi
    | cons b rest =>
      rcases i with _ | i
      · have h1 : (a :: b :: rest)[0] = a := List.getElem_cons_zero a (b :: rest) (by simp)
        have h2 : (a :: b :: rest)[0+1] = b := by
          rw [List.getElem_cons_succ a (b :: rest) 0 (by simp)]
          exact List.getElem_cons_zero b rest (by simp)
        rw [h1, h2, shiftAlong_cons_cons]
        beta_reduce
        simp
      · have hib : i < (b :: rest).length := by
          have h3 := hi; simp only [List.length_cons] at h3 ⊢; omega
        have hib2 : i + 1 < (b :: rest).length := by
          have h3 := hi; simp only [List.length_cons] at h3 ⊢; omega
        have h1 : (a :: b :: rest)[i+1] = (b :: rest)[i] :=
          List.getElem_cons_succ a (b :: rest) i (by omega)
        have h2 : (a :: b :: rest)[i+1+1] = (b :: rest)[i+1] :=
          List.getElem_cons_succ a (b :: rest) (i+1) (by omega)
        rw [h1, h2, shiftAlong_cons_cons]
        beta_reduce
        have hmem : (b :: rest)[i] ∈ (b :: rest) := List.getElem_mem hib
        have han : a ∉ (b :: rest) := (List.nodup_cons.mp hnd).1
        have hne : (b :: rest)[i] ≠ a := fun hh => han (hh ▸ hmem)
        rw [if_neg (fun hh => hne (sym2_mk_left_injective x hh))]
        exact ih hnd.of_cons i hib2

lemma shiftAlong_take_getElem {k : ℕ} (c : Sym2 V → Fin k) (x : V) (yl : List V)
    (hnd : yl.Nodup) {t m : ℕ} (ht : t < yl.length) (hm : m < t) :
    shiftAlong x c (yl.take (t + 1)) (s(x, yl[m])) = c (s(x, yl[m+1])) := by
  have hlen : (yl.take (t + 1)).length = t + 1 := by
    rw [List.length_take]; omega
  have hm1 : m + 1 < (yl.take (t + 1)).length := by rw [hlen]; omega
  have h := shiftAlong_getElem c x (yl.take (t + 1)) (hnd.take) m hm1
  rwa [List.getElem_take, List.getElem_take] at h

lemma shiftAlong_take_eq_of_not {k : ℕ} (c : Sym2 V → Fin k) (x : V) (yl : List V)
    (hnd : yl.Nodup) {t : ℕ} {e : Sym2 V}
    (h : ∀ (i : ℕ) (hi : i < yl.length), i < t → e ≠ s(x, yl[i]'hi)) :
    shiftAlong x c (yl.take (t + 1)) e = c e := by
  refine shiftAlong_eq_of_not c x _ hnd.take e ?_
  intro i hi
  have hi' : i < yl.length := by rw [List.length_take] at hi; omega
  have hit : i < t := by rw [List.length_take] at hi; omega
  have hmain : e ≠ s(x, yl[i]) := h i hi' hit
  simpa only [List.getElem_take] using hmain

/-! ### Fans -/

/-- The relation "the fan can step from `a` to `b`": the edge `s(x,b)` is in `S` and its colour is
missing at `a`. -/
def FanRel {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x : V) (a b : V) : Prop :=
  s(x, b) ∈ S ∧ MissingAt S c a (c (s(x, b)))

/-- A fan at `x`: a list of distinct neighbours `y₀, y₁, …` of `x` such that for `m ≥ 1` the edge
`s(x, y_m)` lies in `S` and its colour is missing at `y_{m-1}`. -/
def IsFan (G : SimpleGraph V) {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x : V)
    (y : List V) : Prop :=
  y.Nodup ∧ (∀ v ∈ y, s(x, v) ∈ G.edgeSet) ∧ List.IsChain (FanRel S c x) y

lemma IsFan.rel {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {x : V}
    {y : List V} (h : IsFan G S c x y) (i : ℕ) (hi : i + 1 < y.length) :
    FanRel S c x y[i] y[i+1] :=
  h.2.2.getElem i hi

/-- A longest fan. -/
theorem exists_longest_fan (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x y0 : V) (hy0G : s(x, y0) ∈ G.edgeSet) :
    ∃ y : List V, y.head? = some y0 ∧ IsFan G S c x y ∧
      ∀ (hne : y ≠ []) (z : V), z ∉ y → s(x, z) ∈ G.edgeSet →
        ¬ FanRel S c x (y.getLast hne) z := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ y : List V, y.head? = some y0 ∧ IsFan G S c x y ∧ y.length = n
  have hP1 : P 1 := by
    refine ⟨[y0], rfl, ⟨by simp, ?_, List.IsChain.singleton y0⟩, rfl⟩
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv; exact hy0G
  have hbound : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨y, -, ⟨hnd, -, -⟩, rfl⟩
    exact hnd.length_le_card
  haveI : Nonempty V := ⟨x⟩
  have hcardpos : 1 ≤ Fintype.card V := Fintype.card_pos
  set n0 := Nat.findGreatest P (Fintype.card V) with hn0def
  have hPn0 : P n0 := Nat.findGreatest_spec hcardpos hP1
  have hmax : ∀ n, n0 < n → n ≤ Fintype.card V → ¬P n :=
    ((Nat.findGreatest_eq_iff (P := P) (k := Fintype.card V)).mp hn0def).2.2
  obtain ⟨y, hhead, hfan, hlen⟩ := hPn0
  refine ⟨y, hhead, hfan, ?_⟩
  intro hne z hz hzG hrel
  have hPsucc : P (n0 + 1) := by
    refine ⟨y ++ [z], ?_, ?_, by simp [List.length_append, hlen]⟩
    · rw [List.head?_append, hhead]; rfl
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hfan.1, List.nodup_singleton z, by
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact fun hab => hz (hab ▸ ha)⟩
      · intro v hv
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · exact hfan.2.1 v hv
        · rw [List.mem_singleton] at hv; subst hv; exact hzG
      · rw [List.isChain_append]
        refine ⟨hfan.2.2, List.IsChain.singleton z, ?_⟩
        intro a ha b hb
        simp only [List.head?_cons, Option.mem_some_iff] at hb
        subst hb
        rw [List.getLast?_eq_some_getLast hne] at ha
        simp only [Option.mem_some_iff] at ha
        subst ha
        exact hrel
  have hle : n0 + 1 ≤ Fintype.card V := hbound _ hPsucc
  exact hmax (n0+1) (Nat.lt_succ_self _) hle hPsucc




/-! ### Shifting colours along a fan -/
lemma IsFan.fst {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} (h : IsFan G S c x yl) {i : ℕ} (hi : i + 1 < yl.length) :
    s(x, yl[i+1]) ∈ S :=
  (h.rel i hi).1

lemma IsFan.snd {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} (h : IsFan G S c x yl) {i : ℕ} (hi : i + 1 < yl.length) :
    MissingAt S c yl[i] (c (s(x, yl[i+1]))) :=
  (h.rel i hi).2

lemma IsFan.ne_x {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} (h : IsFan G S c x yl) {j : ℕ} (hjlen : j < yl.length) :
    yl[j] ≠ x := by
  have h1 := h.2.1 (yl[j]) (List.getElem_mem hjlen)
  rw [SimpleGraph.mem_edgeSet] at h1
  exact fun hh => G.ne_of_adj h1 hh.symm

/-- The "hole" edge set obtained from `S` by removing `et` and adding the (uncoloured) edge `e0`. -/
def holeSet (S : Finset (Sym2 V)) (e0 et : Sym2 V) : Finset (Sym2 V) := (insert e0 S).erase et

/-- `e` is one of the fan edges whose colour is moved one step along the fan. -/
def IsFanShift (yl : List V) (x : V) (t : ℕ) (e : Sym2 V) : Prop :=
  ∃ (m : ℕ) (hm : m < yl.length), m < t ∧ e = s(x, yl[m]'hm)

/-- The index map of the shift. -/
def phi (t m : ℕ) : ℕ := if m < t then m + 1 else m

lemma phi_pos {t m : ℕ} (hm : m ≠ t) : 1 ≤ phi t m := by
  unfold phi; split <;> omega

lemma phi_lt {t m n : ℕ} (ht : t < n) (hm : m < n) (hmt : m ≠ t) : phi t m < n := by
  unfold phi; split <;> omega

lemma phi_inj {t m m' : ℕ} (hm : m ≠ t) (hm' : m' ≠ t) (h : phi t m = phi t m') : m = m' := by
  by_cases h1 : m < t <;> by_cases h2 : m' < t
  · simp only [phi, if_pos h1, if_pos h2] at h; omega
  · simp only [phi, if_pos h1, if_neg h2] at h; omega
  · simp only [phi, if_neg h1, if_pos h2] at h; omega
  · simp only [phi, if_neg h1, if_neg h2] at h; exact h

lemma shiftAlong_take_fanEdge {k : ℕ} (c : Sym2 V → Fin k) (x : V) (yl : List V)
    (hnd : yl.Nodup) {t m : ℕ} (ht : t < yl.length) (hm : m < yl.length) (hmt : m ≠ t) :
    shiftAlong x c (yl.take (t + 1)) (s(x, yl[m]'hm)) =
      c (s(x, yl[phi t m]'(phi_lt ht hm hmt))) := by
  by_cases h : m < t
  · simp only [phi, if_pos h]
    exact shiftAlong_take_getElem c x yl hnd ht h
  · simp only [phi, if_neg h]
    refine shiftAlong_take_eq_of_not c x yl hnd ?_
    intro i hi hit hh
    have h2 : yl[i] = yl[m] := sym2_mk_left_injective x hh.symm
    have h3 : i = m := hnd.getElem_inj_iff.mp h2
    omega

/-- An edge of the hole set that is not a shifted fan edge lies in `S`. -/
lemma mem_S_of_not_sfe {S : Finset (Sym2 V)} {x : V} {yl : List V} {t : ℕ}
    (ht : t < yl.length) {e : Sym2 V} (he : e ∈ holeSet S (s(x, yl[0])) (s(x, yl[t])))
    (hne : ¬ IsFanShift yl x t e) : e ∈ S := by
  unfold holeSet at he
  obtain ⟨hene, heins⟩ := Finset.mem_erase.mp he
  rcases Finset.mem_insert.mp heins with h | h
  · exfalso
    by_cases h0 : 0 < t
    · exact hne ⟨0, by omega, h0, h⟩
    · have ht0 : t = 0 := by omega
      subst ht0
      exact hene h
  · exact h

/-- The shifted colouring is proper on the hole edge set. -/
theorem isProper_shiftAlong (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {x : V} {yl : List V}
    {t : ℕ} (ht : t < yl.length)
    (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c) (hfan : IsFan G S c x yl)
    (he0S : s(x, yl[0]) ∉ S) :
    IsProper (holeSet S (s(x, yl[0])) (s(x, yl[t]))) (shiftAlong x c (yl.take (t + 1))) := by
  intro f hf g hg hfg ⟨u, huf, hug⟩
  have hfne : f ≠ s(x, yl[t]) := (Finset.mem_erase.mp (by unfold holeSet at hf; exact hf)).1
  have hgne : g ≠ s(x, yl[t]) := (Finset.mem_erase.mp (by unfold holeSet at hg; exact hg)).1
  have hfhe : f ∈ holeSet S (s(x, yl[0])) (s(x, yl[t])) := by unfold holeSet; exact hf
  have hghe : g ∈ holeSet S (s(x, yl[0])) (s(x, yl[t])) := by unfold holeSet; exact hg
  by_cases hfSFE : IsFanShift yl x t f
  · obtain ⟨mf, hmflen, hmft, rfl⟩ := hfSFE
    rw [shiftAlong_take_getElem c x yl hfan.1 ht hmft]
    by_cases hgSFE : IsFanShift yl x t g
    · obtain ⟨mg, hmglen, hmgt, rfl⟩ := hgSFE
      rw [shiftAlong_take_getElem c x yl hfan.1 ht hmgt]
      have hmf1 : s(x, yl[mf+1]) ∈ S := hfan.fst (by omega)
      have hmg1 : s(x, yl[mg+1]) ∈ S := hfan.fst (by omega)
      have hne : s(x, yl[mf+1]) ≠ s(x, yl[mg+1]) := by
        intro hh
        have h2 : yl[mf+1] = yl[mg+1] := sym2_mk_left_injective x hh
        have h3 : mf + 1 = mg + 1 := hfan.1.getElem_inj_iff.mp h2
        exact hfg (sym2_getElem_congr (show mf = mg by omega) hmflen hmglen)
      exact hc _ hmf1 _ hmg1 hne ⟨x, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    · have hgS : g ∈ S := mem_S_of_not_sfe ht hghe hgSFE
      have hnot : ∀ (i : ℕ) (hi : i < yl.length), i < t → g ≠ s(x, yl[i]'hi) :=
        fun i hi hit hh => hgSFE ⟨i, hi, hit, hh⟩
      rw [shiftAlong_take_eq_of_not c x yl hfan.1 hnot]
      by_cases hux : u = x
      · rw [hux] at hug
        have hf1 : s(x, yl[mf+1]) ∈ S := hfan.fst (by omega)
        have hne : s(x, yl[mf+1]) ≠ g := by
          intro hh
          by_cases hlt : mf + 1 < t
          · exact hgSFE ⟨mf+1, by omega, hlt, hh.symm⟩
          · have hle : mf + 1 = t := by omega
            exact hgne (by
              have h1 : s(x, yl[t]) = s(x, yl[mf+1]) := sym2_getElem_congr hle.symm ht (by omega)
              rw [h1]; exact hh.symm)
        exact hc _ hf1 _ hgS hne ⟨x, Sym2.mem_mk_left _ _, hug⟩
      · have hu : u = yl[mf] := by
          rcases Sym2.mem_iff.mp huf with h | h
          · exact absurd h hux
          · exact h
        have hmiss := hfan.snd (i := mf) (by omega)
        exact fun hc' => hmiss g hgS (by rw [← hu]; exact hug) hc'.symm
  · have hfS : f ∈ S := mem_S_of_not_sfe ht hfhe hfSFE
    have hnot : ∀ (i : ℕ) (hi : i < yl.length), i < t → f ≠ s(x, yl[i]'hi) :=
      fun i hi hit hh => hfSFE ⟨i, hi, hit, hh⟩
    rw [shiftAlong_take_eq_of_not c x yl hfan.1 hnot]
    by_cases hgSFE : IsFanShift yl x t g
    · obtain ⟨mg, hmglen, hmgt, rfl⟩ := hgSFE
      rw [shiftAlong_take_getElem c x yl hfan.1 ht hmgt]
      have hg1 : s(x, yl[mg+1]) ∈ S := hfan.fst (by omega)
      by_cases hux : u = x
      · rw [hux] at huf
        have hne : f ≠ s(x, yl[mg+1]) := by
          intro hh
          by_cases hlt : mg + 1 < t
          · exact hfSFE ⟨mg+1, by omega, hlt, hh⟩
          · have hle : mg + 1 = t := by omega
            exact hfne (by
              have h1 : s(x, yl[t]) = s(x, yl[mg+1]) := sym2_getElem_congr hle.symm ht (by omega)
              rw [h1]; exact hh)
        exact fun hc' => hc _ hg1 _ hfS hne.symm ⟨x, Sym2.mem_mk_left _ _, huf⟩ hc'.symm
      · have hu : u = yl[mg] := by
          rcases Sym2.mem_iff.mp hug with h | h
          · exact absurd h hux
          · exact h
        have hmiss := hfan.snd (i := mg) (by omega)
        exact fun hc' => hmiss f hfS (by rw [← hu]; exact huf) hc'
    · have hgS : g ∈ S := mem_S_of_not_sfe ht hghe hgSFE
      have hnotg : ∀ (i : ℕ) (hi : i < yl.length), i < t → g ≠ s(x, yl[i]'hi) :=
        fun i hi hit hh => hgSFE ⟨i, hi, hit, hh⟩
      rw [shiftAlong_take_eq_of_not c x yl hfan.1 hnotg]
      exact hc _ hfS _ hgS hfg ⟨u, huf, hug⟩

/-- Colours missing at `x` remain missing after shifting along the fan. -/
theorem missingAt_x_shiftAlong {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} {x : V} {yl : List V} (hfan : IsFan G S c x yl) {t : ℕ}
    (ht : t < yl.length) {a : Fin k} (ha : MissingAt S c x a) :
    MissingAt (holeSet S (s(x, yl[0])) (s(x, yl[t]))) (shiftAlong x c (yl.take (t + 1))) x a := by
  intro e he hxe
  by_cases hSFE : IsFanShift yl x t e
  · obtain ⟨m, hmlen, hmt, rfl⟩ := hSFE
    rw [shiftAlong_take_getElem c x yl hfan.1 ht hmt]
    exact ha (s(x, yl[m+1])) (hfan.fst (by omega)) (Sym2.mem_mk_left _ _)
  · have hnot : ∀ (i : ℕ) (hi : i < yl.length), i < t → e ≠ s(x, yl[i]'hi) :=
      fun i hi hit hh => hSFE ⟨i, hi, hit, hh⟩
    rw [shiftAlong_take_eq_of_not c x yl hfan.1 hnot]
    exact ha e (mem_S_of_not_sfe ht he hSFE) hxe

/-- A colour missing at `yl[t]` (with respect to `S`) is still missing after shifting. -/
theorem missingAt_index_shiftAlong {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} {x : V} {yl : List V} (hfan : IsFan G S c x yl) {t : ℕ}
    (ht : t < yl.length) {b : Fin k} (hb : MissingAt S c yl[t] b) :
    MissingAt (holeSet S (s(x, yl[0])) (s(x, yl[t]))) (shiftAlong x c (yl.take (t + 1))) yl[t] b := by
  intro e he hye
  have hene : e ≠ s(x, yl[t]) := (Finset.mem_erase.mp (by unfold holeSet at he; exact he)).1
  have heS : e ∈ S := by
    unfold holeSet at he
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp he).2 with h | h
    · subst h
      exfalso
      rcases Sym2.mem_iff.mp hye with h | h
      · exact hfan.ne_x (j := t) ht h
      · have ht0 : t = 0 := hfan.1.getElem_inj_iff.mp h
        have h1 : s(x, yl[t]) = s(x, yl[0]) := sym2_getElem_congr ht0 ht (by omega)
        exact hene h1.symm
    · exact h
  have hnot : ∀ (i : ℕ) (hi : i < yl.length), i < t → e ≠ s(x, yl[i]'hi) := by
    intro i hi hit hh
    rw [hh] at hye
    rcases Sym2.mem_iff.mp hye with h | h
    · exact hfan.ne_x (j := t) ht h
    · have hti : t = i := hfan.1.getElem_inj_iff.mp h
      exact hene (hh.trans (sym2_getElem_congr hti.symm hi (by omega)))
  rw [shiftAlong_take_eq_of_not c x yl hfan.1 hnot]
  exact hb e heS hye

/-! ### Alternating (Kempe) paths -/

/-- `l` is an alternating path from `v` whose `i`-th edge has colour `colAt α β i`. -/
def IsABPath {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (α β : Fin k) (v : V)
    (l : List V) : Prop :=
  l.head? = some v ∧ l.Nodup ∧
    ∀ (i : ℕ) (_hi : i + 1 < l.length),
      s(l[i], l[i+1]) ∈ S ∧ c (s(l[i], l[i+1])) = colAt α β i

/-- `l` can be extended by the vertex `w`. -/
def ABExtendible {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (α β : Fin k) (l : List V)
    (w : V) : Prop :=
  ∃ (hne : l ≠ []), w ∉ l ∧ s(l.getLast hne, w) ∈ S ∧
    c (s(l.getLast hne, w)) = colAt α β (l.length - 1)

/-- A longest alternating path. -/
def IsLongestABPath {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (α β : Fin k) (v : V)
    (l : List V) : Prop :=
  IsABPath S c α β v l ∧ ∀ w, ¬ABExtendible S c α β l w

lemma IsABPath.ne_nil {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {α β : Fin k} {v : V}
    {l : List V} (h : IsABPath S c α β v l) : l ≠ [] := by
  intro hh
  have h1 := h.1
  rw [hh] at h1
  simp at h1

lemma IsABPath.head_eq {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {α β : Fin k} {v : V}
    {l : List V} (h : IsABPath S c α β v l) (hl : 0 < l.length) : l[0] = v := by
  have h1 := h.1
  rw [List.head?_eq_getElem?] at h1
  rw [List.getElem?_eq_getElem hl] at h1
  exact Option.some.inj h1

/-- A longest alternating path exists. -/
theorem exists_longest_abpath {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (α β : Fin k)
    (v : V) : ∃ l : List V, IsLongestABPath S c α β v l := by
  classical
  let Q : ℕ → Prop := fun n => ∃ l : List V, IsABPath S c α β v l ∧ l.length = n
  have hQ1 : Q 1 :=
    ⟨[v], ⟨rfl, List.nodup_singleton v, by intro i hi; simp at hi⟩, rfl⟩
  have hbound : ∀ n, Q n → n ≤ Fintype.card V := by
    rintro n ⟨l, hl, rfl⟩
    exact hl.2.1.length_le_card
  haveI : Nonempty V := ⟨v⟩
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  set n0 := Nat.findGreatest Q (Fintype.card V) with hn0def
  have hQn0 : Q n0 := Nat.findGreatest_spec hcard hQ1
  have hmax : ∀ n, n0 < n → n ≤ Fintype.card V → ¬Q n :=
    ((Nat.findGreatest_eq_iff (P := Q) (k := Fintype.card V)).mp hn0def).2.2
  obtain ⟨l, hl, hlen⟩ := hQn0
  refine ⟨l, hl, ?_⟩
  intro w hext
  obtain ⟨hne, hwl, hwS, hwc⟩ := hext
  have hQsucc : Q (n0 + 1) := by
    refine ⟨l ++ [w], ?_, by simp [List.length_append, hlen]⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [List.head?_append, hl.1]; rfl
    · rw [List.nodup_append]
      exact ⟨hl.2.1, List.nodup_singleton w, by
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact fun hab => hwl (hab ▸ ha)⟩
    · intro i hi
      have hlen : (l ++ [w]).length = l.length + 1 := by simp [List.length_append]
      rcases Nat.lt_or_eq_of_le (show i + 1 ≤ l.length by omega) with hlt | heq
      · have h2 := hl.2.2 i (by omega)
        rw [List.getElem_append_left (as := l) (bs := [w]) (i := i) (by omega),
            List.getElem_append_left (as := l) (bs := [w]) (i := i+1) (by omega)]
        exact h2
      · have hlast : (l ++ [w])[i] = l.getLast hne := by
          rw [List.getElem_append_left (as := l) (bs := [w]) (i := i) (by omega),
              List.getLast_eq_getElem hne]
          congr 1
          omega
        have hlastw : (l ++ [w])[i+1] = w := by
          exact List.getElem_concat_length (l := l) (a := w) (i := i+1) heq (by omega)
        rw [hlast, hlastw]
        exact ⟨hwS, by rw [hwc]; congr 1; omega⟩
  have hle : n0 + 1 ≤ Fintype.card V := hbound _ hQsucc
  exact hmax (n0 + 1) (Nat.lt_succ_self _) hle hQsucc

/-- Two alternating paths with the same start agree wherever both are defined. -/
theorem abpath_agree {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {α β : Fin k} {v : V}
    (hc : IsProper S c) {l₁ l₂ : List V} (h₁ : IsABPath S c α β v l₁)
    (h₂ : IsABPath S c α β v l₂) :
    ∀ (i : ℕ) (_h1 : i < l₁.length) (_h2 : i < l₂.length), l₁[i] = l₂[i] := by
  intro i
  induction i with
  | zero =>
    intro h1 h2
    rw [h₁.head_eq h1, h₂.head_eq h2]
  | succ n ih =>
    intro h1 h2
    have ih' : l₁[n] = l₂[n] := ih (by omega) (by omega)
    by_contra hne
    have e1 := h₁.2.2 n (by omega)
    have e2 := h₂.2.2 n (by omega)
    have hedge : s(l₁[n], l₁[n+1]) ≠ s(l₂[n], l₂[n+1]) := by
      intro hh
      rw [← ih'] at hh
      exact hne (sym2_mk_left_injective (l₁[n]) hh)
    have hshare : ∃ u, u ∈ s(l₁[n], l₁[n+1]) ∧ u ∈ s(l₂[n], l₂[n+1]) :=
      ⟨l₁[n], Sym2.mem_mk_left _ _, by rw [← ih']; exact Sym2.mem_mk_left _ _⟩
    have := hc _ e1.1 _ e2.1 hedge hshare
    rw [e1.2, e2.2] at this
    exact this rfl


/-- The edge set of a path given by its vertex list. -/
def PathEdge (P : List V) (e : Sym2 V) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < P.length), e = s(P[i]'(by omega), P[i+1]'hi)

noncomputable instance (P : List V) (e : Sym2 V) : Decidable (PathEdge P e) :=
  Classical.dec _

lemma sym2_snd_congr {a : V} {l : List V} {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : s(a, l[i]'hi) = s(a, l[j]'hj) := by subst h; rfl

lemma getElem_congr {l : List V} {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i]'hi = l[j]'hj := by subst h; rfl

lemma PathEdge.intro' {P : List V} {g : Sym2 V} {i : ℕ} (hi : i + 1 < P.length)
    (h : g = s(P[i], P[i+1])) : PathEdge P g := by
  refine ⟨i, hi, ?_⟩
  rw [h]

lemma PathEdge.sub {P : List V} {g : Sym2 V} {i : ℕ} (hi1 : 0 < i) (hi2 : i < P.length)
    (h : g = s(P[i-1], P[i])) : PathEdge P g := by
  refine ⟨i-1, by omega, ?_⟩
  rw [h]
  exact sym2_snd_congr (show i = i-1+1 by omega) (by omega) (by omega)

/-- Among the two colours `α, β`, any of them is `colAt α β n` or `colAt α β (n+1)`. -/
lemma mem_colAt_pair {k : ℕ} {α β γ : Fin k} (hαβ : α ≠ β) (hγ : γ = α ∨ γ = β) (n : ℕ) :
    γ = colAt α β n ∨ γ = colAt α β (n + 1) := by
  have h1 := colAt_mem α β n
  have h2 := colAt_mem α β (n + 1)
  have hne := colAt_succ_ne hαβ n
  rcases hγ with hγ | hγ
  · rcases h1 with h1 | h1
    · exact Or.inl (hγ.trans h1.symm)
    · refine Or.inr (hγ.trans ?_)
      rcases h2 with h2 | h2
      · exact h2.symm
      · exact absurd (h2.trans h1.symm) hne
  · rcases h1 with h1 | h1
    · refine Or.inr (hγ.trans ?_)
      rcases h2 with h2 | h2
      · exact absurd (h2.trans h1.symm) hne
      · exact h2.symm
    · exact Or.inl (hγ.trans h1.symm)

/-- At an internal vertex of an alternating path, every `α`/`β`-edge of `S` is a path edge. -/
lemma abpath_edges_at {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {α β : Fin k} {v : V}
    {P : List V} (hc : IsProper S c) (hαβ : α ≠ β) (hP : IsABPath S c α β v P)
    {i : ℕ} (hi1 : 0 < i) (hi2 : i + 1 < P.length) {g : Sym2 V} (hgS : g ∈ S)
    (hug : P[i] ∈ g) (hgc : c g = α ∨ c g = β) : PathEdge P g := by
  have he1 := hP.2.2 (i - 1) (by omega)
  have he1' : s(P[i-1], P[i]) ∈ S ∧ c (s(P[i-1], P[i])) = colAt α β (i-1) := by
    have hconv : s(P[i-1], P[i-1+1]'(by omega)) = s(P[i-1], P[i]) :=
      sym2_snd_congr (show i-1+1 = i by omega) (by omega) (by omega)
    rw [← hconv]
    exact he1
  have he2 := hP.2.2 i hi2
  rcases mem_colAt_pair hαβ hgc (i-1) with h | h
  · by_cases hge : g = s(P[i-1], P[i])
    · exact PathEdge.sub hi1 (by omega) hge
    · exfalso
      exact hc g hgS _ he1'.1 hge ⟨P[i], hug, Sym2.mem_mk_right _ _⟩ (h.trans he1'.2.symm)
  · have h' : c g = colAt α β i := h.trans (congrArg (colAt α β) (show i-1+1 = i by omega))
    by_cases hge : g = s(P[i], P[i+1])
    · exact PathEdge.intro' hi2 hge
    · exfalso
      exact hc g hgS _ he2.1 hge ⟨P[i], hug, Sym2.mem_mk_left _ _⟩ (h'.trans he2.2.symm)

/-- Every `α`/`β`-edge of `S` at the head of a longest alternating path is a path edge. -/
lemma abpath_edge_at_head {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} {α β : Fin k} {v : V} {P : List V} (hS : ↑S ⊆ G.edgeSet)
    (hc : IsProper S c) (hαβ : α ≠ β) (hP : IsLongestABPath S c α β v P)
    (hv : MissingAt S c v β) (hlen : 0 < P.length) {g : Sym2 V} (hgS : g ∈ S) (hvg : v ∈ g)
    (hgc : c g = α ∨ c g = β) : PathEdge P g := by
  have hv0 : P[0] = v := hP.1.head_eq hlen
  have hgα : c g = α := by
    rcases hgc with h | h
    · exact h
    · exact absurd h (hv g hgS hvg)
  rcases Nat.lt_or_eq_of_le (by omega : 1 ≤ P.length) with h1 | h1
  · have he1 := hP.1.2.2 0 (by omega)
    have hcol1 : c (s(P[0], P[1])) = α := by rw [he1.2, colAt_zero]
    have hge : g = s(P[0], P[1]) := by
      by_contra hne
      exact hc g hgS _ he1.1 hne ⟨v, hvg, by rw [hv0]; exact Sym2.mem_mk_left _ _⟩
        (by rw [hgα, hcol1])
    exact PathEdge.intro' (by omega) hge
  · exfalso
    obtain ⟨w, hgw⟩ := Sym2.mem_iff_exists.mp hvg
    have hPeq : P = [v] := by
      obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hP.1.1
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at h1
        omega)
      subst ht
      rfl
    have hwP : w ∉ P := by
      rw [hPeq]
      intro hwp
      rw [List.mem_singleton] at hwp
      have hdiag : g = s(v, v) := by rw [hgw, hwp]
      have hd := G.not_isDiag_of_mem_edgeSet (hS hgS)
      rw [hdiag] at hd
      exact hd (Sym2.mk_isDiag_iff.mpr rfl)
    have hlast : P.getLast hP.1.ne_nil = v := by
      rw [List.getLast_eq_getElem hP.1.ne_nil]
      exact (getElem_congr (show P.length - 1 = 0 by omega) (by omega) (by omega)).trans
        (hP.1.head_eq (by omega))
    have hext : ABExtendible S c α β P w := by
      refine ⟨hP.1.ne_nil, hwP, ?_, ?_⟩
      · rw [hlast, ← hgw]; exact hgS
      · rw [hlast, ← hgw, hgα, show P.length - 1 = 0 by omega, colAt_zero]
    exact hP.2 w hext

/-- Every `α`/`β`-edge of `S` meeting a longest alternating path is an edge of the path. -/
theorem abpath_edge_of_mem {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} {α β : Fin k} {v : V} {P : List V} (hS : ↑S ⊆ G.edgeSet)
    (hc : IsProper S c) (hαβ : α ≠ β) (hP : IsLongestABPath S c α β v P)
    (hv : MissingAt S c v β) {u : V} (hu : u ∈ P) {g : Sym2 V} (hgS : g ∈ S) (hug : u ∈ g)
    (hgc : c g = α ∨ c g = β) : PathEdge P g := by
  obtain ⟨i, hilen, hieq⟩ := List.getElem_of_mem hu
  subst hieq
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    have hv0 : P[0] = v := hP.1.head_eq hilen
    rw [hv0] at hug
    exact abpath_edge_at_head hS hc hαβ hP hv hilen hgS hug hgc
  · by_cases hlt : i + 1 < P.length
    · exact abpath_edges_at hc hαβ hP.1 hipos hlt hgS hug hgc
    · have hilast : i + 1 = P.length := by omega
      rcases mem_colAt_pair hαβ hgc (i-1) with h | h
      · by_cases hge : g = s(P[i-1], P[i])
        · exact PathEdge.sub hipos hilen hge
        · exfalso
          have he1' : s(P[i-1], P[i]) ∈ S ∧ c (s(P[i-1], P[i])) = colAt α β (i-1) := by
            have he1 := hP.1.2.2 (i-1) (by omega)
            have hconv : s(P[i-1], P[i-1+1]'(by omega)) = s(P[i-1], P[i]) :=
              sym2_snd_congr (show i-1+1 = i by omega) (by omega) (by omega)
            rw [← hconv]
            exact he1
          exact hc g hgS _ he1'.1 hge ⟨P[i], hug, Sym2.mem_mk_right _ _⟩ (h.trans he1'.2.symm)
      · have h' : c g = colAt α β i :=
          h.trans (congrArg (colAt α β) (show i-1+1 = i by omega))
        exfalso
        obtain ⟨w, hgw⟩ := Sym2.mem_iff_exists.mp hug
        by_cases hwP : w ∈ P
        · obtain ⟨j, hjlen, hjeq⟩ := List.getElem_of_mem hwP
          have hji : j ≠ i := by
            intro hji
            have hwi : w = P[i] := hjeq.symm.trans (getElem_congr hji hjlen hilen)
            have hdiag : g = s(P[i], P[i]) := by rw [hgw, hwi]
            have hd := G.not_isDiag_of_mem_edgeSet (hS hgS)
            rw [hdiag] at hd
            exact hd (Sym2.mk_isDiag_iff.mpr rfl)
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0
            have hvg : v ∈ g := by
              have hv0 : P[0] = v := hP.1.head_eq (by omega)
              have hwv : w = v := hjeq.symm.trans hv0
              rw [hwv] at hgw
              rw [hgw]
              exact Sym2.mem_mk_right _ _
            obtain ⟨t, ht, hgt⟩ := abpath_edge_at_head hS hc hαβ hP hv (by omega) hgS hvg hgc
            have hPi : P[i] ∈ g := hug
            rw [hgt] at hPi
            rcases Sym2.mem_iff.mp hPi with h2 | h2
            · have := hP.1.2.1.getElem_inj_iff.mp h2
              omega
            · have h2' : i = t + 1 := hP.1.2.1.getElem_inj_iff.mp h2
              have hcolt : c g = colAt α β t := by rw [hgt, (hP.1.2.2 t ht).2]
              exact absurd (by rw [← h2']; exact h'.symm.trans hcolt) (colAt_succ_ne hαβ t)
          · obtain ⟨t, ht, hgt⟩ := abpath_edges_at hc hαβ hP.1 hjpos (by omega) hgS
              (by rw [hjeq, hgw]; exact Sym2.mem_mk_right _ _) hgc
            have hPi : P[i] ∈ g := hug
            rw [hgt] at hPi
            rcases Sym2.mem_iff.mp hPi with h2 | h2
            · have := hP.1.2.1.getElem_inj_iff.mp h2
              omega
            · have h2' : i = t + 1 := hP.1.2.1.getElem_inj_iff.mp h2
              have hcolt : c g = colAt α β t := by rw [hgt, (hP.1.2.2 t ht).2]
              exact absurd (by rw [← h2']; exact h'.symm.trans hcolt) (colAt_succ_ne hαβ t)
        · have hlasti : P.getLast hP.1.ne_nil = P[i] := by
            rw [List.getLast_eq_getElem hP.1.ne_nil]
            congr 1
            omega
          have hext : ABExtendible S c α β P w := by
            refine ⟨hP.1.ne_nil, hwP, ?_, ?_⟩
            · rw [hlasti, ← hgw]; exact hgS
            · rw [hlasti, ← hgw, h]
              congr 1
              omega
          exact hP.2 w hext


/-- Adding a properly coloured edge to a proper colouring. -/
lemma insert_proper {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} (hc : IsProper S c)
    {e : Sym2 V} (he : e ∉ S) {a : Fin k}
    (ha : ∀ e' ∈ S, e' ≠ e → (∃ u, u ∈ e ∧ u ∈ e') → c e' ≠ a) :
    IsProper (insert e S) (Function.update c e a) := by
  classical
  have hout : ∀ f ∈ S, Function.update c e a f = c f := by
    intro f hf
    by_cases h : f = e
    · subst h; exact absurd hf he
    · exact Function.update_of_ne h a c
  intro f hf g hg hfg hadj
  rcases Finset.mem_insert.mp hf with rfl | hfS
  · rcases Finset.mem_insert.mp hg with hge | hgS
    · exact absurd hge.symm hfg
    · rw [Function.update_self, hout g hgS]
      exact fun hh => ha g hgS (fun h => he (h ▸ hgS)) hadj hh.symm
  · rcases Finset.mem_insert.mp hg with hge | hgS
    · subst hge
      rw [hout f hfS, Function.update_self]
      exact ha f hfS (by rintro rfl; exact he hfS)
        (by rcases hadj with ⟨u, hu, hu'⟩; exact ⟨u, hu', hu⟩)
    · rw [hout f hfS, hout g hgS]
      exact hc f hfS g hgS hfg hadj

/-- Swapping `α` and `β` on the edges of a longest alternating path yields a proper colouring. -/
theorem kempe_swap_proper {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {α β : Fin k} {v : V} {P : List V} (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c) (hαβ : α ≠ β)
    (hP : IsLongestABPath S c α β v P) (hv : MissingAt S c v β) :
    IsProper S (fun e => if PathEdge P e then Equiv.swap α β (c e) else c e) := by
  classical
  intro f hf g hg hfg ⟨u, huf, hug⟩
  by_cases hfP : PathEdge P f
  · by_cases hgP : PathEdge P g
    · simp only [if_pos hfP, if_pos hgP]
      exact fun hh => hc f hf g hg hfg ⟨u, huf, hug⟩ ((Equiv.swap α β).injective hh)
    · simp only [if_pos hfP, if_neg hgP]
      intro hh
      by_cases hcab : c f = α ∨ c f = β
      · have hgab : c g = α ∨ c g = β := by
          rcases hcab with h | h
          · right; rw [← hh, h, Equiv.swap_apply_left]
          · left; rw [← hh, h, Equiv.swap_apply_right]
        obtain ⟨i, hi, rfl⟩ := hfP
        have huP : u ∈ P := by
          rcases Sym2.mem_iff.mp huf with h | h
          · rw [h]; exact List.getElem_mem (l := P) (by omega)
          · rw [h]; exact List.getElem_mem (l := P) (by omega)
        exact hgP (abpath_edge_of_mem hS hc hαβ hP hv huP hg hug hgab)
      · have hfix : Equiv.swap α β (c f) = c f :=
          Equiv.swap_apply_of_ne_of_ne (fun h => hcab (Or.inl h)) (fun h => hcab (Or.inr h))
        rw [hfix] at hh
        exact hc f hf g hg hfg ⟨u, huf, hug⟩ hh
  · by_cases hgP : PathEdge P g
    · simp only [if_neg hfP, if_pos hgP]
      intro hh
      by_cases hcab : c g = α ∨ c g = β
      · have hfab : c f = α ∨ c f = β := by
          rcases hcab with h | h
          · right; rw [hh, h, Equiv.swap_apply_left]
          · left; rw [hh, h, Equiv.swap_apply_right]
        obtain ⟨i, hi, rfl⟩ := hgP
        have huP : u ∈ P := by
          rcases Sym2.mem_iff.mp hug with h | h
          · rw [h]; exact List.getElem_mem (l := P) (by omega)
          · rw [h]; exact List.getElem_mem (l := P) (by omega)
        exact hfP (abpath_edge_of_mem hS hc hαβ hP hv huP hf huf hfab)
      · have hfix : Equiv.swap α β (c g) = c g :=
          Equiv.swap_apply_of_ne_of_ne (fun h => hcab (Or.inl h)) (fun h => hcab (Or.inr h))
        rw [hfix] at hh
        exact hc f hf g hg hfg ⟨u, huf, hug⟩ hh
    · simp only [if_neg hfP, if_neg hgP]
      exact hc f hf g hg hfg ⟨u, huf, hug⟩

/-- After the swap, the colour `α` is missing at the start of the path. -/
theorem kempe_swap_missing {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} {α β : Fin k} {v : V} {P : List V} (hS : ↑S ⊆ G.edgeSet)
    (hc : IsProper S c) (hαβ : α ≠ β) (hP : IsLongestABPath S c α β v P)
    (hv : MissingAt S c v β) :
    MissingAt S (fun e => if PathEdge P e then Equiv.swap α β (c e) else c e) v α := by
  classical
  intro e he hve
  by_cases heP : PathEdge P e
  · obtain ⟨i, hi, rfl⟩ := heP
    have hv0 : P[0] = v := hP.1.head_eq (by omega)
    have hi0 : i = 0 := by
      rcases Sym2.mem_iff.mp hve with h | h
      · rw [← hv0] at h
        exact (hP.1.2.1.getElem_inj_iff.mp h.symm)
      · rw [← hv0] at h
        have := hP.1.2.1.getElem_inj_iff.mp h
        omega
    subst hi0
    have hcol : c (s(P[0], P[1])) = α := by
      rw [(hP.1.2.2 0 (by omega)).2, colAt_zero]
    simp only [if_pos (PathEdge.intro' (by omega) rfl), hcol, Equiv.swap_apply_left]
    exact fun h => hαβ h.symm
  · simp only [if_neg heP]
    intro hca
    have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.1.ne_nil
    rcases Nat.lt_or_eq_of_le (by omega : 1 ≤ P.length) with hlen | hlen
    · have he1 := hP.1.2.2 0 (by omega)
      have hcol1 : c (s(P[0], P[1])) = α := by rw [he1.2, colAt_zero]
      have hv0 : P[0] = v := hP.1.head_eq (by omega)
      have : e = s(P[0], P[1]) := by
        by_contra hne
        exact hc e he _ he1.1 hne ⟨v, hve, by rw [hv0]; exact Sym2.mem_mk_left _ _⟩
          (hca.trans hcol1.symm)
      exact heP (PathEdge.intro' (by omega) this)
    · exfalso
      obtain ⟨w, hgw⟩ := Sym2.mem_iff_exists.mp hve
      have hPeq : P = [v] := by
        obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hP.1.1
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by
          simp only [List.length_cons] at hlen
          omega)
        subst ht
        rfl
      have hwP : w ∉ P := by
        rw [hPeq]
        intro hwp
        rw [List.mem_singleton] at hwp
        have hdiag : e = s(v, v) := by rw [hgw, hwp]
        have hd := G.not_isDiag_of_mem_edgeSet (hS he)
        rw [hdiag] at hd
        exact hd (Sym2.mk_isDiag_iff.mpr rfl)
      have hlast : P.getLast hP.1.ne_nil = v := by
        rw [List.getLast_eq_getElem hP.1.ne_nil]
        exact (getElem_congr (show P.length - 1 = 0 by omega) (by omega) (by omega)).trans
          (hP.1.head_eq (by omega))
      have hext : ABExtendible S c α β P w := by
        refine ⟨hP.1.ne_nil, hwP, ?_, ?_⟩
        · rw [hlast, ← hgw]; exact he
        · rw [hlast, ← hgw, hca, show P.length - 1 = 0 by omega, colAt_zero]
      exact hP.2 w hext

/-- **Kempe's lemma.**  If `(S,c)` is a largest proper colouring and `s(x,y) ∉ S` with `α` missing
at `x` and `β` missing at `y`, then every longest alternating `α`/`β`-path from `y` reaches `x`. -/
theorem kempe_contains {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {x y : V} {α β : Fin k} (hxy : s(x, y) ∈ G.edgeSet) (hxyS : s(x, y) ∉ S)
    (hα : MissingAt S c x α) (hβ : MissingAt S c y β)
    {P : List V} (hP : IsLongestABPath S c α β y P) : x ∈ P := by
  classical
  by_contra hxP
  have hsub : ↑(insert s(x, y) S) ⊆ G.edgeSet := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact hxy
    · exact hS h
  have hαβ : α ≠ β := by
    intro hab
    have hproper : IsProper (insert s(x, y) S) (Function.update c (s(x, y)) α) := by
      refine insert_proper hc hxyS ?_
      intro e' he' _ hadj
      rcases hadj with ⟨u, hu, hu'⟩
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hα e' he' hu'
      · rw [hab]; exact hβ e' he' hu'
    have hcard := hmax _ _ hsub hproper
    rw [Finset.card_insert_of_notMem hxyS] at hcard
    omega
  let c' : Sym2 V → Fin k := fun e => if PathEdge P e then Equiv.swap α β (c e) else c e
  have hproper' : IsProper S c' := kempe_swap_proper hS hc hαβ hP hβ
  have hmissy : MissingAt S c' y α := kempe_swap_missing hS hc hαβ hP hβ
  have hmissx : MissingAt S c' x α := by
    intro e he hxe
    have hx : ¬PathEdge P e := by
      intro heP
      obtain ⟨i, hi, rfl⟩ := heP
      refine hxP ?_
      rcases Sym2.mem_iff.mp hxe with h | h
      · exact h ▸ List.getElem_mem (l := P) (by omega)
      · exact h ▸ List.getElem_mem (l := P) (by omega)
    change (if PathEdge P e then Equiv.swap α β (c e) else c e) ≠ α
    rw [if_neg hx]
    exact hα e he hxe
  have hproper'' : IsProper (insert s(x, y) S) (Function.update c' (s(x, y)) α) := by
    refine insert_proper hproper' hxyS ?_
    intro e' he' _ hadj
    rcases hadj with ⟨u, hu, hu'⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hmissx e' he' hu'
    · exact hmissy e' he' hu'
  have hcard := hmax _ _ hsub hproper''
  rw [Finset.card_insert_of_notMem hxyS] at hcard
  omega

lemma head?_getElem_zero {l : List V} {a : V} (h : l.head? = some a) (hl : 0 < l.length) :
    l[0] = a := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h
  exact List.getElem_cons_zero a t (by simp)

lemma IsFan.edge_mem_at {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} (h : IsFan G S c x yl) {m : ℕ} (hm : 1 ≤ m) (hml : m < yl.length) :
    s(x, yl[m]) ∈ S := by
  have h1 := h.fst (i := m - 1) (by omega)
  have hconv : s(x, yl[m-1+1]'(by omega)) = s(x, yl[m]'hml) :=
    sym2_snd_congr (show m-1+1 = m by omega) (by omega) hml
  rwa [hconv] at h1

lemma IsFan.missing_at {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} (h : IsFan G S c x yl) {m : ℕ} (hm : 1 ≤ m) (hml : m < yl.length) :
    MissingAt S c yl[m-1] (c (s(x, yl[m]))) := by
  have h1 := h.snd (i := m - 1) (by omega)
  have hconv : s(x, yl[m-1+1]'(by omega)) = s(x, yl[m]'hml) :=
    sym2_snd_congr (show m-1+1 = m by omega) (by omega) hml
  rwa [hconv] at h1

lemma colAt_eq_left_iff {k : ℕ} {α β : Fin k} (hαβ : α ≠ β) (m : ℕ) :
    colAt α β m = α ↔ Even m := by
  induction m with
  | zero => simp [colAt]
  | succ m ih =>
    rw [colAt_succ, Nat.even_add_one]
    constructor
    · intro h
      by_cases hm : Even m
      · rw [if_pos (ih.mpr hm)] at h
        exact absurd h.symm hαβ
      · exact hm
    · intro h
      rw [if_neg (fun hm => h (ih.mp hm))]

lemma colAt_eq_of_even_add {k : ℕ} {α β : Fin k} (hαβ : α ≠ β) {m n : ℕ} (h : Even (m + n)) :
    colAt α β m = colAt α β n := by
  have hmn : Even m ↔ Even n := Nat.even_add.mp h
  have hiff : (colAt α β m = α) ↔ (colAt α β n = α) := by
    rw [colAt_eq_left_iff hαβ, colAt_eq_left_iff hαβ]; exact hmn
  rcases colAt_mem α β n with hn | hn
  · rw [hn]; exact hiff.mpr hn
  · rw [hn]
    rcases colAt_mem α β m with hm | hm
    · rw [hm] at hiff
      exact absurd ((hiff.mp rfl).symm.trans hn) hαβ
    · exact hm

/-- Reversing an alternating path of even length gives an alternating path (with the same
colour parameters) starting at the last vertex. -/
lemma abpath_reverse {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {α β : Fin k} {v : V} {Q : List V} (hαβ : α ≠ β) (hQ : IsABPath S c α β v Q)
    (heven : Even Q.length) (h2 : 2 ≤ Q.length) :
    IsABPath S c α β (Q[Q.length - 1]) Q.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.head?_reverse]
    have hne : Q ≠ [] := by rintro rfl; simp at h2
    rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem hne]
  · rw [List.nodup_reverse]
    exact hQ.2.1
  · intro i hi
    have hLen : Q.reverse.length = Q.length := List.length_reverse
    have hPi : Q.reverse[i] = Q[Q.length - 1 - i] := by
      rw [List.getElem_reverse]
    have hPi1 : Q.reverse[i+1] = Q[Q.length - 2 - i] := by
      rw [List.getElem_reverse]
      exact getElem_congr (show Q.length - 1 - (i+1) = Q.length - 2 - i by omega) (by omega) (by omega)
    rw [hPi, hPi1]
    have hj : Q.length - 2 - i + 1 < Q.length := by omega
    have hQj := hQ.2.2 (Q.length - 2 - i) hj
    have hjeq : Q.length - 2 - i + 1 = Q.length - 1 - i := by omega
    have hedge : s(Q[Q.length - 1 - i]'(by omega), Q[Q.length - 2 - i]'(by omega)) =
        s(Q[Q.length - 2 - i]'(by omega), Q[Q.length - 2 - i + 1]'(by omega)) := by
      rw [Sym2.eq_iff]
      right
      exact ⟨getElem_congr (show Q.length - 1 - i = Q.length - 2 - i + 1 by omega) (by omega)
        (by omega), rfl⟩
    rw [hedge]
    refine ⟨hQj.1, ?_⟩
    rw [hQj.2]
    exact colAt_eq_of_even_add hαβ (by
      rw [show Q.length - 2 - i + i = Q.length - 2 by omega]
      obtain ⟨a, ha⟩ := heven
      exact ⟨a - 1, by omega⟩)

/-- Reversing the edges of a path (dropping the last edge) gives an alternating path. -/
lemma abpath_reverse_inner {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k} {α β : Fin k}
    {Q : List V} (hαβ : α ≠ β) (hnd : Q.Nodup) (h2 : 2 ≤ Q.length)
    (heven : Even (Q.length - 1))
    (hedge : ∀ (i : ℕ) (_hi : i + 1 < Q.length - 1),
      s(Q[i], Q[i+1]) ∈ S ∧ c (s(Q[i], Q[i+1])) = colAt α β i) :
    IsABPath S c α β (Q[Q.length - 2]) Q.dropLast.reverse := by
  have hdl : Q.dropLast.length = Q.length - 1 := List.length_dropLast
  have hlen : (Q.dropLast.reverse).length = Q.length - 1 := by
    rw [List.length_reverse, List.length_dropLast]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.head?_reverse, List.getLast?_dropLast, if_neg (by omega),
      List.getElem?_eq_getElem (by omega : Q.length - 2 < Q.length)]
  · rw [List.nodup_reverse]
    exact List.Sublist.nodup (List.dropLast_sublist Q) hnd
  · intro i hi
    have hiQ : i + 1 < Q.length - 1 := by rw [← hlen]; exact hi
    have hPi : Q.dropLast.reverse[i] = Q[Q.length - 2 - i] := by
      rw [List.getElem_reverse, List.getElem_dropLast]
      congr 1
      omega
    have hPi1 : Q.dropLast.reverse[i+1] = Q[Q.length - 3 - i] := by
      rw [List.getElem_reverse, List.getElem_dropLast]
      exact getElem_congr (show Q.dropLast.length - 1 - (i+1) = Q.length - 3 - i by
        rw [List.length_dropLast]; omega) (by omega) (by omega)
    rw [hPi, hPi1]
    have hj : Q.length - 3 - i + 1 < Q.length - 1 := by omega
    have hQj := hedge (Q.length - 3 - i) hj
    have hedge' : s(Q[Q.length - 2 - i]'(by omega), Q[Q.length - 3 - i]'(by omega)) =
        s(Q[Q.length - 3 - i]'(by omega), Q[Q.length - 3 - i + 1]'(by omega)) := by
      rw [Sym2.eq_iff]
      right
      exact ⟨getElem_congr (show Q.length - 2 - i = Q.length - 3 - i + 1 by omega) (by omega)
        (by omega), rfl⟩
    rw [hedge']
    refine ⟨hQj.1, ?_⟩
    rw [hQj.2]
    exact colAt_eq_of_even_add hαβ (by
      rw [show Q.length - 3 - i + i = Q.length - 3 by omega]
      obtain ⟨a, ha⟩ := heven
      exact ⟨a - 1, by omega⟩)


/-- A colour missing at `yl[u]` for `(S,c)` stays missing for the shifted colouring with the hole
at `yl[j]`, provided `j < u`. -/
lemma missingAt_shiftOf {G : SimpleGraph V} {k : ℕ} {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    {x : V} {yl : List V} {j u : ℕ} (hfan : IsFan G S c x yl) (hul : u < yl.length)
    (he0S : s(x, yl[0]) ∉ S) (hju : j < u) {b : Fin k} (hb : MissingAt S c yl[u] b) :
    MissingAt (holeSet S (s(x, yl[0])) (s(x, yl[j])))
      (shiftAlong x c (yl.take (j + 1))) yl[u] b := by
  intro e he hye
  have heS : e ∈ S := by
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp he).2 with h | h
    · subst h
      exfalso
      rcases Sym2.mem_iff.mp hye with h2 | h2
      · exact hfan.ne_x (j := u) hul h2
      · have := hfan.1.getElem_inj_iff.mp h2
        omega
    · exact h
  have hnot : ∀ (i : ℕ) (hi : i < yl.length), i < j → e ≠ s(x, yl[i]'hi) := by
    intro i hi hij hh
    rw [hh] at hye
    rcases Sym2.mem_iff.mp hye with h2 | h2
    · exact hfan.ne_x (j := u) hul h2
    · have := hfan.1.getElem_inj_iff.mp h2
      omega
  rw [shiftAlong_take_eq_of_not (t := j) c x yl hfan.1 hnot]
  exact hb e heS hye

theorem fan_contradiction {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {S : Finset (Sym2 V)}
    {c : Sym2 V → Fin k} (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {x : V} {yl : List V} {α β : Fin k} {t j : ℕ}
    (hfan : IsFan G S c x yl) (htl : t < yl.length) (he0S : s(x, yl[0]) ∉ S)
    (he0G : s(x, yl[0]) ∈ G.edgeSet) (hα : MissingAt S c x α) (hβ : MissingAt S c yl[t] β)
    (hjt : j < t) (hmissj : MissingAt S c yl[j] β)
    (hsxjck : shiftAlong x c (yl.take (t+1)) (s(x, yl[j])) = β) : False := by
  classical
  let ck : Sym2 V → Fin k := shiftAlong x c (yl.take (t + 1))
  let Sk : Finset (Sym2 V) := holeSet S (s(x, yl[0])) (s(x, yl[t]))
  have hproperk : IsProper Sk ck := isProper_shiftAlong G htl hS hc hfan he0S
  have hmissxk : MissingAt Sk ck x α := missingAt_x_shiftAlong hfan htl hα
  have hmissyk : MissingAt Sk ck yl[t] β := missingAt_index_shiftAlong hfan htl hβ
  have hckj : ck (s(x, yl[j])) = β := hsxjck
  have hekS : s(x, yl[t]) ∉ Sk := Finset.notMem_erase _ _
  have hxyt : s(x, yl[t]) ∈ G.edgeSet := by
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0; exact he0G
    · exact hS (hfan.edge_mem_at htpos htl)
  have hSksub : ↑Sk ⊆ G.edgeSet := by
    intro e' he'
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp he').2 with rfl | h
    · exact he0G
    · exact hS h
  have hSkcard : Sk.card = S.card := by
    show ((insert (s(x, yl[0])) S).erase (s(x, yl[t]))).card = S.card
    have hmem : s(x, yl[t]) ∈ insert (s(x, yl[0])) S := by
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfan.edge_mem_at htpos htl)
    rw [Finset.card_erase_of_mem hmem, Finset.card_insert_of_notMem he0S]
    omega
  have hmaxk : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ Sk.card := by
    intro S' c' hS' hc'
    rw [hSkcard]; exact hmax S' c' hS' hc'
  have hsub' : ↑(insert (s(x, yl[t])) Sk) ⊆ G.edgeSet := by
    intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | h
    · exact hxyt
    · exact hSksub h
  have hαβ : α ≠ β := by
    intro hab
    have hproper' : IsProper (insert (s(x, yl[t])) Sk) (Function.update ck (s(x, yl[t])) α) := by
      refine insert_proper hproperk hekS ?_
      intro e' he' _ hadj
      rcases hadj with ⟨u, hu, hu'⟩
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hmissxk e' he' hu'
      · rw [hab]; exact hmissyk e' he' hu'
    have hcard := hmaxk _ _ hsub' hproper'
    rw [Finset.card_insert_of_notMem hekS, hSkcard] at hcard
    omega
  obtain ⟨Q, hQ⟩ := exists_longest_abpath Sk ck α β yl[t]
  have hxQ : x ∈ Q := kempe_contains hSksub hproperk hmaxk hxyt hekS hmissxk hmissyk hQ
  have hQnd : Q.Nodup := hQ.1.2.1
  have hQlen : 2 ≤ Q.length := by
    by_contra hcon
    obtain ⟨i, hil, hiq⟩ := List.getElem_of_mem hxQ
    have hi0 : i = 0 := by omega
    subst hi0
    have hyt : Q[0] = yl[t] := head?_getElem_zero hQ.1.1 (by omega)
    exact hfan.ne_x htl (by rw [← hiq, hyt])
  have hxlast : Q[Q.length - 1] = x := by
    obtain ⟨i, hil, hiq⟩ := List.getElem_of_mem hxQ
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · exfalso
      subst hi0
      exact hfan.ne_x htl (by rw [← hiq, head?_getElem_zero hQ.1.1 (by omega)])
    · by_cases hilast : i + 1 = Q.length
      · exact (getElem_congr (show Q.length - 1 = i by omega) (by omega) hil).trans hiq
      · exfalso
        have hilt : i + 1 < Q.length := by omega
        obtain ⟨he1i, he1c⟩ := hQ.1.2.2 (i-1) (by omega)
        have he1i' : s(Q[i-1], Q[i]) ∈ Sk := by
          have hconv : s(Q[i-1], Q[i-1+1]'(by omega)) = s(Q[i-1], Q[i]'(by omega)) :=
            sym2_snd_congr (show i-1+1 = i by omega) (by omega) (by omega)
          rwa [hconv] at he1i
        have he1c' : ck (s(Q[i-1], Q[i])) = colAt α β (i-1) := by
          have hconv : s(Q[i-1], Q[i-1+1]'(by omega)) = s(Q[i-1], Q[i]'(by omega)) :=
            sym2_snd_congr (show i-1+1 = i by omega) (by omega) (by omega)
          rwa [hconv] at he1c
        obtain ⟨he2i, he2c⟩ := hQ.1.2.2 i hilt
        have hα1 : colAt α β (i-1) = α ∨ colAt α β i = α := by
          rcases colAt_mem α β (i-1) with h | h
          · exact Or.inl h
          · right
            rcases colAt_mem α β i with h2 | h2
            · exact h2
            · exact absurd (h.trans h2.symm) (fun hh =>
                colAt_succ_ne hαβ (i-1) (by rw [show i-1+1 = i by omega]; exact hh.symm))
        rcases hα1 with hh | hh
        · have hx1 : x ∈ s(Q[i-1], Q[i]) := by rw [hiq]; exact Sym2.mem_mk_right _ _
          have hcontra := hmissxk (s(Q[i-1], Q[i])) he1i' hx1
          rw [he1c', hh] at hcontra
          exact hcontra rfl
        · have hx2 : x ∈ s(Q[i], Q[i+1]) := by rw [hiq]; exact Sym2.mem_mk_left _ _
          have hcontra := hmissxk (s(Q[i], Q[i+1])) he2i hx2
          rw [he2c, hh] at hcontra
          exact hcontra rfl
  have hA1 : Q[Q.length - 2 + 1] = x := by
    exact (getElem_congr (show Q.length - 2 + 1 = Q.length - 1 by omega) (by omega) (by omega)).trans hxlast
  have hlastβ : colAt α β (Q.length - 2) = β := by
    have hilt : Q.length - 2 + 1 < Q.length := by omega
    obtain ⟨heSi, heSc⟩ := hQ.1.2.2 (Q.length - 2) hilt
    have hxe : x ∈ s(Q[Q.length - 2], Q[Q.length - 2 + 1]) := by
      rw [hA1]; exact Sym2.mem_mk_right _ _
    have hcontra := hmissxk (s(Q[Q.length - 2], Q[Q.length - 2 + 1])) heSi hxe
    rcases colAt_mem α β (Q.length - 2) with hh | hh
    · rw [heSc, hh] at hcontra; exact absurd rfl hcontra
    · exact hh
  have heven : Even (Q.length - 1) := by
    have hpoly : Q.length - 1 = Q.length - 2 + 1 := by omega
    rw [hpoly, Nat.even_add_one]
    intro hh
    exact hαβ (((colAt_eq_left_iff hαβ (Q.length - 2)).mpr hh).symm.trans hlastβ)
  have hQlast : Q[Q.length - 2] = yl[j] := by
    have hilt : Q.length - 2 + 1 < Q.length := by omega
    obtain ⟨heSi, heSc⟩ := hQ.1.2.2 (Q.length - 2) hilt
    have hsxjSk : s(x, yl[j]) ∈ Sk := by
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hh
        have h1 : yl[j] = yl[t] := sym2_mk_left_injective x hh
        exact absurd (hfan.1.getElem_inj_iff.mp h1) (by omega)
      · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hfan.edge_mem_at hjpos (by omega))
    have hedge : s(Q[Q.length - 2], Q[Q.length - 2 + 1]) = s(x, yl[j]) := by
      by_contra hne
      exact hproperk _ heSi _ hsxjSk hne
        ⟨x, by rw [hA1]; exact Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
        (by rw [heSc, hlastβ, hckj])
    rw [hA1] at hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact h1.trans h2
    · exact h1
  -- The hole at j
  let Sj : Finset (Sym2 V) := holeSet S (s(x, yl[0])) (s(x, yl[j]))
  let cj : Sym2 V → Fin k := shiftAlong x c (yl.take (j + 1))
  have hjtl : j < yl.length := by omega
  have hproperj : IsProper Sj cj := isProper_shiftAlong G hjtl hS hc hfan he0S
  have hmissxj : MissingAt Sj cj x α := missingAt_x_shiftAlong hfan hjtl hα
  have hmissjj : MissingAt Sj cj yl[j] β := missingAt_index_shiftAlong hfan hjtl hmissj
  have hejSj : s(x, yl[j]) ∉ Sj := Finset.notMem_erase _ _
  have hxjt : s(x, yl[j]) ∈ G.edgeSet := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; exact he0G
    · exact hS (hfan.edge_mem_at hjpos hjtl)
  have hSjsSub : ↑Sj ⊆ G.edgeSet := by
    intro e' he'
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp he').2 with rfl | h
    · exact he0G
    · exact hS h
  have hSjcard : Sj.card = S.card := by
    show ((insert (s(x, yl[0])) S).erase (s(x, yl[j]))).card = S.card
    have hmem : s(x, yl[j]) ∈ insert (s(x, yl[0])) S := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfan.edge_mem_at hjpos hjtl)
    rw [Finset.card_erase_of_mem hmem, Finset.card_insert_of_notMem he0S]
    omega
  have hmaxj : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ Sj.card := by
    intro S' c' hS' hc'
    rw [hSjcard]; exact hmax S' c' hS' hc'
  have hmissing_tj : MissingAt Sj cj yl[t] β :=
    missingAt_shiftOf (j := j) hfan htl he0S hjt hβ
  -- The reversed inner path
  have hinner : ∀ (i : ℕ) (_hi : i + 1 < Q.length - 1),
      s(Q[i], Q[i+1]) ∈ Sj ∧ cj (s(Q[i], Q[i+1])) = colAt α β i := by
    intro i hi
    obtain ⟨hei, hec⟩ := hQ.1.2.2 i (by omega)
    have hxne1 : Q[i] ≠ x := by
      intro hh
      have h1 : i = Q.length - 1 := hQnd.getElem_inj_iff.mp (hh.trans hxlast.symm)
      omega
    have hxne2 : Q[i+1] ≠ x := by
      intro hh
      have h1 : i+1 = Q.length - 1 := hQnd.getElem_inj_iff.mp (hh.trans hxlast.symm)
      omega
    have hxnmem : x ∉ s(Q[i], Q[i+1]) := by
      intro hh
      rcases Sym2.mem_iff.mp hh with h | h
      · exact hxne1 h.symm
      · exact hxne2 h.symm
    have heS : s(Q[i], Q[i+1]) ∈ S := by
      rcases Finset.mem_insert.mp (Finset.mem_erase.mp hei).2 with h | h
      · exact absurd (by rw [h]; exact Sym2.mem_mk_left x (yl[0])) hxnmem
      · exact h
    refine ⟨?_, ?_⟩
    · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_insert_of_mem heS⟩
      intro hh
      exact hxnmem (by rw [hh]; exact Sym2.mem_mk_left x yl[j])
    · have hcjeq : cj (s(Q[i], Q[i+1])) = c (s(Q[i], Q[i+1])) := by
        refine shiftAlong_take_eq_of_not (t := j) c x yl hfan.1 ?_
        intro m hm hmt hh
        exact hxnmem (by rw [hh]; exact Sym2.mem_mk_left x yl[m])
      have hckeq : ck (s(Q[i], Q[i+1])) = c (s(Q[i], Q[i+1])) := by
        refine shiftAlong_take_eq_of_not (t := t) c x yl hfan.1 ?_
        intro m hm hmt hh
        exact hxnmem (by rw [hh]; exact Sym2.mem_mk_left x yl[m])
      rw [hcjeq, ← hckeq]
      exact hec
  have hnddrop : Q.dropLast.Nodup := List.Sublist.nodup (List.dropLast_sublist Q) hQnd
  have hrev : IsABPath Sj cj α β (Q[Q.length - 2]) Q.dropLast.reverse :=
    abpath_reverse_inner hαβ hQnd hQlen heven hinner
  have hrevhead : (Q.dropLast.reverse).head? = some yl[j] := by
    rw [hrev.1, ← hQlast]
  have hrev2 : IsABPath Sj cj α β yl[j] Q.dropLast.reverse := ⟨hrevhead, hrev.2⟩
  -- `P''` is not extendible
  have hrev_nonext : ∀ w, ¬ABExtendible Sj cj α β Q.dropLast.reverse w := by
    intro w hext
    rcases hext with ⟨hne, hwl, hwS, hwc⟩
    have hPne : Q.dropLast.reverse ≠ [] := hrev2.ne_nil
    have hPpos : 0 < (Q.dropLast.reverse).length := List.length_pos_of_ne_nil hPne
    have hlastv : (Q.dropLast.reverse).getLast hne = yl[t] := by
      rw [List.getLast_reverse]
      rw [List.head_eq_getElem_zero, List.getElem_dropLast]
      exact head?_getElem_zero hQ.1.1 (by omega)
    have hreq : colAt α β ((Q.dropLast.reverse).length - 1) = β := by
      have h1 : (Q.dropLast.reverse).length - 1 = Q.length - 2 := by
        rw [List.length_reverse, List.length_dropLast]
        omega
      rw [h1]
      exact hlastβ
    rw [hlastv] at hwS hwc
    rw [hreq] at hwc
    exact hmissing_tj (s(yl[t], w)) hwS (Sym2.mem_mk_left yl[t] w) hwc
  -- R
  obtain ⟨R, hR⟩ := exists_longest_abpath Sj cj α β yl[j]
  have hxR : x ∈ R := kempe_contains hSjsSub hproperj hmaxj hxjt hejSj hmissxj hmissjj hR
  have hRle : R.length ≤ (Q.dropLast.reverse).length := by
    by_contra hcon
    have hlt : (Q.dropLast.reverse).length < R.length := by omega
    have hPne : Q.dropLast.reverse ≠ [] := hrev2.ne_nil
    have hPpos : 0 < (Q.dropLast.reverse).length := List.length_pos_of_ne_nil hPne
    refine hrev_nonext (R[(Q.dropLast.reverse).length]) ⟨hPne, ?_, ?_, ?_⟩
    · intro hmem
      obtain ⟨j', hj'l, hj'q⟩ := List.getElem_of_mem hmem
      have hag : R[j'] = (Q.dropLast.reverse)[j'] :=
        abpath_agree hproperj hR.1 hrev2 j' (by omega) hj'l
      have hw : R[(Q.dropLast.reverse).length] = (Q.dropLast.reverse)[j'] := by rw [hj'q]
      have hjj := hR.1.2.1.getElem_inj_iff.mp (hag.trans hw.symm)
      omega
    · have hvl : (Q.dropLast.reverse).getLast hPne
          = (Q.dropLast.reverse)[(Q.dropLast.reverse).length - 1] := List.getLast_eq_getElem hPne
      have hag : R[(Q.dropLast.reverse).length - 1]
          = (Q.dropLast.reverse)[(Q.dropLast.reverse).length - 1] :=
        abpath_agree hproperj hR.1 hrev2 _ (by omega) (by omega)
      have he := (hR.1.2.2 ((Q.dropLast.reverse).length - 1) (by omega)).1
      have hconv : s(R[(Q.dropLast.reverse).length - 1], R[(Q.dropLast.reverse).length - 1 + 1])
          = s(R[(Q.dropLast.reverse).length - 1], R[(Q.dropLast.reverse).length]) :=
        sym2_snd_congr (show (Q.dropLast.reverse).length - 1 + 1 = (Q.dropLast.reverse).length by omega)
          (by omega) (by omega)
      rw [hvl, ← hag, ← hconv]
      exact he
    · have hvl : (Q.dropLast.reverse).getLast hPne
          = (Q.dropLast.reverse)[(Q.dropLast.reverse).length - 1] := List.getLast_eq_getElem hPne
      have hag : R[(Q.dropLast.reverse).length - 1]
          = (Q.dropLast.reverse)[(Q.dropLast.reverse).length - 1] :=
        abpath_agree hproperj hR.1 hrev2 _ (by omega) (by omega)
      have he := (hR.1.2.2 ((Q.dropLast.reverse).length - 1) (by omega)).2
      have hconv : s(R[(Q.dropLast.reverse).length - 1], R[(Q.dropLast.reverse).length - 1 + 1])
          = s(R[(Q.dropLast.reverse).length - 1], R[(Q.dropLast.reverse).length]) :=
        sym2_snd_congr (show (Q.dropLast.reverse).length - 1 + 1 = (Q.dropLast.reverse).length by omega)
          (by omega) (by omega)
      rw [hvl, ← hag, ← hconv]
      exact he
  have hxnotR : x ∉ R := by
    intro hxR'
    obtain ⟨i, hil, hiq⟩ := List.getElem_of_mem hxR'
    have hiP : i < (Q.dropLast.reverse).length := by omega
    have hag : R[i] = (Q.dropLast.reverse)[i] := abpath_agree hproperj hR.1 hrev2 i hil hiP
    have hiQ : i < Q.length - 1 := by
      have h2 := hiP
      rw [List.length_reverse, List.length_dropLast] at h2
      exact h2
    have hPi : (Q.dropLast.reverse)[i] = Q[Q.length - 2 - i] := by
      have heqidx : Q.dropLast.length - 1 - i = Q.length - 2 - i := by
        have h2 : Q.dropLast.length = Q.length - 1 := List.length_dropLast
        rw [h2]
        omega
      rw [List.getElem_reverse, List.getElem_dropLast]
      exact getElem_congr heqidx (by omega) (by omega)
    have hneq : Q[Q.length - 2 - i] ≠ x := by
      intro hh
      have h1 : Q.length - 2 - i = Q.length - 1 := hQnd.getElem_inj_iff.mp (hh.trans hxlast.symm)
      omega
    exact hneq (hPi.symm.trans (hag.symm.trans hiq))
  exact hxnotR hxR

/-- The extension step of Vizing's theorem: a largest proper partial colouring cannot miss an edge. -/
theorem extends_of_maximal (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hΔ : G.maxDegree < k) {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {e : Sym2 V} (heG : e ∈ G.edgeSet) (heS : e ∉ S) : False := by
  classical
  induction e using Sym2.ind with
  | h x y0 =>
    obtain ⟨α, hα⟩ := exists_missingAt G hΔ hS c x
    obtain ⟨yl, hhead, hfan, hfanmax⟩ := exists_longest_fan G S c x y0 heG
    have hylne : yl ≠ [] := by rintro rfl; simp at hhead
    have hpos : 0 < yl.length := List.length_pos_of_ne_nil hylne
    let t : ℕ := yl.length - 1
    have htl : t < yl.length := by omega
    have hy0 : yl[0] = y0 := head?_getElem_zero hhead hpos
    have he0S : s(x, yl[0]) ∉ S := by rw [hy0]; exact heS
    have he0G : s(x, yl[0]) ∈ G.edgeSet := by rw [hy0]; exact heG
    obtain ⟨β, hβ⟩ := exists_missingAt G hΔ hS c yl[t]
    let ck : Sym2 V → Fin k := shiftAlong x c (yl.take (t + 1))
    let Sk : Finset (Sym2 V) := holeSet S (s(x, yl[0])) (s(x, yl[t]))
    have hproperk : IsProper Sk ck := isProper_shiftAlong G htl hS hc hfan he0S
    have hmissxk : MissingAt Sk ck x α := missingAt_x_shiftAlong hfan htl hα
    have hmissyk : MissingAt Sk ck yl[t] β := missingAt_index_shiftAlong hfan htl hβ
    have hekS : s(x, yl[t]) ∉ Sk := Finset.notMem_erase _ _
    have hxyt : s(x, yl[t]) ∈ G.edgeSet := by
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · rw [sym2_snd_congr ht0 htl hpos]; exact he0G
      · exact hS (hfan.edge_mem_at htpos htl)
    have hSksub : ↑Sk ⊆ G.edgeSet := by
      intro e' he'
      rcases Finset.mem_insert.mp (Finset.mem_erase.mp he').2 with rfl | h
      · exact he0G
      · exact hS h
    have hSkcard : Sk.card = S.card := by
      show ((insert (s(x, yl[0])) S).erase (s(x, yl[t]))).card = S.card
      have hmem : s(x, yl[t]) ∈ insert (s(x, yl[0])) S := by
        rcases Nat.eq_zero_or_pos t with ht0 | htpos
        · rw [sym2_snd_congr ht0 htl hpos]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hfan.edge_mem_at htpos htl)
      rw [Finset.card_erase_of_mem hmem, Finset.card_insert_of_notMem he0S]
      omega
    have hmaxk : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
        IsProper S' c' → S'.card ≤ Sk.card := by
      intro S' c' hS' hc'
      rw [hSkcard]; exact hmax S' c' hS' hc'
    by_cases hmissxk' : MissingAt Sk ck x β
    · have hproper' : IsProper (insert (s(x, yl[t])) Sk) (Function.update ck (s(x, yl[t])) β) := by
        refine insert_proper hproperk hekS ?_
        intro e' he' _ hadj
        rcases hadj with ⟨u, hu, hu'⟩
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · exact hmissxk' e' he' hu'
        · exact hmissyk e' he' hu'
      have hsub' : ↑(insert (s(x, yl[t])) Sk) ⊆ G.edgeSet := by
        intro e' he'
        rcases Finset.mem_insert.mp he' with rfl | h
        · exact hxyt
        · exact hSksub h
      have hcard := hmaxk _ _ hsub' hproper'
      have hmem : s(x, yl[t]) ∈ insert (s(x, yl[0])) S := by
        rcases Nat.eq_zero_or_pos t with ht0 | htpos
        · rw [sym2_snd_congr ht0 htl hpos]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hfan.edge_mem_at htpos htl)
      have hins : insert (s(x, yl[t])) Sk = insert (s(x, yl[0])) S := by
        show insert (s(x, yl[t])) ((insert (s(x, yl[0])) S).erase (s(x, yl[t]))) = insert (s(x, yl[0])) S
        rw [Finset.insert_erase hmem]
      rw [hins, Finset.card_insert_of_notMem he0S] at hcard
      omega
    · unfold MissingAt at hmissxk'
      push_neg at hmissxk'
      obtain ⟨f, hfSk, hxf, hfc⟩ := hmissxk'
      obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp hxf
      have hfG : f ∈ G.edgeSet := hSksub hfSk
      by_cases hzyl : z ∈ yl
      · obtain ⟨j, hjl, hjz⟩ := List.getElem_of_mem hzyl
        have hfj : f = s(x, yl[j]) := by rw [hfz, ← hjz]
        have hjt : j ≠ t := by
          intro hjt
          have h1 : f = s(x, yl[t]) := hfj.trans (sym2_snd_congr hjt hjl htl)
          exact hekS (h1 ▸ hfSk)
        have hjt' : j < t := by omega
        have hckj : ck (s(x, yl[j])) = β := by rw [← hfj]; exact hfc
        have hsxjck : shiftAlong x c (yl.take (t+1)) (s(x, yl[j])) = β := hckj
        have hbeta : β = c (s(x, yl[j+1])) := by
          have h1 := hckj
          change shiftAlong x c (yl.take (t + 1)) (s(x, yl[j])) = β at h1
          rw [shiftAlong_take_getElem c x yl hfan.1 htl hjt'] at h1
          exact h1.symm
        have hmissj : MissingAt S c yl[j] β := by
          rw [hbeta]
          exact hfan.missing_at (m := j+1) (by omega) (by omega)
        exact fan_contradiction hS hc hmax hfan htl he0S he0G hα hβ hjt' hmissj hsxjck
      · exfalso
        have hfS : f ∈ S := by
          rcases Finset.mem_insert.mp (Finset.mem_erase.mp hfSk).2 with h | h
          · exfalso
            apply hzyl
            have h2 : z = yl[0] := sym2_mk_left_injective x (hfz.symm.trans h)
            rw [h2]
            exact List.getElem_mem (l := yl) hpos
          · exact h
        have hckf : ck f = c f := by
          have h1 : shiftAlong x c (yl.take (t+1)) f = c f := by
            rw [hfz]
            refine shiftAlong_take_eq_of_not (t := t) c x yl hfan.1 ?_
            intro m hm hmt hh
            exact hzyl (by
              have h2 : z = yl[m] := sym2_mk_left_injective x hh
              rw [h2]; exact List.getElem_mem (l := yl) hm)
          exact h1
        have hcf : c f = β := by rw [← hckf]; exact hfc
        have hlast : yl.getLast hylne = yl[t] := by
          rw [List.getLast_eq_getElem]
        refine hfanmax hylne z hzyl ?_ ⟨?_, ?_⟩
        · rw [← hfz]; exact hfG
        · rw [← hfz]; exact hfS
        · rw [hlast, ← hfz, hcf]; exact hβ


end Vizing

open Vizing

/-- **Vizing's theorem.**  Every finite simple graph has a proper edge colouring with
`maxDegree + 1` colours. -/
theorem vizing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.lineGraph.Colorable (G.maxDegree + 1) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (S : Finset (Sym2 V)) (c : Sym2 V → Fin (G.maxDegree + 1)),
    ↑S ⊆ G.edgeSet ∧ IsProper S c ∧ S.card = n
  have hP0 : P 0 := ⟨∅, fun _ => 0, by simp, by intro e he; simp at he, rfl⟩
  have hbound : ∀ n, P n → n ≤ Fintype.card G.edgeSet := by
    rintro n ⟨S, c, hS, hc, rfl⟩
    have hsub : S ⊆ G.edgeFinset := by
      intro e he
      rw [SimpleGraph.mem_edgeFinset]
      exact hS he
    calc S.card ≤ G.edgeFinset.card := Finset.card_le_card hsub
      _ = Fintype.card G.edgeSet := SimpleGraph.edgeFinset_card
  have hs := Nat.findGreatest_spec (P := P) (n := Fintype.card G.edgeSet) (m := 0)
    (Nat.zero_le _) hP0
  obtain ⟨S, c, hS, hc, hScard⟩ := hs
  have hmax' : ∀ n, Nat.findGreatest P (Fintype.card G.edgeSet) < n →
      n ≤ Fintype.card G.edgeSet → ¬P n := by
    intro n h1 h2
    exact ((Nat.findGreatest_eq_iff (P := P) (k := Fintype.card G.edgeSet)).mp rfl).2.2 h1 h2
  have hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin (G.maxDegree + 1)),
      ↑S' ⊆ G.edgeSet → IsProper S' c' → S'.card ≤ S.card := by
    intro S' c' hS' hc'
    by_contra hcon
    have hPS' : P S'.card := ⟨S', c', hS', hc', rfl⟩
    have hlt : Nat.findGreatest P (Fintype.card G.edgeSet) < S'.card := by omega
    exact hmax' _ hlt (hbound _ hPS') hPS'
  have hSeq : ∀ e ∈ G.edgeSet, e ∈ S := by
    intro e heG
    by_contra heS
    exact extends_of_maximal (k := G.maxDegree + 1) G (by omega) hS hc hmax heG heS
  refine ⟨SimpleGraph.Coloring.mk (fun e : G.edgeSet => c e.val) ?_⟩
  intro e1 e2 hadj
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hv1, hv2⟩ := hadj
  exact hc e1.val (hSeq _ e1.property) e2.val (hSeq _ e2.property)
    (fun h => hne (Subtype.ext h)) ⟨v, hv1, hv2⟩


end Commons.Combinatorics.SimpleGraph