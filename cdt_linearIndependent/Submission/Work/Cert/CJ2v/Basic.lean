/-
# Conjunct-2 certificate (v4, 1024-grid): the arc-chain glue

`Work.Cert.CJ2`/`CJ2Gen`/`CJ2Grid`/`CJ2Sum` glue the *4096*-grid certificate data (`arcOK`, `arcsOK`,
`gridStep`, `Final` of the 156 chunks) into the per-arc facts of `Conj2Cert`.  The v4 certificate lives
on the `NARC2 = 1024` grid and uses `arcOK2`/`arcsOK2`/`gridStep2`, with its own `Final` (97 chunks,
`vals.length = 3·1024`, `DEN = 7168000`); this file is the literal copy of the data-free arc-chain part
of `CJ2/Gen` + `CJ2/Helpers` with

* `arcOK ↦ arcOK2`, `arcsOK ↦ arcsOK2`, `gridStep ↦ gridStep2`,
* `linkStep ↦ linkStep2`, `arcsChainTo ↦ arcsChainTo2`,
* the grid constants `4096 ↦ 1024` and `12288 ↦ 3072 = 3·1024`.

The purely combinatorial lemmas (`lastArc_append`, `lastArc_eq_getElem_aux`, `sum_range_eq_DsumFin`,
and all the `Dsum`/`msort`/`sortedSum` material in `CJ2Gen`/`CJ2Sum`/`CJ2Grid`) never mention `arcOK`,
so no copy is needed: the originals are reused directly by the v4 assembly.
-/
import Mathlib
import Submission.Work.Cert.Defs
import Submission.Work.Cert.CJ2.Gen
import Submission.Work.Cert.CJ2.Helpers

namespace Work.Cert.CJ2v

open Work.Cert Work.Cert.CJ2

/-! ## Chains of arcs on the 1024-grid -/

/-- one step of the chain, with `arcOK2` in place of `arcOK`. -/
def linkStep2 (a b : ArcD) : Bool :=
  if a.k = b.k then arcOK2 a b.Ex b.Ey else arcOK2 a (Rk a.k) 0

theorem linkStep2_same {a b : ArcD} (h : a.k = b.k) : linkStep2 a b = arcOK2 a b.Ex b.Ey := by
  rw [linkStep2]; exact if_pos h

theorem linkStep2_diff {a b : ArcD} (h : a.k ≠ b.k) : linkStep2 a b = arcOK2 a (Rk a.k) 0 := by
  rw [linkStep2]; exact if_neg h

/-- `arcsChainTo2 Fx Fy L`: the arcs of `L` form one continuous chain of leaves on the 1024-grid of
circle `k`, by the `NARC2`-grid step; the last arc ends at the grid point `(Fx, Fy)`. -/
def arcsChainTo2 (Fx Fy : Int) : List ArcD → Bool
  | [] => true
  | [a] => arcOK2 a Fx Fy
  | a :: b :: rest => linkStep2 a b && arcsChainTo2 Fx Fy (b :: rest)

theorem arcsChainTo2_nil (Fx Fy : Int) : arcsChainTo2 Fx Fy [] = true := rfl
theorem arcsChainTo2_singleton (Fx Fy : Int) (a : ArcD) : arcsChainTo2 Fx Fy [a] = arcOK2 a Fx Fy := rfl
theorem arcsChainTo2_cons_cons (Fx Fy : Int) (a b : ArcD) (t : List ArcD) :
    arcsChainTo2 Fx Fy (a :: b :: t) = (linkStep2 a b && arcsChainTo2 Fx Fy (b :: t)) := rfl

/-! ## Chain lemmas -/

theorem arcsChainTo2_of_arcsOK2 (L : List ArcD) (Fx Fy : Int) (h : arcsOK2 Fx Fy L = true) :
    arcsChainTo2 Fx Fy L = true := by
  induction L generalizing Fx Fy with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simpa [arcsChainTo2, arcsOK2] using h
    | cons b rest =>
      simp only [arcsOK2, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hab, hk⟩, _hj⟩, hrest⟩ := h
      rw [arcsChainTo2_cons_cons, Bool.and_eq_true]
      exact ⟨by rw [linkStep2, if_pos hk]; exact hab, ih Fx Fy hrest⟩

theorem arcsChainTo2_next (L : List ArcD) (Fx Fy : Int)
    (h : arcsChainTo2 Fx Fy L = true) (i : ℕ) (hi : i + 1 < L.length) :
    linkStep2 (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, hi⟩) = true := by
  induction L generalizing Fx Fy i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b rest =>
      rw [arcsChainTo2_cons_cons, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases i with
      | zero => simpa using h1
      | succ i =>
        have hi' : i + 1 < (b :: rest).length := by simpa using hi
        have := ih Fx Fy h2 i hi'
        simpa using this

theorem arcsChainTo2_next_getD (L : List ArcD) (Fx Fy : Int) (h : arcsChainTo2 Fx Fy L = true)
    (i : ℕ) (hi : i + 1 < L.length) :
    linkStep2 (L.getD i dummyArc) (L.getD (i + 1) dummyArc) = true := by
  have h' := arcsChainTo2_next L Fx Fy h i hi
  rw [List.getD_eq_getElem L dummyArc (n := i) (hn := by omega),
      List.getD_eq_getElem L dummyArc (n := i + 1) (hn := hi)]
  exact h'

theorem arcsChainTo2_last (L : List ArcD) (Fx Fy : Int) (h : arcsChainTo2 Fx Fy L = true)
    (hne : L ≠ []) : arcOK2 (lastArc L) Fx Fy = true := by
  induction L generalizing Fx Fy with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => simpa [arcsChainTo2] using h
    | cons b rest =>
      rw [arcsChainTo2_cons_cons, Bool.and_eq_true] at h
      exact ih Fx Fy h.2 (List.cons_ne_nil b rest)

theorem arcsChainTo2_append (L₁ L₂ : List ArcD) (Fx Fy Gx Gy : Int)
    (h₁ : arcsChainTo2 Fx Fy L₁ = true) (h₂ : arcsChainTo2 Gx Gy L₂ = true) (hne : L₂ ≠ [])
    (hl : linkStep2 (lastArc L₁) (headArc L₂) = true) :
    arcsChainTo2 Gx Gy (L₁ ++ L₂) = true := by
  cases L₂ with
  | nil => exact absurd rfl hne
  | cons c t₂ =>
    induction L₁ generalizing Fx Fy with
    | nil => simpa using h₂
    | cons a t ih =>
      cases t with
      | nil =>
        rw [List.singleton_append, arcsChainTo2_cons_cons, Bool.and_eq_true]
        exact ⟨by simpa [lastArc_singleton, headArc_cons] using hl, h₂⟩
      | cons b rest =>
        rw [arcsChainTo2_cons_cons, Bool.and_eq_true] at h₁
        obtain ⟨h1, h1'⟩ := h₁
        rw [List.cons_append, List.cons_append, arcsChainTo2_cons_cons, Bool.and_eq_true]
        refine ⟨by simpa using h1, ?_⟩
        exact ih Fx Fy h1' (by simpa [lastArc_cons_cons] using hl)

theorem arcsOK2_last (L : List ArcD) (Fx Fy : Int) (h : arcsOK2 Fx Fy L = true) (hne : L ≠ []) :
    arcOK2 (lastArc L) Fx Fy = true :=
  arcsChainTo2_last L Fx Fy (arcsChainTo2_of_arcsOK2 L Fx Fy h) hne

theorem arcsChainTo2_last_getElem (L : List ArcD) (Tx Ty : Int) (n : ℕ)
    (h : arcsChainTo2 Tx Ty L = true) (hlen : L.length = n + 1) :
    arcOK2 (L.get ⟨n, by omega⟩) Tx Ty = true := by
  have hL : L ≠ [] := by intro h'; rw [h'] at hlen; simp at hlen
  rw [← lastArc_eq_getElem_aux L n hlen]
  exact arcsChainTo2_last L Tx Ty h hL

theorem arcsChainTo2_last_getD (L : List ArcD) (Tx Ty : Int) (n : ℕ)
    (h : arcsChainTo2 Tx Ty L = true) (hlen : L.length = n + 1) :
    arcOK2 (L.getD n dummyArc) Tx Ty = true := by
  have h' := arcsChainTo2_last_getElem L Tx Ty n h hlen
  rw [List.getD_eq_getElem L dummyArc (n := n) (hn := by omega)]
  exact h'

/-! ## Building a `linkStep2` from an `arcOK2` -/

theorem linkStep2_of_arcOK2 (a b : ArcD) (nx ny : Int) (h : arcOK2 a nx ny = true)
    (h' : (if a.k = b.k then (b.Ex, b.Ey) else (Rk a.k, 0)) = (nx, ny)) :
    linkStep2 a b = true := by
  by_cases hk : a.k = b.k
  · rw [if_pos hk] at h'
    simp only [Prod.mk.injEq] at h'
    rw [← h'.1, ← h'.2] at h
    rw [linkStep2_same hk]
    exact h
  · rw [if_neg hk] at h'
    simp only [Prod.mk.injEq] at h'
    rw [← h'.1, ← h'.2] at h
    rw [linkStep2_diff hk]
    exact h

/-! ## Unpacking `arcOK2` -/

theorem arcOK2_facts (a : ArcD) (nx ny : Int) (h : arcOK2 a nx ny = true) :
    (match a.leaves with
      | [] => false
      | l :: _ => decide (l.Ax = a.Ex) && decide (l.Ay = a.Ey)) = true ∧
    chainOK nx ny a.leaves = true ∧ gridStep2 a.Ex a.Ey nx ny = true ∧
    a.leaves.all (fun l => decide (l.k = a.k) && decide (l.G ≤ a.Gmax) && leafOK l) = true := by
  simp only [arcOK2, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## The `(k,j)` labelling of a list of arcs -/

theorem kAt_of_map (L : List ArcD) (N : ℕ)
    (hmap : L.map (fun a => (a.k, a.j)) = (List.range N).map (fun i => (i / 1024, i % 1024)))
    (i : ℕ) (hi : i < L.length) :
    (L[i]).k = i / 1024 ∧ (L[i]).j = i % 1024 := by
  have hlen : L.length = N := by
    have h := congrArg List.length hmap
    simpa using h
  have h1 : (L[i]?).map (fun a => (a.k, a.j)) = some (i / 1024, i % 1024) := by
    rw [← List.getElem?_map, hmap, List.getElem?_map, List.getElem?_range (by omega : i < N),
      Option.map_some]
  have h2 : (L[i]?).map (fun a => (a.k, a.j)) = some ((L[i]).k, (L[i]).j) := by
    rw [List.getElem?_eq_getElem hi, Option.map_some]
  have h3 : ((L[i]).k, (L[i]).j) = (i / 1024, i % 1024) :=
    Option.some.inj (h2.symm.trans h1)
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-! ## Extraction of the chain steps at index `(k,j)` -/

theorem arcOK2_within (F : ℕ → ArcD) (hstep : ∀ i, i + 1 < 3072 → linkStep2 (F i) (F (i + 1)) = true)
    (hk : ∀ i, i < 3072 → (F i).k = i / 1024)
    (k j : ℕ) (hk2 : k ≤ 2) (hj2 : j + 1 < 1024) :
    arcOK2 (F (1024 * k + j)) (F (1024 * k + j + 1)).Ex (F (1024 * k + j + 1)).Ey = true := by
  have h := hstep (1024 * k + j) (by omega)
  have hk1 : (F (1024 * k + j)).k = k := by
    have h1 := hk (1024 * k + j) (by omega)
    omega
  have hk2' : (F (1024 * k + j + 1)).k = k := by
    have h1 := hk (1024 * k + j + 1) (by omega)
    omega
  rw [linkStep2, if_pos (by rw [hk1, hk2'])] at h
  exact h

theorem arcOK2_end (F : ℕ → ArcD) (hstep : ∀ i, i + 1 < 3072 → linkStep2 (F i) (F (i + 1)) = true)
    (hk : ∀ i, i < 3072 → (F i).k = i / 1024)
    (hlast : arcOK2 (F 3071) (Rk 2) 0 = true)
    (k : ℕ) (hk2 : k ≤ 2) :
    arcOK2 (F (1024 * k + 1023)) (Rk k) 0 = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · have h := hstep 1023 (by omega)
    have hk0 : (F 1023).k = 0 := by
      have h1 := hk 1023 (by omega)
      omega
    have hk1 : (F 1024).k = 1 := by
      have h1 := hk 1024 (by omega)
      omega
    rw [linkStep2, if_neg (by rw [hk0, hk1]; norm_num), hk0] at h
    exact h
  · have h := hstep 2047 (by omega)
    have hk1 : (F 2047).k = 1 := by
      have h1 := hk 2047 (by omega)
      omega
    have hk2' : (F 2048).k = 2 := by
      have h1 := hk 2048 (by omega)
      omega
    rw [linkStep2, if_neg (by rw [hk1, hk2']; norm_num), hk1] at h
    exact h
  · exact hlast

end Work.Cert.CJ2v
