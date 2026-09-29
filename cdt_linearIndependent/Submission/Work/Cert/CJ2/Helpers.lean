/-
# Generic helpers for the conjunct-2 certificate extraction

Data-free lemmas about `arcOK`/`arcsOK`/`arcsChainTo`, about the `(k,j)` labelling of an arc list,
about unpacking `arcOK`, and about the extraction of the chain steps at a given `(k,j)`.
Imports only `Mathlib` and `CJ2/Gen`, so it stays cheap to build.
-/
import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2

open Work.Cert

/-! ## Chain lemmas -/

theorem arcsChainTo_of_arcsOK (L : List ArcD) (Fx Fy : Int) (h : arcsOK Fx Fy L = true) :
    arcsChainTo Fx Fy L = true := by
  induction L generalizing Fx Fy with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simpa [arcsChainTo, arcsOK] using h
    | cons b rest =>
      simp only [arcsOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hab, hk⟩, _hj⟩, hrest⟩ := h
      rw [arcsChainTo_cons_cons, Bool.and_eq_true]
      exact ⟨by rw [linkStep, if_pos hk]; exact hab, ih Fx Fy hrest⟩

theorem arcsChainTo_next (L : List ArcD) (Fx Fy : Int)
    (h : arcsChainTo Fx Fy L = true) (i : ℕ) (hi : i + 1 < L.length) :
    linkStep (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, hi⟩) = true := by
  induction L generalizing Fx Fy i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b rest =>
      rw [arcsChainTo_cons_cons, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases i with
      | zero => simpa using h1
      | succ i =>
        have hi' : i + 1 < (b :: rest).length := by simpa using hi
        have := ih Fx Fy h2 i hi'
        simpa using this

theorem arcsChainTo_next_getD (L : List ArcD) (Fx Fy : Int) (h : arcsChainTo Fx Fy L = true)
    (i : ℕ) (hi : i + 1 < L.length) :
    linkStep (L.getD i dummyArc) (L.getD (i + 1) dummyArc) = true := by
  have h' := arcsChainTo_next L Fx Fy h i hi
  rw [List.getD_eq_getElem L dummyArc (n := i) (hn := by omega),
      List.getD_eq_getElem L dummyArc (n := i + 1) (hn := hi)]
  exact h'

theorem arcsChainTo_last (L : List ArcD) (Fx Fy : Int) (h : arcsChainTo Fx Fy L = true)
    (hne : L ≠ []) : arcOK (lastArc L) Fx Fy = true := by
  induction L generalizing Fx Fy with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => simpa [arcsChainTo] using h
    | cons b rest =>
      rw [arcsChainTo_cons_cons, Bool.and_eq_true] at h
      exact ih Fx Fy h.2 (List.cons_ne_nil b rest)

theorem arcsChainTo_append (L₁ L₂ : List ArcD) (Fx Fy Gx Gy : Int)
    (h₁ : arcsChainTo Fx Fy L₁ = true) (h₂ : arcsChainTo Gx Gy L₂ = true) (hne : L₂ ≠ [])
    (hl : linkStep (lastArc L₁) (headArc L₂) = true) :
    arcsChainTo Gx Gy (L₁ ++ L₂) = true := by
  cases L₂ with
  | nil => exact absurd rfl hne
  | cons c t₂ =>
    induction L₁ generalizing Fx Fy with
    | nil => simpa using h₂
    | cons a t ih =>
      cases t with
      | nil =>
        rw [List.singleton_append, arcsChainTo_cons_cons, Bool.and_eq_true]
        exact ⟨by simpa [lastArc_singleton, headArc_cons] using hl, h₂⟩
      | cons b rest =>
        rw [arcsChainTo_cons_cons, Bool.and_eq_true] at h₁
        obtain ⟨h1, h1'⟩ := h₁
        rw [List.cons_append, List.cons_append, arcsChainTo_cons_cons, Bool.and_eq_true]
        refine ⟨by simpa using h1, ?_⟩
        exact ih Fx Fy h1' (by simpa [lastArc_cons_cons] using hl)

theorem arcsOK_last (L : List ArcD) (Fx Fy : Int) (h : arcsOK Fx Fy L = true) (hne : L ≠ []) :
    arcOK (lastArc L) Fx Fy = true :=
  arcsChainTo_last L Fx Fy (arcsChainTo_of_arcsOK L Fx Fy h) hne

theorem lastArc_eq_getElem_aux (L : List ArcD) (n : ℕ) (hn : L.length = n + 1) :
    lastArc L = L.get ⟨n, by omega⟩ := by
  induction L generalizing n with
  | nil => simp at hn
  | cons a t ih =>
    cases n with
    | zero =>
      cases t with
      | nil => rfl
      | cons b t' => simp at hn
    | succ n =>
      cases t with
      | nil => simp at hn
      | cons b t' =>
        have hn' : (b :: t').length = n + 1 := by simpa using hn
        rw [lastArc_cons_cons, ih n hn', List.get_cons_succ]

/-- the last arc of a chain ends at the chain's endpoint, indexed form. -/
theorem arcsChainTo_last_getElem (L : List ArcD) (Tx Ty : Int) (n : ℕ)
    (h : arcsChainTo Tx Ty L = true) (hlen : L.length = n + 1) :
    arcOK (L.get ⟨n, by omega⟩) Tx Ty = true := by
  have hL : L ≠ [] := by intro h'; rw [h'] at hlen; simp at hlen
  rw [← lastArc_eq_getElem_aux L n hlen]
  exact arcsChainTo_last L Tx Ty h hL

theorem arcsChainTo_last_getD (L : List ArcD) (Tx Ty : Int) (n : ℕ)
    (h : arcsChainTo Tx Ty L = true) (hlen : L.length = n + 1) :
    arcOK (L.getD n dummyArc) Tx Ty = true := by
  have h' := arcsChainTo_last_getElem L Tx Ty n h hlen
  rw [List.getD_eq_getElem L dummyArc (n := n) (hn := by omega)]
  exact h'

/-! ## Building a `linkStep` from an `arcOK` -/

theorem linkStep_of_arcOK (a b : ArcD) (nx ny : Int) (h : arcOK a nx ny = true)
    (h' : (if a.k = b.k then (b.Ex, b.Ey) else (Rk a.k, 0)) = (nx, ny)) :
    linkStep a b = true := by
  by_cases hk : a.k = b.k
  · rw [if_pos hk] at h'
    simp only [Prod.mk.injEq] at h'
    rw [← h'.1, ← h'.2] at h
    rw [linkStep_same hk]
    exact h
  · rw [if_neg hk] at h'
    simp only [Prod.mk.injEq] at h'
    rw [← h'.1, ← h'.2] at h
    rw [linkStep_diff hk]
    exact h

/-! ## Unpacking `arcOK` -/

theorem arcOK_facts (a : ArcD) (nx ny : Int) (h : arcOK a nx ny = true) :
    (match a.leaves with
      | [] => false
      | l :: _ => decide (l.Ax = a.Ex) && decide (l.Ay = a.Ey)) = true ∧
    chainOK nx ny a.leaves = true ∧ gridStep a.Ex a.Ey nx ny = true ∧
    a.leaves.all (fun l => decide (l.k = a.k) && decide (l.G ≤ a.Gmax) && leafOK l) = true := by
  simp only [arcOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## The `(k,j)` labelling of a list of arcs -/

theorem kAt_of_map (L : List ArcD) (N : ℕ)
    (hmap : L.map (fun a => (a.k, a.j)) = (List.range N).map (fun i => (i / 4096, i % 4096)))
    (i : ℕ) (hi : i < L.length) :
    (L[i]).k = i / 4096 ∧ (L[i]).j = i % 4096 := by
  have hlen : L.length = N := by
    have h := congrArg List.length hmap
    simpa using h
  have h1 : (L[i]?).map (fun a => (a.k, a.j)) = some (i / 4096, i % 4096) := by
    rw [← List.getElem?_map, hmap, List.getElem?_map, List.getElem?_range (by omega : i < N),
      Option.map_some]
  have h2 : (L[i]?).map (fun a => (a.k, a.j)) = some ((L[i]).k, (L[i]).j) := by
    rw [List.getElem?_eq_getElem hi, Option.map_some]
  have h3 : ((L[i]).k, (L[i]).j) = (i / 4096, i % 4096) :=
    Option.some.inj (h2.symm.trans h1)
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-! ## Extraction of the chain steps at index `(k,j)` -/

theorem arcOK_within (F : ℕ → ArcD) (hstep : ∀ i, i + 1 < 12288 → linkStep (F i) (F (i + 1)) = true)
    (hk : ∀ i, i < 12288 → (F i).k = i / 4096)
    (k j : ℕ) (hk2 : k ≤ 2) (hj2 : j + 1 < 4096) :
    arcOK (F (4096 * k + j)) (F (4096 * k + j + 1)).Ex (F (4096 * k + j + 1)).Ey = true := by
  have h := hstep (4096 * k + j) (by omega)
  have hk1 : (F (4096 * k + j)).k = k := by
    have h1 := hk (4096 * k + j) (by omega)
    omega
  have hk2' : (F (4096 * k + j + 1)).k = k := by
    have h1 := hk (4096 * k + j + 1) (by omega)
    omega
  rw [linkStep, if_pos (by rw [hk1, hk2'])] at h
  exact h

theorem arcOK_end (F : ℕ → ArcD) (hstep : ∀ i, i + 1 < 12288 → linkStep (F i) (F (i + 1)) = true)
    (hk : ∀ i, i < 12288 → (F i).k = i / 4096)
    (hlast : arcOK (F 12287) (Rk 2) 0 = true)
    (k : ℕ) (hk2 : k ≤ 2) :
    arcOK (F (4096 * k + 4095)) (Rk k) 0 = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · have h := hstep 4095 (by omega)
    have hk0 : (F 4095).k = 0 := by
      have h1 := hk 4095 (by omega)
      omega
    have hk1 : (F 4096).k = 1 := by
      have h1 := hk 4096 (by omega)
      omega
    rw [linkStep, if_neg (by rw [hk0, hk1]; norm_num), hk0] at h
    exact h
  · have h := hstep 8191 (by omega)
    have hk1 : (F 8191).k = 1 := by
      have h1 := hk 8191 (by omega)
      omega
    have hk2' : (F 8192).k = 2 := by
      have h1 := hk 8192 (by omega)
      omega
    rw [linkStep, if_neg (by rw [hk1, hk2']; norm_num), hk1] at h
    exact h
  · exact hlast

theorem lastArc_append : ∀ (L₁ : List ArcD) (L₂ : List ArcD), L₂ ≠ [] →
    lastArc (L₁ ++ L₂) = lastArc L₂ := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ _; rfl
  | cons a t ih =>
    intro L₂ h
    cases t with
    | nil =>
      cases L₂ with
      | nil => exact absurd rfl h
      | cons c t₂ => rfl
    | cons b t' =>
      rw [List.cons_append, List.cons_append, lastArc_cons_cons]
      exact ih L₂ h

/-! ## `Finset.range` double sum versus `DsumFin` -/

theorem sum_range_eq_DsumFin (l : List (ℤ × ℤ)) (w f : ℕ → ℤ)
    (h1 : ∀ (i : ℕ) (hi : i < l.length), (l.get ⟨i, hi⟩).1 = f i)
    (h2 : ∀ (i : ℕ) (hi : i < l.length), (l.get ⟨i, hi⟩).2 = w i) :
    (∑ a ∈ Finset.range l.length, ∑ b ∈ Finset.range l.length, w a * w b * max (f a) (f b))
      = DsumFin l := by
  have hterm : ∀ (a b : Fin l.length),
      (l.get a).2 * (l.get b).2 * max (l.get a).1 (l.get b).1 = w a * w b * max (f a) (f b) := by
    intro a b
    rw [h1 a a.isLt, h2 a a.isLt, h1 b b.isLt, h2 b b.isLt]
  simp only [DsumFin]
  have hL : (∑ a : Fin l.length, ∑ b : Fin l.length,
        (l.get a).2 * (l.get b).2 * max (l.get a).1 (l.get b).1)
      = ∑ a : Fin l.length, ∑ b : Fin l.length, w a * w b * max (f a) (f b) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))
  rw [hL]
  rw [Fin.sum_univ_eq_sum_range
    (fun a => ∑ b : Fin l.length, w a * w b * max (f a) (f b)) l.length]
  exact Finset.sum_congr rfl (fun a _ =>
    (Fin.sum_univ_eq_sum_range (fun b => w a * w b * max (f a) (f b)) l.length).symm)

end Work.Cert.CJ2
