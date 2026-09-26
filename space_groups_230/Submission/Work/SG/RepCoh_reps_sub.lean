import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_span_alg
import Submission.Work.SG.RepCoh_orbit

/-!
# `reps` is closed under subtracting `H`-columns, modulo the `Bl`-lattice

This file proves `Work.SG.RepCoh_reps_sub`: for every cohomology representative index `h`
and every column `c` of the echelon basis `H`, there is another representative index `h'`
with `reps h - H c - reps h' ∈ span (BlR Bl)`.

The mathematical content: let `L = N3 j`, `A = reps.getD h []`, `B = H.getD c []`, and let
`F k = (add k c)` be the "add the `c`-th `H`-column" map on representative indices, so that
`reduceBl Bl (X + B) = reps (F X)` for every representative `X` (certificate fact
`RC.Cd_add_red`).  Since the coordinate space below `L` is a `ℤ`-span (closed under finite
combinations), the relation `X + B ≡ F X` (modulo `span (BlR Bl)`) telescopes:

  `A + k·B ≡ reps (F^[k] h)`   for every `k`,

by induction, the induction step being exactly `hspan` applied to `reps (F^[k] h) + B`
together with `RC.Cd_add_red`.  Now `F` is a self-map of the finite type
`Fin (reps.length)`, so by the pigeonhole principle (`RepCoh_orbit`) two iterates coincide:
`F^[a] h = F^[b] h` for some `a < b`.  Subtracting the two telescoped relations gives
`(a - b)·B ≡ 0`, and hence

  `A - B ≡ A + (b - a - 1)·B ≡ reps (F^[b - a - 1] h)`,

which is the desired statement with `h' = (F^[b - a - 1] h).val`.

All the coordinate bookkeeping is isolated in the private `getD` lemmas `c1`, `c2`, `c3`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- `h`-th representative vector of class `j`. -/
private def repA (j : Fin 73) (h : ℕ) : List ℤ := (Work.SG.RC.Cd j).reps.getD h []

/-- `c`-th column of the echelon basis `H` of class `j`. -/
private def repB (j : Fin 73) (c : ℕ) : List ℤ := (Work.SG.RC.Cd j).H.getD c []

/-! ## Coordinate computations for the flat vector operations -/

private theorem t_vadd_getD {x y : List ℤ} {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (Work.SG.RC.vadd x y).getD q 0 = x.getD q 0 + y.getD q 0 := by
  show (List.zipWith (fun a b => a + b) x y).getD q 0 = _
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]

private theorem t_vsub_getD {x y : List ℤ} {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (Work.SG.RC.vsub x y).getD q 0 = x.getD q 0 - y.getD q 0 := by
  show (List.zipWith (fun a b => a - b) x y).getD q 0 = _
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]

private theorem t_vz_getD {x : List ℤ} (k : ℤ) {q : ℕ} (hx : q < x.length) :
    (Work.SG.RC.vz k x).getD q 0 = k * x.getD q 0 := by
  show (List.map (fun a => k * a) x).getD q 0 = _
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hx), List.getElem_map,
    List.getD_eq_getElem _ _ hx]

private theorem t_vadd_len (x y : List ℤ) :
    (Work.SG.RC.vadd x y).length = min x.length y.length := by
  show (List.zipWith (fun a b => a + b) x y).length = _
  rw [List.length_zipWith]

private theorem t_vsub_len (x y : List ℤ) :
    (Work.SG.RC.vsub x y).length = min x.length y.length := by
  show (List.zipWith (fun a b => a - b) x y).length = _
  rw [List.length_zipWith]

private theorem t_vz_len (k : ℤ) (x : List ℤ) :
    (Work.SG.RC.vz k x).length = x.length := by
  show (List.map (fun a => k * a) x).length = _
  rw [List.length_map]

private theorem c1 {A B X : List ℤ} {L q : ℕ} {k : ℤ}
    (hA : A.length = L) (hB : B.length = L) (hX : X.length = L) (hq : q < L) :
    (Work.SG.RC.vsub (Work.SG.RC.vadd A (Work.SG.RC.vz k B)) X).getD q 0
      = A.getD q 0 + k * B.getD q 0 - X.getD q 0 := by
  have h1 : q < (Work.SG.RC.vadd A (Work.SG.RC.vz k B)).length := by
    rw [t_vadd_len, t_vz_len, hA, hB, min_self]; exact hq
  rw [t_vsub_getD h1 (by rw [hX]; exact hq),
      t_vadd_getD (by rw [hA]; exact hq) (by rw [t_vz_len, hB]; exact hq),
      t_vz_getD k (by rw [hB]; exact hq)]

private theorem c2 {X B Y : List ℤ} {L q : ℕ}
    (hX : X.length = L) (hB : B.length = L) (hY : Y.length = L) (hq : q < L) :
    (Work.SG.RC.vsub (Work.SG.RC.vadd X B) Y).getD q 0
      = X.getD q 0 + B.getD q 0 - Y.getD q 0 := by
  have h1 : q < (Work.SG.RC.vadd X B).length := by rw [t_vadd_len, hX, hB, min_self]; exact hq
  rw [t_vsub_getD h1 (by rw [hY]; exact hq),
      t_vadd_getD (by rw [hX]; exact hq) (by rw [hB]; exact hq)]

private theorem c3 {A B Y : List ℤ} {L q : ℕ}
    (hA : A.length = L) (hB : B.length = L) (hY : Y.length = L) (hq : q < L) :
    (Work.SG.RC.vsub (Work.SG.RC.vsub A B) Y).getD q 0
      = A.getD q 0 - B.getD q 0 - Y.getD q 0 := by
  have h1 : q < (Work.SG.RC.vsub A B).length := by rw [t_vsub_len, hA, hB, min_self]; exact hq
  rw [t_vsub_getD h1 (by rw [hY]; exact hq),
      t_vsub_getD (by rw [hA]; exact hq) (by rw [hB]; exact hq)]

/-! ## The closure facts for `RC.InSpan`, extracted from the certified span algebra -/

private theorem span_zero :
    (∀ (rows : List (List ℤ)) (N : ℕ) (v : List ℤ),
        (∀ q, q < N → v.getD q 0 = 0) → Work.SG.RC.InSpan rows N v) :=
  RepCoh_span_alg.1

private theorem span_add :
    (∀ (rows : List (List ℤ)) (N : ℕ) (u v w : List ℤ),
        Work.SG.RC.InSpan rows N u → Work.SG.RC.InSpan rows N v →
          (∀ q, q < N → w.getD q 0 = u.getD q 0 + v.getD q 0) →
            Work.SG.RC.InSpan rows N w) :=
  RepCoh_span_alg.2.2.1

private theorem span_sub :
    (∀ (rows : List (List ℤ)) (N : ℕ) (u v w : List ℤ),
        Work.SG.RC.InSpan rows N u → Work.SG.RC.InSpan rows N v →
          (∀ q, q < N → w.getD q 0 = u.getD q 0 - v.getD q 0) →
            Work.SG.RC.InSpan rows N w) :=
  RepCoh_span_alg.2.2.2.1

theorem RepCoh_reps_sub (j : Fin 73)
    (hred : ∀ {x y : List ℤ}, x.length = Work.SG.RC.N3 j → y.length = Work.SG.RC.N3 j →
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) (Work.SG.RC.vsub x y) →
        Data.reduceBl (Work.SG.RC.Cd j).Bl x = Data.reduceBl (Work.SG.RC.Cd j).Bl y)
    (hspan : ∀ x : List ℤ, x.length = Work.SG.RC.N3 j →
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j)
        (Work.SG.RC.vsub x (Data.reduceBl (Work.SG.RC.Cd j).Bl x))) :
    ∀ h, h < (Work.SG.RC.Cd j).reps.length → ∀ c, c < Work.SG.RC.N3 j →
      ∃ h', h' < (Work.SG.RC.Cd j).reps.length ∧
        Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j)
          (Work.SG.RC.vsub (Work.SG.RC.vsub ((Work.SG.RC.Cd j).reps.getD h []) ((Work.SG.RC.Cd j).H.getD c []))
            ((Work.SG.RC.Cd j).reps.getD h' [])) := by
  intro h hh c hc
  -- reformulate the goal in terms of the abbreviations `repA`, `repB`
  change ∃ h', h' < (Work.SG.RC.Cd j).reps.length ∧
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j)
        (Work.SG.RC.vsub (Work.SG.RC.vsub (repA j h) (repB j c))
          ((Work.SG.RC.Cd j).reps.getD h' []))
  -- lengths of the two fixed vectors
  have hA : (repA j h).length = Work.SG.RC.N3 j := by
    show ((Work.SG.RC.Cd j).reps.getD h []).length = Work.SG.RC.N3 j
    rw [List.getD_eq_getElem _ _ hh]
    exact (Work.SG.RC.Cd_reps_red j _ (List.getElem_mem hh)).1
  have hB : (repB j c).length = Work.SG.RC.N3 j := by
    show ((Work.SG.RC.Cd j).H.getD c []).length = Work.SG.RC.N3 j
    exact Work.SG.RC.Cd_H_rowlen j c hc
  -- the "add the `c`-th `H`-column" self-map on representative indices
  let F : Fin (Work.SG.RC.Cd j).reps.length → Fin (Work.SG.RC.Cd j).reps.length :=
    fun k => ⟨((Work.SG.RC.Cd j).add.getD k.val []).getD c 0,
      Work.SG.RC.Cd_add_bound j k.val k.isLt c hc⟩
  let h0 : Fin (Work.SG.RC.Cd j).reps.length := ⟨h, hh⟩
  have hRlen : ∀ k : ℕ,
      ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val []).length = Work.SG.RC.N3 j := by
    intro k
    have h1 : (F^[k] h0).val < (Work.SG.RC.Cd j).reps.length := (F^[k] h0).isLt
    rw [List.getD_eq_getElem _ _ h1]
    exact (Work.SG.RC.Cd_reps_red j _ (List.getElem_mem h1)).1
  -- the telescoping relation `A + k·B ≡ reps (F^[k] h)`
  have hiter : ∀ k : ℕ, Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl)
      (Work.SG.RC.N3 j)
      (Work.SG.RC.vsub (Work.SG.RC.vadd (repA j h) (Work.SG.RC.vz (k : ℤ) (repB j c)))
        ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val [])) := by
    intro k
    induction k with
    | zero =>
      have hR0 : (Work.SG.RC.Cd j).reps.getD (F^[0] h0).val [] = repA j h := by
        rw [Function.iterate_zero_apply]
        rfl
      rw [hR0]
      refine span_zero _ _ _ (fun q hq => ?_)
      rw [c1 hA hB hA hq]
      ring
    | succ k ih =>
      -- adding `B` to the `k`-th representative moves to the `(k+1)`-st one
      have hstep : Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl)
          (Work.SG.RC.N3 j)
          (Work.SG.RC.vsub
            (Work.SG.RC.vadd ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val []) (repB j c))
            ((Work.SG.RC.Cd j).reps.getD (F^[k.succ] h0).val [])) := by
        have hx : (Work.SG.RC.vadd ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val [])
            (repB j c)).length = Work.SG.RC.N3 j := by
          rw [t_vadd_len, hRlen k, hB, min_self]
        have hs := hspan (Work.SG.RC.vadd ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val [])
          (repB j c)) hx
        have hred2 : Data.reduceBl (Work.SG.RC.Cd j).Bl
            (Work.SG.RC.vadd ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val []) (repB j c))
            = (Work.SG.RC.Cd j).reps.getD (F^[k.succ] h0).val [] := by
          have h4 : (F^[k.succ] h0).val
              = ((Work.SG.RC.Cd j).add.getD (F^[k] h0).val []).getD c 0 := by
            rw [Function.iterate_succ_apply']
          rw [h4]
          exact Work.SG.RC.Cd_add_red j (F^[k] h0).val (F^[k] h0).isLt c hc
        rw [hred2] at hs
        exact hs
      have hcoord : ∀ q, q < Work.SG.RC.N3 j →
          (Work.SG.RC.vsub (Work.SG.RC.vadd (repA j h) (Work.SG.RC.vz ((k : ℤ) + 1) (repB j c)))
              ((Work.SG.RC.Cd j).reps.getD (F^[k.succ] h0).val [])).getD q 0
            = (Work.SG.RC.vsub (Work.SG.RC.vadd (repA j h) (Work.SG.RC.vz (k : ℤ) (repB j c)))
                ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val [])).getD q 0
              + (Work.SG.RC.vsub
                  (Work.SG.RC.vadd ((Work.SG.RC.Cd j).reps.getD (F^[k] h0).val []) (repB j c))
                  ((Work.SG.RC.Cd j).reps.getD (F^[k.succ] h0).val [])).getD q 0 := by
        intro q hq
        rw [c1 hA hB (hRlen _) hq, c1 hA hB (hRlen k) hq, c2 (hRlen k) hB (hRlen _) hq]
        ring
      exact span_add _ _ _ _ _ ih hstep hcoord
  -- pigeonhole: two iterates of `F` on the orbit of `h` coincide
  obtain ⟨a, b, hab, hFab⟩ := RepCoh_orbit F h0
  have hRR : (Work.SG.RC.Cd j).reps.getD (F^[a] h0).val []
      = (Work.SG.RC.Cd j).reps.getD (F^[b] h0).val [] := by
    rw [hFab]
  -- hence `(a - b)·B` lies in the span
  have hdiff : Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl)
      (Work.SG.RC.N3 j) (Work.SG.RC.vz ((a : ℤ) - b) (repB j c)) := by
    refine span_sub _ _ _ _ _ (hiter a) (hiter b) (fun q hq => ?_)
    rw [t_vz_getD _ (by rw [hB]; exact hq), c1 hA hB (hRlen a) hq,
      c1 hA hB (hRlen b) hq, hRR]
    ring
  -- conclude with `h' = F^[b - a - 1] h`
  refine ⟨(F^[b - a - 1] h0).val, (F^[b - a - 1] h0).isLt, ?_⟩
  refine span_add _ _ _ _ _ (hiter (b - a - 1)) hdiff (fun q hq => ?_)
  have hcast : ((b - a - 1 : ℕ) : ℤ) = (b : ℤ) - (a : ℤ) - 1 := by omega
  rw [c3 hA hB (hRlen _) hq, c1 hA hB (hRlen _) hq,
    t_vz_getD _ (by rw [hB]; exact hq), hcast]
  ring

end Work.SG
