import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_redspan
import Submission.Work.SG.RepCoh_ndvd
import Submission.Work.SG.RepCoh_reps_sub

/-!
# `Work.SG.RepCoh_reps`: the `H¹` representatives cover every solution class

Given `y` with `y ≡ H t (mod n)` coordinatewise, one must find a listed representative
`reps[h]` with `y ≡ reps[h]` modulo the coboundary lattice `Bl = span(BlR Bl)`.

The proof is a `Good`-predicate induction (`Good v` = "`v` is congruent mod `Bl` to a listed
representative"): `Good 0` holds; `Good v → Good (v + H_c)` (from the certificate
`reduceBl (reps[h] + H[c]) = reps[add h c]` and the reduction lies in the span);
`Good v → Good (v - H_c)` (a fibre/cardinality argument: the map `h ↦ add h c` is a bijection on
the finite set of reduction classes); hence `Good (Σ_c t_c H_c) = Good (H t)` for arbitrary
integer `t`, and `y` differs from `H t` by a multiple of `n` in each coordinate, hence by an
element of `Bl`.
-/

namespace Work.SG

namespace RepsAux

/-! ### List plumbing -/

variable {L : ℕ}

theorem zw_getD {f : ℤ → ℤ → ℤ} {u v : List ℤ} (hu : u.length = L) (hv : v.length = L)
    {q : ℕ} (hq : q < L) :
    (List.zipWith f u v).getD q 0 = f (u.getD q 0) (v.getD q 0) := by
  have hlen : (List.zipWith f u v).length = L := by rw [List.length_zipWith, hu, hv, min_self]
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hq),
      List.getD_eq_getElem _ _ (by rw [hu]; exact hq),
      List.getD_eq_getElem _ _ (by rw [hv]; exact hq)]
  exact List.getElem_zipWith

theorem map_getD_of_lt (f : ℤ → ℤ) (u : List ℤ) {q : ℕ} (hq : q < u.length) :
    (u.map f).getD q 0 = f (u.getD q 0) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hq,
    List.getElem_map]

theorem getD_range_map (f : ℕ → ℤ) {n c : ℕ} (hc : c < n) :
    ((List.range n).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hc),
    List.getElem_map, List.getElem_range]

theorem vadd_getD {u v : List ℤ} (hu : u.length = L) (hv : v.length = L) {q : ℕ} (hq : q < L) :
    (RC.vadd u v).getD q 0 = u.getD q 0 + v.getD q 0 := zw_getD hu hv hq

theorem vsub_getD {u v : List ℤ} (hu : u.length = L) (hv : v.length = L) {q : ℕ} (hq : q < L) :
    (RC.vsub u v).getD q 0 = u.getD q 0 - v.getD q 0 := zw_getD hu hv hq

theorem vz_getD (k : ℤ) (u : List ℤ) (q : ℕ) :
    (RC.vz k u).getD q 0 = k * u.getD q 0 := by
  have h := List.getD_map u (0 : ℤ) (n := q) (f := fun a => k * a)
  simpa [RC.vz] using h

theorem vadd_len (u v : List ℤ) : (RC.vadd u v).length = min u.length v.length := by
  simp [RC.vadd, List.length_zipWith]

theorem vsub_len (u v : List ℤ) : (RC.vsub u v).length = min u.length v.length := by
  simp [RC.vsub, List.length_zipWith]

theorem vz_len (k : ℤ) (u : List ℤ) : (RC.vz k u).length = u.length := by
  simp [RC.vz]

theorem vzero_len (N : ℕ) : (RC.vzero N).length = N := by simp [RC.vzero]

theorem vzero_getD {N q : ℕ} (hq : q < N) : (RC.vzero N).getD q 0 = 0 := by
  simp [RC.vzero, List.getD_replicate, hq]

/-! ### `linC` bookkeeping -/

def padC (rows : List (List ℤ)) (cs : List ℤ) : List ℤ :=
  (List.range rows.length).map (fun c => cs.getD c 0)

theorem padC_len (rows : List (List ℤ)) (cs : List ℤ) : (padC rows cs).length = rows.length := by
  simp [padC]

theorem padC_getD (rows : List (List ℤ)) (cs : List ℤ) {c : ℕ} (hc : c < rows.length) :
    (padC rows cs).getD c 0 = cs.getD c 0 := by
  simp only [padC]
  exact getD_range_map _ hc

theorem linC_range_map (rows : List (List ℤ)) (f : ℕ → ℤ) (q : ℕ) :
    RC.linC rows ((List.range rows.length).map f) q
      = (List.map (fun c => f c * (rows.getD c []).getD q 0)
          (List.range rows.length)).sum := by
  simp only [RC.linC]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  rw [getD_range_map f (List.mem_range.mp hc)]

theorem linC_range_getD (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ) :
    RC.linC rows ((List.range rows.length).map (fun c => cs.getD c 0)) q = RC.linC rows cs q := by
  rw [linC_range_map]
  simp only [RC.linC]

theorem linC_add_aux (rows : List (List ℤ)) (f g : ℕ → ℤ) (q : ℕ) :
    RC.linC rows ((List.range rows.length).map (fun c => f c + g c)) q
      = RC.linC rows ((List.range rows.length).map f) q
        + RC.linC rows ((List.range rows.length).map g) q := by
  rw [linC_range_map, linC_range_map, linC_range_map]
  rw [show (List.map (fun c => (f c + g c) * (rows.getD c []).getD q 0)
        (List.range rows.length))
      = (List.map (fun c => f c * (rows.getD c []).getD q 0
            + g c * (rows.getD c []).getD q 0) (List.range rows.length)) from by
        apply List.map_congr_left
        intro c _
        ring]
  rw [List.sum_map_add]

theorem linC_smul_aux (rows : List (List ℤ)) (f : ℕ → ℤ) (k : ℤ) (q : ℕ) :
    RC.linC rows ((List.range rows.length).map (fun c => k * f c)) q
      = k * RC.linC rows ((List.range rows.length).map f) q := by
  rw [linC_range_map, linC_range_map]
  rw [show (List.map (fun c => k * f c * (rows.getD c []).getD q 0)
        (List.range rows.length))
      = (List.map (fun c => k * (f c * (rows.getD c []).getD q 0))
          (List.range rows.length)) from by
        apply List.map_congr_left
        intro c _
        ring]
  rw [List.sum_map_mul_left]

/-! ### Closure of `InSpan` -/

theorem InSpan_congr {rows : List (List ℤ)} {N : ℕ} {u v : List ℤ}
    (h : RC.InSpan rows N u) (huv : ∀ q < N, v.getD q 0 = u.getD q 0) :
    RC.InSpan rows N v := by
  obtain ⟨cs, hcs⟩ := h
  exact ⟨cs, fun q hq => by rw [huv q hq, hcs q hq]⟩

theorem InSpan_vzero (rows : List (List ℤ)) (N : ℕ) : RC.InSpan rows N (RC.vzero N) := by
  refine ⟨[], ?_⟩
  intro q hq
  rw [vzero_getD hq]
  simp [RC.linC]

theorem InSpan_add {rows : List (List ℤ)} {N : ℕ} {u v : List ℤ} (hu : u.length = N)
    (hv : v.length = N) (hu' : RC.InSpan rows N u) (hv' : RC.InSpan rows N v) :
    RC.InSpan rows N (RC.vadd u v) := by
  obtain ⟨cs, hcs⟩ := hu'
  obtain ⟨ds, hds⟩ := hv'
  refine ⟨(List.range rows.length).map (fun c => cs.getD c 0 + ds.getD c 0), ?_⟩
  intro q hq
  rw [vadd_getD hu hv hq, hcs q hq, hds q hq, linC_add_aux]
  rw [linC_range_getD, linC_range_getD]

theorem InSpan_smul {rows : List (List ℤ)} {N : ℕ} {u : List ℤ} (hu : u.length = N) (k : ℤ)
    (hu' : RC.InSpan rows N u) : RC.InSpan rows N (RC.vz k u) := by
  obtain ⟨cs, hcs⟩ := hu'
  refine ⟨(List.range rows.length).map (fun c => k * cs.getD c 0), ?_⟩
  intro q hq
  rw [vz_getD, hcs q hq]
  rw [← linC_range_getD rows cs q, ← linC_smul_aux rows (fun c => cs.getD c 0) k q]

theorem InSpan_sub {rows : List (List ℤ)} {N : ℕ} {u v : List ℤ} (hu : u.length = N)
    (hv : v.length = N) (hu' : RC.InSpan rows N u) (hv' : RC.InSpan rows N v) :
    RC.InSpan rows N (RC.vsub u v) := by
  have h1 : RC.InSpan rows N (RC.vadd u (RC.vz (-1) v)) :=
    InSpan_add hu (by rw [vz_len]; exact hv) hu' (InSpan_smul hv (-1) hv')
  refine InSpan_congr h1 ?_
  intro q hq
  rw [vsub_getD hu hv hq, vadd_getD hu (by rw [vz_len]; exact hv) hq, vz_getD]
  ring

/-! ### The `H`-combination vectors -/

theorem reps_getD_len (j : Fin 73) {h : ℕ} (hh : h < (RC.Cd j).reps.length) :
    ((RC.Cd j).reps.getD h []).length = RC.N3 j := by
  rw [List.getD_eq_getElem _ _ hh]
  exact (RC.Cd_reps_red j _ (List.getElem_mem hh)).1

def hvec (j : Fin 73) (t : List ℤ) : List ℤ :=
  (List.range (RC.N3 j)).map (fun q => RC.linC (RC.Cd j).H t q)

theorem hvec_len (j : Fin 73) (t : List ℤ) : (hvec j t).length = RC.N3 j := by
  simp [hvec]

theorem hvec_getD (j : Fin 73) (t : List ℤ) {q : ℕ} (hq : q < RC.N3 j) :
    (hvec j t).getD q 0 = RC.linC (RC.Cd j).H t q := by
  simp only [hvec]
  exact getD_range_map _ hq

def partH (j : Fin 73) (t : List ℤ) (c : ℕ) : List ℤ :=
  (List.range (RC.N3 j)).map
    (fun q => (List.map (fun k => t.getD k 0 * ((RC.Cd j).H.getD k []).getD q 0)
      (List.range c)).sum)

theorem partH_len (j : Fin 73) (t : List ℤ) (c : ℕ) : (partH j t c).length = RC.N3 j := by
  simp [partH]

theorem partH_getD (j : Fin 73) (t : List ℤ) (c : ℕ) {q : ℕ} (hq : q < RC.N3 j) :
    (partH j t c).getD q 0
      = (List.map (fun k => t.getD k 0 * ((RC.Cd j).H.getD k []).getD q 0)
          (List.range c)).sum := by
  simp only [partH]
  exact getD_range_map _ hq

theorem partH_succ (j : Fin 73) (t : List ℤ) (c : ℕ) {q : ℕ} (hq : q < RC.N3 j) :
    (partH j t (c + 1)).getD q 0
      = (partH j t c).getD q 0 + t.getD c 0 * ((RC.Cd j).H.getD c []).getD q 0 := by
  rw [partH_getD j t (c + 1) hq, partH_getD j t c hq, List.sum_range_succ]

theorem partH_succ_vadd (j : Fin 73) (t : List ℤ) {c : ℕ} (hc : c < RC.N3 j) :
    ∀ q < RC.N3 j,
      (partH j t (c + 1)).getD q 0
        = (RC.vadd (partH j t c) (RC.vz (t.getD c 0) ((RC.Cd j).H.getD c []))).getD q 0 := by
  intro q hq
  rw [partH_succ j t c hq,
    vadd_getD (partH_len j t c) (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD]

theorem hvec_partH (j : Fin 73) (t : List ℤ) :
    ∀ q < RC.N3 j, (hvec j t).getD q 0 = (partH j t (RC.N3 j)).getD q 0 := by
  intro q hq
  rw [hvec_getD j t hq, partH_getD j t (RC.N3 j) hq]
  simp only [RC.linC]
  rw [RC.Cd_H_len j]

/-! ### The predicate `Good` -/

def Good (j : Fin 73) (v : List ℤ) : Prop :=
  v.length = RC.N3 j ∧
    ∃ h, h < (RC.Cd j).reps.length ∧
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub v ((RC.Cd j).reps.getD h []))

theorem Good_congr {j : Fin 73} {v v' : List ℤ} (hv : Good j v) (hlen : v'.length = RC.N3 j)
    (h : ∀ q < RC.N3 j, v'.getD q 0 = v.getD q 0) : Good j v' := by
  obtain ⟨hvlen, h', hh', hInv⟩ := hv
  refine ⟨hlen, h', hh', InSpan_congr hInv ?_⟩
  intro q hq
  rw [vsub_getD hlen (reps_getD_len j hh') hq,
    vsub_getD hvlen (reps_getD_len j hh') hq, h q hq]

theorem Good_vzero (j : Fin 73) : Good j (RC.vzero (RC.N3 j)) := by
  rcases List.head?_eq_some_iff.mp (RC.Cd_reps_head j) with ⟨tl, htl⟩
  have hlen : 0 < (RC.Cd j).reps.length := by rw [htl]; simp
  have h0 : (RC.Cd j).reps.getD 0 [] = List.replicate (RC.N3 j) 0 := by
    rw [htl, List.getD_cons_zero]
  refine ⟨vzero_len _, 0, hlen, ?_⟩
  refine InSpan_congr (InSpan_vzero (RC.BlR (RC.Cd j).Bl) (RC.N3 j)) ?_
  intro q hq
  rw [vsub_getD (vzero_len _) (by rw [h0]; exact List.length_replicate) hq,
    vzero_getD hq, h0, List.getD_replicate 0 hq]
  ring

theorem Good_of_span (j : Fin 73) {v u : List ℤ}
    (hspan : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub v u)) (hu : Good j u)
    (hlen : v.length = RC.N3 j) : Good j v := by
  obtain ⟨hulen, h, hh, hInv⟩ := hu
  have hrep := reps_getD_len j hh
  refine ⟨hlen, h, hh, ?_⟩
  have h3 : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
      (RC.vadd (RC.vsub v u) (RC.vsub u ((RC.Cd j).reps.getD h []))) :=
    InSpan_add (by rw [vsub_len, hlen, hulen, min_self])
      (by rw [vsub_len, hulen, hrep, min_self]) hspan hInv
  refine InSpan_congr h3 ?_
  intro q hq
  rw [vsub_getD hlen hrep hq,
    vadd_getD (by rw [vsub_len, hlen, hulen, min_self])
      (by rw [vsub_len, hulen, hrep, min_self]) hq,
    vsub_getD hlen hulen hq, vsub_getD hulen hrep hq]
  ring

theorem Good_add_H (j : Fin 73)
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    {v : List ℤ} (hv : Good j v) {c : ℕ} (hc : c < RC.N3 j) :
    Good j (RC.vadd v ((RC.Cd j).H.getD c [])) := by
  obtain ⟨hvlen, h, hh, hInv⟩ := hv
  have hrow := RC.Cd_H_rowlen j c hc
  have hrep := reps_getD_len j hh
  have hvadd : (RC.vadd ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c [])).length = RC.N3 j := by
    rw [vadd_len, hrep, hrow, min_self]
  have h2 : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
      (RC.vsub (RC.vadd ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
        ((RC.Cd j).reps.getD (((RC.Cd j).add.getD h []).getD c 0) [])) := by
    have h0 := hspan (RC.vadd ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c [])) hvadd
    rw [show Data.reduceBl (RC.Cd j).Bl (RC.vadd ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
        = ((RC.Cd j).reps.getD (((RC.Cd j).add.getD h []).getD c 0) []) from
      RC.Cd_add_red j h hh c hc] at h0
    exact h0
  have hA : ((RC.Cd j).add.getD h []).getD c 0 < (RC.Cd j).reps.length :=
    RC.Cd_add_bound j h hh c hc
  refine ⟨by rw [vadd_len, hvlen, hrow, min_self], (((RC.Cd j).add.getD h []).getD c 0), hA, ?_⟩
  have h3 : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
      (RC.vadd (RC.vsub v ((RC.Cd j).reps.getD h []))
        (RC.vsub (RC.vadd ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
          ((RC.Cd j).reps.getD (((RC.Cd j).add.getD h []).getD c 0) []))) :=
    InSpan_add (by rw [vsub_len, hvlen, hrep, min_self])
      (by rw [vsub_len, hvadd, reps_getD_len j hA, min_self]) hInv h2
  refine InSpan_congr h3 ?_
  intro q hq
  rw [vsub_getD (by rw [vadd_len, hvlen, hrow, min_self]) (reps_getD_len j hA) hq,
    vadd_getD hvlen hrow hq,
    vadd_getD (by rw [vsub_len, hvlen, hrep, min_self])
      (by rw [vsub_len, hvadd, reps_getD_len j hA, min_self]) hq,
    vsub_getD hvlen hrep hq,
    vsub_getD hvadd (reps_getD_len j hA) hq, vadd_getD hrep hrow hq]
  ring

theorem Good_sub_H (j : Fin 73) {c : ℕ}
    (hsub : ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    {v : List ℤ} (hv : Good j v) (hc : c < RC.N3 j) :
    Good j (RC.vsub v ((RC.Cd j).H.getD c [])) := by
  obtain ⟨hvlen, h, hh, hInv⟩ := hv
  obtain ⟨h', hh', hInv'⟩ := hsub h hh
  have hrow := RC.Cd_H_rowlen j c hc
  have hrep := reps_getD_len j hh
  have hrep' := reps_getD_len j hh'
  have hinner : (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c [])).length = RC.N3 j := by
    rw [vsub_len, hrep, hrow, min_self]
  refine ⟨by rw [vsub_len, hvlen, hrow, min_self], h', hh', ?_⟩
  have h3 : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
      (RC.vadd (RC.vsub v ((RC.Cd j).reps.getD h []))
        (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
          ((RC.Cd j).reps.getD h' []))) :=
    InSpan_add (by rw [vsub_len, hvlen, hrep, min_self])
      (by rw [vsub_len, hinner, hrep', min_self]) hInv hInv'
  refine InSpan_congr h3 ?_
  intro q hq
  rw [vsub_getD (by rw [vsub_len, hvlen, hrow, min_self]) hrep' hq,
    vsub_getD hvlen hrow hq,
    vadd_getD (by rw [vsub_len, hvlen, hrep, min_self])
      (by rw [vsub_len, hinner, hrep', min_self]) hq,
    vsub_getD hvlen hrep hq, vsub_getD hinner hrep' hq, vsub_getD hrep hrow hq]
  ring

theorem Good_add_vz_nat (j : Fin 73)
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    (hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    {v : List ℤ} (hv : Good j v) {c : ℕ} (hc : c < RC.N3 j) :
    ∀ n : ℕ, Good j (RC.vadd v (RC.vz (n : ℤ) ((RC.Cd j).H.getD c []))) := by
  intro n
  induction n with
  | zero =>
      refine Good_congr hv (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self]) ?_
      intro q hq
      rw [vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD]
      ring
  | succ n ih =>
      have h1 := Good_add_H j hspan ih hc
      have hmid : (RC.vadd (RC.vadd v (RC.vz (n : ℤ) ((RC.Cd j).H.getD c [])))
          ((RC.Cd j).H.getD c [])).length = RC.N3 j := by
        rw [vadd_len, ih.1, RC.Cd_H_rowlen j c hc, min_self]
      refine Good_congr h1 (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self]) ?_
      intro q hq
      rw [vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD,
        vadd_getD (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self])
          (RC.Cd_H_rowlen j c hc) hq,
        vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD]
      push_cast
      ring

theorem Good_add_vz_neg (j : Fin 73)
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    (hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    {v : List ℤ} (hv : Good j v) {c : ℕ} (hc : c < RC.N3 j) :
    ∀ n : ℕ, Good j (RC.vadd v (RC.vz (-(n : ℤ)) ((RC.Cd j).H.getD c []))) := by
  intro n
  induction n with
  | zero =>
      refine Good_congr hv (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self]) ?_
      intro q hq
      rw [vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD]
      ring
  | succ n ih =>
      have h1 := Good_sub_H j (hsub c hc) ih hc
      have hmid : (RC.vsub (RC.vadd v (RC.vz (-(n : ℤ)) ((RC.Cd j).H.getD c [])))
          ((RC.Cd j).H.getD c [])).length = RC.N3 j := by
        rw [vsub_len, ih.1, RC.Cd_H_rowlen j c hc, min_self]
      refine Good_congr h1 (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self]) ?_
      intro q hq
      rw [vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD,
        vsub_getD (by rw [vadd_len, hv.1, vz_len, RC.Cd_H_rowlen j c hc, min_self])
          (RC.Cd_H_rowlen j c hc) hq,
        vadd_getD hv.1 (by rw [vz_len, RC.Cd_H_rowlen j c hc]) hq, vz_getD]
      push_cast
      ring

theorem Good_add_vz (j : Fin 73)
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    (hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    {v : List ℤ} (hv : Good j v) (k : ℤ) {c : ℕ} (hc : c < RC.N3 j) :
    Good j (RC.vadd v (RC.vz k ((RC.Cd j).H.getD c []))) := by
  rcases lt_or_ge 0 k with hk | hk
  · have hk1 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk)
    rw [← hk1]
    exact Good_add_vz_nat j hspan hsub hv hc k.toNat
  · have hpos : 0 ≤ -k := by omega
    have hk1 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg hpos
    have hk2 : k = -(((-k).toNat : ℕ) : ℤ) := by rw [hk1]; ring
    rw [hk2]
    exact Good_add_vz_neg j hspan hsub hv hc (-k).toNat

theorem Good_partH (j : Fin 73)
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    (hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    (t : List ℤ) : ∀ c, c ≤ RC.N3 j → Good j (partH j t c) := by
  intro c
  induction c with
  | zero =>
      intro _
      refine Good_congr (Good_vzero j) (partH_len j t 0) ?_
      intro q hq
      rw [partH_getD j t 0 hq, vzero_getD hq]
      simp
  | succ c ih =>
      intro hc
      have hc' : c < RC.N3 j := by omega
      have hprev : Good j (partH j t c) := ih (by omega)
      have h1 := Good_add_vz j hspan hsub hprev (t.getD c 0) hc'
      refine Good_congr h1 (partH_len j t (c + 1)) ?_
      intro q hq
      exact partH_succ_vadd j t hc' q hq

/-- The final step: `y` differs from `H t` by a multiple of `n` in each coordinate, so it is
`Good`. -/
theorem Good_of_hcd (j : Fin 73)
    (hnmem : ∀ q, q < RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vunit ((RC.Ad j).n) (RC.N3 j) q))
    (hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)))
    (hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])))
    (y t : List ℤ) (hy : y.length = RC.N3 j) (ht : t.length = RC.N3 j)
    (hcd : ∀ q, q < RC.N3 j →
      (y.getD q 0 - RC.linC (RC.Cd j).H t q) % ((RC.Ad j).n : ℤ) = 0) :
    Good j y := by
  have hgood_hvec : Good j (hvec j t) := by
    have hh := Good_partH j hspan hsub t (RC.N3 j) (le_refl _)
    exact Good_congr hh (hvec_len j t) (fun q hq => hvec_partH j t q hq)
  have hdiv : ∀ q, q < RC.N3 j → ((RC.Ad j).n : ℤ) ∣ (RC.vsub y (hvec j t)).getD q 0 := by
    intro q hq
    rw [Int.dvd_iff_emod_eq_zero, vsub_getD hy (hvec_len j t) hq, hvec_getD j t hq]
    exact hcd q hq
  have h1 : RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j) (RC.vsub y (hvec j t)) :=
    RepCoh_ndvd j hnmem (RC.vsub y (hvec j t))
      (by rw [vsub_len, hy, hvec_len j t, min_self]) hdiv
  exact Good_of_span j h1 hgood_hvec hy

end RepsAux

theorem RepCoh_reps (j : Fin 73)
    (hnmem : ∀ q, q < Work.SG.RC.N3 j → Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) (Work.SG.RC.vunit ((Work.SG.RC.Ad j).n) (Work.SG.RC.N3 j) q))
    (hred : ∀ {x y : List ℤ}, x.length = Work.SG.RC.N3 j → y.length = Work.SG.RC.N3 j →
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) (Work.SG.RC.vsub x y) →
        Data.reduceBl (Work.SG.RC.Cd j).Bl x = Data.reduceBl (Work.SG.RC.Cd j).Bl y)
    (y t : List ℤ) (hy : y.length = Work.SG.RC.N3 j) (ht : t.length = Work.SG.RC.N3 j)
    (hcd : ∀ q, q < Work.SG.RC.N3 j → (y.getD q 0 - Work.SG.RC.linC (Work.SG.RC.Cd j).H t q) % ((Work.SG.RC.Ad j).n : ℤ) = 0) :
    ∃ h, h < (Work.SG.RC.Cd j).reps.length ∧
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) (Work.SG.RC.vsub y ((Work.SG.RC.Cd j).reps.getD h [])) := by
  have hspan : ∀ x : List ℤ, x.length = RC.N3 j →
      RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
        (RC.vsub x (Data.reduceBl (RC.Cd j).Bl x)) :=
    fun x hx => RepCoh_redspan (RC.N3 j) (RC.Cd j).Bl (RC.Cd_Bl_len j)
      (fun c hc => by rw [RC.BlR_getD]; exact RC.Cd_Bl_rowlen j c hc) x hx
  have hsub : ∀ c, c < RC.N3 j → ∀ h, h < (RC.Cd j).reps.length →
      ∃ h', h' < (RC.Cd j).reps.length ∧
        RC.InSpan (RC.BlR (RC.Cd j).Bl) (RC.N3 j)
          (RC.vsub (RC.vsub ((RC.Cd j).reps.getD h []) ((RC.Cd j).H.getD c []))
            ((RC.Cd j).reps.getD h' [])) :=
    fun c hc h hh => RepCoh_reps_sub j hred hspan h hh c hc
  obtain ⟨h, hh, hInv⟩ := (RepsAux.Good_of_hcd j hnmem hspan hsub y t hy ht hcd).2
  exact ⟨h, hh, hInv⟩

end Work.SG
