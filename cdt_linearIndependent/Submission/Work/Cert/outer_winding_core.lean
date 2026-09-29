import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ACore.drift_le
import Submission.Work.Cert.winding_of_quadrant_arcs
import Submission.Work.ANum3.phiA_analytic_ext

/-! # Abstract core of the outer winding of `φ_A + 1/72` on `|z| = 1`

Given the winding certificate facts `WindCertFacts` (a label `lab j` and a chain of `windLeafOK`
leaves for each of the `4096` uniform arcs of the unit circle, with the cyclic label sequence making
one full turn), the leaf half-plane soundness `WindLeafSound`, the arc cover contract `ArcCover`
and the rotation bounds `RotConsts`, we prove that `φ_A + 1/72` is zero free on the unit circle and
that the circle integral of its logarithmic derivative is `2πI`.

The proof has three independent layers:

* `gridDrift` (from `Work.Cert.ACore.drift_le`) — the grid points `E j` stay within `65536/S` of the exact rotations
  `rot (j/4096)`, so `ArcCover` applies with `k = 2`;
* `arc_halfplane` below — `ArcCover` together with `WindLeafSound` puts the value of `φ_A + 1/72`
  on each arc in the open half plane of the label `I ^ (lab j)`;
* `Work.Cert.winding_of_quadrant_arcs` — the quadrant winding argument (logarithmic derivative of
  an analytic function whose values avoid the branch cut on each arc) together with the cyclic
  argument computation `Work.Cert.labels_arg_sum`.

Nothing here uses the certificate data itself, only the abstract contracts. -/

namespace Work.Cert

open Submission.CDTPlan Complex Metric

set_option maxRecDepth 100000

/-- `circleMap 0 1 (2π t) = rot t`. -/
lemma circleMap_rot (t : ℝ) : circleMap 0 1 (2 * Real.pi * t) = rot t := by
  rw [circleMap_zero]
  simp only [Complex.ofReal_one, one_mul, rot]
  congr 1
  push_cast
  ring

/-- `wchainOK` is `chainOK` transported along the first projection: the `bU` witness of a winding
leaf plays no rôle in the chain check. -/
lemma wchainOK_chainOK : ∀ (L : List (Leaf × ℤ)) (nx ny : ℤ),
    wchainOK nx ny L = true → chainOK nx ny (L.map (fun l : Leaf × ℤ => l.1)) = true := by
  intro L
  induction L with
  | nil => intro nx ny h; simp [wchainOK] at h
  | cons l t ih =>
    intro nx ny h
    cases t with
    | nil =>
      simp only [wchainOK, List.map_cons, List.map_nil, chainOK, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact h
    | cons m rest =>
      have h' := h
      rw [wchainOK] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨⟨h1, h2⟩, h3⟩ := h'
      simp only [List.map_cons, chainOK, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨h1, h2⟩, ih nx ny h3⟩

/-- The geometric part of `leafOK` (`geomOK`) is implied by the success of the value chain
`qChain` of the winding checker: `qChain` starts with exactly the `geomOK` side conditions. -/
lemma geomOK_of_qChain_ok (L : Leaf) : (qChain L).ok = true → geomOK L = true := by
  simp only [qChain, luneStage, slitStage, geomOK, Bool.and_eq_true, decide_eq_true_eq]
  intro h
  tauto

/-- **Grid drift.**  Specialisation of the general `Work.Cert.ACore.drift_le` to the circle
`k = 2` (where `Rk 2 = S`, so the exact points are the rotations `rot (j/4096)` themselves): the
grid points `E j` given by the winding certificate stay within `65536/S` of `rot (j/4096)`. -/
lemma gridDrift (hR : RotConsts) (E : ℕ → ℤ × ℤ) (hE0 : E 0 = (S, 0))
    (hstep : ∀ j, j < 4096 → gridStep (E j).1 (E j).2 (E (j + 1)).1 (E (j + 1)).2 = true) :
    ∀ j : ℕ, j ≤ 4096 → ‖cx (E j).1 (E j).2 - rot ((j : ℝ) / 4096)‖ ≤ 65536 / (S : ℝ) := by
  intro j hj
  have h := Work.Cert.ACore.drift_le hR.2.2.2.2 2 (by norm_num) E
    (by rw [hE0]; exact Prod.ext (by decide) rfl) hstep j hj
  have hRk : (((Rk 2 : ℝ) : ℂ) / ((S : ℝ) : ℂ)) = 1 := by
    have h2 : Rk 2 = S := by decide
    rw [h2]; norm_num [S]
  rw [hRk, one_mul] at h
  exact h

/-- The facts carried by the winding leaf check: the circle index is `2`, the label index is `< 4`,
and the geometric side conditions of `geomOK` hold. -/
lemma windLeafOK_facts (lab : ℕ) (L : Leaf) (bU : ℤ) (h : windLeafOK lab L bU = true) :
    L.k = 2 ∧ lab < 4 ∧ geomOK L = true := by
  have hk : L.k = 2 := by
    have h' := h
    simp only [windLeafOK] at h'
    exact decide_eq_true_eq.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h').1).1).1
  have hl4 : lab < 4 := by
    have h' := h
    simp only [windLeafOK] at h'
    exact decide_eq_true_eq.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h').1).1).2
  have hg : (gDisc L bU).1 = true := by
    have h' := h
    simp only [windLeafOK] at h'
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h').1).2
  have hq : (qChain L).ok = true := by
    have h' := hg
    simp only [gDisc] at h'
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h').1).1).1).1
  exact ⟨hk, hl4, geomOK_of_qChain_ok L hq⟩

/-- **The per-arc half-plane condition.**  From the arc cover, the leaf half-plane soundness and
the grid drift, on every uniform arc `[j/4096, (j+1)/4096]` of the unit circle the value of
`φ_A + 1/72` lies in the open half plane of the label `I ^ (lab j)`. -/
theorem arc_halfplane (hW : WindLeafSound) (hC : ArcCover)
    (lab : ℕ → ℕ) (E : ℕ → ℤ × ℤ) (LS : ℕ → List (Leaf × ℤ))
    (hdrift : ∀ j : ℕ, j ≤ 4096 →
      ‖cx (E j).1 (E j).2 - rot ((j : ℝ) / 4096)‖ ≤ 65536 / (S : ℝ))
    (hLS : ∀ j : ℕ, j < 4096 →
      (match LS j with | [] => false | l :: _ => decide (l.1.Ax = (E j).1) && decide (l.1.Ay = (E j).2)) = true ∧
      wchainOK (E (j+1)).1 (E (j+1)).2 (LS j) = true ∧
      gridStep (E j).1 (E j).2 (E (j+1)).1 (E (j+1)).2 = true ∧
      (LS j).all (fun l => windLeafOK (lab j) l.1 l.2) = true) :
    ∀ j : ℕ, j < 4096 → ∀ t ∈ Set.Icc ((j : ℝ) / 4096) (((j : ℝ) + 1) / 4096),
      0 < ((phiA (circleMap 0 1 (2 * Real.pi * t)) + 1 / 72) * star (Complex.I ^ (lab j))).re := by
  intro j hj t ht
  have hLSj := hLS j hj
  have hhead : (match (LS j).map (fun l : Leaf × ℤ => l.1) with
      | [] => false | l :: _ => decide (l.Ax = (E j).1) && decide (l.Ay = (E j).2)) = true := by
    cases h : LS j with
    | nil =>
      have h1 := hLSj.1
      rw [h] at h1
      simpa using h1
    | cons a t' =>
      have h1 := hLSj.1
      rw [h] at h1
      simpa using h1
  have hchain : chainOK (E (j+1)).1 (E (j+1)).2 ((LS j).map (fun l : Leaf × ℤ => l.1)) = true :=
    wchainOK_chainOK (LS j) _ _ hLSj.2.1
  have hall : ((LS j).map (fun l : Leaf × ℤ => l.1)).all
      (fun l => decide (l.k = 2) && geomOK l) = true := by
    rw [List.all_map]
    refine List.all_eq_true.mpr (fun l hl => ?_)
    have hwl : windLeafOK (lab j) l.1 l.2 = true := List.all_eq_true.mp hLSj.2.2.2 l hl
    obtain ⟨hk, _, hg⟩ := windLeafOK_facts (lab j) l.1 l.2 hwl
    simp [hk, hg]
  have hRk : ((Rk 2 : ℝ) / (S : ℝ)) = 1 := by
    have h : Rk 2 = S := by decide
    rw [h]; norm_num [S]
  have hd1 : ‖cx (E j).1 (E j).2 - ((Rk 2 : ℝ) / S : ℝ) * rot ((j : ℝ) / 4096)‖
      ≤ 65536 / (S : ℝ) := by
    simpa [hRk] using hdrift j (le_of_lt hj)
  have hd2 : ‖cx (E (j+1)).1 (E (j+1)).2 - ((Rk 2 : ℝ) / S : ℝ) * rot (((j : ℝ) + 1) / 4096)‖
      ≤ 65536 / (S : ℝ) := by
    simpa [hRk] using hdrift (j+1) (by omega)
  obtain ⟨l, hlmem, hlball⟩ := hC 2 j (E j).1 (E j).2 (E (j+1)).1 (E (j+1)).2
      ((LS j).map (fun l : Leaf × ℤ => l.1)) (by norm_num) hj hd1 hd2 hhead hchain hall t ht
  obtain ⟨l', hl'mem, hl'eq⟩ := List.mem_map.mp hlmem
  have hwl : windLeafOK (lab j) l'.1 l'.2 = true := List.all_eq_true.mp hLSj.2.2.2 l' hl'mem
  have hball : ‖rot t - leafC l'.1‖ ≤ leafR l'.1 := by
    rw [← hl'eq] at hlball
    simpa [hRk] using hlball
  have hres := hW (lab j) l'.1 l'.2 hwl (rot t) hball
  rw [circleMap_rot]
  exact hres

open Submission.CDTPlan in
theorem outer_winding_core (hW : WindLeafSound) (hC : ArcCover) (hR : RotConsts) (hF : WindCertFacts) :
    (∀ z : ℂ, ‖z‖ = 1 → phiA z + 1 / 72 ≠ 0) ∧
      circleIntegral (fun z => logDeriv (fun w => phiA w + 1 / 72) z) 0 1 =
        2 * (Real.pi : ℂ) * Complex.I := by
  obtain ⟨lab, E, LS, hE0, hE4096, hLS⟩ := hF
  have hdrift : ∀ j : ℕ, j ≤ 4096 →
      ‖cx (E j).1 (E j).2 - rot ((j : ℝ) / 4096)‖ ≤ 65536 / (S : ℝ) :=
    gridDrift hR E hE0 (fun j hj => (hLS.1 j hj).2.2.1)
  have harc := arc_halfplane hW hC lab E LS hdrift (fun j hj => hLS.1 j hj)
  have hlt : ∀ i, i < 4096 → lab i < 4 := by
    intro i hi
    have hLSi := hLS.1 i hi
    have hne : LS i ≠ [] := by
      intro hnil
      have h1 := hLSi.1
      rw [hnil] at h1
      exact Bool.noConfusion h1
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    exact (windLeafOK_facts (lab i) a.1 a.2 (List.all_eq_true.mp hLSi.2.2.2 a ha)).2.1
  exact winding_of_quadrant_arcs (g := fun z => phiA z + 1 / 72) (R := 500 / 491) (by norm_num)
    (Work.ANum3.phiA_analytic_ext.add analyticOnNhd_const) lab hlt hLS.2
    (fun i t ht => harc i i.isLt t ht)

end Work.Cert
