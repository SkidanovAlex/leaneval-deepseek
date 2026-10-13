/-
  WilE5 — the degree bound for the members of `theList` (the cell-wise list of strata).

  A member of `theList Me X` is a leaf of the fibrewise stratification recursion run inside one
  *sign cell* of `X` (`cellSemi X (cell X σ)` for a sign assignment `σ`), so its degree is
  bounded by the leaf-degree estimate `bDeg Me p q` evaluated at the cell's degree; the cell's
  degree is at most `X.deg`, because its conditions are a sub-list of the atoms of `X`.  The
  final arithmetic compares `bDeg Me p q` with the assembly bound `bK * bCount Me p q +
  bDeg Me p q + 1` of `E5.lean` (the `bK`-hypothesis is not needed for the degree bound: it is
  used only for the length bound `theListLen`).

  The leaf-degree estimate itself (`leafDegX` below) is assembled here from
  * the state invariant `Strat.dataInv` of the recursion (`Strat.levelData`),
  * the split of a leaf's degree (`degFlatStratum`),
  * the two sum estimates `stCondDegX` and `flatEqsSumX`,
  * the pure arithmetic `Bounds.bDeg_arith`.

  Everything the leaf estimate needs about the individual states (the bounds on the accumulated
  conditions, on the flatness family and on the test list) is proved in §0 below, so that this
  module depends only on the recursion invariant and on the profile arithmetic.
-/
import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE5.Strat.levelData
import Submission.Work.WilE5.Bounds.atomDeg_yOpSt_le
import Submission.Work.WilE5.Bounds.bDeg_arith

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

/-! ## §0. Degree bookkeeping for the states of the recursion -/

/-- `∑ a, atomDeg (hFun B a)` is the sum of the atom degrees of the first components of `B`. -/
private lemma sum_atomDeg_hFun {p q r : ℕ} (B : List (EAPoly (p + q) r × Fin q)) :
    (∑ a : Fin B.length, atomDeg (hFun B a)) = ((B.map Prod.fst).map atomDeg).sum := by
  rw [← List.sum_ofFn, List.map_map]
  congr 1
  rw [← List.ofFn_getElem_eq_map B (atomDeg ∘ Prod.fst)]
  simp [hFun]

/-- The degree of a state's condition, split into its three parts. -/
private lemma stCond_deg {p q r : ℕ} (σ : St p q r) :
    (stCond σ).deg = (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) +
      (σ.Ξ.map atomDeg).sum + (σ.ν.map atomDeg).sum := by
  have h1 : (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a))
      = ((σ.B.map Prod.fst).map atomDeg).sum := sum_atomDeg_hFun σ.B
  rw [show (stCond σ).deg = ((σ.B.map Prod.fst ++ σ.Ξ ++ σ.ν).map atomDeg).sum from rfl]
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
  rw [← h1]

/-- A sum of a list whose values are bounded by `c` is bounded by `|l| * c`. -/
private lemma sum_map_le_length_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : f a ≤ c := h a List.mem_cons_self
    have h2 : (l.map f).sum ≤ l.length * c := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h3 : (l.length + 1) * c = l.length * c + c := Nat.succ_mul _ _
    omega

/-- `profD` is at least `1` at every level. -/
private lemma one_le_profD_eval (Me : Polynomial ℕ) (p q n D : ℕ) :
    1 ≤ (profD Me p q n).eval D := by
  have h0 : (profD Me p q 0).eval D = D + 3 := profD_eval_zero Me p q D
  have hmono : (profD Me p q 0).eval D ≤ (profD Me p q n).eval D :=
    profD_eval_mono Me p q D (Nat.zero_le n)
  omega

/-- Every test of `testL q M NΦ` has all its multi-index entries `≤ M`. -/
private lemma mem_testL_m_le {q M NΦ : ℕ} {t : Test q} (ht : t ∈ testL q M NΦ) :
    ∀ l, t.m l ≤ M := by
  have h1 : t ∈ (((List.range NΦ).product ((mList q M).product (List.finRange q))).map
      (fun u => (⟨u.1, u.2.1, u.2.2⟩ : Test q))) := (List.mem_filter.mp ht).1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h1
  have h2 : u.2 ∈ (mList q M).product (List.finRange q) := (List.mem_product.mp hu).2
  have h3 : u.2.1 ∈ mList q M := (List.mem_product.mp h2).1
  exact fun l => (mem_mList_iff u.2.1).mp h3 l

/-- The degree of the source of a test is bounded by any bound on the flatness family. -/
private lemma testPoly_atomDeg_le {p q : ℕ} {X : SemiPf (p + q)} {Me : Polynomial ℕ}
    {σ : St p q X.r}
    (hΦ : ∀ ψ ∈ σ.Φ, atomDeg ψ ≤ (profD Me p q σ.B.length).eval X.deg) (i : ℕ) :
    atomDeg (testPoly σ i) ≤ (profD Me p q σ.B.length).eval X.deg := by
  by_cases h : i < σ.Φ.length
  · have h1 : testPoly σ i = σ.Φ[i] := by
      unfold testPoly
      rw [List.getElem?_eq_getElem h, Option.getD_some]
    rw [h1]
    exact hΦ _ (List.getElem_mem h)
  · have h1 : testPoly σ i = 0 := by
      unfold testPoly
      rw [List.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none]
    rw [h1]
    have h0 : atomDeg (0 : EAPoly (p + q) X.r) = 1 := by simp [atomDeg]
    rw [h0]
    exact one_le_profD_eval Me p q σ.B.length X.deg

/-- The multi-index sum is bounded by the number of fibre directions times the entry bound. -/
private lemma mSum_le_of_forall_le {q : ℕ} {m : Fin q → ℕ} {M : ℕ} (h : ∀ l, m l ≤ M) :
    mSum m ≤ q * M := by
  unfold mSum
  calc ∑ l : Fin q, m l ≤ ∑ _l : Fin q, M := Finset.sum_le_sum fun l _ => h l
    _ = q * M := by simp

/-- One round of fibrewise operators applied to a source of degree `≤ profD k` raises the degree
to at most `profD (k+1)` (the recursion `profD (k+1) = profD k + q * profM k * (profS k + 1)`
of `Profile.lean`). -/
private lemma yOpSt_atomDeg_le_profD {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ)
    (σ : St p q X.r) (m : Fin q → ℕ) (ψ : EAPoly (p + q) X.r)
    (hS : (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) ≤
      (profS Me p q σ.B.length).eval X.deg)
    (hψ : atomDeg ψ ≤ (profD Me p q σ.B.length).eval X.deg)
    (hm : ∀ l, m l ≤ (profM Me p q σ.B.length).eval X.deg) :
    atomDeg (yOpSt X.c σ.B m ψ) ≤ (profD Me p q (σ.B.length + 1)).eval X.deg := by
  have h1 := Work.WilE5.Bounds.atomDeg_yOpSt_le X σ ψ m
  have h2 : mSum m ≤ q * (profM Me p q σ.B.length).eval X.deg := mSum_le_of_forall_le hm
  rw [profD_eval_succ]
  calc atomDeg (yOpSt X.c σ.B m ψ)
      ≤ atomDeg ψ + mSum m * ((∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) + 1) := h1
    _ ≤ (profD Me p q σ.B.length).eval X.deg +
          (q * (profM Me p q σ.B.length).eval X.deg) *
            ((profS Me p q σ.B.length).eval X.deg + 1) :=
        Nat.add_le_add hψ (Nat.mul_le_mul h2 (Nat.add_le_add_right hS 1))
    _ = (profD Me p q σ.B.length).eval X.deg +
          q * (profM Me p q σ.B.length).eval X.deg *
            ((profS Me p q σ.B.length).eval X.deg + 1) := by ring

/-- The operator value attached to a test of level `k` has degree `≤ profD (k+1)`. -/
private lemma opVal_atomDeg_le_succ {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ)
    (σ : St p q X.r) {t : Test q}
    (ht : t ∈ testL q (MlOf Me X.deg p q σ.B.length) (NPhi Me X.deg p q))
    (hS : (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) ≤
      (profS Me p q σ.B.length).eval X.deg)
    (hΦ : ∀ ψ ∈ σ.Φ, atomDeg ψ ≤ (profD Me p q σ.B.length).eval X.deg) :
    atomDeg (opVal X.c σ t) ≤ (profD Me p q (σ.B.length + 1)).eval X.deg := by
  unfold opVal
  refine yOpSt_atomDeg_le_profD X Me σ t.m (testPoly σ t.i) hS
    (testPoly_atomDeg_le hΦ t.i) ?_
  intro l
  simpa [MlOf] using mem_testL_m_le ht l

/-! ## §1. The degree of a flat leaf, split into its three parts -/

/-- The degree of the flat leaf of a state: the degree of the ambient set, plus the number of
disjuncts times the degree of the state's own conditions (its accumulated equations `stCond σ`
together with the flatness equations `flatEqs`), plus the degree sum of the pivots. -/
theorem degFlatStratum {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) :
    WilkiesDesign.E.Stratum.deg (Work.WilE5.flatStratum X M NΦ σ) =
      X.deg + X.basics.length *
        ((Work.WilE5.stCond σ).deg + ((Work.WilE5.flatEqs X.c M NΦ σ).map
          WilkiesDesign.E.atomDeg).sum) +
      (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) := by
  have hflat : Work.WilE5.flatSemiPf X M NΦ σ =
      Work.WilE5.semiPfAnd (Work.WilE5.semiPfAnd X (Work.WilE5.stCond σ))
        (Work.WilE5.Basic.eqsOf (Work.WilE5.flatEqs X.c M NΦ σ)) := rfl
  have hdeg : WilkiesDesign.E.Stratum.deg (Work.WilE5.flatStratum X M NΦ σ) =
      (Work.WilE5.flatSemiPf X M NΦ σ).deg +
        (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) := rfl
  rw [hdeg, hflat, Work.WilE5.semiPfAnd_deg, Work.WilE5.semiPfAnd_deg,
    Work.WilE5.Basic.deg_eqsOf]
  simp only [Work.WilE5.semiPfAnd, List.length_map]
  ring

/-! ## §2. The two sum estimates -/

/-- The accumulated conditions of a state have degree at most the pivot-degree sum `profS` plus
the bound on the accumulated vanishing/positivity conditions, both at the global level `2q+1`. -/
theorem stCondDegX {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ)
    (σ : Work.WilE5.St p q X.r)
    (hS : (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      (Work.WilE5.profS Me p q σ.B.length).eval X.deg)
    (hdΞ : ∀ ψ ∈ σ.Ξ, WilkiesDesign.E.atomDeg ψ ≤
      (Work.WilE5.profD Me p q σ.B.length).eval X.deg)
    (hdν : ∀ ψ ∈ σ.ν, WilkiesDesign.E.atomDeg ψ ≤
      (Work.WilE5.profD Me p q σ.B.length).eval X.deg)
    (hΞ : σ.Ξ.length ≤ Work.WilE5.NPhi Me X.deg p q)
    (hν : σ.ν.length ≤ X.deg + 2 * q + 1)
    (hn : σ.B.length ≤ 2 * q) :
    (Work.WilE5.stCond σ).deg ≤
      (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg +
        (Work.WilE5.NPhi Me X.deg p q + (X.deg + 2 * q + 1)) *
          (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
  have hdmono : (Work.WilE5.profD Me p q σ.B.length).eval X.deg ≤
      (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg :=
    Work.WilE5.profD_eval_mono Me p q X.deg (by omega)
  have hSmono : (Work.WilE5.profS Me p q σ.B.length).eval X.deg ≤
      (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg :=
    Work.WilE5.profS_eval_mono Me p q X.deg (by omega)
  have hS' : (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg := hS.trans hSmono
  have hΞsum : (σ.Ξ.map WilkiesDesign.E.atomDeg).sum ≤
      (Work.WilE5.NPhi Me X.deg p q) *
        (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
    refine (sum_map_le_length_mul σ.Ξ WilkiesDesign.E.atomDeg _
      (fun ψ hψ => (hdΞ ψ hψ).trans hdmono)).trans ?_
    exact Nat.mul_le_mul_right _ hΞ
  have hνsum : (σ.ν.map WilkiesDesign.E.atomDeg).sum ≤
      (X.deg + 2 * q + 1) * (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
    refine (sum_map_le_length_mul σ.ν WilkiesDesign.E.atomDeg _
      (fun ψ hψ => (hdν ψ hψ).trans hdmono)).trans ?_
    exact Nat.mul_le_mul_right _ hν
  rw [stCond_deg]
  calc (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) +
        (σ.Ξ.map WilkiesDesign.E.atomDeg).sum + (σ.ν.map WilkiesDesign.E.atomDeg).sum
      ≤ (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg +
          (Work.WilE5.NPhi Me X.deg p q) *
            (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg +
          (X.deg + 2 * q + 1) * (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
        omega
    _ = (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg +
          (Work.WilE5.NPhi Me X.deg p q + (X.deg + 2 * q + 1)) *
            (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
        ring

/-- The flatness equations of a state have `atomDeg`-sum at most the number of tests times the
degree bound `profD` at the global level `2q+1`. -/
theorem flatEqsSumX {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ)
    (σ : Work.WilE5.St p q X.r)
    (hS : (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      (Work.WilE5.profS Me p q σ.B.length).eval X.deg)
    (hΦ : ∀ ψ ∈ σ.Φ, WilkiesDesign.E.atomDeg ψ ≤
      (Work.WilE5.profD Me p q σ.B.length).eval X.deg)
    (hn : σ.B.length ≤ 2 * q) :
    ((Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
        (Work.WilE5.NPhi Me X.deg p q) σ).map WilkiesDesign.E.atomDeg).sum ≤
      (Work.WilE5.NPhi Me X.deg p q) *
        ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q *
        (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
  have hpt : ∀ t ∈ Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
      (Work.WilE5.NPhi Me X.deg p q) σ,
      WilkiesDesign.E.atomDeg t ≤ (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    refine (opVal_atomDeg_le_succ X Me σ
      (List.mem_of_mem_filter ht') hS hΦ).trans ?_
    exact Work.WilE5.profD_eval_mono Me p q X.deg (by omega)
  have hlen : (Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
      (Work.WilE5.NPhi Me X.deg p q) σ).length ≤
      (Work.WilE5.NPhi Me X.deg p q) *
        ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q := by
    have h1 : (Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
        (Work.WilE5.NPhi Me X.deg p q) σ).length ≤
        (Work.WilE5.testL q (Work.WilE5.MlOf Me X.deg p q σ.B.length)
          (Work.WilE5.NPhi Me X.deg p q)).length := by
      rw [Work.WilE5.flatEqs, List.length_map]
      exact List.length_filter_le _ _
    have h2 : (Work.WilE5.testL q (Work.WilE5.MlOf Me X.deg p q σ.B.length)
        (Work.WilE5.NPhi Me X.deg p q)).length ≤
        (Work.WilE5.NPhi Me X.deg p q) *
          (Work.WilE5.MlOf Me X.deg p q σ.B.length + 1) ^ q * q :=
      Work.WilE5.Strat.testL_length_le q
        (Work.WilE5.MlOf Me X.deg p q σ.B.length) (Work.WilE5.NPhi Me X.deg p q)
    have h3 : (Work.WilE5.NPhi Me X.deg p q) *
          (Work.WilE5.MlOf Me X.deg p q σ.B.length + 1) ^ q * q ≤
        (Work.WilE5.NPhi Me X.deg p q) *
          ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q := by
      refine Nat.mul_le_mul_right q (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_left (Nat.succ_le_succ
        (Work.WilE5.profM_eval_mono Me p q X.deg (by omega))) q
    exact h1.trans (h2.trans h3)
  exact (sum_map_le_length_mul _ _ _ hpt).trans (Nat.mul_le_mul_right _ hlen)

/-! ## §3. The degree bound for the leaves of one `SemiPf` set -/

/-- Every leaf produced by the recursion on `X` has degree at most `bDeg Me p q` evaluated at
`X.deg` (`bDeg` is `profLeaf` of `Profile.lean`). -/
theorem leafDegX {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ)
    (hB : X.basics.length ≤ X.deg + 1) :
    ∀ S ∈ Work.WilE5.allStrataP X (Work.WilE5.MlOf Me X.deg p q) (Work.WilE5.NPhi Me X.deg p q) q,
      WilkiesDesign.E.Stratum.deg S ≤ (Work.WilE5.bDeg Me p q).eval X.deg := by
  intro S hS
  obtain ⟨k, hk, σ, hσ, rfl⟩ := (Work.WilE5.mem_allStrataP).mp hS
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
  obtain ⟨hBlen, hSsumB, hΦdeg, hΞdeg, hνdeg, hΞlen, hΦlen, hΦN, -, hνlen⟩ :=
    Work.WilE5.Strat.levelP_dataInv X Me k hkq σ hσ
  have hSsum : (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      (Work.WilE5.profS Me p q σ.B.length).eval X.deg := by
    rw [Work.WilE5.Bounds.Bsum_eq_sum]; exact hSsumB
  have hn2 : σ.B.length ≤ 2 * q := by omega
  have hνlen' : σ.ν.length ≤ X.deg + 2 * q + 1 := by omega
  have hΞlen' : σ.Ξ.length ≤ Work.WilE5.NPhi Me X.deg p q := hΞlen.trans hΦN
  have hflat := flatEqsSumX X Me σ hSsum hΦdeg hn2
  have hstc := stCondDegX X Me σ hSsum hΞdeg hνdeg hΞlen' hνlen' hn2
  have hsp : Work.WilE5.flatStratumP X (Work.WilE5.MlOf Me X.deg p q)
      (Work.WilE5.NPhi Me X.deg p q) σ =
      Work.WilE5.flatStratum X (Work.WilE5.MlOf Me X.deg p q σ.B.length)
        (Work.WilE5.NPhi Me X.deg p q) σ := rfl
  rw [hsp, degFlatStratum]
  have hS' : (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg :=
    hSsum.trans (Work.WilE5.profS_eval_mono Me p q X.deg (by omega))
  have hsum : (Work.WilE5.stCond σ).deg +
      ((Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
        (Work.WilE5.NPhi Me X.deg p q) σ).map WilkiesDesign.E.atomDeg).sum ≤
      (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg +
        (Work.WilE5.NPhi Me X.deg p q + (X.deg + 2 * q + 1)) *
          (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg +
        (Work.WilE5.NPhi Me X.deg p q) *
          ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q *
          (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg := by
    omega
  have houter : X.deg + X.basics.length * ((Work.WilE5.stCond σ).deg +
        ((Work.WilE5.flatEqs X.c (Work.WilE5.MlOf Me X.deg p q σ.B.length)
          (Work.WilE5.NPhi Me X.deg p q) σ).map WilkiesDesign.E.atomDeg).sum) +
        (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
      X.deg + X.basics.length * ((Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg +
        (Work.WilE5.NPhi Me X.deg p q + (X.deg + 2 * q + 1)) *
          (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg +
        (Work.WilE5.NPhi Me X.deg p q) *
          ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q *
          (Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg) +
        (Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg :=
    Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ hsum)) hS'
  exact houter.trans (Work.WilE5.Bounds.bDeg_arith Me p q X.deg X.basics.length
    ((Work.WilE5.profS Me p q (2 * q + 1)).eval X.deg)
    ((Work.WilE5.profD Me p q (2 * q + 1)).eval X.deg)
    (Work.WilE5.NPhi Me X.deg p q)
    ((Work.WilE5.profM Me p q (2 * q + 1)).eval X.deg) hB le_rfl rfl rfl rfl)

/-! ## §4. The degree bound for the list of strata -/

theorem theListDeg {p q F : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hX : X.fmt ≤ F) (bK : Polynomial ℕ)
    (hbK : ∀ (k : ℕ) (Y : WilkiesDesign.E.SemiPf k), Y.fmt ≤ F →
      (Work.WilE5.goodCells Y).length ≤ bK.eval Y.deg) :
    ∀ S ∈ Work.WilE5.theList Me X,
      WilkiesDesign.E.Stratum.deg S ≤
        (bK * Work.WilE5.bCount Me p q + Work.WilE5.bDeg Me p q + Polynomial.C 1).eval X.deg := by
  intro S hS
  obtain ⟨σ, -, hSσ⟩ := (Work.WilE5.mem_theList).mp hS
  have hmem : S ∈ Work.WilE5.allStrataP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ))
      (Work.WilE5.MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q)
      (Work.WilE5.NPhi Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) q :=
    Work.WilE5.mem_cellStrata hSσ
  have hb : (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).basics.length ≤
      (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg + 1 := by
    simp [Work.WilE5.cellSemi, WilkiesDesign.E.SemiPf.deg]
  have hleaf := leafDegX (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)) Me hb S hmem
  have hdeg : (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg ≤ X.deg := by
    rw [Work.WilE5.cellSemi_deg]
    exact Work.WilE5.cell_deg_le X σ
  refine (hleaf.trans (Work.WilE5.eval_mono_nat hdeg)).trans ?_
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Work.WilE5
