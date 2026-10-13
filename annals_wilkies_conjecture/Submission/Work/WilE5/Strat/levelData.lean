import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Profile
import Submission.Work.WilE5.Strat.InitCover
import Submission.Work.WilE5.Bounds.atomDeg_yOpSt_le
import Submission.Work.WilE5.Bounds.stateData_bound
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

variable {p q r : ℕ}

/-! ## §1. `mList` and `testL`: length and duplication -/

/-- `mList q M` enumerates `Fin q → Fin (M+1)`, so it has no duplicates. -/
theorem mList_nodup (q M : ℕ) : (Work.WilE5.mList q M).Nodup := by
  unfold Work.WilE5.mList
  refine List.Nodup.map ?_ (Finset.nodup_toList _)
  intro a b h
  funext i
  exact Fin.ext (by simpa using congrFun h i)

/-- `mList q M` has exactly `(M+1)^q` elements. -/
theorem mList_length (q M : ℕ) : (Work.WilE5.mList q M).length = (M + 1) ^ q := by
  have h : (Work.WilE5.mList q M).length
      = (Finset.univ : Finset (Fin q → Fin (M + 1))).card := by
    rw [Work.WilE5.mList, List.length_map, Multiset.length_toList, Finset.card_def]
  rw [h, Finset.card_univ, Fintype.card_fun]
  simp

/-- The test list has no duplicates. -/
theorem testL_nodup (q M NΦ : ℕ) : (Work.WilE5.testL q M NΦ).Nodup := by
  unfold Work.WilE5.testL
  refine List.Nodup.filter _ (List.Nodup.map ?_ ?_)
  · intro a b h
    exact Prod.ext (congrArg (fun t : Work.WilE5.Test q => t.i) h)
      (Prod.ext (congrArg (fun t : Work.WilE5.Test q => t.m) h)
        (congrArg (fun t : Work.WilE5.Test q => t.l) h))
  · exact (List.nodup_range).product ((mList_nodup q M).product (List.nodup_finRange q))

/-- `testL q M L` has at most `L * (M+1)^q * q` elements. -/
theorem testL_length_le (q M L : ℕ) :
    (Work.WilE5.testL q M L).length ≤ L * (M + 1) ^ q * q := by
  have h1 : (Work.WilE5.testL q M L).length
      ≤ ((List.range L) ×ˢ ((Work.WilE5.mList q M) ×ˢ (List.finRange q))).length := by
    unfold Work.WilE5.testL
    exact (List.length_filter_le _ _).trans (le_of_eq (List.length_map _))
  rw [List.length_product, List.length_product, List.length_range, List.length_finRange,
    mList_length] at h1
  exact h1.trans (le_of_eq (Nat.mul_assoc _ _ _).symm)

/-- The number of *preceding valid* tests of a test is bounded by the size of the flatness family
(not by the nominal source bound).  Every element of `prec` is valid, hence has source index
`< σ.Φ.length`, and for each source index there are at most `(M+1)^q * q` tests. -/
theorem prec_length_le_aux (M NΦ : ℕ) (σ : St p q r) (t : Test q) :
    (prec M NΦ σ t).length ≤ σ.Φ.length * (M + 1) ^ q * q := by
  have hnodup : (prec M NΦ σ t).Nodup := by
    rw [Work.WilE5.prec]
    exact (testL_nodup q M NΦ).filter _
  have hsub : ∀ u ∈ prec M NΦ σ t, u ∈ Work.WilE5.testL q M (σ.Φ.length) := by
    intro u hu
    rw [Work.WilE5.prec] at hu
    obtain ⟨huL, hup⟩ := List.mem_filter.mp hu
    have hvv : valid σ u := by
      rw [decide_eq_true_eq, Bool.and_eq_true_eq_eq_true_and_eq_true] at hup
      exact of_decide_eq_true hup.1
    have hui : u.i < σ.Φ.length := hvv.1
    have htm := (Work.WilE5.Strat.mem_testL_iff u).mp huL
    exact (Work.WilE5.Strat.mem_testL_iff u).mpr ⟨hui, htm.2.1, htm.2.2⟩
  exact (List.subperm_of_subset hnodup hsub).length_le.trans
    (testL_length_le q M (σ.Φ.length))

/-! ## §2. The profile invariant -/

theorem profN_zero (Me : Polynomial ℕ) (p q : ℕ) :
    profN Me p q 0 = Polynomial.X + Polynomial.C 1 := rfl

theorem profN_zero_eval (Me : Polynomial ℕ) (p q D : ℕ) :
    (profN Me p q 0).eval D = D + 1 := by
  rw [profN_zero]; simp

/-- The degree of the source of a test is bounded by any bound on the flatness family. -/
theorem atomDeg_testPoly_aux (σ : St p q r) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : ∀ ψ ∈ σ.Φ, atomDeg ψ ≤ d) (i : ℕ) : atomDeg (testPoly σ i) ≤ d := by
  rcases lt_or_ge i σ.Φ.length with h | h
  · rw [Work.WilE5.testPoly, List.getElem?_eq_getElem h, Option.getD_some]
    exact hd _ (List.getElem_mem h)
  · rw [Work.WilE5.testPoly, List.getElem?_eq_none h, Option.getD_none]
    simp only [WilkiesDesign.E.atomDeg, MvPolynomial.totalDegree_zero, Nat.zero_add]
    exact hd1

/-- The profile-indexed data invariant of a state at recursion level `k`. -/
def dataInv (Me : Polynomial ℕ) (p q D : ℕ) (k : ℕ) {r : ℕ} (σ : St p q r) : Prop :=
  σ.B.length ≤ q + k ∧
  (Work.WilE5.Bounds.Bsum σ.B ≤ (profS Me p q σ.B.length).eval D) ∧
  (∀ ψ ∈ σ.Φ, atomDeg ψ ≤ (profD Me p q σ.B.length).eval D) ∧
  (∀ ψ ∈ σ.Ξ, atomDeg ψ ≤ (profD Me p q σ.B.length).eval D) ∧
  (∀ ψ ∈ σ.ν, atomDeg ψ ≤ (profD Me p q σ.B.length).eval D) ∧
  σ.Ξ.length ≤ σ.Φ.length ∧
  σ.Φ.length ≤ (profN Me p q σ.B.length).eval D ∧
  σ.Φ.length ≤ NPhi Me D p q ∧
  (∀ ψ ∈ σ.Φ,
    Me.eval (Work.WilE5.Bounds.Bsum σ.B + 2 * p + atomDeg ψ) ≤
      MlOf Me D p q σ.B.length) ∧
  σ.ν.length ≤ D + q + k

/-! ## §3. The initial states -/

theorem dataInv_init {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ) :
    ∀ σ ∈ Work.WilE5.initStates X, dataInv Me p q X.deg 0 σ := by
  intro σ hσ
  obtain ⟨A, hA, Fy, ε, rfl⟩ := Work.WilE5.exists_of_mem_initStates X hσ
  -- the disjunct's data
  have hAdeg : A.deg ≤ X.deg := List.le_sum_of_mem (List.mem_map_of_mem hA)
  have hE : (A.eqs.map atomDeg).sum ≤ X.deg := (Work.WilE5.Bounds.eqs_sum_le_deg A).trans hAdeg
  have hP : (A.pos.map atomDeg).sum ≤ X.deg := (Work.WilE5.Bounds.pos_sum_le_deg A).trans hAdeg
  have hEd : ∀ ψ ∈ A.eqs, atomDeg ψ ≤ X.deg :=
    fun ψ hψ => (Work.WilE5.Bounds.mem_atomDeg_le_sum hψ).trans hE
  have hPd : ∀ ψ ∈ A.pos, atomDeg ψ ≤ X.deg :=
    fun ψ hψ => (Work.WilE5.Bounds.mem_atomDeg_le_sum hψ).trans hP
  -- the face pattern
  have hlen : (Fy.attach.toList).length ≤ q := by
    rw [Finset.length_toList, Finset.card_attach]
    exact (Finset.card_le_univ Fy).trans (le_of_eq (Fintype.card_fin q))
  have hlenc : (Fyᶜ.attach.toList).length ≤ q := by
    rw [Finset.length_toList, Finset.card_attach]
    exact (Finset.card_le_univ Fyᶜ).trans (le_of_eq (Fintype.card_fin q))
  have hBlen : (initSt X A Fy ε).B.length = (Fy.attach.toList).length := by
    simp [initSt, List.length_map]
  have hBsum : Work.WilE5.Bounds.Bsum (initSt X A Fy ε).B ≤ 2 * q := by
    have hmap : Work.WilE5.Bounds.Bsum (initSt X A Fy ε).B
        = ((Fy.attach.toList).map
            (fun l => atomDeg (facePoly (p := p) (r := X.r) l.1
              (if ε l then 1 else -1)))).sum := by
      simp only [Work.WilE5.Bounds.Bsum, initSt, List.map_map]
      rfl
    rw [hmap]
    calc ((Fy.attach.toList).map
            (fun l => atomDeg (facePoly (p := p) (r := X.r) l.1
              (if ε l then 1 else -1)))).sum
        ≤ ((Fy.attach.toList).map (fun _ => 2)).sum :=
          List.sum_le_sum (fun x _ =>
            Work.WilE5.Bounds.atomDeg_facePoly_le x.1 (if ε x then 1 else -1))
      _ = (Fy.attach.toList).length * 2 := by
          rw [List.map_const', List.sum_replicate, smul_eq_mul]
      _ ≤ q * 2 := Nat.mul_le_mul_right 2 hlen
      _ = 2 * q := by ring
  -- the profile bounds at the state's own index
  have hprofS0 : 2 * q ≤ (profS Me p q (initSt X A Fy ε).B.length).eval X.deg := by
    have h := profS_eval_mono Me p q X.deg (Nat.zero_le (initSt X A Fy ε).B.length)
    simp only [profS_eval_zero] at h
    exact h
  have hprofD0 : X.deg + 3 ≤ (profD Me p q (initSt X A Fy ε).B.length).eval X.deg := by
    have h := profD_eval_mono Me p q X.deg (Nat.zero_le (initSt X A Fy ε).B.length)
    simp only [profD_eval_zero] at h
    exact h
  have hprofD0' : X.deg ≤ (profD Me p q (initSt X A Fy ε).B.length).eval X.deg :=
    (Nat.le_add_right X.deg 3).trans hprofD0
  have hprofN0 : X.deg + 1 ≤ (profN Me p q (initSt X A Fy ε).B.length).eval X.deg := by
    have h := profN_eval_mono Me p q X.deg (Nat.zero_le (initSt X A Fy ε).B.length)
    simp only [profN_zero_eval] at h
    exact h
  have hΦlen : A.eqs.length ≤ (profN Me p q (initSt X A Fy ε).B.length).eval X.deg :=
    (Work.WilE5.Bounds.list_len_le_sum_atomDeg A.eqs).trans
      (hE.trans (le_trans (Nat.le_succ X.deg) hprofN0))
  have hΦN : A.eqs.length ≤ NPhi Me X.deg p q := by
    have hmono : (profN Me p q 0).eval X.deg ≤ (profN Me p q (2 * q + 1)).eval X.deg := by
      have h := profN_eval_mono Me p q X.deg (show (0 : ℕ) ≤ 2 * q + 1 by omega)
      simpa using h
    have h0 : (profN Me p q 0).eval X.deg = X.deg + 1 := profN_zero_eval Me p q X.deg
    have h1 : X.deg + 1 ≤ NPhi Me X.deg p q := by
      show X.deg + 1 ≤ (profN Me p q (2 * q + 1)).eval X.deg
      omega
    exact (Work.WilE5.Bounds.list_len_le_sum_atomDeg A.eqs).trans
      (hE.trans (le_trans (Nat.le_succ X.deg) h1))
  have hνlen : (initSt X A Fy ε).ν.length = A.pos.length + (Fyᶜ.attach.toList).length := by
    simp [initSt, List.length_append, List.length_map]
  have hνle : A.pos.length ≤ X.deg :=
    (Work.WilE5.Bounds.list_len_le_sum_atomDeg A.pos).trans hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBlen]; omega
  · exact hBsum.trans hprofS0
  · exact fun ψ hψ => (hEd ψ hψ).trans hprofD0'
  · exact fun ψ hψ => (hEd ψ hψ).trans hprofD0'
  · intro ψ hψ
    have hψ' : ψ ∈ A.pos ∨
        ∃ l ∈ Fyᶜ.attach.toList, intPoly (p := p) (r := X.r) l.1 = ψ := by
      simpa [initSt, List.mem_append, List.mem_map] using hψ
    rcases hψ' with h1 | ⟨l, -, hfl⟩
    · exact (hPd ψ h1).trans hprofD0'
    · rw [← hfl]
      exact (Work.WilE5.Bounds.atomDeg_intPoly_le l.1).trans (by omega)
  · exact le_of_eq rfl
  · exact hΦlen
  · exact hΦN
  · intro ψ hψ
    have hψ' : atomDeg ψ ≤ X.deg := hEd ψ hψ
    have hsum : Work.WilE5.Bounds.Bsum (initSt X A Fy ε).B
        ≤ (profS Me p q (initSt X A Fy ε).B.length).eval X.deg := hBsum.trans hprofS0
    have hdeg : atomDeg ψ ≤ (profD Me p q (initSt X A Fy ε).B.length).eval X.deg :=
      hψ'.trans hprofD0'
    have hle : Work.WilE5.Bounds.Bsum (initSt X A Fy ε).B + 2 * p + atomDeg ψ
        ≤ (profS Me p q (initSt X A Fy ε).B.length).eval X.deg
          + (profD Me p q (initSt X A Fy ε).B.length).eval X.deg + (2 * p + 1) := by omega
    have key : Me.eval ((profS Me p q (initSt X A Fy ε).B.length).eval X.deg
          + (profD Me p q (initSt X A Fy ε).B.length).eval X.deg + (2 * p + 1))
        ≤ MlOf Me X.deg p q (initSt X A Fy ε).B.length := by
      rw [show MlOf Me X.deg p q (initSt X A Fy ε).B.length
            = (profM Me p q (initSt X A Fy ε).B.length).eval X.deg from rfl, profM_eval]
    exact (eval_mono_nat hle).trans key
  · rw [hνlen]; omega

/-! ## §4. The recursion step -/

theorem child_dataInv {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ) (k : ℕ)
    (hk : k + 1 ≤ q) {ρ : St p q X.r} (hkρ : dataInv Me p q X.deg k ρ)
    (t : Test q) (s : Bool)
    (ht : t ∈ Work.WilE5.testL q (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q)) :
    dataInv Me p q X.deg (k + 1)
      (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s) := by
  obtain ⟨hB, hS, hd, hdΞ, hdν, hΞ, hΦ, hΦN, hMu, hν⟩ := hkρ
  -- elementary profile facts
  have hd1 : 1 ≤ (profD Me p q ρ.B.length).eval X.deg := by
    have h := profD_eval_mono Me p q X.deg (Nat.zero_le ρ.B.length)
    simp only [profD_eval_zero] at h
    omega
  have hdle : (profD Me p q ρ.B.length).eval X.deg
      ≤ (profD Me p q (ρ.B.length + 1)).eval X.deg :=
    profD_eval_mono Me p q X.deg (Nat.le_succ ρ.B.length)
  have hprofD1 : (profD Me p q (ρ.B.length + 1)).eval X.deg
      = (profD Me p q ρ.B.length).eval X.deg
        + q * (profM Me p q ρ.B.length).eval X.deg
            * ((profS Me p q ρ.B.length).eval X.deg + 1) :=
    profD_eval_succ Me p q ρ.B.length X.deg
  -- the test's data
  have htL := (Work.WilE5.Strat.mem_testL_iff t).mp ht
  have htmSum : mSum t.m ≤ q * (MlOf Me X.deg p q ρ.B.length) :=
    Work.WilE5.Bounds.mSum_mList_le ((Work.WilE5.mem_mList_iff t.m).mp htL.2.1)
  have hsmSum : mSum (mDec t.m t.l) ≤ q * (MlOf Me X.deg p q ρ.B.length) :=
    (Work.WilE5.mSum_mDec_le t.m t.l).trans htmSum
  -- degree of a source
  have htestPoly : ∀ i, atomDeg (testPoly ρ i) ≤ (profD Me p q ρ.B.length).eval X.deg :=
    fun i => atomDeg_testPoly_aux ρ hd1 hd i
  -- degree of an operator value at a test of `testL`
  have hopAny : ∀ t' ∈ Work.WilE5.testL q (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q),
      atomDeg (opVal X.c ρ t') ≤ (profD Me p q (ρ.B.length + 1)).eval X.deg := by
    intro t' ht'
    have ht'L := (Work.WilE5.Strat.mem_testL_iff t').mp ht'
    have hm' : mSum t'.m ≤ q * (MlOf Me X.deg p q ρ.B.length) :=
      Work.WilE5.Bounds.mSum_mList_le ((Work.WilE5.mem_mList_iff t'.m).mp ht'L.2.1)
    have h := Work.WilE5.Bounds.atomDeg_yOpSt_le X ρ (testPoly ρ t'.i) t'.m
    rw [Work.WilE5.Bounds.Bsum_eq_sum] at h
    refine h.trans ?_
    rw [hprofD1]
    exact Nat.add_le_add (htestPoly t'.i) (Nat.mul_le_mul hm' (Nat.add_le_add_right hS 1))
  -- degree of the appended pivot
  have hpeel : atomDeg (peelVal X.c ρ t) ≤ (profD Me p q (ρ.B.length + 1)).eval X.deg := by
    have h := Work.WilE5.Bounds.atomDeg_yOpSt_le X ρ (testPoly ρ t.i) (mDec t.m t.l)
    rw [Work.WilE5.Bounds.Bsum_eq_sum] at h
    refine h.trans ?_
    rw [hprofD1]
    exact Nat.add_le_add (htestPoly t.i) (Nat.mul_le_mul hsmSum (Nat.add_le_add_right hS 1))
  have hop : atomDeg (opVal X.c ρ t) ≤ (profD Me p q (ρ.B.length + 1)).eval X.deg := hopAny t ht
  -- the number of appended conditions
  have hprec : (prec (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length
      ≤ (profN Me p q ρ.B.length).eval X.deg
        * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q * q) := by
    have h1 : ρ.Φ.length * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q)
        ≤ (profN Me p q ρ.B.length).eval X.deg
          * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q) :=
      Nat.mul_le_mul_right _ hΦ
    have h2 : ρ.Φ.length * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q) * q
        ≤ (profN Me p q ρ.B.length).eval X.deg
          * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q) * q :=
      Nat.mul_le_mul_right q h1
    refine (prec_length_le_aux _ _ ρ t).trans (h2.trans ?_)
    exact le_of_eq (Nat.mul_assoc _ _ _)
  have hΞlen : (childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length
      = (ρ.Ξ.length
          + (prec (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length) + 1 := by
    simp only [Work.WilE5.childΞ, List.length_append, List.length_map, List.length_singleton]
  have hnewΞ : (childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length
      ≤ (profN Me p q ρ.B.length).eval X.deg
        + (profN Me p q ρ.B.length).eval X.deg
          * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q * q) + 1 := by
    rw [hΞlen]
    exact Nat.add_le_add_right (add_le_add (hΞ.trans hΦ) hprec) 1
  -- unfolding facts
  have hτBeq : (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).B
      = childB X.c ρ t := rfl
  have hτlen : (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).B.length
      = ρ.B.length + 1 := by simp [Work.WilE5.childSt, Work.WilE5.childB]
  have hτΦ : (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).Φ.length
      = ρ.Φ.length
        + (childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length := by
    simp [Work.WilE5.childSt]
  -- the target bound on `|Φ|` of the child
  have hΦchild : (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).Φ.length
      ≤ (profN Me p q (ρ.B.length + 1)).eval X.deg := by
    rw [hτΦ, Work.WilE5.profN_succ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    have h2 : ρ.Φ.length
          + (childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t).length
        ≤ (profN Me p q ρ.B.length).eval X.deg
          + ((profN Me p q ρ.B.length).eval X.deg
            + (profN Me p q ρ.B.length).eval X.deg
              * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q * q) + 1) :=
      Nat.add_le_add hΦ hnewΞ
    have h3 : (profN Me p q ρ.B.length).eval X.deg
          + ((profN Me p q ρ.B.length).eval X.deg
            + (profN Me p q ρ.B.length).eval X.deg
              * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q * q) + 1)
        ≤ 3 * (profN Me p q ρ.B.length).eval X.deg
          + q * ((profM Me p q ρ.B.length).eval X.deg + 1) ^ q
              * (profN Me p q ρ.B.length).eval X.deg + 1 := by
      have e : (profN Me p q ρ.B.length).eval X.deg
            * (((profM Me p q ρ.B.length).eval X.deg + 1) ^ q * q)
          = q * ((profM Me p q ρ.B.length).eval X.deg + 1) ^ q
              * (profN Me p q ρ.B.length).eval X.deg := by ring
      omega
    exact h2.trans h3
  -- the `Mu` bound for the child
  have hchildMu : ∀ ψ ∈ (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).Φ,
      Me.eval (Work.WilE5.Bounds.Bsum
            (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).B
          + 2 * p + atomDeg ψ)
        ≤ MlOf Me X.deg p q
            (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).B.length := by
    intro ψ hψ
    have hψmem : ψ ∈ ρ.Φ
        ∨ ψ ∈ childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t := by
      simpa [Work.WilE5.childSt] using hψ
    have hψd : atomDeg ψ ≤ (profD Me p q (ρ.B.length + 1)).eval X.deg := by
      rcases hψmem with h1 | h1
      · exact (hd ψ h1).trans hdle
      · rcases Work.WilE5.Bounds.mem_childΞ_imp X.c (MlOf Me X.deg p q ρ.B.length)
            (NPhi Me X.deg p q) ρ t ψ h1 with h2 | ⟨t', ht'p, ht'⟩ | h2
        · exact (hdΞ ψ h2).trans hdle
        · rw [← ht']
          exact hopAny t' (Work.WilE5.Bounds.prec_subset_testL _ _ _ _ _ ht'p)
        · rw [h2]; exact hpeel
    rw [hτlen, hτBeq, Work.WilE5.Bounds.Bsum_childB]
    have hle : Work.WilE5.Bounds.Bsum ρ.B + atomDeg (peelVal X.c ρ t) + 2 * p + atomDeg ψ
        ≤ (profS Me p q (ρ.B.length + 1)).eval X.deg
          + (profD Me p q (ρ.B.length + 1)).eval X.deg + (2 * p + 1) := by
      have hSle : (profS Me p q ρ.B.length).eval X.deg
          ≤ (profS Me p q (ρ.B.length + 1)).eval X.deg :=
        profS_eval_mono Me p q X.deg (Nat.le_succ ρ.B.length)
      have hS1 : (profS Me p q (ρ.B.length + 1)).eval X.deg
          = (profS Me p q ρ.B.length).eval X.deg
            + (profD Me p q (ρ.B.length + 1)).eval X.deg :=
        profS_eval_succ Me p q ρ.B.length X.deg
      omega
    have key : Me.eval ((profS Me p q (ρ.B.length + 1)).eval X.deg
          + (profD Me p q (ρ.B.length + 1)).eval X.deg + (2 * p + 1))
        ≤ MlOf Me X.deg p q (ρ.B.length + 1) := by
      rw [show MlOf Me X.deg p q (ρ.B.length + 1)
            = (profM Me p q (ρ.B.length + 1)).eval X.deg from rfl, profM_eval]
    exact (eval_mono_nat hle).trans key
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hchildMu, ?_⟩
  · rw [hτlen]; omega
  · rw [hτlen, hτBeq, Work.WilE5.Bounds.Bsum_childB, profS_eval_succ]
    exact Nat.add_le_add hS hpeel
  · rw [hτlen]
    intro ψ hψ
    have hmem : ψ ∈ ρ.Φ
        ∨ ψ ∈ childΞ X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t := by
      simpa [Work.WilE5.childSt] using hψ
    rcases hmem with h1 | h1
    · exact (hd ψ h1).trans hdle
    · rcases Work.WilE5.Bounds.mem_childΞ_imp X.c (MlOf Me X.deg p q ρ.B.length)
          (NPhi Me X.deg p q) ρ t ψ h1 with h2 | ⟨t', ht'p, ht'⟩ | h2
      · exact (hdΞ ψ h2).trans hdle
      · rw [← ht']
        exact hopAny t' (Work.WilE5.Bounds.prec_subset_testL _ _ _ _ _ ht'p)
      · rw [h2]; exact hpeel
  · rw [hτlen]
    intro ψ hψ
    rcases Work.WilE5.Bounds.mem_childΞ_imp X.c (MlOf Me X.deg p q ρ.B.length)
        (NPhi Me X.deg p q) ρ t ψ (by simpa [Work.WilE5.childSt] using hψ) with
      h2 | ⟨t', ht'p, ht'⟩ | h2
    · exact (hdΞ ψ h2).trans hdle
    · rw [← ht']
      exact hopAny t' (Work.WilE5.Bounds.prec_subset_testL _ _ _ _ _ ht'p)
    · rw [h2]; exact hpeel
  · rw [hτlen]
    intro ψ hψ
    rcases Work.WilE5.Bounds.mem_childν_imp X.c ρ t s ψ
        (by simpa [Work.WilE5.childSt] using hψ) with h1 | h1 | h1
    · exact (hdν ψ h1).trans hdle
    · rw [h1]; exact hop
    · rw [h1, Work.WilE5.Bounds.atomDeg_neg]; exact hop
  · rw [hτΦ]
    exact Nat.le_add_left _ _
  · rw [hτlen]; exact hΦchild
  · exact hΦchild.trans (profN_eval_mono Me p q X.deg (by omega))
  · have h1 : (childSt X.c (MlOf Me X.deg p q ρ.B.length) (NPhi Me X.deg p q) ρ t s).ν.length
        = ρ.ν.length + 1 := by
      simp only [Work.WilE5.childSt, Work.WilE5.childν, List.length_append]
      split <;> simp
    rw [h1]; omega

/-! ## §5. The invariant holds at every level of the recursion -/

theorem levelP_dataInv {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ) :
    ∀ k, k ≤ q → ∀ σ ∈ Work.WilE5.levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k,
      dataInv Me p q X.deg k σ := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    exact dataInv_init X Me σ hσ
  | succ k ih =>
    intro hk σ' hσ'
    have hk' : k ≤ q := le_trans (Nat.le_succ k) hk
    rw [Work.WilE5.levelP_succ] at hσ'
    obtain ⟨ρ, hρ, hc⟩ := List.mem_flatMap.mp hσ'
    rw [Work.WilE5.childrenP] at hc
    obtain ⟨t, ht, hc2⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc2 with h | h
    · rw [h]
      exact child_dataInv X Me k hk (ih hk' ρ hρ) t false ht
    · rw [List.mem_singleton.mp h]
      exact child_dataInv X Me k hk (ih hk' ρ hρ) t true ht

/-! ## §6. The target statement -/

theorem levelData {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ) :
    ∀ k ∈ Finset.range (q + 1),
      ∀ σ ∈ Work.WilE5.levelP X (Work.WilE5.MlOf Me X.deg p q) (Work.WilE5.NPhi Me X.deg p q) k,
      (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
          (Work.WilE5.profS Me p q σ.B.length).eval X.deg ∧
      (∀ ψ ∈ σ.Φ, WilkiesDesign.E.atomDeg ψ ≤ (Work.WilE5.profD Me p q σ.B.length).eval X.deg) ∧
      (∀ ψ ∈ σ.Ξ, WilkiesDesign.E.atomDeg ψ ≤ (Work.WilE5.profD Me p q σ.B.length).eval X.deg) ∧
      (∀ ψ ∈ σ.ν, WilkiesDesign.E.atomDeg ψ ≤ (Work.WilE5.profD Me p q σ.B.length).eval X.deg) ∧
      σ.Φ.length ≤ (Work.WilE5.profN Me p q σ.B.length).eval X.deg ∧
      σ.Φ.length ≤ Work.WilE5.NPhi Me X.deg p q ∧
      (∀ ψ ∈ σ.Φ,
        Me.eval ((∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) + 2 * p +
          WilkiesDesign.E.atomDeg ψ) ≤ Work.WilE5.MlOf Me X.deg p q σ.B.length) ∧
      σ.ν.length ≤ X.deg + 2 * q + 1 := by
  intro k hk σ hσ
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨hB, hS, hd, hdΞ, hdν, hΞ, hΦ, hΦN, hMu, hν⟩ := levelP_dataInv X Me k hkq σ hσ
  refine ⟨?_, hd, hdΞ, hdν, hΦ, hΦN, ?_, ?_⟩
  · rw [Work.WilE5.Bounds.Bsum_eq_sum]; exact hS
  · intro ψ hψ
    have h := hMu ψ hψ
    rw [← Work.WilE5.Bounds.Bsum_eq_sum] at h
    exact h
  · omega

end Work.WilE5.Strat
