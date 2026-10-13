import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.ExFst.Defs
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.ExFst.exFst_pbF_zero
import Submission.Work.WilE9.Sharp.ExFst.exFst_pbF_branch
import Submission.Work.WilE9.Sharp.ExFst.exFst_sol_eq
import Submission.Work.WilE9.Sharp.ExFst.exFst_clearPbEval
import Submission.Work.WilE9.Sharp.pb_det_ne_zero
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Ift.ift_identity

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Work.WilE9.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## Helpers for the assembly -/

/-- `ψ a / psig a = a`: the `x`-coordinate recovered from the `(ψ, psig)`-pair. -/
theorem psi_div_psig (a : ℝ) : WilkiesDesign.E.psi a / Work.WilE9.psig a = a := by
  rw [(Work.WilE9.Psi.psi_psig_algebra a).1]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Work.WilE9.Psi.psig_pos a))

/-- Evaluating the determinant of a matrix of EA polynomials is taking the determinant of the
evaluated matrix. -/
theorem eaEval_det_fst {N Q r : ℕ} (c : EAChain N r) (M : Matrix (Fin Q) (Fin Q) (EAPoly N r))
    (z : Fin N → ℝ) : eaEval c M.det z = (M.map (fun P => eaEval c P z)).det := by
  have hmat : (MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))).mapMatrix M
      = M.map (fun P => eaEval c P z) := by
    ext i j
    rfl
  have h := RingHom.map_det (MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))) M
  rw [hmat] at h
  exact h

/-- The denominator `pbQ` of the pulled-back system, evaluated at a point: the determinant of the
evaluated fibre Jacobian. -/
theorem eaEval_pbQ {n m : ℕ} (E : EffStratum n m) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain E.X.c) (pbQ E.X.c E.h) z =
      ((Matrix.of fun (j l : Fin (qpb n m)) =>
          eaD (pbChain E.X.c) (Fin.natAdd n l) (pbF n m E.X.r E.h j)).map
        (fun P => eaEval (pbChain E.X.c) P z)).det :=
  eaEval_det_fst (pbChain E.X.c)
    (Matrix.of fun (j l : Fin (qpb n m)) =>
      eaD (pbChain E.X.c) (Fin.natAdd n l) (pbF n m E.X.r E.h j)) z

/-- Eventual equality of functions gives eventual equality of all iterated directional
derivatives. -/
theorem glDeriv_eventuallyEq {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : g =ᶠ[nhds x] f) (L : List (Fin n)) : glDeriv L g =ᶠ[nhds x] glDeriv L f := by
  induction L with
  | nil => exact h
  | cons i L ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    simp only [glDeriv]
    rw [hy]

/-- The circle equation `X a ^ 2 + X b ^ 2 - 1` at a point of the extended ambient. -/
theorem eaEval_circle {n m r : ℕ} (c : EAChain (Next n m) r) (a b : Fin (Next n m))
    (z : Fin (Next n m) → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl a) ^ 2 + MvPolynomial.X (Sum.inl b) ^ 2 - 1) z =
      z a ^ 2 + z b ^ 2 - 1 := by
  simp only [eaEval, map_add, map_sub, map_pow, map_one, MvPolynomial.eval_X, Sum.elim_inl]

/-- The value of `eaEval` at a variable of the extended ambient. -/
theorem eaEval_X_inl_fst {n m r : ℕ} (c : EAChain (Next n m) r) (a : Fin (Next n m))
    (z : Fin (Next n m) → ℝ) : eaEval c (MvPolynomial.X (Sum.inl a)) z = z a := by
  simp only [eaEval, MvPolynomial.eval_X, Sum.elim_inl]

/-- The cleared output equation `exEq6`, evaluated. -/
theorem eaEval_exEq6 {n m : ℕ} (E : EffStratum n m) (L : List (Fin n))
    (z : Fin (Next n m) → ℝ) :
    eaEval (exChain E.X.c) (exEq6 E.X.c E.h L) z =
      z (exSig n m) * eaEval (exChain E.X.c) (exQ E.X.c E.h L) z -
        z (exV n m) * eaEval (exChain E.X.c) (exP E.X.c E.h L) z := by
  simp only [exEq6, eaEval, map_sub, map_mul, MvPolynomial.eval_X, Sum.elim_inl]

/-! ## The forward direction of the extended system -/

theorem exSemiPf_fst_gen {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hQ : ∀ z ∈ Q, ∀ᶠ z' in nhds z,
      (∀ a, WilkiesDesign.E.eaEval E.X.c (E.h a) z' = 0) → z' ∈ Q)
    (hπ : ∀ w ∈ Q, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (x : Fin n → ℝ) (w : Fin (n + (1 + m)) → ℝ) (hw : w ∈ E.X.set)
    (hwQ : w ∈ Q)
    (hbase : Work.WilE9.Sharp.stratProj w =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (f x))) :
    ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc (WilkiesDesign.E.psiV x)
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)) ∧
      Work.WilE9.Sharp.exStrat z ∈ Q := by
  classical
  -- the output value and the extended point
  set σ : ℝ := Work.WilE9.glDeriv L f x with hσ
  set z : Fin (Next n m) → ℝ := exPt w x (f x) σ with hz
  have hY : ∀ i : Fin n, wY w i = WilkiesDesign.E.psi (x i) := wY_of_hbase hbase
  have hT : wTau w = WilkiesDesign.E.psi (f x) := wTau_of_hbase hbase
  -- coordinates of the extended point
  have hzY : ∀ i : Fin n, z (exY n m i) = WilkiesDesign.E.psi (x i) := by
    intro i; rw [hz, exPt_exY, hY i]
  have hzW : ∀ i : Fin n, z (exW n m i) = Work.WilE9.psig (x i) := by
    intro i; rw [hz, exPt_exW]
  have hzSig : z (exSig n m) = WilkiesDesign.E.psi σ := by rw [hz, exPt_exSig]
  have hzV : z (exV n m) = Work.WilE9.psig σ := by rw [hz, exPt_exV]
  have hzTau : z (exT n m) = WilkiesDesign.E.psi (f x) := by rw [hz, exPt_exT, hT]
  have hzU : z (exU n m) = Work.WilE9.psig (f x) := by rw [hz, exPt_exU]
  have hzA : ∀ a : Fin m, z (exA n m a) = wAux w a := by intro a; rw [hz, exPt_exA]
  have hzStr : exStrat z = w := by rw [hz, exStrat_exPt]
  -- the reconstructed pulled-back point
  have hzzX : ∀ i : Fin n, exSub z (pbX n m i) = x i := by
    intro i
    rw [exSub_pbX, hz, exPt_exY, exPt_exW, hY i, psi_div_psig]
  have hexb : exBase z = x := by
    funext i
    rw [exBase_apply]
    exact (exSub_pbX z i).symm.trans (hzzX i)
  have hzz_append : Fin.append x (exFib z) = exSub z := by
    rw [exSub_eq_append, hexb]
  have hstr : pbStrat (Fin.append x (exFib z)) = w := by
    rw [hzz_append, pbStrat_exSub, hzStr]
  -- the pulled-back system vanishes there
  have hF0 : ∀ j : Fin (qpb n m),
      eaEval (pbChain E.X.c) (pbF n m E.X.r E.h j) (Fin.append x (exFib z)) = 0 := by
    intro j
    rw [hzz_append]
    exact Work.WilE9.Sharp.ExFst.exFst_pbF_zero (n := n) (m := m) (x := x) (w := w)
      E hgood hw (f x) σ hbase j
  -- its fibre Jacobian is invertible
  have hfibY : ∀ i : Fin n, exFib z (fY n m i) = x i * exFib z (fW n m i) := by
    intro i
    rw [exFib_fY, exFib_fW, hz, exPt_exY, exPt_exW, hY i]
    exact (Work.WilE9.Psi.psi_psig_algebra (x i)).1
  have hfibW : ∀ i : Fin n, exFib z (fW n m i) ≠ 0 := by
    intro i
    rw [exFib_fW, hz, exPt_exW]
    exact ne_of_gt (Work.WilE9.Psi.psig_pos (x i))
  have hfibU : exFib z (fU n m) ≠ 0 := by
    rw [exFib_fU, hz, exPt_exU]
    exact ne_of_gt (Work.WilE9.Psi.psig_pos (f x))
  have hPdet : (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
      eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a))
        (pbStrat (Fin.append x (exFib z)))).det ≠ 0 := by
    rw [hstr]
    exact (hgood w hw).2.1
  have hdet := pb_det_ne_zero (n := n) (m := m) (r := E.X.r) E.X.c E.h x (exFib z)
    hfibY hfibW hfibU hPdet
  -- the implicit-function solution of the pulled-back system
  obtain ⟨Y, hYx, hYsmooth, hIsSoln⟩ :=
    Work.WilE9.Ift.ift_exists (n := n) (q := qpb n m) (r := E.X.r)
      (pbChain E.X.c) (pbF n m E.X.r E.h) x (exFib z) hF0 hdet
  have hQne : ∀ᶠ x' in nhds x, eaEval (pbChain E.X.c)
      (pbQ E.X.c E.h) (Fin.append x' (Y x')) ≠ 0 := by
    filter_upwards [hIsSoln.2] with x' hx'
    rw [eaEval_pbQ E (Fin.append x' (Y x'))]
    exact hx'
  have hident := Work.WilE9.Ift.ift_identity (n := n) (q := qpb n m) (r := E.X.r)
    (pbChain E.X.c) (pbF n m E.X.r E.h) (fS n m) Y x hYsmooth hIsSoln hQne L
  -- the solution's `s`-coordinate is `f`
  have hYposW : ∀ i : Fin n, 0 < Y x (fW n m i) := by
    intro i
    rw [hYx, exFib_fW, hz, exPt_exW]
    exact Work.WilE9.Psi.psig_pos (x i)
  have hYposU : 0 < Y x (fU n m) := by
    rw [hYx, exFib_fU, hz, exPt_exU]
    exact Work.WilE9.Psi.psig_pos (f x)
  have hbr := Work.WilE9.Sharp.ExFst.exFst_pbF_branch (n := n) (m := m) (r := E.X.r)
    (c := E.X.c) (h := E.h) (Φ := Y) (x₀ := x)
    hYsmooth hIsSoln hYposW hYposU
  have hbr2 : ∀ᶠ x' in nhds x,
      (∀ i : Fin n, Y x' (fY n m i) = WilkiesDesign.E.psi (x' i)) ∧
      Y x' (fT n m) = WilkiesDesign.E.psi (Y x' (fS n m)) := by
    filter_upwards [hbr] with x' hx'
    exact ⟨hx'.1, hx'.2.2.1⟩
  have hYf : ∀ᶠ x' in nhds x, Y x' (fS n m) = f x' :=
    Work.WilE9.Sharp.ExFst.exFst_sol_eq (n := n) (m := m) (f := f) (Zset := Z) (x := x) (w := w)
      hZ E hgood Q hQ hπ hw hwQ hbase σ Y hYsmooth.continuousAt hYx hbr2 hIsSoln.1
  have hgl : glDeriv L (fun x' => Y x' (fS n m)) x = Work.WilE9.glDeriv L f x :=
    (glDeriv_eventuallyEq hYf L).self_of_nhds
  -- BNZ's formula at the reconstructed point
  have hpt : Fin.append x (Y x) = exSub z := by
    rw [hYx]; exact hzz_append
  have hderiv : eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z)
      = σ * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length) := by
    have h := hident
    rw [hpt, hgl, ← hσ] at h
    exact h
  -- the cleared equation
  have hdenS : ∀ b : Fin (n + 1), z (sDen n m b) ≠ 0 := by
    intro b
    by_cases hb : (b : ℕ) < n
    · rw [sDen_of_lt hb, hz, exPt_exW]
      exact ne_of_gt (Work.WilE9.Psi.psig_pos _)
    · rw [sDen_of_not_lt hb, hz, exPt_exU]
      exact ne_of_gt (Work.WilE9.Psi.psig_pos _)
  have hell : ∀ j : Fin E.X.r, (pbChain E.X.c).ell j (exSub z) = (exChain E.X.c).ell j z := by
    intro j
    rw [Work.WilE9.Sharp.pbChain_ell, pbStrat_exSub, Work.WilE9.Sharp.exChain_ell]
  have hKQ : ((pbQ E.X.c E.h) ^ (2 * L.length)).totalDegree ≤ exK E.X.c E.h L := by
    rw [exK]
    exact le_trans (le_max_left _ _) (Nat.le_succ _)
  have hKP : (pbP E.X.c E.h L).totalDegree ≤ exK E.X.c E.h L := by
    rw [exK]
    exact le_trans (le_max_right _ _) (Nat.le_succ _)
  have hclearQ : eaEval (exChain E.X.c) (exQ E.X.c E.h L) z
      = (∏ b : Fin (n + 1), z (sDen n m b)) ^ exK E.X.c E.h L
        * eaEval (pbChain E.X.c) ((pbQ E.X.c E.h) ^ (2 * L.length)) (exSub z) :=
    Work.WilE9.Sharp.ExFst.exFst_clearPbEval (c := E.X.c) (K := exK E.X.c E.h L)
      (P := (pbQ E.X.c E.h) ^ (2 * L.length)) hKQ z hell hdenS
  have hclearP : eaEval (exChain E.X.c) (exP E.X.c E.h L) z
      = (∏ b : Fin (n + 1), z (sDen n m b)) ^ exK E.X.c E.h L
        * eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z) :=
    Work.WilE9.Sharp.ExFst.exFst_clearPbEval (c := E.X.c) (K := exK E.X.c E.h L)
      (P := pbP E.X.c E.h L) hKP z hell hdenS
  have hEq6 : eaEval (exChain E.X.c) (exEq6 E.X.c E.h L) z = 0 := by
    have hpow : eaEval (pbChain E.X.c) ((pbQ E.X.c E.h) ^ (2 * L.length)) (exSub z)
        = (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length) := by
      simp only [eaEval, map_pow]
    rw [eaEval_exEq6, hzSig, hzV, hclearQ, hclearP, hpow, hderiv,
      (Work.WilE9.Psi.psi_psig_algebra σ).1]
    ring
  -- the assembly
  obtain ⟨hwcube, B₀, hB₀mem, hB₀⟩ := hw
  refine ⟨z, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [hz]
      exact exPt_mem_cube x (f x) σ hwcube
    · change ∃ B ∈ E.X.basics.map (exBasic E.X.c E.h L), B.holds (exChain E.X.c) z
      refine ⟨exBasic E.X.c E.h L B₀, List.mem_map.mpr ⟨B₀, hB₀mem, rfl⟩, ?_, ?_⟩
      · intro g hg
        change eaEval (exChain E.X.c) g z = 0
        dsimp only [exBasic] at hg
        rcases List.mem_append.mp hg with hg | hg
        · simp only [exEqList, List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton,
            List.mem_finRange, List.not_mem_nil, false_or, or_false, true_and, and_true, or_assoc] at hg
          rcases hg with ⟨i, hi⟩ | h2 | ⟨a, ha⟩ | h4 | h5
          · rw [← hi, eaEval_circle, hzY i, hzW i, Work.WilE9.Psi.psi_sq_add_psig_sq]
            ring
          · rw [h2, eaEval_circle, hzTau, hzU, Work.WilE9.Psi.psi_sq_add_psig_sq]
            ring
          · rw [← ha, eaEval_exRaise, hzStr]
            exact (hgood w ⟨hwcube, B₀, hB₀mem, hB₀⟩).1 a
          · rw [h4, eaEval_circle, hzSig, hzV, Work.WilE9.Psi.psi_sq_add_psig_sq]
            ring
          · rw [h5]
            exact hEq6
        · obtain ⟨P, hP, hP2⟩ := List.mem_map.mp hg
          rw [← hP2, eaEval_exRaise, hzStr]
          exact hB₀.1 P hP
      · intro g hg
        change 0 < eaEval (exChain E.X.c) g z
        dsimp only [exBasic] at hg
        rcases List.mem_append.mp hg with hg | hg
        · simp only [exPosList, List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map,
            List.mem_finRange, List.not_mem_nil, false_or, or_false, true_and, and_true, or_assoc] at hg
          rcases hg with ⟨i, hi⟩ | h2 | h4
          · rw [← hi, eaEval_X_inl_fst, hzW i]
            exact Work.WilE9.Psi.psig_pos (x i)
          · rw [h2, eaEval_X_inl_fst, hzU]
            exact Work.WilE9.Psi.psig_pos (f x)
          · rw [h4, eaEval_X_inl_fst, hzV]
            exact Work.WilE9.Psi.psig_pos σ
        · obtain ⟨P, hP, hP2⟩ := List.mem_map.mp hg
          rw [← hP2, eaEval_exRaise, hzStr]
          exact hB₀.2 P hP
  · rw [hz]
    exact exOut_exPt (w := w) (x := x) (sval := f x) (σ := σ) hY
  · rw [hzStr]; exact hwQ

/-- The unrestricted forward direction, the instance `Q = E.X.set` of `exSemiPf_fst_gen`. -/
theorem exSemiPf_fst {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (hπ : ∀ w ∈ E.X.set, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (x : Fin n → ℝ) (w : Fin (n + (1 + m)) → ℝ) (hw : w ∈ E.X.set)
    (hbase : Work.WilE9.Sharp.stratProj w =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (f x))) :
    ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc (WilkiesDesign.E.psiV x)
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)) := by
  obtain ⟨z, hz, hout, -⟩ :=
    exSemiPf_fst_gen hZ E hgood E.X.set (fun w hw => (hgood w hw).2.2) hπ L x w hw hw hbase
  exact ⟨z, hz, hout⟩

end Work.WilE9.Sharp
