/-
  WilE9 / Sharp — auxiliary lemmas for the soundness of the extended set (`exSemiPf_snd`).

  Everything here is unconditional; the inputs are the extended ambient point `z` and the (few)
  structural facts that `z ∈ exSemiPf.set` provides.  The content is

  * `eaEval` of the elementary monomials and of `det` (`eaEval_det`), and the eventual-equality
    lemma for `glDeriv` (the iterated derivative only sees a neighbourhood);
  * the membership lemmas for the equation/inequality lists `exEqList`, `exPosList` of the
    extended basic condition;
  * `pbF_at_exSub`: the equations of the *pulled-back* system hold at the reconstructed point
    `exSub z` as soon as the corresponding equations of the extended system hold;
  * `soln_h_eq`: along any implicit solution of the pulled-back system, the stratum's own
    equations vanish at the stratum coordinates;
  * the index/evaluation lemmas `eaEval_pbF_*` for the named fibre coordinates.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.psig_pos
import Submission.Work.WilE9.Sharp.psig_psiInv_of_sq
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Sharp.eaEval_pbRaise

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open WilkiesDesign WilkiesDesign.E Filter MvPolynomial
namespace Work.WilE9.Sharp

/-! ## Evaluation of `eaEval` on the elementary pieces -/

@[simp] theorem eaEval_X_inl {N r : ℕ} (c : EAChain N r) (l : Fin N) (w : Fin N → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl l)) w = w l := by
  simp [eaEval]

@[simp] theorem eaEval_sub {N r : ℕ} (c : EAChain N r) (P Q : EAPoly N r) (w : Fin N → ℝ) :
    eaEval c (P - Q) w = eaEval c P w - eaEval c Q w := by simp [eaEval]

@[simp] theorem eaEval_add {N r : ℕ} (c : EAChain N r) (P Q : EAPoly N r) (w : Fin N → ℝ) :
    eaEval c (P + Q) w = eaEval c P w + eaEval c Q w := by simp [eaEval]

@[simp] theorem eaEval_mul {N r : ℕ} (c : EAChain N r) (P Q : EAPoly N r) (w : Fin N → ℝ) :
    eaEval c (P * Q) w = eaEval c P w * eaEval c Q w := by simp [eaEval]

@[simp] theorem eaEval_pow {N r : ℕ} (c : EAChain N r) (P : EAPoly N r) (k : ℕ)
    (w : Fin N → ℝ) : eaEval c (P ^ k) w = eaEval c P w ^ k := by simp [eaEval]

@[simp] theorem eaEval_one {N r : ℕ} (c : EAChain N r) (w : Fin N → ℝ) :
    eaEval c (1 : EAPoly N r) w = 1 := by simp [eaEval]

/-- The ring homomorphism underlying `eaEval`. -/
def eaEvR {N r : ℕ} (c : EAChain N r) (w : Fin N → ℝ) : EAPoly N r →+* ℝ :=
  MvPolynomial.eval (Sum.elim w (fun j => Real.exp (c.ell j w)))

theorem eaEvR_apply {N r : ℕ} (c : EAChain N r) (w : Fin N → ℝ) (P : EAPoly N r) :
    eaEvR c w P = eaEval c P w := rfl

/-- Evaluation commutes with `Matrix.det`. -/
theorem eaEval_det {N r q : ℕ} (c : EAChain N r) (A : Matrix (Fin q) (Fin q) (EAPoly N r))
    (w : Fin N → ℝ) :
    eaEval c A.det w = (A.map (fun P => eaEval c P w)).det := by
  have h := RingHom.map_det (eaEvR c w) A
  have h2 : (eaEvR c w).mapMatrix A = A.map (fun P => eaEval c P w) := by
    ext i j; rfl
  rw [h2] at h
  exact h

/-! ## `glDeriv` only sees a neighbourhood -/

theorem EventuallyEq.eventually_nhds {α β : Type*} [TopologicalSpace α] {u v : α → β}
    {x₀ : α} (h : u =ᶠ[nhds x₀] v) : ∀ᶠ x in nhds x₀, u =ᶠ[nhds x] v := by
  obtain ⟨t, ht_sub, ht_open, ht_mem⟩ :=
    mem_nhds_iff.mp (show {y | u y = v y} ∈ nhds x₀ from h)
  filter_upwards [ht_open.mem_nhds ht_mem] with x hx
  exact Filter.mem_of_superset (ht_open.mem_nhds hx) ht_sub

theorem glDeriv_congr {n : ℕ} (L : List (Fin n)) {u v : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (h : u =ᶠ[nhds x₀] v) : Work.WilE9.glDeriv L u x₀ = Work.WilE9.glDeriv L v x₀ := by
  induction L generalizing x₀ with
  | nil => exact h.self_of_nhds
  | cons i L ih =>
      have hfun : (fun x => Work.WilE9.glDeriv L u x) =ᶠ[nhds x₀]
          (fun x => Work.WilE9.glDeriv L v x) := by
        filter_upwards [EventuallyEq.eventually_nhds h] with x hx
        exact ih hx
      simp only [Work.WilE9.glDeriv]
      rw [Filter.EventuallyEq.fderiv_eq hfun]

/-! ## Membership in the equation and inequality lists of the extended basic condition -/

lemma mem_exEqList_yw {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) (i : Fin n) :
    (MvPolynomial.X (Sum.inl (exY n m i)) ^ 2 + MvPolynomial.X (Sum.inl (exW n m i)) ^ 2 - 1)
      ∈ exEqList c h L := by
  simp only [exEqList, List.mem_append, List.mem_map, List.mem_singleton, List.mem_finRange,
    true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))

lemma mem_exEqList_tu {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    (MvPolynomial.X (Sum.inl (exT n m)) ^ 2 + MvPolynomial.X (Sum.inl (exU n m)) ^ 2 - 1)
      ∈ exEqList c h L := by
  simp only [exEqList, List.mem_append, List.mem_map, List.mem_singleton, List.mem_finRange,
    true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inr trivial)))

lemma mem_exEqList_sv {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    (MvPolynomial.X (Sum.inl (exSig n m)) ^ 2 + MvPolynomial.X (Sum.inl (exV n m)) ^ 2 - 1)
      ∈ exEqList c h L := by
  simp only [exEqList, List.mem_append, List.mem_map, List.mem_singleton, List.mem_finRange,
    true_and]
  exact Or.inl (Or.inr trivial)

lemma mem_exEqList_h {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) (a : Fin (1 + m)) :
    exRaise (h a) ∈ exEqList c h L := by
  simp only [exEqList, List.mem_append, List.mem_map, List.mem_singleton, List.mem_finRange,
    true_and]
  exact Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))

lemma mem_exEqList_eq6 {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    exEq6 c h L ∈ exEqList c h L := by
  simp only [exEqList, List.mem_append, List.mem_map, List.mem_singleton, List.mem_finRange,
    true_and]
  exact Or.inr trivial

lemma mem_exPosList_w {n m r : ℕ} (B : Basic (n + (1 + m)) r) (i : Fin n) :
    MvPolynomial.X (Sum.inl (exW n m i)) ∈ exPosList (n := n) (m := m) (r := r) B := by
  simp only [exPosList, List.mem_append, List.mem_map, List.mem_finRange, List.mem_cons, true_and]
  exact Or.inl (Or.inl ⟨i, rfl⟩)

lemma mem_exPosList_u {n m r : ℕ} (B : Basic (n + (1 + m)) r) :
    MvPolynomial.X (Sum.inl (exU n m)) ∈ exPosList (n := n) (m := m) (r := r) B := by
  simp only [exPosList, List.mem_append, List.mem_map, List.mem_finRange, List.mem_cons, true_and]
  exact Or.inl (Or.inr (Or.inl trivial))

lemma mem_exPosList_v {n m r : ℕ} (B : Basic (n + (1 + m)) r) :
    MvPolynomial.X (Sum.inl (exV n m)) ∈ exPosList (n := n) (m := m) (r := r) B := by
  simp only [exPosList, List.mem_append, List.mem_map, List.mem_finRange, List.mem_cons, true_and]
  exact Or.inl (Or.inr (Or.inr (Or.inl trivial)))

lemma mem_exPosList_pos {n m r : ℕ} (B : Basic (n + (1 + m)) r) {q : EAPoly (n + (1 + m)) r}
    (hq : q ∈ B.pos) : exRaise q ∈ exPosList (n := n) (m := m) (r := r) B := by
  simp only [exPosList, List.mem_append, List.mem_map, List.mem_finRange, List.mem_cons, true_and]
  exact Or.inr ⟨q, hq, rfl⟩

/-- The equation list of `exBasic` is the extended list followed by the raised equations. -/
theorem exBasic_eqs {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) (B0 : Basic (n + (1 + m)) r) :
    (exBasic c h L B0).eqs
      = exEqList c h L ++ B0.eqs.map (exRaise (n := n) (m := m) (r := r)) := rfl

/-- The inequality list of `exBasic` is `exPosList`. -/
theorem exBasic_pos {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) (B0 : Basic (n + (1 + m)) r) :
    (exBasic c h L B0).pos = exPosList (n := n) (m := m) (r := r) B0 := rfl

/-- The denominators `sDen b` never vanish when the `w` and `u` coordinates do not. -/
theorem sDen_ne_zero {n m : ℕ} (z : Fin (Next n m) → ℝ)
    (hw : ∀ i, z (exW n m i) ≠ 0) (hu : z (exU n m) ≠ 0) (b : Fin (n + 1)) :
    z (sDen n m b) ≠ 0 := by
  by_cases hb : (b : ℕ) < n
  · rw [sDen, dif_pos hb]; exact hw _
  · rw [sDen, dif_neg hb]; exact hu

/-! ## The pulled-back equations at `exSub z` -/

theorem pbF_at_exSub {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Next n m) → ℝ)
    (hw0 : ∀ i, z (exW n m i) ≠ 0) (hu0 : z (exU n m) ≠ 0)
    (hyw : ∀ i, z (exY n m i) ^ 2 + z (exW n m i) ^ 2 = 1)
    (htu : z (exT n m) ^ 2 + z (exU n m) ^ 2 = 1)
    (hstr : ∀ a, eaEval c (h a) (exStrat z) = 0) :
    ∀ j, eaEval (pbChain c) (pbF n m r h j) (exSub z) = 0 := by
  intro j
  rw [pbF]
  split_ifs with h0 h1 h2 h3
  · simp only [eaEval_sub, eaEval_mul, eaEval_X_inl, exSub_pbT, exSub_pbS, exSub_pbU]
    rw [div_mul_cancel₀ (z (exT n m)) hu0]
    ring
  · simp only [eaEval_sub, eaEval_mul, eaEval_X_inl, exSub_pbY, exSub_pbX, exSub_pbW]
    rw [div_mul_cancel₀ (z (exY n m ⟨(j : ℕ) - 1, by omega⟩)) (hw0 _)]
    ring
  · simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one, exSub_pbY,
      exSub_pbW]
    have hh := hyw (⟨(j : ℕ) - n - 1, by omega⟩ : Fin n)
    linarith
  · simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one, exSub_pbT,
      exSub_pbU]
    linarith [htu]
  · simp only [eaEval_pbRaise]
    rw [pbStrat_exSub]
    exact hstr (⟨(j : ℕ) - (2 * n + 2),
      by have := j.isLt; simp only [qpb] at this ⊢; omega⟩ : Fin (1 + m))

/-! ## The stratum's own equations along a solution of the pulled-back system -/

theorem eaEval_pbF_high {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (a : Fin (1 + m)) (w : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c)
        (pbF n m r h (⟨2 * n + 2 + a.val,
          by have := a.isLt; simp only [qpb]; omega⟩ : Fin (qpb n m))) w
      = eaEval c (h a) (pbStrat w) := by
  rw [pbF]
  split_ifs with h0 h1 h2 h3
  · have h0' : (2 * n + 2 + a.val : ℕ) = 0 := h0; omega
  · have h1' : (2 * n + 2 + a.val : ℕ) ≤ n := h1; omega
  · have h2' : (2 * n + 2 + a.val : ℕ) ≤ 2 * n := h2; omega
  · have h3' : (2 * n + 2 + a.val : ℕ) = 2 * n + 1 := h3; omega
  · rw [eaEval_pbRaise]
    have hX : (⟨(2 * n + 2 + a.val) - (2 * n + 2),
        by have := a.isLt; simp only [qpb] at *; omega⟩ : Fin (1 + m)) = a := by
      ext; simp only [Fin.val_mk]; omega
    rw [hX]

theorem soln_h_eq {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (Φ : (Fin n → ℝ) → (Fin (qpb n m) → ℝ)) (x₀ : Fin n → ℝ)
    (hs : Work.WilE9.IsSoln (pbChain c) (pbF n m r h) Φ x₀) :
    ∀ᶠ x in nhds x₀, ∀ a : Fin (1 + m),
      eaEval c (h a) (pbStrat (Fin.append x (Φ x))) = 0 := by
  filter_upwards [hs.1] with x hx
  intro a
  rw [← eaEval_pbF_high c h a (Fin.append x (Φ x))]
  exact hx (⟨2 * n + 2 + a.val, by have := a.isLt; simp only [qpb]; omega⟩ : Fin (qpb n m))

/-! ## Reading the stratum projection of the pulled-back point -/

/-- `stratProj` applied to a stratum point is the value at the corresponding raw index. -/
theorem stratProj_apply {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (i : Fin (n + 1)) :
    stratProj w i = w ⟨(i : ℕ), by have := i.isLt; omega⟩ := rfl

theorem sIdxPb_last {n m : ℕ} (i : Fin (n + (1 + m))) (hi : (i : ℕ) = n) :
    sIdxPb n m i = pbT n m := by
  simp only [sIdxPb]
  rw [dif_neg (by omega), dif_pos hi]

theorem sIdxPb_lt {n m : ℕ} (i : Fin (n + (1 + m))) (hi : (i : ℕ) < n) :
    sIdxPb n m i = pbY n m ⟨(i : ℕ), hi⟩ := by
  simp only [sIdxPb]
  rw [dif_pos hi]

theorem exY_eq_castAdd {n m : ℕ} (i : Fin n) :
    exY n m i = Fin.castAdd (n + m + 3) (Fin.castSucc i) := Fin.ext rfl

theorem exSig_eq_castAdd {n m : ℕ} :
    exSig n m = Fin.castAdd (n + m + 3) (Fin.last n) := Fin.ext rfl

/-- `stratProj` of the stratum coordinates of a pulled-back point is `Fin.snoc` of the `y`- and
`τ`-coordinates. -/
theorem stratProj_pbStrat {n m : ℕ} (p : Fin (n + qpb n m) → ℝ) :
    stratProj (pbStrat p) = Fin.snoc (fun i : Fin n => p (pbY n m i)) (p (pbT n m)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last, stratProj_apply]
    show pbStrat p ⟨(Fin.last n : ℕ), by omega⟩ = p (pbT n m)
    simp only [pbStrat]
    congr 1
    exact sIdxPb_last _ (by simp)
  · intro j
    rw [Fin.snoc_castSucc, stratProj_apply]
    show pbStrat p ⟨(Fin.castSucc j : ℕ), by omega⟩ = p (pbY n m j)
    simp only [pbStrat]
    congr 1
    exact sIdxPb_lt _ (by simpa using j.isLt)

/-! ## Small algebraic facts -/

/-- `y / psig (psiInv y) = psiInv y` on `(-1,1)`. -/
theorem div_psig_psiInv {y : ℝ} (hy : |y| < 1) :
    y / Work.WilE9.psig (Work.WilE9.psiInv y) = Work.WilE9.psiInv y := by
  have hpsi := Work.WilE9.Psi.psi_psiInv y hy
  have halg := (Work.WilE9.Psi.psi_psig_algebra (Work.WilE9.psiInv y)).2.2
  rw [halg, hpsi]
  rfl

/-- `|psi a| < 1`. -/
theorem abs_psi_lt_one (a : ℝ) : |WilkiesDesign.E.psi a| < 1 := by
  rw [WilkiesDesign.E.psi, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  exact (Real.lt_sqrt (abs_nonneg a)).2 (by rw [sq_abs]; linarith)

end Work.WilE9.Sharp
