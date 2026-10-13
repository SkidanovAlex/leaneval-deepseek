/-
  WilE9 / Sharp — the *branch* of the pulled-back system.

  The pulled-back system `pbF` of `Sharp/PbSystem.lean` has, among its equations, the four
  algebraic ones (`y i - x i * w i`, `y i ^ 2 + w i ^ 2 - 1`, `τ - s * u`, `τ ^ 2 + u ^ 2 - 1`).
  This file proves what they force on a solution `Φ` of the whole system: eventually near a point
  `x₀` at which the auxiliary coordinates `w i = Φ x (fW n m i)` and `u = Φ x (fU n m)` are
  *positive*, `Φ` is the canonical ψ-branch

      `Φ x (fY n m i) = ψ (x i)`,  `Φ x (fW n m i) = psig (x i)`,  `Φ x (fT n m) = ψ (Φ x (fS n m))`.

  The proof is the classical one: `y = x·w` and `y² + w² = 1` give `w² (1 + x²) = 1`, and
  `psig x² (1 + x²) = 1`, so `w = ±psig x`; positivity selects the branch.  Same for `(τ, u)`
  over `s`.  The only analysis is that `Φ` is continuous at `x₀` (`ContDiffAt`), so the
  positivity `hw`, `hu` at `x₀` persists in a neighbourhood.

  Implementation note: the ambient dimension of the pulled-back system is the *definition*
  `Npb n m = n + qpb n m`, so a term of the form `eaEval c P (Fin.append x y)` is not
  type-correct at `implicit` transparency, and the keyed matchers of `rw`/`simp` refuse to
  rewrite inside it.  We therefore evaluate the four equations of `pbF` in the *clean* context
  of an arbitrary ambient point `z : Fin (Npb n m) → ℝ` (`eaEval_pbF_f*`), transport the
  solution equation along that identity, and only then read the coordinates of the appended
  point off with the `append_pb*` lemmas (whose statements contain metavariables, so they match
  by unification).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.circle_branch

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E
open Classical Filter Topology

/-! ## Reading the appended point at the named coordinates -/

@[simp] theorem append_pbX {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbX n m i) = x i := by
  rw [show pbX n m i = Fin.castAdd (qpb n m) i from rfl, Fin.append_left]

@[simp] theorem append_pbS {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbS n m) = y (fS n m) := by
  rw [← natAdd_fS, Fin.append_right]

@[simp] theorem append_pbY {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbY n m i) = y (fY n m i) := by
  rw [← natAdd_fY, Fin.append_right]

@[simp] theorem append_pbW {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbW n m i) = y (fW n m i) := by
  rw [← natAdd_fW, Fin.append_right]

@[simp] theorem append_pbT {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbT n m) = y (fT n m) := by
  rw [← natAdd_fT, Fin.append_right]

@[simp] theorem append_pbU {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbU n m) = y (fU n m) := by
  rw [← natAdd_fU, Fin.append_right]

/-! ## The four branches of the definition of `pbF` -/

theorem pbF_fS {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) :
    pbF n m r h (fS n m) =
      ((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbS n m)) * MvPolynomial.X (Sum.inl (pbU n m))) := by
  rw [pbF]
  rw [dif_pos (show ((fS n m : Fin (qpb n m)) : ℕ) = 0 from rfl)]

theorem pbF_fY {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) :
    pbF n m r h (fY n m i) =
      ((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbX n m i)) * MvPolynomial.X (Sum.inl (pbW n m i))) := by
  rw [pbF]
  rw [dif_neg (by simp only [fY]; omega), dif_pos (by simp only [fY]; omega)]
  refine congrArg (fun i' : Fin n => (MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)
    - MvPolynomial.X (Sum.inl (pbX n m i')) * MvPolynomial.X (Sum.inl (pbW n m i'))) ?_
  apply Fin.ext
  simp only [fY, Fin.val_mk]
  omega

theorem pbF_fW {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) :
    pbF n m r h (fW n m i) =
      (((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbW n m i))) ^ 2 - 1) := by
  rw [pbF]
  rw [dif_neg (by simp only [fW]; omega), dif_neg (by simp only [fW]; omega),
    dif_pos (by simp only [fW]; omega)]
  refine congrArg (fun i' : Fin n =>
    ((MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)) ^ 2
      + (MvPolynomial.X (Sum.inl (pbW n m i'))) ^ 2 - 1) ?_
  apply Fin.ext
  simp only [fW, Fin.val_mk]
  omega

theorem pbF_fT {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) :
    pbF n m r h (fT n m) =
      (((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbU n m))) ^ 2 - 1) := by
  rw [pbF]
  rw [dif_neg (by simp only [fT]; omega), dif_neg (by simp only [fT]; omega),
    dif_neg (by simp only [fT]; omega), dif_pos (by simp only [fT])]

/-! ## Evaluating the four branches at an ambient point -/

theorem eaEval_pbF_fS {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fS n m)) z
      = z (pbT n m) - z (pbS n m) * z (pbU n m) := by
  rw [pbF_fS]
  simp only [eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    Sum.elim_inl]

theorem eaEval_pbF_fY {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fY n m i)) z
      = z (pbY n m i) - z (pbX n m i) * z (pbW n m i) := by
  rw [pbF_fY]
  simp only [eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    Sum.elim_inl]

theorem eaEval_pbF_fW {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fW n m i)) z
      = z (pbY n m i) ^ 2 + z (pbW n m i) ^ 2 - 1 := by
  rw [pbF_fW]
  simp only [eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, Sum.elim_inl, map_one, MvPolynomial.eval_C]

theorem eaEval_pbF_fT {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fT n m)) z
      = z (pbT n m) ^ 2 + z (pbU n m) ^ 2 - 1 := by
  rw [pbF_fT]
  simp only [eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, Sum.elim_inl, map_one, MvPolynomial.eval_C]

/-! ## The four equations satisfied by a solution -/

theorem pbF_sol_eqs {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ)
    (hz : ∀ j : Fin (qpb n m), eaEval (pbChain c) (pbF n m r h j) (Fin.append x y) = 0) :
    (y (fT n m) = y (fS n m) * y (fU n m)) ∧
    (∀ i : Fin n, y (fY n m i) = x i * y (fW n m i)) ∧
    (∀ i : Fin n, y (fY n m i) ^ 2 + y (fW n m i) ^ 2 = 1) ∧
    (y (fT n m) ^ 2 + y (fU n m) ^ 2 = 1) := by
  have keyS : eaEval (pbChain c) (pbF n m r h (fS n m)) (Fin.append x y)
      = (Fin.append x y) (pbT n m)
        - (Fin.append x y) (pbS n m) * (Fin.append x y) (pbU n m) :=
    eaEval_pbF_fS c h (Fin.append x y)
  have keyY : ∀ i : Fin n, eaEval (pbChain c) (pbF n m r h (fY n m i)) (Fin.append x y)
      = (Fin.append x y) (pbY n m i)
        - (Fin.append x y) (pbX n m i) * (Fin.append x y) (pbW n m i) :=
    fun i => eaEval_pbF_fY c h i (Fin.append x y)
  have keyW : ∀ i : Fin n, eaEval (pbChain c) (pbF n m r h (fW n m i)) (Fin.append x y)
      = (Fin.append x y) (pbY n m i) ^ 2 + (Fin.append x y) (pbW n m i) ^ 2 - 1 :=
    fun i => eaEval_pbF_fW c h i (Fin.append x y)
  have keyT : eaEval (pbChain c) (pbF n m r h (fT n m)) (Fin.append x y)
      = (Fin.append x y) (pbT n m) ^ 2 + (Fin.append x y) (pbU n m) ^ 2 - 1 :=
    eaEval_pbF_fT c h (Fin.append x y)
  have hS : y (fT n m) - y (fS n m) * y (fU n m) = 0 := by
    have h1 := keyS ▸ hz (fS n m)
    rw [append_pbT, append_pbS, append_pbU] at h1
    exact h1
  have hT : y (fT n m) ^ 2 + y (fU n m) ^ 2 - 1 = 0 := by
    have h1 := keyT ▸ hz (fT n m)
    rw [append_pbT, append_pbU] at h1
    exact h1
  have hY : ∀ i : Fin n, y (fY n m i) - x i * y (fW n m i) = 0 := fun i => by
    have h1 := keyY i ▸ hz (fY n m i)
    rw [append_pbY, append_pbX, append_pbW] at h1
    exact h1
  have hW : ∀ i : Fin n, y (fY n m i) ^ 2 + y (fW n m i) ^ 2 - 1 = 0 := fun i => by
    have h1 := keyW i ▸ hz (fW n m i)
    rw [append_pbY, append_pbW] at h1
    exact h1
  exact ⟨sub_eq_zero.mp hS, fun i => sub_eq_zero.mp (hY i),
    fun i => sub_eq_zero.mp (hW i), sub_eq_zero.mp hT⟩

theorem pbF_branch {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r)
    (Φ : (Fin n → ℝ) → (Fin (Work.WilE9.Sharp.qpb n m) → ℝ)) (x₀ : Fin n → ℝ)
    (hcd : ContDiffAt ℝ ⊤ Φ x₀)
    (hs : Work.WilE9.IsSoln (Work.WilE9.Sharp.pbChain c) (Work.WilE9.Sharp.pbF n m r h) Φ x₀)
    (hw : ∀ i : Fin n, 0 < Φ x₀ (Work.WilE9.Sharp.fW n m i))
    (hu : 0 < Φ x₀ (Work.WilE9.Sharp.fU n m)) :
    ∀ᶠ x in nhds x₀,
      (∀ i : Fin n, Φ x (Work.WilE9.Sharp.fY n m i) = WilkiesDesign.E.psi (x i)) ∧
      (∀ i : Fin n, Φ x (Work.WilE9.Sharp.fW n m i) = Work.WilE9.psig (x i)) ∧
      Φ x (Work.WilE9.Sharp.fT n m) = WilkiesDesign.E.psi (Φ x (Work.WilE9.Sharp.fS n m)) := by
  have hcont : ContinuousAt Φ x₀ := hcd.continuousAt
  have hw_ev : ∀ᶠ x in 𝓝 x₀, ∀ i : Fin n, 0 < Φ x (fW n m i) := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply (fW n m i)).continuousAt.comp hcont).tendsto
      (isOpen_Ioi.mem_nhds (hw i))
  have hu_ev : ∀ᶠ x in 𝓝 x₀, 0 < Φ x (fU n m) :=
    ((continuous_apply (fU n m)).continuousAt.comp hcont).tendsto
      (isOpen_Ioi.mem_nhds hu)
  filter_upwards [hs.1, hw_ev, hu_ev] with x hx hwx hux
  obtain ⟨eS, eY, eW, eT⟩ := pbF_sol_eqs c h x (Φ x) hx
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · exact (circle_branch (hwx i) (eY i) (eW i)).2
  · exact (circle_branch (hwx i) (eY i) (eW i)).1
  · exact (circle_branch hux eS eT).2

end Work.WilE9.Sharp
