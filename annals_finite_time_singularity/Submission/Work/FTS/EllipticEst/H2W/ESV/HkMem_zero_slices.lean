import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Helper A : `∂_θ^n` commutes with multiplication by the first variable -/

theorem pthIter_const_mul_fst (n : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => z * h z θ)
      = fun z θ => z * Work.Spaces.pthIter n h z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth, deriv_const_mul_field]

/-! ## Helper B : Clairaut for `∂_z` against `∂_θ²` -/

theorem pz_pthIter_two_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 g)))
      (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry g) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem hg hz ⟨hθ0, hθ1⟩
  have h2' : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.FTS.EllipticEst.DzAmgm.contDiffAt_two_of_mem (hg.pth) hz ⟨hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth g)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz g))) Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.Spaces.pz_pth_comm (h2 p hp)
  intro p hp
  have e2 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2 :=
    Work.Spaces.pz_pth_comm (h2' p hp)
  have e1 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz g)) p.1 p.2 :=
    Work.Spaces.pth_congr_of_isOpen (f := Work.Spaces.pz (Work.Spaces.pth g))
      (f' := Work.Spaces.pth (Work.Spaces.pz g)) Work.FTS.EllipticEst.isOpen_Q0 hEqOn hp
  show Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact e2.trans e1

/-! ## Helper C : `∂_θ²` commutes with `D_z` -/

theorem pthIter_two_Dz_eqOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  have h1 : Work.Spaces.pthIter 2 (Work.Spaces.Dz g) p.1 p.2
      = p.1 * Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2 := by
    rw [show Work.Spaces.Dz g = fun z θ => z * Work.Spaces.pz g z θ from rfl,
      pthIter_const_mul_fst]
  have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 g) p.1 p.2
      = Work.Spaces.pthIter 2 (Work.Spaces.pz g) p.1 p.2 := pz_pthIter_two_eqOn hg hp
  show Work.Spaces.pthIter 2 (Work.Spaces.Dz g) p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) p.1 p.2
  rw [h1]
  simp only [Work.Spaces.Dz]
  rw [← h2]

/-! ## Helper D : the requested commutation of `∂_θ²` with `D_z^j` -/

theorem pthIter_two_DzIter_comm (f : ℝ → ℝ → ℝ) (j : ℕ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      have hstep := (pthIter_two_Dz_eqOn (hf.DzIter j)).trans
        (Work.FTS.EllipticEst.DzAmgm.Q0_Dz_congr ih)
      simpa only [Work.Spaces.DzIter_succ] using hstep

/-! ## Helper E : `bslOp α Ψ` is `C^∞` on the open quadrant for `Ψ` merely `C^∞` there -/

theorem smoothOpen_bslOp_of_smoothOpen (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-! ## Helper F : the source of the weak class is `C^∞` on the open quadrant -/

theorem SmoothOpen_F_weak (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (smoothOpen_bslOp_of_smoothOpen α Ψ hΨso)
    (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)

/-! ## The target lemma -/

theorem HkMem_zero_slices (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j F) ∧
      Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
  intro j hj
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := SmoothOpen_F_weak α 2 F Ψ h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hQso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨso.pzIter 2)
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j F
      (hFso.DzIter j).continuousOn h.memF hj
  · refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      (g := Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul
        ((hΨso.DzIter j).pzIter 2)).continuousOn
    · intro z θ hz hθ0 hθ1
      have hE := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hΨso j 0
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
      simpa only [Function.uncurry_apply_pair, Work.Spaces.mixed_zero_right] using hE
    · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (hQso.DzIter j).continuousOn h.memA hj
  · refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_congr
      (g := Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
        (hΨso.DzIter j) 2).continuousOn
    · intro z θ hz hθ0 hθ1
      exact pthIter_two_DzIter_comm Ψ j hΨso
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
    · exact Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 j
        (Work.Spaces.pthIter 2 Ψ)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter j).continuousOn
        h.memB hj

end Work.FTS.EllipticEst.H2W
