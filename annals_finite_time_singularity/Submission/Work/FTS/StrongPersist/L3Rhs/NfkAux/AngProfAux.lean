import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000

/-! ## Smoothness helpers for `dthU` on an open interval

`dthU φ = sin(2·)·φ'`; on an open set it preserves `C^∞` and its iterates are additive.
These are the two local facts used to differentiate `aProf α`. -/

lemma contDiffOn_dthU_open {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU f) U := by
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) U :=
    hf.deriv_of_isOpen hU (by simp)
  have hsin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by
    fun_prop
  have h := hsin.mul hd
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.dthU]

lemma contDiffOn_dthU_iter_open {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (m : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] f) U := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [Function.iterate_succ_apply']; exact contDiffOn_dthU_open hU ih

/-- Additivity of the `dthU`-iterates on an open set. -/
lemma dthU_iter_add_eqOn {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (m : ℕ) :
    ∀ θ ∈ U, (Work.Spaces.dthU^[m] (f + g)) θ
      = (Work.Spaces.dthU^[m] f) θ + (Work.Spaces.dthU^[m] g) θ := by
  induction m with
  | zero => intro θ _; simp
  | succ m ih =>
      intro θ hθ
      have hfU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] f) U :=
        contDiffOn_dthU_iter_open hU hf m
      have hgU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] g) U :=
        contDiffOn_dthU_iter_open hU hg m
      have hdiff_f : DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
        (hfU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
      have hdiff_g : DifferentiableAt ℝ (Work.Spaces.dthU^[m] g) θ :=
        (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
      have hev : (Work.Spaces.dthU^[m] (f + g)) =ᶠ[𝓝 θ]
          (Work.Spaces.dthU^[m] f + Work.Spaces.dthU^[m] g) := by
        filter_upwards [hU.mem_nhds hθ] with x hx
        simp only [Pi.add_apply]
        exact ih x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      simp only [Work.Spaces.dthU_apply]
      rw [hev.deriv_eq, deriv_add hdiff_f hdiff_g]
      ring

/-- `Γ(θ) = (sin θ · cos²θ)^{α/3}` is `C^∞` on the open interval. -/
lemma contDiffOn_Gam_Ioo (α : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hbase : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Gam]

/-- The angular profile `aProf α` is `C^∞` on the open interval. -/
lemma contDiffOn_aProf (α : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => aProf α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hgam := contDiffOn_Gam_Ioo α
  have hdth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_dthU_open isOpen_Ioo hgam).congr (fun θ _ => rfl)
  have hsin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.sin θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    exact h1.mul hgam
  have hsum := hdth.add hsin
  have hfin := hsum.const_smul (-(α / Work.Spaces.c α))
  refine hfin.congr (fun θ _ => ?_)
  simp only [aProf, smul_eq_mul, Pi.add_apply]

/-- `dthU φ` vanishes at the two endpoints of `Iθ`, for every `φ`. -/
lemma dthU_zero_left (φ : ℝ → ℝ) : Work.Spaces.dthU φ 0 = 0 := by
  rw [Work.Spaces.dthU_apply, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul]

lemma dthU_zero_right (φ : ℝ → ℝ) : Work.Spaces.dthU φ (Real.pi / 2) = 0 := by
  rw [Work.Spaces.dthU_apply, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
    zero_mul]

end Work.FTS.StrongPersist.L3Rhs.NfkAux
