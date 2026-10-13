import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.MaximalPsi
import Submission.Work.WilE3.MPsi.Defs
import Submission.Work.WilE3.MPsi.good_points_instance
import Submission.Work.WilE3.MPsi.atomDeg_phiPen_le

namespace Work.WilE3.MPsi

open Classical Topology Filter
open WilkiesDesign.E

/-- Polynomial bookkeeping of the assembly (namespace `Work.WilE3.MPsi`): the threshold
`K_G.comp ((4(K_L+1)+2)·X + 1) + 1` evaluated at `n` really is
`K_G.eval ((4(K_L.eval n + 1) + 2)·n + 1) + 1`. -/
lemma eval_assemblyPoly (KG KL : Polynomial ℕ) (n : ℕ) :
    (KG.comp ((Polynomial.C 4 * (KL + 1) + Polynomial.C 2) * Polynomial.X + Polynomial.C 1)
      + Polynomial.C 1).eval n
      = KG.eval ((4 * (KL.eval n + 1) + 2) * n + 1) + 1 := by
  simp [Polynomial.eval_comp]

/-- **Assembly** (namespace `Work.WilE3.MPsi`): the maximal-`ψ` node follows from the effective
gradient inequality for single EA polynomials and the residual Łojasiewicz inequality for basic EA
sets (both PROVED in the workspace).

For `q := K_L.eval B.deg + 1` and `Φ = phiPen B (2q) = P·(P^{4q} − S)` the instance lemma
`Work.WilE3.MPsi.good_points_instance` gives points with the equations vanishing exactly and
`2·dist z y ^ κ < g z` for every `g ∈ B.pos`; the threshold is
`K := K_G.comp((4(K_L+1)+2)·X + 1) + 1`, and the two cases are `y ∈ B.holds` (take `z = y`) and
otherwise (`P(y) = 0`, so `Φ(y) = 0` and `hG` applies).

You may re-derive the elementary continuity facts (`∀ f ∈ B.eqs, eaEval c f y = 0` and
`∀ g ∈ B.pos, 0 ≤ eaEval c g y` follow from `y ∈ closure {x | B.holds c x}` by closedness) and the
trivial case inside this file; do not import `Work.WilE3.Taylor.maximalPsiNode` (it imports you). -/
theorem maximalPsiNode_of_grad_loj
    (hG : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
        (y : Fin k → ℝ), k + r ≤ F → eaEval c Φ y = 0 →
        ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧
          1 / (1 - κ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) ∧
          (∀ᶠ x in 𝓝 y, cst * |eaEval c Φ x| ^ κ ≤
            ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x‖))
    (hL : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval B.deg < q →
      Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
        {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y q) :
    ∀ F : ℕ, Work.WilE3.MaximalPsiNode F := by
  intro F
  obtain ⟨KG, hKG⟩ := hG F
  obtain ⟨KL, hKL⟩ := hL F
  refine ⟨KG.comp ((Polynomial.C 4 * (KL + 1) + Polynomial.C 2) * Polynomial.X + Polynomial.C 1)
      + Polynomial.C 1, ?_⟩
  intro k r c B y κ hkr hκ hy ε hε
  set KK : Polynomial ℕ :=
    KG.comp ((Polynomial.C 4 * (KL + 1) + Polynomial.C 2) * Polynomial.X + Polynomial.C 1)
      + Polynomial.C 1 with hKK
  have heval : KK.eval B.deg = KG.eval ((4 * (KL.eval B.deg + 1) + 2) * B.deg + 1) + 1 := by
    rw [hKK]; exact eval_assemblyPoly KG KL B.deg
  have hq : KL.eval B.deg < KL.eval B.deg + 1 := Nat.lt_succ_self _
  have hloj := hKL k r c B y (KL.eval B.deg + 1) hkr hq
  by_cases hholds : B.holds c y
  · -- Trivial case: `y` itself is a point of `B.holds`.
    refine ⟨y, by simpa using hε, ?_, ?_⟩
    · intro f hf
      rw [hholds.1 f hf, abs_zero, mul_zero]
      exact pow_nonneg dist_nonneg _
    · intro g hg
      have hκ0 : κ ≠ 0 := by omega
      rw [dist_self, zero_pow hκ0, mul_zero]
      exact hholds.2 g hg
  · -- Main case: some strict inequality vanishes at `y`, so `Φ y = 0`.
    have heqs_y : ∀ f ∈ B.eqs, eaEval c f y = 0 := gpi_eqs_zero_of_mem_closure c B hy
    have hpos_y : ∀ g ∈ B.pos, 0 ≤ eaEval c g y := gpi_pos_nonneg_of_mem_closure c B hy
    obtain ⟨g0, hg0mem, hg0val⟩ : ∃ g ∈ B.pos, eaEval c g y = 0 := by
      by_contra hcon
      simp only [not_exists, not_and] at hcon
      exact hholds ⟨heqs_y, fun g hg => lt_of_le_of_ne (hpos_y g hg) (Ne.symm (hcon g hg))⟩
    have hPy : eaEval c (psiProd B) y = 0 := by
      rw [gpi_eaEval_psiProd]
      exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨g0, hg0mem, hg0val⟩)
    have hΦy : eaEval c (phiPen B (2 * (KL.eval B.deg + 1))) y = 0 := by
      rw [gpi_eaEval_phiPen, hPy, zero_mul]
    obtain ⟨θ, cst, hθ0, hθ1, hcst, hKexpθ, hgr⟩ :=
      hKG k r c (phiPen B (2 * (KL.eval B.deg + 1))) y hkr hΦy
    have hdeg : atomDeg (phiPen B (2 * (KL.eval B.deg + 1)))
        ≤ (4 * (KL.eval B.deg + 1) + 2) * B.deg + 1 := by
      have h := atomDeg_phiPen_le B (2 * (KL.eval B.deg + 1))
      have he : 2 * (2 * (KL.eval B.deg + 1)) + 2 = 4 * (KL.eval B.deg + 1) + 2 := by ring
      rw [he] at h
      exact h
    have hKexp_ge : 1 / (1 - θ)
        ≤ ((KG.eval ((4 * (KL.eval B.deg + 1) + 2) * B.deg + 1) : ℕ) : ℝ) :=
      le_trans hKexpθ (by exact_mod_cast eval_mono KG hdeg)
    have hKexp_lt : KG.eval ((4 * (KL.eval B.deg + 1) + 2) * B.deg + 1) < κ := by omega
    obtain ⟨z, hzy, hzeqs, hzpos⟩ :=
      good_points_instance c B y (KL.eval B.deg + 1) (by omega) hloj hθ0 hθ1 hcst hgr
        (KG.eval ((4 * (KL.eval B.deg + 1) + 2) * B.deg + 1)) hKexp_ge hy κ hKexp_lt ε hε
    refine ⟨z, hzy, ?_, hzpos⟩
    intro f hf
    rw [hzeqs f hf, abs_zero, mul_zero]
    exact pow_nonneg dist_nonneg _

end Work.WilE3.MPsi
