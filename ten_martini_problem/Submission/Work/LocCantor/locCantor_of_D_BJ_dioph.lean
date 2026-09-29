import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMContract.Gluing.idsAnalytic_of
import Submission.Work.LocCantor.idsAnalytic_of_dioph
import Submission.Work.LocCantor.bloch_reduction
import Submission.Work.TMComp.prove_OpBasics
import Submission.Work.TMComp.prove_Duality
import Submission.Work.TMComp.prove_RotBasics
import Submission.Work.TMComp.prove_Puig
import Submission.Work.TMComp.prove_Schnol
import Submission.Work.TMComp.prove_RealCartan
import Submission.Work.TMComp.RedProj.differentiableOn_intervalIntegral_kernel
import Submission.Work.TMComp.RedProj.coboundary_of_conjugacy
import Submission.Work.TMComp.RedC7T.dioph_consumers
import Submission.Work.TMComp.RedC7T.mAnalytic_dioph
import Submission.Work.TMComp.RedC8.prove_Kotani
import Submission.Work.TMComp.LocCantor.Bloch
import Submission.Work.TMComp.LocCantor.bloch_identity
import Submission.Work.TMComp.LocCantor.det_blochMat_const
import Submission.Work.TMComp.LocCantor.det_blochReal_eq
import Submission.Work.TMComp.LocCantor.normConj_spec
import Submission.Work.TMComp.LocCantor.normConj_analytic
import Submission.Work.TMComp.LocCantor.blochReal_analytic
import Submission.Work.TMComp.LocCantor.Reducible
import Submission.Work.TMComp.LocCantor.null_iUnion_affine
import Submission.Work.TMComp.LocCantor.null_image_of_analyticOnNhd
import Submission.Work.TMComp.LocCantor.fourier_ne_zero
import Submission.Work.TMComp.LocCantor.fourier_analytic_per
import Submission.Work.TMComp.LocCantor.det_blochMat_ne_zero_dioph

/-!
# `P_LocCantor` from the Diophantine case of Bourgain--Jitomirskaya

`Work.LocCantor.locCantor_of_D_BJ_dioph`: the C17 assembly of
`Submission/Work/TMComp/prove_LocCantor.lean`, run against

* C9 **restricted to Diophantine frequencies** (`Work.TMComp.RedProj.P_mAnalytic_dioph`,
  `Submission/Work/TMComp/RedC7T/mAnalytic_dioph.lean`), which is what `P_LocCantor`'s own
  hypothesis `DiophBelow α b₀` supplies, and
* C11 `P_Reducibility` at those frequencies (`Work.TMComp.RedProj.prove_Reducibility_of_dioph`,
  `Submission/Work/TMComp/RedC7T/dioph_consumers.lean`),
* with C8 `P_Kotani` taken from the axiom-clean fork `Work.TMComp.RedC8.prove_Kotani`.

The resulting obligation is exactly the Diophantine case of C7 (AJ Thm 2.1), which the
statement carries as the hypothesis `hD`.  Nothing in the import closure of this file is
a stub — in particular this file does **not** import
`Submission.Work.TMComp.prove_LocCantor` / `prove_Reducibility` / `prove_BJ`, so all of
`prove_BJ`'s dependencies (the frozen C7 stub) are avoided; the two copies needed from the
C17 file live in `Submission/Work/LocCantor/{bloch_reduction,idsAnalytic_of_dioph}.lean`.
-/

open scoped BigOperators
open MeasureTheory Filter Topology Set
open Work.TMContract

noncomputable section

namespace Work.TMComp

open Work.TMContract
open Work.TMComp.LocCantor

open Work.TMContract
open Work.TMComp.LocCantor

/-- The affine family of phase maps appearing in the counting argument: the phase is recovered
from the value of the dual IDS up to the countable family `y ↦ ±(y-1)/2 + kα + l`. -/
def phaseMapDioph (α : ℝ) (p : ℤ × ℤ × Bool) : ℝ × ℝ :=
  ((if p.2.2 then (1 : ℝ) else -1) / 2, (p.1 : ℝ) * α + (p.2.1 : ℝ) - (if p.2.2 then (1 : ℝ) else -1) / 2)

theorem locCantor_of_components_dioph
    (h1 : P_OpBasics) (h3 : P_Duality) (h5 : P_RotBasics) (h9 : RedProj.P_mAnalytic_dioph)
    (h11 : P_Reducibility) (h12 : P_Puig) (h15 : P_Schnol)
    (hfa : ∀ (u : ℤ → ℂ), ExpDecay u → AnalyticOnNhd ℝ (fourier u) Set.univ ∧
      (∀ x, fourier u (x + 1) = fourier u x))
    (hfz : ∀ {u : ℤ → ℂ}, ExpDecay u → u ≠ 0 → fourier u ≠ 0)
    (hdet : ∀ {α θ : ℝ} {u : ℤ → ℂ}, Irrational α → AnalyticOnNhd ℝ (fourier u) Set.univ →
      Continuous (fourier u) → (∀ x, fourier u (x + 1) = fourier u x) → fourier u ≠ 0 →
      (∀ k l : ℤ, 2 * θ ≠ (k : ℝ) * α + (l : ℝ)) →
      (∀ x, (blochMat α θ u x).det = 0) → False) :
    P_LocCantor := by
  intro α b₀ lam hα hDioph hl1 hloc
  rintro ⟨a, b, hab, hsub⟩
  have hlam0 : lam ≠ 0 := by linarith
  have hlamp : 0 < lam := by linarith
  have hlam'0 : 0 < lam⁻¹ := inv_pos.mpr hlamp
  have hlam'1 : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl1
  -- duality: the rescaled interval lies in the dual spectrum
  have hsub' : Set.Ioo (a / lam) (b / lam) ⊆ amoSpec α lam⁻¹ := by
    intro E hE
    have hE1 : a < E * lam := by
      have := hE.1
      rwa [div_lt_iff₀ hlamp] at this
    have hE2 : E * lam < b := by
      have := hE.2
      rwa [lt_div_iff₀ hlamp] at this
    have h2 := (h3 α lam hα hlam0 (E * lam)).mp (hsub ⟨hE1, hE2⟩)
    rwa [mul_div_cancel_right₀ E hlam0] at h2
  have hab' : a / lam < b / lam := div_lt_div_of_pos_right hab hlamp
  -- the dual IDS is analytic on the dual interval
  have hAnalytic : AnalyticOnNhd ℝ (ids α lam⁻¹) (Set.Ioo (a / lam) (b / lam)) :=
    Work.LocCantor.idsAnalytic_of_dioph h5 h9 α lam⁻¹ (a / lam) (b / lam) b₀ hα
      (RedProj.pos_of_diophBelow α b₀ hDioph) hDioph hlam'0 hlam'1 hab' hsub'
  -- the reducible set is null there
  have hRed_null : volume (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam)) = 0 := by
    rcases h11.2 α b₀ hα hDioph lam⁻¹ hlam'0 hlam'1 (a / lam) (b / lam) hab' hsub' with
      hdeg | ⟨c, d, hcd, hsub2⟩
    · exact hdeg
    · exfalso
      have hspec : Set.Ioo c d ⊆ amoSpec α lam⁻¹ := fun E hE => hsub' (hsub2 hE).2
      exact (h12 α lam⁻¹ hα hlam'0 hlam'1 c d hcd hspec) (fun E hE => (hsub2 hE).1)
  -- its image under the IDS is null
  have hYnull : volume (ids α lam⁻¹ ''
      (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam))) = 0 :=
    null_image_of_analyticOnNhd hAnalytic (fun _ hE => hE.2) hRed_null
  -- the null set of phases
  have hNnull : volume (⋃ p : ℤ × ℤ × Bool,
      (fun y => (phaseMapDioph α p).1 * y + (phaseMapDioph α p).2) ''
        (ids α lam⁻¹ '' (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam)))) = 0 :=
    null_iUnion_affine hYnull (phaseMapDioph α)
  -- the good phases have full measure
  have hbad_count : ({θ : ℝ | ∃ k l : ℤ, 2 * θ = (k : ℝ) * α + (l : ℝ)} : Set ℝ).Countable := by
    refine Set.Countable.mono ?_
      (Set.countable_range (fun p : ℤ × ℤ => ((p.1 : ℝ) * α + (p.2 : ℝ)) / 2))
    rintro θ ⟨k, l, hkl⟩
    exact ⟨(k, l), by linarith⟩
  have hbad_null : volume {θ : ℝ | ∃ k l : ℤ, 2 * θ = (k : ℝ) * α + (l : ℝ)} = 0 :=
    hbad_count.measure_zero volume
  have hbad_ae : ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∉ {θ : ℝ | ∃ k l : ℤ, 2 * θ = (k : ℝ) * α + (l : ℝ)} := by
    rw [MeasureTheory.ae_iff]
    simpa [Set.mem_setOf_eq] using hbad_null
  have hgood : ∀ᵐ θ ∂(volume : Measure ℝ),
      (∀ (E : ℝ) (u : ℤ → ℂ), IsGenEigen α lam θ E u → ExpDecay u) ∧
        (∀ k l : ℤ, 2 * θ ≠ (k : ℝ) * α + (l : ℝ)) := by
    filter_upwards [hloc, hbad_ae] with θ hθ hθ'
    exact ⟨hθ, fun k l hk => hθ' ⟨k, l, hk⟩⟩
  -- every good phase lies in the null set
  have hgood_sub : {θ : ℝ |
      (∀ (E : ℝ) (u : ℤ → ℂ), IsGenEigen α lam θ E u → ExpDecay u) ∧
        (∀ k l : ℤ, 2 * θ ≠ (k : ℝ) * α + (l : ℝ))} ⊆
      (⋃ p : ℤ × ℤ × Bool,
        (fun y => (phaseMapDioph α p).1 * y + (phaseMapDioph α p).2) ''
          (ids α lam⁻¹ '' (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam)))) := by
    intro θ hθ
    obtain ⟨hlocθ, hθbad⟩ := hθ
    -- Schnol + phase independence produce the generalised eigenvalue
    obtain ⟨H, hH⟩ := h1.1 α lam θ
    have hspecθ : ∀ E : ℝ, E ∈ Set.Ioo a b → (E : ℂ) ∈ spectrum ℂ H := by
      intro E hE
      obtain ⟨H', hH', hE'⟩ := hsub hE
      have hphase := h1.2.2 α lam 0 θ hα H' H hH' hH
      rw [hphase] at hE'
      exact hE'
    have hmid' : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have hmid : (((a + b) / 2 : ℝ) : ℂ) ∈ spectrum ℂ H := hspecθ _ hmid'
    have hδ : 0 < (b - a) / 2 := by linarith
    obtain ⟨E, hElt, u, hgen⟩ := h15 α lam θ H hH ((a + b) / 2) hmid ((b - a) / 2) hδ
    have hEab : E ∈ Set.Ioo a b := by
      have hlt := abs_lt.mp hElt
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    have hdec : ExpDecay u := hlocθ E u hgen
    have hnt : u ≠ 0 := hgen.1
    have hrec : ∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n := hgen.2.1
    -- the Bloch reduction
    have hfau := hfa u hdec
    obtain ⟨k, j, ε, hε, hred, hids⟩ := Work.LocCantor.bloch_reduction (h5.2.2.2) hα hlam0 hnt hdec hrec
      (fun k l hk => hθbad k l hk) hfau.1 hfau.2
      (fun c hc => by
        intro hc0
        exact hdet hα hfau.1 (continuousOn_univ.mp hfau.1.continuousOn) hfau.2 (hfz hdec hnt)
          (fun k l hk => hθbad k l hk) (fun x => by rw [hc x, hc0]; simp))
    have hE' : E * lam⁻¹ ∈ Set.Ioo (a / lam) (b / lam) := by
      constructor
      · rw [div_lt_iff₀ hlamp, mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
        exact hEab.1
      · rw [lt_div_iff₀ hlamp, mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
        exact hEab.2
    -- read off the phase
    rcases hε with hε1 | hε1
    · refine Set.mem_iUnion.mpr ⟨(-k, j, true), ?_⟩
      rw [Set.mem_image]
      refine ⟨ids α lam⁻¹ (E * lam⁻¹), ?_, ?_⟩
      · rw [Set.mem_image]
        exact ⟨E * lam⁻¹, ⟨hred, hE'⟩, rfl⟩
      · simp only [phaseMapDioph, if_true]
        push_cast
        rw [hε1] at hids
        push_cast at hids
        linarith
    · refine Set.mem_iUnion.mpr ⟨(k, -j, false), ?_⟩
      rw [Set.mem_image]
      refine ⟨ids α lam⁻¹ (E * lam⁻¹), ?_, ?_⟩
      · rw [Set.mem_image]
        exact ⟨E * lam⁻¹, ⟨hred, hE'⟩, rfl⟩
      · simp only [phaseMapDioph, if_false, Bool.false_eq_true]
        push_cast
        rw [hε1] at hids
        push_cast at hids
        linarith
  -- contradiction: a full-measure set is contained in a null set
  have hNc : volume (⋃ p : ℤ × ℤ × Bool,
      (fun y => (phaseMapDioph α p).1 * y + (phaseMapDioph α p).2) ''
        (ids α lam⁻¹ '' (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam))))ᶜ = 0 :=
    MeasureTheory.ae_iff.mp (hgood.mono hgood_sub)
  have htot : volume (Set.univ : Set ℝ) = 0 := by
    rw [← Set.compl_union_self (s := ⋃ p : ℤ × ℤ × Bool,
      (fun y => (phaseMapDioph α p).1 * y + (phaseMapDioph α p).2) ''
        (ids α lam⁻¹ '' (RedSet α lam⁻¹ ∩ Set.Ioo (a / lam) (b / lam))))]
    exact measure_union_null hNc hNnull
  have : (⊤ : ENNReal) = 0 := by simpa using htot
  exact absurd this (by simp)


end Work.TMComp

namespace Work.LocCantor

open Work.TMComp
open Work.TMComp.LocCantor
open Work.TMComp.RedProj
open Work.TMComp.RedC7T
open Work.TMComp.RedC8

/-- **AJ Thm 5.1 with the Diophantine case of C7 as hypothesis.**

For irrational `α` that is Diophantine with some constant `b₀`, coupling `λ ≥ 1` and a.e.
Anderson localisation, the spectrum `Σ_{λ,α}` contains no interval — *assuming* the
Diophantine case of Bourgain--Jitomirskaya, `L(E) = max 0 (log |λ|)` on the spectrum:
C9 restricted to Diophantine frequencies is then `RedC7T.mAnalytic_dioph`, C11 is
`RedProj.prove_Reducibility_of_dioph`, and the C17 assembly
`Work.TMComp.locCantor_of_components_dioph` finishes the argument. -/
theorem locCantor_of_D_BJ_dioph
    (hD : ∀ (α lam : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ → lam ≠ 0 →
      ∀ E ∈ Work.TMContract.amoSpec α lam, Work.TMContract.lyap α lam (E : ℂ) = max 0 (Real.log |lam|)) :
    Work.TMContract.P_LocCantor :=
  locCantor_of_components_dioph prove_OpBasics prove_Duality prove_RotBasics
    (mAnalytic_dioph hD prove_Kotani)
    (prove_Reducibility_of_dioph differentiableOn_intervalIntegral_kernel
      (fun α hα φ hφc hφp O c hO hper hdet hconj =>
        coboundary_of_conjugacy α hα φ hφc hφp O c hO hper hdet hconj)
      (mAnalytic_dioph hD prove_Kotani) prove_RealCartan)
    prove_Puig prove_Schnol
    (fun u hdec => fourier_analytic_per u hdec)
    (fun hdec hne => fourier_ne_zero hdec hne)
    (fun hα hAn hcont hper hnt hθ hzero => det_blochMat_ne_zero_dioph hα hAn hcont hper hnt hθ hzero)

end Work.LocCantor
