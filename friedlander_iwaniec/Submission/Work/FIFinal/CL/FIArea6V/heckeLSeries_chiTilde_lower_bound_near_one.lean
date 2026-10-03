/-
# `Submission.Work.FIArea6V.heckeLSeries_chiTilde_lower_bound_near_one`

The Hecke `L`-function `L(s, χ̃·ω^{2m})` of *FI* §16 — `χ̃ = chiTilde χ`, `ω(z) = z/|z|` — is
bounded below by a positive constant just to the **right** of `s = 1`, for every strict character
`χ` mod `4d` and every `m : ℤ` for which the Größencharacter is not the trivial one on the primary
units mod `4d`.

Mathematically this is the classical statement `L(1, ψ) ≠ 0` for a non-trivial Hecke character of
`ℚ(i)`, made quantitative by continuity.  The route:

* `HeckeCompletionGeneral` (`FIArea6/TauPieces`) — the datum is not the exceptional one, so an
  **entire** completion `Lam` of `Λ(s,ψ) = heckeArch d (2m) s · heckeLSeries (χ̃) (2m) s` exists on
  `re s > 1 + |m|`;
* `heckeStripZFR` (`FIArea6Hecke`) — the zero-free region *FI* (16.20) + Lemma 16.1 (Siegel), in its
  sharpened `d^{-ε}` form; in particular `Lval d (2m) Lam 1 ≠ 0` (the exceptional real zero is
  farther from `1` than `c·(d^ε·log(|2m|+3))^{-1}`);
* `Lam_div_heckeArch_eq_LSeries` (identity theorem) — on `re s > 1` the continuation
  `Lval = Lam/heckeArch` **is** the Dirichlet series `heckeLSeries (χ̃) (2m)`;
* `Lval` is continuous at `s = 1` (as `Lam` is entire and `heckeArch d (2m) 1 ≠ 0`), so a
  neighbourhood of `σ = 1` on which `‖Lval‖ ≥ ‖Lval 1‖/2` produces the announced `c` and `δ`.
-/
import Mathlib
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeLcontInvBound_strip
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeLcontInvBound_all
import Submission.Work.FIArea6.TauPieces.HeckeCompletionGeneral
import Submission.Work.FIArea6Hecke.chiTildeDefs

namespace Work.FIArea6V

theorem heckeLSeries_chiTilde_lower_bound_near_one :
    ∀ {d : ℕ}, 1 ≤ d → ∀ {chi : GaussianInt → ℂ},
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d (Work.FIArea6Hecke.chiTilde chi) →
      ∀ (m : ℤ),
      ¬(2 * m = 0 ∧ ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
          Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea6Hecke.chiTilde chi z = 1) →
      ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
        c ≤ ‖Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.chiTilde chi) (2 * m)
              (σ : ℂ)‖ := by
  intro d hd chi hchi hchiT m hnt
  -- the datum is not the exceptional one: either `m ≠ 0` or `χ̃` is non-trivial on the primary
  -- units mod `4d` — exactly the hypothesis of `HeckeCompletionGeneral`
  have hnontriv : (2 * m) ≠ 0 ∨ ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea6Hecke.chiTilde chi z ≠ 1 := by
    rw [not_and_or] at hnt
    rcases hnt with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hc
      exact h (fun z hp hu => by
        by_contra hf
        exact hc ⟨z, hp, hu, hf⟩)
  -- the entire completion `Lam` of `Λ(s,ψ)`, `ψ = χ̃·ω^{2m}`
  obtain ⟨Lam, hAn, hagree⟩ :=
    Work.FIArea6.TauPieces.HeckeCompletionGeneral d (Work.FIArea6Hecke.chiTilde chi) (2*m) hd
      hchiT hnontriv
  -- the zero-free region (16.20)/(16.24): `Lval d (2m) Lam` does not vanish at `s = 1`
  obtain ⟨c₁, hc₁pos, hZFR⟩ := Work.FIArea6Hecke.heckeStripZFR (1/4) (by norm_num) le_rfl
  have hArch1 : Work.FITop4.Bridge.heckeArch d (2*m) (1 : ℂ) ≠ 0 :=
    Work.FIArea6Hecke.heckeArch_ne_zero_of_re_pos hd (2*m) (by norm_num)
  have hLval1 : Work.FIArea6Hecke.Lval d (2*m) Lam 1 ≠ 0 := by
    refine hZFR d (Work.FIArea6Hecke.chiTilde chi) (2*m) Lam hd hchiT hAn hagree 1 ?_ ?_
    · have hden : 0 < (d : ℝ) ^ ((1:ℝ)/4) *
          Real.log (|(((2*m : ℤ)) : ℝ)| + |(1:ℂ).im| + 3) := by
        refine mul_pos (Real.rpow_pos_of_pos ?_ _) (Real.log_pos ?_)
        · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
        · simp only [Complex.one_im, abs_zero, add_zero]
          linarith [abs_nonneg (((2*m : ℤ)) : ℝ)]
      have hp : 0 < c₁ / ((d : ℝ) ^ ((1:ℝ)/4) *
          Real.log (|(((2*m : ℤ)) : ℝ)| + |(1:ℂ).im| + 3)) := div_pos hc₁pos hden
      have h1re : (1:ℂ).re = 1 := rfl
      rw [h1re]; linarith
    · norm_num
  have hnormpos : 0 < ‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ := norm_pos_iff.mpr hLval1
  -- `Lval` is continuous at `1` (`Lam` entire, `heckeArch d (2m) 1 ≠ 0`)
  have hcont : ContinuousAt (fun σ : ℝ => Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ)) 1 := by
    have hLam_cont : ContinuousAt Lam (1:ℂ) :=
      (hAn.analyticAt Filter.univ_mem).continuousAt
    have hofReal : ContinuousAt (fun σ : ℝ => ((σ:ℝ):ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    have hnum : ContinuousAt (fun σ : ℝ => Lam ((σ:ℝ):ℂ)) 1 :=
      ContinuousAt.comp (g := Lam) (f := fun σ : ℝ => ((σ:ℝ):ℂ)) hLam_cont hofReal
    have harchd : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d (2*m)) (1:ℂ) :=
      Work.FIArea6Hecke.heckeArch_differentiableAt hd (2*m) (by norm_num)
    have hden : ContinuousAt (fun σ : ℝ => Work.FITop4.Bridge.heckeArch d (2*m) ((σ:ℝ):ℂ)) 1 :=
      ContinuousAt.comp (g := fun s : ℂ => Work.FITop4.Bridge.heckeArch d (2*m) s)
        (f := fun σ : ℝ => ((σ:ℝ):ℂ)) harchd.continuousAt hofReal
    rw [show (fun σ : ℝ => Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ))
        = (fun σ : ℝ => Lam ((σ:ℝ):ℂ)) /
          (fun σ : ℝ => Work.FITop4.Bridge.heckeArch d (2*m) ((σ:ℝ):ℂ)) from by
        funext σ; rfl]
    exact hnum.div hden hArch1
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont (‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ / 2) (half_pos hnormpos)
  refine ⟨‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ / 2, δ, half_pos hnormpos, hδpos, ?_⟩
  intro σ hσ1 hσδ
  have hdist : dist σ (1:ℝ) < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]; linarith
  have hnear := hδ hdist
  have hnear' : ‖Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ)
      - Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ < ‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ / 2 := by
    rwa [dist_eq_norm] at hnear
  have hkey : ‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ / 2
      ≤ ‖Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ)‖ := by
    have h3 : ‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ ≤ ‖Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ)‖ +
        ‖Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ) - Work.FIArea6Hecke.Lval d (2*m) Lam 1‖ := by
      calc ‖Work.FIArea6Hecke.Lval d (2*m) Lam 1‖
          = ‖Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ) - (Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ)
              - Work.FIArea6Hecke.Lval d (2*m) Lam 1)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  -- on `re s > 1` the continuation `Lval` is the Dirichlet series (identity theorem)
  have hLval_eq : Work.FIArea6Hecke.Lval d (2*m) Lam (σ:ℂ) =
      Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.chiTilde chi) (2*m) (σ:ℂ) := by
    rw [Work.FIArea6Hecke.Lval]
    exact Work.FIArea6Hecke.Lam_div_heckeArch_eq_LSeries hd (Work.FIArea6Hecke.chiTilde chi) (2*m)
      hchiT hAn hagree (s := (σ:ℂ)) (by simpa using hσ1)
  rw [← hLval_eq]
  exact hkey

end Work.FIArea6V
