import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.pad_stratum
import Submission.Work.WilE7.PadAux.fiber_padStrat_ncard
import Submission.Work.CoreStep.SigmaFamDefs

namespace Work.WilE7.Endgame.Bv2

theorem padSheets {n m d : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (b : Set (Fin n → ℝ))
    (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) b)
    (hinj : ∀ x ∈ b, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ b →
      Fin.append x (s j x) ∈ Work.WilE7.MainDesign.absSet S)
    (hcov : ∀ z ∈ Work.WilE7.MainDesign.absSet S,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z) :
    (∀ (j : Fin k) (x : Fin n → ℝ), x ∈ b →
      Fin.append x (Work.WilE7.padSection (m + 1) d (s j x)) ∈
        (Work.WilE7.padStrat n (m + 1) d (Work.WilE7.tidy (Work.CoreStep.absSub S))).set) ∧
    (∀ z ∈ (Work.WilE7.padStrat n (m + 1) d (Work.WilE7.tidy (Work.CoreStep.absSub S))).set,
      WilkiesDesign.E.projFirst n (d + m + 1) z ∈ b →
      ∃ j : Fin k, Work.WilE7.padSection (m + 1) d
          (s j (WilkiesDesign.E.projFirst n (d + m + 1) z)) =
        WilkiesDesign.E.projSnd n (d + m + 1) z) ∧
    (∀ (j : Fin k) (x : Fin n → ℝ), x ∈ b →
      (Work.WilE7.padSection (m + 1) d (s j x)) (Fin.last (d + m)) = (s j x) (Fin.last m)) ∧
    (∀ x ∈ b, Function.Injective fun j : Fin k =>
      Work.WilE7.padSection (m + 1) d (s j x)) ∧
    (∀ j, ContinuousOn (fun x => Work.WilE7.padSection (m + 1) d (s j x)) b) ∧
    (Work.WilE7.padStrat n (m + 1) d (Work.WilE7.tidy (Work.CoreStep.absSub S))).fmt =
      S.X.fmt + d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the graph of each padded section lies in the padded set
    intro j x hx
    rw [Work.WilE7.mem_padStrat_append]
    refine ⟨?_, Work.WilE7.projFirst_padSection (m + 1) d (s j x)⟩
    rw [Work.WilE7.projSnd_padSection, Work.WilE7.tidy_set, Work.CoreStep.absSub_set]
    exact hsub j x hx
  · -- the padded sections cover the fibres of the padded set
    intro z hz hx
    rw [Work.WilE7.padStrat_set] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Work.WilE7.tidy_set, Work.CoreStep.absSub_set] at hz1
    have hxw : WilkiesDesign.E.projFirst n (m + 1)
        (fun i => z (Work.WilE7.midInj n d (m + 1) i)) ∈ b := by
      rw [Work.WilE7.projFirst_midInj]
      exact hx
    obtain ⟨j, hj⟩ := hcov _ hz1 hxw
    refine ⟨j, ?_⟩
    change Work.WilE7.padSection (m + 1) d
        (s j (WilkiesDesign.E.projFirst n (d + (m + 1)) z)) =
      WilkiesDesign.E.projSnd n (d + (m + 1)) z
    have hj2 : s j (WilkiesDesign.E.projFirst n (d + (m + 1)) z) =
        WilkiesDesign.E.projSnd d (m + 1) (WilkiesDesign.E.projSnd n (d + (m + 1)) z) := by
      rw [Work.WilE7.projFirst_midInj, Work.WilE7.projSnd_midInj_projSnd] at hj
      exact hj
    have hz0 : WilkiesDesign.E.projFirst d (m + 1)
        (WilkiesDesign.E.projSnd n (d + (m + 1)) z) = 0 := by
      funext a
      rw [Work.WilE7.projFirst_projSnd_eq]
      exact hz2 a
    rw [Work.WilE7.projSnd_append_projFirst_projSnd n d (m + 1) z, ← hj2, hz0]
    exact Work.WilE7.padSection_eq_append (m + 1) d _
  · -- the last coordinate survives the padding
    intro j x hx
    rw [← Fin.natAdd_last]
    exact Work.WilE7.padSection_natAdd (m + 1) d (s j x) (Fin.last m)
  · -- injectivity of the padded sections
    intro x hx j j' h
    exact hinj x hx (by
      have h2 := congrArg (WilkiesDesign.E.projSnd d (m + 1)) h
      rwa [Work.WilE7.projSnd_padSection, Work.WilE7.projSnd_padSection] at h2)
  · -- continuity of the padded sections
    intro j
    exact Work.WilE7.continuousOn_padSection n (m + 1) d k b s hcont j
  · -- the format of the padded stratum
    rw [Work.WilE7.padStrat_fmt, Work.WilE7.tidy_r, Work.CoreStep.absSub_r]
    simp only [WilkiesDesign.E.SemiPf.fmt]
    omega

end Work.WilE7.Endgame.Bv2
