import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.LeafDefs
import Submission.Work.FTS_RegExport.RXT.cone_max_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.step_classical` — leaf port (module `LeafAux.step_classical`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false


/-- `|a + b + c - d| ≤ |a| + |b| + |c| + |d|`. -/
lemma abs_add3_sub_le (a b c d : ℝ) : |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c - d| ≤ |a + b + c| + |d| := by simpa using abs_sub_le (a + b + c) 0 d
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- Two one-dimensional frozen-derivative mean value bounds, combined into the two-variable
first-order expansion error. -/
lemma frozen_mvt_two {f fs fψ : ℝ → ℝ → ℝ} {s ψ s' ψ' C₁ C₂ η : ℝ}
    (hs : ∀ a b, HasDerivAt (fun a' => f a' b) (fs a b) a)
    (hψ : ∀ a b, HasDerivAt (fun b' => f a b') (fψ a b) b)
    (hbds : ∀ l ∈ Set.Icc (min s s') (max s s'), |fs l ψ' - C₁| ≤ η)
    (hbdψ : ∀ l ∈ Set.Icc (min ψ ψ') (max ψ ψ'), |fψ s l - C₂| ≤ η) :
    |f s' ψ' - f s ψ - ((s' - s) * C₁ + (ψ' - ψ) * C₂)| ≤ η * (|s' - s| + |ψ' - ψ|) := by
  have h1 := Work.FTS_RegExport.RXT.ConeAux.mvt_diff_bound (g := fun a : ℝ => f a ψ') (gs := fun a : ℝ => fs a ψ')
    (a := s) (a' := s') (C₁ := C₁) (C₂ := η)
    (fun a _ => ((hs a ψ').continuousAt).continuousWithinAt) (fun a => hs a ψ') hbds
  have h2 := Work.FTS_RegExport.RXT.ConeAux.mvt_diff_bound (g := fun b : ℝ => f s b) (gs := fun b : ℝ => fψ s b)
    (a := ψ) (a' := ψ') (C₁ := C₂) (C₂ := η)
    (fun b _ => ((hψ s b).continuousAt).continuousWithinAt) (fun b => hψ s b) hbdψ
  have h3 : f s' ψ' - f s ψ - ((s' - s) * C₁ + (ψ' - ψ) * C₂)
      = (f s' ψ' - f s ψ' - (s' - s) * C₁) + (f s ψ' - f s ψ - (ψ' - ψ) * C₂) := by ring
  rw [h3]
  calc |(f s' ψ' - f s ψ' - (s' - s) * C₁) + (f s ψ' - f s ψ - (ψ' - ψ) * C₂)|
      ≤ |f s' ψ' - f s ψ' - (s' - s) * C₁| + |f s ψ' - f s ψ - (ψ' - ψ) * C₂| :=
        abs_add_le _ _
    _ = |f s ψ' - f s' ψ' - (s - s') * C₁| + |f s ψ - f s ψ' - (ψ - ψ') * C₂| := by
        rw [show f s' ψ' - f s ψ' - (s' - s) * C₁
              = -(f s ψ' - f s' ψ' - (s - s') * C₁) by ring, abs_neg,
            show f s ψ' - f s ψ - (ψ' - ψ) * C₂
              = -(f s ψ - f s ψ' - (ψ - ψ') * C₂) by ring, abs_neg]
    _ ≤ η * |s - s'| + η * |ψ - ψ'| := add_le_add h1 h2
    _ = η * (|s' - s| + |ψ' - ψ|) := by rw [abs_sub_comm s s', abs_sub_comm ψ ψ']; ring

theorem step_classical {φ φs φψ φt a b c f : ℝ → ℝ → ℝ → ℝ} {T A C F : ℝ}
    (hs : ∀ s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun s' => φ s' ψ τ) (φs s ψ τ) s)
    (hψ : ∀ s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun ψ' => φ s ψ' τ) (φψ s ψ τ) ψ)
    (ht : ∀ s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T,
      HasDerivWithinAt (fun t => φ s ψ t) (φt s ψ τ) (Set.Icc 0 T) τ)
    (hcs : ContinuousOn (fun p : ℝ × ℝ × ℝ => φs p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hcψ : ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hct : ContinuousOn (fun p : ℝ × ℝ × ℝ => φt p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hEq : ∀ s ψ τ, 0 < τ → τ ≤ T →
      φt s ψ τ = f s ψ τ - (a s ψ τ * φs s ψ τ + b s ψ τ * φψ s ψ τ + c s ψ τ * φ s ψ τ))
    (ha : ∀ s ψ τ, 0 < τ → τ ≤ T → |a s ψ τ| ≤ A ∧ |b s ψ τ| ≤ A)
    (hc : ∀ s ψ τ, 0 < τ → τ ≤ T → |c s ψ τ| ≤ C)
    (hf : ∀ s ψ τ, 0 < τ → τ ≤ T → |f s ψ τ| ≤ F) :
    Work.FTS.RegExportIface.RXT.ConeStep 1 (fun _ => φ) T A C F := by
  intro R ε hε
  -- ## constants
  set A₁ : ℝ := max A 1 with hA₁def
  have hA₁1 : 1 ≤ A₁ := le_max_right A 1
  have hA₁pos : 0 < A₁ := lt_of_lt_of_le one_pos hA₁1
  have hAle₁ : A ≤ A₁ := le_max_left A 1
  set R₁ : ℝ := max R 0 + A₁ with hR₁def
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have hRR₁ : R ≤ R₁ := by rw [hR₁def]; have := le_max_left R 0; linarith
  have hA₁R₁ : A₁ ≤ R₁ := by rw [hR₁def]; linarith
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le hA₁pos hA₁R₁
  set η : ℝ := ε / (1 + 4 * A₁) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos hε (by linarith)
  have hηε : η * (1 + 4 * A₁) = ε := by rw [hηdef]; field_simp
  set Box : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (-R₁) R₁ ×ˢ (Set.Icc (-R₁) R₁ ×ˢ Set.Icc (0:ℝ) T) with hBoxdef
  have hBoxc : IsCompact Box := by
    rw [hBoxdef]; exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  -- ## Heine-Cantor on the box, once and for all
  have huc : ∀ g : ℝ → ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ Box, ∀ q ∈ Box, dist p q < δ →
        |g p.1 p.2.1 p.2.2 - g q.1 q.2.1 q.2.2| < η := by
    intro g hg
    have hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) Box := by
      refine hg.mono (fun p hp => ?_)
      rw [hBoxdef] at hp
      exact ⟨trivial, trivial, hp.2.2⟩
    exact (Metric.uniformContinuousOn_iff.mp
      (hBoxc.uniformContinuousOn_of_continuous hcont)) η hηpos
  obtain ⟨δs, hδspos, hδs⟩ := huc φs hcs
  obtain ⟨δψ, hδψpos, hδψ⟩ := huc φψ hcψ
  obtain ⟨δt, hδtpos, hδt⟩ := huc φt hct
  set δ : ℝ := min δs (min δψ δt) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδspos (lt_min hδψpos hδtpos)
  have hδle_s : δ ≤ δs := by rw [hδdef]; exact min_le_left _ _
  have hδle_m : δ ≤ min δψ δt := by rw [hδdef]; exact min_le_right _ _
  have hδle_ψ : δ ≤ δψ := le_trans hδle_m (min_le_left _ _)
  have hδle_t : δ ≤ δt := le_trans hδle_m (min_le_right _ _)
  refine ⟨min 1 (δ / (2 * (A₁ + 1))), lt_min one_pos (div_pos hδpos (by linarith)), ?_⟩
  intro τ hτ h hhpos hhlt hτh s ψ hsR hψR
  -- ## the mesh is small
  have hh1 : h < 1 := lt_of_lt_of_le hhlt (min_le_left _ _)
  have hhδ : h < δ / (2 * (A₁ + 1)) := lt_of_lt_of_le hhlt (min_le_right _ _)
  have hdist_lt : 2 * (A₁ + 1) * h < δ := by
    have h0 : (0:ℝ) < 2 * (A₁ + 1) := by positivity
    have h2 : h * (2 * (A₁ + 1)) < δ := (lt_div_iff₀ h0).mp hhδ
    rw [mul_comm (2 * (A₁ + 1)) h]; exact h2
  have hτ₂pos : 0 < τ + h := by linarith [hτ.1]
  have hτ₂le : τ + h ≤ T := hτh
  have hτmem : τ ∈ Set.Icc (0:ℝ) T := ⟨hτ.1, le_of_lt hτ.2⟩
  have hτ₂mem : τ + h ∈ Set.Icc (0:ℝ) T := ⟨le_of_lt hτ₂pos, hτ₂le⟩
  have hAnn : 0 ≤ A := le_trans (abs_nonneg _) (ha s ψ (τ + h) hτ₂pos hτ₂le).1
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hc s ψ (τ + h) hτ₂pos hτ₂le)
  have h0A₁h : (0:ℝ) ≤ A₁ * h := mul_nonneg hA₁pos.le hhpos.le
  have hself : ∀ x : ℝ, |x - x| ≤ A₁ * h := fun x => by
    rw [sub_self, abs_zero]; exact h0A₁h
  have hττ : |τ - τ| ≤ h := by rw [sub_self, abs_zero]; exact hhpos.le
  have hτh' : |τ + h - τ| ≤ h := by rw [add_sub_cancel_left, abs_of_pos hhpos]
  have hA₁h_le : A₁ * h ≤ A₁ := by
    calc A₁ * h ≤ A₁ * 1 := mul_le_mul_of_nonneg_left (le_of_lt hh1) hA₁pos.le
      _ = A₁ := by ring
  have hAh_le : A * h ≤ A₁ := le_trans (mul_le_mul_of_nonneg_right hAle₁ hhpos.le) hA₁h_le
  -- ## membership in the compact box
  have hmem : ∀ l q t : ℝ, |l| ≤ R₁ → |q| ≤ R₁ → t ∈ Set.Icc (0:ℝ) T → (l, q, t) ∈ Box := by
    intro l q t h1 h2 h3
    rw [hBoxdef]
    exact ⟨abs_le.mp h1, abs_le.mp h2, h3⟩
  have habsl : ∀ l : ℝ, |l - s| ≤ A₁ * h → |l| ≤ R₁ := by
    intro l h1
    have hle : |l| ≤ |s| + |l - s| := by
      calc |l| = |s + (l - s)| := by ring_nf
        _ ≤ |s| + |l - s| := abs_add_le _ _
    have hR2 : R ≤ max R 0 := le_max_left R 0
    rw [hR₁def]
    linarith [hle, hsR, h1, hA₁h_le, hR2]
  have habsψ : ∀ q : ℝ, |q - ψ| ≤ A₁ * h → |q| ≤ R₁ := by
    intro q h2
    have hle : |q| ≤ |ψ| + |q - ψ| := by
      calc |q| = |ψ + (q - ψ)| := by ring_nf
        _ ≤ |ψ| + |q - ψ| := abs_add_le _ _
    have hR2 : R ≤ max R 0 := le_max_left R 0
    rw [hR₁def]
    linarith [hle, hψR, h2, hA₁h_le, hR2]
  have hbox_near : ∀ l q t : ℝ, |l - s| ≤ A₁ * h → |q - ψ| ≤ A₁ * h →
      t ∈ Set.Icc (0:ℝ) T → (l, q, t) ∈ Box := fun l q t h1 h2 h3 =>
    hmem l q t (habsl l h1) (habsψ q h2) h3
  have hsbox : (s, ψ, τ) ∈ Box := hbox_near s ψ τ (hself s) (hself ψ) hτmem
  have hψbox : (s, ψ, τ + h) ∈ Box := hbox_near s ψ (τ + h) (hself s) (hself ψ) hτ₂mem
  -- ## distance of two points close to `(s,ψ,τ)`
  have hdist_lt_aux : ∀ l q t l' q' t' : ℝ, |l - s| ≤ A₁ * h → |q - ψ| ≤ A₁ * h →
      |t - τ| ≤ h → |l' - s| ≤ A₁ * h → |q' - ψ| ≤ A₁ * h → |t' - τ| ≤ h →
      dist (l, q, t) (l', q', t') < δ := by
    intro l q t l' q' t' h1 h2 h3 h4 h5 h6
    have hsub_s : |s - l'| = |l' - s| := abs_sub_comm s l'
    have hsub_q : |ψ - q'| = |q' - ψ| := abs_sub_comm ψ q'
    have hsub_t : |τ - t'| = |t' - τ| := abs_sub_comm τ t'
    have hhA : h ≤ A₁ * h := by
      have := mul_le_mul_of_nonneg_right hA₁1 hhpos.le
      simpa using this
    have hl : |l - l'| ≤ A₁ * h + A₁ * h := by
      have h7 : |l - l'| ≤ |l - s| + |s - l'| := by
        calc |l - l'| = |(l - s) + (s - l')| := by ring_nf
          _ ≤ |l - s| + |s - l'| := abs_add_le _ _
      linarith [h7, h1, h4, hsub_s]
    have hq : |q - q'| ≤ A₁ * h + A₁ * h := by
      have h7 : |q - q'| ≤ |q - ψ| + |ψ - q'| := by
        calc |q - q'| = |(q - ψ) + (ψ - q')| := by ring_nf
          _ ≤ |q - ψ| + |ψ - q'| := abs_add_le _ _
      linarith [h7, h2, h5, hsub_q]
    have htt : |t - t'| ≤ A₁ * h + A₁ * h := by
      have h7 : |t - t'| ≤ |t - τ| + |τ - t'| := by
        calc |t - t'| = |(t - τ) + (τ - t')| := by ring_nf
          _ ≤ |t - τ| + |τ - t'| := abs_add_le _ _
      linarith [h7, h3, h6, hsub_t, hhA]
    have hmax : dist (l, q, t) (l', q', t') = max |l - l'| (max |q - q'| |t - t'|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hmax]
    refine lt_of_le_of_lt (max_le hl (max_le hq htt)) ?_
    nlinarith [hA₁pos.le, hhpos.le, hdist_lt]
  -- ## the backward step point
  set s' : ℝ := s - h * a s ψ (τ + h) with hs'def
  set ψ' : ℝ := ψ - h * b s ψ (τ + h) with hψ'def
  have hsub1 : |s' - s| ≤ A * h := by
    have h1 : s' - s = -(h * a s ψ (τ + h)) := by rw [hs'def]; ring
    rw [h1, abs_neg, abs_mul, abs_of_pos hhpos]
    calc h * |a s ψ (τ + h)| ≤ h * A :=
          mul_le_mul_of_nonneg_left (ha s ψ (τ + h) hτ₂pos hτ₂le).1 hhpos.le
      _ = A * h := by ring
  have hsub2 : |ψ' - ψ| ≤ A * h := by
    have h1 : ψ' - ψ = -(h * b s ψ (τ + h)) := by rw [hψ'def]; ring
    rw [h1, abs_neg, abs_mul, abs_of_pos hhpos]
    calc h * |b s ψ (τ + h)| ≤ h * A :=
          mul_le_mul_of_nonneg_left (ha s ψ (τ + h) hτ₂pos hτ₂le).2 hhpos.le
      _ = A * h := by ring
  have hsub1₂ : |s' - s| ≤ A₁ * h := le_trans hsub1 (mul_le_mul_of_nonneg_right hAle₁ hhpos.le)
  have hsub2₂ : |ψ' - ψ| ≤ A₁ * h := le_trans hsub2 (mul_le_mul_of_nonneg_right hAle₁ hhpos.le)
  have hs'box : (s', ψ', τ) ∈ Box := hbox_near s' ψ' τ hsub1₂ hsub2₂ hτmem
  have hψ'box : (s, ψ', τ) ∈ Box := hbox_near s ψ' τ (hself s) hsub2₂ hτmem
  refine ⟨s', ψ', hsub1, hsub2, ?_⟩
  intro M B hM hB k
  -- ## the mean value theorem in `τ` at `(s,ψ)`
  have hcontτ : ContinuousOn (fun σ : ℝ => φ s ψ σ) (Set.Icc τ (τ + h)) := by
    intro σ hσ
    exact ((ht s ψ σ ⟨le_trans hτ.1 hσ.1, le_trans hσ.2 hτ₂le⟩).continuousWithinAt).mono
      (Set.Icc_subset_Icc hτ.1 hτ₂le)
  obtain ⟨cstar, hcmem, hceq⟩ := Work.FTS_RegExport.RXT.ConeAux.mvt_slope (f := fun σ : ℝ => φ s ψ σ)
      (fs := fun σ : ℝ => φt s ψ σ) (a := τ) (b := τ + h) (by linarith) hcontτ
      (fun σ hσ =>
        (ht s ψ σ ⟨le_trans hτ.1 (le_of_lt hσ.1), le_trans (le_of_lt hσ.2) hτ₂le⟩).hasDerivAt
          (Icc_mem_nhds (by linarith [hτ.1, hσ.1]) (by linarith [hσ.2, hτ₂le])))
  have hcmemIcc : cstar ∈ Set.Icc (0:ℝ) T :=
    ⟨by linarith [hτ.1, hcmem.1], by linarith [hcmem.2, hτ₂le]⟩
  have hcstar : |cstar - τ| ≤ h := by
    rw [abs_of_nonneg (by linarith [hcmem.1])]
    linarith [hcmem.2]
  have hEt : |φt s ψ cstar - φt s ψ (τ + h)| ≤ η :=
    le_of_lt (hδt (s, ψ, cstar) (hbox_near s ψ cstar (hself s) (hself ψ) hcmemIcc)
      (s, ψ, τ + h) hψbox
      (lt_of_lt_of_le (hdist_lt_aux s ψ cstar s ψ (τ + h) (hself s) (hself ψ) hcstar
        (hself s) (hself ψ) hτh') hδle_t))
  -- ## the spatial mean value error at time `τ`
  set W : ℝ := φ s' ψ' τ - φ s ψ τ - ((s' - s) * φs s ψ τ + (ψ' - ψ) * φψ s ψ τ) with hWdef
  have hbds : ∀ l ∈ Set.Icc (min s s') (max s s'), |φs l ψ' τ - φs s ψ τ| ≤ η := by
    intro l hl
    have hl1 : |l - s| ≤ A₁ * h := by
      have hmax : max s s' - min s s' = |s' - s| := max_sub_min_eq_abs s s'
      have hl' : |l - s| ≤ max s s' - min s s' := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hl.2, min_le_left s s'], by linarith [hl.1, le_max_left s s']⟩
      rw [hmax] at hl'
      exact le_trans hl' hsub1₂
    exact le_of_lt (hδs (l, ψ', τ) (hbox_near l ψ' τ hl1 hsub2₂ hτmem) (s, ψ, τ) hsbox
      (lt_of_lt_of_le (hdist_lt_aux l ψ' τ s ψ τ hl1 hsub2₂ hττ (hself s) (hself ψ) hττ)
        hδle_s))
  have hbdψ : ∀ l ∈ Set.Icc (min ψ ψ') (max ψ ψ'), |φψ s l τ - φψ s ψ τ| ≤ η := by
    intro l hl
    have hl1 : |l - ψ| ≤ A₁ * h := by
      have hmax : max ψ ψ' - min ψ ψ' = |ψ' - ψ| := max_sub_min_eq_abs ψ ψ'
      have hl' : |l - ψ| ≤ max ψ ψ' - min ψ ψ' := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hl.2, min_le_left ψ ψ'], by linarith [hl.1, le_max_left ψ ψ']⟩
      rw [hmax] at hl'
      exact le_trans hl' hsub2₂
    exact le_of_lt (hδψ (s, l, τ) (hbox_near s l τ (hself s) hl1 hτmem) (s, ψ, τ) hsbox
      (lt_of_lt_of_le (hdist_lt_aux s l τ s ψ τ (hself s) hl1 hττ (hself s) (hself ψ) hττ)
        hδle_ψ))
  have hWb : |W| ≤ η * (2 * A₁ * h) := by
    have hmvt := frozen_mvt_two (f := fun a b : ℝ => φ a b τ) (fs := fun a b : ℝ => φs a b τ)
      (fψ := fun a b : ℝ => φψ a b τ) (C₁ := φs s ψ τ) (C₂ := φψ s ψ τ) (η := η)
      (fun a b => hs a b τ hτmem) (fun a b => hψ a b τ hτmem) hbds hbdψ
    rw [hWdef]
    calc |φ s' ψ' τ - φ s ψ τ - ((s' - s) * φs s ψ τ + (ψ' - ψ) * φψ s ψ τ)|
        ≤ η * (|s' - s| + |ψ' - ψ|) := hmvt
      _ ≤ η * (2 * A₁ * h) := by
          have h2 : |s' - s| + |ψ' - ψ| ≤ A₁ * h + A₁ * h := by linarith [hsub1₂, hsub2₂]
          have h3 : (A₁ * h + A₁ * h : ℝ) = 2 * A₁ * h := by ring
          rw [h3] at h2
          exact mul_le_mul_of_nonneg_left h2 hηpos.le
      _ = η * (2 * A₁ * h) := rfl
  -- ## the exact decomposition of the step
  have hmain : φ s ψ (τ + h) - φ s' ψ' τ
      = h * (f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h))
        + (h * (φt s ψ cstar - φt s ψ (τ + h))
           + (h * a s ψ (τ + h)) * (φs s ψ τ - φs s ψ (τ + h))
           + (h * b s ψ (τ + h)) * (φψ s ψ τ - φψ s ψ (τ + h)) - W) := by
    have hEq₂ : φt s ψ (τ + h) = f s ψ (τ + h)
        - (a s ψ (τ + h) * φs s ψ (τ + h) + b s ψ (τ + h) * φψ s ψ (τ + h)
           + c s ψ (τ + h) * φ s ψ (τ + h)) := hEq s ψ (τ + h) hτ₂pos hτ₂le
    have h1 : φ s ψ (τ + h) - φ s' ψ' τ
        = (φ s ψ (τ + h) - φ s ψ τ) - (φ s' ψ' τ - φ s ψ τ) := by ring
    have h2 : φ s' ψ' τ - φ s ψ τ
        = (s' - s) * φs s ψ τ + (ψ' - ψ) * φψ s ψ τ + W := by rw [hWdef]; ring
    have h4 : s' - s = -(h * a s ψ (τ + h)) := by rw [hs'def]; ring
    have h5 : ψ' - ψ = -(h * b s ψ (τ + h)) := by rw [hψ'def]; ring
    rw [h1, h2, h4, h5, hceq]
    rw [show φt s ψ cstar = φt s ψ (τ + h) + (φt s ψ cstar - φt s ψ (τ + h)) from by ring]
    rw [hEq₂]
    ring
  -- ## the error is `O(h·ε)`
  set E : ℝ := (φ s ψ (τ + h) - φ s' ψ' τ)
      - h * (f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)) with hEdef
  have hstep : E = h * (φt s ψ cstar - φt s ψ (τ + h))
        + (h * a s ψ (τ + h)) * (φs s ψ τ - φs s ψ (τ + h))
        + (h * b s ψ (τ + h)) * (φψ s ψ τ - φψ s ψ (τ + h)) - W := by
    rw [hEdef, hmain]; ring
  have hErr : |E| ≤ h * ε := by
    rw [hstep]
    have h1 : |h * (φt s ψ cstar - φt s ψ (τ + h))| ≤ h * η := by
      rw [abs_mul, abs_of_pos hhpos]
      exact mul_le_mul_of_nonneg_left hEt hhpos.le
    have hcsc : |φs s ψ τ - φs s ψ (τ + h)| ≤ η :=
      le_of_lt (hδs (s, ψ, τ) hsbox (s, ψ, τ + h) hψbox
        (lt_of_lt_of_le (hdist_lt_aux s ψ τ s ψ (τ + h) (hself s) (hself ψ) hττ
          (hself s) (hself ψ) hτh') hδle_s))
    have hcw : |φψ s ψ τ - φψ s ψ (τ + h)| ≤ η :=
      le_of_lt (hδψ (s, ψ, τ) hsbox (s, ψ, τ + h) hψbox
        (lt_of_lt_of_le (hdist_lt_aux s ψ τ s ψ (τ + h) (hself s) (hself ψ) hττ
          (hself s) (hself ψ) hτh') hδle_ψ))
    have h2 : |(h * a s ψ (τ + h)) * (φs s ψ τ - φs s ψ (τ + h))| ≤ h * A₁ * η := by
      rw [abs_mul, abs_mul, abs_of_pos hhpos]
      have ha' : |a s ψ (τ + h)| ≤ A₁ := le_trans (ha s ψ (τ + h) hτ₂pos hτ₂le).1 hAle₁
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha' hhpos.le) hcsc (abs_nonneg _)
        (by positivity)
    have h3 : |(h * b s ψ (τ + h)) * (φψ s ψ τ - φψ s ψ (τ + h))| ≤ h * A₁ * η := by
      rw [abs_mul, abs_mul, abs_of_pos hhpos]
      have hb' : |b s ψ (τ + h)| ≤ A₁ := le_trans (ha s ψ (τ + h) hτ₂pos hτ₂le).2 hAle₁
      exact mul_le_mul (mul_le_mul_of_nonneg_left hb' hhpos.le) hcw (abs_nonneg _)
        (by positivity)
    have h4 : |h * (φt s ψ cstar - φt s ψ (τ + h))
          + (h * a s ψ (τ + h)) * (φs s ψ τ - φs s ψ (τ + h))
          + (h * b s ψ (τ + h)) * (φψ s ψ τ - φψ s ψ (τ + h)) - W|
        ≤ |h * (φt s ψ cstar - φt s ψ (τ + h))|
          + |(h * a s ψ (τ + h)) * (φs s ψ τ - φs s ψ (τ + h))|
          + |(h * b s ψ (τ + h)) * (φψ s ψ τ - φψ s ψ (τ + h))| + |W| :=
      abs_add3_sub_le _ _ _ _
    have h5 : h * η + h * A₁ * η + h * A₁ * η + η * (2 * A₁ * h) = h * ε := by
      rw [← hηε]; ring
    linarith [h4, h1, h2, h3, hWb, h5]
  -- ## conclusion
  have hM' : |φ s' ψ' τ| ≤ M := by simpa using hM k
  have hB' : |φ s ψ (τ + h)| ≤ B := by simpa using hB k
  have hf' : |f s ψ (τ + h)| ≤ F := hf s ψ (τ + h) hτ₂pos hτ₂le
  have hc' : |c s ψ (τ + h)| ≤ C := hc s ψ (τ + h) hτ₂pos hτ₂le
  have hfc : |f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)| ≤ F + C * B := by
    have h2 : |c s ψ (τ + h) * φ s ψ (τ + h)| ≤ C * B := by
      rw [abs_mul]
      exact mul_le_mul hc' hB' (abs_nonneg _) hCnn
    calc |f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)|
        ≤ |f s ψ (τ + h)| + |c s ψ (τ + h) * φ s ψ (τ + h)| := by
          simpa using abs_sub_le (f s ψ (τ + h)) 0 (c s ψ (τ + h) * φ s ψ (τ + h))
      _ ≤ F + C * B := add_le_add hf' h2
  have hΔ : φ s ψ (τ + h) - φ s' ψ' τ
      = h * (f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)) + E := by
    rw [hEdef]; ring
  have hΔb : |φ s ψ (τ + h) - φ s' ψ' τ| ≤ h * F + h * C * B + h * ε := by
    rw [hΔ]
    calc |h * (f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)) + E|
        ≤ |h * (f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h))| + |E| := abs_add_le _ _
      _ = h * |f s ψ (τ + h) - c s ψ (τ + h) * φ s ψ (τ + h)| + |E| := by
          rw [abs_mul, abs_of_pos hhpos]
      _ ≤ h * (F + C * B) + h * ε :=
          add_le_add (mul_le_mul_of_nonneg_left hfc hhpos.le) hErr
      _ = h * F + h * C * B + h * ε := by ring
  have h1 : |φ s ψ (τ + h)| ≤ |φ s' ψ' τ| + |φ s ψ (τ + h) - φ s' ψ' τ| := by
    calc |φ s ψ (τ + h)| = |φ s' ψ' τ + (φ s ψ (τ + h) - φ s' ψ' τ)| := by
          congr 1; ring
      _ ≤ |φ s' ψ' τ| + |φ s ψ (τ + h) - φ s' ψ' τ| := abs_add_le _ _
  have hfin : M + (h * F + h * C * B + h * ε) = M + h * (C * B + F) + ε * h := by ring
  show |φ s ψ (τ + h)| ≤ M + h * (C * B + F) + ε * h
  linarith [h1, hΔb, hM', hfin]


end Work.FTS.RegExportIface.RXT
