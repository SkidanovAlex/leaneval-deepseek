import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.spatial_expand` — leaf port (module `LeafAux.spatial_expand`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false



/-! ## Elementary helpers -/

/-- The distance on `ℝ × ℝ × ℝ` (the max distance) is at most `δ` as soon as each of the
three coordinate differences is at most `δ`. -/
private lemma dist_triple_le {p q : ℝ × ℝ × ℝ} {δ : ℝ}
    (h1 : |p.1 - q.1| ≤ δ) (h2 : |p.2.1 - q.2.1| ≤ δ) (h3 : |p.2.2 - q.2.2| ≤ δ) :
    dist p q ≤ δ := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le h1 (max_le h2 h3)

/-- If `x` lies between `a` and `b`, then `|x - a| ≤ |b - a|`. -/
private lemma abs_sub_left_le_of_between {x a b : ℝ} (h1 : min a b ≤ x) (h2 : x ≤ max a b) :
    |x - a| ≤ |b - a| := by
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab, max_eq_right hab] at h1 h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · simp only [min_eq_right hab, max_eq_left hab] at h1 h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_sub]
    linarith

/-- `|max s s' - min s s'| = |s' - s|`. -/
private lemma abs_max_sub_min (s s' : ℝ) : |max s s' - min s s'| = |s' - s| := by
  rw [abs_of_nonneg (sub_nonneg.mpr (min_le_max (a := s) (b := s'))), max_sub_min_eq_abs]

/-- A Lipschitz bound stated with the endpoints in the `min`/`max` orientation, restated in the
`(s, s')` orientation. -/
private lemma abs_sub_swap_minmax {F : ℝ → ℝ} {s s' C : ℝ}
    (h : |F (min s s') - F (max s s')| ≤ C * |s' - s|) :
    |F s' - F s| ≤ C * |s' - s| := by
  rcases le_total s s' with hss | hss
  · simpa [min_eq_left hss, max_eq_right hss, abs_sub_comm] using h
  · simpa [min_eq_right hss, max_eq_left hss] using h

theorem spatial_expand {f fs fψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hs : ∀ s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun s' => f s' ψ τ) (fs s ψ τ) s)
    (hψ : ∀ s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun ψ' => f s ψ' τ) (fψ s ψ τ) ψ)
    (hcs : ContinuousOn (fun p : ℝ × ℝ × ℝ => fs p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hcψ : ContinuousOn (fun p : ℝ × ℝ × ℝ => fψ p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T)) :
    ∀ R ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T,
      |τ - τ'| ≤ δ →
      ∀ s ψ s' ψ' : ℝ, |s| ≤ R → |ψ| ≤ R → |s' - s| ≤ δ → |ψ' - ψ| ≤ δ →
        |f s' ψ' τ - f s ψ τ - fs s ψ τ' * (s' - s) - fψ s ψ τ' * (ψ' - ψ)|
          ≤ ε * (|s' - s| + |ψ' - ψ|) := by
  intro R ε hε
  -- The compact box on which `fs` and `fψ` are uniformly continuous.
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (-(R + 1)) (R + 1) ×ˢ Set.Icc (-(R + 1)) (R + 1) ×ˢ Set.Icc (0 : ℝ) T with hK
  have hKsub : K ⊆ Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) T := by
    intro p hp
    rw [hK] at hp
    exact ⟨trivial, trivial, hp.2.2⟩
  have hKcomp : IsCompact K := by
    rw [hK]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hucs : UniformContinuousOn (fun p : ℝ × ℝ × ℝ => fs p.1 p.2.1 p.2.2) K :=
    hKcomp.uniformContinuousOn_of_continuous (hcs.mono hKsub)
  have hucψ : UniformContinuousOn (fun p : ℝ × ℝ × ℝ => fψ p.1 p.2.1 p.2.2) K :=
    hKcomp.uniformContinuousOn_of_continuous (hcψ.mono hKsub)
  obtain ⟨δs, hδs_pos, hδs⟩ := (Metric.uniformContinuousOn_iff_le.mp hucs) (ε / 2) (by linarith)
  obtain ⟨δψ, hδψ_pos, hδψ⟩ := (Metric.uniformContinuousOn_iff_le.mp hucψ) (ε / 2) (by linarith)
  -- The uniform modulus, chosen so that it is `≤ 1` and `≤ δs, δψ`.
  set δ : ℝ := min 1 (min δs δψ) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have h1 : 0 < min (1 : ℝ) (min δs δψ) := lt_min one_pos (lt_min hδs_pos hδψ_pos)
    linarith
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    have h1 : min (1 : ℝ) (min δs δψ) ≤ 1 := min_le_left _ _
    linarith
  have hδles : δ ≤ δs := by
    rw [hδdef]
    have h1 : min (1 : ℝ) (min δs δψ) ≤ δs := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδleψ : δ ≤ δψ := by
    rw [hδdef]
    have h1 : min (1 : ℝ) (min δs δψ) ≤ δψ := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro τ hτ τ' hτ' hττ' s ψ s' ψ' hsR hψR hss' hψψ'
  -- Points of the box that do not involve the varying coordinate.
  have hs1 : |s| ≤ R + 1 := by linarith [hsR]
  have hψ1 : |ψ| ≤ R + 1 := by linarith [hψR]
  have hψ'R : |ψ'| ≤ R + 1 := by
    calc |ψ'| = |(ψ' - ψ) + ψ| := by rw [sub_add_cancel]
      _ ≤ |ψ' - ψ| + |ψ| := abs_add_le _ _
      _ ≤ δ + R := add_le_add hψψ' hψR
      _ ≤ R + 1 := by linarith [hδle1]
  have hqK : (s, ψ, τ') ∈ K := by
    rw [hK]
    exact ⟨abs_le.mp hs1, abs_le.mp hψ1, hτ'⟩
  -- Uniform bound on the `s`-derivative over the segment between `s` and `s'`.
  have hfsb : ∀ x ∈ Set.Icc (min s s') (max s s'), |fs x ψ' τ - fs s ψ τ'| ≤ ε / 2 := by
    intro x hx
    have hxs : |x - s| ≤ δ := le_trans (abs_sub_left_le_of_between hx.1 hx.2) hss'
    have hxR : |x| ≤ R + 1 := by
      calc |x| = |(x - s) + s| := by rw [sub_add_cancel]
        _ ≤ |x - s| + |s| := abs_add_le _ _
        _ ≤ δ + R := add_le_add hxs hsR
        _ ≤ R + 1 := by linarith [hδle1]
    have hpK : (x, ψ', τ) ∈ K := by
      rw [hK]
      exact ⟨abs_le.mp hxR, abs_le.mp hψ'R, hτ⟩
    have hdist : dist (x, ψ', τ) (s, ψ, τ') ≤ δs := by
      refine le_trans (dist_triple_le hxs hψψ' ?_) hδles
      simpa using hττ'
    have h' := hδs (x, ψ', τ) hpK (s, ψ, τ') hqK hdist
    simpa [Real.dist_eq] using h'
  -- Uniform bound on the `ψ`-derivative over the segment between `ψ` and `ψ'`.
  have hψb : ∀ y ∈ Set.Icc (min ψ ψ') (max ψ ψ'), |fψ s y τ - fψ s ψ τ'| ≤ ε / 2 := by
    intro y hy
    have hyψ : |y - ψ| ≤ δ := le_trans (abs_sub_left_le_of_between hy.1 hy.2) hψψ'
    have hyR : |y| ≤ R + 1 := by
      calc |y| = |(y - ψ) + ψ| := by rw [sub_add_cancel]
        _ ≤ |y - ψ| + |ψ| := abs_add_le _ _
        _ ≤ δ + R := add_le_add hyψ hψR
        _ ≤ R + 1 := by linarith [hδle1]
    have hpK : (s, y, τ) ∈ K := by
      rw [hK]
      exact ⟨abs_le.mp hs1, abs_le.mp hyR, hτ⟩
    have hdist : dist (s, y, τ) (s, ψ, τ') ≤ δψ := by
      refine le_trans (dist_triple_le ?_ hyψ ?_) hδleψ
      · simpa using hδpos.le
      · simpa using hττ'
    have h' := hδψ (s, y, τ) hpK (s, ψ, τ') hqK hdist
    simpa [Real.dist_eq] using h'
  -- Mean value theorem in the `s`-direction.
  have hA' : |(fun x => f x ψ' τ - fs s ψ τ' * x) (min s s')
      - (fun x => f x ψ' τ - fs s ψ τ' * x) (max s s')| ≤ ε / 2 * |s' - s| := by
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => f x ψ' τ - fs s ψ τ' * x)
      (f' := fun x => fs x ψ' τ - fs s ψ τ')
      (s := Set.Icc (min s s') (max s s')) (C := ε / 2)
      (fun x _ => ((hs x ψ' τ hτ).sub (hasDerivAt_const_mul (fs s ψ τ'))).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hfsb x hx)
      (convex_Icc _ _)
      (Set.mem_Icc.mpr ⟨le_rfl, min_le_max⟩)
      (Set.mem_Icc.mpr ⟨min_le_max, le_rfl⟩)
    calc |(fun x => f x ψ' τ - fs s ψ τ' * x) (min s s')
          - (fun x => f x ψ' τ - fs s ψ τ' * x) (max s s')|
        = ‖(fun x => f x ψ' τ - fs s ψ τ' * x) (max s s')
            - (fun x => f x ψ' τ - fs s ψ τ' * x) (min s s')‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ε / 2 * ‖max s s' - min s s'‖ := hmvt
      _ = ε / 2 * |s' - s| := by rw [Real.norm_eq_abs, abs_max_sub_min]
  have hA : |(f s' ψ' τ - fs s ψ τ' * s') - (f s ψ' τ - fs s ψ τ' * s)|
      ≤ ε / 2 * |s' - s| := by
    have h := abs_sub_swap_minmax (F := fun x => f x ψ' τ - fs s ψ τ' * x) (C := ε / 2) hA'
    simpa using h
  -- Mean value theorem in the `ψ`-direction.
  have hB' : |(fun y => f s y τ - fψ s ψ τ' * y) (min ψ ψ')
      - (fun y => f s y τ - fψ s ψ τ' * y) (max ψ ψ')| ≤ ε / 2 * |ψ' - ψ| := by
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => f s y τ - fψ s ψ τ' * y)
      (f' := fun y => fψ s y τ - fψ s ψ τ')
      (s := Set.Icc (min ψ ψ') (max ψ ψ')) (C := ε / 2)
      (fun y _ => ((hψ s y τ hτ).sub (hasDerivAt_const_mul (fψ s ψ τ'))).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hψb y hy)
      (convex_Icc _ _)
      (Set.mem_Icc.mpr ⟨le_rfl, min_le_max⟩)
      (Set.mem_Icc.mpr ⟨min_le_max, le_rfl⟩)
    calc |(fun y => f s y τ - fψ s ψ τ' * y) (min ψ ψ')
          - (fun y => f s y τ - fψ s ψ τ' * y) (max ψ ψ')|
        = ‖(fun y => f s y τ - fψ s ψ τ' * y) (max ψ ψ')
            - (fun y => f s y τ - fψ s ψ τ' * y) (min ψ ψ')‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ε / 2 * ‖max ψ ψ' - min ψ ψ'‖ := hmvt
      _ = ε / 2 * |ψ' - ψ| := by rw [Real.norm_eq_abs, abs_max_sub_min]
  have hB : |(f s ψ' τ - fψ s ψ τ' * ψ') - (f s ψ τ - fψ s ψ τ' * ψ)|
      ≤ ε / 2 * |ψ' - ψ| := by
    have h := abs_sub_swap_minmax (F := fun y => f s y τ - fψ s ψ τ' * y) (C := ε / 2) hB'
    simpa using h
  -- Assembly: the two one-dimensional expansions add up to the claimed expansion.
  have hkey : f s' ψ' τ - f s ψ τ - fs s ψ τ' * (s' - s) - fψ s ψ τ' * (ψ' - ψ)
      = ((f s' ψ' τ - fs s ψ τ' * s') - (f s ψ' τ - fs s ψ τ' * s))
        + ((f s ψ' τ - fψ s ψ τ' * ψ') - (f s ψ τ - fψ s ψ τ' * ψ)) := by
    ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add hA hB) ?_
  have hZ : (0 : ℝ) ≤ |s' - s| + |ψ' - ψ| := by positivity
  have hmul : (0 : ℝ) ≤ ε * (|s' - s| + |ψ' - ψ|) := mul_nonneg hε.le hZ
  nlinarith [hmul]


end Work.FTS.RegExportIface.RXT
