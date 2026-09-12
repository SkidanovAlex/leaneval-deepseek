import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeWitness
import Submission.Work.Dani.EscapeGlueEps

/-!
# Conjunct 2 of de Saxcé's Theorem 1: the witness plane

This file assembles the two halves of conjunct 2:

* **Step B** (`EscapeMeasure.escape_ae`, `EscapeMeasure.noRationalPoint_ae`): for almost every
  matrix `c` in the unit box, only finitely many integer times are bad, and `graphPlane c` has no
  nonzero integer point;
* **Step A + the escape assembly** (`EscapeConvert.bad_imp_event`, `EscapeWitness.escape_of_absent`):
  the absence of bad integer times upgrades to the zero escape rate of `a_t s_x ℤᵈ`;

producing the witness required by `EscapeGlueEps.conjunct2_of_witness_eps`.

Module `Submission.Work.Dani.Conjunct2`, namespace `Submission.Conjunct2`.
-/

noncomputable section

open LinearSubspaces Module Real MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Submission.Conjunct2

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The rate sequence `ε_k = 1/(ℓ(k+1))` used to index the Borel–Cantelli statements. -/
noncomputable def eps (l k : ℕ) : ℝ := 1 / ((l : ℝ) * ((k : ℝ) + 1))

theorem eps_pos (l k : ℕ) (hl0 : 0 < l) : 0 < eps l k := by
  rw [eps]
  have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  positivity

theorem eps_le (l k : ℕ) (hl0 : 0 < l) : eps l k ≤ 1 / (l : ℝ) := by
  rw [eps]
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  rw [div_le_div_iff₀ (by positivity) hlR]
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  nlinarith [h1, hlR]

/-- **The good matrix exists.**  There is a matrix `c` in the unit box such that `graphPlane c`
has no nonzero integer point and, for every `k`, only finitely many integer times are bad at
rate `ε_k`. -/
theorem good_matrix_exists {l : ℕ} (hl0 : 0 < l) (hld : l < d) :
    ∃ c : Fin l → Fin (d - l) → ℝ,
      (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1) ∧
      (∀ n : ℝᵈ, n ∈ intPoints (d := d) → n ≠ 0 →
        n ∉ Submission.EscapeMetric.graphPlane l hld c) ∧
      (∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        Submission.EscapeMeasure.rateD l (d - l) (eps l k) n ≤ 1 / 2 ∧
        c ∉ Submission.EscapeMeasure.badEvent l (d - l)
          (Submission.EscapeMeasure.rateA l (eps l k) n)
          (Submission.EscapeMeasure.rateD l (d - l) (eps l k) n)) := by
  classical
  have hm : 0 < d - l := Nat.sub_pos_of_lt hld
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  set μ : Measure (Fin l → Fin (d - l) → ℝ) :=
    volume.restrict (Submission.EscapeMeasure.box l (d - l)) with hμ
  have hboxm : MeasurableSet (Submission.EscapeMeasure.box l (d - l)) :=
    Submission.EscapeMeasure.box_measurable l (d - l)
  have hμbox : μ (Submission.EscapeMeasure.box l (d - l)) = 1 := by
    rw [hμ, MeasureTheory.Measure.restrict_apply hboxm, Set.inter_self]
    exact Submission.EscapeMeasure.volume_box l (d - l)
  have hμne : μ ≠ 0 := by
    intro h
    have h1 : (0 : Measure (Fin l → Fin (d - l) → ℝ))
        (Submission.EscapeMeasure.box l (d - l)) = 1 := by
      rw [← h]; exact hμbox
    simp at h1
  have haebox : ∀ᵐ c ∂μ, c ∈ Submission.EscapeMeasure.box l (d - l) := by
    rw [hμ]
    rw [MeasureTheory.ae_restrict_iff' hboxm]
    exact Filter.Eventually.of_forall fun c h => h
  have haeno : ∀ᵐ c ∂μ, ¬ ∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ ∃ b : Fin (d - l) → ℤ,
      ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ) := by
    rw [hμ]
    exact MeasureTheory.ae_restrict_of_ae
      (Submission.EscapeMeasure.noRationalPoint_ae l (d - l) hm)
  have haeesc : ∀ᵐ c ∂μ, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      Submission.EscapeMeasure.rateD l (d - l) (eps l k) n ≤ 1 / 2 ∧
      c ∉ Submission.EscapeMeasure.badEvent l (d - l)
        (Submission.EscapeMeasure.rateA l (eps l k) n)
        (Submission.EscapeMeasure.rateD l (d - l) (eps l k) n) := by
    rw [MeasureTheory.ae_iff]
    rw [show {c : Fin l → Fin (d - l) → ℝ | ¬ ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
          Submission.EscapeMeasure.rateD l (d - l) (eps l k) n ≤ 1 / 2 ∧
          c ∉ Submission.EscapeMeasure.badEvent l (d - l)
            (Submission.EscapeMeasure.rateA l (eps l k) n)
            (Submission.EscapeMeasure.rateD l (d - l) (eps l k) n)}
        = ⋃ k : ℕ, {c : Fin l → Fin (d - l) → ℝ | ¬ (∃ N : ℕ, ∀ n ≥ N,
          Submission.EscapeMeasure.rateD l (d - l) (eps l k) n ≤ 1 / 2 ∧
          c ∉ Submission.EscapeMeasure.badEvent l (d - l)
            (Submission.EscapeMeasure.rateA l (eps l k) n)
            (Submission.EscapeMeasure.rateD l (d - l) (eps l k) n))} from by
      ext c; simp]
    refine measure_iUnion_null fun k => ?_
    have h := MeasureTheory.ae_restrict_of_ae (s := Submission.EscapeMeasure.box l (d - l))
      (Submission.EscapeMeasure.escape_ae l (d - l) hl0 hm (eps_pos l k hl0) (eps_le l k hl0))
    have h' : ∀ᵐ c ∂μ, ∃ N : ℕ, ∀ n ≥ N,
        Submission.EscapeMeasure.rateD l (d - l) (eps l k) n ≤ 1 / 2 ∧
        c ∉ Submission.EscapeMeasure.badEvent l (d - l)
          (Submission.EscapeMeasure.rateA l (eps l k) n)
          (Submission.EscapeMeasure.rateD l (d - l) (eps l k) n) := by
      rw [hμ]; exact h
    exact MeasureTheory.ae_iff.mp h'
  haveI : Filter.NeBot (MeasureTheory.ae μ) := MeasureTheory.ae_neBot.mpr hμne
  obtain ⟨c, hbox, hno, hesc⟩ := (haebox.and (haeno.and haeesc)).exists
  exact ⟨c, hbox,
    fun n hn hn0 => Submission.EscapeWitness.graphPlane_no_intPoint hld c hno n hn hn0, hesc⟩

/-- **Conjunct 2, given conjunct 1.** -/
theorem conjunct2_of_conjunct1 {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (h1 : ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l))) :
    ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
      diophantineExponent k x = (d : ℝ≥0∞) / (k * (d - l)) := by
  classical
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  have hm : 0 < d - l := Nat.sub_pos_of_lt hld
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  obtain ⟨c, hbox, hno, hesc⟩ := good_matrix_exists (d := d) hl0 hld
  set x : Submodule ℝ ℝᵈ := Submission.EscapeMetric.graphPlane l hld c with hxdef
  have hxfin : Module.finrank ℝ x = l := by
    rw [hxdef]; exact Submission.EscapeWitness.finrank_graphPlane l hld c
  set s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ :=
    Submission.DaniOrthoRep.orthRep (le_of_lt hld) x hxfin with hsdef
  have hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) l :=
    Submission.DaniOrthoRep.orthRep_spec (le_of_lt hld) x hxfin
  -- positivity of all distances to rational `k`-planes
  have hpos : ∀ v : Submodule ℝ ℝᵈ, IsRational v → Module.finrank ℝ v = k →
      0 < distSubspaces v x := by
    intro v hv hvk
    refine Submission.EscapeWitness.dist_pos_of_no_intPoint (d := d) hk1 hvk hxfin hkl ?_ hv
    exact fun n hn hn0 => by rw [hxdef]; exact hno n hn hn0
  -- the escape property for every `ε > 0`
  have hesc_all : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Real.exp (-(ε * t)) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1 := by
    intro ε hε
    -- choose `k` with `ε_k ≤ ε`
    obtain ⟨K, hK⟩ := exists_nat_ge (1 / (ε * (l : ℝ)))
    have hεl0 : 0 < ε * (l : ℝ) := mul_pos hε hlR
    have h1 : 1 / (ε * (l : ℝ)) ≤ (K : ℝ) := hK
    have h2 : 1 ≤ ε * (l : ℝ) * (K : ℝ) := by
      rw [div_le_iff₀ hεl0] at h1
      linarith
    have hεK : eps l K ≤ ε := by
      rw [eps, div_le_iff₀ (by positivity : (0:ℝ) < (l:ℝ) * ((K:ℝ) + 1))]
      nlinarith [h2, hlR, hε]
    obtain ⟨N, hN⟩ := hesc K
    exact Submission.EscapeWitness.escape_of_absent (d := d) hl0 hld x s hs c hxdef hbox
      (eps_pos l K hl0) (eps_le l K hl0) ⟨N, hN⟩ hε hεK
  exact Submission.EscapeGlueEps.conjunct2_of_witness_eps hk1 hkl hld h1
    ⟨x, hxfin, s, hs, hpos, hesc_all⟩

end Submission.Conjunct2

end
