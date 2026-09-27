import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.shape_orbitImage
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLProd.plaque_shape_mass`

The `ν`-mass of the `U`-shape of an orbit plaque is positive and finite.

Setting `S = (fun u => u • x₀) '' (V ε ∩ U)`, `m = generateFrom {S}` and `p = x • x₀`, the
assertion is `0 < ν p (shape m U p) ∧ ν p (shape m U p) < ⊤`, where `x ∈ V ε ∩ U` and the orbit
map `u ↦ u • x₀` is injective on `U`.

* The shape is computed by `Work.EKLProd.shape_orbitImage`:
  `shape m U p = {u ∈ U | u * x ∈ V ε}`.
* Positivity: `{u ∈ U | u * x ∈ V ε}` contains `V δ ∩ U` for a suitable `δ > 0`
  (`exists_V_mul_subset`, an explicit entrywise estimate); and `ν p (V δ ∩ U) = ν p (V δ) > 0`
  because `ν p` is carried by `U` and positive on every `V δ` (`IsLeafwise.pos`).
* Finiteness: `ν p` is a Radon measure (`IsLeafwise.radon`) and the shape is contained in the
  compact entrywise box `|u i j| ≤ 3 (1+ε) C` (with `C` the entrywise bound for `x⁻¹`,
  `Work.EKLProd.inv_entries_bound`), because `u = (u * x) * x⁻¹`.
-/

open MeasureTheory Topology
open scoped ENNReal

set_option maxHeartbeats 1000000

namespace Work.EKLProd

open Work.EKLContract

/-! ## Helper lemmas -/

/-- For `u ∈ V ε` every entry of `u` is bounded by `1 + ε`. -/
lemma mem_V_entries_le {ε : ℝ} {u : SL3} (hu : u ∈ V ε) (i j : Fin 3) :
    |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + ε := by
  have h : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε := hu i j
  have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |((u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
    _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ ε + 1 := add_le_add (le_of_lt h) h2
    _ = 1 + ε := by ring

/-- The displacement neighbourhoods `V δ` are a neighbourhood basis of the identity: for
`x ∈ V ε` there is `δ > 0` with `V δ · x ⊆ V ε`. -/
lemma exists_V_mul_subset {ε : ℝ} {x : SL3} (hx : x ∈ V ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : SL3, g ∈ V δ → g * x ∈ V ε := by
  set M : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup'
      (Finset.univ_nonempty (α := Fin 3 × Fin 3))
      (fun p : Fin 3 × Fin 3 => |(x : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hMdef
  have hMlt : M < ε := by
    rw [hMdef, Finset.sup'_lt_iff]
    intro p _
    exact hx p.1 p.2
  set Sx : ℝ := ∑ k : Fin 3, ∑ j : Fin 3, |(x : Matrix (Fin 3) (Fin 3) ℝ) k j| with hSxdef
  have hSx : 0 ≤ Sx := by
    rw [hSxdef]
    exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  set δ : ℝ := (ε - M) / (2 * (Sx + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (by linarith) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro g hg i j
  have hgg : ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ := hg
  have hgap : |(x : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
    rw [hMdef]
    exact Finset.le_sup'
      (f := fun p : Fin 3 × Fin 3 => |(x : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
  have hslice : ∑ k : Fin 3, |(x : Matrix (Fin 3) (Fin 3) ℝ) k j| ≤ Sx := by
    rw [hSxdef]
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact Finset.single_le_sum (f := fun j' : Fin 3 => |(x : Matrix (Fin 3) (Fin 3) ℝ) k j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  have hδSx : δ * Sx ≤ (ε - M) / 2 := by
    have h2 : (0 : ℝ) < 2 * (Sx + 1) := by linarith
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ h2]
    nlinarith [hMlt, hSx]
  have hdecomp : ((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (x : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ∑ k : Fin 3, ((g : Matrix (Fin 3) (Fin 3) ℝ) i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
          * (x : Matrix (Fin 3) (Fin 3) ℝ) k j := by
    rw [Matrix.mul_apply]
    have hxij : (x : Matrix (Fin 3) (Fin 3) ℝ) i j
        = ∑ k : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i k * (x : Matrix (Fin 3) (Fin 3) ℝ) k j := by
      rw [← Matrix.mul_apply, Matrix.one_mul]
    rw [hxij, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hbound : |((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (x : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ * Sx := by
    rw [hdecomp]
    calc |∑ k : Fin 3, ((g : Matrix (Fin 3) (Fin 3) ℝ) i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
            * (x : Matrix (Fin 3) (Fin 3) ℝ) k j|
        ≤ ∑ k : Fin 3, |((g : Matrix (Fin 3) (Fin 3) ℝ) i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
            * (x : Matrix (Fin 3) (Fin 3) ℝ) k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k|
            * |(x : Matrix (Fin 3) (Fin 3) ℝ) k j| := by simp [abs_mul]
      _ ≤ ∑ k : Fin 3, δ * |(x : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul_of_nonneg_right (le_of_lt (hgg i k)) (abs_nonneg _)
      _ = δ * ∑ k : Fin 3, |(x : Matrix (Fin 3) (Fin 3) ℝ) k j| := by rw [Finset.mul_sum]
      _ ≤ δ * Sx := mul_le_mul_of_nonneg_left hslice (le_of_lt hδpos)
  have hsplit : ((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
          - (x : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by ring
  have hcoe : ((g * x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  calc |((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |(((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
          - (x : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)| := by rw [hsplit]
    _ ≤ |((g : Matrix (Fin 3) (Fin 3) ℝ) * (x : Matrix (Fin 3) (Fin 3) ℝ)) i j
          - (x : Matrix (Fin 3) (Fin 3) ℝ) i j|
        + |(x : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ δ * Sx + M := by linarith
    _ ≤ (ε - M) / 2 + M := by linarith
    _ < ε := by linarith

/-! ## The main theorem -/

theorem plaque_shape_mass {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {X' : Set Work.EKLContract.X3} (hν : Work.EKLContract.IsLeafwise μ U ν X') {x₀ : Work.EKLContract.X3} {ε : ℝ} (hε : 0 < ε) (x : Work.EKLContract.SL3) (hx : x ∈ Work.EKLContract.V ε ∩ (U : Set Work.EKLContract.SL3)) (hxX : x • x₀ ∈ X') (hinj : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) :
    0 < ν (x • x₀) (Work.EKLContract.shape (MeasurableSpace.generateFrom {((fun u : Work.EKLContract.SL3 => u • x₀) '' (Work.EKLContract.V ε ∩ (U : Set Work.EKLContract.SL3)))}) U (x • x₀)) ∧ ν (x • x₀) (Work.EKLContract.shape (MeasurableSpace.generateFrom {((fun u : Work.EKLContract.SL3 => u • x₀) '' (Work.EKLContract.V ε ∩ (U : Set Work.EKLContract.SL3)))}) U (x • x₀)) < ⊤ := by
  set S : Set X3 := (fun u : SL3 => u • x₀) '' (V ε ∩ (U : Set SL3)) with hSdef
  -- ## The shape is an explicit translate of `V ε`
  have hshape : shape (MeasurableSpace.generateFrom {S}) U (x • x₀)
      = {u : SL3 | u ∈ U ∧ u * x ∈ V ε} := by
    rw [hSdef]
    rw [shape_orbitImage U x₀ (V ε ∩ (U : Set SL3)) Set.inter_subset_right hinj x hx]
    ext u
    constructor
    · rintro ⟨huU, huB⟩; exact ⟨huU, huB.1⟩
    · rintro ⟨huU, huV⟩; exact ⟨huU, huV, U.mul_mem huU hx.2⟩
  -- ## Positivity
  obtain ⟨δ, hδpos, hδsub⟩ := exists_V_mul_subset hx.1
  have hsub : V δ ∩ (U : Set SL3) ⊆ shape (MeasurableSpace.generateFrom {S}) U (x • x₀) := by
    intro u hu
    rw [hshape]
    exact ⟨hu.2, hδsub u hu.1⟩
  have hnull : ν (x • x₀) (V δ ∩ ((U : Set SL3))ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right (hν.carried (x • x₀) hxX)
  have hae : (V δ : Set SL3) =ᵐ[ν (x • x₀)] ((V δ) ∩ (U : Set SL3) : Set SL3) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨measure_mono_null ?_ hnull, ?_⟩
    · intro g hg
      exact ⟨hg.1, fun hgU => hg.2 ⟨hg.1, hgU⟩⟩
    · show ν (x • x₀) (((V δ) ∩ (U : Set SL3) : Set SL3) \ V δ) = 0
      rw [show ((V δ) ∩ (U : Set SL3) : Set SL3) \ V δ = ∅ from
        Set.sdiff_eq_empty.mpr Set.inter_subset_left, measure_empty]
  have hmeasure : ν (x • x₀) (V δ ∩ (U : Set SL3)) = ν (x • x₀) (V δ) :=
    (measure_congr hae).symm
  have hposV : 0 < ν (x • x₀) (V δ ∩ (U : Set SL3)) := by
    rw [hmeasure]; exact hν.pos (x • x₀) hxX δ hδpos
  have hposShape : 0 < ν (x • x₀) (shape (MeasurableSpace.generateFrom {S}) U (x • x₀)) :=
    lt_of_lt_of_le hposV (measure_mono hsub)
  -- ## Finiteness
  obtain ⟨C, hC⟩ := inv_entries_bound ε hε
  have h1V : (1 : SL3) ∈ V ε := by
    intro i j
    have h1 : (1 : SL3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
    rw [h1, sub_self, abs_zero]; exact hε
  have hC0 : 0 ≤ C := by
    have h := hC 1 h1V 0 0
    have h2 : (((1 : SL3))⁻¹ : SL3) 0 0 = 1 := by simp
    rw [h2] at h
    have h' : (1 : ℝ) ≤ C := by simpa using h
    linarith
  set B : ℝ := 3 * (1 + ε) * C with hBdef
  have hbound : ∀ u ∈ shape (MeasurableSpace.generateFrom {S}) U (x • x₀), ∀ i j,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B := by
    intro u hu i j
    rw [hshape] at hu
    obtain ⟨huU, huV⟩ := hu
    have h1 : (u : SL3) = (u * x) * x⁻¹ := by rw [mul_inv_cancel_right]
    have hmat : (u : Matrix (Fin 3) (Fin 3) ℝ)
        = ((u * x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * (((x⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) := by
      conv_lhs => rw [h1]
      rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [hmat, Matrix.mul_apply]
    calc |∑ k : Fin 3, ((u * x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k
            * ((x⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j|
        ≤ ∑ k : Fin 3, |((u * x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k
            * ((x⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |((u * x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k|
            * |((x⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| := by simp [abs_mul]
      _ ≤ ∑ _k : Fin 3, (1 + ε) * C := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul (mem_V_entries_le huV i k) (hC x hx.1 k j) (abs_nonneg _) (by linarith)
      _ = 3 * ((1 + ε) * C) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = B := by rw [hBdef]; ring
  have hboxsub : shape (MeasurableSpace.generateFrom {S}) U (x • x₀)
      ⊆ {g : SL3 | ∀ i j, -B ≤ g i j ∧ g i j ≤ B} := by
    intro u hu i j
    exact abs_le.mp (hbound u hu i j)
  have hcmp : IsCompact ({g : SL3 | ∀ i j, -B ≤ g i j ∧ g i j ≤ B}) :=
    sl3EntryBox_compact (fun _ _ => -B) (fun _ _ => B)
  have hfin : ν (x • x₀) (shape (MeasurableSpace.generateFrom {S}) U (x • x₀)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hboxsub)
      ((hν.radon (x • x₀) hxX).lt_top_of_isCompact hcmp)
  exact ⟨hposShape, hfin⟩

end Work.EKLProd
