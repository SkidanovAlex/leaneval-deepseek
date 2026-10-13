import Mathlib
import Submission.Work.WilkiesH.Cell
import Submission.Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE

/-!
# Area H (counting) — cells carry an explicit dimension datum

For the counting argument we need, for a cell `C ⊆ ℝⁿ`, not only a dimension bound
`CellDimLE n C k` but also an *embedding* `e : Fin k ↪ Fin n` of `k` coordinates together
with a section `Φ` of the coordinate projection `x ↦ x ∘ e` (so that `C` is a graph over
the selected coordinates), the inequality `k ≤ n`, and the fact that maximal dimension
`k = n` forces `C` to have nonempty interior.

The construction is the obvious one: `k` is the number of `band` steps in the cell
construction (`graph` steps leave the dimension unchanged and increase the ambient
dimension, `band` steps increase both).  Hence `k ≤ n`, with equality exactly when every
step is a `band` step, in which case the cell is a "band tower" and is open — contained in
a product of open intervals with continuously varying ends — so it has nonempty interior.

The only non-formal input is the `band` step: a band cell over a base of nonempty interior
again has nonempty interior, proved here by exhibiting an explicit open box around a point.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign

/-- **The band step has nonempty interior.**  If `C ⊆ ℝⁿ` has nonempty interior and
`a, b : C → EReal` are continuous with `a < b` pointwise, then the band cell
`{z | Fin.init z ∈ C ∧ a (Fin.init z) < z (last) < b (Fin.init z)} ⊆ ℝⁿ⁺¹` has nonempty
interior. -/
theorem bandCell_interior_nonempty {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (hint : (interior C).Nonempty) :
    (interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := hint
  have hx₀C : x₀ ∈ C := interior_subset hx₀
  obtain ⟨y₀, hy₀a, hy₀b⟩ := EReal.lt_iff_exists_real_btwn.mp (hab x₀ hx₀C)
  obtain ⟨y₁, hy₁a, hy₁y₀⟩ := EReal.lt_iff_exists_real_btwn.mp hy₀a
  obtain ⟨y₂, hy₀y₂, hy₂b⟩ := EReal.lt_iff_exists_real_btwn.mp hy₀b
  have hUa : IsOpen (interior C ∩ a ⁻¹' (Set.Iio (y₁ : EReal))) :=
    ContinuousOn.isOpen_inter_preimage (ha.mono interior_subset) isOpen_interior isOpen_Iio
  have hUb : IsOpen (interior C ∩ b ⁻¹' (Set.Ioi (y₂ : EReal))) :=
    ContinuousOn.isOpen_inter_preimage (hb.mono interior_subset) isOpen_interior isOpen_Ioi
  set U : Set (Fin n → ℝ) :=
    {x | x ∈ interior C ∧ a x < (y₁ : EReal) ∧ (y₂ : EReal) < b x} with hUdef
  have hUopen : IsOpen U := by
    have hEq : U = (interior C ∩ a ⁻¹' (Set.Iio (y₁ : EReal))) ∩
        (interior C ∩ b ⁻¹' (Set.Ioi (y₂ : EReal))) := by
      rw [hUdef]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
      tauto
    rw [hEq]; exact hUa.inter hUb
  have hx₀U : x₀ ∈ U := by
    rw [hUdef]; exact ⟨hx₀, hy₁a, hy₂b⟩
  set B : Set (Fin (n + 1) → ℝ) :=
    {z | Fin.init z ∈ U ∧ z (Fin.last n) ∈ Set.Ioo y₁ y₂} with hBdef
  have hBopen : IsOpen B := by
    have h1 : IsOpen ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' U) :=
      hUopen.preimage (continuous_pi fun i => continuous_apply (Fin.castSucc i))
    have h2 : IsOpen ((fun z : Fin (n + 1) → ℝ => z (Fin.last n)) ⁻¹' (Set.Ioo y₁ y₂)) :=
      isOpen_Ioo.preimage (continuous_apply (Fin.last n))
    have hEq : B = (Fin.init ⁻¹' U) ∩
        ((fun z : Fin (n + 1) → ℝ => z (Fin.last n)) ⁻¹' (Set.Ioo y₁ y₂)) := by
      rw [hBdef]; rfl
    rw [hEq]; exact h1.inter h2
  have hBsub : B ⊆ {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
    intro z hz
    obtain ⟨hzU, hzIoo⟩ := hz
    rw [hUdef] at hzU
    obtain ⟨hzint, hza, hzb⟩ := hzU
    rw [Set.mem_Ioo] at hzIoo
    obtain ⟨hz1, hz2⟩ := hzIoo
    exact ⟨interior_subset hzint,
      lt_trans hza (EReal.coe_lt_coe_iff.mpr hz1),
      lt_trans (EReal.coe_lt_coe_iff.mpr hz2) hzb⟩
  have hpB : Fin.snoc x₀ y₀ ∈ B := by
    rw [hBdef]
    refine ⟨?_, ?_⟩
    · rw [Fin.init_snoc]; exact hx₀U
    · rw [Fin.snoc_last, Set.mem_Ioo]
      exact ⟨EReal.coe_lt_coe_iff.mp hy₁y₀, EReal.coe_lt_coe_iff.mp hy₀y₂⟩
  exact ⟨Fin.snoc x₀ y₀, interior_maximal hBsub hBopen hpB⟩

/-- **Cell data.**  A cell `C ⊆ ℝⁿ` carries a dimension bound `k` presented by an embedding
of `k` coordinates and a section `Φ` of that coordinate projection, with `k ≤ n` and with
full dimension `k = n` forcing `C` to have nonempty interior. -/
def CellData (n : ℕ) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (e : Fin k ↪ Fin n) (Φ : (Fin k → ℝ) → (Fin n → ℝ)),
    Work.WilkiesH.CellDimLE n C k ∧ (∀ x ∈ C, Φ (x ∘ e) = x) ∧ k ≤ n ∧
    (k = n → (interior C).Nonempty)

/-- The cell construction produces cell data, by induction on `IsCell`: `graph` steps keep
`k` and increase `n`, `band` steps increase both, so `k` counts the `band` steps. -/
theorem cellData_of_isCell {N : ℕ} {C₀ : Set (Fin N → ℝ)} (hC₀ : IsCell N C₀) :
    CellData N C₀ := by
  refine IsCell.rec (motive := fun n C _ => CellData n C) ?_ ?_ ?_ hC₀
  · -- zero
    refine ⟨0, (Equiv.refl (Fin 0)).toEmbedding, id, CellDimLE.zero, ?_, ?_, ?_⟩
    · intro x _
      exact Subsingleton.elim _ _
    · exact le_refl 0
    · intro _
      exact ⟨fun i => i.elim0, by simp⟩
  · -- graph
    intro n C hC f hf ih
    obtain ⟨k, e, Φ, hcell, hsec, hle, hint⟩ := ih
    refine ⟨k, e.trans Work.WilkiesH.Cell.succEmb,
      (fun u => Fin.snoc (Φ u) (f (Φ u))), CellDimLE.graph hcell f hf, ?_, ?_, ?_⟩
    · intro z hz
      have h1 : z ∘ (e.trans Work.WilkiesH.Cell.succEmb) = (Fin.init z) ∘ e :=
        Work.WilkiesH.Cell.comp_graphEmb e z
      show Fin.snoc (Φ (z ∘ ⇑(e.trans Work.WilkiesH.Cell.succEmb)))
        (f (Φ (z ∘ ⇑(e.trans Work.WilkiesH.Cell.succEmb)))) = z
      rw [h1, hsec (Fin.init z) hz.1, ← hz.2]
      exact Fin.snoc_init_self z
    · omega
    · intro hk
      exfalso
      omega
  · -- band
    intro n C hC a b ha hb hab ih
    obtain ⟨k, e, Φ, hcell, hsec, hle, hint⟩ := ih
    refine ⟨k + 1, Work.WilkiesH.Cell.bandEmb e,
      (fun u => Fin.snoc (Φ (Fin.init u)) (u (Fin.last k))),
      CellDimLE.band hcell a b ha hb hab, ?_, ?_, ?_⟩
    · intro z hz
      have h1 : Fin.init (z ∘ Work.WilkiesH.Cell.bandEmb e) = (Fin.init z) ∘ e :=
        Work.WilkiesH.Cell.init_comp_bandEmb e z
      have h2 : (z ∘ Work.WilkiesH.Cell.bandEmb e) (Fin.last k) = z (Fin.last n) := by
        rw [Function.comp_apply, Work.WilkiesH.Cell.bandEmb_last]
      show Fin.snoc (Φ (Fin.init (z ∘ ⇑(Work.WilkiesH.Cell.bandEmb e))))
        ((z ∘ ⇑(Work.WilkiesH.Cell.bandEmb e)) (Fin.last k)) = z
      rw [h1, hsec (Fin.init z) hz.1, h2]
      exact Fin.snoc_init_self z
    · omega
    · intro hk
      have hk' : k = n := by omega
      exact bandCell_interior_nonempty ha hb hab (hint hk')

theorem cellData {n : ℕ} {C : Set (Fin n → ℝ)} (hC : WilkiesDesign.IsCell n C) :
    ∃ (k : ℕ) (e : Fin k ↪ Fin n) (Φ : (Fin k → ℝ) → (Fin n → ℝ)),
      Work.WilkiesH.CellDimLE n C k ∧ (∀ x ∈ C, Φ (x ∘ e) = x) ∧ k ≤ n ∧
      (k = n → (interior C).Nonempty) :=
  cellData_of_isCell hC

end Work.WilkiesH.Strat
