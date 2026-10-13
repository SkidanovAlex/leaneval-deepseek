/-
  A cylindrical cell `κ ⊆ ℝ^p` (in the sense of `WilkiesDesign.IsCell`) that has nonempty interior
  is open.

  The proof rests on the level-by-level description of cells.  A `graph` level of a cell is
  contained in the graph of a function, which has empty interior in the ambient space (a small
  displacement in the last coordinate direction leaves the graph).  A `band` level over a base `C`
  is open whenever `C` is open (the defining inequalities are strict, the boundary functions are
  continuous on `C`, and one can squeeze the vertical coordinate between two real levels), and its
  interior is empty whenever that of `C` is (a ball inside the band projects onto a ball inside
  `C`).  Hence, by induction on the cell, every cell is either open or has empty interior.

  The target lemma is the specialisation "nonempty interior ⟹ open".
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilCrux

open WilkiesDesign

/-! ## 0. Metric kinematics of `ℝ^{n+1} = ℝ^n × ℝ` -/

/-- `Fin.init` (drop the last coordinate) is continuous. -/
theorem continuous_finInit {n : ℕ} :
    Continuous (fun z : Fin (n + 1) → ℝ => Fin.init z) := by
  refine continuous_pi fun i => ?_
  simpa [Fin.init] using continuous_apply i.castSucc

/-- If `y` is `ε`-close to the initial segment of `z` and `t` is `ε`-close to the last coordinate
of `z`, then the tuple `Fin.snoc y t` is `ε`-close to `z`.  In other words the decomposition
`ℝ^{n+1} = ℝ^n × ℝ` is metric. -/
theorem dist_snoc_lt {n : ℕ} {y : Fin n → ℝ} {z : Fin (n + 1) → ℝ} {t ε : ℝ}
    (hε : 0 < ε) (hy : dist y (Fin.init z) < ε) (ht : dist t (z (Fin.last n)) < ε) :
    dist ((Fin.snoc y t : Fin (n + 1) → ℝ)) z < ε := by
  rw [dist_pi_lt_iff hε]
  intro i
  refine Fin.lastCases (motive := fun i =>
    dist ((Fin.snoc y t : Fin (n + 1) → ℝ) i) (z i) < ε) ?_ ?_ i
  · simpa using ht
  · intro j
    have h := dist_le_pi_dist y (Fin.init z) j
    simpa [Fin.init] using lt_of_le_of_lt h hy

/-! ## 1. Graphs have empty interior -/

/-- The graph of any function `f : ℝ^n → ℝ` has empty interior in `ℝ^{n+1}`: from a point of the
interior one moves a little in the last coordinate direction, staying inside a ball contained in
the graph, which is impossible. -/
theorem interior_graph_eq_empty {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    interior {w : Fin (n + 1) → ℝ | w (Fin.last n) = f (Fin.init w)} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  have hxS : x (Fin.last n) = f (Fin.init x) := by simpa using interior_subset hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  have hy : dist (Fin.init x) (Fin.init x) < ε := by simpa using hε
  have ht : dist (x (Fin.last n) + ε / 2) (x (Fin.last n)) < ε := by
    rw [Real.dist_eq]
    have h₁ : x (Fin.last n) + ε / 2 - x (Fin.last n) = ε / 2 := by ring
    rw [h₁, abs_of_pos (by linarith)]
    linarith
  have hd : dist ((Fin.snoc (Fin.init x) (x (Fin.last n) + ε / 2) : Fin (n + 1) → ℝ)) x < ε :=
    dist_snoc_lt hε hy ht
  have hmem : (Fin.snoc (Fin.init x) (x (Fin.last n) + ε / 2) : Fin (n + 1) → ℝ) ∈
      {w : Fin (n + 1) → ℝ | w (Fin.last n) = f (Fin.init w)} := hball hd
  rw [Set.mem_ofPred_eq, Fin.snoc_last, Fin.init_snoc] at hmem
  linarith

/-- A graph level of a cell has empty interior. -/
theorem interior_graphCell_eq_empty {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    interior {w : Fin (n + 1) → ℝ | Fin.init w ∈ C ∧ w (Fin.last n) = f (Fin.init w)} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  have hxG : x ∈ interior {w : Fin (n + 1) → ℝ | w (Fin.last n) = f (Fin.init w)} :=
    interior_mono (fun _ hw => hw.2) hx
  rw [interior_graph_eq_empty f] at hxG
  exact hxG

/-! ## 2. Band levels -/

/-- A band cell over an *open* base `C ⊆ ℝ^n` is open in `ℝ^{n+1}`, provided the two boundary
functions are continuous on `C`.  (No nonemptiness of the band is needed.)  Around a point of the
cell one squeezes the vertical coordinate between two real levels `m₁ < zₙ < m₂` lying between the
boundary functions. -/
theorem isOpen_bandCell {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsOpen C)
    {a b : (Fin n → ℝ) → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C) :
    IsOpen {z : Fin (n + 1) → ℝ |
      Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨hzC, hza, hzb⟩ := hz
  -- squeeze the vertical coordinate between two real levels
  obtain ⟨m₁, hm₁a, hm₁z⟩ := EReal.lt_iff_exists_real_btwn.mp hza
  obtain ⟨m₂, hzm₂, hm₂b⟩ := EReal.lt_iff_exists_real_btwn.mp hzb
  refine ⟨(((fun z : Fin (n + 1) → ℝ => Fin.init z) ⁻¹' C ∩
        (fun z : Fin (n + 1) → ℝ => a (Fin.init z)) ⁻¹' Set.Iio (m₁ : EReal)) ∩
      ((fun z : Fin (n + 1) → ℝ => Fin.init z) ⁻¹' C ∩
        (fun z : Fin (n + 1) → ℝ => b (Fin.init z)) ⁻¹' Set.Ioi (m₂ : EReal))) ∩
      (fun z : Fin (n + 1) → ℝ => ((z (Fin.last n) : ℝ) : EReal)) ⁻¹' Set.Ioi (m₁ : EReal) ∩
      (fun z : Fin (n + 1) → ℝ => ((z (Fin.last n) : ℝ) : EReal)) ⁻¹' Set.Iio (m₂ : EReal),
    ?_, ?_, ?_⟩
  · rintro z' ⟨⟨⟨⟨hz'C, hz'a⟩, ⟨-, hz'b⟩⟩, hz'D⟩, hz'E⟩
    exact ⟨hz'C, hz'a.trans hz'D, hz'E.trans hz'b⟩
  · have hA : IsOpen ((fun z : Fin (n + 1) → ℝ => Fin.init z) ⁻¹' C) :=
      hC.preimage continuous_finInit
    have hAB : IsOpen ((fun z : Fin (n + 1) → ℝ => Fin.init z) ⁻¹' C ∩
        (fun z : Fin (n + 1) → ℝ => a (Fin.init z)) ⁻¹' Set.Iio (m₁ : EReal)) :=
      (ha.comp continuous_finInit.continuousOn fun _ h => h).isOpen_inter_preimage hA isOpen_Iio
    have hAC : IsOpen ((fun z : Fin (n + 1) → ℝ => Fin.init z) ⁻¹' C ∩
        (fun z : Fin (n + 1) → ℝ => b (Fin.init z)) ⁻¹' Set.Ioi (m₂ : EReal)) :=
      (hb.comp continuous_finInit.continuousOn fun _ h => h).isOpen_inter_preimage hA isOpen_Ioi
    have hD : IsOpen ((fun z : Fin (n + 1) → ℝ =>
        ((z (Fin.last n) : ℝ) : EReal)) ⁻¹' Set.Ioi (m₁ : EReal)) :=
      isOpen_Ioi.preimage (continuous_coe_real_ereal.comp (continuous_apply (Fin.last n)))
    have hE : IsOpen ((fun z : Fin (n + 1) → ℝ =>
        ((z (Fin.last n) : ℝ) : EReal)) ⁻¹' Set.Iio (m₂ : EReal)) :=
      isOpen_Iio.preimage (continuous_coe_real_ereal.comp (continuous_apply (Fin.last n)))
    exact ((hAB.inter hAC).inter hD).inter hE
  · exact ⟨⟨⟨⟨hzC, hm₁a⟩, ⟨hzC, hm₂b⟩⟩, hm₁z⟩, hzm₂⟩

/-- If the base of a band cell has empty interior, then so has the band cell: a ball inside the
band projects onto a ball inside the base (take the point of the ball with the same last
coordinate). -/
theorem interior_bandCell_eq_empty {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (hCint : interior C = ∅) :
    interior {w : Fin (n + 1) → ℝ | Fin.init w ∈ C ∧
        a (Fin.init w) < ((w (Fin.last n) : ℝ) : EReal) ∧
        ((w (Fin.last n) : ℝ) : EReal) < b (Fin.init w)} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  have hxC : Fin.init x ∈ interior C := by
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨ε, hε, fun y hy => ?_⟩
    have ht : dist (x (Fin.last n)) (x (Fin.last n)) < ε := by simpa using hε
    have hd : dist ((Fin.snoc y (x (Fin.last n)) : Fin (n + 1) → ℝ)) x < ε :=
      dist_snoc_lt hε hy ht
    have hmem : (Fin.snoc y (x (Fin.last n)) : Fin (n + 1) → ℝ) ∈
        {w : Fin (n + 1) → ℝ | Fin.init w ∈ C ∧
          a (Fin.init w) < ((w (Fin.last n) : ℝ) : EReal) ∧
          ((w (Fin.last n) : ℝ) : EReal) < b (Fin.init w)} := hball hd
    have h1 : Fin.init ((Fin.snoc y (x (Fin.last n)) : Fin (n + 1) → ℝ)) ∈ C := by
      simpa only [Set.mem_ofPred_eq] using hmem.1
    simpa only [Fin.init_snoc] using h1
  rw [hCint] at hxC
  exact hxC

/-! ## 3. Every cell is open or has empty interior -/

/-- **The dichotomy for cylindrical cells.**  A cell is either open, or it has empty interior. -/
theorem isCell_open_or_interior_eq_empty {n : ℕ} {κ : Set (Fin n → ℝ)} (hκ : IsCell n κ) :
    IsOpen κ ∨ interior κ = ∅ := by
  induction hκ with
  | zero => exact Or.inl isOpen_univ
  | graph hC f hf ih => exact Or.inr (interior_graphCell_eq_empty _ f)
  | band hC a b ha hb hab ih =>
      rcases ih with hCop | hCint
      · exact Or.inl (isOpen_bandCell hCop ha hb)
      · exact Or.inr (interior_bandCell_eq_empty hCint)

/-! ## 4. The target lemma -/

theorem isOpen_of_isCell_interior_nonempty {p : ℕ} {κ : Set (Fin p → ℝ)}
    (hκ : WilkiesDesign.IsCell p κ) (hne : (interior κ).Nonempty) : IsOpen κ := by
  rcases isCell_open_or_interior_eq_empty hκ with h | h
  · exact h
  · exact absurd h hne.ne_empty

end Work.WilCrux
