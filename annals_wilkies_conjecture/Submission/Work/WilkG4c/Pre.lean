/-
  WilkG4c / Pre — vocabulary and elementary cell lemmas for `DefSection`.

  * `projFirst p n : ℝ^{p+n} → ℝ^p`, the projection to the first `p` ("parameter")
    coordinates of the `Fin.append`-splitting;
  * `snocR`/`append_snocR`: `Fin.snoc` with codomain `ℝ`, and its interaction with `Fin.append`
    (the recursion adding one fibre coordinate at the end);
  * `continuousOn_append`;
  * the projection of a cell is a cell (`isCell_projFirst`);
  * a cell with nonempty interior is open (`isCell_isOpen_of_interior_nonempty`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Cell.isNowhereDense_graph

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign

/-! ## The projection to the first `p` coordinates -/

/-- The projection to the first `p` coordinates of `ℝ^{p+n}`: the "parameter" block of the
`Fin.append`-splitting. -/
def projFirst (p n : ℕ) (z : Fin (p + n) → ℝ) : Fin p → ℝ := fun i => z (Fin.castAdd n i)

@[simp] theorem projFirst_apply {p n : ℕ} (z : Fin (p + n) → ℝ) (i : Fin p) :
    projFirst p n z i = z (Fin.castAdd n i) := rfl

theorem projFirst_append {p n : ℕ} (w : Fin p → ℝ) (y : Fin n → ℝ) :
    projFirst p n (Fin.append w y) = w := by
  funext i
  exact Fin.append_left w y i

/-- Reassembling a point of `ℝ^{p+n}` from its two blocks. -/
theorem eq_append_projFirst {p n : ℕ} (z : Fin (p + n) → ℝ) :
    Fin.append (projFirst p n z) (fun j : Fin n => z (Fin.natAdd p j)) = z :=
  Fin.append_castAdd_natAdd (f := z)

theorem projFirst_image_eq {p n : ℕ} (κ : Set (Fin (p + n) → ℝ)) :
    projFirst p n '' κ = {w : Fin p → ℝ | ∃ y : Fin n → ℝ, Fin.append w y ∈ κ} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun j => z (Fin.natAdd p j), by rw [eq_append_projFirst]; exact hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨Fin.append w y, hy, projFirst_append w y⟩

theorem projFirst_succ {p n : ℕ} (z : Fin (p + (n + 1)) → ℝ) :
    projFirst p (n + 1) z = projFirst p n (Fin.init z) := by
  funext i
  show z (Fin.castAdd (n + 1) i) = z (Fin.castSucc (Fin.castAdd n i))
  rw [Fin.castSucc_castAdd]

theorem projFirst_zero {p : ℕ} (z : Fin (p + 0) → ℝ) : projFirst p 0 z = z := by
  funext i <;> rfl

theorem projFirst_zero_image {p : ℕ} (κ : Set (Fin (p + 0) → ℝ)) : projFirst p 0 '' κ = κ := by
  ext z
  constructor
  · rintro ⟨z', hz', rfl⟩
    rwa [projFirst_zero]
  · intro hz
    exact ⟨z, hz, projFirst_zero z⟩

/-! ## `Fin.snoc` with codomain `ℝ`

Nesting the dependent `Fin.snoc` leaves the codomain family undetermined, so we work with the
abbreviation `snocR` and its computation rules. -/

/-- `Fin.snoc` with codomain `ℝ`, as a plain function. -/
def snocR {n : ℕ} (u : Fin n → ℝ) (c : ℝ) : Fin (n + 1) → ℝ := Fin.snoc u c

@[simp] theorem snocR_castSucc {n : ℕ} (u : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    snocR u c i.castSucc = u i := by simp [snocR]

@[simp] theorem snocR_last {n : ℕ} (u : Fin n → ℝ) (c : ℝ) :
    snocR u c (Fin.last n) = c := by simp [snocR]

@[simp] theorem snocR_init {n : ℕ} (u : Fin n → ℝ) (c : ℝ) : Fin.init (snocR u c) = u := by
  funext i
  simp [snocR]

theorem snocR_init_last {n : ℕ} (q : Fin (n + 1) → ℝ) :
    snocR (Fin.init q) (q (Fin.last n)) = q := by
  rw [snocR, Fin.snoc_init_self]

/-- Adding a coordinate at the end commutes with `Fin.append` (Mathlib's `Fin.append_snoc`,
in the `snocR` notation). -/
theorem append_snocR {p M : ℕ} (l : Fin p → ℝ) (u : Fin M → ℝ) (c : ℝ) :
    Fin.append l (snocR u c) = snocR (Fin.append l u) c := by
  rw [snocR, Fin.append_snoc]
  rfl

theorem init_append {p n : ℕ} (w : Fin p → ℝ) (y : Fin (n + 1) → ℝ) :
    Fin.init (Fin.append (m := p) (n := n + 1) w y) =
      Fin.append (m := p) (n := n) w (Fin.init y) := by
  conv_lhs => rw [← snocR_init_last y, snocR]
  rw [Fin.append_snoc, Fin.init_snoc]

/-- `Fin.append` is continuous in both arguments. -/
theorem continuousOn_append {p n : ℕ} {O : Set (Fin p → ℝ)}
    {γ : (Fin p → ℝ) → (Fin n → ℝ)} (hγ : ContinuousOn γ O) :
    ContinuousOn (fun w => Fin.append w (γ w)) O := by
  have h : ContinuousOn (fun w : Fin p → ℝ => (w, γ w)) O := continuousOn_id.prodMk hγ
  have h2 : ContinuousOn (fun q : (Fin p → ℝ) × (Fin n → ℝ) => Fin.append q.1 q.2) Set.univ :=
    (Fin.continuous_append (X := ℝ) p n).continuousOn
  exact h2.comp h (fun _ _ => Set.mem_univ _)

/-! ## The projection of a cell -/

/-- `Fin.init` of a graph cell is its base cell. -/
theorem image_init_graph {n : ℕ} {C : Set (Fin n → ℝ)} (f : (Fin n → ℝ) → ℝ) :
    Fin.init '' {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    refine ⟨snocR x (f x), ⟨?_, ?_⟩, snocR_init x (f x)⟩
    · rw [snocR_init]; exact hx
    · rw [snocR_last, snocR_init]

/-- `Fin.init` of a band cell is its base cell. -/
theorem image_init_band {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (hab : ∀ x ∈ C, a x < b x) :
    Fin.init '' {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz.1
  · intro hx
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab x hx)
    refine ⟨snocR x t, ⟨?_, ?_, ?_⟩, snocR_init x t⟩
    · rw [snocR_init]; exact hx
    · rw [snocR_last, snocR_init]; exact ht1
    · rw [snocR_last, snocR_init]; exact ht2

/-- **The projection of a cell is a cell** (the base of the cylinder). -/
theorem isCell_projFirst : ∀ (n p : ℕ) {κ : Set (Fin (p + n) → ℝ)},
    IsCell (p + n) κ → IsCell p (projFirst p n '' κ) := by
  intro n
  induction n with
  | zero =>
      intro p κ hκ
      rwa [projFirst_zero_image]
  | succ n ih =>
      intro p κ hκ
      have h1 : projFirst p (n + 1) '' κ = projFirst p n '' (Fin.init '' κ) := by
        have h2 : projFirst p (n + 1) = projFirst p n ∘ Fin.init :=
          funext fun z => projFirst_succ z
        rw [h2]
        exact (Set.image_image (projFirst p n) Fin.init κ).symm
      rw [h1]
      cases hκ with
      | graph hC f hf =>
          rw [image_init_graph]
          exact ih p hC
      | band hC a b ha hb hab =>
          rw [image_init_band hab]
          exact ih p hC

/-! ## Openness of a cell with nonempty interior -/

theorem continuous_fin_init {n : ℕ} :
    Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  continuous_pi fun i => continuous_apply (Fin.castSucc i)

/-- `Fin.init` admits a continuous right inverse, so the interior of a preimage is contained
in the preimage of the interior. -/
theorem interior_preimage_init_subset {n : ℕ} (T : Set (Fin n → ℝ)) :
    interior ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' T) ⊆
      (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' interior T := by
  intro x hx
  rw [mem_interior_iff_mem_nhds] at hx
  rw [Set.mem_preimage, mem_interior_iff_mem_nhds]
  let g : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => snocR y (x (Fin.last n))
  have hg : Continuous g := Continuous.finSnoc continuous_id continuous_const
  have hgx : g (Fin.init x) = x := snocR_init_last x
  have hmem : g ⁻¹' (Fin.init ⁻¹' T) ∈ 𝓝 (Fin.init x) := by
    rw [← hgx] at hx
    exact hg.continuousAt.preimage_mem_nhds hx
  have hset : g ⁻¹' (Fin.init ⁻¹' T) = T := by
    ext y
    simp only [Set.mem_preimage, g, snocR_init]
  rwa [hset] at hmem

/-- A graph cell is nowhere dense, hence has empty interior. -/
theorem interior_graph_cell_eq_empty {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f C) :
    interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = ∅ :=
  Set.eq_empty_of_subset_empty
    ((interior_mono subset_closure).trans_eq (Work.WilG1.Cell.isNowhereDense_graph hf))

/-- **A cell with nonempty interior is open.** -/
theorem isCell_isOpen_of_interior_nonempty : ∀ (n : ℕ) {κ : Set (Fin n → ℝ)},
    IsCell n κ → (interior κ).Nonempty → IsOpen κ := by
  intro n
  induction n with
  | zero =>
      intro κ hκ _
      cases hκ
      exact isOpen_univ
  | succ n ih =>
      intro κ hκ hint
      cases hκ with
      | graph hC f hf =>
          rw [interior_graph_cell_eq_empty hf] at hint
          exact absurd hint Set.not_nonempty_empty
      | band hC a b ha hb hab =>
          rename_i C
          have hCint : (interior C).Nonempty := by
            by_contra h
            have h0 : interior C = ∅ := Set.not_nonempty_iff_eq_empty.mp h
            have hsub : interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
                a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
                ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} ⊆
                (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' interior C :=
              (interior_mono (fun z hz => hz.1)).trans (interior_preimage_init_subset C)
            rw [h0, Set.preimage_empty] at hsub
            exact hint.ne_empty (Set.eq_empty_of_subset_empty hsub)
          have hCopen : IsOpen C := ih hC hCint
          refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
          obtain ⟨hzC, hza, hzb⟩ := hz
          obtain ⟨q1, haq1, hq1t⟩ := EReal.exists_between_coe_real hza
          obtain ⟨q2, htq2, hq2b⟩ := EReal.exists_between_coe_real hzb
          have hW1 : IsOpen (C ∩ a ⁻¹' Set.Iio ((q1 : ℝ) : EReal)) :=
            ha.isOpen_inter_preimage hCopen isOpen_Iio
          have hW2 : IsOpen (C ∩ b ⁻¹' Set.Ioi ((q2 : ℝ) : EReal)) :=
            hb.isOpen_inter_preimage hCopen isOpen_Ioi
          have hO : IsOpen ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹'
                (C ∩ a ⁻¹' Set.Iio ((q1 : ℝ) : EReal)) ∩
              (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹'
                (C ∩ b ⁻¹' Set.Ioi ((q2 : ℝ) : EReal)) ∩
              (fun z' : Fin (n + 1) → ℝ => z' (Fin.last n)) ⁻¹' Set.Ioo q1 q2) :=
            ((hW1.preimage continuous_fin_init).inter
              (hW2.preimage continuous_fin_init)).inter
              (isOpen_Ioo.preimage (continuous_apply (Fin.last n)))
          refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
          · exact ⟨⟨⟨hzC, haq1⟩, ⟨hzC, hq2b⟩⟩,
              ⟨EReal.coe_lt_coe_iff.mp hq1t, EReal.coe_lt_coe_iff.mp htq2⟩⟩
          · rintro z' ⟨⟨⟨hz'C, hz'1⟩, ⟨-, hz'2⟩⟩, ⟨hz'3, hz'4⟩⟩
            exact ⟨hz'C, hz'1.trans_le (EReal.coe_le_coe_iff.mpr hz'3.le),
              (EReal.coe_le_coe_iff.mpr hz'4.le).trans_lt hz'2⟩

end Work.WilkG4c
