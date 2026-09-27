import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.abs_sub_lt_of_floor_div_eq
import Submission.Work.EKLC6Core.floor_div_mem_Icc
import Submission.Work.EKLC6Core.adjugate_entry_close
import Submission.Work.EKLC6Core.entrybox_card_bound

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The displacement estimate `g * w⁻¹ ∈ V (15 η)`

If `w` lies in the closed unit entry-box of `SL₃(ℝ)` and `g` agrees with `w` to within `η`
entrywise, then `g * w⁻¹` is within `15 η` of the identity: since `det w = 1` we have
`↑(g * w⁻¹) - 1 = (↑g - ↑w) * (↑w).adjugate`, the rows have length `3`, and the adjugate of an
element of the unit entry-box has entries of absolute value at most `5`
(`adjugate_entry_close` with `ε = 1`, whose `2·2` minors are bounded by `2·2 + 2·2² = 4` up to
the identity entry). -/

/-- An element of the closed unit entry-box has adjugate entries of absolute value at most `5`. -/
lemma adjugate_entry_abs_le_five {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) :
    ∀ i j, |A.adjugate i j| ≤ 5 := by
  intro i j
  have h := adjugate_entry_close (ε := 1) (by norm_num) (by norm_num) hA i j
  norm_num at h
  have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |A.adjugate i j|
      = |(A.adjugate i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
    _ ≤ |A.adjugate i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ 4 + 1 := add_le_add h h1
    _ = 5 := by norm_num

/-- If `w` is in the closed unit entry-box and `g` is entrywise within `η ≥ 0` of `w`, then
`g * w⁻¹` is within `15 η` of the identity entrywise. -/
lemma mul_inv_entry_bound {η : ℝ} (hη : 0 ≤ η)
    {g w : Matrix.SpecialLinearGroup (Fin 3) ℝ}
    (hw : ∀ i j, |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1)
    (hgw : ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (w : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ η) :
    ∀ i j, |((g * w⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 15 * η := by
  intro i j
  have hcoemul : ((g * w⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
      = (g : Matrix (Fin 3) (Fin 3) ℝ) * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  have hkey : (g : Matrix (Fin 3) (Fin 3) ℝ) * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate
      - 1 = ((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ))
            * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate := by
    rw [Matrix.sub_mul, Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe, one_smul]
  rw [hcoemul]
  have hentry : ((g : Matrix (Fin 3) (Fin 3) ℝ) * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ))
          * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j := by
    rw [← Matrix.sub_apply, hkey]
  rw [hentry]
  have hB : ∀ k, |((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k| ≤ η := by
    intro k
    rw [Matrix.sub_apply]
    exact hgw i k
  have hC : ∀ k, |(w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j| ≤ 5 :=
    fun k => adjugate_entry_abs_le_five hw k j
  calc |(((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ))
          * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j|
      = |∑ k, ((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
            * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j| := by rw [Matrix.mul_apply]
    _ ≤ ∑ k, |((g : Matrix (Fin 3) (Fin 3) ℝ) - (w : Matrix (Fin 3) (Fin 3) ℝ)) i k
            * (w : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, η * 5 :=
          Finset.sum_le_sum (fun k _ => by
            rw [abs_mul]
            exact mul_le_mul (hB k) (hC k) (abs_nonneg _) hη)
    _ = 15 * η := by rw [Fin.sum_univ_three]; ring

/-! ## The witness map of the floor grid

For `η > 0` and an integer tuple `ı : Fin 3 × Fin 3 → ℤ` we choose an element `gridWit η ı` of
`SL₃(ℝ)` whose `(i,j)`-entry has floor `ı (i,j)` after division by `η` and which lies in the
closed unit entry-box, whenever such an element exists; otherwise we fall back on the identity.
The covering argument only ever uses the tuples that really occur as the entrywise floors of an
element of the box, and for those a witness is available by construction. -/

/-- A witness for the integer tuple `ı`: any element of the closed unit entry-box whose entrywise
`⌊·/η⌋` is `ı`, if one exists, and `1` otherwise. -/
noncomputable def gridWit (η : ℝ) (ı : Fin 3 × Fin 3 → ℤ) : SL3 := by
  classical
  exact if h : (∃ h : SL3,
      (∀ i j, |(h : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) ∧
      (∀ i j, ⌊((h : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋ = ı (i, j)))
    then Classical.choose h else 1

/-- The defining property of `gridWit` at a tuple for which a witness exists. -/
lemma gridWit_spec {η : ℝ} {ı : Fin 3 × Fin 3 → ℤ}
    (hex : ∃ h : SL3,
      (∀ i j, |(h : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) ∧
      (∀ i j, ⌊((h : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋ = ı (i, j))) :
    (∀ i j, |(gridWit η ı : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) ∧
    (∀ i j, ⌊((gridWit η ı : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋ = ı (i, j)) := by
  have h : gridWit η ı = Classical.choose hex := by
    rw [gridWit]; exact dif_pos hex
  rw [h]; exact Classical.choose_spec hex

/-- The counting half of Pisa 7.46 at the level of `SL₃(ℝ)`: the entrywise box
`B = {g | ∀ i j, |g i j - 1 i j| ≤ 1}` around the identity is covered by `c * (1 + δ⁻¹)^9`
right-translates `{u * w | u ∈ V δ}` of the displacement neighbourhood `V δ`, with `c` absolute.

Suggested route: cover the 9 entries of the box by a floor grid of mesh `η = δ/48`:
`enc a := ⌊a / η⌋`, encoded into `Fin (2N+1)` with `N = ⌈2/η⌉₊ + 1` (entries of `B` lie in
`[-1,2]`, so `|enc a| ≤ N`).  If `enc a = enc b` and `|a|, |b| ≤ 2` then `|a - b| ≤ η`.  For each
index tuple `ı : Fin 3 → Fin 3 → Fin (2N+1)` choose a witness `w ı : SL3` with entries in `B`
satisfying `enc (w ı i j) = ı i j` (and `w ı = 1` if there is none).  Every `g ∈ B` is then within
`η` entrywise of the witness `w` of its own tuple, and `g * w⁻¹ ∈ V (24 η) ⊆ V δ` because
`(↑(g * w⁻¹) - 1) = (↑g - ↑w) * (↑w).adjugate` (`Matrix.SpecialLinearGroup.coe_inv`) and
`(↑w).adjugate` has entries bounded by `8` (`Matrix.adjugate_fin_three`).  Cardinality:
`S.card ≤ (2N+1)^9 ≤ (389 * (1 + δ⁻¹))^9`. -/
theorem entrybox_cover_V :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∃ S : Finset Work.EKLContract.SL3,
      (∀ g : Work.EKLContract.SL3,
        (∀ i j : Fin 3,
          |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) →
        ∃ w ∈ S, ∃ u ∈ Work.EKLContract.V δ, g = u * w) ∧
      (S.card : ℝ) ≤ C * (1 + δ⁻¹) ^ 9 := by
  obtain ⟨C, hCpos, hcard⟩ := entrybox_card_bound
  refine ⟨C, hCpos, fun δ hδ => ?_⟩
  -- mesh `η = δ/48`, grid index bound `N = ⌈96/δ⌉₊ + 1`
  set η : ℝ := δ / 48 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  set N : ℕ := ⌈(96 : ℝ) / δ⌉₊ + 1 with hNdef
  have hNbound : (2 : ℝ) / η + 1 ≤ (N : ℝ) := by
    rw [hηdef, hNdef]
    have h2η : 2 / (δ / 48) = 96 / δ := by field_simp; ring
    rw [h2η]
    push_cast
    linarith [Nat.le_ceil ((96 : ℝ) / δ)]
  -- the finite index set of integer tuples with entries in `[-N,N]`
  set I : Finset (Fin 3 × Fin 3 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 3 × Fin 3 => Finset.Icc (-(N : ℤ)) N) with hIdef
  have hIcard : I.card = (2 * N + 1) ^ 9 := by
    rw [hIdef, Fintype.card_piFinset]
    have h1 : ∀ p : Fin 3 × Fin 3, (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := fun _ => by
      rw [Int.card_Icc]
      have hcast : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, Int.toNat_natCast]
    rw [Finset.prod_congr rfl (fun p _ => h1 p), Finset.prod_const]
    simp
  refine ⟨I.image (gridWit η), ?_, ?_⟩
  · -- covering: the witness of `g`'s own floor tuple
    intro g hg
    set e : Fin 3 × Fin 3 → ℤ := fun p => ⌊((g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2) / η⌋ with he
    -- entries of the box are bounded by `2`
    have hg2 : ∀ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| ≤ 2 := by
      intro p
      have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| ≤ 1 := by
        rw [Matrix.one_apply]; split <;> simp
      calc |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|
          = |((g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2)
              + (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| := by ring_nf
        _ ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|
              + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (hg p.1 p.2) h1
        _ = 2 := by norm_num
    have hemem : e ∈ I := by
      rw [hIdef, Fintype.mem_piFinset]
      intro p
      rw [he]
      exact floor_div_mem_Icc hηpos N hNbound (hg2 p)
    -- `g` itself witnesses its own floor tuple
    have hex : ∃ h : SL3,
        (∀ i j, |(h : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) ∧
        (∀ i j, ⌊((h : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋ = e (i, j)) := by
      refine ⟨g, hg, ?_⟩
      intro i j
      rw [he]
    have hwit := gridWit_spec hex
    refine ⟨gridWit η e, Finset.mem_image.mpr ⟨e, hemem, rfl⟩, g * (gridWit η e)⁻¹, ?_, ?_⟩
    · -- `g * w⁻¹` is a displacement of radius `15 η < δ`
      intro i j
      have hclose : ∀ a b : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) a b
          - (gridWit η e : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ η := by
        intro a b
        have h1 : ⌊((g : Matrix (Fin 3) (Fin 3) ℝ) a b) / η⌋
            = ⌊((gridWit η e : Matrix (Fin 3) (Fin 3) ℝ) a b) / η⌋ := by
          have h2 := hwit.2 a b
          simpa [he] using h2.symm
        exact le_of_lt (abs_sub_lt_of_floor_div_eq hηpos h1)
      have hb := mul_inv_entry_bound (g := g) (w := gridWit η e) hηpos.le hwit.1 hclose i j
      have h15 : 15 * η < δ := by rw [hηdef]; linarith
      exact lt_of_le_of_lt hb h15
    · -- `g = (g * w⁻¹) * w`
      show g = (g * (gridWit η e)⁻¹) * gridWit η e
      rw [mul_assoc, inv_mul_cancel, mul_one]
  · -- the count
    calc ((I.image (gridWit η)).card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (((2 * N + 1) ^ 9 : ℕ) : ℝ) := by rw [hIcard]
      _ = (((2 * (⌈(96 : ℝ) / δ⌉₊ + 1) + 1) ^ 9 : ℕ) : ℝ) := by rw [hNdef]
      _ ≤ C * (1 + δ⁻¹) ^ 9 := hcard δ hδ

end Work.EKLC6Core
