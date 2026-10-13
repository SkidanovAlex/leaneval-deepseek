/-
  WilG4c — BNZ §2.3, the fibre ends: the `lo` half and the assembly (module
  `Work.WilG4c.FiberEndsLo`).

  `FiberEndsDefs` builds the two sets `A_lo p Z`, `A_hi p Z` as first-order combinations of `Z`
  (pullbacks along `iota1`/`iota2`, coordinate comparisons, projections, complements), with the
  pointwise descriptions `mem_A_lo_snoc` / `mem_A_hi_snoc`.  Here we prove:

  * every fibre `Z_l` is contained in `(0,1)` (`fibre_subset_Ioo`), hence a nonempty one is
    bounded below and above (`bddBelow_fibre`, `bddAbove_fibre`);
  * `sInf`/`sSup` of a nonempty fibre are its greatest lower / least upper bound
    (`sInf_fibre_spec`, `sSup_fibre_spec`), with the sharpness conditions
    `∀u > sInf, ∃x ∈ Z_l, x < u` and `∀u < sSup, ∃x ∈ Z_l, u < x`;
  * `A_lo p Z = graphOf (loOf p Z)` (`graphOf_loOf_eq`), where `loOf p Z l = sInf (Z_l)` (and
    `0` on the empty fibre) — the pointwise input is `mem_A_lo_iff_eq_loOf`;
  * the assembly `stepFiberEnds_aux`: given the `Ω`-membership of `A_lo`/`A_hi` (proved in the
    sibling modules) and the analogous exactness statement for `hiOf`, the frozen statement
    `StepFiberEnds` follows.

  The interval hypothesis bounds every fibre by `(0,1)`, which is exactly what makes `sInf`/
  `sSup` genuine (greatest) lower/upper bounds.
-/
import Mathlib
import Submission.Work.WilG4c.FiberEndsDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The fibres are subsets of `(0,1)`, hence nonempty ones are bounded -/

theorem fibre_subset_Ioo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ) :
    fibre p Z l ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  have h := hI (Fin.snoc l x) hx
  rwa [Fin.snoc_last] at h

theorem bddBelow_fibre (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ) :
    BddBelow (fibre p Z l) := by
  refine ⟨0, fun x hx => ?_⟩
  have h := hI (Fin.snoc l x) hx
  rw [Fin.snoc_last] at h
  exact le_of_lt h.1

theorem bddAbove_fibre (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ) :
    BddAbove (fibre p Z l) := by
  refine ⟨1, fun x hx => ?_⟩
  have h := hI (Fin.snoc l x) hx
  rw [Fin.snoc_last] at h
  exact le_of_lt h.2

/-! ## 2. `sInf`/`sSup` of a fibre are its greatest lower / least upper bounds -/

theorem sInf_fibre_spec (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ)
    (hne : (fibre p Z l).Nonempty) :
    (∀ x ∈ fibre p Z l, sInf (fibre p Z l) ≤ x) ∧
      (∀ u : ℝ, sInf (fibre p Z l) < u → ∃ x ∈ fibre p Z l, x < u) := by
  refine ⟨fun x hx => csInf_le (bddBelow_fibre p Z hI l) hx, ?_⟩
  intro u hu
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (le_csInf hne h)) hu

theorem sSup_fibre_spec (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ)
    (hne : (fibre p Z l).Nonempty) :
    (∀ x ∈ fibre p Z l, x ≤ sSup (fibre p Z l)) ∧
      (∀ u : ℝ, u < sSup (fibre p Z l) → ∃ x ∈ fibre p Z l, u < x) := by
  refine ⟨fun x hx => le_csSup (bddAbove_fibre p Z hI l) hx, ?_⟩
  intro u hu
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (csSup_le hne h)) hu

/-! ## 3. The two ends as functions -/

theorem loOf_eq_sInf (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
    (hne : (fibre p Z l).Nonempty) : loOf p Z l = sInf (fibre p Z l) := by
  simp [loOf, hne]

theorem loOf_eq_zero (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
    (hne : ¬(fibre p Z l).Nonempty) : loOf p Z l = 0 := by
  simp [loOf, hne]

theorem hiOf_eq_sSup (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
    (hne : (fibre p Z l).Nonempty) : hiOf p Z l = sSup (fibre p Z l) := by
  simp [hiOf, hne]

theorem loOf_props (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ)
    (hne : (fibre p Z l).Nonempty) :
    (∀ x : ℝ, Fin.snoc l x ∈ Z → loOf p Z l ≤ x) ∧
      (∀ u : ℝ, loOf p Z l < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u) := by
  obtain ⟨h1, h2⟩ := sInf_fibre_spec p Z hI l hne
  rw [loOf_eq_sInf p Z l hne]
  exact ⟨fun x hx => h1 x hx, fun u hu => h2 u hu⟩

/-! ## 4. `A_lo` is the graph of `loOf` -/

theorem mem_graphOf_loOf_iff (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ graphOf (loOf p Z) ↔ y = loOf p Z l := by
  simp [graphOf]

/-- The pointwise identity: `y` is the infimum of the fibre over `l` exactly when `y` is a
lower bound of the fibre and no larger number is one. -/
theorem mem_A_lo_iff_eq_loOf (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ A_lo p Z ↔ y = loOf p Z l := by
  rw [mem_A_lo_snoc]
  by_cases hne : (fibre p Z l).Nonempty
  · rw [loOf_eq_sInf p Z l hne]
    refine ⟨fun hd => ?_, fun hy => ?_⟩
    · rcases hd with ⟨_, h1, h2⟩ | ⟨hne', _⟩
      · exact le_antisymm (le_csInf hne h1)
          (h2 _ (fun t ht => csInf_le (bddBelow_fibre p Z hI l) ht))
      · exact (hne' hne).elim
    · rw [hy]
      exact Or.inl ⟨hne, (fun t ht => csInf_le (bddBelow_fibre p Z hI l) ht),
        (fun u hu => le_csInf hne hu)⟩
  · rw [loOf_eq_zero p Z l hne]
    refine ⟨fun hd => ?_, fun hy => Or.inr ⟨hne, hy⟩⟩
    rcases hd with ⟨hne', _⟩ | ⟨_, hy'⟩
    · exact (hne hne').elim
    · exact hy'

theorem snoc_init_self (p : ℕ) (z : Fin (p + 1) → ℝ) :
    Fin.snoc (Fin.init z) (z (Fin.last p)) = z := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    rfl
  · rw [Fin.snoc_last]

/-- `A_lo p Z` is the graph of the pointwise infimum of the fibre. -/
theorem graphOf_loOf_eq (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) :
    graphOf (loOf p Z) = A_lo p Z := by
  ext z
  rw [show z = Fin.snoc (Fin.init z) (z (Fin.last p)) from (snoc_init_self p z).symm]
  rw [mem_graphOf_loOf_iff p Z (Fin.init z) (z (Fin.last p)),
    mem_A_lo_iff_eq_loOf p Z hI (Fin.init z) (z (Fin.last p))]

/-! ## 5. Assembly -/

/-- The degree budget of the two fibre ends: `100 * D + 1000`. -/
theorem eval_degPoly (D r : ℕ) :
    MvPolynomial.eval ![D, r]
        (MvPolynomial.C 1000 + MvPolynomial.C 100 * MvPolynomial.X 0) = 100 * D + 1000 := by
  simp
  omega

/-- The assembly: given the `Ω`-membership of the two fibre-end sets and the exactness
statements for the supremum end (proved in the sibling modules), the frozen statement
follows. -/
theorem stepFiberEnds_aux (S : SOMin) (m F0 : ℕ)
    (hlo : ∃ a : ℕ, ∀ (D : ℕ) (Z : Set (Fin (m + 1) → ℝ)), Z ∈ S.Ω F0 D (m + 1) →
      A_lo m Z ∈ S.Ω a (100 * D + 1000) (m + 1))
    (hhi : ∃ a : ℕ, ∀ (D : ℕ) (Z : Set (Fin (m + 1) → ℝ)), Z ∈ S.Ω F0 D (m + 1) →
      A_hi m Z ∈ S.Ω a (100 * D + 1000) (m + 1))
    (hhiG : ∀ (Z : Set (Fin (m + 1) → ℝ)),
      (∀ z ∈ Z, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1) →
      graphOf (hiOf m Z) = A_hi m Z ∧
        ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
          (∀ x : ℝ, Fin.snoc l x ∈ Z → x ≤ hiOf m Z l) ∧
          (∀ u : ℝ, u < hiOf m Z l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x)) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (Z : Set (Fin (m + 1) → ℝ)), Z ∈ S.Ω F0 D (m + 1) →
        (∀ z ∈ Z, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1) →
        ∃ (lo hi : (Fin m → ℝ) → ℝ),
          graphOf lo ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (m + 1) ∧
          graphOf hi ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (m + 1) ∧
          ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
            (∀ x : ℝ, Fin.snoc l x ∈ Z → lo l ≤ x ∧ x ≤ hi l) ∧
            (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u) ∧
            (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x) := by
  obtain ⟨a₁, h₁⟩ := hlo
  obtain ⟨a₂, h₂⟩ := hhi
  refine ⟨max a₁ a₂, MvPolynomial.C 1000 + MvPolynomial.C 100 * MvPolynomial.X 0, ?_⟩
  intro D r Z hZ hI
  refine ⟨loOf m Z, hiOf m Z, ?_, ?_, ?_⟩
  · rw [graphOf_loOf_eq m Z hI]
    refine Work.WilG1.Omega.mono (h₁ D Z hZ) (le_max_left _ _) ?_
    rw [eval_degPoly]
  · rw [(hhiG Z hI).1]
    refine Work.WilG1.Omega.mono (h₂ D Z hZ) (le_max_right _ _) ?_
    rw [eval_degPoly]
  · intro l hl
    exact ⟨fun x hx => ⟨(loOf_props m Z hI l hl).1 x hx, ((hhiG Z hI).2 l hl).1 x hx⟩,
      (loOf_props m Z hI l hl).2, ((hhiG Z hI).2 l hl).2⟩

end Work.WilG4c
