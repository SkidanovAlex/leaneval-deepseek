/-
  Area E7, item 2 (fourth piece), **open form**: the open above cell of the highest sheet is a
  `*`-set and a sub-Pfaffian set.

  This is the strict-upper-bound companion of `Submission/Work/WilE7/aboveCell_star_proved.lean`
  (the *closed* above cell, `y (Fin.last p) ≤ 1`) and of
  `Submission/Work/WilE7/AboveAux/aboveBand_star.lean` (the `*`-half alone).

  Under the sheet data of `Work.WilE7.sheetAssembly` (a stratum `S : Stratum p (m+1)` with
  `S.j = m+1`, a `SemiPf` base `Z` with `C = π_p (connectedComponentIn Z.set u₀)`, and continuous
  sheets `s j : C → ℝ^{m+1}` covering `S.X.set` over `C`), the open above cell of the *highest*
  sheet `k - 1`

    `above = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s (k-1) (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1}`

  is `Star a (c.eval D) (p+1)` and `SubPf (p+1)`, with `a`, `c` independent of `D` and `F`.

  * The `*`-half is exactly `Work.WilE7.AboveAux.aboveBand_star`: the fibre product `Z ×_C S.X`
    with the vertical coordinate appended, cut by `v₂ < t < 1`, whose connected component through
    the canonical interior point projects onto the cell.
  * The sub-Pfaffian half does **not** use `Prop9`/the component track: it is the explicit
    "counting" presentation.  For `x ∈ C` the sheets enumerate the fibre of `S.X.set` over `x`
    (`hsub` + `hcov` + `hinj`), so by `hcard` that fibre has exactly `k` points and (by `hlvl`)
    the highest level is `(s (k-1) x) (Fin.last m)`.  Hence, for `y (Fin.last p) ∈ [-1,1]`,

      `(s (k-1) (Fin.init y)) (Fin.last m) < y (Fin.last p)`

    is *equivalent* to the existential statement "there are `k` pairwise distinct points of the
    fibre over `Fin.init y` with strictly increasing levels, all below `y (Fin.last p)`": `⟹`
    take the sheets themselves, `⟸` the `k` points exhaust a fibre of cardinality `k`.  That
    existential is a projection of a semi-Pfaffian set
    (`Work.WilE7.AboveAux.aboveLevel_subPf`), and the two directions of the equivalence (together
    with `hCpf`, which writes `C` as a projection) are `Work.WilE7.aboveOpen_eq_descr` below.
  * This is where the extra hypotheses `hCpf`, `hcard` and `hlvl` of the statement are used; only
    the `*`-half needs `hGood`, `hj` and the format/degree bounds, and those enter solely through
    the `Star`-packaging of `aboveBand_star`.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.aboveCell_star_proved
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.AboveAux.aboveBand_star
import Submission.Work.WilE7.AboveAux.aboveLevel_subPf
import Submission.Work.WilE7.AboveAux.level_lt_of_fibre_chain
import Submission.Work.WilE7.AboveAux.aboveComp_sub
import Submission.Work.WilE7.AboveAux.aboveComp_cov
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.WilE7.fiberProduct_semiPf

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Elementary helpers about projections of a semi-Pfaffian set -/

/-- A point of `ℝ^{n+m}` is recovered from its first `n` and last `m` coordinates. -/
private theorem append_projFirst_projSnd' {n m : ℕ} (z : Fin (n + m) → ℝ) :
    Fin.append (projFirst n m z) (projSnd n m z) = z := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- Membership in the projection of a semi-Pfaffian set, in terms of a witness in the fibre. -/
theorem aboveCellOpen_mem_projFirst_image_iff {n M : ℕ} (X : SemiPf (n + M)) (x : Fin n → ℝ) :
    x ∈ projFirst n M '' X.set ↔ ∃ w : Fin M → ℝ, Fin.append x w ∈ X.set := by
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact ⟨projSnd n M z, by rw [← hxz, append_projFirst_projSnd']; exact hz⟩
  · rintro ⟨w, hw⟩
    exact ⟨Fin.append x w, hw, projFirst_append x w⟩

/-- The projection of a semi-Pfaffian set lies in the closed cube. -/
theorem aboveCellOpen_projFirst_image_set_subset_cube {n M : ℕ} (X : SemiPf (n + M)) :
    projFirst n M '' X.set ⊆ cubeC n := by
  rintro x ⟨z, hz, rfl⟩ i
  exact Work.WilE8.SemiPf.set_subset_cube X hz (Fin.castAdd M i)

/-- Every point of a set cut out as `projFirst n M '' X.set` lies in the closed cube. -/
private theorem mem_cubeC_of_mem_image {n M : ℕ} {X : SemiPf (n + M)}
    {C : Set (Fin n → ℝ)} (hC : C = projFirst n M '' X.set) {x : Fin n → ℝ} (hx : x ∈ C) :
    x ∈ cubeC n := by
  rw [hC] at hx
  exact aboveCellOpen_projFirst_image_set_subset_cube X hx

/-! ## The open above cell is the "`k` fibre points below the level" description -/

/-- **The open above cell of the top sheet equals the "`k` fibre points strictly below the level"
description.**

Both directions use that the sheets enumerate the fibre of `S.X.set` over a point of `C`: to
*produce* a chain of `k` strictly increasing levels below `y (Fin.last p)` we take the sheets
themselves (`hsub`, `hlvl`); to *deduce* that the level of the top sheet is below
`y (Fin.last p)` from such a chain we use `hcard` — the fibre has exactly `k` points, so the
chain exhausts it (`Work.WilE7.AboveAux.level_lt_of_fibre_chain`). -/
theorem aboveCellOpen_eq_descr {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (C : Set (Fin p → ℝ)) (M : ℕ) (XC : SemiPf (p + M))
    (hXC : C = projFirst p M '' XC.set)
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcard : ∀ x ∈ C, (fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1}
      = {y : Fin (p + 1) → ℝ | y ∈ cubeC (p + 1) ∧
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        y (Fin.last p) < 1 ∧
        ∃ z : Fin k → (Fin (p + (m + 1)) → ℝ),
          (∀ l, z l ∈ S.X.set) ∧
          (∀ l, projFirst p (m + 1) (z l) = Fin.init y) ∧
          (∀ l l', l < l' → (z l) (Fin.natAdd p (Fin.last m)) <
            (z l') (Fin.natAdd p (Fin.last m))) ∧
          (∀ l, (z l) (Fin.natAdd p (Fin.last m)) < y (Fin.last p))} := by
  classical
  set j₀ : Fin k := ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ with hj₀
  ext y
  constructor
  · -- ## the cell is contained in the description
    rintro ⟨hyC, hyL, hy1⟩
    have hyC' : Fin.init y ∈ C := hyC
    have hyL' : (s j₀ (Fin.init y)) (Fin.last m) < y (Fin.last p) := hyL
    -- the base point is in the cube
    have hxcube : Fin.init y ∈ cubeC p := mem_cubeC_of_mem_image hXC hyC
    -- the level of the top sheet is `≥ -1`
    have hLb : -1 ≤ (s j₀ (Fin.init y)) (Fin.last m) := by
      have hmem := hsub j₀ (Fin.init y) hyC'
      have h := Work.WilE8.SemiPf.set_subset_cube S.X hmem (Fin.natAdd p (Fin.last m))
      rw [Fin.append_right] at h
      linarith [neg_abs_le ((s j₀ (Fin.init y)) (Fin.last m)), h]
    refine ⟨?_, ?_, hy1, ?_⟩
    · -- `y` is in the cube
      intro i
      refine Fin.lastCases ?_ ?_ i
      · show |y (Fin.last p)| ≤ 1
        rw [abs_le]
        exact ⟨by linarith, le_of_lt hy1⟩
      · intro i
        show |y i.castSucc| ≤ 1
        have hi : y i.castSucc = Fin.init y i := rfl
        rw [hi]
        exact hxcube i
    · -- the base has a witness in `XC`
      exact (aboveCellOpen_mem_projFirst_image_iff XC (Fin.init y)).mp (by rw [← hXC]; exact hyC)
    · -- the chain given by the sheets
      refine ⟨fun l => Fin.append (Fin.init y) (s l (Fin.init y)), ?_, ?_, ?_, ?_⟩
      · intro l; exact hsub l (Fin.init y) hyC'
      · intro l; exact projFirst_append (Fin.init y) (s l (Fin.init y))
      · intro l l' hll
        simp only [Fin.append_right]
        exact hlvl (Fin.init y) hyC' hll
      · intro l
        simp only [Fin.append_right]
        have hle : l ≤ j₀ := by
          rw [Fin.le_iff_val_le_val]
          exact Nat.le_sub_one_of_lt l.isLt
        exact lt_of_le_of_lt ((hlvl (Fin.init y) hyC').monotone hle) hyL'
  · -- ## the description is contained in the cell
    rintro ⟨-, ⟨w, hw⟩, hy1, z, hzX, hzπ, hzmono, hzlt⟩
    have hxC : Fin.init y ∈ C := by
      have h : Fin.init y ∈ projFirst p M '' XC.set :=
        (aboveCellOpen_mem_projFirst_image_iff XC (Fin.init y)).mpr ⟨w, hw⟩
      rwa [← hXC] at h
    refine ⟨hxC, ?_, hy1⟩
    have h := AboveAux.level_lt_of_fibre_chain S C k hk hcard hxC
      ⟨z, hzX, hzπ, hzmono, hzlt⟩
    exact h (s j₀ (Fin.init y)) (hsub j₀ (Fin.init y) hxC)

/-! ## The target -/

theorem aboveCell_star_open {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good)
    (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} := by
  classical
  have _ := hGood
  have _ := hj
  -- the `*`-half: the open above band of the top sheet
  obtain ⟨a, c, hstar⟩ :=
    AboveAux.aboveBand_star S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
  -- the sub-Pfaffian half: the fibre-chain description of the cell
  obtain ⟨M, XC, hXC⟩ := hCpf
  have hdescr := aboveCellOpen_eq_descr S C M XC hXC k hk s hsub hcard hlvl
  have hsubpf : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := by
    rw [hdescr]
    exact AboveAux.aboveLevel_subPf S.X (Fin.last m) XC
  exact ⟨a, c, fun D F h1 h2 h3 h4 => ⟨hstar D F h1 h2 h3 h4, hsubpf⟩⟩

end Work.WilE7
