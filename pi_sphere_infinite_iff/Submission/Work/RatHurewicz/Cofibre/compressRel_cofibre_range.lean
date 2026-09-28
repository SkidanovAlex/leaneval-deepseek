import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic
import Submission.Work.RatHurewicz.Cofibre.Maps
import Submission.Work.RatHurewicz.Cofibre.Cover
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.Cofibre.UShrink
import Submission.Work.RatHurewicz.Cofibre.compressRel_cofibre_range_zero
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.ThomBordism.TwoSet.CollarSubdivision
import Submission.Work.ThomBordism.Grassmann.chartPieceCompressFarCrux
import Submission.Work.RatHurewicz.Cofibre.compressRel_cofibreV_collar

/-!
# The compression property of the cofibre of an `n`-connected map

`Work.RatHurewicz.Cofibre.compressRel_cofibre_range`: for `ι : C(F, E)` with `F` `n`-connected, the
pair `(cofibre ι, range (cofibreIncl ι))` has the compression property in dimensions `≤ n+1`.

The route (do not re-derive; the alternatives are recorded in `NOTES_compressRel.md`):

* `U := cofibreU ι = {h < 1/2}` and `V := cofibreV ι = {0 < h}` are the two open pieces of the
  cover of the cofibre, and `U ∩ V` is a collar of the punctured cone `V`;
* `compressRel_cofibreV_collar` (in `Cofibre/compressRel_cofibreV_collar.lean`) gives the
  *one-sided* compression of the pair `(V, V ∩ U)` in dimensions `≤ n+1` — here the obvious
  two-set route fails, because the complementary compression `Compress ↥U (U ∩ V)` is **false**
  in general (it would force `π_j(U) ≅ π_j(cofibre)` for `j ≤ n`);
* `Work.ThomBordism.Grassmann.processCells2` is the cell-by-cell compression that needs only the
  `V`-side input: it subdivides a map of pairs `(I^d, ∂I^d) → (cofibre, U)` into small boxes,
  pushes the `V`-labelled boxes one at a time into `U ∩ V ⊆ U` and leaves the `U`-labelled boxes
  alone.  The collared Lebesgue subdivision `SubdivisionCollared` supplies the labelling;
* finally `cofibreU ι` deformation-retracts onto `range (cofibreIncl ι)` along `uShrink`, and the
  two homotopies are spliced — this is `compressRel_range_of_cofibreU`;
* `F = ∅` is trivial: the cone on `F` is empty, so `cofibreIncl ι` is surjective.

The geometric lemmas `coneLinePath`, `cofibre_joined_range` (every point of the cofibre is joined
to the base) are kept here for reference.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Cofibre

noncomputable section
variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

theorem mul_oneMinus_mem (s t : unitInterval) :
    0 ≤ (1 - (s : ℝ)) * (t : ℝ) ∧ (1 - (s : ℝ)) * (t : ℝ) ≤ 1 := by
  constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]

/-- The "cone-line" path from the class of `(y,t)` to the base point `coneIncl y`. -/
def coneLinePath (p : F × unitInterval) :
    Path (Work.RatHurewicz.coneMk p) (Work.Stems.coneIncl p.1) where
  toFun s := Work.RatHurewicz.coneMk (p.1, ⟨(1 - (s : ℝ)) * (p.2 : ℝ), mul_oneMinus_mem s p.2⟩)
  continuous_toFun := by
    refine continuous_quotient_mk'.comp (Continuous.prodMk continuous_const ?_)
    exact Continuous.subtype_mk ((continuous_const.sub continuous_subtype_val).mul
      continuous_const) _
  source' := by
    have h : (⟨(1 - ((0:unitInterval):ℝ)) * (p.2:ℝ), mul_oneMinus_mem 0 p.2⟩ : unitInterval)
        = p.2 := Subtype.ext (by norm_num)
    show Work.RatHurewicz.coneMk (p.1, _) = Work.RatHurewicz.coneMk p
    rw [h]
  target' := by
    have h : (⟨(1 - ((1:unitInterval):ℝ)) * (p.2:ℝ), mul_oneMinus_mem 1 p.2⟩ : unitInterval)
        = 0 := Subtype.ext (by norm_num)
    show Work.RatHurewicz.coneMk (p.1, _) = Work.Stems.coneIncl p.1
    rw [h]
    rfl

/-- The range of `cofibreIncl` as a subset. -/
abbrev cofibreBase (ι : C(F, E)) : Set (cofibre ι) := Set.range ⇑(cofibreIncl ι)

/-- **Every point of the cofibre is joined to the base.** -/
theorem cofibre_joined_range (ι : C(F, E)) (z : cofibre ι) :
    ∃ b : ↥(cofibreBase ι), Nonempty (Path z (b : cofibre ι)) := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with x | Y
    · -- the `E` part
      refine ⟨⟨cofibreIncl ι x, x, rfl⟩, ⟨Path.refl _⟩⟩
    · -- the cone part: use the cone-line path
      induction Y using Quotient.inductionOn with
      | h p =>
        have hpath : Path (cofibreInclCone ι (Work.RatHurewicz.coneMk p))
            (cofibreInclCone ι (Work.Stems.coneIncl p.1)) :=
          (coneLinePath p).map (cofibreInclCone ι).continuous
        exact ⟨⟨cofibreInclCone ι (Work.Stems.coneIncl p.1),
          ι p.1, cofibreIncl_coneIncl ι p.1⟩, ⟨hpath⟩⟩

/-! ## Step 1: the cell-by-cell compression of `(cofibre, cofibreU)` -/

/-- **From the `V`-side compression to the compression of `(cofibre ι, cofibreU ι)`.**

Given the compression of the pair `(cofibreV ι, cofibreV ι ∩ cofibreU ι)` in dimensions `≤ n+1`
(which is provided by `compressRel_cofibreV_collar`, from the connectivity of `F`), the pair
`(cofibre ι, cofibreU ι)` compresses in the same dimensions.  The proof is the collared Lebesgue
subdivision of the cube plus the one-sided cell-by-cell compression
`Work.ThomBordism.Grassmann.processCells2`. -/
theorem compressRel_cofibreU_of_Vcollar {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (n : ℕ)
    (hVc : ∀ d, d ≤ n + 1 → Work.ThomBordism.TwoSet.Compress ↥(cofibreV ι)
      {v : ↥(cofibreV ι) | (v : cofibre ι) ∈ cofibreU ι} d) :
    ∀ d, d ≤ n + 1 → CompressRel (cofibre ι) (cofibreU ι) d := by
  intro d hd
  intro f hf
  classical
  obtain ⟨N, hN3, hsub⟩ := Work.ThomBordism.TwoSet.SubdivisionCollared
    (isOpen_cofibreU ι) (isOpen_cofibreV ι) (cofibreU_union_cofibreV ι) f hf
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  let lab : (Fin d → Fin N) → Bool := fun m =>
    decide (¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
      x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι)
  have hlabU : ∀ m, lab m = false → ∀ x ∈ Work.ThomBordism.TwoSet.boxSet m,
      f x ∈ cofibreU ι := by
    intro m hm
    have hm' : decide (¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι) = false := hm
    have h2 : ¬ ¬ (∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι) := of_decide_eq_false hm'
    exact fun x hx => (not_not.mp h2) x hx
  have hlabV : ∀ m, lab m = true → ∀ x ∈ Work.ThomBordism.TwoSet.boxSet m,
      f x ∈ cofibreV ι := by
    intro m hm x hx
    have hm' : decide (¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι) = true := hm
    have hneg : ¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι := of_decide_eq_true hm'
    rcases (hsub m).1 with h | h
    · exact absurd h hneg
    · exact h x hx
  have hfar : ∀ m, lab m = true → ∀ x ∈ Work.ThomBordism.TwoSet.boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ) := by
    intro m hm x hx i
    have hm' : decide (¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι) = true := hm
    have hneg : ¬ ∀ x : Work.ThomBordism.TwoSet.IC d,
        x ∈ Work.ThomBordism.TwoSet.boxSet m → f x ∈ cofibreU ι := of_decide_eq_true hm'
    have hnot : ¬ (∃ i, (m i : ℕ) = 0 ∨ (m i : ℕ) = 1 ∨ (m i : ℕ) = N - 2 ∨
        (m i : ℕ) = N - 1) := by
      rintro ⟨i, hi⟩
      exact hneg fun y hy => (hsub m).2 ⟨i, hi⟩ y hy
    have hmge : 2 ≤ (m i : ℕ) := by
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hmle : (m i : ℕ) ≤ N - 3 := by
      have h1 : (m i : ℕ) < N := (m i).isLt
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hxi := hx i
    constructor
    · have h2 : (2 : ℝ) ≤ (N : ℝ) * (x i : ℝ) := by
        have h3 : (2 : ℝ) ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast hmge
        linarith [hxi.1]
      exact (div_le_iff₀ hNpos).mpr (by linarith [h2])
    · have h2 : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) - 2 := by
        have h3 : ((m i : ℕ) + 1 : ℕ) ≤ N - 2 := by omega
        have h4 : (((m i : ℕ) + 1 : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ N)]
          norm_num
        rw [h5] at h4
        push_cast at h4
        linarith [hxi.2]
      have h6 : (x i : ℝ) ≤ ((N : ℝ) - 2) / N := by
        rw [le_div_iff₀ hNpos]
        linarith [h2]
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have h7 : ((N : ℝ) - 2) / N = 1 - 2/(N : ℝ) := by
        field_simp
      linarith [h6, h7]
  exact Work.ThomBordism.Grassmann.processCells2 (U := cofibreU ι) (V := cofibreV ι)
    (j := d) hN3 lab (fun e he => hVc e (by omega)) hfar f hlabU hlabV hf

/-! ## Step 2: shrinking `cofibreU` onto the base -/

/-- **From the compression of `(cofibre ι, cofibreU ι)` to the compression of the target pair
`(cofibre ι, range (cofibreIncl ι))`.**

The two homotopies are spliced along the half-time `t = 1/2`: the first half is the compression
into `cofibreU ι` (whose boundary values already lie in `range (cofibreIncl ι) ⊆ cofibreU ι`), the
second half is the shrink homotopy `uShrink`, which retracts `cofibreU ι` onto
`range (cofibreIncl ι)` while fixing it. -/
theorem compressRel_range_of_cofibreU {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    [Nonempty F] (ι : C(F, E)) (e₀ : E) (d : ℕ)
    (hU : CompressRel (cofibre ι) (cofibreU ι) d) :
    CompressRel (cofibre ι) (Set.range ⇑(cofibreIncl ι)) d := by
  haveI : Nonempty E := ⟨e₀⟩
  intro f hf
  have hfU : ∀ x, x ∈ Cube.boundary (Fin d) → f x ∈ cofibreU ι := by
    intro x hx
    obtain ⟨e, he⟩ := hf x hx
    rw [← he]
    exact cofibreIncl_mem_cofibreU ι e
  obtain ⟨G₁, hG₁0, hG₁bd, hG₁1⟩ := hU f hfU
  refine ⟨⟨fun p : ICube d × unitInterval =>
      if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then G₁ (p.1, clampI (2 * (p.2 : ℝ)))
      else ↑(uShrink ι e₀ (⟨G₁ (p.1, 1), hG₁1 p.1⟩, clampI (2 * (p.2 : ℝ) - 1))), ?_⟩,
    ?_, ?_, ?_⟩
  · -- continuity
    refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact G₁.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact (continuous_subtype_val.comp (uShrink ι e₀).continuous).comp
        ((Continuous.subtype_mk (f := fun p : ICube d × unitInterval => G₁ (p.1, 1))
            (G₁.continuous.comp (continuous_fst.prodMk continuous_const))
            (fun p => hG₁1 p.1)).prodMk
          (continuous_clampI.comp (by fun_prop)))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
    · intro p hp
      have h1 : clampI (2 * (p.2 : ℝ)) = (1 : unitInterval) := by
        rw [hp]; exact clampI_one'
      have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : unitInterval) := by
        have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
        rw [h2']; exact clampI_zero'
      rw [h1, h2, uShrink_zero]
  · -- the homotopy starts at `f`
    intro x
    show (if (2 : ℝ) * (((0 : unitInterval)) : ℝ) ≤ 1
      then G₁ (x, clampI (2 * (((0 : unitInterval)) : ℝ)))
      else ↑(uShrink ι e₀ (⟨G₁ (x, 1), hG₁1 x⟩,
        clampI (2 * (((0 : unitInterval)) : ℝ) - 1)))) = f x
    rw [if_pos (by norm_num),
      show (2 : ℝ) * (((0 : unitInterval)) : ℝ) = 0 by norm_num, clampI_zero']
    exact hG₁0 x
  · -- the homotopy is relative to the boundary
    intro x hx t
    show (if (2 : ℝ) * (t : ℝ) ≤ 1 then G₁ (x, clampI (2 * (t : ℝ)))
      else ↑(uShrink ι e₀ (⟨G₁ (x, 1), hG₁1 x⟩, clampI (2 * (t : ℝ) - 1)))) = f x
    by_cases hle : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [if_pos hle]
      exact hG₁bd x hx _
    · rw [if_neg hle]
      obtain ⟨e, he⟩ := hf x hx
      have hpt : (⟨G₁ (x, 1), hG₁1 x⟩ : ↥(cofibreU ι)) = cofibreUIncl ι e := by
        apply Subtype.ext
        show G₁ (x, 1) = cofibreIncl ι e
        rw [hG₁bd x hx 1]
        exact he.symm
      rw [hpt, uShrink_cofibreUIncl, cofibreUIncl_apply]
      exact he
  · -- the homotopy ends in the range of `cofibreIncl`
    intro x
    show (if (2 : ℝ) * (((1 : unitInterval)) : ℝ) ≤ 1
      then G₁ (x, clampI (2 * (((1 : unitInterval)) : ℝ)))
      else ↑(uShrink ι e₀ (⟨G₁ (x, 1), hG₁1 x⟩,
        clampI (2 * (((1 : unitInterval)) : ℝ) - 1)))) ∈ Set.range ⇑(cofibreIncl ι)
    rw [if_neg (by norm_num : ¬ (2 : ℝ) * (((1 : unitInterval)) : ℝ) ≤ 1),
      show 2 * (((1 : unitInterval)) : ℝ) - 1 = 1 by norm_num, clampI_one']
    refine ⟨cofibreURetract ι e₀ ⟨G₁ (x, 1), hG₁1 x⟩, ?_⟩
    simp only [uShrink_one, cofibreUIncl_apply]

/-! ## The target -/

/-- **The requested lemma.**  The cofibre of an `n`-connected map is `(n+1)`-connected relative to
the total space, in compression form. -/
theorem compressRel_cofibre_range {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (n : ℕ)
    (hF : ∀ (j : ℕ), j ≤ n → ∀ y : F, Subsingleton (HomotopyGroup (Fin j) F y)) :
    ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel (Work.RatHurewicz.cofibre ι)
      (Set.range ⇑(Work.RatHurewicz.cofibreIncl ι)) d := by
  rcases isEmpty_or_nonempty F with hFe | hFn
  · -- `F = ∅`: the cone on `F` is empty, so `cofibreIncl ι` is surjective
    haveI : IsEmpty F := hFe
    haveI : IsEmpty (Work.Stems.Cone F) :=
      ⟨fun y => by
        obtain ⟨a, -⟩ := Quotient.exists_rep y
        exact isEmptyElim a.1⟩
    have hsurj : Function.Surjective (cofibreIncl ι) := by
      intro z
      obtain ⟨a, rfl⟩ := Quotient.exists_rep z
      rcases a with x | y
      · exact ⟨x, rfl⟩
      · exact isEmptyElim y
    intro d _
    intro f _
    refine ⟨f.comp ⟨fun p : ICube d × unitInterval => p.1, continuous_fst⟩, ?_, ?_, ?_⟩
    · intro x; rfl
    · intro x _ t; rfl
    · intro x
      obtain ⟨e, he⟩ := hsurj (f x)
      exact ⟨e, he⟩
  · -- `F ≠ ∅`
    haveI : Nonempty F := hFn
    haveI : Nonempty E := ⟨ι (Classical.arbitrary F)⟩
    intro d hd
    exact compressRel_range_of_cofibreU ι (ι (Classical.arbitrary F)) d
      (compressRel_cofibreU_of_Vcollar ι n
        (fun e he => compressRel_cofibreV_collar ι n hF e he) d hd)

end

end Work.RatHurewicz.Cofibre
