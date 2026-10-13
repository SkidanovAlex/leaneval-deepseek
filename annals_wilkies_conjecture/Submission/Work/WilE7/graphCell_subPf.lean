import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.LevelFibre.levelFibre_subPf

/-!
  # `Work.WilE7.graphCell_subPf`: the graph cell of one sheet is sub-Pfaffian

  Under the sheet data `hsub`/`hcov`/`hinj` (for `x ∈ C` the fibre of `S.X.set` over `x` is
  exactly the `k`-element set `{s j x}`), the cardinality datum `hcard` (the fibre has exactly
  `k` points) and the level ordering `hlvl` (`j ↦ (s j x) (Fin.last m)` is strictly increasing),
  the graph cell

      `G_i = {y : ℝ^{p+1} | Fin.init y ∈ C ∧ y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)}`

  is the projection of a semi-Pfaffian set, i.e. `SubPf (p + 1)`.

  ## The mathematics

  For `x ∈ C`, `hsub`+`hcov` say that the fibre of `S.X.set` over `x` is exactly the range
  `{s j x : j}` (`fiber_eq_range_of_sheets`), and `hlvl` says that the *level map*
  `j ↦ (s j x) (Fin.last m)` is strictly increasing along `j`.

  Hence the level map is injective on the fibre, so the set `B` of levels of the fibre has
  exactly `k` elements, and the graph cell `G_i` is the set of pairs `(x, t)` with `x ∈ C` and
  `t` the `i`-th smallest element of `B` (which is `(s i x) (Fin.last m)`).

  "`i`-th smallest" becomes *existential* once the cardinality `k` of the fibre is known: `t` is
  the `i`-th smallest level iff there are `k` fibre points `z 0, …, z (k-1)` of strictly
  increasing level with `t = (z i) (Fin.last m)` (elements `i` below and `k-1-i` above force the
  count to be exactly `i`).  Formally this is the observation that *a finite set of reals has only
  one strictly increasing enumeration* (`eq_of_strictMono_of_mem_finset`): the maps
  `l ↦ (s l x) (Fin.last m)` and `l ↦ (z l) (Fin.last m)` both map `Fin k` strictly increasingly
  into the `k`-element set `B`, so they agree (`level_eq_of_fiber_tuple`); the two implications
  are assembled in `levelFibreSet_eq_graphCell`.

  Undoing the existential over the `k` fibre points is a projection of a semi-Pfaffian set: the
  `k`-fold product of `S.X.set` with itself, glued along the base (`x`), cut by the level-ordering
  inequalities and by a semi-Pfaffian presentation of `C`.  This construction — for *arbitrary*
  `SemiPf` sets `X`, `XC` — is exactly what `Work.WilE7.LevelFibre.levelFibre_subPf` provides,
  and the final step of `graphCell_subPf` applies it and rewrites along
  `levelFibreSet_eq_graphCell`.

  (Note: `hinj` and `hcard` are in fact not needed — `hsub`+`hcov` already force the fibre to be
  the range of the sheets, which has exactly `k` elements because the level map is strictly
  increasing.  They are kept because the requested statement carries them.)
-/

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The fibre of `S.X.set` over a point of the base cell -/

/-- Over a point `x ∈ C`, the fibre of `S.X.set` is exactly the range of the sheets `s j`. -/
theorem fiber_eq_range_of_sheets {p m k : ℕ} {S : Stratum p (m + 1)}
    {C : Set (Fin p → ℝ)} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    {x : Fin p → ℝ} (hx : x ∈ C) :
    fiber S.X.set x = Set.range (fun j : Fin k => s j x) := by
  ext y
  constructor
  · intro hy
    have hmem : Fin.append x y ∈ S.X.set := hy
    have hxC : projFirst p (m + 1) (Fin.append x y) ∈ C := by
      rwa [projFirst_append]
    obtain ⟨j, hj⟩ := hcov _ hmem hxC
    exact ⟨j, by rw [projFirst_append, projSnd_append] at hj; exact hj⟩
  · rintro ⟨j, rfl⟩
    exact hsub j x hx

/-! ## Uniqueness of the increasing enumeration of a finite set of reals -/

/-- A finite set of reals has only one strictly increasing enumeration. -/
theorem eq_of_strictMono_of_mem_finset {k : ℕ} {B : Finset ℝ} (hB : B.card = k)
    {f g : Fin k → ℝ} (hf : ∀ l, f l ∈ B) (hfm : StrictMono f)
    (hg : ∀ l, g l ∈ B) (hgm : StrictMono g) : f = g := by
  rw [Finset.orderEmbOfFin_unique hB hf hfm, Finset.orderEmbOfFin_unique hB hg hgm]

/-! ## The level of one of `k` ordered fibre points -/

/-- **The counting core.**  If the fibre of `S.X.set` over `x ∈ C` is the `k`-element set
`{s j x}` with strictly increasing levels `j ↦ (s j x) (Fin.last m)`, then any `k`-tuple
`z 0, …, z (k-1)` of fibre points with strictly increasing levels satisfies
`(z i) (Fin.last m) = (s i x) (Fin.last m)`: both are the `i`-th smallest level of the fibre. -/
theorem level_eq_of_fiber_tuple {p m k : ℕ} {S : Stratum p (m + 1)}
    {C : Set (Fin p → ℝ)} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    {x : Fin p → ℝ} (hx : x ∈ C)
    {z : Fin k → (Fin (m + 1) → ℝ)} (hz : ∀ l, z l ∈ fiber S.X.set x)
    (hzmono : ∀ l l' : Fin k, l < l' → (z l) (Fin.last m) < (z l') (Fin.last m))
    (i : Fin k) :
    (z i) (Fin.last m) = (s i x) (Fin.last m) := by
  have hfib : fiber S.X.set x = Set.range (fun j : Fin k => s j x) :=
    fiber_eq_range_of_sheets hsub hcov hx
  set B : Finset ℝ := Finset.univ.image (fun l : Fin k => (s l x) (Fin.last m)) with hBdef
  have hB : B.card = k := by
    rw [hBdef, Finset.card_image_of_injOn (hlvl x hx).injective.injOn, Finset.card_univ,
      Fintype.card_fin]
  have hf : ∀ l : Fin k, (s l x) (Fin.last m) ∈ B := by
    intro l
    rw [hBdef]
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  have hg : ∀ l : Fin k, (z l) (Fin.last m) ∈ B := by
    intro l
    rw [hfib] at hz
    obtain ⟨l', hl'⟩ := hz l
    rw [hBdef]
    exact Finset.mem_image.mpr ⟨l', Finset.mem_univ l', congrFun hl' (Fin.last m)⟩
  have hfg := eq_of_strictMono_of_mem_finset hB hf (hlvl x hx) hg hzmono
  exact (congrFun hfg i).symm

/-! ## The identification of the level set with the graph cell -/

/-- **The identification.**  The set carved out by the construction
`Work.WilE7.LevelFibre.levelFibre_subPf` — `x ∈ C`, and `k` points of `S.X.set` over `x` with
strictly increasing levels, one of which has level the last coordinate — is exactly the graph
cell of the `i`-th sheet. -/
theorem levelFibreSet_eq_graphCell {p m M k : ℕ} (S : Stratum p (m + 1))
    (C : Set (Fin p → ℝ)) (XC : SemiPf (p + M)) (hC : C = projFirst p M '' XC.set)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin k)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ |
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        ∃ z : Fin k → (Fin (p + (m + 1)) → ℝ),
          (∀ l : Fin k, z l ∈ S.X.set) ∧
          (∀ l : Fin k, projFirst p (m + 1) (z l) = Fin.init y) ∧
          (∀ l l' : Fin k, l < l' →
            (z l) (Fin.natAdd p (Fin.last m)) < (z l') (Fin.natAdd p (Fin.last m))) ∧
          (z i) (Fin.natAdd p (Fin.last m)) = y (Fin.last p)} =
      {y : Fin (p + 1) → ℝ |
        Fin.init y ∈ C ∧ y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} := by
  ext y
  constructor
  · rintro ⟨⟨w, hw⟩, z, hz1, hz2, hz3, hz4⟩
    have hxC : Fin.init y ∈ C := by
      rw [hC]
      exact ⟨Fin.append (Fin.init y) w, hw, projFirst_append _ _⟩
    refine ⟨hxC, ?_⟩
    have hzfib : ∀ l : Fin k,
        projSnd p (m + 1) (z l) ∈ fiber S.X.set (Fin.init y) := by
      intro l
      show Fin.append (Fin.init y) (projSnd p (m + 1) (z l)) ∈ S.X.set
      have h1 := append_projFirst_projSnd (n := p) (m := m + 1) (z l)
      rw [hz2 l] at h1
      rw [h1]
      exact hz1 l
    have hzmono : ∀ l l' : Fin k, l < l' →
        (projSnd p (m + 1) (z l)) (Fin.last m) <
          (projSnd p (m + 1) (z l')) (Fin.last m) := by
      intro l l' hlt
      have h := hz3 l l' hlt
      simpa [WilkiesDesign.E.projSnd] using h
    have hlevel := level_eq_of_fiber_tuple hinj hsub hcov hcard hlvl hxC hzfib hzmono i
    rw [← hz4]
    exact hlevel
  · rintro ⟨hxC, hy⟩
    have hxCmem : Fin.init y ∈ C := hxC
    rw [hC] at hxC
    obtain ⟨ζ, hζmem, hζ⟩ := hxC
    refine ⟨⟨projSnd p M ζ, ?_⟩, ?_⟩
    · have h1 := append_projFirst_projSnd (n := p) (m := M) ζ
      rw [hζ] at h1
      rw [h1]
      exact hζmem
    · refine ⟨fun l => Fin.append (Fin.init y) (s l (Fin.init y)), ?_, ?_, ?_, ?_⟩
      · intro l; exact hsub l (Fin.init y) hxCmem
      · intro l; exact projFirst_append _ _
      · intro l l' hlt
        simp only [Fin.append_right]
        exact (hlvl (Fin.init y) hxCmem) hlt
      · simp only [Fin.append_right]
        exact hy.symm

/-! ## The target -/

theorem graphCell_subPf {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (C : Set (Fin p → ℝ)) (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} := by
  obtain ⟨M, XC, hC⟩ := hCpf
  rw [← levelFibreSet_eq_graphCell S C XC hC s i hinj hsub hcov hcard hlvl]
  exact Work.WilE7.LevelFibre.levelFibre_subPf (Fin.last m) i S.X XC

end Work.WilE7
