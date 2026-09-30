import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.mbarPt_continuous
import Submission.Work.Cusp.mbarPt_eq_iff
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.beta_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### Auxiliary facts

`mbarPt : E3 → M̄` is the ceiling of the `v`-th cusp composed with the cusp coordinate: the point of
the truncation torus with cube coordinate `x`.  The three lemmas below supply exactly what the
construction of `τ_v : ℝ³/Λ_v ≃ₜ range mbarPt` needs. -/

/-- The cusp coordinate of the ceiling point over `x` is `x`. -/
private theorem xOf_ceilingPt (x : E3) : xOf (ceilingPt x) = x := by
  ext i
  fin_cases i <;> simp [xOf, ceilingPt]

/-- **The coordinate box is contained in the Euclidean ball of twice the radius.**  The coordinate
box `{|z i − c i| < δ}` is the box in which the collar chart `cuspBoxTop c δ` is stated, while
openness of a set of `E3` produces Euclidean balls; the comparison is the elementary
`‖z − c‖² = Σ (z i − c i)² ≤ 3 δ² < (2δ)²`. -/
private theorem cbox_subset_ball (c : E3) {δ : ℝ} (hδ : 0 < δ) :
    {z : E3 | ∀ i, |z i - c i| < δ} ⊆ Metric.ball c (2 * δ) := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm]
  have hsq : ‖z - c‖ ^ 2 = ∑ i : Fin 3, (z i - c i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    simp
  have h2 : ∑ i : Fin 3, (z i - c i) ^ 2 < 3 * δ ^ 2 := by
    rw [Fin.sum_univ_three]
    have h0 := hz 0; have h1 := hz 1; have h2' := hz 2
    rw [abs_lt] at h0 h1 h2'
    nlinarith [h0.1, h0.2, h1.1, h1.2, h2'.1, h2'.2]
  nlinarith [sq_nonneg (‖z - c‖ - 2 * δ), hsq, h2, hδ, norm_nonneg (z - c)]

/-- **A continuous bijection which is an open map has a continuous inverse.**  The inverse sends
`y` to any preimage of `y`; since `f` is an open map, the preimage under `g` of an open set `U` is
`f '' U`, which is open. -/
private theorem continuous_inv_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {g : Y → X} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (hop : IsOpenMap f) : Continuous g := by
  rw [continuous_def]
  intro U hU
  have h : g ⁻¹' U = f '' U := by
    ext y
    constructor
    · intro hy
      exact ⟨g y, hy, hr y⟩
    · rintro ⟨x, hx, rfl⟩
      show g (f x) ∈ U
      rw [hl x]
      exact hx
  rw [h]
  exact hop U hU

/-- **The truncation torus is the range of the ceiling map.**  The ceiling map `mbarPt : E3 → M̄` of
`CuspGlueData` (the point of `M̄` with cube coordinates `(x, β x)`) is invariant under the cusp
lattice `Λ_v` (`mbarPt_periodic`) and its fibres are exactly the cosets of `Λ_v`
(`mbarPt_eq_iff`); it is continuous (`mbarPt_continuous`).  Hence it descends to a continuous
bijection `ℝ³/Λ_v → range mbarPt`, carried by the class of `x` to the ceiling point over `x`.

It remains to see that this bijection has a continuous inverse.  This is where the *chart* content
of `CuspGlueData` enters: on every collar box `cuspBoxTop v c δ` the chart `mbarLow` is continuous,
its image on the region below the ceiling is open in `M̄` (`mbarLow_openTop`), and the image of the
*strictly* below-ceiling part misses the truncation torus `Tset` (`mbarLow_not_TsetTop`) while the
ceiling points lie on it (`mbarPt_mem`).  Consequently, for every open coordinate box `B` the set
`mbarTp '' B` is open in `range mbarPt`: `mbarLow` maps the ceiling of one box (sitting in the
below-or-at-ceiling region of that box) onto exactly the part of the range inside the open set
`mbarLow '' (box below ceiling)`.  Since `f` is therefore an open map, its inverse is continuous.

The full strength of `mbarLow` as a chart (injectivity on the boxes, `mbarLow_injTop`) is *not*
needed: only that the ceiling is the only part of the box whose image meets `Tset`. -/
theorem exists_tauHomeoMbar (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v) :
    ∃ Φ : CuspTorus v ≃ₜ Set.range D.mbarPt,
      ∀ x : E3, Φ (Quotient.mk'' x) = ⟨D.mbarPt x, Set.mem_range_self x⟩ := by
  classical
  -- ### The descended ceiling map
  let F : E3 → Set.range D.mbarPt := fun x => ⟨D.mbarPt x, Set.mem_range_self x⟩
  have hperF : ∀ x x' : E3, QuotientAddGroup.leftRel (lattice v) x x' → F x = F x' := by
    intro x x' h
    have hb : -x + x' ∈ lattice v := QuotientAddGroup.leftRel_apply.mp h
    have h1 := mbarPt_periodic a v D x (-x + x') hb
    rw [show x + (-x + x') = x' by abel] at h1
    exact Subtype.ext h1.symm
  let f : CuspTorus v → Set.range D.mbarPt := Quotient.lift F hperF
  have hf_mk : ∀ x : E3, f (Quotient.mk'' x) = F x := fun _ => rfl
  have hfc : Continuous f :=
    ((mbarPt_continuous a v D).subtype_mk (fun x => Set.mem_range_self x)).quotient_lift hperF
  -- ### Bijectivity
  have hinj : Function.Injective f := by
    intro t t' ht
    revert ht
    refine Quotient.inductionOn₂ t t' ?_
    intro x x' h
    have hx : D.mbarPt x = D.mbarPt x' := congrArg Subtype.val h
    have hd : x - x' ∈ lattice v := (mbarPt_eq_iff a v D x x').mp hx
    exact QuotientAddGroup.eq_iff_sub_mem.mpr hd
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨y, hy⟩ := w.2
    exact ⟨Quotient.mk'' y, Subtype.ext (by rw [hf_mk]; exact hy)⟩
  -- ### Openness
  have hopen : IsOpenMap f := by
    intro U hU
    let S : Set E3 := Quotient.mk'' ⁻¹' U
    have hSopen : IsOpen S := hU.preimage continuous_quotient_mk'
    -- the open collar boxes: `V c δ` is the image under the chart `mbarLow` of the part of the
    -- box `cuspBoxTop v c δ` below or at the ceiling
    let V : E3 → ℝ → Set a.Mbar :=
      fun c δ => D.mbarLow '' {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)}
    have hVopen : ∀ (c : E3) (δ : ℝ), IsOpen (V c δ) := fun c δ => D.mbarLow_openTop c δ
    -- the union of the boxes of radius `δ` around interior points, with room `2δ` inside `S`
    let Idx : Type := {p : E3 × ℝ // p.1 ∈ S ∧ 0 < p.2 ∧ Metric.ball p.1 (2 * p.2) ⊆ S}
    let O : Set a.Mbar := ⋃ (i : Idx), V i.1.1 i.1.2
    have hOopen : IsOpen O := isOpen_iUnion (fun i => hVopen i.1.1 i.1.2)
    -- `S` is saturated under the lattice
    have hSsat : ∀ (y l : E3), l ∈ lattice v → y ∈ S → y + l ∈ S := by
      intro y l hl hy
      have hmk : Quotient.mk'' (y + l) = Quotient.mk'' y :=
        QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hl)
      show Quotient.mk'' (y + l) ∈ U
      rw [hmk]
      exact hy
    -- the ceiling over a coordinate box lies in the box
    have hA1 : ∀ (c : E3) (δ : ℝ) (y : E3), (∀ i, |y i - c i| < δ) → D.mbarPt y ∈ V c δ := by
      intro c δ y hy
      show D.mbarPt y ∈ D.mbarLow '' {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)}
      have hq : ceilingPt y ∈ cuspBoxTop v c δ := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          rw [xOf_ceilingPt]
          exact hy i
        · simpa [ceilingPt] using s1_lt_beta y
        · simpa [ceilingPt] using beta_lt_sTop y
      exact ⟨ceilingPt y, ⟨hq, by rw [xOf_ceilingPt]; simp [ceilingPt]⟩, (D.mbarPt_eq y).symm⟩
    -- a point of the range inside `V c δ` is the ceiling over a lattice translate of `c`
    have hA2 : ∀ (c : E3) (δ : ℝ) (y : E3), D.mbarPt y ∈ V c δ →
        ∃ l ∈ lattice v, ∀ i, |(y + l) i - c i| < δ := by
      intro c δ y hy
      change D.mbarPt y ∈ D.mbarLow '' {q : E4 | q ∈ cuspBoxTop v c δ ∧ q 3 ≤ beta (xOf q)} at hy
      obtain ⟨q, hq, hqeq⟩ := hy
      -- the image lies on the truncation torus, so `q` is a ceiling point
      have hTset : D.mbarLow q ∈ a.Tset := by rw [hqeq]; exact D.mbarPt_mem y
      have hle : beta (xOf q) ≤ q 3 := by
        by_contra hlt
        exact D.mbarLow_not_TsetTop c δ hq.1 (lt_of_not_ge hlt) hTset
      have hq3 : q 3 = beta (xOf q) := le_antisymm hq.2 hle
      have hqe : q = ceilingPt (xOf q) := by
        ext i
        fin_cases i <;> simp [ceilingPt, xOf, hq3]
      have hmkpt : D.mbarPt (xOf q) = D.mbarPt y := by
        calc D.mbarPt (xOf q) = D.mbarLow (ceilingPt (xOf q)) := D.mbarPt_eq (xOf q)
          _ = D.mbarLow q := by rw [← hqe]
          _ = D.mbarPt y := hqeq
      refine ⟨xOf q - y, (mbarPt_eq_iff a v D (xOf q) y).mp hmkpt, ?_⟩
      intro i
      have h1 : (y + (xOf q - y)) i = (xOf q) i := by simp
      rw [h1]
      exact hq.1.1 i
    -- the two traces of `O`
    have hkey : Subtype.val ⁻¹' O = f '' U := by
      ext w
      constructor
      · -- a range point inside `O` is the ceiling over a point of `S`
        intro hw
        rw [Set.mem_preimage, show O = ⋃ (i : Idx), V i.1.1 i.1.2 from rfl, Set.mem_iUnion] at hw
        obtain ⟨i, hi⟩ := hw
        obtain ⟨hxS, hδpos, hballS⟩ := i.2
        obtain ⟨y, hy⟩ := w.2
        have hyV : D.mbarPt y ∈ V i.1.1 i.1.2 := by rw [hy]; exact hi
        obtain ⟨l, hl, hlbox⟩ := hA2 i.1.1 i.1.2 y hyV
        have hmemS : y + l ∈ S := hballS (cbox_subset_ball i.1.1 hδpos hlbox)
        have hyS : y ∈ S := by
          have h2 := hSsat (y + l) (-l) (neg_mem hl) hmemS
          rwa [add_assoc, add_neg_cancel, add_zero] at h2
        refine ⟨Quotient.mk'' y, hyS, ?_⟩
        rw [hf_mk]
        exact Subtype.ext hy
      · -- the ceiling over a point of `S` is inside `O`
        intro hw
        obtain ⟨t, htU, ht⟩ := hw
        obtain ⟨y, rfl⟩ := Quotient.mk''_surjective t
        have hyS : y ∈ S := htU
        obtain ⟨ε, hεpos, hεS⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hyS)
        have hδpos : 0 < ε / 2 := by linarith
        have hball : Metric.ball y (2 * (ε / 2)) ⊆ S := by
          rw [show 2 * (ε / 2) = ε by ring]
          exact hεS
        show w.val ∈ O
        refine Set.mem_iUnion.mpr ⟨⟨(y, ε / 2), hyS, hδpos, hball⟩, ?_⟩
        have hybox : ∀ i, |y i - y i| < ε / 2 := by intro i; simp [hδpos]
        have hmem : D.mbarPt y ∈ V y (ε / 2) := hA1 y (ε / 2) y hybox
        have hwy : D.mbarPt y = w.val := by
          rw [hf_mk] at ht
          exact congrArg Subtype.val ht
        rw [← hwy]
        exact hmem
    rw [isOpen_induced_iff]
    exact ⟨O, hOopen, hkey⟩
  -- ### The homeomorphism
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  refine ⟨⟨Equiv.ofBijective f hbij, ?_, ?_⟩, ?_⟩
  · show Continuous f
    exact hfc
  · exact continuous_inv_of_isOpenMap (Equiv.ofBijective f hbij).left_inv
      (Equiv.ofBijective f hbij).right_inv hopen
  · intro x
    show Equiv.ofBijective f hbij (Quotient.mk'' x) = ⟨D.mbarPt x, Set.mem_range_self x⟩
    rw [Equiv.ofBijective_apply, hf_mk]

end Work.Cusp
