import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.Holes
import Submission.Work.WilG4c.DS.Points
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG1.Cell.interior_preimage_init_subset
import Submission.Work.WilG4c.CellLocalSection

namespace Work.WilG4c

open WilkiesDesign
open scoped Topology

/-!
## Definable selection over a fat parameter set: helper material

The proof of `Work.WilG4c.DefinableSection` splits into three parts.

* `isCylDecomp_image_projFirst`: the projection of a cylindrical decomposition of `ℝ^{m+N}` to
  the first `m` coordinates is a cylindrical decomposition of `ℝ^m`.
* `cellSelection`: the sharp cell decomposition of `Z` (plus the fact that a *thin* cell is
  nowhere dense) produces a cell `κ ⊆ Z` which contains a point `(w0, y0)` with `y0 ∈ U` and
  whose projection is a neighbourhood of `w0`.
* `CellLocalSection` (proved in `Submission.Work.WilG4c.CellLocalSection`): a cylindrical cell
  admits a continuous local section through any point of its interior-projection.
-/

/-! ## A cell is thin or open -/

/-- `Fin.init` is continuous. -/
theorem ds_continuous_fin_init {n : ℕ} :
    Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  continuous_pi (fun i => continuous_apply i.castSucc)

/-- The graph of a function over `C` has empty interior. -/
lemma interior_graph_eq_empty {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} :
    interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = ∅ := by
  refine Set.eq_empty_of_subset_empty (fun p hp => ?_)
  have hpset := interior_subset hp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hd : dist (Fin.snoc (Fin.init p) (p (Fin.last n) + ε / 2) : Fin (n + 1) → ℝ) p = ε / 2 := by
    have h := Work.WilG1.Cell.dist_snoc_last (Fin.init p) (p (Fin.last n) + ε / 2) (p (Fin.last n))
    rw [Fin.snoc_init_self p] at h
    rw [show p (Fin.last n) + ε / 2 - p (Fin.last n) = ε / 2 by ring] at h
    rwa [abs_of_pos (by linarith : (0 : ℝ) < ε / 2)] at h
  have hqball : (Fin.snoc (Fin.init p) (p (Fin.last n) + ε / 2) : Fin (n + 1) → ℝ) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    rw [hd]
    linarith
  have hqmem := hsub hqball
  have hcontr : p (Fin.last n) + ε / 2 = f (Fin.init p) := by
    have h2 := hqmem.2
    rw [Fin.snoc_last, Fin.init_snoc] at h2
    exact h2
  rw [← hpset.2] at hcontr
  linarith [hε]

/-- The "band" between two `EReal`-valued functions continuous on an open base is open. -/
lemma isOpen_band_of_isOpen {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsOpen C)
    {a b : (Fin n → ℝ) → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C) :
    IsOpen {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hzC, hza, hzb⟩ := hz
  obtain ⟨q1, haq1, hq1z⟩ := EReal.exists_between_coe_real hza
  obtain ⟨q2, hzq2, hq2b⟩ := EReal.exists_between_coe_real hzb
  have hca : ContinuousAt a (Fin.init z) := ha.continuousAt (hC.mem_nhds hzC)
  have hcb : ContinuousAt b (Fin.init z) := hb.continuousAt (hC.mem_nhds hzC)
  have hN1 : {x : Fin n → ℝ | a x < (q1 : EReal)} ∈ 𝓝 (Fin.init z) :=
    hca.preimage_mem_nhds (isOpen_Iio.mem_nhds haq1)
  have hN2 : {x : Fin n → ℝ | (q2 : EReal) < b x} ∈ 𝓝 (Fin.init z) :=
    hcb.preimage_mem_nhds (isOpen_Ioi.mem_nhds hq2b)
  have hNC : C ∈ 𝓝 (Fin.init z) := hC.mem_nhds hzC
  have hNinit : {w : Fin (n + 1) → ℝ | Fin.init w ∈
      ({x : Fin n → ℝ | a x < (q1 : EReal)} ∩ {x : Fin n → ℝ | (q2 : EReal) < b x}) ∩ C}
      ∈ 𝓝 z :=
    (ds_continuous_fin_init.tendsto z) (Filter.inter_mem (Filter.inter_mem hN1 hN2) hNC)
  have hq1z' : q1 < z (Fin.last n) := EReal.coe_lt_coe_iff.mp hq1z
  have hzq2' : z (Fin.last n) < q2 := EReal.coe_lt_coe_iff.mp hzq2
  have hNl1 : {w : Fin (n + 1) → ℝ | q1 < w (Fin.last n)} ∈ 𝓝 z :=
    (continuous_apply (Fin.last n)).tendsto z (isOpen_Ioi.mem_nhds hq1z')
  have hNl2 : {w : Fin (n + 1) → ℝ | w (Fin.last n) < q2} ∈ 𝓝 z :=
    (continuous_apply (Fin.last n)).tendsto z (isOpen_Iio.mem_nhds hzq2')
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hNinit hNl1) hNl2) ?_
  rintro w ⟨⟨hwinit, hwl1⟩, hwl2⟩
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff] at hwinit hwl1 hwl2
  exact ⟨hwinit.2, (hwinit.1.1).trans (EReal.coe_lt_coe_iff.mpr hwl1),
    (EReal.coe_lt_coe_iff.mpr hwl2).trans (hwinit.1.2)⟩

/-- A band over a base with empty interior has empty interior. -/
lemma interior_band_eq_empty_of_interior_base_eq_empty {n : ℕ} {C : Set (Fin n → ℝ)}
    {a b : (Fin n → ℝ) → EReal} (hemp : interior C = ∅) :
    interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  have h1 : interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} ⊆ interior (Fin.init ⁻¹' C) :=
    interior_mono (fun z hz => hz.1)
  have h2 : interior ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' C) ⊆
      Fin.init ⁻¹' interior C :=
    Work.WilG1.Cell.interior_preimage_init_subset C
  have h3 : (Fin.init ⁻¹' interior C : Set (Fin (n + 1) → ℝ)) = ∅ := by rw [hemp]; simp
  rw [h3] at h2
  exact h1.trans h2

/-- A cylindrical cell either has empty interior or is open. -/
theorem isCell_interior_empty_or_isOpen {n : ℕ} {κ : Set (Fin n → ℝ)} (h : IsCell n κ) :
    interior κ = ∅ ∨ IsOpen κ := by
  induction h with
  | zero => exact Or.inr isOpen_univ
  | graph hC f hf ih => exact Or.inl interior_graph_eq_empty
  | band hC a b ha hb hab ih =>
      rcases ih with hemp | hopen
      · left
        exact interior_band_eq_empty_of_interior_base_eq_empty hemp
      · right
        exact isOpen_band_of_isOpen hopen ha hb

/-- A cell with nonempty interior is open. -/
lemma isOpen_of_isCell_of_interior_nonempty {n : ℕ} {κ : Set (Fin n → ℝ)} (h : IsCell n κ)
    (hne : (interior κ).Nonempty) : IsOpen κ := by
  rcases isCell_interior_empty_or_isOpen h with hemp | hopen
  · exact absurd (hemp ▸ hne) (by simp)
  · exact hopen

/-! ## The projected decomposition -/

/-- The projection of a cylindrical decomposition of `ℝ^{m+N}` to the first `m` coordinates is a
cylindrical decomposition of `ℝ^m`. -/
theorem isCylDecomp_image_projFirst (m : ℕ) :
    ∀ (N : ℕ) (C : Finset (Set (Fin (m + N) → ℝ))),
      IsCylDecomp (m + N) C →
      IsCylDecomp m (C.image (fun c => DS.projFirst m N '' c)) := by
  intro N
  induction N with
  | zero =>
      intro C hC
      rw [DS.projFirst_zero_image_finset]
      exact hC
  | succ N ih =>
      intro C hC
      have hC' : IsCylDecomp (m + N) (C.image (fun c => Fin.init '' c)) :=
        ((IsCylDecomp.eq_2 (m + N) C).mp hC).2.2.2
      have h3 : C.image (fun c => DS.projFirst m (N + 1) '' c)
          = (C.image (fun c => Fin.init '' c)).image (fun c => DS.projFirst m N '' c) := by
        rw [Finset.image_image]
        refine Finset.image_congr (fun c _ => ?_)
        exact (DS.projFirst_image_init (m := m) (N := N) c)
      rw [h3]
      exact ih (C.image (fun c => Fin.init '' c)) hC'

/-! ## Selection of a well-positioned cell -/

/-- **Cell selection.**  If an `Ω`-definable set `Z ⊆ ℝ^{m+N}` has fibres meeting `U` over a fat
set of parameters in `W`, then some cell `κ ⊆ Z` of the sharp cylindrical decomposition of `Z`
carries a point `(w0, y0)`, `y0 ∈ U`, and is a "full" cell over a neighbourhood of `w0`, so that
its fibre is nonempty on a whole ball around `w0`. -/
theorem cellSelection (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 : ℕ) :
    ∀ (D : ℕ) (Z : Set (Fin (m + N) → ℝ)), Z ∈ S.Ω F0 D (m + N) →
    ∀ (W : Set (Fin m → ℝ)) (_ : IsOpen W) (U : Set (Fin N → ℝ)) (_ : IsOpen U),
      (∃ w : Fin m → ℝ, w ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ w' : Fin m → ℝ, w' ∈ W →
          dist w' w < r → ∃ y : Fin N → ℝ, y ∈ U ∧ Fin.append w' y ∈ Z) →
      ∃ (κ : Set (Fin (m + N) → ℝ)) (w0 : Fin m → ℝ) (y0 : Fin N → ℝ),
        IsCell (m + N) κ ∧ κ ⊆ Z ∧ w0 ∈ W ∧ y0 ∈ U ∧ Fin.append w0 y0 ∈ κ ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin m → ℝ, dist w w0 < ε → ∃ y : Fin N → ℝ,
          Fin.append w y ∈ κ) := by
  classical
  intro D Z hZ W hW U hU hfat
  -- sharp cell decomposition of `Z`
  obtain ⟨a, bb, c, hsharp⟩ := hcd F0 (m + N)
  obtain ⟨C, hCyl, hsplit, -, hΩ⟩ := hsharp D 1 (fun _ : Fin 1 => Z) (fun _ => hZ)
  have hcover : ∀ z : Fin (m + N) → ℝ, ∃ κ ∈ C, z ∈ κ :=
    fun z => Work.WilG1.Cell.exists_mem_of_cylDecomp hCyl z
  -- the cells of `C` contained in `Z`
  set K : Finset (Set (Fin (m + N) → ℝ)) := C.filter (fun κ => κ ⊆ Z) with hKdef
  have hZeq : Z = ⋃₀ (K : Set (Set (Fin (m + N) → ℝ))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨κ, hκC, hzκ⟩ := hcover z
      have hsub : κ ⊆ Z := by
        rcases hsplit 0 κ hκC with h | hd
        · exact h
        · exact absurd hz (Set.disjoint_left.mp hd hzκ)
      exact Set.mem_sUnion.mpr
        ⟨κ, by rw [hKdef]; exact Finset.mem_filter.mpr ⟨hκC, hsub⟩, hzκ⟩
    · rintro ⟨κ, hκK, hzκ⟩
      rw [hKdef] at hκK
      exact (Finset.mem_filter.mp hκK).2 hzκ
  -- the projected decomposition
  set Cm : Finset (Set (Fin m → ℝ)) := C.image (fun c => DS.projFirst m N '' c) with hCmdef
  have hCylm : IsCylDecomp m Cm := by
    rw [hCmdef]
    exact isCylDecomp_image_projFirst m N C hCyl
  set Km : Finset (Set (Fin m → ℝ)) := K.image (fun c => DS.projFirst m N '' c) with hKmdef
  have hKm_sub : Km ⊆ Cm := by
    rw [hKmdef, hCmdef]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  set Tm : Finset (Set (Fin m → ℝ)) := Km.filter (fun ρ => interior ρ = ∅) with hTmdef
  have hTm_sub : Tm ⊆ Cm := by
    intro ρ hρ
    exact hKm_sub (Finset.mem_filter.mp hρ).1
  have hthin : interior (⋃₀ (Tm : Set (Set (Fin m → ℝ)))) = ∅ :=
    Work.WilG1.Cell.sUnion_thin hCylm Tm hTm_sub (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  -- the fat set is covered by the projections of the cells in `Z`
  obtain ⟨wstar, hwstarW, r, hr, hfat'⟩ := hfat
  have hball : Metric.ball wstar r ∩ W ⊆ ⋃₀ (Km : Set (Set (Fin m → ℝ))) := by
    intro w hw
    obtain ⟨y, hyU, hwy⟩ := hfat' w hw.2 (Metric.mem_ball.mp hw.1)
    rw [hZeq] at hwy
    obtain ⟨κ, hκK, hκ⟩ := Set.mem_sUnion.mp hwy
    refine Set.mem_sUnion.mpr ⟨DS.projFirst m N '' κ, ?_, ?_⟩
    · rw [hKmdef]; exact Finset.mem_image.mpr ⟨κ, hκK, rfl⟩
    · rw [DS.mem_projFirst_image]; exact ⟨y, hκ⟩
  -- a point of the fat set outside the thin projections
  have hnotsub : ¬ (Metric.ball wstar r ∩ W ⊆ ⋃₀ (Tm : Set (Set (Fin m → ℝ)))) := by
    intro hsub
    have h1 : interior (Metric.ball wstar r ∩ W) ⊆ interior (⋃₀ (Tm : Set (Set (Fin m → ℝ)))) :=
      interior_mono hsub
    rw [hthin] at h1
    obtain ⟨x, hx⟩ : (Metric.ball wstar r ∩ W).Nonempty :=
      ⟨wstar, Metric.mem_ball_self hr, hwstarW⟩
    exact h1 (by rw [(Metric.isOpen_ball.inter hW).interior_eq]; exact hx)
  obtain ⟨w0, hw0ballW, hw0notT⟩ := Set.not_subset.mp hnotsub
  -- a witness point of `Z` over `w0` inside `U`
  obtain ⟨y0, hy0U, hw0y0⟩ := hfat' w0 hw0ballW.2 (Metric.mem_ball.mp hw0ballW.1)
  -- the cell containing the witness
  obtain ⟨κ1, hκ1C, hκ1mem⟩ := hcover (Fin.append w0 y0)
  have hκ1sub : κ1 ⊆ Z := by
    rcases hsplit 0 κ1 hκ1C with h | hd
    · exact h
    · exact absurd hw0y0 (Set.disjoint_left.mp hd hκ1mem)
  have hκ1K : κ1 ∈ K := by
    rw [hKdef]; exact Finset.mem_filter.mpr ⟨hκ1C, hκ1sub⟩
  have hprojK : DS.projFirst m N '' κ1 ∈ Km := by
    rw [hKmdef]; exact Finset.mem_image.mpr ⟨κ1, hκ1K, rfl⟩
  have hw0proj : w0 ∈ DS.projFirst m N '' κ1 := by
    rw [DS.mem_projFirst_image]; exact ⟨y0, hκ1mem⟩
  -- the projection is not thin, hence a fat cell, hence open at `w0`
  have hnotthin : interior (DS.projFirst m N '' κ1) ≠ ∅ := by
    intro hemp
    have hmem : DS.projFirst m N '' κ1 ∈ Tm := by
      rw [hTmdef]; exact Finset.mem_filter.mpr ⟨hprojK, hemp⟩
    exact hw0notT (Set.mem_sUnion.mpr ⟨_, hmem, hw0proj⟩)
  have hcellproj : IsCell m (DS.projFirst m N '' κ1) :=
    Work.WilG1.Cell.isCell_of_mem_cylDecomp hCylm
      (by rw [hCmdef]; exact Finset.mem_image.mpr ⟨κ1, hκ1C, rfl⟩)
  have hopenproj : IsOpen (DS.projFirst m N '' κ1) :=
    isOpen_of_isCell_of_interior_nonempty hcellproj (Set.nonempty_iff_ne_empty.mpr hnotthin)
  have hint : w0 ∈ interior (DS.projFirst m N '' κ1) := by
    rw [hopenproj.interior_eq]; exact hw0proj
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  refine ⟨κ1, w0, y0, Work.WilG1.Cell.isCell_of_mem_cylDecomp hCyl hκ1C, hκ1sub,
    hw0ballW.2, hy0U, hκ1mem, ε, hε, ?_⟩
  intro w hw
  have hwS : w ∈ DS.projFirst m N '' κ1 := hεsub (Metric.mem_ball.mpr hw)
  rwa [DS.mem_projFirst_image] at hwS

/-- **Definable selection over a fat parameter set.**  If an `Ω`-definable set `Z ⊆ ℝ^{m+N}`
has fibres meeting the open set `U` over a fat set of parameters inside the open set `W`, then
there is a continuous section of `Z` over a nonempty open set `O ⊆ W` with values in `U`:
`O ∋ w ↦ γ w` with `(w, γ w) ∈ Z`.  (Proof route: sharp cylindrical decomposition of `Z`,
the projection of each cell is a cell of the induced decomposition of `ℝ^m`; a fat union of
finitely many of them contains a cell with nonempty interior; a continuous section of a cell
is built by recursion on the cell tower; the restriction to `U` is handled by observing that
the sets of parameters over which the fibres meet `U` are open and finite in number.) -/
theorem DefinableSection (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 : ℕ) :
    ∀ (D : ℕ) (Z : Set (Fin (m + N) → ℝ)), Z ∈ S.Ω F0 D (m + N) →
    ∀ (W : Set (Fin m → ℝ)) (_ : IsOpen W) (U : Set (Fin N → ℝ)) (_ : IsOpen U),
      (∃ w : Fin m → ℝ, w ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ w' : Fin m → ℝ, w' ∈ W →
          dist w' w < r → ∃ y : Fin N → ℝ, y ∈ U ∧ Fin.append w' y ∈ Z) →
      ∃ (O : Set (Fin m → ℝ)) (γ : (Fin m → ℝ) → (Fin N → ℝ)),
        IsOpen O ∧ O.Nonempty ∧ O ⊆ W ∧ ContinuousOn γ O ∧ (∀ w ∈ O, γ w ∈ U) ∧
          ∀ w ∈ O, Fin.append w (γ w) ∈ Z := by
  intro D Z hZ W hW U hU hfat
  obtain ⟨κ, w0, y0, hcell, hsub, hw0W, hy0U, hmem, hε⟩ :=
    cellSelection S hcd m N F0 D Z hZ W hW U hU hfat
  obtain ⟨O, γ, hOopen, hw0O, hanchor, hcont, hsec⟩ :=
    CellLocalSection N m κ hcell w0 y0 U hU hmem hy0U hε
  refine ⟨O ∩ W, γ, hOopen.inter hW, ⟨w0, hw0O, hw0W⟩, Set.inter_subset_right,
    hcont.mono Set.inter_subset_left, ?_, ?_⟩
  · intro w hw
    exact (hsec w hw.1).1
  · intro w hw
    exact hsub (hsec w hw.1).2

end Work.WilG4c
