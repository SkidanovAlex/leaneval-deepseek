import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Embedding.finite_double_points_of_transverse

/-!
# Existence of a "clean" point with a centred chart

Given a map `f : M → ℝ^{2n}` on a smooth `n`-manifold (`n ≥ 1`) whose **set of ordered double
points** `Work.Whitney.doubleSet f = {(y, w) | y ≠ w, f y = f w}` is *finite*, every neighbourhood
`V` of a point `p` contains a point `z` at which `f` is *clean*, i.e. `f z` has no other preimage
(`f y = f w` with `y ≠ w` forces `f z ≠ f y`), together with a chart-like open partial
homeomorphism `c` centred at `z` (a translate of `chartAt z`), whose smoothness and inverse
smoothness are recorded pointwise.

This is the standing hypothesis under which Whitney's cancellation move is performed: the "bad"
points (those whose value is attained twice) form a *finite* set, so they cannot fill up the open
neighbourhood `V` of `p` (a nonempty open subset of a positive-dimensional manifold is infinite).

The proof has two ingredients.

* `finite_fiber_of_finite_doubleSet` — if the double point set of `f` is finite, then every fibre of
  `f` is finite: an infinite fibre would contain infinitely many ordered pairs of distinct points,
  all of them double points (contradiction with `Set.infinite_of_injOn_mapsTo`, transporting the
  injection `x ↦ (x, x₀)` of the fibre minus one point into the double point set).
  Consequently the preimage of a finite set is finite (`finite_preimage_image_of_finite_doubleSet`).
* `infinite_of_mem_nhds` — a neighbourhood of a point of a manifold modelled on `ℝⁿ`, `n ≥ 1`, is
  infinite: a chart turns it into a nonempty open subset of `ℝⁿ`, which contains a ball, and a ball
  is infinite because it contains a segment.

The chart `c` is the translate `y ↦ (chartAt z) y - (chartAt z) z` of the chart at `z`; it is
`c = (chartAt z).trans (Homeomorph.subRight ((chartAt z) z)).toOpenPartialHomeomorph`, so that both
`c` and `c.symm` are compositions of a chart (or its inverse) with a translation, hence smooth
(`contMDiffOn_chart`, `contMDiffOn_chart_symm` and the smoothness of translations on `ℝⁿ`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-! ### Two general facts about (in)finite sets -/

/-- If the double point set of `f` is finite, then every fibre of `f` is finite.  Indeed, an
infinite fibre `f ⁻¹' {s}` would contain an infinite subset (itself minus one point) mapping
injectively into the double point set of `f` via `x ↦ (x, x₀)`. -/
lemma finite_fiber_of_finite_doubleSet {M Y : Type*} (f : M → Y)
    (hfin : (doubleSet f).Finite) (s : Y) : (f ⁻¹' {s}).Finite := by
  by_contra h
  have hinf : (f ⁻¹' {s}).Infinite := h
  obtain ⟨x₀, hx₀⟩ := hinf.nonempty
  have hmem : f x₀ = s := by simpa using hx₀
  have hInf : (f ⁻¹' {s} \ {x₀}).Infinite := hinf.sdiff (Set.finite_singleton x₀)
  have hmaps : Set.MapsTo (fun x => (x, x₀)) (f ⁻¹' {s} \ {x₀}) (doubleSet f) := by
    intro x hx
    obtain ⟨hxf, hxne⟩ := hx
    have h1 : f x = s := by simpa using hxf
    exact ⟨by simpa using hxne, by rw [h1, hmem]⟩
  have hinj : Set.InjOn (fun x => (x, x₀)) (f ⁻¹' {s} \ {x₀}) := by
    intro a _ b _ hab
    simpa using hab
  exact (Set.infinite_of_injOn_mapsTo hinj hmaps hInf) hfin

/-- The preimage of the image of a finite set under `f` is finite, provided the double point set of
`f` is finite: it is the finite union over `t ∈ T` of the fibres `f ⁻¹' {f t}`, each of which is
finite by `finite_fiber_of_finite_doubleSet`. -/
lemma finite_preimage_image_of_finite_doubleSet {M Y : Type*} (f : M → Y)
    (hfin : (doubleSet f).Finite) (T : Set M) (hT : T.Finite) :
    (f ⁻¹' (f '' T)).Finite := by
  have h : f ⁻¹' (f '' T) = ⋃ t ∈ T, f ⁻¹' ({f t} : Set Y) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, hft⟩
      exact ⟨t, ht, hft.symm⟩
    · rintro ⟨t, ht, hft⟩
      exact ⟨t, ht, hft.symm⟩
  rw [h]
  exact hT.biUnion fun t _ => finite_fiber_of_finite_doubleSet f hfin (f t)

/-- In `ℝⁿ` with `n ≥ 1`, every ball is infinite: it contains the image of the infinite interval
`Ioo 0 1` under the injective segment `t ↦ x + (t * (r/2)) • v`, where `v` is a unit vector. -/
lemma infinite_ball_of_one_le {n : ℕ} (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) : (Metric.ball x r).Infinite := by
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have hvn : ‖v‖ = 1 := by simp [v]
  have hvne : v ≠ 0 := by rw [← norm_ne_zero_iff, hvn]; norm_num
  have hinj : Set.InjOn (fun t : ℝ => x + (t * (r / 2)) • v) (Set.Ioo (0 : ℝ) 1) := by
    intro a _ b _ hab
    have h1 : (a * (r / 2)) • v = (b * (r / 2)) • v := add_left_cancel hab
    have h2 : a * (r / 2) = b * (r / 2) := smul_left_injective ℝ hvne h1
    exact mul_right_cancel₀ (by linarith) h2
  have hsub : (fun t : ℝ => x + (t * (r / 2)) • v) '' Set.Ioo (0 : ℝ) 1 ⊆ Metric.ball x r := by
    rintro y ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hvn, mul_one]
    have ht1 : t < 1 := ht.2
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  exact (Set.Ioo_infinite (by norm_num)).image hinj |>.mono hsub

/-- A nonempty open subset of `ℝⁿ` (`n ≥ 1`) is infinite. -/
lemma infinite_of_isOpen_nonempty {n : ℕ} (hn : 1 ≤ n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsOpen U) (hne : U.Nonempty) : U.Infinite := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hs x hx
  exact (infinite_ball_of_one_le hn x hr).mono hrsub

/-- A neighbourhood of a point of a manifold modelled on `ℝⁿ` (`n ≥ 1`) is infinite: the chart at
`p` carries it to a nonempty open subset of `ℝⁿ`. -/
lemma infinite_of_mem_nhds {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {p : M} {V : Set M} (hV : V ∈ nhds p) :
    V.Infinite := by
  obtain ⟨U, hUV, hUo, hpU⟩ := mem_nhds_iff.mp hV
  set e := chartAt (EuclideanSpace ℝ (Fin n)) p with he
  have hWo : IsOpen (U ∩ e.source) := hUo.inter e.open_source
  have hpW : p ∈ U ∩ e.source := ⟨hpU, mem_chart_source _ _⟩
  have hWsub : U ∩ e.source ⊆ e.source := Set.inter_subset_right
  have himg : IsOpen (e '' (U ∩ e.source)) := (e.isOpen_image_iff_of_subset_source hWsub).mpr hWo
  have hne : (e '' (U ∩ e.source)).Nonempty := ⟨e p, p, hpW, rfl⟩
  have hinfimg : (e '' (U ∩ e.source)).Infinite := infinite_of_isOpen_nonempty hn himg hne
  have hinj : Set.InjOn e (U ∩ e.source) := e.injOn.mono hWsub
  have hinfW : (U ∩ e.source).Infinite := (Set.infinite_image_iff hinj).mp hinfimg
  exact hinfW.mono (fun x hx => hUV (Set.inter_subset_left hx))

/-! ### The main statement -/

theorem exists_clean_point_and_chart {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (p : M) (V : Set M) (hV : V ∈ nhds p) :
    ∃ (z : M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      z ∈ V ∧
      c.source = (chartAt (EuclideanSpace ℝ (Fin n)) z).source ∧
      (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target ∧
      c z = 0 ∧
      (∀ y : M, y ∈ c.source → c y =
        (chartAt (EuclideanSpace ℝ (Fin n)) z) y - (chartAt (EuclideanSpace ℝ (Fin n)) z) z) ∧
      (∀ y : M, y ∈ c.source →
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u) ∧
      (∀ y w : M, y ≠ w → f y = f w → f z ≠ f y) := by
  -- The finite set of points of `M` that occur in a double point of `f`.
  let D : Set (M × M) := doubleSet f
  let T : Set M := Prod.fst '' D ∪ Prod.snd '' D
  have hT : T.Finite := (hfin.image Prod.fst).union (hfin.image Prod.snd)
  have hBad : (f ⁻¹' (f '' T)).Finite := finite_preimage_image_of_finite_doubleSet f hfin T hT
  -- A neighbourhood of `p` is infinite, so it meets the complement of the finite bad set.
  have hVinf : V.Infinite := infinite_of_mem_nhds hn hV
  obtain ⟨z, hzV, hzBad⟩ := hVinf.exists_notMem_finite hBad
  -- `z` is clean: its value is attained only at `z`.
  have hclean : ∀ y w : M, y ≠ w → f y = f w → f z ≠ f y := by
    intro y w hyw hfyw hfzy
    have hpair : (y, w) ∈ D := ⟨hyw, hfyw⟩
    have hyT : y ∈ T := Or.inl ⟨(y, w), hpair, rfl⟩
    exact hzBad ⟨y, hyT, hfzy.symm⟩
  -- The chart at `z`, translated to be centred at `z`.
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) z).trans
      ((Homeomorph.subRight ((chartAt (EuclideanSpace ℝ (Fin n)) z) z)).toOpenPartialHomeomorph)
  have hsrc : c.source = (chartAt (EuclideanSpace ℝ (Fin n)) z).source := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp
  have hzsrc : z ∈ c.source := by rw [hsrc]; exact mem_chart_source _ _
  have hz0 : c z = 0 := by
    rw [OpenPartialHomeomorph.trans_apply]
    simp [Homeomorph.subRight_apply]
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := by
    rw [← hz0]; exact c.map_source hzsrc
  have hval : ∀ y : M, y ∈ c.source →
      c y = (chartAt (EuclideanSpace ℝ (Fin n)) z) y - (chartAt (EuclideanSpace ℝ (Fin n)) z) z := by
    intro y _
    rw [OpenPartialHomeomorph.trans_apply]
    simp [Homeomorph.subRight_apply]
  -- Smoothness of `c`: a chart followed by a translation.
  have hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y := by
    intro y hy
    have hsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin n) => w - (chartAt (EuclideanSpace ℝ (Fin n)) z) z) := by
      rw [contMDiff_iff_contDiff]; fun_prop
    have hcont : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) z) y - (chartAt (EuclideanSpace ℝ (Fin n)) z) z)
        (chartAt (EuclideanSpace ℝ (Fin n)) z).source :=
      hsm.comp_contMDiffOn
        (contMDiffOn_chart (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (x := z))
    have hy' : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) z).source := by rw [← hsrc]; exact hy
    have hAt : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) z) y - (chartAt (EuclideanSpace ℝ (Fin n)) z) z)
        y :=
      hcont.contMDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) z).open_source.mem_nhds hy')
    exact hAt.congr_of_eventuallyEq (Filter.eventually_of_mem (c.open_source.mem_nhds hy)
      (fun x hx => (hval x hx).symm))
  -- Smoothness of `c.symm`: a translation followed by the inverse chart.
  have hcsm' : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u := by
    intro u hu
    have hsymm : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
        c.symm u =
          (chartAt (EuclideanSpace ℝ (Fin n)) z).symm (u + (chartAt (EuclideanSpace ℝ (Fin n)) z) z) := by
      intro u _
      rw [OpenPartialHomeomorph.coe_trans_symm]
      simp [Homeomorph.toOpenPartialHomeomorph_symm_apply]
    have hsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin n) => w + (chartAt (EuclideanSpace ℝ (Fin n)) z) z) := by
      rw [contMDiff_iff_contDiff]; fun_prop
    have hcomp : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
          (u + (chartAt (EuclideanSpace ℝ (Fin n)) z) z)) c.target := by
      refine (contMDiffOn_chart_symm (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (x := z)).comp hsm.contMDiffOn ?_
      intro u hu
      rw [OpenPartialHomeomorph.trans_target] at hu
      simpa [Homeomorph.toOpenPartialHomeomorph_symm_apply] using hu.2
    have hAt : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
          (u + (chartAt (EuclideanSpace ℝ (Fin n)) z) z)) u :=
      hcomp.contMDiffAt (c.open_target.mem_nhds hu)
    exact hAt.congr_of_eventuallyEq (Filter.eventually_of_mem (c.open_target.mem_nhds hu)
      (fun x hx => (hsymm x hx).symm))
  exact ⟨z, c, hzV, hsrc, hzero, hz0, hval, hcsm, hcsm', hclean⟩

end Work.Whitney
