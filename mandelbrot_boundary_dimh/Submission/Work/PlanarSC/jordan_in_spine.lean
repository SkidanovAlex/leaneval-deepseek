import Mathlib
import Submission.Work.PlanarSC.SpineDefs

/-!
# A Jordan curve inside the spine of a polyomino forces a hole

`Commons.Topology.Plane.polyK S = ⋃ p ∈ S, unitSqAt p` is the finite union of the closed unit
lattice squares indexed by `S : Finset (ℤ × ℤ)`, and `Work.PlanarSC.spine S` is the union of the
lattice edges of `polyK S`; equivalently (`Work.PlanarSC.spine_eq_spineSet`)
`spine S = (⋃ p ∈ S, unitSqAt p) \ (⋃ p ∈ S, badSet p)`, the union of the closed cells with the
*open interior* and the *open top edge* of every cell removed.

The lemma proved here is the geometric core of "a connected hole-free polyomino is simply
connected": **if the spine contains a Jordan curve then `(polyK S)ᶜ` is disconnected.**

Proof.  Suppose `(polyK S)ᶜ` were preconnected.  Since `spine S ⊆ polyK S`, the range of `γ` lies
in `polyK S`, so `(polyK S)ᶜ` is a preconnected subset of `(range γ)ᶜ = U ∪ V` (the two
complementary domains of the Jordan curve, `U` bounded and `V` unbounded); as it is unbounded it
cannot lie in `U`, hence it lies in `V` and `U ⊆ polyK S`.  Being a nonempty open subset of the
finite union of the closed unit squares, `U` meets the *open* square `openSqAt c` of at least one
cell `c ∈ S`; choose such a `c` of maximal `im`.  Then `openSqAt c ⊆ U` (it is preconnected, meets
`U`, avoids `range γ ⊆ spine S` — which removes `openSqAt c` — and avoids `(polyK S)ᶜ`).

Let `w` be the midpoint of the (open) top edge of `c`.  Then `w ∈ closure (openSqAt c) ⊆ closure U`.
If `w ∈ U`, then a whole ball around `w` lies in `U`, in particular the point just above `w`; that
point lies in `polyK S`, hence in `unitSqAt q` for some `q ∈ S`, and it also lies in the open square
of the cell `(c.1, c.2 + 1)`, which forces `q = (c.1, c.2 + 1)`: a cell of `S` with strictly larger
`im` meeting `U` in its interior, contradicting the maximality of `c`.  If `w ∉ U`, then
`w ∈ closure U \ U ⊆ range γ ⊆ spine S`; but `w` also lies in `unitSqAt c` with `c ∈ S` and on the
*open* top edge of `c`, i.e. in `badSet c`, so it cannot lie in the spine — a contradiction.
-/

namespace Work.PlanarSC

open Set
open scoped Topology

noncomputable section

/-! ## Elementary facts about the unit lattice -/

/-- The closed unit lattice square at `p` is bounded. -/
theorem unitSqAt_isBounded (p : ℤ × ℤ) :
    Bornology.IsBounded (Commons.Topology.Plane.unitSqAt p) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨|((p.1 : ℤ) : ℝ)| + 1 + (|((p.2 : ℤ) : ℝ)| + 1), fun z hz => ?_⟩
  rw [Commons.Topology.Plane.mem_unitSqAt] at hz
  have h1 : |z.re| ≤ |((p.1 : ℤ) : ℝ)| + 1 := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le ((p.1 : ℤ) : ℝ), hz.1],
      by linarith [le_abs_self ((p.1 : ℤ) : ℝ), hz.2.1]⟩
  have h2 : |z.im| ≤ |((p.2 : ℤ) : ℝ)| + 1 := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le ((p.2 : ℤ) : ℝ), hz.2.2.1],
      by linarith [le_abs_self ((p.2 : ℤ) : ℝ), hz.2.2.2]⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |((p.1 : ℤ) : ℝ)| + 1 + (|((p.2 : ℤ) : ℝ)| + 1) := by linarith

/-- `polyK S`, a finite union of closed unit squares, is compact. -/
theorem isCompact_polyK (S : Finset (ℤ × ℤ)) : IsCompact (Commons.Topology.Plane.polyK S) := by
  change IsCompact (⋃ p ∈ S, Commons.Topology.Plane.unitSqAt p)
  exact S.finite_toSet.isCompact_biUnion fun p _ =>
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Commons.Topology.Plane.isClosed_unitSqAt p, unitSqAt_isBounded p⟩

/-- `polyK S` is bounded. -/
theorem polyK_isBounded (S : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (Commons.Topology.Plane.polyK S) := (isCompact_polyK S).isBounded

/-- The complement of a bounded subset of `ℂ` is not bounded. -/
private theorem not_isBounded_compl {X : Set ℂ} (hX : Bornology.IsBounded X) :
    ¬ Bornology.IsBounded Xᶜ := by
  intro hc
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hX
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp hc
  set R : ℝ := |max C D| + 2 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hznorm : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
  have hnotmem : (R : ℂ) ∉ X := by
    intro hmem
    have h := hC _ hmem
    rw [hznorm] at h
    have h1 : C ≤ max C D := le_max_left C D
    have h2 : max C D ≤ |max C D| := le_abs_self _
    rw [hR] at h
    linarith
  have h2 := hD _ (Set.mem_compl hnotmem)
  rw [hznorm] at h2
  have h1 : D ≤ max C D := le_max_right C D
  have h3 : max C D ≤ |max C D| := le_abs_self _
  rw [hR] at h2
  linarith

/-- The spine is contained in `polyK S`. -/
theorem spine_subset_polyK (S : Finset (ℤ × ℤ)) : spine S ⊆ Commons.Topology.Plane.polyK S := by
  rw [spine_eq_spineSet]
  exact Commons.Topology.Plane.spineSet_subset_union S S

/-- The open unit square at `p` is convex. -/
private theorem convex_openSqAt (p : ℤ × ℤ) : Convex ℝ (Commons.Topology.Plane.openSqAt p) := by
  rw [convex_iff_forall_pos]
  rintro x hx y hy a b ha hb hab
  rw [Commons.Topology.Plane.mem_openSqAt] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  have key : ∀ u v t : ℝ, t < u → t < v → t < a * u + b * v := by
    intro u v t hu hv
    have h1 : a * t < a * u := mul_lt_mul_of_pos_left hu ha
    have h2 : b * t < b * v := mul_lt_mul_of_pos_left hv hb
    have h3 : a * t + b * t = t := by
      have h4 : (a + b) * t = t := by rw [hab, one_mul]
      linarith [h4]
    linarith [h1, h2, h3]
  have key' : ∀ u v t : ℝ, u < t → v < t → a * u + b * v < t := by
    intro u v t hu hv
    have h1 : a * u < a * t := mul_lt_mul_of_pos_left hu ha
    have h2 : b * v < b * t := mul_lt_mul_of_pos_left hv hb
    have h3 : a * t + b * t = t := by
      have h4 : (a + b) * t = t := by rw [hab, one_mul]
      linarith [h4]
    linarith [h1, h2, h3]
  rw [hre, him]
  exact ⟨key x.re y.re _ hx1 hy1, key' x.re y.re _ hx2 hy2, key x.im y.im _ hx3 hy3,
    key' x.im y.im _ hx4 hy4⟩

/-! ## Counting arguments for points with non-integer coordinates -/

/-- Every interval of positive radius around a real number contains a non-integer. -/
private theorem exists_not_int_mem_Ioo (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ x ∈ Set.Ioo (a - ρ) (a + ρ), ∀ n : ℤ, x ≠ (n : ℝ) := by
  by_cases h : ∃ n : ℤ, a = (n : ℝ)
  · obtain ⟨n, rfl⟩ := h
    refine ⟨(n : ℝ) + min ρ 1 / 2, ⟨?_, ?_⟩, ?_⟩
    · have h1 : 0 < min ρ 1 / 2 := by
        have : 0 < min ρ 1 := lt_min hρ one_pos
        linarith
      linarith
    · have h1 : min ρ 1 ≤ ρ := min_le_left _ _
      have h2 : 0 < min ρ 1 / 2 := by
        have : 0 < min ρ 1 := lt_min hρ one_pos
        linarith
      linarith
    · intro m hm
      have hkey : ((m - n : ℤ) : ℝ) = min ρ 1 / 2 := by
        have hmn : ((m : ℝ) - (n : ℝ)) = min ρ 1 / 2 := by linarith
        simpa using hmn
      have hpos : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
        rw [hkey]
        have : 0 < min ρ 1 := lt_min hρ one_pos
        linarith
      have hlt : ((m - n : ℤ) : ℝ) < 1 := by
        rw [hkey]
        have h1 : min ρ 1 ≤ 1 := min_le_right _ _
        linarith
      have hpos' : (0 : ℤ) < m - n := by exact_mod_cast hpos
      have hlt' : m - n < 1 := by exact_mod_cast hlt
      omega
  · refine ⟨a, ⟨by linarith, by linarith⟩, ?_⟩
    intro n hna
    exact h ⟨n, hna⟩

/-- Every ball in `ℂ` contains a point whose real and imaginary parts are both non-integers. -/
private theorem exists_mem_ball_not_int (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w ∈ Metric.ball z ρ, (∀ n : ℤ, w.re ≠ (n : ℝ)) ∧ (∀ n : ℤ, w.im ≠ (n : ℝ)) := by
  obtain ⟨x, hx, hxni⟩ := exists_not_int_mem_Ioo z.re (by linarith : 0 < ρ / 2)
  obtain ⟨y, hy, hyni⟩ := exists_not_int_mem_Ioo z.im (by linarith : 0 < ρ / 2)
  rw [Set.mem_Ioo] at hx hy
  refine ⟨⟨x, y⟩, ?_, hxni, hyni⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 : ((⟨x, y⟩ : ℂ) - z).re = x - z.re := rfl
  have h2 : ((⟨x, y⟩ : ℂ) - z).im = y - z.im := rfl
  calc ‖(⟨x, y⟩ : ℂ) - z‖ ≤ |((⟨x, y⟩ : ℂ) - z).re| + |((⟨x, y⟩ : ℂ) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |x - z.re| + |y - z.im| := by rw [h1, h2]
    _ < ρ := by
        have hxa : |x - z.re| < ρ / 2 := by
          rw [abs_lt]
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hya : |y - z.im| < ρ / 2 := by
          rw [abs_lt]
          exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
        linarith

/-- A nonempty open subset of `polyK S` meets the *open* square of some cell of `S`. -/
theorem openSqAt_exists_inter {S : Finset (ℤ × ℤ)} {U : Set ℂ} (hUo : IsOpen U) (hne : U.Nonempty)
    (hU : U ⊆ Commons.Topology.Plane.polyK S) :
    ∃ p ∈ S, (Commons.Topology.Plane.openSqAt p ∩ U).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hUo z hz
  obtain ⟨w, hwball, hwre, hwim⟩ := exists_mem_ball_not_int z hρ
  have hwU : w ∈ U := hball hwball
  have hwP : w ∈ Commons.Topology.Plane.polyK S := hU hwU
  rw [Commons.Topology.Plane.polyK] at hwP
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hwP
  refine ⟨p, hp, w, ?_, hwU⟩
  rw [Commons.Topology.Plane.mem_unitSqAt] at hwp
  rw [Commons.Topology.Plane.mem_openSqAt]
  obtain ⟨h1, h2, h3, h4⟩ := hwp
  refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, lt_of_le_of_ne h3 ?_, lt_of_le_of_ne h4 ?_⟩
  · intro hcontra; exact hwre p.1 hcontra.symm
  · intro hcontra; exact hwre (p.1 + 1) (by rw [hcontra]; push_cast; ring)
  · intro hcontra; exact hwim p.2 hcontra.symm
  · intro hcontra; exact hwim (p.2 + 1) (by rw [hcontra]; push_cast; ring)

/-! ## The main theorem -/

theorem jordan_in_spine (S : Finset (ℤ × ℤ)) (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (hrange : Set.range γ ⊆ Work.PlanarSC.spine S) :
    ¬ IsPreconnected (Commons.Topology.Plane.polyK S)ᶜ := by
  classical
  intro hpre
  have hrg : Set.range γ ⊆ Commons.Topology.Plane.polyK S := hrange.trans (spine_subset_polyK S)
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVub, hcover⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγ
  -- the complement of `polyK S` lies in one of the two complementary domains of the curve
  have hsub : (Commons.Topology.Plane.polyK S)ᶜ ⊆ U ∪ V := by
    rw [hcover]
    exact Set.compl_subset_compl.mpr hrg
  rcases IsPreconnected.subset_or_subset hUo hVo hdisj hsub hpre with hPU | hPV
  · -- impossible: `(polyK S)ᶜ` is unbounded while `U` is bounded
    exact not_isBounded_compl (polyK_isBounded S) (hUb.subset hPU)
  · -- hence `U ⊆ polyK S`
    have hUP : U ⊆ Commons.Topology.Plane.polyK S := by
      intro u hu
      by_contra hu'
      exact Set.disjoint_left.mp hdisj hu (hPV hu')
    obtain ⟨u₀, hu₀⟩ := hUc.1
    -- the topmost cell of `S` whose open square meets `U`
    have hne : (S.filter fun p => (Commons.Topology.Plane.openSqAt p ∩ U).Nonempty).Nonempty := by
      obtain ⟨p, hpS, hpne⟩ := openSqAt_exists_inter hUo ⟨u₀, hu₀⟩ hUP
      exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hpne⟩⟩
    obtain ⟨c, hcmem, hcmax⟩ :=
      Finset.exists_max_image _ (fun p : ℤ × ℤ => p.2) hne
    have hcS : c ∈ S := (Finset.mem_filter.mp hcmem).1
    have hcne : (Commons.Topology.Plane.openSqAt c ∩ U).Nonempty :=
      (Finset.mem_filter.mp hcmem).2
    have hcmax' : ∀ p ∈ S, (Commons.Topology.Plane.openSqAt p ∩ U).Nonempty → p.2 ≤ c.2 :=
      fun p hp hpne => hcmax p (Finset.mem_filter.mpr ⟨hp, hpne⟩)
    -- the open square of `c` is contained in `U`
    have hsqU : Commons.Topology.Plane.openSqAt c ⊆ U := by
      have hsub2 : Commons.Topology.Plane.openSqAt c ⊆ U ∪ V := by
        intro z hz
        rw [hcover]
        intro hzr
        have hzs : z ∈ Commons.Topology.Plane.spineSet S S := by
          rw [← spine_eq_spineSet]
          exact hrange hzr
        exact hzs.2 (Set.mem_iUnion₂.mpr ⟨c, hcS, Or.inl hz⟩)
      rcases IsPreconnected.subset_or_subset hUo hVo hdisj hsub2
        (convex_openSqAt c).isPreconnected with h | h
      · exact h
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hcne
        exact Set.disjoint_left.mp hdisj hz2 (h hz1)
    -- the midpoint of the open top edge of `c`
    set w : ℂ := ⟨(c.1 : ℝ) + 1/2, (c.2 : ℝ) + 1⟩ with hwdef
    have hwtop : w ∈ Commons.Topology.Plane.openTopAt c := by
      rw [Commons.Topology.Plane.mem_openTopAt]
      exact ⟨by rw [hwdef]; norm_num, by rw [hwdef]; norm_num, rfl⟩
    have hwcl : w ∈ closure U := by
      refine closure_mono hsqU ?_
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hεpos : 0 < min ε 1 / 2 := by
        have : 0 < min ε 1 := lt_min hε one_pos
        linarith
      have hεlt : min ε 1 / 2 < 1 := by
        have : min ε 1 ≤ 1 := min_le_right _ _
        linarith
      have hερ : min ε 1 / 2 < ε := by
        have : min ε 1 ≤ ε := min_le_left _ _
        linarith
      refine ⟨⟨(c.1 : ℝ) + 1/2, (c.2 : ℝ) + 1 - min ε 1 / 2⟩, ?_, ?_⟩
      · rw [Commons.Topology.Plane.mem_openSqAt]
        exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
      · have hsub : w - (⟨(c.1 : ℝ) + 1/2, (c.2 : ℝ) + 1 - min ε 1 / 2⟩ : ℂ) =
            ((min ε 1 / 2 : ℝ) : ℂ) * Complex.I := by
          rw [hwdef]
          apply Complex.ext <;> simp
        have hle : dist w (⟨(c.1 : ℝ) + 1/2, (c.2 : ℝ) + 1 - min ε 1 / 2⟩ : ℂ)
            ≤ min ε 1 / 2 := by
          rw [dist_eq_norm, hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hεpos]
        linarith
    by_cases hwU : w ∈ U
    · -- a point just above `w` lies in `U`, and this forces a cell above `c` meeting `U`
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hUo w hwU
      have hδpos : 0 < min ρ 1 / 3 := by
        have : 0 < min ρ 1 := lt_min hρ one_pos
        linarith
      have hδ1 : min ρ 1 / 3 < 1 := by
        have : min ρ 1 ≤ 1 := min_le_right _ _
        linarith
      have hδρ : min ρ 1 / 3 < ρ := by
        have : min ρ 1 ≤ ρ := min_le_left _ _
        linarith
      set z : ℂ := ⟨(c.1 : ℝ) + 1/2, (c.2 : ℝ) + 1 + min ρ 1 / 3⟩ with hzdef
      have hzU : z ∈ U := by
        refine hball ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z - w = ((min ρ 1 / 3 : ℝ) : ℂ) * Complex.I := by
          rw [hzdef, hwdef]
          apply Complex.ext <;> simp
        have hle : ‖z - w‖ ≤ min ρ 1 / 3 := by
          rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hδpos]
        linarith
      have hzP : z ∈ ⋃ p ∈ S, Commons.Topology.Plane.unitSqAt p :=
        hUP hzU
      obtain ⟨q, hqS, hzq⟩ := Set.mem_iUnion₂.mp hzP
      have hzopen : z ∈ Commons.Topology.Plane.openSqAt (c.1, c.2 + 1) := by
        rw [Commons.Topology.Plane.mem_openSqAt, hzdef]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
      have hq : q = (c.1, c.2 + 1) :=
        (Commons.Topology.Plane.openSqAt_inter_unitSqAt hzopen hzq).symm
      have hmemS : (c.1, c.2 + 1) ∈ S := hq ▸ hqS
      have hne' : (Commons.Topology.Plane.openSqAt (c.1, c.2 + 1) ∩ U).Nonempty :=
        ⟨z, hzopen, hzU⟩
      have hstep := hcmax' (c.1, c.2 + 1) hmemS hne'
      change c.2 + 1 ≤ c.2 at hstep
      omega
    · -- then `w ∈ closure U \ U` lies on the curve, yet on the open top edge of a cell of `S`
      have hVcl : Disjoint V (closure U) := by
        rw [Set.disjoint_left]
        intro x hxV hxcl
        have hsub' : closure U ⊆ Vᶜ :=
          closure_minimal (fun y hy => Set.disjoint_left.mp hdisj hy) hVo.isClosed_compl
        exact hsub' hxcl hxV
      have hwrg : w ∈ Set.range γ := by
        by_contra hwr
        have hmem : w ∈ U ∪ V := by
          rw [hcover]
          exact hwr
        rcases hmem with h | h
        · exact hwU h
        · exact Set.disjoint_left.mp hVcl h hwcl
      have hwspine : w ∈ spine S := hrange hwrg
      have hwspineSet : w ∈ Commons.Topology.Plane.spineSet S S := by
        rwa [← spine_eq_spineSet]
      exact hwspineSet.2 (Set.mem_iUnion₂.mpr ⟨c, hcS, Or.inr hwtop⟩)

end

end Work.PlanarSC
