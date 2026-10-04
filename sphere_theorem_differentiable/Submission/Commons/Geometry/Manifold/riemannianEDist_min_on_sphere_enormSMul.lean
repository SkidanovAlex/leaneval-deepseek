import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option backward.isDefEq.respectTransparency.types false

/-!
# A minimiser on a Riemannian distance sphere satisfies the triangle equality

Let `(M, g)` be a compact manifold whose tangent spaces carry an extended norm.  Fix two points
`p q : M`, a real radius `r > 0`, and suppose that the `r`-sphere around `p` for the Riemannian
extended distance `d = Manifold.riemannianEDist I` is nonempty, that `z ↦ d p z` and
`z ↦ d z q` are continuous and that `ofReal r < d p q`.  Then among the points `z` with
`d p z = ofReal r` there is one minimising `z ↦ d z q`, and for such a minimiser `y` one has the
triangle equality `d y q + ofReal r = d p q`.

The existence of the minimiser is compactness.  The triangle equality is the interesting part: the
triangle inequality gives `d p q ≤ d y q + ofReal r`, and the reverse inequality is obtained by
pushing a `C¹` path from `p` to `q`, whose length is arbitrarily close to `d p q`, through the
level set `d p z = ofReal r`.  Since the path is continuous and `z ↦ d p z` is continuous, the
intermediate value theorem produces a point `γ t₀` of the path with `d p (γ t₀) = ofReal r`; the
two pieces of the path have lengths `P₀` and `P₁` with `ofReal r ≤ P₀`, `d (γ t₀) q ≤ P₁` and
`P₀ + P₁ < ofReal (d p q) + ε`.  Passing to `ε → 0` gives the reverse inequality.

The main result is `riemannianEDist_min_on_sphere_enormSMul`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology ENNReal
open Set Filter

namespace Commons.Geometry.Manifold

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [(x : M) → ENorm (TangentSpace I x)]
  [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]

/-- **An approximate point on a distance sphere with a controlled distance to `q`.**

Suppose that `d p q = ofReal d` is finite, that `0 < r < d` and that `z ↦ d p z` is continuous.
Then for every `ε > 0` there is a point `z` with `d p z = ofReal r` whose distance to `q` is at
most `d p q + ε - r`, i.e. `d z q + ofReal r ≤ d p q + ofReal ε`.

This is the path-subdivision argument: take a `C¹` path `γ` from `p` to `q` of length
`< ofReal (d + ε)`, cut it at a point of the level set `d p z = ofReal r` (intermediate value
theorem) and add up the two pieces. -/
theorem exists_riemannianEDist_eq_ofReal_and_add_le
    (p q : M) {r d : ℝ} (hr : 0 < r)
    (hcontp : Continuous (fun z : M => Manifold.riemannianEDist I p z))
    (hd : Manifold.riemannianEDist I p q = ENNReal.ofReal d)
    (hrq : ENNReal.ofReal r < Manifold.riemannianEDist I p q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ z : M, Manifold.riemannianEDist I p z = ENNReal.ofReal r ∧
      Manifold.riemannianEDist I z q + ENNReal.ofReal r ≤
        Manifold.riemannianEDist I p q + ENNReal.ofReal ε := by
  have hdpos : 0 < d := by
    have h : (0 : ℝ≥0∞) < ENNReal.ofReal d := by
      rw [← hd]
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hr) hrq.le
    exact ENNReal.ofReal_pos.mp h
  have hrd : r < d := by
    rw [hd] at hrq
    exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mp hrq
  have hDε : Manifold.riemannianEDist I p q < ENNReal.ofReal (d + ε) := by
    rw [hd]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) (x := p) (y := q)
      (r := ENNReal.ofReal (d + ε)) hDε
  -- the distance from `p` along the path stays finite
  have hfin_t : ∀ t ∈ Icc (0 : ℝ) 1, Manifold.riemannianEDist I p (γ t) ≠ ⊤ := by
    intro t ht
    have hle : Manifold.riemannianEDist I p (γ t) ≤ Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength
        (hγC1.mono (Icc_subset_Icc (le_refl 0) ht.2)) hγ0 rfl ht.1
    have hmono : Manifold.pathELength I γ 0 t ≤ Manifold.pathELength I γ 0 1 :=
      Manifold.pathELength_mono (le_refl 0) ht.2
    exact ne_of_lt (lt_of_le_of_lt (hle.trans hmono) (lt_of_lt_of_le hγlen le_top))
  have hgcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p (γ t)).toReal)
      (Icc 0 1) :=
    ENNReal.continuousOn_toReal.comp (hcontp.comp_continuousOn hγC1.continuousOn)
      (fun t ht => hfin_t t ht)
  have hg0 : (Manifold.riemannianEDist I p (γ 0)).toReal = 0 := by
    rw [hγ0, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
  have hg1 : (Manifold.riemannianEDist I p (γ 1)).toReal = d := by
    rw [hγ1, hd, ENNReal.toReal_ofReal hdpos.le]
  have hmem : r ∈ Set.image (fun t : ℝ => (Manifold.riemannianEDist I p (γ t)).toReal)
      (Icc (0 : ℝ) 1) :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hgcont)
      (by rw [hg0, hg1]; exact ⟨hr.le, hrd.le⟩)
  obtain ⟨t0, ht0, ht0eq⟩ := hmem
  have ht0eq' : (Manifold.riemannianEDist I p (γ t0)).toReal = r := ht0eq
  have hz1 : Manifold.riemannianEDist I p (γ t0) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal (hfin_t t0 ht0), ht0eq']
  refine ⟨γ t0, hz1, ?_⟩
  have hP0 : ENNReal.ofReal r ≤ Manifold.pathELength I γ 0 t0 := by
    have h := Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ)
      (hγC1.mono (Icc_subset_Icc (le_refl 0) ht0.2)) hγ0 rfl ht0.1
    rw [← hz1]
    exact h
  have hP1 : Manifold.riemannianEDist I (γ t0) q ≤ Manifold.pathELength I γ t0 1 :=
    Manifold.riemannianEDist_le_pathELength
      (hγC1.mono (Icc_subset_Icc ht0.1 le_rfl)) rfl hγ1 ht0.2
  have hPadd : Manifold.pathELength I γ 0 t0 + Manifold.pathELength I γ t0 1
      = Manifold.pathELength I γ 0 1 := Manifold.pathELength_add ht0.1 ht0.2
  exact le_of_lt (calc Manifold.riemannianEDist I (γ t0) q + ENNReal.ofReal r
      ≤ Manifold.pathELength I γ t0 1 + Manifold.pathELength I γ 0 t0 := add_le_add hP1 hP0
    _ = Manifold.pathELength I γ 0 t0 + Manifold.pathELength I γ t0 1 := add_comm _ _
    _ = Manifold.pathELength I γ 0 1 := hPadd
    _ < ENNReal.ofReal (d + ε) := hγlen
    _ = Manifold.riemannianEDist I p q + ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_add (le_of_lt hdpos) hε.le, ← hd])

/-- **A minimiser on a distance sphere satisfies the triangle equality.**

Suppose `d p q` is finite, `0 < r < d p q`, `z ↦ d p z` is continuous, and `y` is a point of the
sphere `d p y = ofReal r` minimising `z ↦ d z q` over that sphere.  Then
`d y q + ofReal r = d p q`. -/
theorem add_ofReal_le_of_riemannianEDist_min
    (p q : M) {r : ℝ} (hr : 0 < r)
    (hcontp : Continuous (fun z : M => Manifold.riemannianEDist I p z))
    (hfin : Manifold.riemannianEDist I p q ≠ ⊤)
    (hrq : ENNReal.ofReal r < Manifold.riemannianEDist I p q)
    {y : M}
    (hmin : ∀ z : M, Manifold.riemannianEDist I p z = ENNReal.ofReal r →
      Manifold.riemannianEDist I y q ≤ Manifold.riemannianEDist I z q) :
    Manifold.riemannianEDist I y q + ENNReal.ofReal r ≤ Manifold.riemannianEDist I p q := by
  have hd : Manifold.riemannianEDist I p q
      = ENNReal.ofReal (Manifold.riemannianEDist I p q).toReal :=
    (ENNReal.ofReal_toReal hfin).symm
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨z, hz1, hz2⟩ :=
    exists_riemannianEDist_eq_ofReal_and_add_le (I := I) p q hr hcontp hd hrq (ε : ℝ) hε'
  calc Manifold.riemannianEDist I y q + ENNReal.ofReal r
      ≤ Manifold.riemannianEDist I z q + ENNReal.ofReal r := add_le_add (hmin z hz1) le_rfl
    _ ≤ Manifold.riemannianEDist I p q + ENNReal.ofReal (ε : ℝ) := hz2
    _ = Manifold.riemannianEDist I p q + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

end Helpers

theorem riemannianEDist_min_on_sphere_enormSMul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((1 : ENat) : WithTop ENat) M]
    [(x : M) → ENorm (TangentSpace I x)]
    [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]
    [CompactSpace M] (p q : M) {r : ℝ} (hr : 0 < r)
    (hne : ({z : M | Manifold.riemannianEDist I p z = ENNReal.ofReal r} : Set M).Nonempty)
    (hcontp : Continuous (fun z : M => Manifold.riemannianEDist I p z))
    (hcontq : Continuous (fun z : M => Manifold.riemannianEDist I z q))
    (hrq : ENNReal.ofReal r < Manifold.riemannianEDist I p q) :
    ∃ y : M, Manifold.riemannianEDist I p y = ENNReal.ofReal r ∧
      Manifold.riemannianEDist I y q + ENNReal.ofReal r = Manifold.riemannianEDist I p q ∧
      (∀ z : M, Manifold.riemannianEDist I p z = ENNReal.ofReal r →
        Manifold.riemannianEDist I y q ≤ Manifold.riemannianEDist I z q) := by
  obtain ⟨y, hyS, hymin⟩ :=
    (isClosed_eq hcontp continuous_const).isCompact.exists_isMinOn hne hcontq.continuousOn
  refine ⟨y, hyS, le_antisymm ?_ ?_, fun z hz => hymin hz⟩
  · by_cases hfin : Manifold.riemannianEDist I p q = ⊤
    · rw [hfin]; exact le_top
    · exact add_ofReal_le_of_riemannianEDist_min (I := I) (y := y) p q hr hcontp hfin hrq
        (fun z hz => hymin hz)
  · have htri : Manifold.riemannianEDist I p q
        ≤ ENNReal.ofReal r + Manifold.riemannianEDist I y q := by
      have h := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := y) (z := q)
      rwa [hyS] at h
    exact htri.trans_eq (add_comm _ _)

end Commons.Geometry.Manifold