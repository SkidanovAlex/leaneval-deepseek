import Mathlib

/-!
# The collar construction for changing the basepoint of a homotopy group

Given a path `p : Path x y` in a space `X` and a nonempty finite type `M`, we build a continuous
map `Ω^M X x → Ω^M X y` between the based `M`-cubes of `X`, obtained by "filling the collar of
the cube with `p`" and shrinking the interior.  This is the geometric input for the fact that
`πₙ(X,x) ≅ πₙ(X,y)` for `x`, `y` in the same path component.

The construction uses the radial function `delta` measuring the distance of a point of the cube
`M → I` to its boundary, the affine shrinking `scale`, and the coordinatewise `sigma`.
-/

open scoped Topology unitInterval Topology.Homotopy
open Set Function

namespace Work.Stems.Collar

variable {M : Type*} [Fintype M] [Nonempty M]

/-- The radial function: the (attained) minimum over the coordinates of
`min (t j) (1 - t j)`.  It vanishes exactly on the boundary of the cube. -/
noncomputable def delta (t : M → I) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => min ((t j : ℝ)) (1 - (t j : ℝ))

/-- The projection of `ℝ` onto the unit interval. -/
noncomputable def clamp01 (r : ℝ) : I := projIcc 0 1 zero_le_one r

@[simp]
theorem coe_clamp01 (r : ℝ) : ((clamp01 r : I) : ℝ) = max 0 (min 1 r) :=
  coe_projIcc _ _ _ _

@[simp]
theorem clamp01_zero : clamp01 0 = (0 : I) := by
  apply Subtype.ext
  simp [clamp01]

@[simp]
theorem clamp01_one : clamp01 1 = (1 : I) := by
  apply Subtype.ext
  simp [clamp01]

theorem continuous_clamp01 : Continuous clamp01 := continuous_projIcc (h := zero_le_one)

theorem clamp01_of_mem {r : ℝ} (h : r ∈ Icc 0 1) : clamp01 r = ⟨r, h⟩ := projIcc_of_mem zero_le_one h

theorem clamp01_eq_zero_iff {r : ℝ} : clamp01 r = 0 ↔ r ≤ 0 := projIcc_eq_zero

theorem clamp01_eq_one_iff {r : ℝ} : clamp01 r = 1 ↔ 1 ≤ r := projIcc_eq_one

/-- Coordinatewise affine shrinking of the unit interval: the map sending `c` to `0` and
`1 - c` to `1`. -/
noncomputable def scale (c : ℝ) (x : I) : I := clamp01 (((x : ℝ) - c) / (1 - 2 * c))

/-- The shrinking of the cube `I^M` onto its inner subcube `[c,1-c]^M`, written
coordinatewise as `scale c`. -/
noncomputable def sigma (c : ℝ) (t : M → I) : M → I := fun j => scale c (t j)

@[simp]
theorem coe_scale (c : ℝ) (x : I) :
    ((scale c x : I) : ℝ) = max 0 (min 1 (((x : ℝ) - c) / (1 - 2 * c))) :=
  coe_clamp01 _

@[simp]
theorem sigma_apply (c : ℝ) (t : M → I) (j : M) : sigma c t j = scale c (t j) := rfl

omit [Fintype M] [Nonempty M] in
theorem continuous_scale (c : ℝ) : Continuous (scale c) :=
  continuous_clamp01.comp (by fun_prop)

theorem continuous_sigma (c : ℝ) : Continuous (sigma (M := M) c) :=
  continuous_pi fun j => (continuous_scale c).comp (continuous_apply j)

@[simp]
theorem delta_apply (t : M → I) : delta t = Finset.univ.inf' Finset.univ_nonempty
    (fun j => min ((t j : ℝ)) (1 - (t j : ℝ))) := rfl

theorem delta_nonneg (t : M → I) : 0 ≤ delta t := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j => min ((t j : ℝ)) (1 - (t j : ℝ)))
  rw [delta, hj]
  exact le_min (t j).2.1 (by linarith [(t j).2.2])

theorem delta_le_iff {t : M → I} {c : ℝ} :
    delta t ≤ c ↔ ∃ j, (t j : ℝ) ≤ c ∨ 1 - c ≤ (t j : ℝ) := by
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun j => min ((t j : ℝ)) (1 - (t j : ℝ)))
    rw [delta, hj] at h
    rcases le_total ((t j : ℝ)) (1 - (t j : ℝ)) with hle | hle
    · rw [min_eq_left hle] at h
      exact ⟨j, Or.inl h⟩
    · rw [min_eq_right hle] at h
      exact ⟨j, Or.inr (by linarith)⟩
  · rintro ⟨j, hj⟩
    have h1 : min ((t j : ℝ)) (1 - (t j : ℝ)) ≤ c := by
      rcases hj with h | h
      · exact le_trans (min_le_left _ _) h
      · exact le_trans (min_le_right _ _) (by linarith)
    exact le_trans (Finset.inf'_le _ (Finset.mem_univ j)) h1

theorem delta_le_half (t : M → I) : delta t ≤ 1 / 2 := by
  rw [delta_le_iff]
  refine ⟨Classical.arbitrary M, ?_⟩
  rcases le_total ((t (Classical.arbitrary M) : I) : ℝ) (1 / 2) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem delta_eq_zero_iff {t : M → I} : delta t = 0 ↔ t ∈ Cube.boundary M := by
  constructor
  · intro h
    obtain ⟨j, hj | hj⟩ := (delta_le_iff (t := t) (c := 0)).mp (le_of_eq h)
    · exact ⟨j, Or.inl (Subtype.ext (le_antisymm hj (t j).2.1))⟩
    · refine ⟨j, Or.inr (Subtype.ext (le_antisymm (t j).2.2 ?_))⟩
      simpa using hj
  · rintro ⟨j, hj⟩
    have h2 : delta t ≤ 0 := by
      rw [delta_le_iff]
      refine ⟨j, ?_⟩
      rcases hj with h | h
      · exact Or.inl (le_of_eq (congrArg Subtype.val h))
      · refine Or.inr ?_
        have : ((t j : I) : ℝ) = 1 := congrArg Subtype.val h
        linarith
    exact le_antisymm h2 (delta_nonneg t)

theorem continuous_delta : Continuous (delta (M := M)) := by
  show Continuous fun t : M → I => Finset.univ.inf' Finset.univ_nonempty
    (fun j => min ((t j : ℝ)) (1 - (t j : ℝ)))
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun j _ =>
    ((continuous_subtype_val.comp (continuous_apply j))).min
      (continuous_const.sub (continuous_subtype_val.comp (continuous_apply j))))

theorem scale_eq_zero_iff {c : ℝ} (hc : c < 1 / 2) (u : I) :
    scale c u = 0 ↔ (u : ℝ) ≤ c := by
  have hpos : (0 : ℝ) < 1 - 2 * c := by linarith
  rw [scale, clamp01_eq_zero_iff]
  constructor
  · intro h
    by_contra hc'
    exact absurd h (not_le.2 (div_pos (by linarith) hpos))
  · intro h
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le

theorem scale_eq_one_iff {c : ℝ} (hc : c < 1 / 2) (u : I) :
    scale c u = 1 ↔ 1 - c ≤ (u : ℝ) := by
  have hpos : (0 : ℝ) < 1 - 2 * c := by linarith
  rw [scale, clamp01_eq_one_iff]
  constructor
  · intro h
    have : 1 * (1 - 2 * c) ≤ (u : ℝ) - c := by
      rw [← le_div_iff₀ hpos]; exact h
    linarith
  · intro h
    rw [le_div_iff₀ hpos]
    linarith

theorem sigma_mem_boundary_of_delta_le {c : ℝ} (hc : c < 1 / 2) {t : M → I}
    (h : delta t ≤ c) : sigma c t ∈ Cube.boundary M := by
  obtain ⟨j, hj | hj⟩ := (delta_le_iff (t := t) (c := c)).mp h
  · exact ⟨j, Or.inl (scale_eq_zero_iff hc (t j) |>.2 hj)⟩
  · exact ⟨j, Or.inr (scale_eq_one_iff hc (t j) |>.2 hj)⟩

section Collar

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- The collar formula: on the collar of the cube (where `delta ≤ 1/4`) walk along `p`, and
on the inner cube apply `f` after the shrinking `sigma 1/4`. -/
noncomputable def collarFun (p : Path x y) (f : Ω^ M X x) (t : M → I) : X :=
  if delta t ≤ 1 / 4 then p (clamp01 (1 - 4 * delta t)) else f (sigma (1 / 4) t)

theorem collarFun_boundary (p : Path x y) (f : Ω^ M X x) {t : M → I}
    (ht : t ∈ Cube.boundary M) : collarFun p f t = y := by
  have h0 : delta t = 0 := (delta_eq_zero_iff (M := M)).2 ht
  rw [collarFun, if_pos (by rw [h0]; norm_num), h0, mul_zero, sub_zero, clamp01_one]
  exact p.target

theorem continuous_collarFun (p : Path x y) :
    Continuous fun q : Ω^ M X x × (M → I) => collarFun p q.1 q.2 := by
  have hδ : Continuous fun q : Ω^ M X x × (M → I) => delta q.2 :=
    continuous_delta.comp continuous_snd
  have hA : Continuous fun q : Ω^ M X x × (M → I) =>
      p (clamp01 (1 - 4 * delta q.2)) :=
    p.continuous.comp (continuous_clamp01.comp
      (continuous_const.sub (continuous_const.mul hδ)))
  have hB : Continuous fun q : Ω^ M X x × (M → I) => q.1 (sigma (1 / 4) q.2) :=
    continuous_fst.eval ((continuous_sigma (1 / 4)).comp continuous_snd)
  rw [show (fun q : Ω^ M X x × (M → I) => collarFun p q.1 q.2) = fun q =>
      if delta q.2 ≤ 1 / 4 then p (clamp01 (1 - 4 * delta q.2))
      else q.1 (sigma (1 / 4) q.2) from rfl]
  refine Continuous.if_le hA hB hδ continuous_const ?_
  intro q hq
  have hb : sigma (1 / 4) q.2 ∈ Cube.boundary M :=
    sigma_mem_boundary_of_delta_le (by norm_num) (le_of_eq hq)
  rw [show (1 : ℝ) - 4 * delta q.2 = 0 by rw [hq]; norm_num, clamp01_zero, p.source]
  exact (GenLoop.boundary q.1 _ hb).symm

/-- The collar map `Ω^M X x → Ω^M X y`. -/
noncomputable def collar (p : Path x y) : C(Ω^ M X x, Ω^ M X y) where
  toFun f := ⟨⟨fun t => collarFun p f t,
    (continuous_collarFun p).comp (continuous_const.prodMk continuous_id)⟩,
    fun t ht => collarFun_boundary p f ht⟩
  continuous_toFun := Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_collarFun p)) _

@[simp]
theorem collar_apply (p : Path x y) (f : Ω^ M X x) (t : M → I) :
    collar p f t = collarFun p f t := rfl

end Collar

end Work.Stems.Collar
