import Mathlib
import Submission.Work.Drive.exists_lift_degree
import Submission.Work.Measurable

/-!
# The degree (winding number) of a continuous map of the circle

`Work.Drive.exists_lift_degree` supplies, for a continuous `f : ℝ/ℤ → ℝ/ℤ`, a continuous lift
`F : ℝ → ℝ` whose monodromy `F (t+1) - F t` is a constant integer.  This file packages that integer
as the **degree** `degree f hf` and proves the first structural facts:

* `liftOf_lifts`, `liftOf_add_one`: the defining properties of the chosen lift;
* `degree_eq_of_lift`: the degree is *intrinsic* — any continuous lift of `f` with constant
  monodromy has that monodromy equal to `degree f hf`;
* `degree_const`, `degree_id`: the degree of a constant map is `0` and the degree of the identity
  is `1`.

This is the beginning of the winding-number API that the capping step of Hugelmeyer's order theory
needs (the `arg γ` coordinate of `∂M` is a degree) and that classical treatments of the
inscribed-square input use.  The natural continuations — homotopy invariance of the degree, and
`degree f ≠ 0 → Surjective f` — are stated in the accompanying documentation.
-/

namespace Work.Drive

open scoped Topology

/-- A chosen lift of a continuous circle map to `ℝ`. -/
noncomputable def liftOf (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) : ℝ → ℝ :=
  (exists_lift_degree f hf).choose

lemma liftOf_continuous (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) :
    Continuous (liftOf f hf) :=
  (exists_lift_degree f hf).choose_spec.1

lemma liftOf_lifts (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (t : ℝ) :
    (liftOf f hf t : UnitAddCircle) = f (t : UnitAddCircle) :=
  (exists_lift_degree f hf).choose_spec.2.1 t

/-- **The degree (winding number) of a continuous circle map**: the monodromy of a lift. -/
noncomputable def degree (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) : ℤ :=
  (exists_lift_degree f hf).choose_spec.2.2.choose

/-- The defining property of the degree: the chosen lift shifts by `degree f hf` over a period. -/
lemma liftOf_add_one (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (t : ℝ) :
    liftOf f hf (t + 1) = liftOf f hf t + (degree f hf : ℝ) :=
  (exists_lift_degree f hf).choose_spec.2.2.choose_spec t

/-- **The degree is intrinsic.**  Any continuous lift `G` of `f` whose monodromy is the constant
integer `n` has `n = degree f hf`. -/
theorem degree_eq_of_lift {f : UnitAddCircle → UnitAddCircle} (hf : Continuous f)
    {G : ℝ → ℝ} (hG : Continuous G)
    (hlift : ∀ t : ℝ, (G t : UnitAddCircle) = f (t : UnitAddCircle))
    {n : ℤ} (hmono : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ)) : n = degree f hf := by
  set H : ℝ → ℝ := fun t => liftOf f hf t - G t with hH
  have hHcont : Continuous H := (liftOf_continuous f hf).sub hG
  have hHz : ∀ t : ℝ, ∃ k : ℤ, H t = (k : ℝ) := by
    intro t
    have h1 : ((H t : ℝ) : UnitAddCircle) = 0 := by
      simp only [hH, AddCircle.coe_sub, liftOf_lifts f hf t, hlift t, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    exact ⟨k, by simpa [zsmul_eq_mul] using hk.symm⟩
  -- `H` is locally constant: nearby values are integers within `1/2` of each other
  have hloc : ∀ t : ℝ, ∃ U ∈ 𝓝 t, ∀ s ∈ U, H s = H t := by
    intro t
    obtain ⟨k, hk⟩ := hHz t
    obtain ⟨ε, hε, hεU⟩ :=
      Metric.continuousAt_iff.mp hHcont.continuousAt (1 / 2) (by norm_num)
    refine ⟨Metric.ball t ε, Metric.ball_mem_nhds t hε, fun s hs => ?_⟩
    have h1 : dist (H s) (H t) < 1 / 2 := hεU hs
    obtain ⟨l, hl⟩ := hHz s
    have h2 : H s - H t = ((l - k : ℤ) : ℝ) := by
      rw [hl, hk]; push_cast; ring
    have h3 : |((l - k : ℤ) : ℝ)| < 1 / 2 := by
      rw [← h2, ← Real.dist_eq]
      exact h1
    have h4 : l - k = 0 := by
      have h5 := abs_lt.mp h3
      have h6 : (-1 : ℤ) < l - k := by
        have : ((-1 : ℤ) : ℝ) < ((l - k : ℤ) : ℝ) := by push_cast; linarith [h5.1]
        exact_mod_cast this
      have h7 : l - k < (1 : ℤ) := by
        have : ((l - k : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith [h5.2]
        exact_mod_cast this
      omega
    have hlk : l = k := by omega
    rw [hl, hk]
    exact_mod_cast hlk
  -- hence `H` is constant
  have hconst : ∀ s t : ℝ, H s = H t := by
    have hopen : IsOpen {s : ℝ | H s = H 0} := by
      rw [isOpen_iff_mem_nhds]
      intro s hs
      obtain ⟨U, hU, hUc⟩ := hloc s
      exact Filter.mem_of_superset hU fun x hx => by
        show H x = H 0
        rw [hUc x hx]
        exact hs
    have hclosed : IsClosed {s : ℝ | H s = H 0} := isClosed_eq hHcont continuous_const
    have huniv : {s : ℝ | H s = H 0} = Set.univ :=
      IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, rfl⟩
    have hmem : ∀ x : ℝ, H x = H 0 := by
      intro x
      have : x ∈ {t : ℝ | H t = H 0} := by rw [huniv]; trivial
      exact this
    intro s t
    rw [hmem s, hmem t]
  have hkey : ∀ t : ℝ, H (t + 1) = H t + ((degree f hf : ℤ) - n : ℝ) := by
    intro t
    have h1 := liftOf_add_one f hf t
    have h2 := hmono t
    rw [hH]
    show liftOf f hf (t + 1) - G (t + 1) = liftOf f hf t - G t + ((degree f hf : ℤ) - n : ℝ)
    rw [h1, h2]
    push_cast
    ring
  have h0 : H (0 + 1) = H 0 + ((degree f hf : ℤ) - n : ℝ) := hkey 0
  rw [hconst (0 + 1) 0] at h0
  have h1 : ((degree f hf : ℤ) - n : ℝ) = 0 := by linarith
  have h2 : (degree f hf : ℤ) - n = 0 := by exact_mod_cast h1
  omega

/-- The degree of a constant map is `0`. -/
theorem degree_const (c : UnitAddCircle) :
    degree (fun _ : UnitAddCircle => c) continuous_const = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (a : UnitAddCircle) = c := by
    refine ⟨(AddCircle.equivIco (1 : ℝ) 0 c : ℝ), ?_⟩
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := c)
  refine (degree_eq_of_lift continuous_const continuous_const
    (G := fun _ : ℝ => a) (fun t => ha) (n := 0) (fun t => by simp)).symm

/-- The degree of the identity is `1`. -/
theorem degree_id : degree (id : UnitAddCircle → UnitAddCircle) continuous_id = 1 := by
  refine (degree_eq_of_lift continuous_id continuous_id (G := id) (fun t => rfl)
    (n := 1) (fun t => ?_)).symm
  push_cast
  simp only [id_eq]

/-! ## The winding number of a closed plane curve -/

/-- The direction map `ℝ² ∖ {0} → ℝ/ℤ` (the doubled argument of a non-zero vector).  `dirC` itself is
discontinuous at `0` (its value there is `0`), so the honest object is this map on the punctured
plane. -/
noncomputable def dirP (q : {q : ℝ × ℝ // q ≠ 0}) : UnitAddCircle := Submission.Collision.dirC q.1

lemma continuous_dirP : Continuous dirP :=
  Submission.Configuration.continuousOn_dirC.domRestrict

/-- The direction of the vector from `p` to `γ t`, as a map on the circle. -/
noncomputable def dirCurve (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) (p : ℝ × ℝ)
    (hp : p ∉ Set.range γ) : UnitAddCircle → UnitAddCircle :=
  fun t => dirP ⟨γ t - p, by
    intro h
    exact hp ⟨t, sub_eq_zero.mp h⟩⟩

lemma continuous_dirCurve (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) (p : ℝ × ℝ)
    (hp : p ∉ Set.range γ) : Continuous (dirCurve γ hγ p hp) :=
  continuous_dirP.comp ((hγ.sub continuous_const).subtype_mk _)

/-- **The winding number of a closed plane curve `γ` about a point `p` off it**: the degree of the
direction of `γ - p`.  The classical facts about it (invariance under homotopies of `γ` avoiding
`p`; local constancy in `p`; the values `0` and `±1` for a *simple* closed curve) are the
continuations of this chapter; the last one is the Jordan-curve-theorem input that the capping step
of the order theory needs. -/
noncomputable def winding (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) : ℤ :=
  degree (dirCurve γ hγ p hp) (continuous_dirCurve γ hγ p hp)

/-! ## Two computations of the degree -/

/-- **The degree is additive in the circle group**: `deg (f + g) = deg f + deg g` (pointwise sum). -/
theorem degree_add (f g : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (hg : Continuous g) :
    degree (f + g) (hf.add hg) = degree f hf + degree g hg := by
  refine (degree_eq_of_lift (hf.add hg)
    ((liftOf_continuous f hf).add (liftOf_continuous g hg)) ?_
    (n := degree f hf + degree g hg) ?_).symm
  · intro t
    show ((liftOf f hf t + liftOf g hg t : ℝ) : UnitAddCircle) = (f + g) t
    rw [AddCircle.coe_add, Pi.add_apply, liftOf_lifts, liftOf_lifts]
  · intro t
    simp only [Pi.add_apply]
    rw [liftOf_add_one, liftOf_add_one]
    push_cast
    ring

/-- **The degree of multiplication by `n` on the circle is `n`.** -/
theorem degree_nsmul (n : ℕ) :
    degree (fun u : UnitAddCircle => n • u) (continuous_nsmul n) = n := by
  have hcont : Continuous (fun t : ℝ => (n : ℝ) * t) := continuous_const.mul continuous_id
  refine (degree_eq_of_lift (continuous_nsmul n) hcont ?_ (n := (n : ℤ)) ?_).symm
  · intro t
    show (((n : ℝ) * t : ℝ) : UnitAddCircle) = n • (t : UnitAddCircle)
    rw [← AddCircle.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  · intro t
    show (n : ℝ) * (t + 1) = (n : ℝ) * t + ((n : ℤ) : ℝ)
    push_cast
    ring

end Work.Drive
