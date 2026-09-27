import Mathlib
import Submission.Work.Drive.stripChartExt
import Submission.Work.Drive.exists_contMDiffAt_chordDir_sq
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.cappedPlaneCharts
import Submission.Work.Drive.dense_circleExp_ne
import Submission.Work.Drive.eventually_norm_eq_one_of_contMDiffAt_dense

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Classical
open Submission.Configuration Submission.Geometry Submission.Collision

noncomputable section

/-! ## Elementary properties of the strip chart and of its extension

The proofs below use the following three rewritings of the two charts into classes of
`CappingSpace`, and the consequent invariance of `stripChart` under a change of the parameters
which does not change `Circle.exp` of either of them (this is what lets the diagonal case be
reduced to the lift `p₀ 0 = p₀ 1`). -/

/-- **The rotated strip chart as a class of the configuration piece.**  This is the explicit form of
`Work.Drive.stripChart` in which the rotation `rotConfig v` has been performed on the coordinates. -/
lemma stripChart_eq_mk (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (v : UnitAddCircle)
    (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne v w = Quotient.mk'' (Sum.inl (⟨((stripData γ w).1, (stripData γ w).2.1,
      (stripData γ w).2.2 + v),
      stripData_pos hγne w, confOf_snd_norm_le_one (muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))⟩
        : ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  unfold stripChart confPiece stripData rotConfig
  rfl

/-- **The strip chart with a prescribed unit direction, in explicit coordinates.** -/
lemma stripChartExt_eq_mk (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {W : EuclideanSpace ℝ (Fin 2) → ℂ} (hW : ∀ p, ‖W p‖ = 1) (p : EuclideanSpace ℝ (Fin 2)) :
    stripChartExt γ hγne W hW p = Quotient.mk'' (Sum.inl (⟨(stripR γ p, stripD γ p, circOf (W p) (hW p)),
      stripR_pos hγne p, stripD_le_one γ p⟩ : ConfigPiece) : ConfigPiece ⊕ CapPiece) := rfl

/-- The capping coordinates of the chord only see `γ ∘ Circle.exp`. -/
lemma stripData_congr {γ : Circle → ℝ × ℝ} {p p' : EuclideanSpace ℝ (Fin 2)}
    (h0 : Circle.exp (p 0) = Circle.exp (p' 0)) (h1 : Circle.exp (p 1) = Circle.exp (p' 1)) :
    stripData γ p = stripData γ p' := by
  unfold stripData
  rw [h0, h1]

/-- **The strip chart only depends on `Circle.exp` of the two parameters.** -/
lemma stripChart_congr {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0) (v : UnitAddCircle)
    {p p' : EuclideanSpace ℝ (Fin 2)} (h0 : Circle.exp (p 0) = Circle.exp (p' 0))
    (h1 : Circle.exp (p 1) = Circle.exp (p' 1)) :
    stripChart γ hγne v p = stripChart γ hγne v p' := by
  rw [stripChart_eq_mk, stripChart_eq_mk, mk_inl_inj]
  refine Subtype.ext ?_
  show ((stripData γ p).1, (stripData γ p).2.1, (stripData γ p).2.2 + v)
      = ((stripData γ p').1, (stripData γ p').2.1, (stripData γ p').2.2 + v)
  rw [stripData_congr h0 h1]

/-- **Off the diagonal the two charts agree**, provided the prescribed unit direction `W` is the
doubled chord direction `(chordUnitDir γ) ^ 2` at the point. -/
lemma stripChartExt_eq_stripChart_of_unit {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {W : EuclideanSpace ℝ (Fin 2) → ℂ} (hW : ∀ p, ‖W p‖ = 1)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : Circle.exp (p 0) ≠ Circle.exp (p 1))
    (hWp : W p = (chordUnitDir γ (p 0, p 1)) ^ 2) :
    stripChartExt γ hγne W hW p = stripChart γ hγne 0 p := by
  rw [stripChartExt_eq_mk, stripChart_eq_mk, mk_inl_inj]
  refine Subtype.ext (Prod.ext (stripData_fst γ p).symm (Prod.ext (stripData_snd γ p).symm ?_))
  rw [add_zero]
  refine circleOf_injective ?_
  rw [circleOf_circOf, stripData_thd, (contDiffOn_chordUnitDir γ hγ).2.1 (p 0, p 1) hp]
  exact hWp

/-- The set of off-diagonal parameters is open. -/
lemma isOpen_offdiag :
    IsOpen {w : EuclideanSpace ℝ (Fin 2) | Circle.exp (w 0) ≠ Circle.exp (w 1)} := by
  have h : {w : EuclideanSpace ℝ (Fin 2) | Circle.exp (w 0) ≠ Circle.exp (w 1)}
      = (fun w : EuclideanSpace ℝ (Fin 2) => (Circle.exp (w 0), Circle.exp (w 1))) ⁻¹'
          {x : Circle × Circle | x.1 ≠ x.2} := rfl
  rw [h]
  refine (isClosed_diagonal.isOpen_compl).preimage ?_
  exact (Circle.exp.continuous.comp (by fun_prop)).prodMk
    (Circle.exp.continuous.comp (by fun_prop))

open Manifold in
open scoped Manifold ContDiff Topology in
/-- **The configuration strip has a smooth chart across its boundary.**

`Work.Drive.stripChart γ hγne 0` presents the configuration strip `M` of `γ` (a Möbius band whose
boundary is the diagonal, `μ (x,x) = (γ x, tangentDirC γ x, 0)`) in the capping space, and is `C^∞`
only *off* the diagonal (`Work.Drive.contMDiffOn_stripChart`): the doubled chord direction is
discontinuous there for the formula `circleOf (dirC (γ x - γ y))` (`dirC 0 = 0` while the limit is the
tangent direction).

This statement is the **smooth extension across the diagonal**: for every parameter point `p₀` there
is a map `F` into `CappingSpace`, `C^∞` (for `cappingCharted`) at `p₀`, which agrees with the strip
chart on the off-diagonal parameters near `p₀`.  (Its value on the diagonal is then forced to be
`μ (x,x)` by continuity, so `F` presents the *closed* strip.)  This is the datum a smooth presentation
of the capped plane needs along the gluing curve (`PLANE_MAP_NOTES.md`).

Route (all ingredients are in the workspace).

1. *Off the diagonal* (`Circle.exp (p₀ 0) ≠ Circle.exp (p₀ 1)`): take `F := stripChart γ hγne 0`; its
   smoothness at `p₀` follows from `Work.Drive.contMDiffOn_stripChart` (rotation parameter `0`, the
   square root `w_v := 1` of `circleOf 0 = 1`, `Work.Drive.circleOf_zero`) and
   `ContDiffOn.contMDiffAt`, and the equality holds everywhere off the diagonal.
2. *On the diagonal*: reduce to the lift `p₀ 0 = p₀ 1` using the `2π`-periodicity of the chord data
   (`Circle.exp_eq_exp` gives `p₀ 1 - p₀ 0 ∈ 2πℤ`; apply the extension at `q := (p₀ 0, p₀ 0)` and shift
   the second parameter back; `stripData` and `chordUnitDir` only see `γ ∘ Circle.exp`).
   `Work.Drive.exists_contMDiffAt_chordDir_sq` supplies `Z`, smooth at `q`, with `‖Z q‖ = 1` and
   `Z = (chordUnitDir γ)²` eventually off the diagonal.
3. *Unit modulus on a neighbourhood.*  `Z` is smooth at `q`, so `ContDiffAt.contDiffOn` gives
   `ContDiffOn ℝ 1 Z u` for some `u ∈ 𝓝 q`, hence continuity on `u`; the set `{p | ‖Z p‖ = 1}` is
   closed in `u` (`isClosed_eq`, `ContinuousOn`) and contains the off-diagonal points of `u`, which are
   dense there (the complement of the off-diagonal is a union of closed sets with empty interior), so
   it contains all of `u`.
4. *Global unit-valuedness for the chart.*  `Work.Drive.stripChartExt` wants a **global** proof
   `∀ p, ‖W p‖ = 1`; take `W p := if ‖Z p‖ = 1 then Z p else 1` (norm one for every `p`, by cases, and
   equal to `Z` on the neighbourhood of step 3, hence smooth at the relevant point).  Then
   `Work.Drive.contMDiffAt_stripChartExt` gives the smoothness of `stripChartExt γ hγne W ⋯`.
5. *The off-diagonal identification.*  Off the diagonal the third coordinate
   `circOf (Z p) = circOf ((chordUnitDir γ p)²)` is `dirC (γ (exp (p 0)) - γ (exp (p 1)))`
   (`Work.Drive.contDiffOn_chordUnitDir`, `Work.Drive.stripData_thd`), and `stripR`, `stripD` are the
   coordinates of `confOf (muOrd γ _)` (`Work.Drive.stripData_fst`, `Work.Drive.stripData_snd`), so
   the two classes agree by `Quotient.sound`, `Work.Drive.cappingRel_inl_inl`, `Subtype.ext` (the
   `rotConfig 0` of `stripChart` being the identity up to `add_zero`). -/
theorem exists_contMDiffAt_stripChart_closed (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (p₀ : EuclideanSpace ℝ (Fin 2)) :
    letI := Work.Drive.cappingCharted
    ∃ F : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace,
      ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) F p₀ ∧
      ∀ᶠ p in 𝓝 p₀, Circle.exp (p 0) ≠ Circle.exp (p 1) →
        F p = Work.Drive.stripChart γ hγne 0 p := by
  letI := Work.Drive.cappingCharted
  by_cases hoff : Circle.exp (p₀ 0) ≠ Circle.exp (p₀ 1)
  · -- the two parameters are distinct: the strip chart itself is smooth at `p₀`
    refine ⟨stripChart γ hγne 0, ?_, Filter.Eventually.of_forall (fun p _ => rfl)⟩
    refine (contMDiffOn_stripChart γ hγ hγne 0 (w_v := 1) ?_ (by norm_num)).contMDiffAt
      (isOpen_offdiag.mem_nhds hoff)
    rw [one_pow, circleOf_zero]
  · -- on the diagonal: reduce to the lift `p₀ 0 = p₀ 1` by shifting the second parameter
    push Not at hoff
    set d : ℝ := p₀ 1 - p₀ 0 with hd
    have hperiod : ∀ x : ℝ, Circle.exp (x - d) = Circle.exp x := by
      intro x
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hoff
      have hx : x - d = x + m * (2 * Real.pi) := by rw [hd, hm]; ring
      rw [hx, ← zsmul_eq_mul]
      exact Circle.periodic_exp.zsmul m x
    set e₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1] with he₂
    have hφ0 : ∀ p : EuclideanSpace ℝ (Fin 2), (p - d • e₂) 0 = p 0 := fun p => by simp [he₂]
    have hφ1 : ∀ p : EuclideanSpace ℝ (Fin 2), (p - d • e₂) 1 = p 1 - d := fun p => by simp [he₂]
    have hqq : (p₀ - d • e₂) 0 = (p₀ - d • e₂) 1 := by rw [hφ0 p₀, hφ1 p₀, hd]; ring
    -- the smooth extension of the squared chord direction at the lifted point
    obtain ⟨Z, hZs, hZq, hZeq⟩ := exists_contMDiffAt_chordDir_sq γ hγ (p₀ - d • e₂) hqq
    -- it has unit modulus on a neighbourhood of the lifted point
    have hunitZ : ∀ᶠ p in 𝓝 (p₀ - d • e₂), ‖Z p‖ = 1 := by
      refine eventually_norm_eq_one_of_contMDiffAt_dense
        (T := {p | Circle.exp (p 0) ≠ Circle.exp (p 1)}) dense_circleExp_ne hZs ?_
      refine Filter.Eventually.mono hZeq ?_
      intro p hp hpT
      rw [hp hpT, norm_pow, (contDiffOn_chordUnitDir γ hγ).2.2 (p 0, p 1) hpT, one_pow]
    -- a globally unit-valued direction, smooth at the lifted point
    let W : EuclideanSpace ℝ (Fin 2) → ℂ := fun p => if ‖Z p‖ = 1 then Z p else 1
    have hW : ∀ p, ‖W p‖ = 1 := by
      intro p
      by_cases h : ‖Z p‖ = 1
      · simp [W, h]
      · simp [W, h]
    have hWeq : W =ᶠ[𝓝 (p₀ - d • e₂)] Z := by
      filter_upwards [hunitZ] with p hp
      simp [W, hp]
    have hWs : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) W (p₀ - d • e₂) :=
      hZs.congr_of_eventuallyEq hWeq
    have hGs : ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (stripChartExt γ hγne W hW) (p₀ - d • e₂) :=
      contMDiffAt_stripChartExt hγ hγne (p₀ - d • e₂) hWs hW
    have hGoff : ∀ᶠ p in 𝓝 (p₀ - d • e₂), Circle.exp (p 0) ≠ Circle.exp (p 1) →
        stripChartExt γ hγne W hW p = stripChart γ hγne 0 p := by
      filter_upwards [hWeq, hZeq] with p hWp hZp hpT
      exact stripChartExt_eq_stripChart_of_unit hγ hγne hW hpT (by rw [hWp]; exact hZp hpT)
    -- the reparametrisation shifting the second parameter back
    have hφs : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => p - d • e₂) p₀ := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    refine ⟨fun p => stripChartExt γ hγne W hW (p - d • e₂), ?_, ?_⟩
    · exact ContMDiffAt.comp (f := fun p : EuclideanSpace ℝ (Fin 2) => p - d • e₂) p₀ hGs hφs
    · refine Filter.Eventually.mono (hφs.continuousAt.eventually hGoff) ?_
      intro p hp hpT
      have hprem : Circle.exp ((p - d • e₂) 0) ≠ Circle.exp ((p - d • e₂) 1) := by
        rw [hφ0 p, hφ1 p, hperiod]
        exact hpT
      show stripChartExt γ hγne W hW (p - d • e₂) = stripChart γ hγne 0 p
      rw [hp hprem]
      exact stripChart_congr hγne 0 (by rw [hφ0 p]) (by rw [hφ1 p, hperiod])

end

end Work.Drive
