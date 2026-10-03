import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_biholomorphicOn_of_greenOn_modulus
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.quadraticRemainder_of_analyticAt
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sectorComplement_of_quadraticRemainder
import Submission.Lib.Unif2.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# From a Green function and a modulus on a relatively compact domain to a regular piece

Let `W ⊆ X` be a relatively compact open domain of a Riemann surface `X`, `W ≠ X`, carrying a
Green function `E` with pole `x₀` (`Work.SimplyConnected.ABS.IsGreenOn`) and a holomorphic modulus
`Φ` of `E` on `W` (`Work.SimplyConnected.ABS.IsModulusOn`).  The disc lemma
`Work.SimplyConnected.ABS.exists_biholomorphicOn_of_greenOn_modulus` produces a biholomorphism
`χ` of `W` onto a round ball `ball 0 r`.  Taking `U := W ∩ χ ⁻¹' ball 0 ρ` for a radius
`max_K ‖χ‖ < ρ < r`, the present module verifies that `U` is a *regular piece* containing `K`:

* `χ` restricts to a homeomorphism of `W` onto `ball 0 r` (the map `χ` is injective and holomorphic
  on `W`, hence open by `Work.Parabolic.isOpenMap_of_injective_holomorphic`; continuity of the
  inverse follows from the open mapping property), so `ball 0 1 ≃ₜ ball 0 ρ ≃ₜ U`;
* the closure of `U` is `W ∩ χ ⁻¹' closedBall 0 ρ` — compact, as the image under `χ` of the closed
  ball inside the disc;
* `frontier (closure U) = frontier U = W ∩ χ ⁻¹' sphere 0 ρ` is a circle, hence connected;
* at a frontier point `p`, in the chart at `p` the function `g = χ ∘ (chartAt ℂ p).symm` is analytic
  with `g (c p) ≠ 0` and `deriv g (c p) ≠ 0` (by
  `Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn` and injectivity of `χ`), so its
  quadratic Taylor remainder produces a sector of directions in which `‖g‖ > ρ`; that sector is
  exactly the one required by `Work.SimplyConnected.ABS.HasSectorBoundary`.
-/

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

section Aux

/-- **An open subset of the disc `ball 0 r` contained in `closedBall 0 ρ` has no point of norm
exactly `ρ`.** -/
lemma norm_lt_of_isOpen_subset_closedBall {A : Set ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hA : IsOpen A) (hsub : A ⊆ Metric.closedBall (0 : ℂ) ρ) (hball : A ⊆ Metric.ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ A) : ‖z‖ < ρ := by
  by_contra hcon
  have hle : ‖z‖ ≤ ρ := by
    have h := hsub hz
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hzeq : ‖z‖ = ρ := le_antisymm hle (not_lt.mp hcon)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hz)
  set t : ℝ := min (ε / (2 * ρ)) ((r - ρ) / (2 * ρ)) with htdef
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  set w : ℂ := ((1 + t : ℝ) : ℂ) * z with hwdef
  have hdist : dist w z < ε := by
    have h1 : w - z = ((t : ℝ) : ℂ) * z := by rw [hwdef]; push_cast; ring
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos,
      hzeq]
    calc t * ρ ≤ (ε / (2 * ρ)) * ρ := mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have hwA : w ∈ A := hεsub hdist
  have hwnorm : ρ < ‖w‖ := by
    have h1 : ‖w‖ = (1 + t) * ‖z‖ := by
      rw [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + t)]
    rw [h1, hzeq]
    nlinarith [htpos]
  have h2 : ‖w‖ ≤ ρ := by
    have h := hsub hwA
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  linarith

/-- **An open set meeting `{ρ ≤ ‖z‖}` has points of norm `< ρ`.** -/
lemma exists_norm_lt_of_isOpen_subset_compl_closedBall {A : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hA : IsOpen A) (hsub : A ⊆ {z : ℂ | ρ ≤ ‖z‖}) {z : ℂ} (hz : z ∈ A) : ρ < ‖z‖ := by
  have hge : ρ ≤ ‖z‖ := hsub hz
  by_contra hcon
  have hzeq : ‖z‖ = ρ := le_antisymm (not_lt.mp hcon) hge
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hz)
  set t : ℝ := min (ε / (2 * ρ)) (1 / 2) with htdef
  have htpos : 0 < t := lt_min (by positivity) (by norm_num)
  have htle : t ≤ 1 / 2 := min_le_right _ _
  set w : ℂ := ((1 - t : ℝ) : ℂ) * z with hwdef
  have hdist : dist w z < ε := by
    have h1 : w - z = ((-(t : ℝ)) : ℂ) * z := by rw [hwdef]; push_cast; ring
    rw [dist_eq_norm, h1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos, hzeq]
    calc t * ρ ≤ (ε / (2 * ρ)) * ρ := mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have hwA : w ∈ A := hεsub hdist
  have hwnorm : ‖w‖ < ρ := by
    have h1 : ‖w‖ = (1 - t) * ‖z‖ := by
      rw [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    rw [h1, hzeq]
    nlinarith [htle, hρ]
  have h2 : ρ ≤ ‖w‖ := hsub hwA
  linarith

end Aux

/-- **From a Green function and a modulus on a relatively compact domain to a regular piece.**

Let `W` be an open subset of a Riemann surface, `W ≠ X`, with compact closure, and suppose `W`
carries a Green function `E` with pole `x₀ ∈ W` and a holomorphic modulus `Φ` of `E` on `W`
(in the ambient sense `IsGreenOn`, `IsModulusOn`).  Then every compact `K ⊆ W` is contained in an
open `U` homeomorphic to the open unit disc, with compact closure, whose closure has connected
frontier, and which satisfies the sector condition `HasSectorBoundary U p` at every frontier point.

(The proof uses the endgame `exists_biholomorphicOn_of_greenOn_modulus`: `χ` is a biholomorphism of
`W` onto a round ball `ball 0 r`; take `U := W ∩ χ ⁻¹' ball 0 ρ` for a radius `ρ < r` exceeding
`max_K ‖χ‖`; then `U ≅ ball 0 ρ ≅ ball 0 1`, its closure is compact and
`frontier (closure U) = W ∩ χ ⁻¹' (sphere 0 ρ)` is a circle, hence connected; and the sector
condition at a frontier point follows from the analytic local geometry of `χ` in a chart at that
point: the quadratic Taylor remainder of the local representative at a point where its derivative
does not vanish (`Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`) produces the cone.) -/
theorem exists_regularPiece_of_greenOn_modulus {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {W : Set X} (hWo : IsOpen W) (hWne : W ≠ Set.univ)
    (hcomp : IsCompact (closure W)) {x₀ : X} (hx₀ : x₀ ∈ W) {E : X → ℝ} {Φ : X → ℂ}
    (hE : Work.SimplyConnected.ABS.IsGreenOn W x₀ E)
    (hΦ : Work.SimplyConnected.ABS.IsModulusOn W x₀ E Φ)
    {K : Set X} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, Work.SimplyConnected.ABS.HasSectorBoundary U p := by
  classical
  obtain ⟨r, χ, hrpos, hχhol, hχinj, hχzero, hχimage, hχderiv, hχout⟩ :=
    exists_biholomorphicOn_of_greenOn_modulus hX hWo hWne hcomp hx₀ hE hΦ
  have hχcontOn : ContinuousOn χ W :=
    fun x hx => (hχhol x hx).continuousAt.continuousWithinAt
  -- ## The radius `ρ`
  have hρexists : ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∀ x ∈ K, ‖χ x‖ < ρ := by
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨r / 2, by linarith, by linarith, by simp⟩
    · obtain ⟨x₁, hx₁K, hmax⟩ := hK.exists_isMaxOn hKne (hχcontOn.mono hKW).norm
      have hlt : ‖χ x₁‖ < r := by
        have h : χ x₁ ∈ χ '' W := ⟨x₁, hKW hx₁K, rfl⟩
        rwa [hχimage, Metric.mem_ball, dist_zero_right] at h
      refine ⟨(‖χ x₁‖ + r) / 2, by linarith [norm_nonneg (χ x₁)], by linarith,
        fun x hx => lt_of_le_of_lt (hmax hx) ?_⟩
      linarith
  obtain ⟨ρ, hρpos, hρlt, hKρ⟩ := hρexists
  -- ## Transport to the open sub-surface `W`
  let W' : TopologicalSpace.Opens X := ⟨W, hWo⟩
  have hχholW : Submission.HolomorphicOnX (X := ↥W') (fun ξ : ↥W' => χ ξ.1) Set.univ :=
    fun ξ _ => subtypeHolomorphicOnXAt ξ (hχhol ξ.1 ξ.2)
  have hχinjW : Function.Injective (fun ξ : ↥W' => χ ξ.1) :=
    fun a b hab => Subtype.ext (hχinj a.2 b.2 hab)
  have hχopenW : IsOpenMap (fun ξ : ↥W' => χ ξ.1) :=
    Work.Parabolic.isOpenMap_of_injective_holomorphic hχholW hχinjW
  have hχcontW : Continuous (fun ξ : ↥W' => χ ξ.1) := hχholW.continuous
  have hmemW : ∀ ξ : ↥W', χ ξ.1 ∈ Metric.ball (0 : ℂ) r := fun ξ => by
    have h : χ ξ.1 ∈ χ '' W := ⟨ξ.1, ξ.2, rfl⟩
    rwa [hχimage] at h
  let χ'' : ↥W' → Metric.ball (0 : ℂ) r := fun ξ => ⟨χ ξ.1, hmemW ξ⟩
  have hχ''inj : Function.Injective χ'' := fun a b hab =>
    hχinjW (by simpa using congrArg Subtype.val hab)
  have hχ''surj : Function.Surjective χ'' := fun y => by
    have hy : (y : ℂ) ∈ χ '' W := by rw [hχimage]; exact y.2
    obtain ⟨x, hxW, hxeq⟩ := hy
    exact ⟨⟨x, hxW⟩, Subtype.ext hxeq⟩
  have hχ''cont : Continuous χ'' := hχcontW.subtype_mk hmemW
  have hχ''open : IsOpenMap χ'' := hχopenW.codRestrict hmemW
  let e : ↥W' ≃ₜ Metric.ball (0 : ℂ) r :=
    IsHomeomorph.homeomorph χ'' ⟨hχ''cont, hχ''open, hχ''inj, hχ''surj⟩
  have he_apply : ∀ ξ : ↥W', (e ξ : ℂ) = χ ξ.1 := fun ξ => rfl
  have he_symm : ∀ y : Metric.ball (0 : ℂ) r, χ ((e.symm y : ↥W') : X) = (y : ℂ) := fun y => by
    have h := congrArg Subtype.val (e.apply_symm_apply y)
    rw [← he_apply (e.symm y)]
    exact h
  -- ## The candidate piece `U`
  have hρballc : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r :=
    Metric.closedBall_subset_ball hρlt
  have hρball : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r :=
    Metric.ball_subset_ball hρlt.le
  have hUopen : IsOpen (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have h1 : χ ⁻¹' Metric.ball (0 : ℂ) ρ ∈ 𝓝 x :=
      (hχhol x hx.1).continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2)
    exact Filter.inter_mem (hWo.mem_nhds hx.1) h1
  -- the closed companion `W ∩ χ ⁻¹' closedBall 0 ρ` is compact
  have hCcompact : IsCompact (W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ) := by
    let ι : Metric.closedBall (0 : ℂ) ρ → Metric.ball (0 : ℂ) r :=
      fun y => ⟨(y : ℂ), hρballc y.2⟩
    have hDcomp : IsCompact {y : Metric.ball (0 : ℂ) r | (y : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ} := by
      have hιcont : Continuous ι := continuous_subtype_val.subtype_mk _
      have himg : ι '' Set.univ
          = {y : Metric.ball (0 : ℂ) r | (y : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ} := by
        ext y; constructor
        · rintro ⟨z, -, rfl⟩
          exact z.2
        · intro hy
          exact ⟨⟨(y : ℂ), hy⟩, Set.mem_univ _, rfl⟩
      haveI : CompactSpace ↥(Metric.closedBall (0 : ℂ) ρ) :=
        isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) ρ)
      rw [← himg]
      exact isCompact_univ.image hιcont
    have hAc : IsCompact (e ⁻¹' {y : Metric.ball (0 : ℂ) r |
        (y : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ}) := (e.isCompact_preimage).mpr hDcomp
    have hCeq : Subtype.val '' (e ⁻¹' {y : Metric.ball (0 : ℂ) r |
          (y : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ})
        = W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ := by
      ext x; constructor
      · rintro ⟨ξ, hξ, rfl⟩
        have hξ' : (e ξ : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := hξ
        refine ⟨ξ.2, ?_⟩
        rw [Set.mem_preimage, ← he_apply ξ]
        exact hξ'
      · rintro ⟨hxW, hxc⟩
        refine ⟨⟨x, hxW⟩, ?_, rfl⟩
        rw [Set.mem_preimage]
        show (e ⟨x, hxW⟩ : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ
        rw [he_apply]
        exact hxc
    rw [← hCeq]
    exact hAc.image continuous_subtype_val
  -- ## `closure U` and `interior` of the closed companion
  have hclosureU : closure (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ)
      = W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ := by
    apply Subset.antisymm
    · exact closure_minimal (fun x hx => ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩)
        hCcompact.isClosed
    · intro x hx
      rw [mem_closure_iff]
      intro O hO hxO
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      set O' : Set X := O ∩ W with hO'def
      have hO'open : IsOpen O' := hO.inter hWo
      have hxO' : x ∈ O' := ⟨hxO, hx.1⟩
      set A : Set ↥W' := Subtype.val ⁻¹' O' with hAdef
      have hAopen : IsOpen A := hO'open.preimage continuous_subtype_val
      have hImOpen : IsOpen ((fun ξ : ↥W' => χ ξ.1) '' A) := hχopenW A hAopen
      have hmemIm : χ x ∈ (fun ξ : ↥W' => χ ξ.1) '' A := ⟨⟨x, hx.1⟩, hxO', rfl⟩
      have hsubIm : (fun ξ : ↥W' => χ ξ.1) '' A ⊆ {z : ℂ | ρ ≤ ‖z‖} := by
        rintro z ⟨ξ, hξ, rfl⟩
        have hξO : ξ.1 ∈ O := hξ.1
        have hξW : ξ.1 ∈ W := hξ.2
        have hξnotU : ¬ (ξ.1 ∈ W ∧ χ ξ.1 ∈ Metric.ball (0 : ℂ) ρ) := by
          intro hcon
          have hmem : ξ.1 ∈ O ∩ (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) := ⟨hξO, hcon⟩
          rw [hemp] at hmem
          exact hmem
        exact le_of_not_gt fun hlt =>
          hξnotU ⟨hξW, by rw [Metric.mem_ball, dist_zero_right]; exact hlt⟩
      have hgt : ρ < ‖χ x‖ :=
        exists_norm_lt_of_isOpen_subset_compl_closedBall hρpos hImOpen hsubIm hmemIm
      have hle : ‖χ x‖ ≤ ρ := by
        have h := hx.2
        rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at h
        exact h
      linarith
  have hinteriorC : interior (W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ)
      = W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ := by
    apply Subset.antisymm
    · intro x hx
      have hxC : x ∈ W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ := interior_subset hx
      obtain ⟨hxW, hxc⟩ := hxC
      have hle : ‖χ x‖ ≤ ρ := by
        rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hxc
        exact hxc
      by_cases hlt : ‖χ x‖ < ρ
      · refine ⟨hxW, ?_⟩
        rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
        exact hlt
      · exfalso
        have heq : ‖χ x‖ = ρ := le_antisymm hle (not_lt.mp hlt)
        set O' : Set X := interior (W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ) ∩ W with hO'def
        have hO'open : IsOpen O' := isOpen_interior.inter hWo
        have hxO' : x ∈ O' := ⟨hx, hxW⟩
        set A : Set ↥W' := Subtype.val ⁻¹' O' with hAdef
        have hAopen : IsOpen A := hO'open.preimage continuous_subtype_val
        have hImOpen : IsOpen ((fun ξ : ↥W' => χ ξ.1) '' A) := hχopenW A hAopen
        have hmemIm : χ x ∈ (fun ξ : ↥W' => χ ξ.1) '' A := ⟨⟨x, hxW⟩, hxO', rfl⟩
        have hsubIm : (fun ξ : ↥W' => χ ξ.1) '' A ⊆ Metric.closedBall (0 : ℂ) ρ := by
          rintro z ⟨ξ, hξ, rfl⟩
          have h : ξ.1 ∈ W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ := interior_subset hξ.1
          exact h.2
        have hballIm : (fun ξ : ↥W' => χ ξ.1) '' A ⊆ Metric.ball (0 : ℂ) r := by
          rintro z ⟨ξ, hξ, rfl⟩
          exact hmemW ξ
        have hlt' := norm_lt_of_isOpen_subset_closedBall hρpos hρlt hImOpen hsubIm hballIm hmemIm
        rw [heq] at hlt'
        exact absurd hlt' (lt_irrefl ρ)
    · intro x hx
      have hsub : W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ ⊆ W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ :=
        fun y hy => ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
      exact interior_maximal hsub hUopen hx
  have hdiff : (W ∩ χ ⁻¹' Metric.closedBall (0 : ℂ) ρ) \ (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ)
      = W ∩ χ ⁻¹' Metric.sphere (0 : ℂ) ρ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxB⟩ := hx
      obtain ⟨hxW, h1⟩ := hxA
      have h2 : ¬ (χ x ∈ Metric.ball (0 : ℂ) ρ) := fun hb => hxB ⟨hxW, hb⟩
      refine ⟨hxW, ?_⟩
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at h1
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right]
      exact le_antisymm h1 (not_lt.mp h2)
    · intro hx
      obtain ⟨hxW, h⟩ := hx
      rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right] at h
      refine ⟨⟨hxW, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]; exact le_of_eq h
      · intro hb
        have h2 : ‖χ x‖ < ρ := by
          have hh := hb.2
          rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hh
        rw [h] at h2
        exact absurd h2 (lt_irrefl ρ)
  have hfrontU : frontier (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ)
      = W ∩ χ ⁻¹' Metric.sphere (0 : ℂ) ρ := by
    rw [hUopen.frontier_eq, hclosureU, hdiff]
  have hfrontC : frontier (closure (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ))
      = W ∩ χ ⁻¹' Metric.sphere (0 : ℂ) ρ := by
    rw [isClosed_closure.frontier_eq, hclosureU, hinteriorC, hdiff]
  -- ## `S` is a circle, hence connected
  set S : Set X := W ∩ χ ⁻¹' Metric.sphere (0 : ℂ) ρ with hSdef
  let Ψ : Metric.sphere (0 : ℂ) ρ → Metric.ball (0 : ℂ) r :=
    fun y => ⟨(y : ℂ), hρballc (Metric.sphere_subset_closedBall y.2)⟩
  let Φ' : Metric.sphere (0 : ℂ) ρ → X := fun y => ((e.symm (Ψ y) : ↥W') : X)
  have hΨcont : Continuous Ψ := continuous_subtype_val.subtype_mk _
  have hΦcont : Continuous Φ' :=
    continuous_subtype_val.comp (e.symm.continuous.comp hΨcont)
  have hrange : Set.range Φ' = S := by
    rw [hSdef]
    ext x; constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(e.symm (Ψ y) : ↥W').2, ?_⟩
      rw [Set.mem_preimage, he_symm]
      exact y.2
    · rintro ⟨hxW, hxsph⟩
      have hsph : χ x ∈ Metric.sphere (0 : ℂ) ρ := hxsph
      refine ⟨⟨χ x, hsph⟩, ?_⟩
      have h1 : Ψ ⟨χ x, hsph⟩ = e ⟨x, hxW⟩ := Subtype.ext (he_apply ⟨x, hxW⟩).symm
      dsimp only [Φ']
      rw [h1, e.symm_apply_apply]
  haveI : ConnectedSpace ↥(Metric.sphere (0 : ℂ) ρ) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) hρpos.le)
  have hSconn : IsConnected S := by
    rw [← hrange]
    exact isConnected_range hΦcont
  -- ## The homeomorphism `ball 0 1 ≃ₜ U`
  have hFU : ∀ y : Metric.ball (0 : ℂ) ρ,
      (e.symm ⟨(y : ℂ), hρball y.2⟩ : ↥W').1 ∈ W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ := by
    intro y
    refine ⟨(e.symm ⟨(y : ℂ), hρball y.2⟩ : ↥W').2, ?_⟩
    rw [Set.mem_preimage, he_symm]
    exact y.2
  let F : Metric.ball (0 : ℂ) ρ → ↥(W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) :=
    fun y => ⟨(e.symm ⟨(y : ℂ), hρball y.2⟩ : ↥W').1, hFU y⟩
  let G : ↥(W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) → Metric.ball (0 : ℂ) ρ :=
    fun x => ⟨χ x.1, x.2.2⟩
  have hleftinv : Function.LeftInverse G F := by
    intro y
    apply Subtype.ext
    dsimp only [F, G]
    exact he_symm _
  have hrightinv : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    dsimp only [F, G]
    have h1 : (⟨χ x.1, hρball x.2.2⟩ : Metric.ball (0 : ℂ) r) = e ⟨x.1, x.2.1⟩ :=
      Subtype.ext (he_apply ⟨x.1, x.2.1⟩).symm
    rw [h1, e.symm_apply_apply]
  have hFcont : Continuous F := by
    have hι : Continuous (fun y : Metric.ball (0 : ℂ) ρ =>
        (⟨(y : ℂ), hρball y.2⟩ : Metric.ball (0 : ℂ) r)) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_subtype_val.comp (e.symm.continuous.comp hι)).subtype_mk _
  have hGcont : Continuous G := by
    have hχU : Continuous (fun x : ↥(W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) => χ x.1) :=
      continuous_iff_continuousAt.mpr fun x =>
        ((hχhol x.1 x.2.1).continuousAt).comp continuous_subtype_val.continuousAt
    exact hχU.subtype_mk _
  let hb : Metric.ball (0 : ℂ) ρ ≃ₜ ↥(W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) :=
    { toEquiv := ⟨F, G, hleftinv, hrightinv⟩
      continuous_toFun := hFcont
      continuous_invFun := hGcont }
  have hρne : (ρ : ℂ) ≠ 0 := fun h => hρpos.ne' (Complex.ofReal_eq_zero.mp h)
  let hscal : Metric.ball (0 : ℂ) 1 ≃ₜ Metric.ball (0 : ℂ) ρ :=
    (Homeomorph.mulLeft₀ (ρ : ℂ) hρne).subtype (fun z => by
      have h2 : ρ * ‖z‖ < ρ ↔ ‖z‖ < 1 := by
        have h3 := mul_lt_mul_iff_left₀ (a := ρ) (b := ‖z‖) (c := 1) hρpos
        rwa [mul_comm ‖z‖ ρ, one_mul] at h3
      simp only [Metric.mem_ball, dist_zero_right, Homeomorph.coe_mulLeft₀, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
      exact h2.symm)
  -- ## The sector condition at frontier points
  have hsector : ∀ p ∈ frontier (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ),
      HasSectorBoundary (W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ) p := by
    intro p hp
    have hpS : p ∈ W ∩ χ ⁻¹' Metric.sphere (0 : ℂ) ρ := by
      rw [hfrontU] at hp
      exact hp
    obtain ⟨hpW, hpsphere⟩ := hpS
    have hpnorm : ‖χ p‖ = ρ := by
      rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right] at hpsphere
      exact hpsphere
    -- the chart at `p` and its local representative of `χ`
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hcdef
    have hcsrc : p ∈ c.source := mem_chart_source ℂ p
    have htend : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := c.tendsto_symm hcsrc
    have hε₁ : ∀ᶠ z in 𝓝 (c p), c.symm z ∈ W := htend.eventually (hWo.mem_nhds hpW)
    obtain ⟨ε₁, hε₁pos, hε₁W⟩ := Metric.mem_nhds_iff.mp hε₁
    obtain ⟨ε₃, hε₃pos, hε₃⟩ : ∃ ε₃ > 0, Metric.ball (c p) ε₃ ⊆ c.target :=
      Metric.isOpen_iff.mp c.open_target (c p) (c.map_source hcsrc)
    set r₀ : ℝ := min ε₁ ε₃ with hr₀def
    have hr₀pos : 0 < r₀ := lt_min hε₁pos hε₃pos
    have hsub_cball : Metric.ball (c p) r₀ ⊆ Metric.ball (c p) ε₁ :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hsub_ctarget : Metric.ball (c p) r₀ ⊆ c.target :=
      fun z hz => hε₃ (Metric.ball_subset_ball (min_le_right _ _) hz)
    have hderiv : deriv (χ ∘ c.symm) (c p) ≠ 0 := by
      refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr₀pos (hχhol p hpW) ?_
      intro u hu v hv huv
      have huW : c.symm u ∈ W := hε₁W (hsub_cball hu)
      have hvW : c.symm v ∈ W := hε₁W (hsub_cball hv)
      have hsymm : c.symm u = c.symm v := hχinj huW hvW huv
      calc u = c (c.symm u) := (c.right_inv (hsub_ctarget hu)).symm
        _ = c (c.symm v) := by rw [hsymm]
        _ = v := c.right_inv (hsub_ctarget hv)
    have hgval : (χ ∘ c.symm) (c p) ≠ 0 := by
      have h1 : (χ ∘ c.symm) (c p) = χ p := by
        simp only [Function.comp_apply]
        rw [c.left_inv hcsrc]
      rw [h1]
      intro hzero
      have : ‖χ p‖ = 0 := by rw [hzero, norm_zero]
      rw [hpnorm] at this
      exact hρpos.ne' this
    obtain ⟨C, hC⟩ := quadraticRemainder_of_analyticAt (hχhol p hpW)
    obtain ⟨L₁, L₂, δ, hL₁, hL₂, hδpos, hsectne, hsect⟩ :=
      sectorComplement_of_quadraticRemainder (g := χ ∘ c.symm) (w₀ := c p)
        (d := deriv (χ ∘ c.symm) (c p)) hgval hderiv ⟨C, hC⟩
    refine ⟨c, c.source ∩ c ⁻¹' Metric.ball (c p) δ, L₁, L₂, chart_mem_atlas ℂ p,
      ?_, ?_, ?_, hcsrc, hL₁, hL₂, hsectne, ?_⟩
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      exact Filter.inter_mem (c.open_source.mem_nhds hx.1)
        ((c.continuousAt hx.1).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2))
    · refine ⟨hcsrc, ?_⟩
      rw [Set.mem_preimage]
      exact Metric.mem_ball_self hδpos
    · exact Set.inter_subset_left
    · intro x hx
      obtain ⟨hxU, hxV⟩ := hx
      obtain ⟨hxcsrc, hxcball⟩ := hxV
      have hxnorm : ‖χ x‖ < ρ := by
        have h := hxU.2
        rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at h
      have hdist : ‖c x - c p‖ < δ := by
        have h := hxcball
        rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      have hχx : χ x = (χ ∘ c.symm) (c p + (c x - c p)) := by
        have h1 : c p + (c x - c p) = c x := by abel
        simp only [Function.comp_apply, h1]
        rw [c.left_inv hxcsrc]
      have hgw : (χ ∘ c.symm) (c p) = χ p := by
        simp only [Function.comp_apply]
        rw [c.left_inv hcsrc]
      have hlt : ‖(χ ∘ c.symm) (c p + (c x - c p))‖ < ‖(χ ∘ c.symm) (c p)‖ := by
        rw [hgw, hpnorm, ← hχx]
        exact hxnorm
      exact hsect (c x - c p) hdist hlt
  -- ## Assembly
  refine ⟨W ∩ χ ⁻¹' Metric.ball (0 : ℂ) ρ, hUopen, ⟨hscal.trans hb⟩, ?_, ?_, ?_, ?_⟩
  · rw [hclosureU]
    exact hCcompact
  · rw [hfrontC]
    exact hSconn
  · intro x hx
    exact ⟨hKW hx,
      by simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hKρ x hx⟩
  · intro p hp
    exact hsector p hp

end Work.SimplyConnected.ABS
