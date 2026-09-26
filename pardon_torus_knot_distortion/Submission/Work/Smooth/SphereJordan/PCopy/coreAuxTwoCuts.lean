import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.plainAnnulusSetup
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts
import Submission.Work.Smooth.SphereJordan.PCopy.coreAuxTwoCutsCrux
import Submission.Work.Smooth.SphereJordan.PCopy.SpanSetup
import Submission.Work.Smooth.SphereJordan.PCopy.radialTwoCutsPieces
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetSpans
import Submission.Work.Smooth.SphereJordan.PCopy.tgtSpansClean
import Submission.Work.Smooth.SphereJordan.PCopy.twoCutsAssemblyCrux

namespace Work.Smooth.SphereJordan

/-!
# The two-pccuts core of the planar pcannulus theorem

The target of this file, `Work.Smooth.SphereJordan.pccoreAuxTwoCuts`, is the planar pcannulus theorem
in its *injection* form: for a simple closed plane curve `γ` whose trace lies in the open unit disc
and a planar Schoenflies datum `S` for it, there are a sign `s = ±1` and an injective continuous
`F : 𝔻 → 𝔻` which fixes `∂𝔻` pointwise and carries the half-circle `(1/2) e^{i s θ}` onto `γ(θ)` in
the prescribed parametrisation.

The mathematical content is the classical two-dimensional **pcannulus theorem** ("the region between
a Jordan curve inside the unit disc and the boundary circle of the disc is a standard pcannulus"),
here in the *plain* form `PlainAnnulusSchoenflies` of the module
`Submission/Work/Smooth/SphereJordan/Pasting.lean`; the reduction below is the standard one:

* the *plain* form applied to the Schoenflies embedding `S.e` of `γ` (regarded as an embedding of
  the model disc into itself, legitimate because `closure S.V` lies in the *open* unit disc,
  `pcclosure_V_subset_openBall`) gives, through the parametrised form `AnnulusSchoenflies`
  (`annulusSchoenflies_of_plain`, proved by reparametrising the inner boundary circle with
  `annulusInterpolation`), a homeomorphism `Θ` of `𝔻` fixing `∂𝔻` pointwise and carrying the
  boundary circle of `S.e` onto the concentric circle of radius `1/2` **in the prescribed
  parametrisation up to the orientation sign** `s`;
* the inverse `F := Θ⁻¹` is then an injection fixing `∂𝔻` pointwise with
  `F ((1/2) e^{i s θ}) = S.e (e^{iθ}) = γ(θ)`, which is the conclusion.

The geometric input (the plain pcannulus form) is isolated in `_of_plain` so that the file can be
consumed with whatever proof of it is available; the final theorem instantiates it.
-/

/-!
## The route to the plain pcannulus form (the two-pccuts construction), and what is verified

The single remaining input is `PlainAnnulusSchoenflies` (from `PlaneHypothesis`); equivalently the
*closure clause*: a homeomorphism `Θ` of `𝔻` fixing `∂𝔻` pointwise with `x ∈ closure S.V ↔
‖Θ x‖ ≤ 1/2`.  The classical route is the "two pccuts" of the pcannulus `A = 𝔻 ∖ S.V`:

* `Work.Smooth.SphereJordan.pcexists_cuts` (module `plainAnnulusSetup`, **proved**) produces the two
  crosscuts along the *diameter through the pcbase point* `p = S.e 0`: with `u = pccutDir S` a unit
  vector and `p = ‖p‖ • u`, the pccuts are `pccut₁ = [p + t₁u, p + s₁u]`, `pccut₂ = [p - s₂u, p - t₂u]`,
  whose open parts lie in `A ∖ closure S.V`, whose inner endpoints lie on `γ`, and whose outer
  endpoints lie on `∂𝔻` (they are `±u`).
* What remains is the *tiling*: the cut pcannulus `pcannulusCut S t₁ s₁ t₂ s₂ = A ∖ (pccut₁ ∪ pccut₂)` has
  exactly two components, and the closure of each is a closed disc (bounded by the four-arc curve
  consisting of a `γ`-arc, a cut, the semicircle `pcupArc S` (resp. `pcdownArc S`), and the other cut).

**What is verified by hand (the reader may reproduce it).**  In the rotated coordinates `z ↦ z/u`
(so `u = 1`, `p = r ∈ (0,1)` real) the pccuts are the segments `[a₁,1]` and `[-1,a₂]` with
`-1 < a₂ < r < a₁ < 1`, and the two marked points of `pcpieceUp` / `pcpieceDown` are `i` and `-i`.

* *At most two components.*  For `x ∈ pcannulusCut`, let `z(σ) = (1-σ)p + σx` (`σ ∈ [0,1]`) be the
  segment from the pcbase point to `x`, and let `σ₁` be the *last* parameter `≤ σ_x` with
  `z(σ₁) ∈ closure S.V`.  Then `z(σ₁) ∈ γ` (if it were interior to `closure S.V`, a full
  neighbourhood of it would meet the segment beyond `σ₁`), `z(σ₁) ≠ a₁, a₂` (the parameters of
  `a₁`, `a₂` are `> σ_x` on a cut ray, by the cut properties), and the segment `z([σ₁,σ_x])` lies in
  `pcannulusCut` (its points are outside `closure S.V` by maximality, in `closedBall` by convexity,
  and off the pccuts because those live on the two rays `p ± [tᵢ, sᵢ]u` while `σ_x` is below `t₁`).
  So every point of `pcannulusCut` is joined inside it to a point of `γ ∖ {a₁, a₂}`, which has at most
  two components (the two open arcs); hence `pcannulusCut` has at most two components.
* *At least two components.*  It suffices to show that the two open arcs of `γ ∖ {a₁, a₂}` lie in
  different components; a path joining them would, together with the two pccuts, cross the "barrier"
  `pccut₁ ∪ (the γ-arc) ∪ pccut₂` which separates `A` — the precise form used by the classical proof is
  that the four-arc curve is a simple closed curve whose *bounded* side is the corresponding piece.

**A rejected false start.**  Note that the two pccuts do *not* have to be "generic": `γ` may meet the
diameter through `p` in further points (an "outward peninsula" of `closure S.V`), and at such a
point the *exterior* half-disc of `γ` joins the two sides of the diameter locally.  This does *not*
merge the two components: in that configuration the local half-disc lies entirely in the *lower*
component (the "gap" of the diameter in `A` opens only away from `γ`), which is a useful check for
any proposed proof of the tiling.
-/

open Set

/-- **The target from the plain planar pcannulus theorem.**

If the planar pcannulus theorem holds in its plain form (`PlainAnnulusSchoenflies`), then the
two-pccuts core `pccoreAuxTwoCuts` holds. -/
theorem pccoreAuxTwoCuts_of_plain (hP : Work.Smooth.SphereJordan.PlainAnnulusSchoenflies)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) =
        Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  have hAS : Work.Smooth.SphereJordan.AnnulusSchoenflies :=
    Work.Smooth.SphereJordan.annulusSchoenflies_of_plain hP
  -- the Schoenflies embedding of `γ`, regarded as an embedding of the model disc into itself
  have hb : ∀ z : Work.Smooth.SphereJordan.Disc, ‖(S.e z : ℂ)‖ < 1 := fun z =>
    Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball
      (by rw [← S.range_e]; exact ⟨z, rfl⟩)
  let f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) :=
    ⟨fun z => ⟨S.e z, by rw [Metric.mem_closedBall, dist_zero_right]; exact (hb z).le⟩,
      Continuous.subtype_mk S.e.continuous (fun z => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (hb z).le)⟩
  have hfval : ∀ z : Work.Smooth.SphereJordan.Disc,
      ((f z : Work.Smooth.SphereJordan.Disc) : ℂ) = S.e z := fun z => rfl
  have hfinj : Function.Injective f := fun a b hab =>
    S.inj (by rw [← hfval a, ← hfval b, congrArg Subtype.val hab])
  have hfbd : ∀ θ : ℝ,
      ‖((f (Work.Smooth.SphereJordan.circlePoint θ) :
        Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 := fun θ => by
    rw [hfval, S.boundary θ]; exact hball θ
  obtain ⟨Θ, s, hs1, hfix, hhalf, -, -⟩ := hAS f hfinj hfbd
  refine ⟨⟨Θ.symm, Θ.symm.continuous⟩, s, hs1, (fun a b hab => Θ.symm.injective hab), ?_, ?_⟩
  · intro θ
    show Θ.symm (Work.Smooth.SphereJordan.circlePoint θ) =
      Work.Smooth.SphereJordan.circlePoint θ
    rw [Homeomorph.symm_apply_eq]
    exact (hfix θ).symm
  · intro θ
    have hs2 : s * (s * θ) = θ := by rcases hs1 with h1 | h1 <;> rw [h1] <;> ring
    have key : Θ.symm (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) =
        f (Work.Smooth.SphereJordan.circlePoint θ) := by
      rw [← hhalf (s * θ), Homeomorph.symm_apply_apply, hs2]
    change ((Θ.symm (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
      Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ
    rw [key, hfval, S.boundary θ]

/-!
## The first half of the two-pccuts tiling: inward reachability

`Work.Smooth.SphereJordan.pcannulusCut_reach_inner` (**proved below**): every point of the cut pcannulus
`pcannulusCut S t₁ s₁ t₂ s₂` is joined, inside the cut pcannulus, to a point of the trace of `γ` off the
two pccuts — along the segment from the pcbase point `p = S.e 0` stopped at the last point of
`closure S.V`.  Consequently the cut pcannulus has **at most two components** (every point is joined
to a point of `γ ∖ {a₁, a₂}`, a space with at most two components).

The supporting lemmas are geometric: `pcsegPt` is the parametrised segment, `pcnorm_base_add`,
`pcnorm_base_sub`, `pcsphere_param`, `pcsphere_param_sub` compute the radius along the two cut rays, and
`pcray_param_lt`, `pcray_param_lt_neg` are the key observation — a point of one of the pccuts forces the
corresponding parameter of `x` below `tᵢ`.
-/

section TwoCutsReach

open Set

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The segment from the pcbase point to `x`, as a function of the parameter `σ`. -/
def pcsegPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) (σ : ℝ) : ℂ :=
  (1 - σ) * pcbase S + σ * x

@[simp] theorem pcsegPt_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) :
    pcsegPt S x 0 = pcbase S := by simp [pcsegPt]

@[simp] theorem pcsegPt_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) :
    pcsegPt S x 1 = x := by simp [pcsegPt]

theorem pccontinuous_segPt (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) :
    Continuous (pcsegPt S x) := by unfold pcsegPt; fun_prop

theorem pcsegPt_sub (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) (σ : ℝ) :
    pcsegPt S x σ - pcbase S = (σ : ℂ) * (x - pcbase S) := by unfold pcsegPt; ring

theorem pcsegPt_affine (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℂ) {a τ : ℝ} :
    pcsegPt S x (a + τ * (1 - a)) = (1 - τ) * pcsegPt S x a + τ * x := by
  unfold pcsegPt; push_cast; ring

/-- The pcbase point plus a nonnegative multiple of `pccutDir` lies on the ray, at the expected
radius. -/
theorem pcnorm_base_add_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} (hc : 0 ≤ c) :
    pcbase S + (c : ℂ) * pccutDir S = ((‖pcbase S‖ + c : ℝ) : ℂ) * pccutDir S := by
  have hb : pcbase S = ((‖pcbase S‖ : ℝ) : ℂ) * pccutDir S := pcbase_eq_smul_cutDir S
  have h : ((‖pcbase S‖ + c : ℝ) : ℂ) = ((‖pcbase S‖ : ℝ) : ℂ) + ((c : ℝ) : ℂ) :=
    Complex.ofReal_add _ _
  rw [h, add_mul, ← hb]

theorem pcnorm_base_add (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} (hc : 0 ≤ c) :
    ‖pcbase S + (c : ℂ) * pccutDir S‖ = ‖pcbase S‖ + c := by
  rw [pcnorm_base_add_smul S hc, norm_mul, pcnorm_cutDir S, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hc)]

theorem pcsphere_param (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {s : ℝ} (hs : 0 < s)
    (h : pcbase S + (s : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1) :
    ‖pcbase S‖ + s = 1 := by
  have h1 : ‖pcbase S + (s : ℂ) * pccutDir S‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using h
  rw [pcnorm_base_add S hs.le] at h1
  exact h1


/-- The pcbase point minus a positive multiple of `pccutDir`. -/
theorem pcnorm_base_sub_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} :
    pcbase S - (c : ℂ) * pccutDir S = ((‖pcbase S‖ - c : ℝ) : ℂ) * pccutDir S := by
  have hb : pcbase S = ((‖pcbase S‖ : ℝ) : ℂ) * pccutDir S := pcbase_eq_smul_cutDir S
  have h : ((‖pcbase S‖ - c : ℝ) : ℂ) = ((‖pcbase S‖ : ℝ) : ℂ) - ((c : ℝ) : ℂ) :=
    Complex.ofReal_sub _ _
  rw [h, sub_mul, ← hb]

theorem pcnorm_base_sub (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} :
    ‖pcbase S - (c : ℂ) * pccutDir S‖ = |‖pcbase S‖ - c| := by
  rw [pcnorm_base_sub_smul S, norm_mul, pcnorm_cutDir S, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- The parameter of the *outer* endpoint of the second cut. -/
theorem pcsphere_param_sub (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {s : ℝ} (hs : 0 < s)
    (h : pcbase S - (s : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1) :
    s - ‖pcbase S‖ = 1 := by
  have h1 : ‖pcbase S - (s : ℂ) * pccutDir S‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using h
  rw [pcnorm_base_sub S] at h1
  have hb : ‖pcbase S‖ < 1 := pcnorm_base_lt_one S hball
  have h2 : (‖pcbase S‖ - s) ^ 2 = 1 := by
    rw [sq, ← abs_mul_abs_self, h1]; norm_num
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · linarith
  · linarith

/-- On the ray from the pcbase point in the direction `pccutDir`, a point whose parameter is `≥ t₁`
scales to `x`; a point of the cut forces that parameter below `t₁`. -/
theorem pcray_param_lt (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ : ℝ} (ht₁ : 0 < t₁) (hs₁pos : 0 < s₁)
    (hsph₁ : pcbase S + (s₁ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    {x : ℂ} (hxball : x ∈ Metric.closedBall (0 : ℂ) 1) (hxC : x ∉ pccut₁ S t₁ s₁)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {t : ℝ} (ht : t₁ ≤ t)
    (h : (σ : ℂ) * (x - pcbase S) = (t : ℂ) * pccutDir S) : t < t₁ := by
  have hσne : σ ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, zero_mul] at h
    have ht0 : (t : ℂ) * pccutDir S = 0 := h.symm
    rcases mul_eq_zero.mp ht0 with h' | h'
    · exact absurd (Complex.ofReal_eq_zero.mp h') (by linarith : t ≠ 0)
    · exact absurd h' (pccutDir_ne_zero S)
  have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσne)
  have hxc : x = pcbase S + (((t / σ : ℝ)) : ℂ) * pccutDir S := by
    have h2 : x - pcbase S = (σ : ℂ)⁻¹ * ((t : ℂ) * pccutDir S) := by
      rw [← h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hσne), one_mul]
    have h3 : (((t / σ : ℝ)) : ℂ) = (σ : ℂ)⁻¹ * (t : ℂ) := by push_cast; field_simp
    have h4 : x - pcbase S = (((t / σ : ℝ)) : ℂ) * pccutDir S := by rw [h3, mul_assoc, ← h2]
    rw [sub_eq_iff_eq_add] at h4
    rw [h4, add_comm]
  have hnorm : ‖pcbase S‖ + t / σ ≤ 1 := by
    have h1 : ‖pcbase S + (((t / σ : ℝ)) : ℂ) * pccutDir S‖ ≤ 1 := by
      rw [← hxc]; simpa [Metric.mem_closedBall, dist_zero_right] using hxball
    rwa [pcnorm_base_add S (div_pos (lt_of_lt_of_le ht₁ ht) hσpos).le] at h1
  have hs₁ : ‖pcbase S‖ + s₁ = 1 := pcsphere_param S hs₁pos hsph₁
  have hle : t / σ ≤ s₁ := by linarith
  have hlt : t / σ < t₁ := by
    by_contra hcon2
    push_neg at hcon2
    exact hxC ⟨t / σ, ⟨hcon2, hle⟩, by rw [hxc]⟩
  have hσt : t = σ * (t / σ) := by field_simp
  nlinarith [hσpos, hσ1, hlt, hσt]

/-- The same on the ray in the direction `-pccutDir`. -/
theorem pcray_param_lt_neg (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₂ s₂ : ℝ} (ht₂ : 0 < t₂) (hs₂pos : 0 < s₂)
    (hsph₂ : pcbase S - (s₂ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    {x : ℂ} (hxball : x ∈ Metric.closedBall (0 : ℂ) 1) (hxC : x ∉ pccut₂ S t₂ s₂)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {t : ℝ} (ht : t₂ ≤ t)
    (h : (σ : ℂ) * (x - pcbase S) = -((t : ℂ) * pccutDir S)) : t < t₂ := by
  have hσne : σ ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, zero_mul] at h
    have ht0 : -((t : ℂ) * pccutDir S) = 0 := h.symm
    rw [neg_eq_zero] at ht0
    rcases mul_eq_zero.mp ht0 with h' | h'
    · exact absurd (Complex.ofReal_eq_zero.mp h') (by linarith : t ≠ 0)
    · exact absurd h' (pccutDir_ne_zero S)
  have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσne)
  have hxc : x = pcbase S - (((t / σ : ℝ)) : ℂ) * pccutDir S := by
    have h2 : x - pcbase S = (σ : ℂ)⁻¹ * (-((t : ℂ) * pccutDir S)) := by
      rw [← h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hσne), one_mul]
    have h3 : (((t / σ : ℝ)) : ℂ) = (σ : ℂ)⁻¹ * (t : ℂ) := by push_cast; field_simp
    have h4 : x - pcbase S = -((((t / σ : ℝ)) : ℂ) * pccutDir S) := by
      calc x - pcbase S = (σ : ℂ)⁻¹ * (-((t : ℂ) * pccutDir S)) := h2
        _ = -((σ : ℂ)⁻¹ * ((t : ℂ) * pccutDir S)) := by rw [mul_neg]
        _ = -(((σ : ℂ)⁻¹ * (t : ℂ)) * pccutDir S) := by rw [mul_assoc]
        _ = -((((t / σ : ℝ)) : ℂ) * pccutDir S) := by rw [← h3]
    rw [sub_eq_iff_eq_add] at h4
    rw [h4]; ring
  have hnorm : |‖pcbase S‖ - t / σ| ≤ 1 := by
    have h1 : ‖pcbase S - (((t / σ : ℝ)) : ℂ) * pccutDir S‖ ≤ 1 := by
      rw [← hxc]; simpa [Metric.mem_closedBall, dist_zero_right] using hxball
    rwa [pcnorm_base_sub S] at h1
  have hs₂ : s₂ - ‖pcbase S‖ = 1 := pcsphere_param_sub S hball hs₂pos hsph₂
  have hle : t / σ ≤ s₂ := by
    have h1 : -(1 : ℝ) ≤ ‖pcbase S‖ - t / σ := by
      linarith [neg_abs_le (‖pcbase S‖ - t / σ), hnorm]
    linarith
  have hlt : t / σ < t₂ := by
    by_contra hcon2
    push_neg at hcon2
    exact hxC ⟨t / σ, ⟨hcon2, hle⟩, by rw [hxc]⟩
  have hσt : t = σ * (t / σ) := by field_simp
  nlinarith [hσpos, hσ1, hlt, hσt]

/-- **Inward reachability in the cut pcannulus.**  Every point of the cut pcannulus is joined, inside
the cut pcannulus, to a point of the trace of `γ` off the two pccuts. -/
theorem pcannulusCut_reach_inner {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hsph₁ : pcbase S + (s₁ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (hsph₂ : pcbase S - (s₂ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (hb₁ : ∀ σ : ℝ, t₁ < σ → pcbase S + (σ : ℂ) * pccutDir S ∉ closure S.V)
    (hb₂ : ∀ σ : ℝ, t₂ < σ → pcbase S - (σ : ℂ) * pccutDir S ∉ closure S.V)
    {x : ℂ} (hx : x ∈ pcannulusCut S t₁ s₁ t₂ s₂) :
    ∃ y : ℂ, y ∈ γ.trace ∧ y ∉ pccut₁ S t₁ s₁ ∧ y ∉ pccut₂ S t₂ s₂ ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (1 - τ) * y + τ * x ∈ pcannulusCut S t₁ s₁ t₂ s₂ := by
  obtain ⟨⟨hxball, hxV⟩, hxcut⟩ := hx
  have hxcut₁ : x ∉ pccut₁ S t₁ s₁ := fun h => hxcut (Or.inl h)
  have hxcut₂ : x ∉ pccut₂ S t₂ s₂ := fun h => hxcut (Or.inr h)
  have hw : x - pcbase S ≠ 0 := by
    intro h
    exact hxV (by rw [sub_eq_zero.mp h]; exact pcbase_mem_V S)
  set T : Set ℝ := {σ : ℝ | 0 ≤ σ ∧ σ ≤ 1 ∧ pcsegPt S x σ ∈ closure S.V} with hTdef
  have hTne : T.Nonempty :=
    ⟨0, le_rfl, zero_le_one, by rw [pcsegPt_zero]; exact subset_closure (pcbase_mem_V S)⟩
  have hTbdd : BddAbove T := ⟨1, fun σ hσ => hσ.2.1⟩
  have hTcl : IsClosed T := by
    have he : T = Set.Icc (0 : ℝ) 1 ∩ {σ : ℝ | pcsegPt S x σ ∈ closure S.V} := by
      ext σ; constructor
      · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, h2⟩
      · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, h2⟩
    rw [he]
    exact IsClosed.inter isClosed_Icc (isClosed_closure.preimage (pccontinuous_segPt S x))
  set σ₁ : ℝ := sSup T with hσ₁def
  have hσ₁T : σ₁ ∈ T := hTcl.csSup_mem hTne hTbdd
  obtain ⟨hσ₁0, hσ₁1, hσ₁K⟩ := hσ₁T
  set y : ℂ := pcsegPt S x σ₁ with hydef
  have hyK : y ∈ closure S.V := hσ₁K
  have hyV : y ∉ S.V := by
    intro hyV'
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds hyV')
    rcases lt_or_eq_of_le hσ₁1 with hlt | heq
    · set δ : ℝ := min ((1 - σ₁) / 2) (ε / (2 * ‖x - pcbase S‖)) with hδdef
      have hδ : 0 < δ := by rw [hδdef]; apply lt_min <;> positivity
      have hδ1 : σ₁ + δ ≤ 1 := by
        have h := min_le_left ((1 - σ₁) / 2) (ε / (2 * ‖x - pcbase S‖))
        rw [← hδdef] at h; linarith
      have hδε : δ * ‖x - pcbase S‖ < ε := by
        have h2 := min_le_right ((1 - σ₁) / 2) (ε / (2 * ‖x - pcbase S‖))
        rw [← hδdef] at h2
        have hpos : 0 < ‖x - pcbase S‖ := norm_pos_iff.mpr hw
        have h3 : (ε / (2 * ‖x - pcbase S‖)) * ‖x - pcbase S‖ = ε / 2 := by
          field_simp
        have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (x - pcbase S))
        rw [h3] at h4
        linarith
      have e : pcsegPt S x (σ₁ + δ) - pcsegPt S x σ₁ = ((δ : ℝ) : ℂ) * (x - pcbase S) := by
        unfold pcsegPt; push_cast; ring
      have hmem : pcsegPt S x (σ₁ + δ) ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm, hydef, e, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hδ.le]
        exact hδε
      have hσT : σ₁ + δ ∈ T := ⟨by linarith, hδ1, subset_closure (hεV hmem)⟩
      have hle := le_csSup hTbdd hσT
      rw [← hσ₁def] at hle
      linarith
    · have h1 : σ₁ = 1 := heq
      have hyx : y = x := by rw [hydef, h1, pcsegPt_one]
      have : x ∈ S.V := by rw [← hyx]; exact hyV'
      exact hxV this
  have hyΓ : y ∈ γ.trace := by
    have h := hyK; rw [pcclosure_V_eq S] at h
    rcases h with h | h
    · exact absurd h hyV
    · exact h
  -- `y ∉ pccut₁`
  have hyc₁ : y ∉ pccut₁ S t₁ s₁ := by
    rintro ⟨t, ht, hy⟩
    have hrel : (σ₁ : ℂ) * (x - pcbase S) = (t : ℂ) * pccutDir S := by
      have h := pcsegPt_sub S x σ₁
      rw [← hydef, hy] at h
      rw [add_sub_cancel_left] at h
      exact h.symm
    have := pcray_param_lt S hball ht₁ (by linarith) hsph₁ hxball hxcut₁ hσ₁0 hσ₁1 ht.1 hrel
    linarith [ht.1]
  have hyc₂ : y ∉ pccut₂ S t₂ s₂ := by
    rintro ⟨t, ht, hy⟩
    have hrel : (σ₁ : ℂ) * (x - pcbase S) = -((t : ℂ) * pccutDir S) := by
      have h := pcsegPt_sub S x σ₁
      rw [← hydef, hy] at h
      rw [show (pcbase S - (t : ℂ) * pccutDir S) - pcbase S = -((t : ℂ) * pccutDir S) by ring] at h
      exact h.symm
    have := pcray_param_lt_neg S hball ht₂ (by linarith) hsph₂ hxball hxcut₂ hσ₁0 hσ₁1 ht.1 hrel
    linarith [ht.1]
  refine ⟨y, hyΓ, hyc₁, hyc₂, ?_⟩
  intro τ hτ0 hτ1
  have hpt : (1 - τ) * y + τ * x = pcsegPt S x (σ₁ + τ * (1 - σ₁)) := by
    rw [hydef, ← pcsegPt_affine S x]
  set σ : ℝ := σ₁ + τ * (1 - σ₁) with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; nlinarith
  have hσ1 : σ ≤ 1 := by rw [hσdef]; nlinarith
  have hyb : ‖y‖ ≤ 1 := by
    have h := pcclosure_V_subset_openBall S hball hyK
    simp only [Set.mem_setOf_eq] at h
    linarith
  have hxb : ‖x‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxball
    exact hxball
  rw [hpt]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, ← hpt]
    calc ‖(1 - τ) * y + τ * x‖ ≤ ‖(1 - τ) * y‖ + ‖τ * x‖ := norm_add_le _ _
      _ = (1 - τ) * ‖y‖ + τ * ‖x‖ := by
          have h1 : ‖((1 - τ : ℝ) : ℂ)‖ = 1 - τ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          have h2 : ‖((τ : ℝ) : ℂ)‖ = τ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
          rw [norm_mul, norm_mul,
            show ((1 : ℂ) - (τ : ℂ)) = ((1 - τ : ℝ) : ℂ) by push_cast; ring, h1, h2]
      _ ≤ 1 := by nlinarith
  · intro hmem
    rcases eq_or_lt_of_le (by rw [hσdef]; nlinarith : σ₁ ≤ σ) with heq | hlt
    · rw [← heq, ← hydef] at hmem; exact hyV hmem
    · have : σ ∈ T := ⟨hσ0, hσ1, subset_closure hmem⟩
      have hle := le_csSup hTbdd this
      rw [← hσ₁def] at hle
      linarith
  · rintro (h1 | h2)
    · obtain ⟨t, ht, htz⟩ := h1
      have hrel : (σ : ℂ) * (x - pcbase S) = (t : ℂ) * pccutDir S := by
        have h := pcsegPt_sub S x σ
        rw [htz] at h
        rw [add_sub_cancel_left] at h
        exact h.symm
      have := pcray_param_lt S hball ht₁ (by linarith) hsph₁ hxball hxcut₁ hσ0 hσ1 ht.1 hrel
      linarith [ht.1]
    · obtain ⟨t, ht, htz⟩ := h2
      have hrel : (σ : ℂ) * (x - pcbase S) = -((t : ℂ) * pccutDir S) := by
        have h := pcsegPt_sub S x σ
        rw [htz] at h
        rw [show (pcbase S - (t : ℂ) * pccutDir S) - pcbase S = -((t : ℂ) * pccutDir S) by ring] at h
        exact h.symm
      have := pcray_param_lt_neg S hball ht₂ (by linarith) hsph₂ hxball hxcut₂ hσ0 hσ1 ht.1 hrel
      linarith [ht.1]

end

end TwoCutsReach



/-!
## Side lemmas for the two-pccuts tiling

The four-arc curves of the cut-and-paste have trace contained in

`∂𝔻 ∪ γ.trace ∪ pccut₁ ∪ pccut₂`;

none of these parts meets the open bounded side `S.V`, so `S.V` is disjoint from both four-arc
curves and `plane_separation_preconnected_subset` puts it on one side of each of them.  The lemmas
below establish the three disjointness facts (`∂𝔻`, `γ.trace` and the pccuts against `S.V`).
-/

section TwoCutsSides

open Set

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The trace of the curve does not meet the open bounded side. -/
theorem pctrace_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ}
    (hz : z ∈ γ.trace) : z ∉ S.V := by
  intro hzV
  have hsub : S.V ⊆ γ.traceᶜ := by
    rw [← S.union_eq]; exact subset_union_right
  exact hsub hzV hz

/-- Points of the boundary circle do not lie in the open bounded side: the latter is contained in
the *open* unit disc (`pcclosure_V_subset_openBall`). -/
theorem pcnorm_one_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) : z ∉ S.V := by
  intro hzV
  have h1 : ‖z‖ < 1 := pcclosure_V_subset_openBall S hball (subset_closure hzV)
  rw [hz] at h1
  exact lt_irrefl 1 h1

/-- **The first crosscut does not meet the open bounded side.** -/
theorem pccut₁_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ : ℝ}
    (ha₁ : (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S ∈ γ.trace)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (pcbase S : ℂ) + (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V) :
    ∀ z ∈ pccut₁ S t₁ s₁, z ∉ S.V := by
  rintro z ⟨σ, hσ, rfl⟩
  rcases lt_or_eq_of_le hσ.1 with h1 | h1
  · rcases lt_or_eq_of_le hσ.2 with h2 | h2
    · exact (hseg₁ σ h1 h2).2
    · rw [h2]
      exact pcnorm_one_notMem_V S hball (by rw [hb₁]; exact pcnorm_cutDir S)
  · rw [← h1]
    exact pctrace_notMem_V S ha₁

/-- **The second crosscut does not meet the open bounded side.** -/
theorem pccut₂_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₂ s₂ : ℝ}
    (ha₂ : (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S ∈ γ.trace)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (pcbase S : ℂ) - (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V) :
    ∀ z ∈ pccut₂ S t₂ s₂, z ∉ S.V := by
  rintro z ⟨σ, hσ, rfl⟩
  rcases lt_or_eq_of_le hσ.1 with h1 | h1
  · rcases lt_or_eq_of_le hσ.2 with h2 | h2
    · exact (hseg₂ σ h1 h2).2
    · rw [h2]
      refine pcnorm_one_notMem_V S hball ?_
      rw [hb₂, norm_neg, pcnorm_cutDir S]
  · rw [← h1]
    exact pctrace_notMem_V S ha₂

end TwoCutsSides


/-!
## The two-pccuts tiling: the next layer (statements)

These are the two lemmas that turn the side lemmas above into the tiling.  They are stated with the
Schoenflies datum `T` of the four-arc curve supplied as an argument (the existence of `T` is
`h` applied to the curve, whose simplicity is `Work.SphereJordan.pctgtUpPC_isSimple`).
-/

section TwoCutsTilingStatements

open Set

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **The open bounded side of `γ` avoids the trace of the upper four-arc curve.**
Immediate from the description of `pctgtUpB` (outer semicircle / second cut / γ-arc / first cut) and
the four side lemmas above. -/
theorem pctgtUpB_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ha₁ : (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S ∈ γ.trace)
    (ha₂ : (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S ∈ γ.trace)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (pcbase S : ℂ) + (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (pcbase S : ℂ) - (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ ∉ S.V := by
  have hpm := Work.SphereJordan.pcperPt_mem τ
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Work.Smooth.SphereJordan.pctgtUpB]
  by_cases h1 : pcperPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    refine pcnorm_one_notMem_V S hball ?_
    rw [pcsrcOuterUp, norm_mul, pcnorm_cutDir S, one_mul, Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : pcperPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (pcperPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (pcperPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      refine pccut₂_notMem_V S hball ha₂ hb₂ hseg₂ _
        ⟨s₂ + ((pcperPt τ - Real.pi / 2) / (Real.pi / 2)) * (t₂ - s₂), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂)
          (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - Real.pi / 2) / (Real.pi / 2))]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₂ - s₂ ≤ 0)]
      · simp only [pctgtCut₂]
    · rw [if_neg h2]
      by_cases h3 : pcperPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact pctrace_notMem_V S ⟨_, rfl⟩
      · rw [if_neg h3]
        have hx0 : 0 ≤ (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        refine pccut₁_notMem_V S hball ha₁ hb₁ hseg₁ _
          ⟨s₁ + (1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2)) * (t₁ - s₁),
            ⟨?_, ?_⟩, ?_⟩
        · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0]
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : t₁ - s₁ ≤ 0)
            (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]
        · simp only [pctgtCut₁]

/-- **The open bounded side of `γ` avoids the trace of the lower four-arc curve.** -/
theorem pctgtDnB_notMem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ha₁ : (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S ∈ γ.trace)
    (ha₂ : (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S ∈ γ.trace)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (pcbase S : ℂ) + (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (pcbase S : ℂ) - (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ ∉ S.V := by
  have hpm := Work.SphereJordan.pcperPt_mem τ
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Work.Smooth.SphereJordan.pctgtDnB]
  by_cases h1 : pcperPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    refine pcnorm_one_notMem_V S hball ?_
    rw [pcsrcOuterDn, norm_mul, norm_neg, pcnorm_cutDir S, one_mul, Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : pcperPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (pcperPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (pcperPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      refine pccut₁_notMem_V S hball ha₁ hb₁ hseg₁ _
        ⟨s₁ + ((pcperPt τ - Real.pi / 2) / (Real.pi / 2)) * (t₁ - s₁), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₁ - s₁ ≤ 0)]
      · simp only [pctgtCut₁]
    · rw [if_neg h2]
      by_cases h3 : pcperPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact pctrace_notMem_V S ⟨_, rfl⟩
      · rw [if_neg h3]
        have hx0 : 0 ≤ (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        refine pccut₂_notMem_V S hball ha₂ hb₂ hseg₂ _
          ⟨s₂ + (1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2)) * (t₂ - s₂),
            ⟨?_, ?_⟩, ?_⟩
        · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂) hx0]
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : t₂ - s₂ ≤ 0)
            (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]
        · simp only [pctgtCut₂]

/-- **The upper four-arc curve lies in the closed unit disc.**  Case analysis over the four arcs:
the outer semicircle has norm `1`; the two pccuts have `(tᵢ,sᵢ)`-parameters, hence norms
`‖pcbase S‖ + σ ≤ ‖pcbase S‖ + s₁ = 1` and `|‖pcbase S‖ - σ| ≤ 1`; the `γ`-arc has norm `< 1`. -/
theorem pctgtUpB_norm_le_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    ‖Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ‖ ≤ 1 := by
  have hpm := Work.SphereJordan.pcperPt_mem τ
  have hb : ‖(pcbase S : ℂ)‖ < 1 := pcnorm_base_lt_one S hball
  have hnorm₁ : ‖(pcbase S : ℂ)‖ + s₁ = 1 := by
    have h := pcnorm_base_add S (c := s₁) (by linarith)
    rw [hb₁, pcnorm_cutDir S] at h
    linarith
  have hnorm₂ : ‖(pcbase S : ℂ)‖ - s₂ = -1 := by
    have h := pcnorm_base_sub_smul (S := S) (c := s₂)
    rw [hb₂] at h
    have h' : ((‖(pcbase S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
      have h2 := congrArg (fun z : ℂ => z / pccutDir S) h
      rw [mul_div_cancel_right₀ _ (pccutDir_ne_zero S), neg_div,
        div_self (pccutDir_ne_zero S)] at h2
      simpa using h2.symm
    exact_mod_cast h'
  rw [Work.Smooth.SphereJordan.pctgtUpB]
  by_cases h1 : pcperPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    rw [pcsrcOuterUp, norm_mul, pcnorm_cutDir S, one_mul, Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : pcperPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (pcperPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (pcperPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      rw [pctgtCut₂, pcnorm_base_sub, abs_le]
      refine ⟨?_, ?_⟩ <;>
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₂ - s₂ ≤ 0),
          mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂)
            (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - Real.pi / 2) / (Real.pi / 2))]
    · rw [if_neg h2]
      by_cases h3 : pcperPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact le_of_lt (hball _)
      · rw [if_neg h3]
        have hx0 : 0 ≤ (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        rw [pctgtCut₁, pcnorm_base_add]
        · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
            mul_nonpos_of_nonpos_of_nonneg (by linarith : t₁ - s₁ ≤ 0)
              (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]
        · nlinarith

/-- **The lower four-arc curve lies in the closed unit disc** (same case analysis). -/
theorem pctgtDnB_norm_le_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    ‖Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ‖ ≤ 1 := by
  have hpm := Work.SphereJordan.pcperPt_mem τ
  have hb : ‖(pcbase S : ℂ)‖ < 1 := pcnorm_base_lt_one S hball
  have hnorm₁ : ‖(pcbase S : ℂ)‖ + s₁ = 1 := by
    have h := pcnorm_base_add S (c := s₁) (by linarith)
    rw [hb₁, pcnorm_cutDir S] at h
    linarith
  have hnorm₂ : ‖(pcbase S : ℂ)‖ - s₂ = -1 := by
    have h := pcnorm_base_sub_smul (S := S) (c := s₂)
    rw [hb₂] at h
    have h' : ((‖(pcbase S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
      have h2 := congrArg (fun z : ℂ => z / pccutDir S) h
      rw [mul_div_cancel_right₀ _ (pccutDir_ne_zero S), neg_div,
        div_self (pccutDir_ne_zero S)] at h2
      simpa using h2.symm
    exact_mod_cast h'
  rw [Work.Smooth.SphereJordan.pctgtDnB]
  by_cases h1 : pcperPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    rw [pcsrcOuterDn, norm_mul, norm_neg, pcnorm_cutDir S, one_mul,
      Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : pcperPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (pcperPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (pcperPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      rw [pctgtCut₁, pcnorm_base_add]
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₁ - s₁ ≤ 0)]
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₁ - s₁ ≤ 0)]
    · rw [if_neg h2]
      by_cases h3 : pcperPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact le_of_lt (hball _)
      · rw [if_neg h3]
        have hx0 : 0 ≤ (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        rw [pctgtCut₂, pcnorm_base_sub, abs_le]
        refine ⟨?_, ?_⟩ <;>
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂) hx0,
            mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₂ - s₂ ≤ 0),
            mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂)
              (by linarith : (0:ℝ) ≤ 1 - (pcperPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]

/-- **The bounded side of an upper four-arc curve lies in the pcannulus `pcannulus S`.**
It lies in the closed unit disc (the trace is in the closed unit disc by `pctgtUpB_norm_le_one` and
`pcplaneSeparation_V_subset_closedBall'`) and is disjoint from `S.V` by the hypothesis. -/
theorem pcupCurve_V_subset_annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcannulus S := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have hcl : T.V ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Work.Smooth.SphereJordan.pcplaneSeparation_V_subset_closedBall' T.toPlaneSeparation (by
        rintro _ ⟨τ, rfl⟩
        simpa using pctgtUpB_norm_le_one S hball hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ b θ₁ θ₂ τ)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hcl hx
  · intro hxV
    exact Set.disjoint_left.mp T.disjoint_UV (hVU hxV) hx

/-- **The bounded side of a lower four-arc curve lies in the pcannulus `pcannulus S`.** -/
theorem pcdnCurve_V_subset_annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcannulus S := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have hcl : T.V ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Work.Smooth.SphereJordan.pcplaneSeparation_V_subset_closedBall' T.toPlaneSeparation (by
        rintro _ ⟨τ, rfl⟩
        simpa using pctgtDnB_norm_le_one S hball hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ b θ₁ θ₂ τ)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hcl hx
  · intro hxV
    exact Set.disjoint_left.mp T.disjoint_UV (hVU hxV) hx

/-- `pcperPt` is the identity on one period `[0, 2π)`. -/
theorem pcperPt_eq_self {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ < 2 * Real.pi) : pcperPt τ = τ := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hf : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h0 hpos.le, by rw [div_lt_one hpos]; exact h2⟩
  unfold pcperPt
  rw [hf]
  norm_num

/-- **Both crosscuts are contained in the trace of the upper four-arc curve.**
For `σ ∈ [t₁,s₁]`, the witness is `τ = 3π/2 + ((σ-t₁)/(s₁-t₁))·(π/2)` (the second half of the third
and the fourth branch of `pctgtUpB`); for `σ ∈ [t₂,s₂]` the witness is
`τ = π/2 + ((s₂-σ)/(s₂-t₂))·(π/2)` (the second branch, through `pctgtCut₂`). -/
theorem pccuts_subset_trace_up (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S) :
    Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂ ⊆
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).trace := by
  have hpi : 0 < Real.pi := Real.pi_pos
  intro z hz
  rcases hz with hz | hz
  · -- first crosscut: z = pcbase S + σ u, σ ∈ [t₁,s₁]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.1 with hσt | hσt
    · -- σ = t₁ : witness 3π/2, on the γ-arc endpoint a₁
      refine ⟨3 * Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2)
        = (pcbase S : ℂ) + (σ : ℂ) * pccutDir S
      have hper : pcperPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
        pcperPt_eq_self (by positivity) (by linarith [hpi])
      have hcoef : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
        field_simp
        ring
      rw [Work.Smooth.SphereJordan.pctgtUpB, hper,
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl, hcoef,
        ← hσt]
      split_ifs with hb
      · rw [show θ₂ + 1 * (θ₁ - θ₂) = θ₁ by ring, hθ₁]
      · rw [show θ₂ + 1 * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ - 2 * Real.pi by ring]
        rw [show γ.γ (θ₁ - 2 * Real.pi) = γ.γ θ₁ from by
          have h := γ.periodic (θ₁ - 2 * Real.pi)
          rw [show θ₁ - 2 * Real.pi + 2 * Real.pi = θ₁ by ring] at h
          exact h.symm]
        rw [hθ₁]
    · rcases eq_or_lt_of_le hσ.2 with hσs | hσs
      · -- σ = s₁ : witness 2π, on the outer semicircle start u
        refine ⟨2 * Real.pi, ?_⟩
        show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi)
          = (pcbase S : ℂ) + (σ : ℂ) * pccutDir S
        have hper : pcperPt (2 * Real.pi) = 0 := by
          have h := Work.Smooth.SphereJordan.pcperPt_shift (0 : ℝ)
          rw [show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h
          rw [h, pcperPt_eq_self (le_refl 0) (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [Work.Smooth.SphereJordan.pctgtUpB, hper,
          if_pos (by positivity : (0 : ℝ) ≤ Real.pi / 2), zero_div,
          Work.Smooth.SphereJordan.pcsrcOuterUp, mul_zero, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, mul_one, hσs, hb₁]
      · -- t₁ < σ < s₁ : witness 3π/2 + ((σ-t₁)/(s₁-t₁))·(π/2), fourth branch
        refine ⟨3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2), ?_⟩
        show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
            (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2))
          = (pcbase S : ℂ) + (σ : ℂ) * pccutDir S
        have hy0 : 0 < (σ - t₁) / (s₁ - t₁) := by apply div_pos <;> linarith
        have hy1 : (σ - t₁) / (s₁ - t₁) < 1 := by
          rw [div_lt_one (by linarith)]; linarith [hσs]
        have hper : pcperPt (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2))
            = 3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) :=
          pcperPt_eq_self (by positivity) (by nlinarith [hpi])
        rw [Work.Smooth.SphereJordan.pctgtUpB, hper,
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ Real.pi / 2)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ Real.pi)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ 3 * Real.pi / 2)),
          Work.Smooth.SphereJordan.pctgtCut₁,
          show (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) - 3 * Real.pi / 2)
              / (Real.pi / 2) = (σ - t₁) / (s₁ - t₁) by
            rw [show 3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) - 3 * Real.pi / 2
              = ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) by ring]
            exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
        have hst : s₁ - t₁ ≠ 0 := by linarith
        congr 1
        congr 1
        rw [Complex.ofReal_inj]
        field_simp
        ring
  · -- second crosscut: z = pcbase S - σ u, σ ∈ [t₂,s₂]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.2 with hσs | hσs
    · -- σ = s₂ : witness π/2, on the outer semicircle end -u
      refine ⟨Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2)
        = (pcbase S : ℂ) - (σ : ℂ) * pccutDir S
      have hper : pcperPt (Real.pi / 2) = Real.pi / 2 :=
        pcperPt_eq_self (by positivity) (by linarith [hpi])
      rw [Work.Smooth.SphereJordan.pctgtUpB, hper, if_pos le_rfl,
        div_self (by positivity : (Real.pi / 2) ≠ 0), Work.Smooth.SphereJordan.pcsrcOuterUp,
        mul_one, Complex.exp_pi_mul_I, mul_neg, mul_one, hσs, hb₂]
    · -- σ < s₂ : witness π/2 + ((s₂-σ)/(s₂-t₂))·(π/2), second branch
      refine ⟨Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2), ?_⟩
      show Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
          (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2))
        = (pcbase S : ℂ) - (σ : ℂ) * pccutDir S
      have hx0 : 0 < (s₂ - σ) / (s₂ - t₂) := by apply div_pos <;> linarith
      have hx1 : (s₂ - σ) / (s₂ - t₂) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [hσ.1]
      have hper : pcperPt (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2))
          = Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) :=
        pcperPt_eq_self (by positivity) (by nlinarith [hpi])
      rw [Work.Smooth.SphereJordan.pctgtUpB, hper,
        if_neg (by nlinarith [hpi, hx0] : ¬ (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2)
            ≤ Real.pi / 2)),
        if_pos (by nlinarith [hpi, hx1] : Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2)
            ≤ Real.pi),
        Work.Smooth.SphereJordan.pctgtCut₂,
        show (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) - Real.pi / 2)
            / (Real.pi / 2) = (s₂ - σ) / (s₂ - t₂) by
          rw [show Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) - Real.pi / 2
            = ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) by ring]
          exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
      have hst : s₂ - t₂ ≠ 0 := by linarith
      congr 1
      congr 1
      rw [Complex.ofReal_inj]
      field_simp
      ring

/-- **The same for the lower four-arc curve** (the third/fourth branches are swapped). -/
theorem pccuts_subset_trace_dn (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S) :
    Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂ ⊆
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).trace := by
  have hpi : 0 < Real.pi := Real.pi_pos
  intro z hz
  rcases hz with hz | hz
  · -- z = pcbase S + σ u, σ ∈ [t₁,s₁]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.2 with hσs | hσs
    · -- σ = s₁ : the first branch, `pcsrcOuterDn S 1 = pccutDir S`
      refine ⟨Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2)
        = (pcbase S : ℂ) + (σ : ℂ) * pccutDir S
      have hper : pcperPt (Real.pi / 2) = Real.pi / 2 :=
        pcperPt_eq_self (by positivity) (by linarith [hpi])
      rw [Work.Smooth.SphereJordan.pctgtDnB, hper, if_pos le_rfl,
        div_self (by positivity : (Real.pi / 2) ≠ 0), Work.Smooth.SphereJordan.pcsrcOuterDn,
        show (Real.pi * 1 : ℝ) = Real.pi by ring, Complex.exp_pi_mul_I,
        show -pccutDir S * (-1) = pccutDir S by ring, hσs, hb₁]
    · -- t₁ ≤ σ < s₁ : the second branch at π/2 + x·(π/2), x = (s₁-σ)/(s₁-t₁)
      refine ⟨Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2), ?_⟩
      show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
          (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2))
        = (pcbase S : ℂ) + (σ : ℂ) * pccutDir S
      have hx0 : 0 < (s₁ - σ) / (s₁ - t₁) :=
        div_pos (by linarith [hσs]) (by linarith [hts₁])
      have hx1 : (s₁ - σ) / (s₁ - t₁) ≤ 1 := by
        rw [div_le_one (by linarith [hts₁])]; linarith [hσ.1]
      have hper : pcperPt (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2))
          = Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) :=
        pcperPt_eq_self (by positivity) (by nlinarith [hpi])
      rw [Work.Smooth.SphereJordan.pctgtDnB, hper,
        if_neg (by nlinarith [hpi, hx0] : ¬ (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2)
            ≤ Real.pi / 2)),
        if_pos (by nlinarith [hpi, hx1] : Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2)
            ≤ Real.pi),
        Work.Smooth.SphereJordan.pctgtCut₁,
        show (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) - Real.pi / 2)
            / (Real.pi / 2) = (s₁ - σ) / (s₁ - t₁) by
          rw [show Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) - Real.pi / 2
            = ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) by ring]
          exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
      have hst : s₁ - t₁ ≠ 0 := by linarith
      congr 1
      congr 1
      rw [Complex.ofReal_inj]
      field_simp
      ring
  · -- z = pcbase S - σ u, σ ∈ [t₂,s₂]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.1 with hσt | hσt
    · -- σ = t₂ : the third (γ-arc) branch with coefficient 1 lands on γ.γ θ₂ = a₂
      refine ⟨3 * Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2)
        = (pcbase S : ℂ) - (σ : ℂ) * pccutDir S
      have hper : pcperPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
        pcperPt_eq_self (by positivity) (by linarith [hpi])
      have hcoef : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
        field_simp
        ring
      rw [Work.Smooth.SphereJordan.pctgtDnB, hper,
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl, hcoef]
      split_ifs with hb
      · rw [show θ₁ - 2 * Real.pi + 1 * (θ₂ - θ₁ + 2 * Real.pi) = θ₂ by ring, hθ₂, hσt]
      · rw [show θ₁ + 1 * (θ₂ - θ₁) = θ₂ by ring, hθ₂, hσt]
    · rcases eq_or_lt_of_le hσ.2 with hσs | hσs
      · -- σ = s₂ : the first branch, `pcsrcOuterDn S 0 = -pccutDir S`
        refine ⟨2 * Real.pi, ?_⟩
        show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi)
          = (pcbase S : ℂ) - (σ : ℂ) * pccutDir S
        have hper : pcperPt (2 * Real.pi) = 0 := by
          have h := Work.Smooth.SphereJordan.pcperPt_shift (0 : ℝ)
          rw [show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h
          rw [h, pcperPt_eq_self (le_refl 0) (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [Work.Smooth.SphereJordan.pctgtDnB, hper,
          if_pos (by positivity : (0 : ℝ) ≤ Real.pi / 2), zero_div,
          Work.Smooth.SphereJordan.pcsrcOuterDn,
          show (Real.pi * 0 : ℝ) = 0 by ring, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, mul_one, hσs, hb₂]
      · -- t₂ < σ < s₂ : the fourth branch at 3π/2 + ((σ-t₂)/(s₂-t₂))·(π/2)
        refine ⟨3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2), ?_⟩
        show Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
            (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2))
          = (pcbase S : ℂ) - (σ : ℂ) * pccutDir S
        have hy0 : 0 < (σ - t₂) / (s₂ - t₂) :=
          div_pos (by linarith [hσt]) (by linarith [hts₂])
        have hy1 : (σ - t₂) / (s₂ - t₂) < 1 := by
          rw [div_lt_one (by linarith [hts₂])]; linarith [hσs]
        have hper : pcperPt (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2))
            = 3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) :=
          pcperPt_eq_self (by positivity) (by nlinarith [hpi])
        rw [Work.Smooth.SphereJordan.pctgtDnB, hper,
          if_neg (by nlinarith [hpi] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ Real.pi / 2)),
          if_neg (by nlinarith [hpi] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ Real.pi)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ 3 * Real.pi / 2)),
          Work.Smooth.SphereJordan.pctgtCut₂,
          show 1 - (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) - 3 * Real.pi / 2)
              / (Real.pi / 2) = (s₂ - σ) / (s₂ - t₂) by
            rw [show 3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) - 3 * Real.pi / 2
              = ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) by ring]
            rw [mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
            have hst : s₂ - t₂ ≠ 0 := by linarith
            field_simp
            ring]
        have hst : s₂ - t₂ ≠ 0 := by linarith
        congr 1
        congr 1
        rw [Complex.ofReal_inj]
        field_simp
        ring

/-- **The bounded side of an upper four-arc curve lies in the cut pcannulus.**
`T.V ⊆ pcannulus S` and the pccuts are contained in the trace of the curve
(`pccuts_subset_trace_up`), while the sides avoid the trace. -/
theorem pcupCurve_V_subset_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  intro x hx
  refine ⟨pcupCurve_V_subset_annulus S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
    T hVU hx, ?_⟩
  intro hxcuts
  have hsub : T.V ⊆ (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂
      hout₁ hout₂ hθ₁ hθ₂).traceᶜ := by
    rw [← T.union_eq]; exact subset_union_right
  rcases hxcuts with hx1 | hx2
  · exact hsub hx (pccuts_subset_trace_up S hball b θ₁ θ₂ hb₁ hb₂ hts₁ hts₂ hout₁ hout₂ hθ₁ hθ₂
      (Or.inl hx1))
  · exact hsub hx (pccuts_subset_trace_up S hball b θ₁ θ₂ hb₁ hb₂ hts₁ hts₂ hout₁ hout₂ hθ₁ hθ₂
      (Or.inr hx2))

/-- **The bounded side of a lower four-arc curve lies in the cut pcannulus.** -/
theorem pcdnCurve_V_subset_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  intro x hx
  refine ⟨pcdnCurve_V_subset_annulus S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
    T hVU hx, ?_⟩
  intro hxcuts
  have hsub : T.V ⊆ (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂
      hout₁ hout₂ hθ₁ hθ₂).traceᶜ := by
    rw [← T.union_eq]; exact subset_union_right
  rcases hxcuts with hx1 | hx2
  · exact hsub hx (pccuts_subset_trace_dn S hball b θ₁ θ₂ hb₁ hb₂ hts₁ hts₂ hout₁ hout₂ hθ₁ hθ₂
      (Or.inl hx1))
  · exact hsub hx (pccuts_subset_trace_dn S hball b θ₁ θ₂ hb₁ hb₂ hts₁ hts₂ hout₁ hout₂ hθ₁ hθ₂
      (Or.inr hx2))

/-- **Step (i) of the identification, upper curve.**
The bounded side of an upper four-arc curve is preconnected, nonempty, and contained in
`pcannulusCut` (`pcupCurve_V_subset_annulusCut`), hence lies in the connected component of
`pcannulusCut` of any of its points. -/
theorem pcupCurve_V_subset_component (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    ∃ w ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂,
      T.V ⊆ connectedComponentIn (Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂) w := by
  obtain ⟨w, hw⟩ := T.nonempty_V
  refine ⟨w, pcupCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂
    hθ₁ hθ₂ T hVU hw, ?_⟩
  exact T.preconn_V.subset_connectedComponentIn hw
    (pcupCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
      T hVU)

/-- **Step (i) of the identification, lower curve.** -/
theorem pcdnCurve_V_subset_component (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    ∃ w ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂,
      T.V ⊆ connectedComponentIn (Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂) w := by
  obtain ⟨w, hw⟩ := T.nonempty_V
  refine ⟨w, pcdnCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂
    hθ₁ hθ₂ T hVU hw, ?_⟩
  exact T.preconn_V.subset_connectedComponentIn hw
    (pcdnCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
      T hVU)

/-- **(b): the crosscuts meet the boundary circle only at their outer endpoints `±pccutDir S`.**
A point of `pccut₁` has norm `‖pcbase S‖ + σ` and a point of `pccut₂` has norm `|‖pcbase S‖ - σ|`; a point
of norm `1` therefore has `σ = s₁` resp. `σ = s₂` (for the second cut, the alternative
`‖pcbase S‖ - σ = 1` would force `σ = ‖pcbase S‖ - 1 < 0`). -/
theorem pccut_inter_sphere_subset (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂) :
    ∀ z ∈ Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂,
      ‖z‖ = 1 → z ∈ ({pccutDir S, -pccutDir S} : Set ℂ) := by
  intro z hz hzn
  have hb : ‖(pcbase S : ℂ)‖ < 1 := pcnorm_base_lt_one S hball
  rcases hz with hz | hz
  · obtain ⟨σ, hσ, rfl⟩ := hz
    have h1 : ‖(pcbase S : ℂ)‖ + σ = 1 := by
      have h := pcnorm_base_add S (c := σ) (le_trans (le_of_lt ht₁) hσ.1)
      rw [hzn] at h
      linarith
    have h2 : ‖(pcbase S : ℂ)‖ + s₁ = 1 := by
      have h := pcnorm_base_add S (c := s₁) (by linarith)
      rw [hb₁, pcnorm_cutDir S] at h
      linarith
    have hσ₁ : σ = s₁ := by linarith
    rw [hσ₁, hb₁]
    simp
  · obtain ⟨σ, hσ, rfl⟩ := hz
    have h3 : |‖(pcbase S : ℂ)‖ - σ| = 1 := by
      have h := pcnorm_base_sub S (c := σ)
      rw [hzn] at h
      exact h.symm
    have h4 : ‖(pcbase S : ℂ)‖ - s₂ = -1 := by
      have h := pcnorm_base_sub_smul (S := S) (c := s₂)
      rw [hb₂] at h
      have h' : ((‖(pcbase S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
        have h2 := congrArg (fun w : ℂ => w / pccutDir S) h
        rw [mul_div_cancel_right₀ _ (pccutDir_ne_zero S), neg_div,
          div_self (pccutDir_ne_zero S)] at h2
        simpa using h2.symm
      exact_mod_cast h'
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h3 with h | h
    · exfalso; linarith [ht₂, hσ.1, hb]
    · have hσ₂ : σ = s₂ := by linarith
      rw [hσ₂, hb₂]
      simp

/-- Points of the boundary circle other than `±pccutDir S` lie in the cut pcannulus. -/
theorem pcsphere_subset_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    {z : ℂ} (hzn : ‖z‖ = 1) (hne : z ≠ pccutDir S) (hne' : z ≠ -pccutDir S) :
    z ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  refine ⟨⟨?_, pcnorm_one_notMem_V S hball hzn⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, hzn]
  · rintro hcuts
    have hmem := pccut_inter_sphere_subset S hball hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ z hcuts hzn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hne h
    · exact hne' h

/-- A preconnected set together with a point of its closure is preconnected. -/
theorem pcisPreconnected_insert_of_mem_closure {A : Set ℂ} (hA : IsPreconnected A) {x : ℂ}
    (hx : x ∈ closure A) : IsPreconnected (insert x A) := by
  refine (isPreconnected_iff_subset_of_disjoint).mpr ?_
  intro u v hu hv huv huv'
  have hAuv : A ⊆ u ∪ v := fun a ha => huv (Or.inr ha)
  have hAuv' : A ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨haA, hau, hav⟩
    have h1 : a ∈ insert x A ∩ (u ∩ v) := ⟨Or.inr haA, hau, hav⟩
    simpa [huv'] using h1
  have hAu_or_hAv : A ⊆ u ∨ A ⊆ v :=
    (isPreconnected_iff_subset_of_disjoint.mp hA) u v hu hv hAuv hAuv'
  have hxu : x ∈ u ∪ v := huv (Or.inl rfl)
  rcases hAu_or_hAv with hAu | hAv
  · left
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hyx | hyA
    · rw [hyx]
      rcases hxu with hxu' | hxv
      · exact hxu'
      · exfalso
        obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.mp hv x hxv
        obtain ⟨a, haA, hax⟩ := Metric.mem_closure_iff.mp hx ε hε
        have hav : a ∈ v := hεv (by rw [Metric.mem_ball, dist_comm]; exact hax)
        have h1 : a ∈ insert x A ∩ (u ∩ v) := ⟨Or.inr haA, hAu haA, hav⟩
        simpa [huv'] using h1
    · exact hAu hyA
  · right
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hyx | hyA
    · rw [hyx]
      rcases hxu with hxu' | hxv
      · exfalso
        obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.mp hu x hxu'
        obtain ⟨a, haA, hax⟩ := Metric.mem_closure_iff.mp hx ε hε
        have hau : a ∈ u := hεu (by rw [Metric.mem_ball, dist_comm]; exact hax)
        have h1 : a ∈ insert x A ∩ (u ∩ v) := ⟨Or.inr haA, hau, hAv haA⟩
        simpa [huv'] using h1
      · exact hxv
    · exact hAv hyA

/-- The point `I * pccutDir S` lies on the upper four-arc curve (at parameter `π/4`). -/
theorem pctgtUpB_pi_div_four (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (b : Bool) {θ₁ θ₂ : ℝ} :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 4) =
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Work.Smooth.SphereJordan.pctgtUpB, pcperPt_eq_self (by positivity) (by linarith)]
  rw [if_pos (by linarith : Real.pi / 4 ≤ Real.pi / 2)]
  have h : Real.pi / 4 / (Real.pi / 2) = 1 / 2 := by field_simp; ring
  rw [h, Work.Smooth.SphereJordan.pcsrcOuterUp,
    show ((Real.pi * (1 / 2) : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring,
    show ((Real.pi : ℂ) / 2) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I from rfl,
    Complex.exp_pi_div_two_mul_I]
  ring

/-- The point `-(I * pccutDir S)` lies on the lower four-arc curve (at parameter `π/4`). -/
theorem pctgtDnB_pi_div_four (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (b : Bool) {θ₁ θ₂ : ℝ} :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 4) =
      -Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Work.Smooth.SphereJordan.pctgtDnB, pcperPt_eq_self (by positivity) (by linarith)]
  rw [if_pos (by linarith : Real.pi / 4 ≤ Real.pi / 2)]
  have h : Real.pi / 4 / (Real.pi / 2) = 1 / 2 := by field_simp; ring
  rw [h, Work.Smooth.SphereJordan.pcsrcOuterDn,
    show ((Real.pi * (1 / 2) : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]
  ring

/-- **The bounded side of an upper four-arc curve lies in the upper piece.**
`T.V` is preconnected and contained in `pcannulusCut` (`pcupCurve_V_subset_annulusCut`), and `I·u` is
both in `pcannulusCut` and in the closure of `T.V` (it lies on the outer semicircle arc of the
curve); hence `T.V ∪ {I·u}` is a preconnected subset of `pcannulusCut` and lies in the component of
`I·u`. -/
theorem pcupCurve_subset_pieceUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂ := by
  have hsub : T.V ⊆ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ :=
    pcupCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
      T hVU
  have hx : Complex.I * pccutDir S ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ :=
    pcI_mul_cutDir_mem_annulusCut S hball
  have hxcl : Complex.I * pccutDir S ∈ closure T.V := by
    rw [Work.Smooth.SphereJordan.pcclosure_V_eq T]
    exact Or.inr ⟨Real.pi / 4, pctgtUpB_pi_div_four S b⟩
  have hpre : IsPreconnected (insert (Complex.I * pccutDir S) T.V) :=
    pcisPreconnected_insert_of_mem_closure T.preconn_V hxcl
  have hins : insert (Complex.I * pccutDir S) T.V ⊆
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · exact hsub hz
  have hcomp := hpre.subset_connectedComponentIn (Or.inl rfl : Complex.I * pccutDir S ∈
    insert (Complex.I * pccutDir S) T.V) hins
  exact fun z hz => hcomp (Or.inr hz)

/-- **The bounded side of a lower four-arc curve lies in the lower piece.** -/
theorem pcdnCurve_subset_pieceDown (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.pcpieceDown S t₁ s₁ t₂ s₂ := by
  have hsub : T.V ⊆ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ :=
    pcdnCurve_V_subset_annulusCut S hball b θ₁ θ₂ hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ hout₁ hout₂ hθ₁ hθ₂
      T hVU
  have hx : -Complex.I * pccutDir S ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ :=
    pcneg_I_mul_cutDir_mem_annulusCut S hball
  have hxcl : -Complex.I * pccutDir S ∈ closure T.V := by
    rw [Work.Smooth.SphereJordan.pcclosure_V_eq T]
    exact Or.inr ⟨Real.pi / 4, pctgtDnB_pi_div_four S b⟩
  have hpre : IsPreconnected (insert (-Complex.I * pccutDir S) T.V) :=
    pcisPreconnected_insert_of_mem_closure T.preconn_V hxcl
  have hins : insert (-Complex.I * pccutDir S) T.V ⊆
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · exact hsub hz
  have hcomp := hpre.subset_connectedComponentIn (Or.inl rfl : -Complex.I * pccutDir S ∈
    insert (-Complex.I * pccutDir S) T.V) hins
  exact fun z hz => hcomp (Or.inr hz)

/-- **The Schoenflies disc lies on one side of each four-arc curve.**
`S.V` is preconnected and, by `pctgtUpB_notMem_V`, disjoint from the trace of the curve, so
`Work.Smooth.Jordan.plane_separation_preconnected_subset` puts it on one of the two sides. -/
theorem pcside_of_upCurve (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ha₁ : (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S ∈ γ.trace)
    (ha₂ : (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S ∈ γ.trace)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (pcbase S : ℂ) + (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (pcbase S : ℂ) - (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz
  rintro ⟨τ, hτ⟩
  refine pctgtUpB_notMem_V S hball hb₁ hb₂ ha₁ ha₂ hts₁ hts₂ hseg₁ hseg₂ b θ₁ θ₂ τ ?_
  show (Work.SphereJordan.pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ ∈ S.V
  rw [hτ]; exact hz

/-- **The Schoenflies disc lies on one side of the lower four-arc curve.** -/
theorem pcside_of_dnCurve (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hb₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (ha₁ : (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S ∈ γ.trace)
    (ha₂ : (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S ∈ γ.trace)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (pcbase S : ℂ) + (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (pcbase S : ℂ) - (σ : ℂ) * pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₁ : (pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S)
    (hout₂ : (pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S)
    (hθ₁ : γ.γ θ₁ = (pcbase S : ℂ) + (t₁ : ℂ) * pccutDir S)
    (hθ₂ : γ.γ θ₂ = (pcbase S : ℂ) - (t₂ : ℂ) * pccutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz
  rintro ⟨τ, hτ⟩
  refine pctgtDnB_notMem_V S hball hb₁ hb₂ ha₁ ha₂ hts₁ hts₂ hseg₁ hseg₂ b θ₁ θ₂ τ ?_
  show (Work.SphereJordan.pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ ∈ S.V
  rw [hτ]; exact hz

end TwoCutsTilingStatements

/-!
## The two-pccuts construction: the target

The target `pccoreAuxTwoCuts` below is proved by the two-pccuts construction of the sibling
development, whose pieces are all in the workspace and all complete:

* `Work.SphereJordan.pcexists_targetData` (`Submission/Work/SphereJordan/pcannulusTargetSpans.lean`) —
  the two crosscuts of the pcannulus `pcannulus S` through the pcbase point of `S`, with the two inner
  endpoints on `γ`, bundled as a `pcSpanHyp`;
* `Work.SphereJordan.pctgtSpans_pairingExists` (`Submission/Work/SphereJordan/tgtSpansClean.lean`) —
  the pairing flag `b` for which the disc `S.V` lies on the *unbounded* side of **both** four-arc
  curves, together with `Work.SphereJordan.pctgtSpans_spansOfPairing`, which turns that flag into the
  tiling of the pcannulus by the two spanning discs, meeting exactly along the two crosscuts,
  and the Schoenflies data `pctgtSpans_upSch` / `pctgtSpans_dnSch` of the two curves;
* `Work.SphereJordan.TwoCutsAsm.pctwoCutsAssembly`
  (`Submission/Work/Smooth/SphereJordan/twoCutsAssemblyCrux.lean`) — the gluing of the two spanning
  discs with the two halves of the model pcannulus and the reparametrisation of the inner circle,
  yielding the injection `F` with the prescribed parametrisation of `γ` up to the sign `s`.

The module `twoCutsAssemblyCrux` is a verbatim copy (in a fresh namespace, and with the import of
this module removed) of `Submission/Work/SphereJordan/pctwoCutsAssembly.lean`: the latter imports
*this* module, so it cannot be used underneath it — this is the same device by which
`coreAuxTwoCutsCrux.lean` makes the crux `pcpieceUp ≠ pcpieceDown` available here.
-/

end Work.Smooth.SphereJordan

namespace Work.Smooth.SphereJordan

theorem pccoreAuxTwoCuts (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  -- the two-crosscut configuration through the pcbase point of `S`
  obtain ⟨t₁, s₁, t₂, s₂, θ₁, θ₂, ht₁, ht₁s₁, ht₂, ht₂s₂, ha₁, hseg₁, hout₁, ha₂, hseg₂, hout₂,
    hθ₁, hθ₂, hθ, hθ', hmax₁, hmax₂⟩ := Work.SphereJordan.pcexists_targetData h hs hball S
  let H : Work.SphereJordan.pcSpanHyp h hs hball S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, θ₁ := θ₁, θ₂ := θ₂,
      ht₁ := ht₁, ht₁s₁ := ht₁s₁, ht₂ := ht₂, ht₂s₂ := ht₂s₂,
      ha₁ := ha₁, hseg₁ := hseg₁, hout₁ := hout₁,
      ha₂ := ha₂, hseg₂ := hseg₂, hout₂ := hout₂,
      hθ₁ := hθ₁, hθ₂ := hθ₂, hθ := hθ, hθ' := hθ', hmax₁ := hmax₁, hmax₂ := hmax₂ }
  -- the pairing flag: `S.V` is on the unbounded side of both four-arc curves
  obtain ⟨b, hb⟩ := Work.SphereJordan.pctgtSpans_pairingExists h hs hball S H
  -- the two pieces of the cut pcannulus tile the pcannulus and meet exactly along the two crosscuts
  have hspans := Work.SphereJordan.pctgtSpans_spansOfPairing H b
    (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b) hb
  obtain ⟨-, -, -, -, -, -, hun, hin⟩ := hspans
  -- glue the two spanning discs with the two halves of the model pcannulus and reparametrise
  refine Work.SphereJordan.TwoCutsAsm.pctwoCutsAssembly h hs hball S b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
    (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b)
    (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b) ?_ ?_
  · rw [← (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b).range_e]
    exact hun
  · rw [← (Work.SphereJordan.pctgtSpans_upSch h hs hball S H b).range_e,
      ← (Work.SphereJordan.pctgtSpans_dnSch h hs hball S H b).range_e]
    exact hin

end Work.Smooth.SphereJordan
