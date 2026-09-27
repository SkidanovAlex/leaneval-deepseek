import Mathlib
import Submission.Work.Isotopy.exists_localInverse_param
import Submission.Work.Whitney.CutPush.Model
import Submission.Work.Whitney.exists_tubular_data_smooth

/-!
# The tube of the collar push, I: the local smooth left inverse

`Work.Whitney.CutPush.Model` (`slabPush`, `contDiff_slabPush_of_geometry`) reduces the whole ambient
push of the Whitney collar to *tubular data*:

* `H : ℝⁿ × ℝⁿ → ℝ^{2n}` smooth, with `H (u, 0)` the point of the finger over the base parameter `u`
  (the *first* factor is the base, the *second* is the normal offset),
* `g : ℝ^{2n} → ℝⁿ × ℝⁿ` **smooth** with `g (H x) = x` on the pushed slab `A`,
* an amplitude `d : ℝⁿ → ℝⁿ` (a function of the base only),

from which `ψ := slabPush H g d A` is the `C^∞` self-map of the target and `slabPush H g (-d) A` its
inverse.  This module starts the construction of that tubular data.  The map `H` is supplied (at a
double point) by `Work.Whitney.exists_tubular_data_smooth`; what is missing is a smooth left inverse
`g`.  Here we prove its *local* form — the input of the gluing argument (a finite cover of the
compact set `H '' A` by such neighbourhoods, glued with a smooth partition of unity; the map `g` may
be chosen freely off `H '' A`, so the gluing is standard).

The proof is a single application of the parametrised inverse function theorem
`Work.Isotopy.exists_localInverse_param`, applied to the family `G (s, v) = H v` (independent of the
dummy parameter `s`).  That theorem returns `h : ℝ → ℝ^{2n} → ℝⁿ × ℝⁿ`, `C^∞` on `O ×ˢ W`, with
`h s (G (s, y)) = y` for `y ∈ U` and `h s w ∈ V` for `w ∈ W`; the map `h 0` is the local left
inverse, and the range control (`h 0 '' W ⊆ V`, for a *prescribed* `V`) is what allows the local
inverses of a finite cover to be glued.

What is proved here:

* `exists_smooth_local_leftInverse` — the local smooth left inverse, with the range of `g` on a
  prescribed neighbourhood `V` of the tube point (the form the gluing consumes);
* `exists_smooth_local_inverse` — the local smooth inverse *with both inverse properties*, built
  directly from Mathlib's inverse function theorem (`ContDiffAt.localInverse`) via the observation
  that in the target dimension `2n` an injective derivative is a continuous linear equivalence;
* `isOpen_image_ball` — the image of a ball (on which the derivative is injective) is open;
* `contDiff_slabPush_of_contDiffOn` — a variant of the smoothness lemma of the slab push
  (`Work.Whitney.CutPush.contDiff_slabPush_of_geometry`) which asks only for `g` to be smooth on the
  *support* instead of globally, so that the tube map of the previous item (smooth only on the image
  of the ball) can be used directly, with no globalisation;
* `exists_smooth_leftInverse_on_ball` — the *global* smooth left inverse on the image of a ball:
  `g` is `C^∞` on `H '' ball 0 ρ''` and `g (H z) = z` on `closedBall 0 ρ'` (`ρ' < ρ'' < ρ`).  The
  gluing is by *injectivity*: the local inverses agree on the overlap of their images, so the
  (unique) preimage inside the ball — the natural global candidate — is smooth on the whole image.

Remaining for the full tubular data of `slabPush` (which asks for a *globally* `C^∞` `g`): multiply
the map above by a smooth bump `ν` which is `1` on the compact set `H '' closedBall 0 ρ'` and has
compact support in `H '' ball 0 ρ''`; the product is globally `C^∞` (a product of a smooth function
with a function that is smooth on a neighbourhood of `supp ν`) and is still a left inverse on the
compact set.  Mathlib's `exists_contDiff_tsupport_subset`
(`Analysis/Calculus/BumpFunction/FiniteDimension.lean`) supplies the pointwise bumps, which are
combined over a finite subcover.
-/

namespace Work.Whitney.CutPush

open scoped ContDiff
open Topology Set

set_option linter.unusedSectionVars false

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The local smooth left inverse of a tube map.**  Let `H : ℝⁿ × ℝⁿ → F` be smooth and suppose
that its derivative at `z` is injective (so that, the dimensions being equal, `H` is a local
diffeomorphism at `z`).  Then for every prescribed open neighbourhood `V` of `z` there are an open
neighbourhood `W` of `H z`, an open neighbourhood `U` of `z`, and a map `g`, smooth on `W`, with

* `g (H z) = z`,
* `g` maps `W` into the prescribed neighbourhood `V` of `z`,
* `g (H x) = x` for every `x ∈ U`.

These are exactly the local tubular data (a smooth left inverse with a controlled range) needed to
build the slab push. -/
theorem exists_smooth_local_leftInverse
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hinj : Function.Injective (fderiv ℝ H z))
    (V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hV : IsOpen V) (hzV : z ∈ V) :
    ∃ (g : F → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (W : Set F) (U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ H z ∈ W ∧ IsOpen U ∧ z ∈ U ∧ g (H z) = z ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g W ∧
      (∀ y ∈ W, g y ∈ V) ∧ (∀ x ∈ U, g (H x) = x) := by
  classical
  set G : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F :=
    H ∘ Prod.snd with hGdef
  have hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hGdef]
    exact hH.comp contDiff_snd
  have hderiv : ∀ v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      fderiv ℝ G (0, z) (0, v) = fderiv ℝ H z v := by
    intro v
    have hsnd : HasFDerivAt (Prod.snd : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
        (0, z) := hasFDerivAt_snd
    have h2 : HasFDerivAt H (fderiv ℝ H z) z :=
      (hH.differentiable (by simp) z).hasFDerivAt
    have h3 : HasFDerivAt G ((fderiv ℝ H z).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
        (0, z) := by
      rw [hGdef]
      exact h2.comp (0, z) hsnd
    rw [h3.fderiv, ContinuousLinearMap.comp_apply]
    simp
  have hinj' : Function.Injective (fun v => fderiv ℝ G (0, z) (0, v)) := by
    intro v w h
    simp only at h
    rw [hderiv, hderiv] at h
    exact hinj h
  obtain ⟨O, U, W, h, hO, h0O, hU, hzU, hW, hHW, hmap, hsm, _himg, hleft⟩ :=
    Work.Isotopy.exists_localInverse_param G Set.univ isOpen_univ 0 z (Set.mem_univ _)
      hGsm.contDiffOn V hV hzV hinj'
  refine ⟨fun y => h 0 y, W, U, hW, ?_, hU, hzU, ?_, ?_, ?_, ?_⟩
  · have hzW : G (0, z) ∈ W := hHW
    simpa [hGdef] using hzW
  · have hz : h 0 (G (0, z)) = z := hleft 0 h0O z hzU
    simpa [hGdef] using hz
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : F => ((0 : ℝ), y)) W :=
      (contDiffOn_const (c := (0 : ℝ))).prodMk contDiffOn_id
    exact hsm.comp h1 (fun y hy => ⟨h0O, hy⟩)
  · intro y hy
    exact hmap 0 h0O y hy
  · intro x hx
    have hx' : h 0 (G (0, x)) = x := hleft 0 h0O x hx
    simpa [hGdef] using hx'

/-- **The local smooth inverse of a tube map, with *both* inverse properties.**  In the target
dimension `2n` (so that the derivative of `H` at `z` is a *continuous linear equivalence* as soon as
it is injective) the local inverse can be produced directly by the inverse function theorem of
Mathlib, and then it is both a left and a right inverse in a neighbourhood.  This is the form needed
to glue the local inverses: two of them agree on the overlap of the images, by injectivity of `H`
and the right-inverse property. -/
theorem exists_smooth_local_inverse
    {H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hinj : Function.Injective (fderiv ℝ H z)) :
    ∃ g : EuclideanSpace ℝ (Fin (2 * n)) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      g (H z) = z ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (H z) ∧
      (∀ᶠ y in 𝓝 (H z), H (g y) = y) ∧ (∀ᶠ x in 𝓝 z, g (H x) = x) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    simp [Module.finrank_prod, two_mul]
  let f' : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) :=
    LinearEquiv.toContinuousLinearEquiv
      ((fderiv ℝ H z).toLinearMap.linearEquivOfInjective hinj hfin)
  have hf' : (f' : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n))) = fderiv ℝ H z := rfl
  have hderiv : HasFDerivAt H (f' : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n))) z := by
    rw [hf']
    exact (hH.differentiable (by simp) z).hasFDerivAt
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨(hH.contDiffAt).localInverse hderiv hn, ?_, ?_, ?_, ?_⟩
  · exact ContDiffAt.localInverse_apply_image _ _ _
  · exact ContDiffAt.to_localInverse _ _ _
  · exact (hH.contDiffAt.hasStrictFDerivAt' hderiv hn).eventually_right_inverse
  · exact (hH.contDiffAt.hasStrictFDerivAt' hderiv hn).eventually_left_inverse

/-- **The image of a ball under a tube map is open.**  If the derivative of `H` is injective at
every point of a ball, then `H` is a local diffeomorphism there, and its image of the ball is open:
every point `H z` of the image has a neighbourhood consisting of points `y = H (g y)` with `g y` in
the ball (the range control of the local inverse). -/
theorem isOpen_image_ball
    {H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) {ρ : ℝ}
    (hderiv : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      Function.Injective (fderiv ℝ H z)) :
    IsOpen (H '' Metric.ball 0 ρ) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨g, hgz, hgsm, hright, _hleft⟩ := exists_smooth_local_inverse hH (hderiv z hz)
  have hpre : {y | g y ∈ Metric.ball 0 ρ} ∈ 𝓝 (H z) :=
    hgsm.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by rw [hgz]; exact hz))
  filter_upwards [hpre, hright] with y hy hyr
  exact ⟨g y, hy, hyr⟩

/-- **The smooth left inverse of a tube map on a ball.**  Under the hypotheses of the tubular data
(`H` smooth, its derivative injective on the ball of radius `ρ`), there is a map `g` which is
`C^∞` on the image of the ball of radius `ρ''` and is a left inverse of `H` on the closed ball of
radius `ρ'` (`ρ' < ρ'' < ρ`).

The map `g` is the (unique, by injectivity of `H`) preimage of `H` inside the ball; the values of
`g` off the ball's image may be chosen arbitrarily, so smoothing/altering `g` off that image is
harmless (this is what makes the map usable in the slab push, whose support is contained in the
image of the pushed slab). -/
theorem exists_smooth_leftInverse_on_ball
    {H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    {ρ ρ' ρ'' : ℝ} (hρ'ρ'' : ρ' < ρ'') (hρ''ρ : ρ'' < ρ)
    (hinjOn : Set.InjOn H (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ))
    (hderiv : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      Function.Injective (fderiv ℝ H z)) :
    ∃ g : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (H '' Metric.ball 0 ρ'') ∧
      (∀ z ∈ Metric.closedBall 0 ρ', g (H z) = z) := by
  classical
  set g : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun y => if h : ∃ z ∈ Metric.ball 0 ρ, H z = y then Classical.choose h else 0 with hgdef
  have hgle : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      g (H z) = z := by
    intro z hz
    have hex : ∃ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
        H z' = H z := ⟨z, hz, rfl⟩
    have hmain : (if h : ∃ z' ∈ Metric.ball
          (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ, H z' = H z
        then Classical.choose h else 0) = z := by
      rw [dif_pos hex]
      exact hinjOn (Classical.choose_spec hex).1 hz (Classical.choose_spec hex).2
    simpa only [hgdef] using hmain
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ''
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ :=
    Metric.ball_subset_ball hρ''ρ.le
  have hclosed : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ'
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ :=
    fun z hz => hball (Metric.closedBall_subset_ball hρ'ρ'' hz)
  refine ⟨g, ?_, fun z hz => hgle z (hclosed hz)⟩
  have hopen : IsOpen (H '' Metric.ball 0 ρ'') :=
    isOpen_image_ball hH (fun z hz => hderiv z (hball hz))
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzρ : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ :=
    hball hz
  obtain ⟨gl, hglz, hglsm, hglright, _⟩ := exists_smooth_local_inverse hH (hderiv z hzρ)
  have hAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (H z) := by
    refine hglsm.congr_of_eventuallyEq ?_
    have hcont : ContinuousAt gl (H z) := hglsm.continuousAt
    have hmemρ : {y | gl y ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ} ∈ 𝓝 (H z) :=
      hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [hglz]; exact hzρ))
    filter_upwards [hopen.mem_nhds ⟨z, hz, rfl⟩, hglright, hmemρ] with y' hy' hy'r hy'ρ
    obtain ⟨z', hz', hz'y'⟩ := hy'
    have hmem : z' = gl y' :=
      hinjOn (hball hz') hy'ρ (by rw [hz'y', hy'r])
    rw [← hmem, ← hz'y']
    exact hgle z' (hball hz')
  exact (contDiffWithinAt_iff_contDiffAt (hopen.mem_nhds ⟨z, hz, rfl⟩)).mpr hAt

/-- **Smoothness of the slab push from a *locally* smooth inverse.**  The smoothness lemma
`Work.Whitney.CutPush.contDiff_slabPush_of_geometry` asks for a *globally* `C^∞` left inverse `g` of
the tube map.  The tube supplies only a map that is smooth on the image of the tube ball (see
`exists_smooth_leftInverse_on_ball`), and this is all that is used: the composite
`H ∘ normalShear d ∘ g` only has to be smooth on the support `H '' A`, the push is the identity off
the closure of the support, and on the frontier the gluing hypothesis applies.

Hence the ambient push of the collar can be built from `exists_smooth_leftInverse_on_ball` with no
globalisation of `g` at all, provided the pushed slab `A` lies in the closed ball of the tube
(so that `H '' A` lies in the image of the ball, on which `g` is known to be smooth). -/
theorem contDiff_slabPush_of_contDiffOn
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hAopen : IsOpen (H '' A))
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (H '' A))
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hglue : ∀ y ∈ frontier (H '' A), ∀ᶠ z in 𝓝 y, slabPush H g d A z = z) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (slabPush H g d A) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hyf : y ∈ frontier (H '' A)
  · exact (contDiffAt_id).congr_of_eventuallyEq (hglue y hyf)
  · by_cases hy : y ∈ H '' A
    · have hgy : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g y :=
        (contDiffWithinAt_iff_contDiffAt (hAopen.mem_nhds hy)).mp (hg y hy)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z => H (normalShear d (g z))) y :=
        (hH.contDiffAt).comp y (((contDiff_normalShear hd).contDiffAt).comp y hgy)
      exact h1.congr_of_eventuallyEq
        (slabPush_eventuallyEq_comp (H := H) (g := g) (d := d) hAopen hy)
    · have hycl : y ∉ closure (H '' A) := by
        intro hcl
        exact hyf (by rw [frontier_eq_closure_inter_closure]; exact ⟨hcl, subset_closure hy⟩)
      exact (contDiffAt_id).congr_of_eventuallyEq
        (slabPush_eventuallyEq_id_of_notMem_closure (H := H) (g := g) (d := d) hycl)

/-- **Tube data from one chart of the finger.**  Given an immersion `f`, and a chart `c` of the
source with `0 ∈ c.target` whose two directions are smooth (`c` on its source, `c.symm` everywhere —
the *gluing chart* that `Work.Whitney.exists_gluing_chart_open` produces along an arc), there are
radii `ρ' < ρ'' < ρ` with `0 < ρ'`, a smooth `H` and a map `g` such that

* `H (u, 0) = f (c.symm u)` — the finger over the base parameter `u`,
* `g` is `C^∞` on `H '' ball 0 ρ''` and `g (H z) = z` for `z ∈ closedBall 0 ρ'`,
* `H '' ball 0 ρ''` is open.

These are exactly the tubular data the slab push consumes (`slabPush` with `A ⊆ closedBall 0 ρ'`
and its smoothness by `contDiff_slabPush_of_contDiffOn`, whose hypothesis `ContDiffOn g (H '' A)` is
inherited from `ContDiffOn g (H '' ball 0 ρ'')`).  The map `H` is
`Work.Whitney.exists_tubular_data_smooth`; the map `g` is `exists_smooth_leftInverse_on_ball`. -/
theorem exists_tube_data_of_chart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ∀ u : EuclideanSpace ℝ (Fin n),
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u) :
    ∃ (ρ ρ' ρ'' : ℝ)
      (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (2 * n)))
      (g : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      0 < ρ' ∧ ρ' < ρ'' ∧ ρ'' < ρ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
      (∀ u : EuclideanSpace ℝ (Fin n), H (u, 0) = f (c.symm u)) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (H '' Metric.ball 0 ρ'') ∧
      IsOpen (H '' Metric.ball 0 ρ'') ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ',
        g (H z) = z) := by
  obtain ⟨H, ρ, L, hρ, _hL, hHc, hHaxis, hHinj, hHderiv, _hHLip⟩ :=
    exists_tubular_data_smooth f hf himm c h0 hcsm hsymm
  obtain ⟨g, hgsm, hgleft⟩ := exists_smooth_leftInverse_on_ball (H := H) hHc
    (ρ := ρ) (ρ' := ρ / 3) (ρ'' := 2 * ρ / 3) (by linarith) (by linarith) hHinj
    (fun z hz => hHderiv z hz)
  exact ⟨ρ, ρ / 3, 2 * ρ / 3, H, g, by linarith, by linarith, by linarith, hHc, hHaxis, hgsm,
    isOpen_image_ball hHc (fun z hz => hHderiv z (Metric.ball_subset_ball (by linarith) hz)),
    hgleft⟩

/-- **The composition of two slab pushes is a diffeomorphism of the target.**  Each factor is the
ambient push `slabPush H g d A` of `Work.Whitney.CutPush.Model` (the identity off `H '' A`, the
conjugated normal shear on `H '' A`), a `C^∞` diffeomorphism with inverse `slabPush H g (-d) A`
(`slabPush_leftInverse`, `slabPush_rightInverse`) and `C^∞` when `g` is smooth on the support
(`contDiff_slabPush_of_contDiffOn`).  The composite of two such pushes has the explicit inverse
obtained by composing the inverses in the reverse order — no disjointness is needed for this, only
for the verification of the clauses of the interface.

This is the step that assembles the Whitney finger from its per-chart pieces (the tubular data of
`exists_tube_data_of_chart`): `ψ := ψ₂ ∘ ψ₁` with inverse `ψ₁⁻¹ ∘ ψ₂⁻¹`.

The gluing hypotheses are stated in the notation-free form `{z | slabPush … z = z} ∈ 𝓝 y` (the same
as `∀ᶠ z in 𝓝 y, slabPush … z = z`, but readable by tools whose prelude lacks the scoped filter
notation). -/
theorem slabPush_comp {n : ℕ}
    {H₁ H₂ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin (2 * n))}
    {g₁ g₂ : EuclideanSpace ℝ (Fin (2 * n)) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {d₁ d₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A₁ A₂ B₁ B₂ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hA₁open : IsOpen (H₁ '' A₁)) (hA₂open : IsOpen (H₂ '' A₂))
    (hH₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H₁)
    (hH₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H₂)
    (hg₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g₁ (H₁ '' A₁))
    (hg₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g₂ (H₂ '' A₂))
    (hd₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d₁)
    (hd₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d₂)
    (hB₁ : Set.InjOn H₁ B₁) (hB₂ : Set.InjOn H₂ B₂)
    (hAB₁ : A₁ ⊆ B₁) (hAB₂ : A₂ ⊆ B₂)
    (hfix₁ : ∀ x ∈ B₁, g₁ (H₁ x) = x) (hfix₂ : ∀ x ∈ B₂, g₂ (H₂ x) = x)
    (hsh₁ : ∀ x ∈ A₁, normalShear d₁ x ∈ A₁)
    (hsh₂ : ∀ x ∈ A₂, normalShear d₂ x ∈ A₂)
    (hsh₁' : ∀ x ∈ A₁, normalShear (-d₁) x ∈ A₁)
    (hsh₂' : ∀ x ∈ A₂, normalShear (-d₂) x ∈ A₂)
    (hglue₁ : ∀ y ∈ frontier (H₁ '' A₁), {z | slabPush H₁ g₁ d₁ A₁ z = z} ∈ 𝓝 y)
    (hglue₂ : ∀ y ∈ frontier (H₂ '' A₂), {z | slabPush H₂ g₂ d₂ A₂ z = z} ∈ 𝓝 y) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁ y)) ∧
      Function.LeftInverse
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          slabPush H₁ g₁ (-d₁) A₁ (slabPush H₂ g₂ (-d₂) A₂ y))
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁ y)) ∧
      Function.RightInverse
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          slabPush H₁ g₁ (-d₁) A₁ (slabPush H₂ g₂ (-d₂) A₂ y))
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁ y)) := by
  have hcomp₁ := contDiff_slabPush_of_contDiffOn hA₁open hH₁ hg₁ hd₁ hglue₁
  have hcomp₂ := contDiff_slabPush_of_contDiffOn hA₂open hH₂ hg₂ hd₂ hglue₂
  refine ⟨hcomp₂.comp hcomp₁, ?_, ?_⟩
  · intro y
    show slabPush H₁ g₁ (-d₁) A₁ (slabPush H₂ g₂ (-d₂) A₂
        (slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁ y))) = y
    rw [slabPush_leftInverse hB₂ hfix₂ hAB₂ hsh₂ hsh₂' (slabPush H₁ g₁ d₁ A₁ y)]
    exact slabPush_leftInverse hB₁ hfix₁ hAB₁ hsh₁ hsh₁' y
  · intro y
    show slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁
        (slabPush H₁ g₁ (-d₁) A₁ (slabPush H₂ g₂ (-d₂) A₂ y))) = y
    rw [slabPush_rightInverse hB₁ hfix₁ hAB₁ hsh₁ hsh₁' (slabPush H₂ g₂ (-d₂) A₂ y)]
    exact slabPush_rightInverse hB₂ hfix₂ hAB₂ hsh₂ hsh₂' y

/-- **A slab push whose amplitude vanishes everywhere on its slab is the identity.**  This is the
per-piece *disjointness tool* of the gluing: on the part of a piece where the amplitude vanishes the
piece acts trivially, so in the overlap of two chart pieces only a piece whose amplitude does not
vanish can move a point.  (`slabPush H g d A` is `H ∘ normalShear d ∘ g` on `H '' A` and the
identity off `H '' A`; on `H '' A` the left-inverse hypothesis `g (H x) = x` reduces the value to
`H (normalShear d x)`, and `normalShear_eq_self` turns `d x.1 = 0` into the identity of the shear.)

Combined with `exists_smooth_bump_slab` — whose amplitude vanishes on the open exterior of the
radius-`R` ball, while `A \ W` is the inner slab over `closedBall u₀ R` — this confines the motion
of each piece to the image of its *inner* slab, which is what makes the per-piece data disjoint
along an overlapping finite cover. -/
theorem slabPush_eq_self_of_vanishes
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hfix : ∀ x ∈ A, g (H x) = x) (hd : ∀ x ∈ A, d x.1 = 0) :
    ∀ y : F, slabPush H g d A y = y := by
  intro y
  by_cases hy : y ∈ H '' A
  · obtain ⟨w, hw, rfl⟩ := hy
    rw [slabPush_of_mem ⟨w, hw, rfl⟩, hfix w hw, normalShear_eq_self (hd w hw)]
  · exact slabPush_of_notMem hy

/-- **One factor is trivial on the inner slab of another.**  Let `A₂in ⊆ A₂` be the set on which the
amplitude `d₂` of the second piece may be non-zero (so `d₂ = 0` off `A₂in`), and suppose the *inner*
slabs are disjoint: `H₁ '' A₁in` and `H₂ '' A₂in` do not meet.  Then the second push fixes every
point of `H₁ '' A₁in`.

The mechanism is `slabPush_eq_self_of_vanishes`: for `y = H₂ x ∈ H₁ '' A₁in ∩ H₂ '' A₂` the
parameter `x` cannot lie in `A₂in` (else the two inner slabs would meet), so `d₂ x.1 = 0` and the
shear is the identity at `x`; off `H₂ '' A₂` the push is the identity by construction.

This is the pairwise step of the gluing: with the inner slabs of the finite cover of
`Work.Whitney.arc_chart_cover` chosen pairwise disjoint (possible, each inner slab being strictly
inside its piece), each piece is trivial on the inner slabs of all the others. -/
theorem slabPush_eq_self_on_of_disjoint_inner
    {H₁ H₂ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g₂ : F → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {d₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A₂ A₁in A₂in : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hfix₂ : ∀ x ∈ A₂, g₂ (H₂ x) = x)
    (hd₂ : ∀ x ∈ A₂, x ∉ A₂in → d₂ x.1 = 0)
    (hdisj : Disjoint (H₁ '' A₁in) (H₂ '' A₂in)) :
    ∀ y : F, y ∈ H₁ '' A₁in → slabPush H₂ g₂ d₂ A₂ y = y := by
  intro y hy
  by_cases hy2 : y ∈ H₂ '' A₂
  · obtain ⟨x, hx, rfl⟩ := hy2
    have hxin : x ∉ A₂in := fun hcon => (Set.disjoint_left.mp hdisj hy) ⟨x, hcon, rfl⟩
    rw [slabPush_of_mem ⟨x, hx, rfl⟩, hfix₂ x hx, normalShear_eq_self (hd₂ x hx hxin)]
  · exact slabPush_of_notMem hy2

/-- **The pairwise locality of the composite.**  Under the hypotheses of
`slabPush_eq_self_on_of_disjoint_inner`, plus that the inner slab of the *first* piece is preserved by
its own shear (which holds for the slab `closedBall u₀ R ×ˢ univ` of `exists_smooth_bump_slab`, by
`normalShear_mem_slab`), the composite `ψ₂ ∘ ψ₁` acts on the inner slab of the first piece exactly as
`ψ₁` does: the second factor fixes the image. -/
theorem slabPush_comp_on_inner
    {H₁ H₂ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g₁ g₂ : F → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {d₁ d₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A₁ A₂ A₁in A₂in : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hfix₁ : ∀ x ∈ A₁, g₁ (H₁ x) = x)
    (hfix₂ : ∀ x ∈ A₂, g₂ (H₂ x) = x)
    (hsub₁ : A₁in ⊆ A₁)
    (hd₂ : ∀ x ∈ A₂, x ∉ A₂in → d₂ x.1 = 0)
    (hsh₁ : ∀ x ∈ A₁in, normalShear d₁ x ∈ A₁in)
    (hdisj : Disjoint (H₁ '' A₁in) (H₂ '' A₂in)) :
    ∀ y : F, y ∈ H₁ '' A₁in →
      slabPush H₂ g₂ d₂ A₂ (slabPush H₁ g₁ d₁ A₁ y) = slabPush H₁ g₁ d₁ A₁ y := by
  intro y hy
  have hψ : slabPush H₁ g₁ d₁ A₁ y ∈ H₁ '' A₁in := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [slabPush_of_mem ⟨x, hsub₁ hx, rfl⟩, hfix₁ x (hsub₁ hx)]
    exact ⟨normalShear d₁ x, hsh₁ x hx, rfl⟩
  exact slabPush_eq_self_on_of_disjoint_inner (H₁ := H₁) hfix₂ hd₂ hdisj _ hψ

end Work.Whitney.CutPush
