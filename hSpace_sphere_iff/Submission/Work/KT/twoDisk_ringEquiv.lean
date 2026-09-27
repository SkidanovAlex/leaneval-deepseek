import Mathlib
import Submission.Work.KT.ClutchGeom
import Submission.Work.KT.Hemi
import Submission.Work.KT.hemiContinuous
import Submission.Work.KT.hemiParam
import Submission.Work.KT.hemiEquator

/-!
# The double-disk algebra is the algebra of functions on the sphere

`Work.KT.TwoDisk V` is the fibre product of two copies of `C(Ball V, ℂ)` over `C(Sph V, ℂ)`: the
algebra of the space obtained by gluing two copies of the closed unit ball of `V` along their
boundary spheres.  The maps `hemiUp, hemiDown : Ball V → Sph (WithLp 2 (V × ℝ))` of `Work.KT.Hemi`
parametrise the two closed hemispheres of the sphere, whose intersection is the equator
`{t = 0} ≅ Sph V`.

The algebra isomorphism `C(Sph (WithLp 2 (V × ℝ)), ℂ) ≃+* TwoDisk V` is the pull-back
`f ↦ (f ∘ hemiUp, f ∘ hemiDown)`; injectivity and surjectivity both come from the fact that the two
closed hemispheres cover the sphere, and on the overlap the two pull-backs agree by the
fibre-product condition.
-/

namespace Work.KT

noncomputable section

/-- The projection `(v, t) ↦ v` from the unit sphere of `V × ℝ` to the closed unit ball, bundled
as a continuous map. -/
def hemiProjCM (V : Type) [NormedAddCommGroup V] :
    C(Sph (WithLp 2 (V × ℝ)), Ball V) := ⟨hemiProj, hemiContinuous.2.2⟩

/-- The upper hemisphere parametrisation, bundled as a continuous map. -/
def hemiUpCM (V : Type) [NormedAddCommGroup V] :
    C(Ball V, Sph (WithLp 2 (V × ℝ))) := ⟨hemiUp, hemiContinuous.1⟩

/-- The lower hemisphere parametrisation, bundled as a continuous map. -/
def hemiDownCM (V : Type) [NormedAddCommGroup V] :
    C(Ball V, Sph (WithLp 2 (V × ℝ))) := ⟨hemiDown, hemiContinuous.2.1⟩

@[simp] lemma hemiProjCM_apply (V : Type) [NormedAddCommGroup V]
    (x : Sph (WithLp 2 (V × ℝ))) : hemiProjCM V x = hemiProj x := rfl

@[simp] lemma hemiUpCM_apply (V : Type) [NormedAddCommGroup V] (v : Ball V) :
    hemiUpCM V v = hemiUp v := rfl

@[simp] lemma hemiDownCM_apply (V : Type) [NormedAddCommGroup V] (v : Ball V) :
    hemiDownCM V v = hemiDown v := rfl

/-- The algebra homomorphism from functions on the sphere `Sph (WithLp 2 (V × ℝ))` to the
double-disk algebra: the two components are the pull-backs along the two hemisphere
parametrisations. -/
def twoDiskHom (V : Type) [NormedAddCommGroup V] :
    C(Sph (WithLp 2 (V × ℝ)), ℂ) →+* TwoDisk V where
  toFun f := ⟨(f.comp (hemiUpCM V), f.comp (hemiDownCM V)), by
    show restRho V (f.comp (hemiUpCM V)) = restRho V (f.comp (hemiDownCM V))
    ext s
    simp only [restRho_apply, ContinuousMap.comp_apply, hemiUpCM_apply, hemiDownCM_apply]
    rw [hemiEquator.1 s]⟩
  map_one' := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_ <;> ext x <;> simp
  map_mul' f g := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_ <;> ext x <;> simp
  map_zero' := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_ <;> ext x <;> simp
  map_add' f g := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_ <;> ext x <;> simp

lemma twoDiskHom_apply (V : Type) [NormedAddCommGroup V]
    (f : C(Sph (WithLp 2 (V × ℝ)), ℂ)) :
    ((twoDiskHom V f : TwoDisk V) : C(Ball V, ℂ) × C(Ball V, ℂ)) =
      (f.comp (hemiUpCM V), f.comp (hemiDownCM V)) := rfl

/-- The parametrised boundary sphere inside the ball. -/
lemma sphToBall_eta (V : Type) [NormedAddCommGroup V] (y : Ball V)
    (hy : (y : V) ∈ Metric.sphere (0 : V) 1) :
    sphToBall V ⟨(y : V), hy⟩ = y := Subtype.ext rfl

/-- The fibre-product condition, read inside the two balls: the two components of an element of
`TwoDisk V` agree on the boundary sphere. -/
lemma twoDisk_compat (V : Type) [NormedAddCommGroup V] (z : TwoDisk V) (y : Ball V)
    (hy : ‖(y : V)‖ = 1) : z.1.1 y = z.1.2 y := by
  have hy' : (y : V) ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy
  have hz := congrArg (fun u : C(Sph V, ℂ) => u ⟨(y : V), hy'⟩) z.2
  simpa [restRho_apply, sphToBall_eta V y hy'] using hz

lemma twoDiskHom_injective (V : Type) [NormedAddCommGroup V] :
    Function.Injective (twoDiskHom V) := by
  intro f f' hff'
  have hpair : (f.comp (hemiUpCM V), f.comp (hemiDownCM V)) =
      (f'.comp (hemiUpCM V), f'.comp (hemiDownCM V)) := by
    have h := congrArg (fun z : TwoDisk V => (z : C(Ball V, ℂ) × C(Ball V, ℂ))) hff'
    simpa only [twoDiskHom_apply] using h
  have h1 := (Prod.ext_iff.mp hpair).1
  have h2 := (Prod.ext_iff.mp hpair).2
  ext x
  rcases le_total (0 : ℝ) ((x : WithLp 2 (V × ℝ)).snd) with hs | hs
  · have hx : hemiUp (hemiProj x) = x := hemiParam.2.2.2.2.1 x hs
    have h := congrArg (fun u : C(Ball V, ℂ) => u (hemiProj x)) h1
    simp only [ContinuousMap.comp_apply, hemiUpCM_apply] at h
    rw [hx] at h
    exact h
  · have hx : hemiDown (hemiProj x) = x := hemiParam.2.2.2.2.2 x hs
    have h := congrArg (fun u : C(Ball V, ℂ) => u (hemiProj x)) h2
    simp only [ContinuousMap.comp_apply, hemiDownCM_apply] at h
    rw [hx] at h
    exact h

lemma twoDiskHom_surjective (V : Type) [NormedAddCommGroup V] :
    Function.Surjective (twoDiskHom V) := by
  classical
  intro z
  have hcompat : ∀ y : Ball V, ‖(y : V)‖ = 1 → z.1.1 y = z.1.2 y :=
    twoDisk_compat V z
  let G : C(Sph (WithLp 2 (V × ℝ)), ℂ) := z.1.1.comp (hemiProjCM V)
  let H : C(Sph (WithLp 2 (V × ℝ)), ℂ) := z.1.2.comp (hemiProjCM V)
  have hGH : ∀ x : Sph (WithLp 2 (V × ℝ)), (x : WithLp 2 (V × ℝ)).snd = 0 → G x = H x := by
    intro x hx
    have hnorm : ‖((hemiProj x : Ball V) : V)‖ = 1 := hemiEquator.2.1 x hx
    simpa [G, H, ContinuousMap.comp_apply, hemiProjCM_apply] using hcompat (hemiProj x) hnorm
  have hcont : Continuous (fun x : Sph (WithLp 2 (V × ℝ)) =>
      if 0 ≤ (x : WithLp 2 (V × ℝ)).snd then G x else H x) := by
    have hsnd : Continuous (fun x : Sph (WithLp 2 (V × ℝ)) =>
        (x : WithLp 2 (V × ℝ)).snd) := by fun_prop
    have hA : IsClosed {x : Sph (WithLp 2 (V × ℝ)) | 0 ≤ (x : WithLp 2 (V × ℝ)).snd} :=
      isClosed_le continuous_const hsnd
    have hB : IsClosed {x : Sph (WithLp 2 (V × ℝ)) | (x : WithLp 2 (V × ℝ)).snd ≤ 0} :=
      isClosed_le hsnd continuous_const
    have hcA : ContinuousOn (fun x : Sph (WithLp 2 (V × ℝ)) =>
        if 0 ≤ (x : WithLp 2 (V × ℝ)).snd then G x else H x)
        {x : Sph (WithLp 2 (V × ℝ)) | 0 ≤ (x : WithLp 2 (V × ℝ)).snd} :=
      (G.continuous.continuousOn).congr (fun x hx => if_pos hx)
    have hcB : ContinuousOn (fun x : Sph (WithLp 2 (V × ℝ)) =>
        if 0 ≤ (x : WithLp 2 (V × ℝ)).snd then G x else H x)
        {x : Sph (WithLp 2 (V × ℝ)) | (x : WithLp 2 (V × ℝ)).snd ≤ 0} :=
      (H.continuous.continuousOn).congr (fun x hx => by
        by_cases h : 0 ≤ (x : WithLp 2 (V × ℝ)).snd
        · rw [if_pos h, hGH x (le_antisymm hx h)]
        · rw [if_neg h])
    have hunion : {x : Sph (WithLp 2 (V × ℝ)) | 0 ≤ (x : WithLp 2 (V × ℝ)).snd} ∪
        {x : Sph (WithLp 2 (V × ℝ)) | (x : WithLp 2 (V × ℝ)).snd ≤ 0} = Set.univ := by
      ext x
      rcases le_total (0 : ℝ) ((x : WithLp 2 (V × ℝ)).snd) with h | h
      · simp [h]
      · simp [h]
    rw [← continuousOn_univ, ← hunion]
    exact hcA.union_of_isClosed hcB hA hB
  let F : C(Sph (WithLp 2 (V × ℝ)), ℂ) :=
    ⟨fun x => if 0 ≤ (x : WithLp 2 (V × ℝ)).snd then G x else H x, hcont⟩
  have hFup : ∀ v : Ball V, F (hemiUp v) = z.1.1 v := by
    intro v
    have hs : 0 ≤ (hemiUpFun v).snd := hemiParam.2.2.1 v
    show (if 0 ≤ ((hemiUp v : Sph (WithLp 2 (V × ℝ))) : WithLp 2 (V × ℝ)).snd
      then G (hemiUp v) else H (hemiUp v)) = z.1.1 v
    rw [hemiUp_coe, if_pos hs]
    simp [G, ContinuousMap.comp_apply, hemiProjCM_apply, hemiParam.1 v]
  have hFdown : ∀ v : Ball V, F (hemiDown v) = z.1.2 v := by
    intro v
    show (if 0 ≤ ((hemiDown v : Sph (WithLp 2 (V × ℝ))) : WithLp 2 (V × ℝ)).snd
      then G (hemiDown v) else H (hemiDown v)) = z.1.2 v
    rw [hemiDown_coe]
    by_cases hs : 0 ≤ (hemiDownFun v).snd
    · rw [if_pos hs]
      have hnorm : ‖(v : V)‖ = 1 := hemiEquator.2.2 v hs
      rw [show G (hemiDown v) = z.1.1 v by
        simp [G, ContinuousMap.comp_apply, hemiProjCM_apply, hemiParam.2.1 v]]
      exact hcompat v hnorm
    · rw [if_neg hs]
      simp [H, ContinuousMap.comp_apply, hemiProjCM_apply, hemiParam.2.1 v]
  refine ⟨F, ?_⟩
  refine Subtype.ext ?_
  rw [twoDiskHom_apply]
  show (F.comp (hemiUpCM V), F.comp (hemiDownCM V)) = (z.1.1, z.1.2)
  rw [show F.comp (hemiUpCM V) = z.1.1 from ContinuousMap.ext (fun v => hFup v),
    show F.comp (hemiDownCM V) = z.1.2 from ContinuousMap.ext (fun v => hFdown v)]

/-- The algebra of two disks glued along their boundary spheres (`Work.KT.TwoDisk V`) is the
algebra of continuous functions on the round sphere `Sph (WithLp 2 (V × ℝ))`, whose two closed
hemispheres are the two disks: the hemisphere `±t ≥ 0` is parametrised by `v ↦ (v, ±√(1-‖v‖²))`
and is homeomorphic to `Ball V` by the projection `(v,t) ↦ v` (with `‖v‖ = 1` on the equator
`t = 0`).  The isomorphism is the pull-back along this parametrisation; it sends the character
"evaluate at the north pole `(0,1)`" to "evaluate the first component at the centre `0` of the
first disk". -/
theorem twoDisk_ringEquiv (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ Θ : C(Sph (WithLp 2 (V × ℝ)), ℂ) ≃+* Work.KT.TwoDisk V,
      ∀ f : C(Sph (WithLp 2 (V × ℝ)), ℂ),
        (Θ f).1.1 ⟨0, by simp⟩ = f ⟨WithLp.toLp 2 ((0 : V), 1), by simp⟩ := by
  have hbij : Function.Bijective (twoDiskHom V) :=
    ⟨twoDiskHom_injective V, twoDiskHom_surjective V⟩
  refine ⟨RingEquiv.ofBijective (twoDiskHom V) hbij, ?_⟩
  intro f
  have hup0 : hemiUp (⟨0, by simp⟩ : Ball V) =
      ⟨WithLp.toLp 2 ((0 : V), 1), by simp⟩ := by
    apply Subtype.ext
    simp [hemiUp_coe, hemiUpFun]
  have hval : (RingEquiv.ofBijective (twoDiskHom V) hbij f : TwoDisk V) = twoDiskHom V f := rfl
  rw [hval, twoDiskHom_apply]
  change (f.comp (hemiUpCM V)) ⟨0, by simp⟩ = f ⟨WithLp.toLp 2 ((0 : V), 1), by simp⟩
  rw [ContinuousMap.comp_apply, hemiUpCM_apply]
  exact congrArg f hup0

end

end Work.KT
