import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs

/-!
# Tier B2: the squash of a level picture

The statement `Work.Drive.N2Lead.isLevelIsotopy_squash` together with the small toolkit of the
squash `sq s v = (v 0, v 1, (1 - s) * v 2)` of `Submission/Work/Drive/N2Lead/twistDefs.lean`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function

/-- The `C^∞` binding of the manifold calculus. -/
abbrev tpC : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ## The linear maps attached to `sq` and `proj2` -/

/-- The squash `sq s` as a continuous linear map: `v ↦ (v 0, v 1, (1 - s) * v 2)`.  (The `def`
`sq s` is the *same function*, and this is the form in which `ContinuousLinearMap.mfderiv_eq`
applies to it.) -/
noncomputable def sqLM (s : ℝ) : E3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 ![v 0, v 1, (1 - s) * v 2]
      map_add' := fun a b => by
        ext i
        fin_cases i
        · simp
        · simp
        · simp; ring
      map_smul' := fun c a => by
        ext i
        fin_cases i
        · simp
        · simp
        · simp; ring }

/-- The planar projection `proj2` as a continuous linear map: `v ↦ (v 0) + (v 1) i`. -/
noncomputable def proj2CLM : E3 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟨v 0, v 1⟩ : ℂ)
      map_add' := fun a b => by apply Complex.ext <;> simp
      map_smul' := fun c a => by apply Complex.ext <;> simp }

@[simp] lemma sqLM_apply (s : ℝ) (v : E3) : sqLM s v = sq s v := rfl

@[simp] lemma proj2CLM_apply (v : E3) : proj2CLM v = proj2 v := rfl

/-- The `mfderiv` of the squash is the squash itself. -/
lemma mfderiv_sq (s : ℝ) (x : E3) : mfderiv (𝓡 3) (𝓡 3) (sq s) x = sqLM s := by
  rw [show (sq s : E3 → E3) = ⇑(sqLM s) from rfl]
  exact ContinuousLinearMap.mfderiv_eq (sqLM s) (x := x)

/-- The `mfderiv` of the planar projection is the planar projection itself. -/
lemma mfderiv_proj2 (x : E3) : mfderiv (𝓡 3) 𝓘(ℝ,ℂ) proj2 x = proj2CLM := by
  rw [show (proj2 : E3 → ℂ) = ⇑proj2CLM from rfl]
  exact ContinuousLinearMap.mfderiv_eq (proj2CLM) (x := x)

/-! ## The coordinate rows of the squash -/

@[simp] lemma sq_coord_zero (s : ℝ) (v : E3) : (sq s v) 0 = v 0 := by simp [sq]

@[simp] lemma sq_coord_one (s : ℝ) (v : E3) : (sq s v) 1 = v 1 := by simp [sq]

@[simp] lemma sq_coord_two (s : ℝ) (v : E3) : (sq s v) 2 = (1 - s) * v 2 := by simp [sq]

/-- **The squash keeps the planar projection**: `proj2 (sq s v) = proj2 v`. -/
@[simp] lemma proj2_sq (s : ℝ) (v : E3) : proj2 (sq s v) = proj2 v := by
  simp only [proj2, sq]; congr 1

/-! ## Joint smoothness of the squash -/

/-- The uncurried squash `(s, v) ↦ sq s v` is `C^∞`. -/
theorem contDiff_uncurry_sq : ContDiff ℝ tpC (Function.uncurry sq) := by
  have h : ContDiff ℝ tpC (fun p : ℝ × E3 => (fun i : Fin 3 => sq p.1 p.2 i)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> · simp [sq]; fun_prop
  convert ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).comp h using 1
  ext p : 1
  rw [Function.uncurry_apply_pair]
  simp [EuclideanSpace.equiv, WithLp.toLp_ofLp]

/-- The uncurried squash on the product manifold `ℝ × ℝ³` (product model) is `C^∞`. -/
theorem contMDiff_uncurry_sq :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) tpC (fun q : ℝ × E3 => sq q.1 q.2) := by
  have h : ContMDiff (𝓘(ℝ, ℝ × E3)) (𝓡 3) tpC (fun q : ℝ × E3 => sq q.1 q.2) :=
    contMDiff_iff_contDiff.mpr contDiff_uncurry_sq
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
  exact h

open scoped Manifold ContDiff Topology in
/-- **Tier B2: the squash of a level picture.**  (The design's `Work.Drive.N2C.isLevelIsotopy_squash`,
§4 of `N2Lead/NOTES_LEAD_coherentWindows.md`; it is *not* on disk in `Drive/N2C`, and the Tier `D`
certificates of the saddle windows consume it, so it is restated here with the definition
`Work.Drive.N2Lead.sq s v = (v 0, v 1, (1 - s) * v 2)` of `Submission/Work/Drive/N2Lead/twistDefs.lean`.)
If `g` is smooth at every point of the regular level `f = b`, its **planar projection**
`y ↦ proj2 (g y) = ((g y) 0, (g y) 1)` is injective on the level, and `df`-immersive there (i.e. a `v`
with `df v = 0` whose `proj2`-derivative vanishes is zero), then `s ↦ sq s ∘ g` is a level isotopy at
`b`: the squash keeps the two planar coordinates, which carry injectivity and immersivity alone (the
only delicate case is `s = 1`, where `ker (sq 1) = ker proj2`).  The result goes in namespace
`Work.Drive.N2Lead`. -/
theorem isLevelIsotopy_squash {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (hsm : ∀ y : M, f y = b →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) g y)
    (hinj : ∀ x y : M, f x = b → f y = b →
      Work.Drive.N2Lead.proj2 (g x) = Work.Drive.N2Lead.proj2 (g y) → x = y)
    (himm : ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 →
      mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (g z)) y v = 0 → v = 0) :
    Work.Drive.N2C.IsLevelIsotopy f b (fun s y => Work.Drive.N2Lead.sq s (g y)) := by
  have hjoint : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) tpC
        (fun p : ℝ × M => sq p.1 (g p.2)) (s, y) := by
    intro s y hy
    have hpq : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) tpC
        (fun p : ℝ × M => (p.1, g p.2)) (s, y) :=
      ContMDiffAt.prodMk contMDiff_fst.contMDiffAt
        ((hsm y hy).comp (s, y) contMDiff_snd.contMDiffAt)
    have h := (contMDiff_uncurry_sq.contMDiffAt (x := (s, g y))).comp (s, y) hpq
    simpa only [Function.comp_def] using h
  have hslice : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt (𝓡 2) (𝓡 3) tpC (fun z : M => sq s (g z)) y := by
    intro s y hy
    have h := (hjoint s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    simpa only [Function.comp_def] using h
  refine ⟨hjoint, ?_, ?_⟩
  · -- injectivity: the squash keeps the two planar coordinates
    intro s x y hx hy hxy
    refine hinj x y hx hy ?_
    have h0 : (g x) 0 = (g y) 0 := by
      have hh := congrArg (fun w : E3 => w 0) hxy
      simpa using hh
    have h1 : (g x) 1 = (g y) 1 := by
      have hh := congrArg (fun w : E3 => w 1) hxy
      simpa using hh
    apply Complex.ext <;> simp [Work.Drive.N2Lead.proj2, h0, h1]
  · -- immersivity: `ker (sq s) ⊆ ker proj2`
    intro s y hy v hv hvh
    have hgmd : MDifferentiableAt (𝓡 2) (𝓡 3) (fun z : M => sq s (g z)) y :=
      (hslice s y hy).mdifferentiableAt (by simp)
    have hpjmd : MDifferentiableAt (𝓡 3) 𝓘(ℝ,ℂ) proj2 (sq s (g y)) := by
      rw [show (proj2 : E3 → ℂ) = ⇑proj2CLM from rfl]
      exact proj2CLM.mdifferentiableAt
    have hchain := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓘(ℝ,ℂ))
      (f := fun z : M => sq s (g z)) (g := proj2) (x := y) hpjmd hgmd v
    rw [hvh, map_zero] at hchain
    have hfun : (fun z : M => proj2 (sq s (g z))) = (fun z : M => proj2 (g z)) :=
      funext fun z => proj2_sq s (g z)
    rw [Function.comp_def, hfun] at hchain
    exact himm y hy v hv hchain

end Work.Drive.N2Lead
