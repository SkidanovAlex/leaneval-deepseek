import Mathlib
import Submission.Work.Whitney.CutPush.BigonData
import Submission.Work.Drive.Push.tubeFlattening
import Submission.Work.Drive.Whitney.exists_smooth_fderiv_two
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The fold collar

(File skeleton; the main theorem `foldCollar` is at the bottom.)
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Topology Set Module

set_option linter.unusedSectionVars false

/-! ## Part 1: the manifold-derivative facts -/

/-- An element of `N` is killed by the orthogonal projection onto `Nᗮ`. -/
theorem starProj_eq_zero_of_mem {n : ℕ} {N : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n)))}
    {y : EuclideanSpace ℝ (Fin (2*n))} (hy : y ∈ N) : Nᗮ.starProjection y = 0 := by
  have h2 : (Nᗮ).orthogonalProjectionOnto y = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact hy
  rw [Submodule.starProjection_apply, h2]
  rfl

/-- Conversely, an element killed by the projection onto `Nᗮ` lies in `N`. -/
theorem mem_of_starProjection_eq_zero {n : ℕ} {N : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n)))}
    {x : EuclideanSpace ℝ (Fin (2*n))} (h : Nᗮ.starProjection x = 0) : x ∈ N := by
  have h2 : (Nᗮ).orthogonalProjectionOnto x = 0 := by
    rw [Submodule.starProjection_apply] at h
    exact Submodule.coe_eq_zero.mp h
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at h2
  exact h2

/-- **The range of the `mfderiv` of a map that lands in a submodule.** -/
theorem mfderiv_range_le_of_eventually_mem {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {g : M → EuclideanSpace ℝ (Fin (2*n))} {p : M}
    {N : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n)))}
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) g p)
    (hN : ∀ᶠ x in 𝓝 p, g x ∈ N) :
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) g p).toLinearMap ≤ N := by
  have hzero : (fun x : M => Nᗮ.starProjection (g x)) =ᶠ[𝓝 p] fun _ => 0 :=
    hN.mono (fun x hx => starProj_eq_zero_of_mem hx)
  have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
      (fun x : M => Nᗮ.starProjection (g x)) p = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq_v433 hzero, mfderiv_const]
    rfl
  have h2 : ∀ w, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
        (fun x : M => Nᗮ.starProjection (g x)) p w
      = Nᗮ.starProjection (((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) g p).toLinearMap) w) := by
    intro w
    have hπ : HasMFDerivAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) (fun y => Nᗮ.starProjection y) (g p)
        Nᗮ.starProjection := ContinuousLinearMap.hasMFDerivAt _
    have hcomp := hπ.comp p hg.hasMFDerivAt
    have hw := congrArg (fun (L : _ →L[ℝ] _) => L w) hcomp.mfderiv
    have hw2 : (Nᗮ.starProjection ∘SL (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) g p)) w
        = Nᗮ.starProjection (((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) g p).toLinearMap) w) :=
      ContinuousLinearMap.comp_apply _ _ w
    rw [show (fun x : M => Nᗮ.starProjection (g x)) = ((fun y => Nᗮ.starProjection y) ∘ g) from rfl]
    exact hw.trans hw2
  intro v hv
  rw [LinearMap.mem_range] at hv
  obtain ⟨w, rfl⟩ := hv
  exact mem_of_starProjection_eq_zero (by rw [← h2 w, h1]; rfl)

/-- **The same, for a compsite `A₀ ∘ f`, in the form needed below.** -/
theorem map_fderiv_range_le_of_eventually_mem {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A₀ : EuclideanSpace ℝ (Fin (2*n)) → EuclideanSpace ℝ (Fin (2*n)))
    (hA : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) A₀)
    {f : M → EuclideanSpace ℝ (Fin (2*n))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {p : M} {K : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n)))}
    (hU : ∀ᶠ x in 𝓝 p, A₀ (f x) ∈ K) :
    Submodule.map ((fderiv ℝ A₀ (f p)).toLinearMap)
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap) ≤ K := by
  have hmdA : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) A₀ (f p) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (hA.differentiable (by simp)).differentiableAt
  have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p := hf.mdifferentiableAt (by simp)
  have hsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => A₀ (f y)) := hA.contMDiff.comp hf
  have hlocal := mfderiv_range_le_of_eventually_mem
    (g := fun y : M => A₀ (f y)) (p := p) (N := K) (hsm.mdifferentiableAt (by simp)) hU
  have hchain : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) (fun y => A₀ (f y)) p
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) A₀ (f p)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p) := by
    simpa [Function.comp_def] using
      mfderiv_comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
        (I'' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
        (g := A₀) (f := f) p hmdA hmdF
  have hMA : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) A₀ (f p) = fderiv ℝ A₀ (f p) :=
    mfderiv_eq_fderiv
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) (fun y => A₀ (f y)) p
      = ((fderiv ℝ A₀ (f p)).comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p)) := by
    rw [hchain]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) =>
      L.comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p)) hMA
  have heq : Submodule.map ((fderiv ℝ A₀ (f p)).toLinearMap)
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap)
      = LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) (fun y => A₀ (f y)) p).toLinearMap := by
    rw [hcomp]
    exact (LinearMap.range_comp _ _).symm
  exact heq.symm ▸ hlocal


/-! ## Part 3b: the chain rule on `Submodule.map` -/

/-- **The chain rule for `Submodule.map`.**  If the derivative of `Ψ` at `B x` agrees with the linear
map `g`, then the derivative at `x` of the composite `y ↦ Ψ (B y)` pushes a submodule `X` to the
`g`-image of the `B x`-image of `X`. -/
theorem map_fderiv_comp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ B : E → E} {x : E} {X : Submodule ℝ E} {g : E →ₗ[ℝ] E}
    (hΨ : DifferentiableAt ℝ Ψ (B x)) (hB : DifferentiableAt ℝ B x)
    (h : (fderiv ℝ Ψ (B x) : E →ₗ[ℝ] E) = g) :
    Submodule.map ((fderiv ℝ (fun y : E => Ψ (B y)) x).toLinearMap) X
      = Submodule.map g (Submodule.map ((fderiv ℝ B x).toLinearMap) X) := by
  have hchain : fderiv ℝ (fun y : E => Ψ (B y)) x
      = (fderiv ℝ Ψ (B x)).comp (fderiv ℝ B x) := by
    have h0 := fderiv_comp (x := x) (g := Ψ) (f := B) hΨ hB
    simpa [Function.comp_def] using h0
  rw [hchain]
  rw [show (((fderiv ℝ Ψ (B x)).comp (fderiv ℝ B x)).toLinearMap : E →ₗ[ℝ] E)
      = ((fderiv ℝ Ψ (B x) : E →ₗ[ℝ] E)).comp ((fderiv ℝ B x).toLinearMap) from rfl]
  rw [h]
  exact Submodule.map_comp ((fderiv ℝ B x).toLinearMap) g X


/-! ## Part 2: the graph/shape bookkeeping -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The graph of `φ : Kᗮ → K` over the orthogonal complement of `K`: `{r + φ r : r ∈ Kᗮ}`. -/
noncomputable def gr (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) : Submodule ℝ E :=
  LinearMap.range ((Kᗮ).subtype + (K.subtype.comp φ))

theorem mem_gr_iff (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) (v : E) :
    v ∈ gr K φ ↔ ∃ r : Kᗮ, (r : E) + (φ r : E) = v := by
  rw [gr, LinearMap.mem_range]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, by simpa using hr⟩, fun ⟨r, hr⟩ => ⟨r, by simpa using hr⟩⟩

theorem gr_inf_K (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) : gr K φ ⊓ K = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv, hvK⟩
  obtain ⟨r, rfl⟩ := (mem_gr_iff K φ v).mp hv
  have hvK' : (r : E) + (φ r : E) ∈ K := hvK
  have hxK : (r : E) ∈ K := by
    have h1 : (r : E) + (φ r : E) - (φ r : E) ∈ K := K.sub_mem hvK' (φ r).2
    rwa [add_sub_cancel_right] at h1
  have hx0 : (r : E) = 0 := by
    have h2 : (r : E) ∈ K ⊓ Kᗮ := ⟨hxK, r.2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h2
    simpa using h2
  have hr0 : r = 0 := Subtype.ext hx0
  rw [hr0]
  simp

theorem injective_grMap (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) :
    Function.Injective (((Kᗮ).subtype + (K.subtype.comp φ)) : Kᗮ → E) := by
  intro r s hrs
  have h1 : ((r : E) + (φ r : E)) = ((s : E) + (φ s : E)) := hrs
  have h2 : ((r - s : Kᗮ) : E) + (φ (r - s) : E) = 0 := by
    have h3 : ((r - s : Kᗮ) : E) + (φ (r - s) : E)
        = ((r : E) + (φ r : E)) - ((s : E) + (φ s : E)) := by
      rw [Submodule.coe_sub, map_sub, Submodule.coe_sub]
      abel
    rw [h3, h1, sub_self]
  have h4 : ((r - s : Kᗮ) : E) = -(φ (r - s) : E) := eq_neg_of_add_eq_zero_left h2
  have h5 : ((r - s : Kᗮ) : E) ∈ K ⊓ Kᗮ :=
    ⟨by rw [h4]; exact K.neg_mem (φ (r - s)).2, (r - s).2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at h5
  exact sub_eq_zero.mp (Subtype.ext (by simpa using h5))

theorem gr_finrank (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) :
    finrank ℝ ↥(gr K φ) = finrank ℝ ↥(Kᗮ) := by
  rw [gr]
  exact LinearMap.finrank_range_of_inj (injective_grMap K φ)

theorem gr_isCompl (K : Submodule ℝ E) (φ : Kᗮ →ₗ[ℝ] K) : IsCompl (gr K φ) K := by
  have hdim : finrank ℝ E ≤ finrank ℝ ↥(gr K φ) + finrank ℝ ↥K := by
    rw [gr_finrank, ← Submodule.finrank_add_finrank_orthogonal K]
    omega
  refine (Submodule.isCompl_iff_disjoint (gr K φ) K hdim).mpr ?_
  rw [disjoint_iff, gr_inf_K]

theorem starProj_eq_zero_of_mem_K {K : Submodule ℝ E} {v : E} (hv : v ∈ K) :
    (Kᗮ).starProjection v = 0 := by
  have h2 : (Kᗮ).orthogonalProjectionOnto v = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact hv
  rw [Submodule.starProjection_apply, h2]
  rfl

theorem starProjection_add_gr (K : Submodule ℝ E) (ψ : Kᗮ →ₗ[ℝ] K) (r : Kᗮ) :
    (Kᗮ).starProjection ((r : E) + (ψ r : E)) = (r : E) := by
  rw [map_add, Submodule.starProjection_eq_self_iff.mpr r.2, starProj_eq_zero_of_mem_K (ψ r).2,
    add_zero]

theorem map_eq_range_comp {N : Type*} [AddCommGroup N] [Module ℝ N] (f : E →ₗ[ℝ] N)
    (p : Submodule ℝ E) :
    Submodule.map f p = LinearMap.range (f.comp p.subtype) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩

noncomputable def shear (K : Submodule ℝ E) (S : E →L[ℝ] E) : E →ₗ[ℝ] E :=
  LinearMap.id - (S.comp (Kᗮ).starProjection).toLinearMap

noncomputable def restrictK (K : Submodule ℝ E) (S : E →L[ℝ] E) (hS : ∀ v : E, S v ∈ K) :
    Kᗮ →ₗ[ℝ] K :=
  (S.toLinearMap.codRestrict K hS).comp (Kᗮ).subtype

theorem restrictK_apply (K : Submodule ℝ E) (S : E →L[ℝ] E) (hS : ∀ v : E, S v ∈ K)
    (r : Kᗮ) : ((restrictK K S hS r : K) : E) = S (r : E) := rfl

theorem map_shear_gr (K : Submodule ℝ E) (S : E →L[ℝ] E) (hS : ∀ v : E, S v ∈ K)
    (φ : Kᗮ →ₗ[ℝ] K) :
    Submodule.map (shear K S) (gr K φ) = gr K (φ - restrictK K S hS) := by
  have hshear : ∀ r : Kᗮ, (shear K S) ((r : E) + (φ r : E)) = (r : E) + ((φ - restrictK K S hS) r : E) := by
    intro r
    have hpr : (Kᗮ).starProjection ((r : E) + (φ r : E)) = (r : E) := starProjection_add_gr K φ r
    have hc : ((S.comp (Kᗮ).starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E) ((r : E) + (φ r : E))
        = S ((Kᗮ).starProjection ((r : E) + (φ r : E))) := ContinuousLinearMap.comp_apply _ _ _
    have h1 : (shear K S) ((r : E) + (φ r : E)) = ((r : E) + (φ r : E)) - S (r : E) := by
      rw [shear, LinearMap.sub_apply, LinearMap.id_apply, hc, hpr]
    have h2 : ((φ - restrictK K S hS) r : E) = (φ r : E) - S (r : E) := by
      rw [LinearMap.sub_apply, Submodule.coe_sub, restrictK_apply]
    rw [h1, h2]
    abel
  apply le_antisymm
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).mp hw
    obtain ⟨r, rfl⟩ := (mem_gr_iff K φ v).mp hv
    exact (mem_gr_iff K (φ - restrictK K S hS) _).mpr ⟨r, (hshear r).symm⟩
  · intro w hw
    obtain ⟨r, hr⟩ := (mem_gr_iff K (φ - restrictK K S hS) w).mp hw
    exact ⟨(r : E) + (φ r : E), (mem_gr_iff K φ _).mpr ⟨r, rfl⟩, by rw [hshear r, hr]⟩

theorem exists_gr_of_isCompl (K V : Submodule ℝ E) (hV : IsCompl V K) :
    ∃ φ : Kᗮ →ₗ[ℝ] K, V = gr K φ := by
  refine ⟨-((K.projectionOnto V hV.symm).comp (Kᗮ).subtype), ?_⟩
  have hfin : finrank ℝ ↥V = finrank ℝ ↥(Kᗮ) := by
    have h1 : finrank ℝ E = finrank ℝ ↥V + finrank ℝ ↥K := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq V K
      rw [hV.sup_eq_top, hV.inf_eq_bot, finrank_top, finrank_bot, add_zero] at h
      exact h
    have h2 := Submodule.finrank_add_finrank_orthogonal K
    omega
  have hle : V ≤ gr K (-((K.projectionOnto V hV.symm).comp (Kᗮ).subtype)) := by
    intro v hv
    refine (mem_gr_iff K _ v).mpr ⟨(Kᗮ).orthogonalProjectionOnto v, ?_⟩
    have hsplit : ((K.orthogonalProjectionOnto v : K) : E) + (((Kᗮ).orthogonalProjectionOnto v : Kᗮ) : E) = v := by
      have h := Submodule.starProjection_add_starProjection_orthogonal (K := K) v
      rwa [Submodule.starProjection_apply, Submodule.starProjection_apply] at h
    have hK : (K.projectionOnto V hV.symm) (((K.orthogonalProjectionOnto v : K)) : E)
        = K.orthogonalProjectionOnto v :=
      Submodule.projectionOnto_apply_of_mem_left hV.symm (K.orthogonalProjectionOnto v).2
    have hV0 : (K.projectionOnto V hV.symm) v = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff hV.symm).mpr hv
    have h3 : (K.projectionOnto V hV.symm) (((K.orthogonalProjectionOnto v : K)) : E)
        + (K.projectionOnto V hV.symm) (((Kᗮ).orthogonalProjectionOnto v : Kᗮ) : E)
        = (K.projectionOnto V hV.symm) v := by
      rw [← map_add, hsplit]
    rw [hK, hV0] at h3
    have h4 : (K.projectionOnto V hV.symm) (((Kᗮ).orthogonalProjectionOnto v : Kᗮ) : E)
        = -(K.orthogonalProjectionOnto v) := eq_neg_of_add_eq_zero_right h3
    have h5 : ((-((K.projectionOnto V hV.symm).comp (Kᗮ).subtype)) ((Kᗮ).orthogonalProjectionOnto v) : E)
        = (K.orthogonalProjectionOnto v : E) := by
      show - (((K.projectionOnto V hV.symm) (((Kᗮ).orthogonalProjectionOnto v : Kᗮ) : E)) : E)
        = (K.orthogonalProjectionOnto v : E)
      rw [h4]
      simp
    rw [h5]
    rw [add_comm]
    exact hsplit
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [gr_finrank, hfin])

theorem finrank_gr_inf_gr_sub (K : Submodule ℝ E) (ψ T : Kᗮ →ₗ[ℝ] K) :
    finrank ℝ ↥(gr K ψ ⊓ gr K (ψ - T))
      = finrank ℝ ↥(Kᗮ) - finrank ℝ ↥(LinearMap.range T) := by
  have heq : gr K ψ ⊓ gr K (ψ - T)
      = Submodule.map (((Kᗮ).subtype + (K.subtype.comp ψ)) : Kᗮ →ₗ[ℝ] E) (LinearMap.ker T) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
      obtain ⟨r, rfl⟩ := (mem_gr_iff K ψ w).mp hw1
      obtain ⟨s, hs⟩ := (mem_gr_iff K (ψ - T) ((r : E) + (ψ r : E))).mp hw2
      have hrs : (r : E) = (s : E) := by
        have h := congrArg (fun z => (Kᗮ).starProjection z) hs.symm
        rw [starProjection_add_gr, starProjection_add_gr] at h
        exact h
      have h5 : s = r := Subtype.ext hrs.symm
      have hs' : (s : E) + ((ψ - T) s : E) = (s : E) + (ψ s : E) := by
        rw [← h5] at hs
        exact hs
      have h2 : ((ψ - T) s : E) = (ψ s : E) := add_left_cancel hs'
      have h3 : (T s : E) = 0 := by
        have h4 : ((ψ - T) s : E) = (ψ s : E) - (T s : E) := by
          rw [LinearMap.sub_apply, Submodule.coe_sub]
        rw [h4] at h2
        exact sub_eq_self.mp h2
      refine ⟨s, (LinearMap.mem_ker).mpr (Subtype.ext h3), ?_⟩
      rw [h5]
      simp
    · intro w hw
      obtain ⟨r, hr, rfl⟩ := (Submodule.mem_map).mp hw
      have hrT : T r = 0 := (LinearMap.mem_ker).mp hr
      refine ⟨(mem_gr_iff K ψ _).mpr ⟨r, rfl⟩, (mem_gr_iff K (ψ - T) _).mpr ⟨r, ?_⟩⟩
      have h1 : ((ψ - T) r : E) = (ψ r : E) := by
        simp only [LinearMap.sub_apply, hrT, Submodule.coe_zero, sub_zero]
      rw [h1]
      simp
  rw [heq, map_eq_range_comp]
  rw [LinearMap.finrank_range_of_inj
    (fun a b hab => Subtype.ext ((injective_grMap K ψ) hab))]
  rw [← LinearMap.finrank_range_add_finrank_ker T]
  omega

/-! ## Part 3: the plane of the tube -/

/-- The derivative of the composite `A₀ ∘ f` at a point where `A₀ ∘ f` lands in the plane `K`. -/
theorem map_fderiv_range_eq_of_tube {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A₀ : EuclideanSpace ℝ (Fin (2*n)) → EuclideanSpace ℝ (Fin (2*n)))
    (hA : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) A₀)
    (hAinj : ∀ x : EuclideanSpace ℝ (Fin (2*n)), Function.Injective (fderiv ℝ A₀ x))
    {f : M → EuclideanSpace ℝ (Fin (2*n))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfinj : ∀ x : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f x))
    {p : M} {K : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n)))}
    (hKfin : finrank ℝ K = n)
    (hU : ∀ᶠ x in 𝓝 p, A₀ (f x) ∈ K) :
    Submodule.map ((fderiv ℝ A₀ (f p)).toLinearMap)
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap) = K := by
  refine Submodule.eq_of_le_of_finrank_eq
    (map_fderiv_range_le_of_eventually_mem A₀ hA hf hU) ?_
  have h1 : finrank ℝ ↥(LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap) = n := by
    rw [LinearMap.finrank_range_of_inj (hfinj p)]
    have h2 : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      rw [finrank_euclideanSpace]
      simp
    exact h2
  have h2 : finrank ℝ ↥(Submodule.map ((fderiv ℝ A₀ (f p)).toLinearMap)
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap)) = n := by
    rw [map_eq_range_comp]
    rw [LinearMap.finrank_range_of_inj]
    · exact h1
    · intro a b hab
      have h3 : (fderiv ℝ A₀ (f p)) ((LinearMap.range (mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap).subtype a)
          = (fderiv ℝ A₀ (f p)) ((LinearMap.range (mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p).toLinearMap).subtype b) := hab
      exact Subtype.ext ((hAinj (f p)) h3)
  rw [h2, hKfin]

/-- The orthogonal projection onto a submodule is idempotent. -/
theorem starProjection_comp_self (K : Submodule ℝ E) :
    (K.starProjection.comp K.starProjection : E →L[ℝ] E) = K.starProjection := by
  ext v
  rw [ContinuousLinearMap.comp_apply]
  refine Submodule.starProjection_eq_self_iff.mpr ?_
  rw [Submodule.starProjection_apply]
  exact (K.orthogonalProjectionOnto v).2


/-! ## Part 4: the linear core -/

/-- **The fold planes** (local form of the linear core). -/
theorem foldPlanesAux {n : ℕ} (hn : 3 ≤ n) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K V W : Submodule ℝ E} (hV : IsCompl V K) (hW : IsCompl W K)
    (hK : Module.finrank ℝ K = n) (hE : Module.finrank ℝ E = 2 * n)
    (u : E) (hu : u ∈ K) (hu0 : u ≠ 0) :
    ∃ (S₁ S₂ : E →L[ℝ] E) (C : Submodule ℝ E),
      (∀ v : E, S₁ v ∈ K ⊓ (Submodule.span ℝ {u})ᗮ) ∧
      (∀ v : E, S₂ v ∈ K ⊓ (Submodule.span ℝ {u})ᗮ) ∧
      (∀ a : E, a ∈ Submodule.span ℝ {u} → S₁ a = 0) ∧
      (∀ a : E, a ∈ Submodule.span ℝ {u} → S₂ a = 0) ∧
      IsCompl C K ∧
      Module.finrank ℝ ↥(Submodule.map ((LinearMap.id : E →ₗ[ℝ] E) -
        (S₁.comp Kᗮ.starProjection).toLinearMap) V ⊓ C) = n - 1 ∧
      Module.finrank ℝ ↥(Submodule.map ((LinearMap.id : E →ₗ[ℝ] E) -
        (S₂.comp Kᗮ.starProjection).toLinearMap) W ⊓ C) = n - 1 := by
  classical
  have hR : finrank ℝ ↥(Kᗮ) = n := by
    have h := Submodule.finrank_add_finrank_orthogonal K
    omega
  obtain ⟨φV, hφV⟩ := exists_gr_of_isCompl K V hV
  obtain ⟨φW, hφW⟩ := exists_gr_of_isCompl K W hW
  let Δ : Kᗮ →ₗ[ℝ] K := φV - φW
  let lam : Kᗮ →ₗ[ℝ] ℝ :=
    { toFun := fun r => (inner ℝ u u)⁻¹ * inner ℝ u (Δ r : E)
      map_add' := by
        intro a b
        simp only [map_add, Submodule.coe_add, inner_add_right, mul_add]
      map_smul' := by
        intro c a
        simp only [map_smul, Submodule.coe_smul, real_inner_smul_right, RingHom.id_apply]
        ring_nf }
  let Δu : Kᗮ →ₗ[ℝ] K := (LinearMap.toSpanSingleton ℝ K ⟨u, hu⟩).comp lam
  let β : Kᗮ →ₗ[ℝ] K := Δ - Δu
  have huu : inner ℝ u u ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0)
  have hβval : ∀ r : Kᗮ, (β r : E) = (Δ r : E) - (lam r) • u := by
    intro r
    have h1 : ((Δu r : K) : E) = (lam r) • u := by
      show (((LinearMap.toSpanSingleton ℝ K ⟨u, hu⟩) (lam r) : K) : E) = (lam r) • u
      rw [LinearMap.toSpanSingleton_apply]
      rfl
    rw [show β = Δ - Δu from rfl, LinearMap.sub_apply, Submodule.coe_sub, h1]
  have hβperp : ∀ r : Kᗮ, inner ℝ (β r : E) u = 0 := by
    intro r
    rw [hβval r, inner_sub_left, real_inner_smul_left]
    have hlam : lam r = (inner ℝ u u)⁻¹ * inner ℝ u (Δ r : E) := rfl
    rw [hlam, real_inner_comm u (Δ r : E)]
    have h3 : ((inner ℝ u u)⁻¹ * inner ℝ u (Δ r : E)) * inner ℝ u u = inner ℝ u (Δ r : E) := by
      rw [mul_assoc, mul_comm (inner ℝ u (Δ r : E)) (inner ℝ u u), ← mul_assoc,
        inv_mul_cancel₀ huu, one_mul]
    rw [h3, sub_self]
  have hβmem : ∀ r : Kᗮ, (β r : E) ∈ (Submodule.span ℝ {u})ᗮ := by
    intro r
    rw [Submodule.mem_orthogonal']
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [real_inner_smul_right, hβperp r, mul_zero]
  -- a nonzero functional
  have hKorth_ne : Kᗮ ≠ ⊥ := by
    intro hbot
    have : finrank ℝ ↥(Kᗮ) = 0 := by rw [hbot]; simp
    omega
  obtain ⟨r₀, hr₀mem, hr₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKorth_ne
  let r₁ : Kᗮ := ⟨r₀, hr₀mem⟩
  let ν₀ : Kᗮ →ₗ[ℝ] ℝ :=
    { toFun := fun r => inner ℝ r₀ (r : E)
      map_add' := by intro a b; simp only [map_add, Submodule.coe_add, inner_add_right]
      map_smul' := by intro c a; simp only [map_smul, Submodule.coe_smul, real_inner_smul_right,
        RingHom.id_apply, smul_eq_mul] }
  have hν₀ : ν₀ r₁ ≠ 0 := by
    have h1 : inner ℝ r₀ r₀ ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hr₀ne)
    show inner ℝ r₀ r₀ ≠ 0
    exact h1
  have hνexists : ∃ ν : Kᗮ →ₗ[ℝ] ℝ, ν ≠ 0 ∧ ν ≠ -lam := by
    by_cases hcase : ν₀ = -lam
    · refine ⟨(2:ℝ) • ν₀, ?_, ?_⟩
      · intro h0
        have h1 : ν₀ = 0 := by
          rcases (smul_eq_zero.mp h0) with h2 | h2
          · norm_num at h2
          · exact h2
        rw [h1] at hν₀
        exact hν₀ rfl
      · intro h2
        have h3 : ν₀ r₁ = -(lam r₁) := by
          have hh := congrArg (fun ff : Kᗮ →ₗ[ℝ] ℝ => ff r₁) hcase
          simpa using hh
        have h4 : (2:ℝ) * (ν₀ r₁) = -(lam r₁) := by
          have hh := congrArg (fun ff : Kᗮ →ₗ[ℝ] ℝ => ff r₁) h2
          simpa using hh
        rw [h3] at h4
        have hlam0 : lam r₁ = 0 := by linarith
        rw [hlam0] at h3
        simp at h3
        exact hν₀ h3
    · exact ⟨ν₀, fun h0 => hν₀ (by rw [h0]; rfl), hcase⟩
  obtain ⟨ν, hν0, hnulam⟩ := hνexists
  let νu : Kᗮ →ₗ[ℝ] K := (LinearMap.toSpanSingleton ℝ K ⟨u, hu⟩).comp ν
  let ψC : Kᗮ →ₗ[ℝ] K := φW + Δu + νu
  let S₁ : E →L[ℝ] E :=
    (K.subtype.comp (β.comp (Kᗮ).orthogonalProjectionOnto.toLinearMap)).toContinuousLinearMap
  have hS₁apply : ∀ v : E, S₁ v = (β ((Kᗮ).orthogonalProjectionOnto v) : E) := fun v => rfl
  have hS₁mem : ∀ v : E, S₁ v ∈ K ⊓ (Submodule.span ℝ {u})ᗮ := by
    intro v
    refine Submodule.mem_inf.mpr ⟨(β ((Kᗮ).orthogonalProjectionOnto v)).2, ?_⟩
    rw [hS₁apply v]
    exact hβmem _
  have hpr : ∀ r : Kᗮ, ((Kᗮ).orthogonalProjectionOnto (r : E)) = r := by
    intro r
    apply Subtype.ext
    rw [← Submodule.starProjection_apply]
    exact Submodule.starProjection_eq_self_iff.mpr r.2
  have hS₁van : ∀ a : E, a ∈ Submodule.span ℝ {u} → S₁ a = 0 := by
    intro a ha
    have haK : a ∈ K := (Submodule.span_singleton_le_iff_mem u K).mpr hu ha
    have h0 : (Kᗮ).orthogonalProjectionOnto a = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
      exact haK
    rw [hS₁apply a, h0]
    simp
  have hβeq : restrictK K S₁ (fun v => (hS₁mem v).1) = β := by
    ext r
    rw [restrictK_apply, hS₁apply, hpr r]
  have hφVeq : φV - β = φW + Δu := by
    rw [show β = Δ - Δu from rfl, show Δ = φV - φW from rfl]
    abel
  have hψeq : ψC - νu = φW + Δu := by
    rw [show ψC = φW + Δu + νu from rfl]
    abel
  have hψeq₂ : ψC - (Δu + νu) = φW := by
    rw [show ψC = φW + Δu + νu from rfl]
    abel
  have hm1 : Submodule.map (shear K S₁) V = gr K (ψC - νu) := by
    rw [hφV, map_shear_gr K S₁ (fun v => (hS₁mem v).1) φV, hβeq, hφVeq, hψeq]
  have hβeq₀ : restrictK K (0 : E →L[ℝ] E) (fun v => (by simp : (0 : E →L[ℝ] E) v ∈ K)) = 0 := by
    ext r
    rfl
  have hm2 : Submodule.map (shear K (0 : E →L[ℝ] E)) W = gr K φW := by
    rw [hφW, map_shear_gr K (0 : E →L[ℝ] E)
      (fun v => (by simp : (0 : E →L[ℝ] E) v ∈ K)) φW, hβeq₀]
    simp
  have hνuK : ∀ r : Kᗮ, νu r = (ν r) • (⟨u, hu⟩ : K) := by
    intro r
    show ((LinearMap.toSpanSingleton ℝ K ⟨u, hu⟩) (ν r)) = (ν r) • ⟨u, hu⟩
    rw [LinearMap.toSpanSingleton_apply]
  have hνunz : νu ≠ 0 := by
    intro h0
    apply hν0
    ext r
    have h1 : ((νu r : K) : E) = 0 := by
      have hh := congrArg (fun ff : Kᗮ →ₗ[ℝ] K => ff r) h0
      rw [hh]
      rfl
    have h2 : (ν r) • u = 0 := by
      simpa [hνuK r, Submodule.coe_smul] using h1
    rcases (smul_eq_zero.mp h2) with h3 | h3
    · exact h3
    · exact absurd h3 hu0
  have huk_ne : (⟨u, hu⟩ : K) ≠ 0 := fun hc => hu0 (by simpa using congrArg Subtype.val hc)
  have hrangeK : ∀ f : Kᗮ →ₗ[ℝ] K, f ≠ 0 →
      LinearMap.range f ≤ Submodule.span ℝ ({(⟨u, hu⟩ : K)} : Set K) →
      finrank ℝ ↥(LinearMap.range f) = 1 := by
    intro f hf hle
    have h1 : finrank ℝ ↥(LinearMap.range f)
        ≤ finrank ℝ ↥(Submodule.span ℝ ({(⟨u, hu⟩ : K)} : Set K)) :=
      Submodule.finrank_mono (R := ℝ) hle
    rw [finrank_span_singleton huk_ne] at h1
    have h2 : finrank ℝ ↥(LinearMap.range f) ≠ 0 := by
      intro h2'
      exact hf ((LinearMap.range_eq_bot).mp ((Submodule.finrank_eq_zero).mp h2'))
    omega
  have hrangenu : finrank ℝ ↥(LinearMap.range νu) = 1 := by
    refine hrangeK νu hνunz ?_
    rintro z ⟨r, rfl⟩
    refine Submodule.mem_span_singleton.mpr ?_
    exact ⟨ν r, (hνuK r).symm⟩
  have hsumK : ∀ r : Kᗮ, (Δu + νu) r = (lam r + ν r) • (⟨u, hu⟩ : K) := by
    intro r
    have h1 : Δu r = (lam r) • (⟨u, hu⟩ : K) := by
      show ((LinearMap.toSpanSingleton ℝ K ⟨u, hu⟩) (lam r)) = (lam r) • ⟨u, hu⟩
      rw [LinearMap.toSpanSingleton_apply]
    rw [LinearMap.add_apply, h1, hνuK r, add_smul]
  have hsumE : ∀ r : Kᗮ, ((Δu + νu) r : E) = (lam r + ν r) • u := by
    intro r
    rw [hsumK r, Submodule.coe_smul]
  have hsumne : Δu + νu ≠ 0 := by
    intro h0
    apply hnulam
    ext r
    have h1 : (lam r + ν r) • u = 0 := by
      rw [← hsumE r]
      have hh := congrArg (fun ff : Kᗮ →ₗ[ℝ] K => (ff r : E)) h0
      simpa using hh
    have h4 : lam r + ν r = 0 := by
      rcases (smul_eq_zero.mp h1) with h5 | h5
      · exact h5
      · exact absurd h5 hu0
    exact eq_neg_of_add_eq_zero_right h4
  have hrangesum : finrank ℝ ↥(LinearMap.range (Δu + νu)) = 1 := by
    refine hrangeK (Δu + νu) hsumne ?_
    rintro z ⟨r, rfl⟩
    refine Submodule.mem_span_singleton.mpr ?_
    exact ⟨lam r + ν r, (hsumK r).symm⟩
  refine ⟨S₁, 0, gr K ψC, hS₁mem, ?_, hS₁van, ?_, gr_isCompl K ψC, ?_, ?_⟩
  · intro v
    simp
  · intro a ha
    simp
  · show finrank ℝ ↥(Submodule.map (shear K S₁) V ⊓ gr K ψC) = n - 1
    rw [hm1, inf_comm, finrank_gr_inf_gr_sub K ψC νu, hR, hrangenu]
  · show finrank ℝ ↥(Submodule.map (shear K (0 : E →L[ℝ] E)) W ⊓ gr K ψC) = n - 1
    rw [hm2, inf_comm, ← hψeq₂, finrank_gr_inf_gr_sub K ψC (Δu + νu), hR, hrangesum]


/-! ## Part 5: the fold collar -/

/-- **The fold collar** (corrected after review; see `Drive/Whitney/NOTES_sheetSetupAll_S2.md` §2 (F3), §9). -/
theorem foldCollar {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (h : Work.Whitney.CutPush.HasBigonData n M f W p₁ p₂ q₁ q₂ γ₁ γ₂)
    (hγ₂sm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t)) :
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K C : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) ∧
      IsCompl C K ∧
      Module.finrank ℝ ↥(Submodule.map
        ((fderiv ℝ A (f p₁)).toLinearMap)
        ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range) ⊓ C) = n - 1 ∧
      Module.finrank ℝ ↥(Submodule.map
        ((fderiv ℝ A (f q₁)).toLinearMap)
        ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range) ⊓ C) = n - 1 := by
  classical
  obtain ⟨U, A₀, A₀inv, K, hUo, hUcl, hUarc, hp₁U, hq₁U, hA₀, hA₀inv, hA₀l, hA₀r, hKfin,
    htube⟩ :=
    Work.Drive.Push.tubeFlattening hn f W p₁ p₂ q₁ q₂ γ₁ γ₂ h hγ₂sm hγ₂imm
  have hfp : f p₁ = f p₂ := h.val₁₂
  have hfq : f q₁ = f q₂ := h.val₃₄
  have hxy : f p₁ ≠ f q₁ := by
    intro hcon
    rcases h.clean p₁ q₁ h.mem₁ h.mem₃ hcon with h' | h' | h' | h' | h'
    · exact h.ne₁₃ h'
    · exact h.ne₂₃ h'.2.symm
    · exact h.ne₁₂ h'.1
    · exact h.ne₁₃ h'.1
    · exact h.ne₁₄ h'.1
  have hp₂U : p₂ ∈ U := by
    have h1 : γ₂ 0 ∈ U := hUarc ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩
    rwa [h.arc₂₀] at h1
  have hq₂U : q₂ ∈ U := by
    have h1 : γ₂ 1 ∈ U := hUarc ⟨1, ⟨by norm_num, le_refl 1⟩, rfl⟩
    rwa [h.arc₂₁] at h1
  have hA₀inj : Function.Injective A₀ := fun x y hxy' => by
    have h1 := congrArg A₀inv hxy'
    rwa [hA₀l, hA₀l] at h1
  have hA₀fderiv_inj : ∀ x : EuclideanSpace ℝ (Fin (2*n)),
      Function.Injective (fderiv ℝ A₀ x) := by
    intro x p q hpq
    have h1 : (fderiv ℝ A₀inv (A₀ x)).comp (fderiv ℝ A₀ x)
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2*n))) := by
      have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (2*n)) => A₀inv (A₀ z))
          ((fderiv ℝ A₀inv (A₀ x)).comp (fderiv ℝ A₀ x)) x :=
        (((hA₀inv.differentiable (by simp)).differentiableAt).hasFDerivAt.comp x
          (((hA₀.differentiable (by simp)).differentiableAt).hasFDerivAt))
      have h3 : (fun z : EuclideanSpace ℝ (Fin (2*n)) => A₀inv (A₀ z)) = fun z => z :=
        funext hA₀l
      rw [← h2.fderiv, h3]
      exact fderiv_id
    have h4 := congrArg (fun L : EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) =>
      L (p - q)) h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h4
    have h5 : fderiv ℝ A₀ x (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    rw [h5, map_zero] at h4
    exact sub_eq_zero.mp h4.symm
  -- the four tangent planes, written at the model space
  set X₁ : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p₁).toLinearMap with hX₁
  set X₂ : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p₂).toLinearMap with hX₂
  set X₃ : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f q₁).toLinearMap with hX₃
  set X₄ : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f q₂).toLinearMap with hX₄
  have htransP : X₁ ⊔ X₂ = ⊤ := h.transP
  have htransQ : X₃ ⊔ X₄ = ⊤ := h.transQ
  have hE2 : finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) = 2 * n := by
    rw [finrank_euclideanSpace]
    simp
  have hKp : Submodule.map ((fderiv ℝ A₀ (f p₂)).toLinearMap) X₂ = K :=
    map_fderiv_range_eq_of_tube A₀ hA₀ hA₀fderiv_inj h.smooth h.immersed hKfin
      (Filter.mem_of_superset (hUo.mem_nhds hp₂U) (fun x hx => htube x hx))
  have hKq : Submodule.map ((fderiv ℝ A₀ (f q₂)).toLinearMap) X₄ = K :=
    map_fderiv_range_eq_of_tube A₀ hA₀ hA₀fderiv_inj h.smooth h.immersed hKfin
      (Filter.mem_of_superset (hUo.mem_nhds hq₂U) (fun x hx => htube x hx))
  -- the two planes
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    Submodule.map ((fderiv ℝ A₀ (f p₁)).toLinearMap) X₁ with hVdef
  set Q : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    Submodule.map ((fderiv ℝ A₀ (f q₁)).toLinearMap) X₃ with hQdef
  have hVfin : finrank ℝ ↥V = n := by
    rw [hVdef, map_eq_range_comp]
    rw [LinearMap.finrank_range_of_inj
      (fun a b hab => Subtype.ext ((hA₀fderiv_inj (f p₁)) hab))]
    change finrank ℝ ↥(LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f p₁).toLinearMap) = n
    rw [LinearMap.finrank_range_of_inj (h.immersed p₁)]
    have h2 : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      rw [finrank_euclideanSpace]
      simp
    exact h2
  have hQfin : finrank ℝ ↥Q = n := by
    rw [hQdef, map_eq_range_comp]
    rw [LinearMap.finrank_range_of_inj
      (fun a b hab => Subtype.ext ((hA₀fderiv_inj (f q₁)) hab))]
    change finrank ℝ ↥(LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*n)))) f q₁).toLinearMap) = n
    rw [LinearMap.finrank_range_of_inj (h.immersed q₁)]
    have h2 : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      rw [finrank_euclideanSpace]
      simp
    exact h2
  have hVsup : V ⊔ K = ⊤ := by
    have h1 : fderiv ℝ A₀ (f p₁) = fderiv ℝ A₀ (f p₂) := by rw [hfp]
    rw [hVdef, h1, ← hKp, ← Submodule.map_sup, htransP, Submodule.map_top]
    exact (Submodule.eq_top_iff_finrank_eq).mpr
      (LinearMap.finrank_range_of_inj (hA₀fderiv_inj (f p₂)))
  have hQsup : Q ⊔ K = ⊤ := by
    have h1 : fderiv ℝ A₀ (f q₁) = fderiv ℝ A₀ (f q₂) := by rw [hfq]
    rw [hQdef, h1, ← hKq, ← Submodule.map_sup, htransQ, Submodule.map_top]
    exact (Submodule.eq_top_iff_finrank_eq).mpr
      (LinearMap.finrank_range_of_inj (hA₀fderiv_inj (f q₂)))
  have hVcompl : IsCompl V K := by
    have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) ≤ finrank ℝ ↥V + finrank ℝ ↥K := by
      rw [hE2, hVfin, hKfin]
      omega
    refine (Submodule.isCompl_iff_disjoint V K hdim).mpr ?_
    rw [disjoint_iff]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq V K
    rw [hVsup, hVfin, hKfin, finrank_top] at h1
    exact (Submodule.finrank_eq_zero).mp (by omega)
  have hQcompl : IsCompl Q K := by
    have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) ≤ finrank ℝ ↥Q + finrank ℝ ↥K := by
      rw [hE2, hQfin, hKfin]
      omega
    refine (Submodule.isCompl_iff_disjoint Q K hdim).mpr ?_
    rw [disjoint_iff]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Q K
    rw [hQsup, hQfin, hKfin, finrank_top] at h1
    exact (Submodule.finrank_eq_zero).mp (by omega)

  -- the separating vector
  set u : EuclideanSpace ℝ (Fin (2*n)) := A₀ (f p₁) - A₀ (f q₁) with hudef
  have huK : u ∈ K := K.sub_mem (by rw [hfp]; exact htube p₂ hp₂U)
    (by rw [hfq]; exact htube q₂ hq₂U)
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 : A₀ (f p₁) = A₀ (f q₁) := sub_eq_zero.mp h0
    exact hxy (hA₀inj h1)
  obtain ⟨S₁, S₂, C, hS₁mem, hS₂mem, hS₁van, hS₂van, hCcompl, hCfin₁, hCfin₂⟩ :=
    foldPlanesAux hn hVcompl hQcompl hKfin hE2 u huK hu0
  -- the base plane of the folding shear
  set Psub : Submodule ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    Submodule.span ℝ {u} ⊔ Kᗮ with hPsub
  have hPorth : Psubᗮ ≤ K := by
    rw [hPsub, ← Submodule.inf_orthogonal (Submodule.span ℝ {u}) Kᗮ, Submodule.orthogonal_orthogonal]
    exact inf_le_right
  have hPorth_eq : Psubᗮ = K ⊓ (Submodule.span ℝ {u})ᗮ := by
    rw [hPsub, ← Submodule.inf_orthogonal (Submodule.span ℝ {u}) Kᗮ,
      Submodule.orthogonal_orthogonal, inf_comm]
  have hz : Psub.starProjection (A₀ (f p₁)) ≠ Psub.starProjection (A₀ (f q₁)) := by
    intro heq
    have h1 : Psub.starProjection u = 0 := by
      have h2 : Psub.starProjection u
          = Psub.starProjection (A₀ (f p₁)) - Psub.starProjection (A₀ (f q₁)) := by
        show Psub.starProjection (A₀ (f p₁) - A₀ (f q₁)) = _
        rw [map_sub]
      rw [h2, heq, sub_self]
    have h3 : Psub.starProjection u = u := by
      refine Submodule.starProjection_eq_self_iff.mpr ?_
      rw [hPsub]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ u⟩)
    rw [h3] at h1
    exact hu0 h1
  set T₁p : EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) :=
    S₁.comp (Kᗮ).starProjection with hT₁p
  set T₂p : EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) :=
    S₂.comp (Kᗮ).starProjection with hT₂p
  have hT₁mem : ∀ v : EuclideanSpace ℝ (Fin (2*n)), T₁p v ∈ Psubᗮ := by
    intro v
    rw [hT₁p, ContinuousLinearMap.comp_apply, hPorth_eq]
    exact hS₁mem _
  have hT₂mem : ∀ v : EuclideanSpace ℝ (Fin (2*n)), T₂p v ∈ Psubᗮ := by
    intro v
    rw [hT₂p, ContinuousLinearMap.comp_apply, hPorth_eq]
    exact hS₂mem _
  obtain ⟨g, hgsm, hgmem, hg₁, hg₂⟩ := Work.Drive.Whitney.exists_smooth_fderiv_two
    (Psub.starProjection (A₀ (f p₁))) (Psub.starProjection (A₀ (f q₁))) hz T₁p T₂p hT₁mem hT₂mem
  obtain ⟨Φ, Φinv, hΦsm, hΦinvsm, hΦl, hΦr, hΦform, _hΦinvform⟩ :=
    Work.Whitney.CutPush.exists_global_diffeo_of_base_shear Psub g hgsm hgmem
  -- the derivative of `Φ`
  have hderivΦ : ∀ z, fderiv ℝ Φ z
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2*n))) -
        (fderiv ℝ g (Psub.starProjection z)).comp Psub.starProjection := by
    intro z
    have hΦeq : Φ = fun y : EuclideanSpace ℝ (Fin (2*n)) => y - g (Psub.starProjection y) :=
      funext hΦform
    have hd1 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => y) z :=
      differentiableAt_id
    have hd2 : DifferentiableAt ℝ
        (fun y : EuclideanSpace ℝ (Fin (2*n)) => g (Psub.starProjection y)) z :=
      ((hgsm.differentiable (by simp)).differentiableAt).comp z (Psub.starProjection).differentiableAt
    have h3 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => g (Psub.starProjection y)) z
        = (fderiv ℝ g (Psub.starProjection z)).comp Psub.starProjection := by
      have h4 := fderiv_comp (x := z) (g := g)
        (f := fun y : EuclideanSpace ℝ (Fin (2*n)) => Psub.starProjection y)
        ((hgsm.differentiable (by simp)).differentiableAt) (Psub.starProjection).differentiableAt
      simpa [Function.comp_def, ContinuousLinearMap.fderiv] using h4
    have h8 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => y - g (Psub.starProjection y)) z
        = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => y) z
          - fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => g (Psub.starProjection y)) z :=
      fderiv_sub hd1 hd2
    have hid : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => y) z
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2*n))) := fderiv_id
    rw [hΦeq, h8, hid, h3]

  have hproj_comp : (Kᗮ).starProjection.comp Psub.starProjection = (Kᗮ).starProjection := by
    ext v
    rw [ContinuousLinearMap.comp_apply]
    have hw : v - Psub.starProjection v ∈ K :=
      hPorth (Submodule.sub_starProjection_mem_orthogonal v)
    have h2 : Psub.starProjection v = v - (v - Psub.starProjection v) := by abel
    rw [h2, map_sub, starProj_eq_zero_of_mem_K hw, sub_zero]
  have hshear_eq : (fderiv ℝ Φ (A₀ (f p₁)) :
      EuclideanSpace ℝ (Fin (2*n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2*n))) = shear K S₁ := by
    rw [hderivΦ (A₀ (f p₁)), hg₁]
    show ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2*n)))
      - (S₁.comp (Kᗮ).starProjection).comp Psub.starProjection :
        EuclideanSpace ℝ (Fin (2*n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2*n)))) = shear K S₁
    rw [ContinuousLinearMap.comp_assoc, hproj_comp]
    rfl
  have hshear_eq₂ : (fderiv ℝ Φ (A₀ (f q₁)) :
      EuclideanSpace ℝ (Fin (2*n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2*n))) = shear K S₂ := by
    rw [hderivΦ (A₀ (f q₁)), hg₂]
    show ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2*n)))
      - (S₂.comp (Kᗮ).starProjection).comp Psub.starProjection :
        EuclideanSpace ℝ (Fin (2*n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2*n)))) = shear K S₂
    rw [ContinuousLinearMap.comp_assoc, hproj_comp]
    rfl
  -- the final assembly
  refine ⟨U, (fun y => Φ (A₀ y)), (fun y => A₀inv (Φinv y)), K, C, hUo, hUcl, hUarc, hp₁U,
    hq₁U, ?_, ?_, ?_, ?_, hKfin, ?_, hCcompl, ?_, ?_⟩
  · exact hΦsm.comp hA₀
  · exact hA₀inv.comp hΦinvsm
  · intro y
    show A₀inv (Φinv (Φ (A₀ y))) = y
    rw [hΦl (A₀ y), hA₀l y]
  · intro y
    show Φ (A₀ (A₀inv (Φinv y))) = y
    rw [hA₀r (Φinv y), hΦr y]
  · intro x hx
    show Φ (A₀ (f x)) ∈ K
    rw [hΦform]
    exact K.sub_mem (htube x hx) (hPorth (hgmem _))
  · -- first finrank condition
    change finrank ℝ ↥(Submodule.map
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => Φ (A₀ y)) (f p₁)).toLinearMap)
      X₁ ⊓ C) = n - 1
    rw [map_fderiv_comp_eq (Ψ := Φ) (B := A₀) (x := f p₁) (X := X₁) (g := shear K S₁)
      ((hΦsm.differentiable (by simp)).differentiableAt)
      ((hA₀.differentiable (by simp)).differentiableAt) hshear_eq]
    rw [← hVdef]
    exact hCfin₁
  · -- second finrank condition
    change finrank ℝ ↥(Submodule.map
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2*n)) => Φ (A₀ y)) (f q₁)).toLinearMap)
      X₃ ⊓ C) = n - 1
    rw [map_fderiv_comp_eq (Ψ := Φ) (B := A₀) (x := f q₁) (X := X₃) (g := shear K S₂)
      ((hΦsm.differentiable (by simp)).differentiableAt)
      ((hA₀.differentiable (by simp)).differentiableAt) hshear_eq₂]
    rw [← hQdef]
    exact hCfin₂

end Work.Drive.Whitney
