import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic

/-!
# `Work.KT.Cone.Setup` — structural glue for `Work.KT.cone_exact`

The mapping cone `C_f` of `f : S_V → T` is the pull-back algebra
`coneAlg f = C(T) ×_{C(S_V)} C(D_V)`.  This file collects the elementary structural facts
about it that the proof of `Work.KT.cone_exact` needs:

* Tietze: a continuous `ℂ`-valued function on the unit sphere `S_V` extends to the closed unit
  ball `D_V`; consequently both `coneToT f : C(C_f) → C(T)` and the restriction
  `C(D_V) → C(S_V)` are surjective;
* the algebra `Kpair V = C(D_V/S_V)` is the range of `relToCone f y0 hy0`, with its
  augmentation `ε = augPair V y0`;
* the resulting algebra isomorphism `Kpair V ≃ₐ[ℂ] U`.
-/

namespace Work.KT.Cone

open Work.KT Matrix

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The inclusion `S_V → D_V` of the unit sphere into the closed unit ball. -/
def sphIncl (V : Type) [NormedAddCommGroup V] : C(Sph V, Ball V) where
  toFun x := ⟨(x : V), by
    rw [mem_closedBall_zero_iff]
    have h := Metric.mem_sphere.mp x.2
    rw [dist_eq_norm, sub_zero] at h
    exact le_of_eq h⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] lemma sphIncl_coe (x : Sph V) : (sphIncl V x : V) = (x : V) := rfl

/-- Membership in the unit sphere, in terms of the norm. -/
lemma mem_sphere_one_iff {x : V} : x ∈ Metric.sphere (0 : V) 1 ↔ ‖x‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]

/-- Membership in the boundary sphere of the ball, in terms of the norm. -/
lemma mem_bdry_iff {y : Ball V} : y ∈ bdry V ↔ (y : V) ∈ Metric.sphere (0 : V) 1 := by
  rw [bdry, Set.mem_setOf_eq, mem_sphere_one_iff]

/-- **Tietze.** A continuous `ℂ`-valued function on the unit sphere extends to the closed unit
ball. -/
theorem exists_ball_extension (g : C(Sph V, ℂ)) :
    ∃ G : C(Ball V, ℂ), G.comp (sphIncl V) = g := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq
    (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : V) 1)) g
  refine ⟨F.comp ⟨fun y : Ball V => (y : V), continuous_subtype_val⟩, ?_⟩
  ext x
  have h2 : (ContinuousMap.restrict (Metric.sphere (0 : V) 1) F) x = g x :=
    congrFun (congrArg (fun m : C(Sph V, ℂ) => (m : Sph V → ℂ)) hF) x
  simpa using h2

/-- Restriction of functions on the ball to the sphere, as an algebra map. -/
def restrictSph : C(Ball V, ℂ) →ₐ[ℂ] C(Sph V, ℂ) := pullAlg (sphIncl V)

@[simp] lemma restrictSph_apply (G : C(Ball V, ℂ)) :
    restrictSph (V := V) G = G.comp (sphIncl V) := rfl

/-- Restriction to the sphere is surjective (Tietze). -/
theorem restrictSph_surjective : Function.Surjective (restrictSph (V := V)) := by
  intro g
  obtain ⟨G, hG⟩ := exists_ball_extension (V := V) g
  exact ⟨G, hG⟩

/-- `coneToT f : C(C_f) → C(T)` is surjective (Tietze). -/
theorem coneToT_surjective {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [Nonempty T] (f : C(Sph V, T)) : Function.Surjective (coneToT f) := by
  intro g
  obtain ⟨G, hG⟩ := exists_ball_extension (V := V) (pullAlg f g)
  refine ⟨⟨(g, G), ?_⟩, ?_⟩
  · intro y hy
    have hy1 : (y : V) ∈ Metric.sphere (0 : V) 1 := (mem_bdry_iff (V := V)).mp hy
    have h : G (sphIncl V ⟨(y : V), hy1⟩) = (pullAlg f g) ⟨(y : V), hy1⟩ :=
      congrFun (congrArg (fun m : C(Sph V, ℂ) => (m : Sph V → ℂ)) hG) ⟨(y : V), hy1⟩
    have hy' : sphIncl V ⟨(y : V), hy1⟩ = y := Subtype.ext rfl
    rw [hy'] at h
    simpa [pullAlg] using h
  · rfl

section U

variable {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T] [Nonempty T]
  (f : C(Sph V, T)) (y0 : Ball V) (hy0 : y0 ∈ bdry V)

/-- `U = ℂ·1 + ker (coneToT f)`, realised as the range of `relToCone`. -/
def U : Subalgebra ℂ (coneAlg f) := (relToCone f y0 hy0).range

/-- `relToCone` is injective. -/
lemma relToCone_injective : Function.Injective (relToCone f y0 hy0) := by
  intro a b h
  refine Subtype.ext ?_
  have := congrArg (fun z : coneAlg f => (z : C(T, ℂ) × C(Ball V, ℂ)).2) h
  exact this

@[simp] lemma relToCone_fst (h : Kpair V) :
    ((relToCone f y0 hy0 h : coneAlg f) : C(T, ℂ) × C(Ball V, ℂ)).1
      = Algebra.ofId ℂ C(T, ℂ) (augPair V y0 h) := rfl

@[simp] lemma relToCone_snd (h : Kpair V) :
    ((relToCone f y0 hy0 h : coneAlg f) : C(T, ℂ) × C(Ball V, ℂ)).2
      = (h : C(Ball V, ℂ)) := rfl

/-- `coneToT` of `relToCone h` is the constant function `augPair V y0 h`. -/
@[simp] lemma coneToT_relToCone (h : Kpair V) :
    coneToT f (relToCone f y0 hy0 h) = Algebra.ofId ℂ C(T, ℂ) (augPair V y0 h) := rfl

lemma ofId_apply (c : ℂ) (t : T) : Algebra.ofId ℂ C(T, ℂ) c t = c := rfl

/-- **Structural description of `U`:** an element of `C(C_f)` lies in `U` iff its `C(T)`-component
is constant. -/
theorem mem_U_iff (r : coneAlg f) :
    r ∈ U f y0 hy0 ↔ ∃ c : ℂ, coneToT f r = Algebra.ofId ℂ C(T, ℂ) c := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨augPair V y0 h, rfl⟩
  · rintro ⟨c, hc⟩
    have hconst : (r : C(T, ℂ) × C(Ball V, ℂ)).1 = Algebra.ofId ℂ C(T, ℂ) c := hc
    have hconst_pt : ∀ t : T, (r : C(T, ℂ) × C(Ball V, ℂ)).1 t = c := by
      intro t
      have := congrFun (congrArg (fun m : C(T, ℂ) => (m : T → ℂ)) hconst) t
      simpa using this
    have hbdry : ∀ y : Ball V, y ∈ bdry V → (r : C(T, ℂ) × C(Ball V, ℂ)).2 y = c := by
      intro y hy
      rw [r.2 y hy]
      exact hconst_pt _
    refine ⟨⟨(r : C(T, ℂ) × C(Ball V, ℂ)).2, ?_⟩, ?_⟩
    · intro y hy y' hy'
      rw [hbdry y hy, hbdry y' hy']
    · apply Subtype.ext
      refine Prod.ext ?_ ?_
      · show Algebra.ofId ℂ C(T, ℂ) (augPair V y0 ⟨(r : C(T, ℂ) × C(Ball V, ℂ)).2, _⟩)
          = (r : C(T, ℂ) × C(Ball V, ℂ)).1
        rw [hconst]
        congr 1
        exact hbdry y0 hy0
      · rfl

/-- The augmentation `ε : U → ℂ`, evaluation of the `C(T)`-component at a point of `T`. -/
def eps (t0 : T) : U f y0 hy0 →ₐ[ℂ] ℂ :=
  (evalC t0).comp ((coneToT f).comp (U f y0 hy0).val)

/-- On `U`, `coneToT` is the constant function `ε`. -/
theorem coneToT_val_eq_ofId_eps (t0 : T) (u : U f y0 hy0) :
    coneToT f (u : coneAlg f) = Algebra.ofId ℂ C(T, ℂ) (eps f y0 hy0 t0 u) := by
  obtain ⟨c, hc⟩ := (mem_U_iff f y0 hy0 (u : coneAlg f)).mp u.2
  have hc' : coneToT f ((U f y0 hy0).val u) = Algebra.ofId ℂ C(T, ℂ) c := hc
  have h1 : eps f y0 hy0 t0 u = c := by
    simp only [eps, AlgHom.comp_apply]
    rw [hc']
    rfl
  rw [h1, hc]

/-- The algebra isomorphism `Kpair V ≃ₐ[ℂ] U`. -/
def sigma : Kpair V ≃ₐ[ℂ] U f y0 hy0 :=
  AlgEquiv.ofBijective ((relToCone f y0 hy0).rangeRestrict)
    ⟨fun _a _b h => relToCone_injective f y0 hy0 (Subtype.ext_iff.mp h),
      AlgHom.rangeRestrict_surjective _⟩

@[simp] lemma sigma_apply (h : Kpair V) : (sigma f y0 hy0 h : coneAlg f)
    = relToCone f y0 hy0 h := rfl

/-- `U.val ∘ σ = relToCone`. -/
theorem val_comp_sigma :
    (U f y0 hy0).val.comp (sigma f y0 hy0).toAlgHom = relToCone f y0 hy0 := by
  apply AlgHom.ext
  intro h
  show ((sigma f y0 hy0 h : U f y0 hy0) : coneAlg f) = relToCone f y0 hy0 h
  rw [sigma_apply]

/-- `ε ∘ σ = augPair`. -/
theorem eps_comp_sigma (t0 : T) :
    (eps f y0 hy0 t0).comp (sigma f y0 hy0).toAlgHom = augPair V y0 := by
  apply AlgHom.ext
  intro h
  show (evalC t0) (coneToT f ((sigma f y0 hy0 h : U f y0 hy0) : coneAlg f)) = augPair V y0 h
  rw [sigma_apply]
  rfl

/-- `augPair ∘ σ.symm = ε`. -/
theorem augPair_comp_sigma_symm (t0 : T) :
    (augPair V y0).comp (sigma f y0 hy0).symm.toAlgHom = eps f y0 hy0 t0 := by
  rw [← eps_comp_sigma f y0 hy0 t0, AlgHom.comp_assoc]
  rw [show (sigma f y0 hy0).toAlgHom.comp (sigma f y0 hy0).symm.toAlgHom
      = AlgHom.id ℂ (U f y0 hy0) from AlgEquiv.comp_symm (sigma f y0 hy0)]
  exact AlgHom.comp_id _

/-- `σ.symm ∘ σ = id`. -/
@[simp] theorem sigma_symm_comp :
    (sigma f y0 hy0).symm.toAlgHom.comp (sigma f y0 hy0).toAlgHom = AlgHom.id ℂ (Kpair V) :=
  AlgEquiv.symm_comp _

/-- `σ ∘ σ.symm = id`. -/
@[simp] theorem sigma_comp_symm :
    (sigma f y0 hy0).toAlgHom.comp (sigma f y0 hy0).symm.toAlgHom = AlgHom.id ℂ (U f y0 hy0) :=
  AlgEquiv.comp_symm _


end U

end

end Work.KT.Cone
