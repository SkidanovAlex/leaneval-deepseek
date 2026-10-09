import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.nonempty_galois_completion_equiv
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer

/-!
# The decomposition group embeds in the group of local automorphisms

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L`, the
decomposition group `D_w` acts on the completion `L_w` by `K_v`-algebra automorphisms, and this
action is faithful.  This file constructs that action explicitly -- by extending the action of a
prime-preserving automorphism of `L` (which preserves the `w`-adic valuation, see
`Work.LocalFields.valuation_smul_of_mem_stabilizer`) to the completion `L_w` and checking
`K_v`-linearity by density -- and deduces the existence of an injective group homomorphism
`D_w →* (L_w ≃ₐ[K_v] L_w)`.

## Main result

* `Work.LocalFields.completionAut_injective` : `D_w` embeds into `Gal(L_w/K_v)`.
-/

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private theorem ucont_vc {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued R Γ₀] (f : R →+* R) (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  simp only [map_zero] at hs
  rw [Valued.mem_nhds_zero] at hs ⊢
  obtain ⟨γ, hγ⟩ := hs
  refine ⟨γ, fun x hx => hγ ?_⟩
  change Valued.v.restrict (f x) < ↑γ
  have h1 : MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict (f x))
      = MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x) := by
    rw [Valuation.embedding_restrict, Valuation.embedding_restrict, hf]
  have key : Valued.v.restrict (f x) = Valued.v.restrict x :=
    MonoidWithZeroHom.ValueGroup₀.embedding_injective h1
  rw [key]
  exact hx

private noncomputable def toWithVal (w : FinitePrime L) (g : decompositionGroup K w) :
    WithVal (w.valuation L) ≃+* WithVal (w.valuation L) :=
  ((WithVal.equiv (w.valuation L)).trans (g.1).toRingEquiv).trans
    (WithVal.equiv (w.valuation L)).symm

private theorem toWithVal_apply (w : FinitePrime L) (g : decompositionGroup K w)
    (x : WithVal (w.valuation L)) :
    toWithVal w g x = WithVal.toVal (w.valuation L) (g.1 x.ofVal) := rfl

private theorem toWithVal_val (w : FinitePrime L) (g : decompositionGroup K w) :
    ∀ x, Valued.v (toWithVal w g x) = Valued.v x := by
  intro x
  rw [toWithVal_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal (w.valuation L) x]
  exact valuation_smul_of_mem_stabilizer w g.1 g.2 x.ofVal

private theorem toWithVal_ucont (w : FinitePrime L) (g : decompositionGroup K w) :
    UniformContinuous (toWithVal w g : WithVal (w.valuation L) → WithVal (w.valuation L)) :=
  ucont_vc (toWithVal w g : WithVal (w.valuation L) →+* WithVal (w.valuation L))
    (toWithVal_val w g)

private theorem toWithVal_continuous (w : FinitePrime L) (g : decompositionGroup K w) :
    Continuous (toWithVal w g : WithVal (w.valuation L) → WithVal (w.valuation L)) :=
  (toWithVal_ucont w g).continuous

private theorem toWithVal_continuous_symm (w : FinitePrime L) (g : decompositionGroup K w) :
    Continuous ((toWithVal w g).symm : WithVal (w.valuation L) → WithVal (w.valuation L)) :=
  (ucont_vc ((toWithVal w g).symm : WithVal (w.valuation L) →+* WithVal (w.valuation L))
    (fun x => by
      have h := toWithVal_val w g ((toWithVal w g).symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm)).continuous

private theorem toWithVal_mul_apply (w : FinitePrime L) (g₁ g₂ : decompositionGroup K w)
    (x : WithVal (w.valuation L)) :
    toWithVal w (g₁ * g₂) x = toWithVal w g₁ (toWithVal w g₂ x) := by
  rw [toWithVal_apply, toWithVal_apply, toWithVal_apply, Subgroup.coe_mul]
  rfl

private theorem toWithVal_one (w : FinitePrime L) :
    toWithVal w (1 : decompositionGroup K w) = 1 := by
  refine RingEquiv.ext (fun x => ?_)
  rw [toWithVal_apply]
  simp

private theorem toWithVal_injective (w : FinitePrime L) : Function.Injective (toWithVal (K := K) w) := by
  intro g₁ g₂ h
  refine Subtype.ext (AlgEquiv.ext (fun y => ?_))
  have h' := congrArg (fun e => e (WithVal.toVal (w.valuation L) y)) h
  rw [toWithVal_apply, toWithVal_apply] at h'
  exact WithVal.toVal_injective (w.valuation L) h'

private noncomputable def completionEquiv (w : FinitePrime L) (g : decompositionGroup K w) :
    (w.valuation L).Completion ≃+* (w.valuation L).Completion :=
  UniformSpace.Completion.mapRingEquiv (toWithVal w g) (toWithVal_continuous w g)
    (toWithVal_continuous_symm w g)

private theorem completionEquiv_mul (w : FinitePrime L) (g₁ g₂ : decompositionGroup K w) :
    completionEquiv w (g₁ * g₂) = (completionEquiv w g₂).trans (completionEquiv w g₁) := by
  refine RingEquiv.ext (fun x => ?_)
  rw [RingEquiv.trans_apply]
  simp only [completionEquiv, UniformSpace.Completion.mapRingEquiv_apply]
  have hfun : (⇑(toWithVal w g₁) ∘ ⇑(toWithVal w g₂)) = ⇑(toWithVal w (g₁ * g₂)) := by
    funext y; exact (toWithVal_mul_apply w g₁ g₂ y).symm
  rw [show UniformSpace.Completion.map (⇑(toWithVal w g₁))
        (UniformSpace.Completion.map (⇑(toWithVal w g₂)) x)
      = (UniformSpace.Completion.map (⇑(toWithVal w g₁)) ∘
          UniformSpace.Completion.map (⇑(toWithVal w g₂))) x from rfl,
    UniformSpace.Completion.map_comp (toWithVal_ucont w g₁) (toWithVal_ucont w g₂), hfun]

private theorem completionEquiv_coe (w : FinitePrime L) (g : decompositionGroup K w)
    (x : WithVal (w.valuation L)) :
    completionEquiv w g (x : (w.valuation L).Completion) =
      (toWithVal w g x : (w.valuation L).Completion) := by
  rw [completionEquiv, UniformSpace.Completion.mapRingEquiv_apply]
  exact UniformSpace.Completion.map_coe (toWithVal_ucont w g) x

private theorem completionEquiv_one (w : FinitePrime L) :
    completionEquiv w (1 : decompositionGroup K w) = 1 := by
  refine RingEquiv.ext (fun x => ?_)
  rw [completionEquiv, UniformSpace.Completion.mapRingEquiv_apply, toWithVal_one]
  rw [show (⇑(1 : WithVal (w.valuation L) ≃+* WithVal (w.valuation L)))
      = (id : WithVal (w.valuation L) → WithVal (w.valuation L)) from rfl]
  rw [UniformSpace.Completion.map_id]
  rfl

private noncomputable def completionAut (w : FinitePrime L) (g : decompositionGroup K w) :
    Completion L w ≃+* Completion L w :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).trans
    ((completionEquiv w g).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm)

private theorem completionAut_mul (w : FinitePrime L) (g₁ g₂ : decompositionGroup K w) :
    completionAut w (g₁ * g₂) = (completionAut w g₂).trans (completionAut w g₁) := by
  refine RingEquiv.ext (fun x => ?_)
  have hmul : ∀ y, completionEquiv w (g₁ * g₂) y
      = completionEquiv w g₁ (completionEquiv w g₂ y) := fun y => by
    rw [completionEquiv_mul, RingEquiv.trans_apply]
  simp only [completionAut, RingEquiv.trans_apply]
  rw [RingEquiv.apply_symm_apply, hmul]

private theorem completionAut_one (w : FinitePrime L) :
    completionAut w (1 : decompositionGroup K w) = 1 := by
  refine RingEquiv.ext (fun x => ?_)
  show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm
      (completionEquiv w 1 ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w) x)) = x
  rw [completionEquiv_one]
  have h : (1 : (w.valuation L).Completion ≃+* (w.valuation L).Completion)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w) x)
      = (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w) x := by simp
  rw [h, RingEquiv.symm_apply_apply]

private theorem completionAut_coe (w : FinitePrime L) (g : decompositionGroup K w) (y : L) :
    completionAut w g (y : Completion L w) = (g.1 y : Completion L w) := by
  have hx : (y : Completion L w) = IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
      (WithVal.toVal (w.valuation L) y) := rfl
  rw [hx]
  show IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
      (completionEquiv w g (WithVal.toVal (w.valuation L) y : (w.valuation L).Completion)) = _
  rw [completionEquiv_coe, toWithVal_apply]
  try rfl

private theorem completionAut_continuous (w : FinitePrime L) (g : decompositionGroup K w) :
    Continuous (completionAut w g : Completion L w → Completion L w) := by
  have h2 : Continuous (completionEquiv w g :
      (w.valuation L).Completion → (w.valuation L).Completion) := by
    have hfun : (⇑(completionEquiv w g) : (w.valuation L).Completion →
        (w.valuation L).Completion) = UniformSpace.Completion.map (⇑(toWithVal w g)) := by
      funext y; rw [completionEquiv, UniformSpace.Completion.mapRingEquiv_apply]
    rw [hfun]
    exact UniformSpace.Completion.continuous_map
  have key : (⇑(completionAut w g) : Completion L w → Completion L w)
      = (fun y => IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y) ∘
        ((⇑(completionEquiv w g)) ∘
          (fun x => IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion x)) := rfl
  rw [key]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (h2.comp (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L w))

private theorem completionEquiv_eq_conj (w : FinitePrime L) (g : decompositionGroup K w) :
    completionEquiv w g =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm.trans
        ((completionAut w g).trans
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w)) := by
  refine RingEquiv.ext (fun x => ?_)
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [show (completionAut w g)
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm x)
      = (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm
          (completionEquiv w g ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w)
            ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm x))) from rfl]
  simp only [RingEquiv.apply_symm_apply]

private theorem completionAut_map_injective (w : FinitePrime L) :
    Function.Injective (completionAut (K := K) w) := by
  intro g₁ g₂ h
  apply toWithVal_injective (K := K) w
  refine RingEquiv.ext (fun x => ?_)
  have hce : completionEquiv w g₁ = completionEquiv w g₂ := by
    rw [completionEquiv_eq_conj w g₁, completionEquiv_eq_conj w g₂, h]
  have hx : (toWithVal w g₁ x : (w.valuation L).Completion)
      = (toWithVal w g₂ x : (w.valuation L).Completion) := by
    have h' := congrArg (fun e : (w.valuation L).Completion ≃+* (w.valuation L).Completion =>
      e (x : (w.valuation L).Completion)) hce
    rwa [completionEquiv_coe, completionEquiv_coe] at h'
  exact UniformSpace.Completion.coe_inj.mp hx

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
private theorem algebraMap_completion_eq_coe (w : FinitePrime L)
    (c : K) :
    (algebraMap K (Completion L w)) c = (algebraMap K L c : Completion L w) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (𝓞 L) L (v := w)]
  rfl

private theorem completionAut_ringHom (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (g : decompositionGroup K w)
    (a : Completion K v) :
    completionAut w g (CompletionHom.ringHom v w a) = CompletionHom.ringHom v w a := by
  have hdense : DenseRange (fun c : K => algebraMap K (Completion K v) c) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v
  have hcont1 : Continuous (fun a : Completion K v =>
      completionAut w g (CompletionHom.ringHom v w a)) :=
    (completionAut_continuous w g).comp (CompletionHom.continuous_ringHom v w)
  have heq : (fun a : Completion K v => completionAut w g (CompletionHom.ringHom v w a)) ∘
      (fun c : K => algebraMap K (Completion K v) c)
      = (CompletionHom.ringHom v w) ∘ (fun c : K => algebraMap K (Completion K v) c) := by
    funext c
    simp only [Function.comp_apply]
    rw [CompletionHom.ringHom_algebraMap, algebraMap_completion_eq_coe w]
    rw [completionAut_coe, AlgEquiv.commutes]
  have h := DenseRange.equalizer hdense hcont1 (CompletionHom.continuous_ringHom v w) heq
  exact congrFun h a

private theorem completionAut_algebraMap (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (g : decompositionGroup K w)
    (a : Completion K v) :
    completionAut w g (algebraMap (Completion K v) (Completion L w) a) =
      algebraMap (Completion K v) (Completion L w) a := by
  have h : (algebraMap (Completion K v) (Completion L w)) = CompletionHom.ringHom v w :=
    RingHom.algebraMap_toAlgebra (CompletionHom.ringHom v w)
  rw [h]
  exact completionAut_ringHom v w g a

private noncomputable def completionAutEquiv (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (g : decompositionGroup K w) :
    (Completion L w ≃ₐ[Completion K v] Completion L w) :=
  AlgEquiv.ofRingEquiv (f := completionAut w g) (completionAut_algebraMap v w g)

private theorem completionAutEquiv_apply (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (g : decompositionGroup K w) (x : Completion L w) :
    completionAutEquiv v w g x = completionAut w g x :=
  AlgEquiv.ofRingEquiv_apply (completionAut_algebraMap v w g) x

private theorem completionAutEquiv_coe (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (g : decompositionGroup K w) :
    ((completionAutEquiv v w g : Completion L w ≃+* Completion L w)) = completionAut w g := by
  refine RingEquiv.ext (fun x => ?_)
  rw [show ((completionAutEquiv v w g : Completion L w ≃+* Completion L w)) x
      = completionAutEquiv v w g x from rfl]
  rw [completionAutEquiv_apply]

private noncomputable def completionAutHom (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    decompositionGroup K w →* (Completion L w ≃ₐ[Completion K v] Completion L w) where
  toFun := completionAutEquiv v w
  map_one' := by
    refine AlgEquiv.ext (fun x => ?_)
    rw [completionAutEquiv_apply, completionAut_one]
    rfl
  map_mul' g₁ g₂ := by
    refine AlgEquiv.ext (fun x => ?_)
    rw [AlgEquiv.mul_apply, completionAutEquiv_apply, completionAutEquiv_apply,
      completionAutEquiv_apply, completionAut_mul]
    rfl

private theorem completionAutHom_injective (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] : Function.Injective (completionAutHom v w) := by
  intro g₁ g₂ h
  have h' : completionAut w g₁ = completionAut w g₂ := by
    have hce : completionAutEquiv v w g₁ = completionAutEquiv v w g₂ := h
    have h2 := congrArg (fun e : Completion L w ≃ₐ[Completion K v] Completion L w =>
      (e : Completion L w ≃+* Completion L w)) hce
    rwa [completionAutEquiv_coe v w g₁, completionAutEquiv_coe v w g₂] at h2
  exact completionAut_map_injective (K := K) w h'

theorem completionAut_injective {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    ∃ Φ : Work.LocalFields.decompositionGroup K w →*
        (Work.LocalFields.Completion L w ≃ₐ[Work.LocalFields.Completion K v]
          Work.LocalFields.Completion L w), Function.Injective Φ :=
  ⟨completionAutHom v w, completionAutHom_injective v w⟩

end Work.LocalFields
