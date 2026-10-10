import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.AsTwCoordAt
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotV5.Alpha.CoeffAct
import Submission.Work.MotV5.Alpha.TwistTransport
import Submission.Work.MotV5.Alpha.Transport
import Submission.Work.MotV5.Alpha.kb_algEquiv_extend

set_option linter.unusedVariables false -- v435-speed

/-!
# The `α`-reduction of the LAM node

`Work.MotV5.Alpha.lam_AS_alpha_of` reduces the `α`-semilinear form of the LAM node
(`Work.MotV5.Nodes.lam_AS_alpha`) to the `K`-linear form (`Work.MotV5.Nodes.lam_AS`), which is
supplied as an explicit hypothesis.

Given `θ : F_{f₁} ≃ₐ[𝕜] F_{f₂}` with `θ (algebraMap c) = algebraMap (α c)`, extend `α.symm` to a
`𝕜`-automorphism `σ` of `Kb` and let `Φ` be its coefficient action on `Om D`.  Then
`ψ := Φ ∘ θ : F_{f₁} → Φ(F_{f₂})` is `RatFunc 𝕜`-linear, `Φ(F_{f₂})` is the twist field
`asTwistFieldTrue D (α.symm f₂) τ' σS` for the transported data `τ' = Φ τ₂ Φ⁻¹`,
`σ' = σ σ₂ σ⁻¹`, and that transported data is again admissible.  Applying the `K`-linear LAM node
with the pair `(f₁, α.symm f₂)` therefore gives a nonzero `y` whose Galois coordinates for the class
`f₁ - ε · α.symm f₂` lie on the Klein cone — the conclusion of `lam_AS_alpha`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotV5.Alpha

open IntermediateField

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The conclusion shape of the LAM node (used as an explicit hypothesis of the reduction). -/
def LamConcl (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (g₁ g₂ : RatFunc 𝕜) : Prop :=
  ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (y : Fin 5 → RatFunc 𝕜), y ≠ 0 ∧
    ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
      (Work.MotV.asCoord
        (Work.MotV5.asRoot (g₁ - algebraMap 𝕜 (RatFunc 𝕜) ((ε : ℤ) : 𝕜) * g₂))
        (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0

/-- The `K`-linear LAM node, as an explicit hypothesis. -/
def LamK (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) : Prop :=
  ∀ (g₁ g₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ₁ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜),
    Work.MotV5.ASTwistData 𝕜 D g₁ τ₁ σS σ₁ → Work.MotV5.ASTwistData 𝕜 D g₂ τ₂ σS σ₂ →
    (↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS)) → LamConcl 𝕜 D g₁ g₂

/-- Powers of conjugate automorphisms. -/
theorem conj_pow (D : Work.MotV.KleinData 𝕜) (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (A A' : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hA' : ∀ y : Work.MotV.Om D, A' y = Φ (A (Φ.symm y))) (n : ℕ) (y : Work.MotV.Om D) :
    (A' ^ n) y = Φ ((A ^ n) (Φ.symm y)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, hA' _, AlgEquiv.symm_apply_apply, pow_succ',
      AlgEquiv.mul_apply]

/-- **`α`-reduction of the LAM node.**  From the `K`-linear LAM node, its `α`-semilinear form. -/
theorem lam_AS_alpha_of (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (hLAM : LamK 𝕜 D hD) (f₁ f₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ₁ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D f₁ τ₁ σS σ₁)
    (h2 : Work.MotV5.ASTwistData 𝕜 D f₂ τ₂ σS σ₂)
    (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (θ : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS))
    (hθ : ∀ c : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) c)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) (α c)) :
    LamConcl 𝕜 D f₁ (α.symm f₂) := by
  classical
  -- the extension `σ` of `α.symm` to `Kb 𝕜` and its coefficient action `Φ`
  obtain ⟨σ, hσ⟩ := kb_algEquiv_extend 𝕜 α.symm
  obtain ⟨Φ, hΦc, hΦκ, _⟩ := exists_coeffAut D σ
  have hΦratio : ∀ i : Fin 5, Φ (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i := by
    intro i
    rw [Work.MotV5.asRatio, map_div₀, hΦκ i, hΦκ 0]
  have hΦsymm : ∀ c : Work.MotV.Kb 𝕜,
      Φ.symm (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ.symm c) := by
    intro c
    have h := hΦc (σ.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
  have hcomm : ∀ y : Work.MotV.Om D, Φ (σS y) = σS (Φ y) :=
    coeffAut_comm_shiftOf D hD σS h2.hσS Φ σ hΦc hΦratio
  -- the transported coefficient action `τ'`
  have hτ'lin : ∀ c : RatFunc 𝕜,
      Φ (τ₂ (Φ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)))
        = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c := by
    intro c
    have hsymm : Φ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (α c) := by
      have hΦαc : Φ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (α c))
          = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c := by
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
            (Work.MotV.Om D) (α c),
          hΦc (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c)), hσ (α c),
          AlgEquiv.symm_apply_apply,
          ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
            (Work.MotV.Om D) c]
      exact (AlgEquiv.symm_apply_eq Φ).mpr hΦαc.symm
    rw [hsymm, IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
        (Work.MotV.Om D) (α c),
      h2.hτ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c)),
      AlgEquiv.commutes σ₂ (α c),
      hΦc (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c)), hσ (α c),
      AlgEquiv.symm_apply_apply,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c]
  let τ' : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D :=
    AlgEquiv.ofRingEquiv (f := (Φ * (τ₂.restrictScalars 𝕜) * Φ.symm).toRingEquiv) hτ'lin
  have hτ'val : ∀ x : Work.MotV.Om D, τ' x = Φ (τ₂ (Φ.symm x)) := fun x => by
    show (Φ * (τ₂.restrictScalars 𝕜) * Φ.symm) x = Φ (τ₂ (Φ.symm x))
    simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  -- the transported Artin–Schreier generator `σ'`
  have hσ'lin : ∀ c : RatFunc 𝕜,
      σ (σ₂ (σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)))
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c :=
    fun c => transport_sigma_linear σ σ₂ α.symm hσ c
  let σ' : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜 :=
    AlgEquiv.ofRingEquiv
      (f := (σ * (σ₂.restrictScalars 𝕜) * σ.symm).toRingEquiv) hσ'lin
  have hσ'val : ∀ x : Work.MotV.Kb 𝕜, σ' x = σ (σ₂ (σ.symm x)) := fun x => by
    show (σ * (σ₂.restrictScalars 𝕜) * σ.symm) x = σ (σ₂ (σ.symm x))
    simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  -- the transported data satisfies `ASTwistData`
  have h2' : Work.MotV5.ASTwistData 𝕜 D (α.symm f₂) τ' σS σ' := by
    refine ⟨?_, ?_, ?_, h2.hσS, ?_, ?_, ?_⟩
    · -- `hτ`
      intro c
      rw [hτ'val, hΦsymm, h2.hτ, hΦc, hσ'val]
    · -- `hτk`
      intro x hx
      have h1 : Φ.symm x ∈ Work.MotV5.kleinField D :=
        (coeffAut_kleinField_iff D α.symm σ hσ Φ hΦc hΦratio (Φ.symm x)).mp
          (by rw [AlgEquiv.apply_symm_apply]; exact hx)
      rw [hτ'val, h2.hτk _ h1]
      exact AlgEquiv.apply_symm_apply Φ x
    · -- `hσ`
      rw [hσ'val]
      exact transport_sigma_asRoot f₂ σ σ₂ α.symm hσ h2.hσ
    · -- `h5L`
      intro x hx
      have hx' : Φ.symm x ∈ Work.MotV5.asFieldL D f₂ :=
        (coeffAut_asFieldL_iff D α.symm σ hσ Φ hΦc hΦratio f₂ (Φ.symm x)).mp
          (by rw [AlgEquiv.apply_symm_apply]; exact hx)
      rw [conj_pow D Φ (Work.MotV5.asTwistAction D τ₂ σS) (Work.MotV5.asTwistAction D τ' σS)
          (fun y => asTwistAction_transport D τ₂ σS τ' Φ hτ'val hcomm y) 5 x,
        h2.h5L _ hx', AlgEquiv.apply_symm_apply]
    · -- `hneL`
      obtain ⟨x, hx, hne⟩ := h2.hneL
      refine ⟨Φ x, (coeffAut_asFieldL_iff D α.symm σ hσ Φ hΦc hΦratio f₂ x).mpr hx, ?_⟩
      intro hcon
      have h := asTwistAction_transport D τ₂ σS τ' Φ hτ'val hcomm (Φ x)
      rw [AlgEquiv.symm_apply_apply] at h
      rw [h] at hcon
      exact hne (Φ.injective hcon)
    · -- `hpres`
      intro x hx
      have hx' : Φ.symm x ∈ Work.MotV5.asFieldL D f₂ :=
        (coeffAut_asFieldL_iff D α.symm σ hσ Φ hΦc hΦratio f₂ (Φ.symm x)).mp
          (by rw [AlgEquiv.apply_symm_apply]; exact hx)
      rw [asTwistAction_transport D τ₂ σS τ' Φ hτ'val hcomm x]
      exact (coeffAut_asFieldL_iff D α.symm σ hσ Φ hΦc hΦratio f₂ _).mpr (h2.hpres _ hx')
  -- the transported twist field
  have hTrans : ∀ x : Work.MotV.Om D,
      Φ x ∈ Work.MotV5.asTwistFieldTrue D (α.symm f₂) τ' σS ↔
        x ∈ Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS :=
    fun x => asTwistFieldTrue_transport_iff D hD f₂ τ₂ σS h2.hσS Φ σ hΦc hΦratio α.symm
      hσ τ' hτ'val x
  -- the `RatFunc 𝕜`-linear isomorphism `ψ = Φ ∘ θ`
  have hcoe : ∀ c : RatFunc 𝕜,
      ((algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) c :
          ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) : Work.MotV.Om D)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c := by
    intro c
    rw [← IntermediateField.algebraMap_apply (Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) c)]
    exact (IsScalarTower.algebraMap_apply (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) (Work.MotV.Om D) c).symm
  have hψ_add : ∀ x y : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS),
      Φ (θ (x + y)) = Φ (θ x) + Φ (θ y) := by
    intro x y
    rw [map_add θ]
    change Φ (((θ x : ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) : Work.MotV.Om D)
      + ((θ y : ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) : Work.MotV.Om D))
      = Φ (θ x) + Φ (θ y)
    rw [map_add]
  have hψ_mul : ∀ x y : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS),
      Φ (θ (x * y)) = Φ (θ x) * Φ (θ y) := by
    intro x y
    rw [map_mul θ]
    change Φ (((θ x : ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) : Work.MotV.Om D)
      * ((θ y : ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) : Work.MotV.Om D))
      = Φ (θ x) * Φ (θ y)
    rw [map_mul]
  let ψhom : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) →ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D (α.symm f₂) τ' σS) :=
    { toFun := fun x => ⟨Φ (θ x), (hTrans (θ x)).mpr (θ x).2⟩
      map_one' := by
        apply Subtype.ext
        show Φ (θ (1 : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS))) = (1 : Work.MotV.Om D)
        rw [map_one θ]
        exact map_one Φ
      map_zero' := by
        apply Subtype.ext
        show Φ (θ (0 : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS))) = (0 : Work.MotV.Om D)
        rw [map_zero θ]
        exact map_zero Φ
      map_add' := fun x y => Subtype.ext (hψ_add x y)
      map_mul' := fun x y => Subtype.ext (hψ_mul x y)
      commutes' := fun c => by
        apply Subtype.ext
        show Φ (θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) c))
          = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c
        rw [hθ c, hcoe (α c), coeffAut_algebraMap_K D α.symm σ hσ Φ hΦc (α c),
          AlgEquiv.symm_apply_apply] }
  have hψinj : Function.Injective ψhom := by
    intro x y hxy
    have h1 : Φ (θ x) = Φ (θ y) := congrArg Subtype.val hxy
    exact θ.injective (Subtype.ext (Φ.injective h1))
  have hψsurj : Function.Surjective ψhom := by
    intro y
    have hy : Φ.symm (y : Work.MotV.Om D) ∈ Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS :=
      (hTrans (Φ.symm y)).mp (by rw [AlgEquiv.apply_symm_apply]; exact y.2)
    refine ⟨θ.symm ⟨Φ.symm (y : Work.MotV.Om D), hy⟩, ?_⟩
    apply Subtype.ext
    show Φ (θ (θ.symm ⟨Φ.symm (y : Work.MotV.Om D), hy⟩)) = (y : Work.MotV.Om D)
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  let ψ : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D (α.symm f₂) τ' σS) :=
    AlgEquiv.ofBijective ψhom ⟨hψinj, hψsurj⟩
  exact hLAM f₁ (α.symm f₂) τ₁ τ' σS σ₁ σ' h1 h2' ψ

end Work.MotV5.Alpha
