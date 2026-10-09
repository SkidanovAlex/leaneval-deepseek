import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
import Submission.Work.SSGRoute.PTCore.h3loc_decomp_subsingleton
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.EulerSymm.mackeyIndDecomp
import Submission.Work.SSGRoute.PTembedding.h3_triv_subsingleton_of_units_divisible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# `H³` of the decomposition group in a coefficient module that only carries an action of the
*image* of `D_A` in `Gal(K/k)`

The target

`Subsingleton (H³(D_A, V))`

for a finite `𝔽_p`-module `V` whose `D_A`-action factors through the image
`G_A = res k K (D_A) ≤ Gal(K/k)` is deduced from the arithmetic input

`∀ M [𝔽_p[Gal(K/k)]-module, finite], Subsingleton (H3loc p k Ω K M (decomp k A))`

(`cd_p(G_{k_v}) ≤ 2`) as follows.  `V` is an `𝔽_p[G_A]`-module, so it is a direct summand of the
induced module `W = Ind_{G_A}^{Gal(K/k)} V` (`ArtinInduced.ind`), which *is* an
`𝔽_p[Gal(K/k)]`-module: the equivariant section `indIncl : V → Ind_{G_A}^G V` (supported on `G_A`)
and the equivariant projection `indProj : Ind_{G_A}^G V → V` (evaluation at `1`) satisfy
`indProj ∘ indIncl = id`.  Hence `H³(-)` in coefficients is injective along `indIncl`
(`mapH3_injective_of_leftInverse`), and the vanishing for `W` — the arithmetic input, transported
to the model `H³(↥D_A, W)` by `PTCore.subsingleton_h3loc_iff_subsingleton_H3` — gives the
vanishing for `V`.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-! ## Generalities: `V` is a direct summand of the induced module `Ind_H^G V` -/

section IndGeneral

variable (p : ℕ) (G : Type*) [Group G] (H : Subgroup G)
  (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction ↥H V] [SMulCommClass ↥H (ZMod p) V]

/-- The `H`-equivariant section `V → Ind_H^G V`, sending `v` to the element supported on the
coset `H`, i.e. the function which is `h⁻¹ • v` at `h ∈ H` and `0` outside `H`. -/
def indIncl : V →+ Work.SSGRoute.ArtinInduced.ind p G H V :=
  { toFun := fun v => ⟨fun x => if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • v else 0, by
      intro x h
      show (if hx : x * (h : G) ∈ H then ((⟨x * (h : G), hx⟩ : ↥H))⁻¹ • v else 0)
        = h⁻¹ • (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • v else 0)
      by_cases hx : x ∈ H
      · have hxh : x * (h : G) ∈ H := H.mul_mem hx h.2
        rw [dif_pos hxh, dif_pos hx]
        have h1 : (⟨x * (h : G), hxh⟩ : ↥H) = (⟨x, hx⟩ : ↥H) * h := Subtype.ext rfl
        rw [h1, mul_inv_rev, mul_smul]
      · have hxh : x * (h : G) ∉ H := by
          intro hcon
          have hmem : (x * (h : G)) * (h : G)⁻¹ ∈ H := H.mul_mem hcon (H.inv_mem h.2)
          rw [mul_assoc, mul_inv_cancel, mul_one] at hmem
          exact hx hmem
        simp [dif_neg hxh, dif_neg hx]⟩
    map_zero' := Subtype.ext (funext fun x => by
      show (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • (0:V) else 0) = (0 : G → V) x
      by_cases hx : x ∈ H
      · simp [dif_pos hx]
      · simp [dif_neg hx])
    map_add' := fun v w => Subtype.ext (funext fun x => by
      show (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • (v+w) else 0)
          = (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • v else 0)
            + (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • w else 0)
      by_cases hx : x ∈ H
      · simp [dif_pos hx, smul_add]
      · simp [dif_neg hx]) }

/-- Evaluation at `1`: the `H`-equivariant projection `Ind_H^G V → V`. -/
def indProj : Work.SSGRoute.ArtinInduced.ind p G H V →+ V where
  toFun f := f.1 1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem indProj_indIncl (v : V) : indProj p G H V (indIncl p G H V v) = v := by
  show (if hx : (1:G) ∈ H then ((⟨1, hx⟩ : ↥H))⁻¹ • v else 0) = v
  have h1 : ((⟨1, H.one_mem⟩ : ↥H))⁻¹ = (1 : ↥H) := Subtype.ext (by simp)
  rw [dif_pos H.one_mem, h1, one_smul]

/-- The section `indIncl` is `H`-equivariant (for the action of `H` on `Ind_H^G V` restricted
from `G`). -/
theorem indIncl_smul (h : ↥H) (v : V) :
    indIncl p G H V (h • v) = (h : G) • indIncl p G H V v := by
  refine Subtype.ext (funext fun x => ?_)
  show (if hx : x ∈ H then ((⟨x, hx⟩ : ↥H))⁻¹ • (h • v) else 0)
      = (if hx : (h : G)⁻¹ * x ∈ H then ((⟨(h : G)⁻¹ * x, hx⟩ : ↥H))⁻¹ • v else 0)
  by_cases hx : x ∈ H
  · have hx' : (h : G)⁻¹ * x ∈ H := H.mul_mem (H.inv_mem h.2) hx
    rw [dif_pos hx, dif_pos hx']
    have hb : ((⟨x, hx⟩ : ↥H))⁻¹ * h = ((⟨(h : G)⁻¹ * x, hx'⟩ : ↥H))⁻¹ :=
      Subtype.ext (by simp [mul_inv_rev])
    rw [← mul_smul, hb]
  · have hx' : (h : G)⁻¹ * x ∉ H := by
      intro hcon
      apply hx
      have hmem : ((h : G)) * ((h : G)⁻¹ * x) ∈ H := H.mul_mem h.2 hcon
      rw [← mul_assoc, mul_inv_cancel, one_mul] at hmem
      exact hmem
    simp [dif_neg hx, dif_neg hx']

/-- The projection `indProj` is `H`-equivariant. -/
theorem indProj_smul (h : ↥H) (f : Work.SSGRoute.ArtinInduced.ind p G H V) :
    indProj p G H V ((h : G) • f) = h • indProj p G H V f := by
  show ((h : G) • f).1 1 = h • (f.1 1)
  rw [Work.SSGRoute.ArtinInduced.ind_smul_apply, mul_one]
  have key : f.1 ((h : G)⁻¹) = h • f.1 1 := by
    have h2 := Work.SSGRoute.ArtinInduced.ind_mem p G H V f (1 : G) h⁻¹
    simpa using h2
  rw [key]

end IndGeneral

/-! ## The coefficient module induced from the image of the decomposition group -/

/-- The `𝔽_p[Gal(K/k)]`-module `Ind_{G_A}^{Gal(K/k)} V` induced from the image
`G_A = res k K (D_A) ≤ Gal(K/k)` of the decomposition group; it receives the `G_A`-module `V` as a
direct summand (`indIncl`, `indProj`). -/
abbrev liftCoeff (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (A : ValuationSubring Ω)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction ↥((SSGRoute.decomp k A).map (SSGRoute.res k K)) V]
    [SMulCommClass ↥((SSGRoute.decomp k A).map (SSGRoute.res k K)) (ZMod p) V] : Type _ :=
  Work.SSGRoute.ArtinInduced.ind p (K ≃ₐ[k] K)
    ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V

theorem h3_H3_subsingleton_of_image
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h3 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)))
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    [DistribMulAction ↥((SSGRoute.decomp k A).map (SSGRoute.res k K)) V]
    [SMulCommClass ↥((SSGRoute.decomp k A).map (SSGRoute.res k K)) (ZMod p) V]
    [DistribMulAction ↥(SSGRoute.decomp k A) V]
    (hcompat : ∀ (σ : ↥(SSGRoute.decomp k A)) (v : V),
      σ • v = (⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
        Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩ :
        ↥((SSGRoute.decomp k A).map (SSGRoute.res k K))) • v) :
    Subsingleton (Work.SSGRoute.H3 (M := V) ↥(SSGRoute.decomp k A)) := by
  classical
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  -- The canonical action of `D_A` on the induced module, through `res k K`.
  letI : DistribMulAction ↥(SSGRoute.decomp k A) (liftCoeff p k Ω K A V) :=
    SSGRoute.decompDistribMulAction K (liftCoeff p k Ω K A V) A
  -- The arithmetical input, for the induced module.
  have hsub_loc : Subsingleton
      (Work.SSGRoute.H3loc p k Ω K (liftCoeff p k Ω K A V) (SSGRoute.decomp k A)) :=
    h3 (liftCoeff p k Ω K A V)
  -- Transport to the standard model `H³(↥D_A, ·)`.
  have hH : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A
  have hcompatW : ∀ (σ : ↥(SSGRoute.decomp k A)) (m : liftCoeff p k Ω K A V),
      σ • m = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • m :=
    fun σ m => SSGRoute.decomp_smul_eq_res K (liftCoeff p k Ω K A V) A σ m
  have hsub_W : Subsingleton
      (Work.SSGRoute.H3 (M := liftCoeff p k Ω K A V) ↥(SSGRoute.decomp k A)) :=
    (Work.SSGRoute.PTCore.subsingleton_h3loc_iff_subsingleton_H3 p k Ω K
      (liftCoeff p k Ω K A V) (SSGRoute.decomp k A) hH hcompatW).mp hsub_loc
  -- The equivariant section, the equivariant projection, and `indProj ∘ indIncl = id`.
  have hincl : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) := by
    intro σ v
    have hW : ∀ w : liftCoeff p k Ω K A V,
        σ • w = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • w := fun w => hcompatW σ w
    rw [hW, hcompat σ v]
    exact indIncl_smul p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V
      ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
        Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩ v
  have hproj : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      (indProj p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) := by
    intro σ f
    have hW : σ • f = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f := hcompatW σ f
    rw [hW, hcompat σ (indProj p (K ≃ₐ[k] K)
      ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V f)]
    exact indProj_smul p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V
      ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
        Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩ f
  have hleft : ∀ v : V, indProj p (K ≃ₐ[k] K)
      ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V v) = v :=
    fun v => indProj_indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V v
  have hinj : Function.Injective (Work.SSGRoute.H3Map.mapH3
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) hincl) :=
    Work.SSGRoute.PTembedding.mapH3_injective_of_leftInverse
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) hincl
      (indProj p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) hproj hleft
  exact ⟨fun a b => hinj (hsub_W.elim
    (Work.SSGRoute.H3Map.mapH3
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) hincl a)
    (Work.SSGRoute.H3Map.mapH3
      (indIncl p (K ≃ₐ[k] K) ((SSGRoute.decomp k A).map (SSGRoute.res k K)) V) hincl b))⟩

end

end Work.SSGRoute.PT
