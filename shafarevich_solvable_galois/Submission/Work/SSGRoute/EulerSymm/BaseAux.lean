import Mathlib
import Submission.Work.SSGRoute.EulerSymm.Defs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.h1loc_conjLinearMap
import Submission.Work.SSGRoute.LTDDefs.H2locAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The group-theoretic setup of the prime-to-`p` base case

`DC A C = decomp k A ⊓ res⁻¹ C` and `UD A = decomp k A ⊓ Gal(Ω/K)`, together with the conjugation
action of `DC A C` on the local cohomology of `UD A` (degree `1`).
-/

open scoped Pointwise TensorProduct
open Classical

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.EulerSymm

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `D_C = decomp k A ⊓ res⁻¹ C`. -/
abbrev DC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ Subgroup.comap (SSGRoute.res k K) C

/-- `U = decomp k A ⊓ Gal(Ω/K) = decomp k A ⊓ ker(res)`. -/
abbrev UD (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

lemma mem_UD_iff (A : ValuationSubring Ω) (x : Ω ≃ₐ[k] Ω) :
    x ∈ UD k Ω K A ↔ x ∈ SSGRoute.decomp k A ∧ SSGRoute.res k K x = 1 := by
  rw [UD, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : x ∈ (SSGRoute.res k K).ker := by
      rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact h2
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← IntermediateField.restrictNormalHom_ker (E := K)]
    simpa using h2

lemma UD_le_DC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) :
    UD k Ω K A ≤ DC k Ω K A C := by
  intro x hx
  rw [mem_UD_iff] at hx
  rw [DC, Subgroup.mem_inf, Subgroup.mem_comap]
  exact ⟨hx.1, by rw [hx.2]; exact C.one_mem⟩

lemma UD_conj_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    {δ : Ω ≃ₐ[k] Ω} (hδ : δ ∈ DC k Ω K A C) {u : Ω ≃ₐ[k] Ω} (hu : u ∈ UD k Ω K A) :
    δ * u * δ⁻¹ ∈ UD k Ω K A := by
  rw [mem_UD_iff] at hu ⊢
  rw [DC, Subgroup.mem_inf] at hδ
  refine ⟨?_, ?_⟩
  · exact (SSGRoute.decomp k A).mul_mem
      ((SSGRoute.decomp k A).mul_mem hδ.1 hu.1) ((SSGRoute.decomp k A).inv_mem hδ.1)
  · rw [map_mul, map_mul, map_inv, hu.2, mul_one, mul_inv_cancel]

lemma UD_conj_inv_mem (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    {δ : Ω ≃ₐ[k] Ω} (hδ : δ ∈ DC k Ω K A C) {u : Ω ≃ₐ[k] Ω} (hu : u ∈ UD k Ω K A) :
    δ⁻¹ * u * δ ∈ UD k Ω K A := by
  have hδ' : δ⁻¹ ∈ DC k Ω K A C := (DC k Ω K A C).inv_mem hδ
  exact UD_conj_mem k Ω K A C hδ' hu

/-! ## The conjugation action on `H1loc` -/

/-- Conjugation by `σ ∈ D_C` as a linear endomorphism of `H1loc(UD, X)`. -/
def h1ConjEndo (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ DC k Ω K A C) :
    H1loc p k Ω K X (UD k Ω K A) →ₗ[ZMod p] H1loc p k Ω K X (UD k Ω K A) :=
  Classical.choose (h1loc_conjLinearMap p k Ω K (UD k Ω K A) σ
    (fun n hn => UD_conj_mem k Ω K A C hσ hn)
    (fun n hn => UD_conj_inv_mem k Ω K A C hσ hn) X)

lemma h1ConjEndo_toClass (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ DC k Ω K A C)
    {f : (Ω ≃ₐ[k] Ω) → X} (hf : f ∈ lcCocycles p k Ω K X (UD k Ω K A)) :
    h1ConjEndo p k Ω K A C X σ hσ (toClass p k Ω K X (UD k Ω K A) f) =
      toClass p k Ω K X (UD k Ω K A)
        (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) :=
  Classical.choose_spec (h1loc_conjLinearMap p k Ω K (UD k Ω K A) σ
    (fun n hn => UD_conj_mem k Ω K A C hσ hn)
    (fun n hn => UD_conj_inv_mem k Ω K A C hσ hn) X) f hf

instance instSMulDC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    SMul ↥(DC k Ω K A C) (H1loc p k Ω K X (UD k Ω K A)) :=
  ⟨fun γ x => h1ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 x⟩

instance instDistribMulActionDC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    DistribMulAction ↥(DC k Ω K A C) (H1loc p k Ω K X (UD k Ω K A)) where
  one_smul := by
    intro x
    obtain ⟨f, hf, rfl⟩ := toClass_surjective p k Ω K X (UD k Ω K A) x
    show h1ConjEndo p k Ω K A C X (↑(1 : ↥(DC k Ω K A C))) (1 : ↥(DC k Ω K A C)).2
        (toClass p k Ω K X (UD k Ω K A) f) = toClass p k Ω K X (UD k Ω K A) f
    rw [h1ConjEndo_toClass p k Ω K A C X (↑(1 : ↥(DC k Ω K A C)))
      (1 : ↥(DC k Ω K A C)).2 hf]
    congr 1
    funext n
    simp
  mul_smul := by
    intro a b x
    obtain ⟨f, hf, rfl⟩ := toClass_surjective p k Ω K X (UD k Ω K A) x
    have hb : (b : Ω ≃ₐ[k] Ω) ∈ DC k Ω K A C := b.2
    have hg : (fun n => SSGRoute.res k K (b : Ω ≃ₐ[k] Ω) •
        f ((b : Ω ≃ₐ[k] Ω)⁻¹ * n * (b : Ω ≃ₐ[k] Ω))) ∈
        lcCocycles p k Ω K X (UD k Ω K A) :=
      h1locConjShift_mem_lcCocycles p k Ω K X (UD k Ω K A) (b : Ω ≃ₐ[k] Ω)
        (fun n hn => UD_conj_inv_mem k Ω K A C hb hn) hf
    change h1ConjEndo p k Ω K A C X (↑a * ↑b) ((DC k Ω K A C).mul_mem a.2 b.2)
        (toClass p k Ω K X (UD k Ω K A) f) =
      h1ConjEndo p k Ω K A C X (↑a) a.2
        (h1ConjEndo p k Ω K A C X (↑b) b.2 (toClass p k Ω K X (UD k Ω K A) f))
    rw [h1ConjEndo_toClass p k Ω K A C X (↑a * ↑b) ((DC k Ω K A C).mul_mem a.2 b.2) hf,
      h1ConjEndo_toClass p k Ω K A C X (↑b) b.2 hf,
      h1ConjEndo_toClass p k Ω K A C X (↑a) a.2 hg]
    congr 1
    funext n
    rw [show (↑a * ↑b)⁻¹ * n * (↑a * ↑b)
        = (↑b)⁻¹ * ((↑a)⁻¹ * n * ↑a) * ↑b from by group]
    simp only [map_mul, mul_smul]
  smul_zero := by
    intro γ
    show h1ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 0 = 0
    exact map_zero _
  smul_add := by
    intro γ x y
    show h1ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 (x + y) = _ + _
    exact map_add _ _ _

instance instSMulCommClassDC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    SMulCommClass ↥(DC k Ω K A C) (ZMod p) (H1loc p k Ω K X (UD k Ω K A)) where
  smul_comm := by
    intro γ r x
    show h1ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 (r • x)
      = r • (h1ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 x)
    exact map_smul _ _ _

/-! ## The conjugation action on `H2loc` -/

/-- The conjugation shift `c ↦ ((g,h) ↦ res σ • c (σ⁻¹gσ) (σ⁻¹hσ))` on `2`-cochains. -/
def h2ConjShift (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (σ : Ω ≃ₐ[k] Ω) :
    ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X) where
  toFun c g h := SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)
  map_add' c d := by funext g h; simp only [Pi.add_apply, smul_add]
  map_smul' r c := by
    funext g h
    exact smul_comm (SSGRoute.res k K σ) r (c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ))

lemma h2ConjShift_isCocycle2On (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X}
    (hc : IsCocycle2On p k Ω K X N c) :
    IsCocycle2On p k Ω K X N (h2ConjShift p k Ω K X σ c) := by
  intro g hg h hh l hl
  have hg' : σ⁻¹ * g * σ ∈ N := hnorm' g hg
  have hh' : σ⁻¹ * h * σ ∈ N := hnorm' h hh
  have hl' : σ⁻¹ * l * σ ∈ N := hnorm' l hl
  have h1 := hc (σ⁻¹ * g * σ) hg' (σ⁻¹ * h * σ) hh' (σ⁻¹ * l * σ) hl'
  have e1 : (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) = σ⁻¹ * (g * h) * σ := by group
  have e2 : (σ⁻¹ * h * σ) * (σ⁻¹ * l * σ) = σ⁻¹ * (h * l) * σ := by group
  rw [e1, e2] at h1
  have key : SSGRoute.res k K g • (SSGRoute.res k K σ • c (σ⁻¹ * h * σ) (σ⁻¹ * l * σ))
      = SSGRoute.res k K σ •
        (SSGRoute.res k K (σ⁻¹ * g * σ) • c (σ⁻¹ * h * σ) (σ⁻¹ * l * σ)) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show SSGRoute.res k K g • (SSGRoute.res k K σ • c (σ⁻¹ * h * σ) (σ⁻¹ * l * σ))
      - SSGRoute.res k K σ • c (σ⁻¹ * (g * h) * σ) (σ⁻¹ * l * σ)
      + SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * (h * l) * σ)
      - SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ) = 0
  rw [key]
  have hEq : SSGRoute.res k K σ •
        (SSGRoute.res k K (σ⁻¹ * g * σ) • c (σ⁻¹ * h * σ) (σ⁻¹ * l * σ))
      - SSGRoute.res k K σ • c (σ⁻¹ * (g * h) * σ) (σ⁻¹ * l * σ)
      + SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * (h * l) * σ)
      - SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)
      = SSGRoute.res k K σ •
        (SSGRoute.res k K (σ⁻¹ * g * σ) • c (σ⁻¹ * h * σ) (σ⁻¹ * l * σ)
          - c (σ⁻¹ * (g * h) * σ) (σ⁻¹ * l * σ)
          + c (σ⁻¹ * g * σ) (σ⁻¹ * (h * l) * σ)
          - c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)) := by
    rw [smul_sub, smul_add, smul_sub]
  rw [hEq, h1, smul_zero]

lemma h2ConjShift_isLocConst2On (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X}
    (hc : IsLocConst2On p k Ω K X N c) :
    IsLocConst2On p k Ω K X N (h2ConjShift p k Ω K X σ c) := by
  obtain ⟨U, hUo, hU⟩ := hc
  refine ⟨{ carrier := {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_⟩
  · intro x y hx hy
    show σ⁻¹ * (x * y) * σ ∈ U
    rw [show σ⁻¹ * (x * y) * σ = (σ⁻¹ * x * σ) * (σ⁻¹ * y * σ) from by group]
    exact U.mul_mem hx hy
  · show σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ ∈ U
    rw [show σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ = 1 from by group]
    exact U.one_mem
  · intro x hx
    show σ⁻¹ * x⁻¹ * σ ∈ U
    rw [show σ⁻¹ * x⁻¹ * σ = (σ⁻¹ * x * σ)⁻¹ from by group]
    exact U.inv_mem hx
  · have hset : {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
        = (fun z : Ω ≃ₐ[k] Ω => σ⁻¹ * (z * σ)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)) := by
      ext z; simp [mul_assoc]
    change IsOpen {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
    rw [hset]
    exact hUo.preimage (continuous_const.mul (continuous_id.mul continuous_const))
  · intro g hg h hh u hu v hv huN hvN
    have hg' : σ⁻¹ * g * σ ∈ N := hnorm' g hg
    have hh' : σ⁻¹ * h * σ ∈ N := hnorm' h hh
    have hu' : σ⁻¹ * u * σ ∈ U := hu
    have hv' : σ⁻¹ * v * σ ∈ U := hv
    have huN' : σ⁻¹ * u * σ ∈ N := hnorm' u huN
    have hvN' : σ⁻¹ * v * σ ∈ N := hnorm' v hvN
    have e1 : σ⁻¹ * (g * u) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * u * σ) := by group
    have e2 : σ⁻¹ * (h * v) * σ = (σ⁻¹ * h * σ) * (σ⁻¹ * v * σ) := by group
    show SSGRoute.res k K σ • c (σ⁻¹ * (g * u) * σ) (σ⁻¹ * (h * v) * σ)
      = SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)
    rw [e1, e2, hU (σ⁻¹ * g * σ) hg' (σ⁻¹ * h * σ) hh' (σ⁻¹ * u * σ) hu' (σ⁻¹ * v * σ) hv'
      huN' hvN']

lemma h2ConjShift_mem_lcCocycles2 (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X}
    (hc : c ∈ lcCocycles2 p k Ω K X N) :
    h2ConjShift p k Ω K X σ c ∈ lcCocycles2 p k Ω K X N :=
  ⟨h2ConjShift_isCocycle2On p k Ω K X N σ hnorm' hc.1,
    h2ConjShift_isLocConst2On p k Ω K X N σ hnorm' hc.2⟩

lemma h2ConjShift_mem_coboundaries2 (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → X}
    (hc : c ∈ coboundaries2 p k Ω K X N) :
    h2ConjShift p k Ω K X σ c ∈ coboundaries2 p k Ω K X N := by
  obtain ⟨β, hβloc, hβ⟩ := hc
  refine ⟨fun g => SSGRoute.res k K σ • β (σ⁻¹ * g * σ), ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hβloc
    refine ⟨{ carrier := {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, ?_, ?_⟩
    · intro x y hx hy
      show σ⁻¹ * (x * y) * σ ∈ U
      rw [show σ⁻¹ * (x * y) * σ = (σ⁻¹ * x * σ) * (σ⁻¹ * y * σ) from by group]
      exact U.mul_mem hx hy
    · show σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ ∈ U
      rw [show σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ = 1 from by group]; exact U.one_mem
    · intro x hx
      show σ⁻¹ * x⁻¹ * σ ∈ U
      rw [show σ⁻¹ * x⁻¹ * σ = (σ⁻¹ * x * σ)⁻¹ from by group]
      exact U.inv_mem hx
    · have hset : {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
          = (fun z : Ω ≃ₐ[k] Ω => σ⁻¹ * (z * σ)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)) := by
        ext z; simp [mul_assoc]
      change IsOpen {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
      rw [hset]
      exact hUo.preimage (continuous_const.mul (continuous_id.mul continuous_const))
    · intro g hg u hu huN
      have hu' : σ⁻¹ * u * σ ∈ U := hu
      have huN' : σ⁻¹ * u * σ ∈ N := hnorm' u huN
      have e1 : σ⁻¹ * (g * u) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * u * σ) := by group
      show SSGRoute.res k K σ • β (σ⁻¹ * (g * u) * σ) = SSGRoute.res k K σ • β (σ⁻¹ * g * σ)
      rw [e1, hU (σ⁻¹ * g * σ) (hnorm' g hg) (σ⁻¹ * u * σ) hu' huN']
  · intro g hg h hh
    have hg' : σ⁻¹ * g * σ ∈ N := hnorm' g hg
    have hh' : σ⁻¹ * h * σ ∈ N := hnorm' h hh
    have e1 : (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) = σ⁻¹ * (g * h) * σ := by group
    have hrec := hβ (σ⁻¹ * g * σ) hg' (σ⁻¹ * h * σ) hh'
    rw [e1] at hrec
    show SSGRoute.res k K σ • c (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)
      = SSGRoute.res k K g • (SSGRoute.res k K σ • β (σ⁻¹ * h * σ))
        - SSGRoute.res k K σ • β (σ⁻¹ * (g * h) * σ) + SSGRoute.res k K σ • β (σ⁻¹ * g * σ)
    rw [hrec, smul_add, smul_sub]
    have key : SSGRoute.res k K σ • (SSGRoute.res k K (σ⁻¹ * g * σ) • β (σ⁻¹ * h * σ))
        = SSGRoute.res k K g • (SSGRoute.res k K σ • β (σ⁻¹ * h * σ)) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [key]

/-- The conjugation shift as a linear endomorphism of the locally constant `2`-cocycles. -/
def h2ConjCocycles (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) :
    ↥(lcCocycles2 p k Ω K X N) →ₗ[ZMod p] ↥(lcCocycles2 p k Ω K X N) where
  toFun c := ⟨h2ConjShift p k Ω K X σ c.1,
    h2ConjShift_mem_lcCocycles2 p k Ω K X N σ hnorm' c.2⟩
  map_add' c d := Subtype.ext ((h2ConjShift p k Ω K X σ).map_add c.1 d.1)
  map_smul' r c := Subtype.ext ((h2ConjShift p k Ω K X σ).map_smul r c.1)

lemma h2ConjCocycles_mem_cobQ2 (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) :
    cobQ2 p k Ω K X N ≤ (cobQ2 p k Ω K X N).comap
      (h2ConjCocycles p k Ω K X N σ hnorm') := by
  intro x hx
  rw [Submodule.mem_comap] at hx ⊢
  exact h2ConjShift_mem_coboundaries2 p k Ω K X N σ hnorm' hx

/-- Conjugation by `σ ∈ D_C` as a linear endomorphism of `H2loc(UD, X)`. -/
def h2ConjEndo (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ DC k Ω K A C) :
    H2loc p k Ω K X (UD k Ω K A) →ₗ[ZMod p] H2loc p k Ω K X (UD k Ω K A) :=
  Submodule.mapQ (cobQ2 p k Ω K X (UD k Ω K A)) (cobQ2 p k Ω K X (UD k Ω K A))
    (h2ConjCocycles p k Ω K X (UD k Ω K A) σ
      (fun n hn => UD_conj_inv_mem k Ω K A C hσ hn))
    (h2ConjCocycles_mem_cobQ2 p k Ω K X (UD k Ω K A) σ
      (fun n hn => UD_conj_inv_mem k Ω K A C hσ hn))

lemma h2ConjEndo_mkQ (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ DC k Ω K A C)
    (c : ↥(lcCocycles2 p k Ω K X (UD k Ω K A))) :
    h2ConjEndo p k Ω K A C X σ hσ (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c)
      = Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A))
          ⟨h2ConjShift p k Ω K X σ c.1,
            h2ConjShift_mem_lcCocycles2 p k Ω K X (UD k Ω K A) σ
              (fun n hn => UD_conj_inv_mem k Ω K A C hσ hn) c.2⟩ := by
  rw [h2ConjEndo, Submodule.mkQ_apply, Submodule.mapQ_apply]
  exact congrArg (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A))) (Subtype.ext rfl)

instance instSMulDC2 (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    SMul ↥(DC k Ω K A C) (H2loc p k Ω K X (UD k Ω K A)) :=
  ⟨fun γ x => h2ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 x⟩

lemma h2ConjEndo_one (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (c : ↥(lcCocycles2 p k Ω K X (UD k Ω K A))) :
    h2ConjEndo p k Ω K A C X (1 : Ω ≃ₐ[k] Ω) (DC k Ω K A C).one_mem
        (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c)
      = Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c := by
  change Submodule.mapQ (cobQ2 p k Ω K X (UD k Ω K A)) (cobQ2 p k Ω K X (UD k Ω K A))
      (h2ConjCocycles p k Ω K X (UD k Ω K A) (1 : Ω ≃ₐ[k] Ω)
        (fun n hn => UD_conj_inv_mem k Ω K A C (DC k Ω K A C).one_mem hn))
      (h2ConjCocycles_mem_cobQ2 p k Ω K X (UD k Ω K A) (1 : Ω ≃ₐ[k] Ω)
        (fun n hn => UD_conj_inv_mem k Ω K A C (DC k Ω K A C).one_mem hn))
      (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c) = _
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply]
  exact congrArg (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)))
    (Subtype.ext (funext fun g => funext fun h => by
      show SSGRoute.res k K (1 : Ω ≃ₐ[k] Ω) • c.1 (1⁻¹ * g * 1) (1⁻¹ * h * 1) = c.1 g h
      simp))

lemma h2ConjEndo_mul (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (a b : ↥(DC k Ω K A C))
    (c : ↥(lcCocycles2 p k Ω K X (UD k Ω K A))) :
    h2ConjEndo p k Ω K A C X (↑(a * b)) (a * b).2
        (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c)
      = h2ConjEndo p k Ω K A C X (↑a) a.2
          (h2ConjEndo p k Ω K A C X (↑b) b.2
            (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)) c)) := by
  rw [h2ConjEndo, h2ConjEndo, h2ConjEndo]
  simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
  exact congrArg (Submodule.mkQ (cobQ2 p k Ω K X (UD k Ω K A)))
    (Subtype.ext (funext fun g => funext fun h => by
      show SSGRoute.res k K (↑(a * b)) •
            c.1 ((↑(a * b))⁻¹ * g * (↑(a * b))) ((↑(a * b))⁻¹ * h * (↑(a * b)))
          = SSGRoute.res k K (↑a) • (SSGRoute.res k K (↑b) •
            c.1 ((↑b)⁻¹ * ((↑a)⁻¹ * g * ↑a) * ↑b) ((↑b)⁻¹ * ((↑a)⁻¹ * h * ↑a) * ↑b))
      rw [show (↑(a * b) : Ω ≃ₐ[k] Ω) = (↑a : Ω ≃ₐ[k] Ω) * ↑b from rfl]
      rw [show ((↑a : Ω ≃ₐ[k] Ω) * ↑b)⁻¹ * g * ((↑a : Ω ≃ₐ[k] Ω) * ↑b)
        = (↑b)⁻¹ * ((↑a)⁻¹ * g * ↑a) * ↑b from by group]
      rw [show ((↑a : Ω ≃ₐ[k] Ω) * ↑b)⁻¹ * h * ((↑a : Ω ≃ₐ[k] Ω) * ↑b)
        = (↑b)⁻¹ * ((↑a)⁻¹ * h * ↑a) * ↑b from by group]
      rw [map_mul, mul_smul]))

instance instDistribMulActionDC2 (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    DistribMulAction ↥(DC k Ω K A C) (H2loc p k Ω K X (UD k Ω K A)) where
  toSMul := instSMulDC2 p k Ω K A C X
  one_smul := by
    intro x
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (cobQ2 p k Ω K X (UD k Ω K A)) x
    exact h2ConjEndo_one p k Ω K A C X c
  mul_smul := by
    intro a b x
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (cobQ2 p k Ω K X (UD k Ω K A)) x
    exact h2ConjEndo_mul p k Ω K A C X a b c
  smul_zero := by
    intro γ
    show h2ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 0 = 0
    exact map_zero _
  smul_add := by
    intro γ x y
    show h2ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 (x + y) = _ + _
    exact map_add _ _ _

instance instSMulCommClassDC2 (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] :
    SMulCommClass ↥(DC k Ω K A C) (ZMod p) (H2loc p k Ω K X (UD k Ω K A)) where
  smul_comm := by
    intro γ r x
    show h2ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 (r • x)
      = r • (h2ConjEndo p k Ω K A C X (γ : Ω ≃ₐ[k] Ω) γ.2 x)
    exact map_smul _ _ _

end

end Work.SSGRoute.EulerSymm
