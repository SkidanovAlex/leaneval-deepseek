import Mathlib
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.map_topologicalClosure_zpowers_subtype
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-! ## The abstract gauge algebra

Let `Γ` be a group with a homomorphism `ρ : Γ →* G` into a group `G` acting on the abelian group
`M`.  For a `2`-cochain `c`, a cochain `E` and its coboundary `d¹E = cob`, the whole gauge
computation is an identity in the additive group `M`. -/

namespace GaugeAlg

variable {Γ G M : Type*} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The inhomogeneous coboundary `d¹E` of a `1`-cochain. -/
def cob (ρ : Γ →* G) (E : Γ → M) (g h : Γ) : M := ρ g • E h - E (g * h) + E g

/-- `d¹` of anything is a `2`-cocycle. -/
theorem cob_cocycle (ρ : Γ →* G) (E : Γ → M) (g h l : Γ) :
    ρ g • cob ρ E h l - cob ρ E (g * h) l + cob ρ E g (h * l) - cob ρ E g h = 0 := by
  simp only [cob]
  rw [map_mul, mul_smul, ← mul_assoc]
  simp only [smul_add, smul_sub]
  abel

/-- The `M`-component of the gauge cochain on a product of coordinates `i * γ`. -/
def Ec (ρ : Γ →* G) (c : Γ → Γ → M) (β χ : Γ → M) (i γ : Γ) : M :=
  β i - ρ i • χ γ - c i γ

variable {ρ : Γ →* G}

/-- Normalised cocycles kill the first variable. -/
theorem coc_one_left {D : Subgroup Γ} {c : Γ → Γ → M}
    (hcc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g * h) l + c g (h * l) - c g h = 0)
    (hc11 : c 1 1 = 0) {h : Γ} (hh : h ∈ D) : c 1 h = 0 := by
  have h := hcc 1 D.one_mem 1 D.one_mem h hh
  rw [one_mul, map_one, one_smul, hc11] at h
  simpa using h

/-- The general normalisation identity `c g 1 = ρ g • c 1 1`. -/
theorem coc_one_right {D : Subgroup Γ} {c : Γ → Γ → M}
    (hcc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g * h) l + c g (h * l) - c g h = 0)
    {g : Γ} (hg : g ∈ D) : c g 1 = ρ g • c 1 1 := by
  have h := hcc g hg 1 D.one_mem 1 D.one_mem
  rw [mul_one, one_mul] at h
  have h' : ρ g • c 1 1 - c g 1 = 0 := by rw [← h]; abel
  exact (sub_eq_zero.mp h').symm

/-- The cocycle identity solved for `c (g * h) l`. -/
theorem coc_mul_left {D : Subgroup Γ} {c : Γ → Γ → M}
    (hcc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g * h) l + c g (h * l) - c g h = 0)
    {g h l : Γ} (hg : g ∈ D) (hh : h ∈ D) (hl : l ∈ D) :
    c (g * h) l = ρ g • c h l + c g (h * l) - c g h := by
  have hcoc := hcc g hg h hh l hl
  have key : c (g * h) l - (ρ g • c h l + c g (h * l) - c g h)
      = -(ρ g • c h l - c (g * h) l + c g (h * l) - c g h) := by abel
  have h2 : c (g * h) l - (ρ g • c h l + c g (h * l) - c g h) = 0 := by
    rw [key, hcoc, neg_zero]
  exact sub_eq_zero.mp h2

/-- The standard consequence `ρ g • c g⁻¹ g = c g g⁻¹` of a normalised cocycle. -/
theorem coc_inv_self {D : Subgroup Γ} {c : Γ → Γ → M}
    (hcc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g * h) l + c g (h * l) - c g h = 0)
    (hc11 : c 1 1 = 0) {g : Γ} (hg : g ∈ D) : ρ g • c g⁻¹ g = c g g⁻¹ := by
  have hg' : g⁻¹ ∈ D := D.inv_mem hg
  have h := hcc g hg g⁻¹ hg' g hg
  rw [mul_inv_cancel, inv_mul_cancel] at h
  have h1 : c 1 g = 0 := coc_one_left hcc hc11 hg
  have h2 : c g 1 = 0 := by rw [coc_one_right hcc hg, hc11, smul_zero]
  rw [h1, h2] at h
  have key : ρ g • c g⁻¹ g - c g g⁻¹ = 0 := by rw [← h]; abel
  exact sub_eq_zero.mp key

/-- `β 1 = 0` for a primitive `β` of a normalised cocycle. -/
theorem beta_one {I : Subgroup Γ} {c : Γ → Γ → M} {β : Γ → M}
    (hβ : ∀ n ∈ I, ∀ m ∈ I, ρ n • β m - β (n * m) + β n = c n m) (hc11 : c 1 1 = 0) :
    β 1 = 0 := by
  have h := hβ 1 I.one_mem 1 I.one_mem
  rw [one_mul, map_one, one_smul, hc11] at h
  have key : β 1 = 0 := by rw [← h]; abel
  exact key

/-- The primitive identity solved for `β (n * m)`. -/
theorem beta_mul {I : Subgroup Γ} {c : Γ → Γ → M} {β : Γ → M}
    (hβ : ∀ n ∈ I, ∀ m ∈ I, ρ n • β m - β (n * m) + β n = c n m) {n m : Γ}
    (hn : n ∈ I) (hm : m ∈ I) : β (n * m) = ρ n • β m + β n - c n m := by
  have h := hβ n hn m hm
  rw [← h]; abel

/-- `χ 1 = 0` for a `c`-twisted crossed homomorphism and a normalised `c`. -/
theorem chi_one {C : Subgroup Γ} {c : Γ → Γ → M} {χ : Γ → M}
    (hχ1 : ∀ γ ∈ C, ∀ δ ∈ C, χ (γ * δ) = χ γ + ρ γ • χ δ + c γ δ) (hc11 : c 1 1 = 0) :
    χ 1 = 0 := by
  have h := hχ1 1 C.one_mem 1 C.one_mem
  rw [mul_one, map_one, one_smul, hc11, add_zero] at h
  have h2 : χ 1 + (0 : M) = χ 1 + χ 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **The core gauge computation (row form).** -/
theorem ec_row {D I C : Subgroup Γ} {c : Γ → Γ → M} {β χ : Γ → M}
    (hID : I ≤ D) (hCD : C ≤ D)
    (hnorm : ∀ δ ∈ D, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hcc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D,
      ρ g • c h l - c (g * h) l + c g (h * l) - c g h = 0)
    (hβ1 : β 1 = 0)
    (hc1 : ∀ γ ∈ C, c 1 γ = 0)
    (hχ1 : ∀ γ ∈ C, ∀ δ ∈ C, χ (γ * δ) = χ γ + ρ γ • χ δ + c γ δ)
    {γ : Γ} (hγC : γ ∈ C)
    (hDrel : ∀ n ∈ I, ρ γ • β n - β (γ * n * γ⁻¹) + ρ (γ * n * γ⁻¹) • χ γ - χ γ
      + c (γ * n * γ⁻¹) γ = c γ n)
    (i : ↥I) (γ' : ↥C) :
    ρ γ • (β (i : Γ) - ρ (i : Γ) • χ (γ' : Γ) - c (i : Γ) (γ' : Γ))
      - (β (γ * (i : Γ) * γ⁻¹) - ρ (γ * (i : Γ) * γ⁻¹) • χ (γ * (γ' : Γ))
        - c (γ * (i : Γ) * γ⁻¹) (γ * (γ' : Γ)))
      + (β 1 - ρ 1 • χ γ - c 1 γ)
    = c γ ((i : Γ) * (γ' : Γ)) := by
  have hiD : (i : Γ) ∈ D := hID i.2
  have hγD : γ ∈ D := hCD hγC
  have hγ'D : (γ' : Γ) ∈ D := hCD γ'.2
  have hjI : γ * (i : Γ) * γ⁻¹ ∈ I := hnorm γ hγD (i : Γ) i.2
  have hjD : γ * (i : Γ) * γ⁻¹ ∈ D := hID hjI
  have hcc1 := hcc γ hγD (i : Γ) hiD (γ' : Γ) hγ'D
  have hcc2 := hcc (γ * (i : Γ) * γ⁻¹) hjD γ hγD (γ' : Γ) hγ'D
  have hβsol : β (γ * (i : Γ) * γ⁻¹) =
      ρ γ • β (i : Γ) + ρ (γ * (i : Γ) * γ⁻¹) • χ γ - χ γ
        + c (γ * (i : Γ) * γ⁻¹) γ - c γ (i : Γ) := by
    rw [← hDrel (i : Γ) i.2]; abel
  have hZ2 : c γ ((i : Γ) * (γ' : Γ)) =
      -(ρ γ • c (i : Γ) (γ' : Γ)) + c (γ * (i : Γ)) (γ' : Γ) + c γ (i : Γ) := by
    have key : c γ ((i : Γ) * (γ' : Γ)) -
        (-(ρ γ • c (i : Γ) (γ' : Γ)) + c (γ * (i : Γ)) (γ' : Γ) + c γ (i : Γ))
        = (ρ γ • c (i : Γ) (γ' : Γ) - c (γ * (i : Γ)) (γ' : Γ)
            + c γ ((i : Γ) * (γ' : Γ)) - c γ (i : Γ)) := by abel
    have h2 : c γ ((i : Γ) * (γ' : Γ)) -
        (-(ρ γ • c (i : Γ) (γ' : Γ)) + c (γ * (i : Γ)) (γ' : Γ) + c γ (i : Γ)) = 0 := by
      rw [key, hcc1]
    exact sub_eq_zero.mp h2
  have hZ : c (γ * (i : Γ)) (γ' : Γ) =
      ρ (γ * (i : Γ) * γ⁻¹) • c γ (γ' : Γ)
        + c (γ * (i : Γ) * γ⁻¹) (γ * (γ' : Γ)) - c (γ * (i : Γ) * γ⁻¹) γ := by
    have h2' : γ * (i : Γ) = (γ * (i : Γ) * γ⁻¹) * γ := by group
    have key : c ((γ * (i : Γ) * γ⁻¹) * γ) (γ' : Γ) -
        (ρ (γ * (i : Γ) * γ⁻¹) • c γ (γ' : Γ)
          + c (γ * (i : Γ) * γ⁻¹) (γ * (γ' : Γ)) - c (γ * (i : Γ) * γ⁻¹) γ)
        = -(ρ (γ * (i : Γ) * γ⁻¹) • c γ (γ' : Γ) - c ((γ * (i : Γ) * γ⁻¹) * γ) (γ' : Γ)
            + c (γ * (i : Γ) * γ⁻¹) (γ * (γ' : Γ)) - c (γ * (i : Γ) * γ⁻¹) γ) := by abel
    have h2 : c ((γ * (i : Γ) * γ⁻¹) * γ) (γ' : Γ) -
        (ρ (γ * (i : Γ) * γ⁻¹) • c γ (γ' : Γ)
          + c (γ * (i : Γ) * γ⁻¹) (γ * (γ' : Γ)) - c (γ * (i : Γ) * γ⁻¹) γ) = 0 := by
      rw [key, hcc2, neg_zero]
    rw [← h2'] at h2
    exact sub_eq_zero.mp h2
  have hρ : ρ (γ * (i : Γ) * γ⁻¹) • (ρ γ • χ (γ' : Γ))
      = ρ γ • (ρ (i : Γ) • χ (γ' : Γ)) := by
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hβsol, hχ1 γ hγC (γ' : Γ) γ'.2, hZ2, hZ, hβ1, hc1 γ hγC, map_one, one_smul]
  simp only [smul_sub, smul_add]
  rw [hρ]
  abel

end GaugeAlg

/-- A function which is locally constant on a subgroup `H` is locally constant after composition
with a continuous map landing in `H`. -/
lemma gauge_lc_comp
    {Γ : Type*} [TopologicalSpace Γ] [Group Γ] [ContinuousConstSMul Γ Γ]
    {Y : Type*} {H : Subgroup Γ} {f : Γ → Y}
    (hf : ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
      ∀ g ∈ H, ∀ u ∈ U, u ∈ H → f (g * u) = f g)
    {α : Type*} [TopologicalSpace α] (φ : α → Γ)
    (hφ : Continuous φ) (hφH : ∀ x, φ x ∈ H) :
    IsLocallyConstant (fun x => f (φ x)) := by
  obtain ⟨U, hUo, hU⟩ := hf
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨φ ⁻¹' ((φ x) • (U : Set Γ)), hφ.isOpen_preimage _ (hUo.smul (φ x)), ?_, ?_⟩
  · exact ⟨1, U.one_mem, by simp⟩
  · intro x' hx'
    obtain ⟨u, hu, hxu⟩ := hx'
    have huH : u ∈ H := by
      have hxu' : (φ x) * u = φ x' := hxu
      rw [eq_inv_mul_of_mul_eq hxu']
      exact H.mul_mem (H.inv_mem (hφH x)) (hφH x')
    show f (φ x') = f (φ x)
    rw [show φ x' = φ x * u from hxu.symm]
    exact hU (φ x) (hφH x) u hu huH

/-- A two-variable function which is locally constant on a subgroup `H` is locally constant after
composition with a continuous map into `H × H`. -/
lemma gauge_lc2_comp
    {Γ : Type*} [TopologicalSpace Γ] [Group Γ] [ContinuousConstSMul Γ Γ]
    {Y : Type*} {H : Subgroup Γ} {c : Γ → Γ → Y}
    (hc : ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
      ∀ g ∈ H, ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ U, u ∈ H → v ∈ H → c (g * u) (h * v) = c g h)
    {α : Type*} [TopologicalSpace α] (φ : α → Γ × Γ)
    (hφ : Continuous φ) (hφH : ∀ x, (φ x).1 ∈ H ∧ (φ x).2 ∈ H) :
    IsLocallyConstant (fun x => c (φ x).1 (φ x).2) := by
  obtain ⟨U, hUo, hU⟩ := hc
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨φ ⁻¹' (((φ x).1 • (U : Set Γ)) ×ˢ ((φ x).2 • (U : Set Γ))),
    hφ.isOpen_preimage _ ((hUo.smul (φ x).1).prod (hUo.smul (φ x).2)), ?_, ?_⟩
  · exact ⟨⟨1, U.one_mem, by simp⟩, ⟨1, U.one_mem, by simp⟩⟩
  · intro x' hx'
    obtain ⟨hx'1, hx'2⟩ := hx'
    obtain ⟨u, hu, hxu⟩ := hx'1
    obtain ⟨v, hv, hxv⟩ := hx'2
    have huH : u ∈ H := by
      have hxu' : (φ x).1 * u = (φ x').1 := hxu
      rw [eq_inv_mul_of_mul_eq hxu']
      exact H.mul_mem (H.inv_mem (hφH x).1) (hφH x').1
    have hvH : v ∈ H := by
      have hxv' : (φ x).2 * v = (φ x').2 := hxv
      rw [eq_inv_mul_of_mul_eq hxv']
      exact H.mul_mem (H.inv_mem (hφH x).2) (hφH x').2
    show c (φ x').1 (φ x').2 = c (φ x).1 (φ x).2
    rw [show (φ x').1 = (φ x).1 * u from hxu.symm,
        show (φ x').2 = (φ x).2 * v from hxv.symm]
    exact hU (φ x).1 (hφH x).1 (φ x).2 (hφH x).2 u hu v hv huH hvH

/-- The restriction map `res k K : G_k →* Gal(K/k)` is locally constant (its kernel is the open
subgroup `K.fixingSubgroup`). -/
lemma gauge_res_lc
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] :
    IsLocallyConstant (SSGRoute.res k K : (Ω ≃ₐ[k] Ω) → (K ≃ₐ[k] K)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨g • (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)),
    ?_, ⟨1, MonoidHom.mem_ker.mpr (map_one _), by simp⟩, ?_⟩
  · refine IsOpen.smul ?_ g
    rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
      IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isOpen K
  · intro g' hg'
    obtain ⟨u, hu, hgu⟩ := hg'
    rw [show g' = g * u from hgu.symm, map_mul, MonoidHom.mem_ker.mp hu, mul_one]

/-- Local constancy on the whole group, in the `IsLocConstOn ⊤` form. -/
lemma gauge_lc_top
    {Γ : Type*} [TopologicalSpace Γ] [Group Γ] [ContinuousConstSMul Γ Γ]
    {Y : Type*} {f : Γ → Y}
    (hf : ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
      ∀ g ∈ (⊤ : Subgroup Γ), ∀ u ∈ U, u ∈ (⊤ : Subgroup Γ) → f (g * u) = f g) :
    IsLocallyConstant f :=
  gauge_lc_comp (α := Γ) hf id continuous_id (fun _ => trivial)

/-! ## The structural context -/

/-- The structural hypotheses of the gauge construction, bundled. -/
structure Ctx (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] where
  A : ValuationSubring Ω
  I : Subgroup (Ω ≃ₐ[k] Ω)
  σ : Ω ≃ₐ[k] Ω
  hI : I ≤ SSGRoute.decomp k A
  hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I
  hσ : σ ∈ SSGRoute.decomp k A
  hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ)
  hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥

namespace Ctx

/-- The procyclic closed subgroup `C = closure (zpowers σ)`. -/
abbrev CC (X : Ctx p k Ω K M) : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers X.σ)

/-- The decomposition group `D = decomp k A`. -/
abbrev DD (X : Ctx p k Ω K M) : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k X.A

theorem CC_le_DD (X : Ctx p k Ω K M) : X.CC ≤ X.DD := SSGRoute.HS.CC_le_DD X.A X.σ X.hσ

/-- The `I`-coordinate of an element of `D`. -/
def ipD (X : Ctx p k Ω K M) (d : ↥X.DD) : ↥X.I :=
  SSGRoute.HS.ip X.A X.I X.σ X.hI X.hnorm (SSGRoute.HS.CC_le_DD X.A X.σ X.hσ) X.hsup d

/-- The `C`-coordinate of an element of `D`. -/
def projD (X : Ctx p k Ω K M) (d : ↥X.DD) : ↥X.CC :=
  SSGRoute.HS.proj X.A X.I X.σ X.hI X.hnorm (SSGRoute.HS.CC_le_DD X.A X.σ X.hσ) X.hsup d

theorem ipD_mul_projD (X : Ctx p k Ω K M) (d : ↥X.DD) :
    (X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω) :=
  SSGRoute.HS.ip_mul_proj X.A X.I X.σ X.hI X.hnorm (SSGRoute.HS.CC_le_DD X.A X.σ X.hσ) X.hsup d

theorem projD_mul (X : Ctx p k Ω K M) (d₁ d₂ : ↥X.DD) : X.projD (d₁ * d₂) = X.projD d₁ * X.projD d₂ :=
  SSGRoute.HS.proj_mul X.A X.I X.σ X.hI X.hnorm (SSGRoute.HS.CC_le_DD X.A X.σ X.hσ) X.hsup X.hinf d₁ d₂

/-- Uniqueness of the coordinates: an element of `D` which is a product `i * γ` has coordinates
`i` and `γ`. -/
theorem ipD_projD_unique (X : Ctx p k Ω K M) {d : ↥X.DD} {i : ↥X.I} {γ : ↥X.CC}
    (h : (i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω)) :
    X.ipD d = i ∧ X.projD d = γ := by
  obtain ⟨h1, h2⟩ := SSGRoute.HS.factor_unique X.A X.I X.σ X.hinf
    (X.ipD d).2 i.2 (X.projD d).2 γ.2 (by rw [X.ipD_mul_projD d, h])
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- Multiplication formula for the `I`-coordinate. -/
theorem ipD_mul (X : Ctx p k Ω K M) (d₁ d₂ : ↥X.DD) :
    X.ipD (d₁ * d₂) = X.ipD d₁ * ⟨(X.projD d₁ : Ω ≃ₐ[k] Ω) * (X.ipD d₂ : Ω ≃ₐ[k] Ω)
      * (X.projD d₁ : Ω ≃ₐ[k] Ω)⁻¹, X.hnorm (X.projD d₁ : Ω ≃ₐ[k] Ω)
        (X.CC_le_DD (X.projD d₁).2) (X.ipD d₂ : Ω ≃ₐ[k] Ω) (X.ipD d₂).2⟩ := by
  obtain ⟨h1, -⟩ := X.ipD_projD_unique (d := d₁ * d₂)
    (i := X.ipD d₁ * ⟨(X.projD d₁ : Ω ≃ₐ[k] Ω) * (X.ipD d₂ : Ω ≃ₐ[k] Ω)
      * (X.projD d₁ : Ω ≃ₐ[k] Ω)⁻¹, X.hnorm (X.projD d₁ : Ω ≃ₐ[k] Ω)
        (X.CC_le_DD (X.projD d₁).2) (X.ipD d₂ : Ω ≃ₐ[k] Ω) (X.ipD d₂).2⟩)
    (γ := X.projD d₁ * X.projD d₂) (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (X.ipD d₁ : Ω ≃ₐ[k] Ω) *
            (⟨(X.projD d₁ : Ω ≃ₐ[k] Ω) * (X.ipD d₂ : Ω ≃ₐ[k] Ω)
              * (X.projD d₁ : Ω ≃ₐ[k] Ω)⁻¹, _⟩ : ↥X.I)
            * ((X.projD d₁ : Ω ≃ₐ[k] Ω) * (X.projD d₂ : Ω ≃ₐ[k] Ω))
          = ((X.ipD d₁ : Ω ≃ₐ[k] Ω) * (X.projD d₁ : Ω ≃ₐ[k] Ω))
            * ((X.ipD d₂ : Ω ≃ₐ[k] Ω) * (X.projD d₂ : Ω ≃ₐ[k] Ω)) := by group
        _ = (d₁ : Ω ≃ₐ[k] Ω) * (d₂ : Ω ≃ₐ[k] Ω) := by
              rw [X.ipD_mul_projD d₁, X.ipD_mul_projD d₂])
  exact h1

theorem mem_mul_of_mem (X : Ctx p k Ω K M) (i : ↥X.I) (γ : ↥X.CC) :
    ((i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)) ∈ X.DD :=
  X.DD.mul_mem (X.hI i.2) (X.CC_le_DD γ.2)

theorem ipD_of_mul (X : Ctx p k Ω K M) (i : ↥X.I) (γ : ↥X.CC) :
    X.ipD ⟨(i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω), X.mem_mul_of_mem i γ⟩ = i :=
  (X.ipD_projD_unique (d := ⟨_, X.mem_mul_of_mem i γ⟩) (i := i) (γ := γ) rfl).1

theorem projD_of_mul (X : Ctx p k Ω K M) (i : ↥X.I) (γ : ↥X.CC) :
    X.projD ⟨(i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω), X.mem_mul_of_mem i γ⟩ = γ :=
  (X.ipD_projD_unique (d := ⟨_, X.mem_mul_of_mem i γ⟩) (i := i) (γ := γ) rfl).2

theorem ipD_of_I (X : Ctx p k Ω K M) (i : ↥X.I) : X.ipD ⟨(i : Ω ≃ₐ[k] Ω), X.hI i.2⟩ = i := by
  simpa using X.ipD_of_mul i 1

theorem projD_of_I (X : Ctx p k Ω K M) (i : ↥X.I) : X.projD ⟨(i : Ω ≃ₐ[k] Ω), X.hI i.2⟩ = 1 := by
  simpa using X.projD_of_mul i 1

theorem ipD_of_C (X : Ctx p k Ω K M) (γ : ↥X.CC) : X.ipD ⟨(γ : Ω ≃ₐ[k] Ω), X.CC_le_DD γ.2⟩ = 1 := by
  simpa using X.ipD_of_mul 1 γ

theorem projD_of_C (X : Ctx p k Ω K M) (γ : ↥X.CC) : X.projD ⟨(γ : Ω ≃ₐ[k] Ω), X.CC_le_DD γ.2⟩ = γ := by
  simpa using X.projD_of_mul 1 γ

/-- The element `σ` of `C`. -/
abbrev sigmaC (X : Ctx p k Ω K M) : ↥X.CC := ⟨X.σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers X.σ)⟩

/-- Extension of a function on `C` by `0`. -/
def chiExt (X : Ctx p k Ω K M) (χ : ↥X.CC → M) : (Ω ≃ₐ[k] Ω) → M :=
  fun g => if h : g ∈ X.CC then χ ⟨g, h⟩ else 0

theorem chiExt_apply_coe (X : Ctx p k Ω K M) (χ : ↥X.CC → M) (γ : ↥X.CC) :
    X.chiExt χ (γ : Ω ≃ₐ[k] Ω) = χ γ := by
  rw [chiExt, dif_pos γ.2]

/-! ## The gauge cochain -/

/-- The gauge cochain evaluated using the coordinates of `D`. -/
def GEd (X : Ctx p k Ω K M) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (χ : ↥X.CC → M)
    (d : ↥X.DD) : M :=
  β (X.ipD d : Ω ≃ₐ[k] Ω) - SSGRoute.res k K (X.ipD d : Ω ≃ₐ[k] Ω) • χ (X.projD d)
    - c (X.ipD d : Ω ≃ₐ[k] Ω) (X.projD d : Ω ≃ₐ[k] Ω)

/-- The gauge cochain, extended by `0` off `D`. -/
def GE (X : Ctx p k Ω K M) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (χ : ↥X.CC → M)
    (g : Ω ≃ₐ[k] Ω) : M :=
  if h : g ∈ X.DD then X.GEd c β χ ⟨g, h⟩ else 0

theorem GE_apply (X : Ctx p k Ω K M) (c β χ) (d : ↥X.DD) : X.GE c β χ (d : Ω ≃ₐ[k] Ω) = X.GEd c β χ d := by
  rw [GE, dif_pos d.2]

theorem GEd_of_mul (X : Ctx p k Ω K M) (c β χ) (i : ↥X.I) (γ : ↥X.CC) :
    X.GEd c β χ ⟨(i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω), X.mem_mul_of_mem i γ⟩
      = β (i : Ω ≃ₐ[k] Ω) - SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • χ γ
        - c (i : Ω ≃ₐ[k] Ω) (γ : Ω ≃ₐ[k] Ω) := by
  rw [GEd, X.ipD_of_mul i γ, X.projD_of_mul i γ]

theorem GE_of_mul (X : Ctx p k Ω K M) (c β χ) (i : ↥X.I) (γ : ↥X.CC) :
    X.GE c β χ ((i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω))
      = β (i : Ω ≃ₐ[k] Ω) - SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • χ γ
        - c (i : Ω ≃ₐ[k] Ω) (γ : Ω ≃ₐ[k] Ω) := by
  rw [GE, dif_pos (X.mem_mul_of_mem i γ)]
  exact X.GEd_of_mul c β χ i γ

theorem GEd_of_I (X : Ctx p k Ω K M) (c β χ) (i : ↥X.I) (hχ0 : χ 1 = 0) (hc1 : c (i : Ω ≃ₐ[k] Ω) 1 = 0) :
    X.GEd c β χ ⟨(i : Ω ≃ₐ[k] Ω), X.hI i.2⟩ = β (i : Ω ≃ₐ[k] Ω) := by
  rw [GEd, X.ipD_of_I i, X.projD_of_I i]
  simp [hχ0, hc1]

theorem GE_of_I (X : Ctx p k Ω K M) (c β χ) (i : ↥X.I) (hχ0 : χ 1 = 0) (hc1 : c (i : Ω ≃ₐ[k] Ω) 1 = 0) :
    X.GE c β χ (i : Ω ≃ₐ[k] Ω) = β (i : Ω ≃ₐ[k] Ω) := by
  rw [GE, dif_pos (X.hI i.2)]
  exact X.GEd_of_I c β χ i hχ0 hc1

theorem GEd_of_C (X : Ctx p k Ω K M) (c β χ) (γ : ↥X.CC)
    (hβ1 : β 1 = 0) (hc1 : c 1 (γ : Ω ≃ₐ[k] Ω) = 0) :
    X.GEd c β χ ⟨(γ : Ω ≃ₐ[k] Ω), X.CC_le_DD γ.2⟩ = -χ γ := by
  rw [GEd, X.ipD_of_C γ, X.projD_of_C γ]
  simp [hβ1, hc1]

theorem GE_of_C (X : Ctx p k Ω K M) (c β χ) (γ : ↥X.CC)
    (hβ1 : β 1 = 0) (hc1 : c 1 (γ : Ω ≃ₐ[k] Ω) = 0) :
    X.GE c β χ (γ : Ω ≃ₐ[k] Ω) = -χ γ := by
  rw [GE, dif_pos (X.CC_le_DD γ.2)]
  exact X.GEd_of_C c β χ γ hβ1 hc1

/-- `χ 1 = 0` for a `c`-twisted crossed homomorphism on `C`. -/
theorem chi_zero (X : Ctx p k Ω K M) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (χ : ↥X.CC → M)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (hc11 : c 1 1 = 0) : χ 1 = 0 := by
  have h := hχ1 1 1
  rw [mul_one, Subgroup.coe_one, map_one, one_smul, hc11, add_zero] at h
  have h2 : χ 1 + (0 : M) = χ 1 + χ 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-! ## The relation `(d)` -/

/-- The relation `(d)` at `γ ∈ C`: the transgression condition of the gauge. -/
def Drel (X : Ctx p k Ω K M) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (χ : ↥X.CC → M)
    (γ : ↥X.CC) : Prop :=
  ∀ n : ↥X.I, SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • β (n : Ω ≃ₐ[k] Ω)
      - β ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹)
      + SSGRoute.res k K ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) • χ γ
      - χ γ
      + c ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) (γ : Ω ≃ₐ[k] Ω)
    = c (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)

/-- `Drel` is exactly the statement that the gauge coboundary is `c` in the row of `γ`. -/
theorem Drel_iff_cob (X : Ctx p k Ω K M) (c β χ) (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (γ : ↥X.CC) :
    X.Drel c β χ γ ↔ ∀ n : ↥X.I,
      GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
        = c (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω) := by
  have hβ1 : β 1 = 0 := GaugeAlg.beta_one hβ hc11
  have hχ0 : χ 1 = 0 := X.chi_zero c χ hχ1 hc11
  have hcn1 : ∀ n : ↥X.I, c (n : Ω ≃ₐ[k] Ω) 1 = 0 := fun n => by
    rw [GaugeAlg.coc_one_right hcc (X.hI n.2), hc11, smul_zero]
  have hc1c : c 1 (γ : Ω ≃ₐ[k] Ω) = 0 := GaugeAlg.coc_one_left hcc hc11 (X.CC_le_DD γ.2)
  have key : ∀ n : ↥X.I,
      GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
        = (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • β (n : Ω ≃ₐ[k] Ω)
            - β ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹)
            + SSGRoute.res k K ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) • χ γ
            - χ γ
            + c ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) (γ : Ω ≃ₐ[k] Ω)) := by
    intro n
    have hn : X.GE c β χ (n : Ω ≃ₐ[k] Ω) = β (n : Ω ≃ₐ[k] Ω) := X.GE_of_I c β χ n hχ0 (hcn1 n)
    have hγ : X.GE c β χ (γ : Ω ≃ₐ[k] Ω) = -χ γ := X.GE_of_C c β χ γ hβ1 hc1c
    have hj : ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) ∈ X.I :=
      X.hnorm (γ : Ω ≃ₐ[k] Ω) (X.CC_le_DD γ.2) (n : Ω ≃ₐ[k] Ω) n.2
    rw [GaugeAlg.cob, hn, hγ]
    nth_rewrite 1 [show (γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω)
        = (⟨(γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹, hj⟩ : ↥X.I)
          * (γ : Ω ≃ₐ[k] Ω) from by group]
    rw [X.GE_of_mul c β χ ⟨_, hj⟩ γ,
      show ((⟨(γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹, hj⟩ : ↥X.I) :
          Ω ≃ₐ[k] Ω) = (γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹ from rfl]
    abel
  simp only [Drel, key]
/-- The row of `γ ∈ C`: if `(d)` holds at `γ` then the gauge coboundary is `c` in the whole
`γ`-row.  This is the `i₁ = 1` case of the core computation `GaugeAlg.ec_row`. -/
theorem cob_row (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    {γ : ↥X.CC} (h : X.Drel c β χ γ) :
    ∀ d : ↥X.DD, GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω) (d : Ω ≃ₐ[k] Ω)
      = c (γ : Ω ≃ₐ[k] Ω) (d : Ω ≃ₐ[k] Ω) := by
  intro d
  have hβ1 : β 1 = 0 := GaugeAlg.beta_one hβ hc11
  have hχ0 : χ 1 = 0 := X.chi_zero c χ hχ1 hc11
  have hcn1 : ∀ i : ↥X.I, c (i : Ω ≃ₐ[k] Ω) 1 = 0 := fun i => by
    rw [GaugeAlg.coc_one_right hcc (X.hI i.2), hc11, smul_zero]
  have h1c : ∀ u ∈ X.CC, c 1 (u : Ω ≃ₐ[k] Ω) = 0 := fun u hu =>
    GaugeAlg.coc_one_left hcc hc11 (X.CC_le_DD hu)
  have hDrel : ∀ n ∈ X.I, SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • β n
      - β ((γ : Ω ≃ₐ[k] Ω) * n * (γ : Ω ≃ₐ[k] Ω)⁻¹)
      + SSGRoute.res k K ((γ : Ω ≃ₐ[k] Ω) * n * (γ : Ω ≃ₐ[k] Ω)⁻¹)
        • (X.chiExt χ) (γ : Ω ≃ₐ[k] Ω)
      - (X.chiExt χ) (γ : Ω ≃ₐ[k] Ω)
      + c ((γ : Ω ≃ₐ[k] Ω) * n * (γ : Ω ≃ₐ[k] Ω)⁻¹) (γ : Ω ≃ₐ[k] Ω)
      = c (γ : Ω ≃ₐ[k] Ω) n := by
    intro n hn
    simpa only [X.chiExt_apply_coe χ γ] using h ⟨n, hn⟩
  have hjI : (γ : Ω ≃ₐ[k] Ω) * (X.ipD d : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹ ∈ X.I :=
    X.hnorm (γ : Ω ≃ₐ[k] Ω) (X.CC_le_DD γ.2) (X.ipD d : Ω ≃ₐ[k] Ω) (X.ipD d).2
  have hcore := GaugeAlg.ec_row (D := X.DD) (I := X.I) (C := X.CC)
    (c := c) (β := β) (χ := X.chiExt χ) (X.hI) (X.CC_le_DD) (X.hnorm) hcc hβ1
    (fun u hu => GaugeAlg.coc_one_left hcc hc11 (X.CC_le_DD hu))
    (fun a ha b hb => by
      rw [X.chiExt_apply_coe χ ⟨a, ha⟩, X.chiExt_apply_coe χ ⟨b, hb⟩,
        X.chiExt_apply_coe χ ⟨a * b, X.CC.mul_mem ha hb⟩]
      exact hχ1 ⟨a, ha⟩ ⟨b, hb⟩)
    γ.2 hDrel (X.ipD d) (X.projD d)
  have hcore'' := hcore
  rw [show X.chiExt χ ((γ : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω)) = χ (γ * X.projD d)
    from X.chiExt_apply_coe χ (γ * X.projD d)] at hcore''
  simp only [X.chiExt_apply_coe] at hcore''
  simp only [hβ1, map_one, one_smul, h1c γ γ.2, zero_sub, sub_zero] at hcore''
  have hgoal : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω)
      ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω))
      = c (γ : Ω ≃ₐ[k] Ω) ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω)) := by
    rw [GaugeAlg.cob,
      X.GE_of_mul c β χ (X.ipD d) (X.projD d),
      X.GE_of_C c β χ γ hβ1 (h1c γ γ.2),
      show (γ : Ω ≃ₐ[k] Ω) * ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω))
        = (⟨(γ : Ω ≃ₐ[k] Ω) * (X.ipD d : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹, hjI⟩ : ↥X.I)
          * ((γ * X.projD d : ↥X.CC) : Ω ≃ₐ[k] Ω) from by rw [Subgroup.coe_mul]; group,
      X.GE_of_mul c β χ ⟨_, hjI⟩ (γ * X.projD d),
      show ((⟨(γ : Ω ≃ₐ[k] Ω) * (X.ipD d : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹, hjI⟩ : ↥X.I) :
          Ω ≃ₐ[k] Ω)
        = (γ : Ω ≃ₐ[k] Ω) * (X.ipD d : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹ from rfl]
    exact hcore''
  rw [X.ipD_mul_projD d] at hgoal
  exact hgoal

/-- The row of `i ∈ I`. -/
theorem cob_I_row (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (i : ↥X.I) :
    ∀ d : ↥X.DD, GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (i : Ω ≃ₐ[k] Ω) (d : Ω ≃ₐ[k] Ω)
      = c (i : Ω ≃ₐ[k] Ω) (d : Ω ≃ₐ[k] Ω) := by
  have hβ1 : β 1 = 0 := GaugeAlg.beta_one hβ hc11
  have hχ0 : χ 1 = 0 := X.chi_zero c χ hχ1 hc11
  have hcn1 : ∀ i : ↥X.I, c (i : Ω ≃ₐ[k] Ω) 1 = 0 := fun i => by
    rw [GaugeAlg.coc_one_right hcc (X.hI i.2), hc11, smul_zero]
  intro d
  have h3 : X.GE c β χ (i : Ω ≃ₐ[k] Ω) = β (i : Ω ≃ₐ[k] Ω) :=
    X.GE_of_I c β χ i hχ0 (hcn1 i)
  have hcore : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (i : Ω ≃ₐ[k] Ω)
      ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω))
      = c (i : Ω ≃ₐ[k] Ω) ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω)) := by
    rw [GaugeAlg.cob,
      X.GE_of_mul c β χ (X.ipD d) (X.projD d),
      X.GE_of_I c β χ i hχ0 (hcn1 i),
      show (i : Ω ≃ₐ[k] Ω) * ((X.ipD d : Ω ≃ₐ[k] Ω) * (X.projD d : Ω ≃ₐ[k] Ω))
        = (⟨(i : Ω ≃ₐ[k] Ω) * (X.ipD d : Ω ≃ₐ[k] Ω), X.I.mul_mem i.2 (X.ipD d).2⟩ : ↥X.I)
          * ((X.projD d : ↥X.CC) : Ω ≃ₐ[k] Ω) from by group,
      X.GE_of_mul c β χ ⟨_, X.I.mul_mem i.2 (X.ipD d).2⟩ (X.projD d)]
    have hbm := GaugeAlg.beta_mul hβ i.2 (X.ipD d).2
    have hcm := GaugeAlg.coc_mul_left hcc (X.hI i.2) (X.hI (X.ipD d).2) (X.CC_le_DD (X.projD d).2)
    rw [hbm, hcm]
    simp only [smul_sub, smul_add]
    rw [← mul_smul, ← map_mul]
    abel
  rwa [X.ipD_mul_projD d] at hcore

/-- `(d)` holds at `1`. -/
theorem Drel_one (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)) :
    X.Drel c β χ 1 := by
  have hβ1 : β 1 = 0 := GaugeAlg.beta_one hβ hc11
  have hχ0 : χ 1 = 0 := X.chi_zero c χ hχ1 hc11
  have hcn1 : ∀ i : ↥X.I, c (i : Ω ≃ₐ[k] Ω) 1 = 0 := fun i => by
    rw [GaugeAlg.coc_one_right hcc (X.hI i.2), hc11, smul_zero]
  rw [X.Drel_iff_cob c β χ hcc hc11 hβ hχ1 1]
  intro n
  have h1 : X.GE c β χ (n : Ω ≃ₐ[k] Ω) = β (n : Ω ≃ₐ[k] Ω) :=
    X.GE_of_I c β χ n hχ0 (hcn1 n)
  have hc1c : c 1 ((1 : ↥X.CC) : Ω ≃ₐ[k] Ω) = 0 := by
    rw [show ((1 : ↥X.CC) : Ω ≃ₐ[k] Ω) = 1 from rfl]
    exact GaugeAlg.coc_one_left hcc hc11 (X.CC_le_DD (1 : ↥X.CC).2)
  have h3 : X.GE c β χ (1 : Ω ≃ₐ[k] Ω) = 0 := by
    rw [show (1 : Ω ≃ₐ[k] Ω) = ((1 : ↥X.CC) : Ω ≃ₐ[k] Ω) from rfl,
      X.GE_of_C c β χ 1 hβ1 hc1c, hχ0, neg_zero]
  rw [GaugeAlg.cob, show ((1 : ↥X.CC) : Ω ≃ₐ[k] Ω) = (1 : Ω ≃ₐ[k] Ω) from rfl,
    one_mul, h1, h3, map_one, one_smul]
  have hc0 : c 1 (n : Ω ≃ₐ[k] Ω) = 0 := by
    have h := GaugeAlg.coc_one_left hcc hc11 (X.hI n.2)
    simpa using h
  rw [hc0]
  abel

/-- `(d)` holds at `σ`, from the hypothesis `hm`. -/
theorem Drel_sigma (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M) (m : M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ mm ∈ X.I, SSGRoute.res k K n • β mm - β (n * mm) + β n = c n mm)
    (hm : ∀ n ∈ X.I, tprim p k Ω K M X.σ c β n - β n = SSGRoute.res k K n • m - m)
    (hχσ : χ X.sigmaC = -m) :
    X.Drel c β χ X.sigmaC := by
  intro n
  have hn : (X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹ ∈ X.I :=
    X.hnorm X.σ X.hσ (n : Ω ≃ₐ[k] Ω) n.2
  have hm' := hm ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) hn
  have htprim : tprim p k Ω K M X.σ c β
        ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹)
      = SSGRoute.res k K X.σ • β (n : Ω ≃ₐ[k] Ω) - c X.σ (n : Ω ≃ₐ[k] Ω)
        + SSGRoute.res k K ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹)
          • c X.σ X.σ⁻¹
        - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹ + c 1 1 := by
    rw [tprim,
      show (X.σ : Ω ≃ₐ[k] Ω)⁻¹ * ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹)
          * (X.σ : Ω ≃ₐ[k] Ω) = (n : Ω ≃ₐ[k] Ω) from by group,
      show ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) * (X.σ : Ω ≃ₐ[k] Ω)
          = (X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) from by group]
  have hcoc1 := hcc (X.σ * (n : Ω ≃ₐ[k] Ω)) (X.DD.mul_mem X.hσ (X.hI n.2)) X.σ⁻¹
    (X.DD.inv_mem X.hσ) X.σ X.hσ
  rw [inv_mul_cancel] at hcoc1
  have hρeq : SSGRoute.res k K (X.σ * (n : Ω ≃ₐ[k] Ω)) • c X.σ⁻¹ X.σ
      = SSGRoute.res k K ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) • c X.σ X.σ⁻¹ := by
    nth_rewrite 1 [show (X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω)
        = ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) * (X.σ : Ω ≃ₐ[k] Ω) from by
      group]
    rw [map_mul, mul_smul, GaugeAlg.coc_inv_self hcc hc11 X.hσ]
  have h1 : c (X.σ * (n : Ω ≃ₐ[k] Ω)) 1 = 0 := by
    rw [GaugeAlg.coc_one_right hcc (X.DD.mul_mem X.hσ (X.hI n.2)), hc11, smul_zero]
  have hcoc_eq : c ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) X.σ
      = SSGRoute.res k K (X.σ * (n : Ω ≃ₐ[k] Ω)) • c X.σ⁻¹ X.σ
        + c (X.σ * (n : Ω ≃ₐ[k] Ω)) 1 - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹ := by
    have key2 : c ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) X.σ
          - (SSGRoute.res k K (X.σ * (n : Ω ≃ₐ[k] Ω)) • c X.σ⁻¹ X.σ
              + c (X.σ * (n : Ω ≃ₐ[k] Ω)) 1 - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹)
        = -(SSGRoute.res k K (X.σ * (n : Ω ≃ₐ[k] Ω)) • c X.σ⁻¹ X.σ
            - c ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) X.σ
            + c (X.σ * (n : Ω ≃ₐ[k] Ω)) 1 - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹) := by abel
    have key3 : c ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) X.σ
          - (SSGRoute.res k K (X.σ * (n : Ω ≃ₐ[k] Ω)) • c X.σ⁻¹ X.σ
              + c (X.σ * (n : Ω ≃ₐ[k] Ω)) 1 - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹) = 0 := by
      rw [key2, hcoc1, neg_zero]
    exact sub_eq_zero.mp key3
  have hsol : c ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) X.σ
      = SSGRoute.res k K ((X.σ * (n : Ω ≃ₐ[k] Ω)) * X.σ⁻¹) • c X.σ X.σ⁻¹
        - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹ := by
    rw [hcoc_eq, hρeq, h1]
    abel
  rw [htprim, hc11, add_zero] at hm'
  rw [show ((X.sigmaC : ↥X.CC) : Ω ≃ₐ[k] Ω) = (X.σ : Ω ≃ₐ[k] Ω) from rfl, hsol,
    show χ X.sigmaC = -m from hχσ]
  rw [smul_neg, sub_neg_eq_add]
  rw [← sub_eq_zero]
  have h2 : SSGRoute.res k K X.σ • β (n : Ω ≃ₐ[k] Ω)
        - β ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹)
        + -(SSGRoute.res k K ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) • m) + m
        + (SSGRoute.res k K ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) • c X.σ X.σ⁻¹
          - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹)
        - c X.σ (n : Ω ≃ₐ[k] Ω)
      = (SSGRoute.res k K X.σ • β (n : Ω ≃ₐ[k] Ω) - c X.σ (n : Ω ≃ₐ[k] Ω)
          + SSGRoute.res k K ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) • c X.σ X.σ⁻¹
          - c (X.σ * (n : Ω ≃ₐ[k] Ω)) X.σ⁻¹
          - β ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹))
        - (SSGRoute.res k K ((X.σ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (X.σ : Ω ≃ₐ[k] Ω)⁻¹) • m - m) := by
    abel
  rw [h2, hm', sub_self]

/-- `(d)` is multiplicative. -/
theorem Drel_mul (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    {γ₁ γ₂ : ↥X.CC} (h₁ : X.Drel c β χ γ₁) (h₂ : X.Drel c β χ γ₂) :
    X.Drel c β χ (γ₁ * γ₂) := by
  have h₂' : ∀ n : ↥X.I, GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₂ : Ω ≃ₐ[k] Ω)
      (n : Ω ≃ₐ[k] Ω) = c (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω) :=
    (X.Drel_iff_cob c β χ hcc hc11 hβ hχ1 γ₂).mp h₂
  rw [X.Drel_iff_cob c β χ hcc hc11 hβ hχ1 (γ₁ * γ₂)]
  rw [show ((γ₁ * γ₂ : ↥X.CC) : Ω ≃ₐ[k] Ω) = (γ₁ : Ω ≃ₐ[k] Ω) * (γ₂ : Ω ≃ₐ[k] Ω) from rfl]
  intro n
  have hc' := GaugeAlg.cob_cocycle (SSGRoute.res k K) (X.GE c β χ)
    (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
  have hrowa : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω)
      ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω))
      = c (γ₁ : Ω ≃ₐ[k] Ω) ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω)) :=
    X.cob_row c β χ hcc hc11 hβ hχ1 h₁ ⟨_, X.DD.mul_mem (X.CC_le_DD γ₂.2) (X.hI n.2)⟩
  have hrowb : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω)
      = c (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω) :=
    X.cob_row c β χ hcc hc11 hβ hχ1 h₁ ⟨_, X.CC_le_DD γ₂.2⟩
  have hcm := GaugeAlg.coc_mul_left hcc (X.CC_le_DD γ₁.2) (X.CC_le_DD γ₂.2) (X.hI n.2)
  have hsol : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ₁ : Ω ≃ₐ[k] Ω) * (γ₂ : Ω ≃ₐ[k] Ω))
        (n : Ω ≃ₐ[k] Ω)
      = SSGRoute.res k K (γ₁ : Ω ≃ₐ[k] Ω)
          • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
        + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω)
          ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω))
        - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω) := by
    have key : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ₁ : Ω ≃ₐ[k] Ω) * (γ₂ : Ω ≃ₐ[k] Ω))
            (n : Ω ≃ₐ[k] Ω)
          - (SSGRoute.res k K (γ₁ : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω)
              ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω))
        = -(SSGRoute.res k K (γ₁ : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ₁ : Ω ≃ₐ[k] Ω) * (γ₂ : Ω ≃ₐ[k] Ω))
              (n : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω)
              ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω)) := by
      abel
    have h2 : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ₁ : Ω ≃ₐ[k] Ω) * (γ₂ : Ω ≃ₐ[k] Ω))
            (n : Ω ≃ₐ[k] Ω)
          - (SSGRoute.res k K (γ₁ : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₂ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω)
              ((γ₂ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ₁ : Ω ≃ₐ[k] Ω) (γ₂ : Ω ≃ₐ[k] Ω)) = 0 := by
      rw [key, hc', neg_zero]
    exact sub_eq_zero.mp h2
  rw [hsol, h₂' n, hrowa, hrowb, ← hcm]

/-- `(d)` is preserved by inversion. -/
theorem Drel_inv (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    {γ : ↥X.CC} (h : X.Drel c β χ γ) : X.Drel c β χ γ⁻¹ := by
  have hβ1 : β 1 = 0 := GaugeAlg.beta_one hβ hc11
  have hχ0 : χ 1 = 0 := X.chi_zero c χ hχ1 hc11
  have hcn1 : ∀ i : ↥X.I, c (i : Ω ≃ₐ[k] Ω) 1 = 0 := fun i => by
    rw [GaugeAlg.coc_one_right hcc (X.hI i.2), hc11, smul_zero]
  have h1c : ∀ u ∈ X.CC, c 1 (u : Ω ≃ₐ[k] Ω) = 0 := fun u hu =>
    GaugeAlg.coc_one_left hcc hc11 (X.CC_le_DD hu)
  rw [X.Drel_iff_cob c β χ hcc hc11 hβ hχ1 γ⁻¹]
  rw [show ((γ⁻¹ : ↥X.CC) : Ω ≃ₐ[k] Ω) = (γ : Ω ≃ₐ[k] Ω)⁻¹ from rfl]
  intro n
  have hγD : (γ : Ω ≃ₐ[k] Ω) ∈ X.DD := X.CC_le_DD γ.2
  have hc' := GaugeAlg.cob_cocycle (SSGRoute.res k K) (X.GE c β χ)
    (γ : Ω ≃ₐ[k] Ω) (γ : Ω ≃ₐ[k] Ω)⁻¹ (n : Ω ≃ₐ[k] Ω)
  have hrow : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω)
      ((γ : Ω ≃ₐ[k] Ω)⁻¹ * (n : Ω ≃ₐ[k] Ω))
      = c (γ : Ω ≃ₐ[k] Ω) ((γ : Ω ≃ₐ[k] Ω)⁻¹ * (n : Ω ≃ₐ[k] Ω)) :=
    X.cob_row c β χ hcc hc11 hβ hχ1 h
      ⟨_, X.DD.mul_mem (X.DD.inv_mem hγD) (X.hI n.2)⟩
  have hrow2 : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (γ : Ω ≃ₐ[k] Ω) (γ : Ω ≃ₐ[k] Ω)⁻¹
      = c (γ : Ω ≃ₐ[k] Ω) (γ : Ω ≃ₐ[k] Ω)⁻¹ :=
    X.cob_row c β χ hcc hc11 hβ hχ1 h ⟨_, X.DD.inv_mem hγD⟩
  have hone : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (1 : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω) = 0 := by
    have h3 : X.GE c β χ (1 : Ω ≃ₐ[k] Ω) = 0 := by
      rw [show (1 : Ω ≃ₐ[k] Ω) = ((1 : ↥X.CC) : Ω ≃ₐ[k] Ω) from rfl,
        X.GE_of_C c β χ 1 hβ1 (h1c 1 (1 : ↥X.CC).2), hχ0, neg_zero]
    rw [GaugeAlg.cob, one_mul, map_one, one_smul, X.GE_of_I c β χ n hχ0 (hcn1 n), h3]
    abel
  have hc'' : SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ : Ω ≃ₐ[k] Ω)⁻¹) (n : Ω ≃ₐ[k] Ω)
      + c (γ : Ω ≃ₐ[k] Ω) ((γ : Ω ≃ₐ[k] Ω)⁻¹ * (n : Ω ≃ₐ[k] Ω))
      - c (γ : Ω ≃ₐ[k] Ω) ((γ : Ω ≃ₐ[k] Ω)⁻¹) = 0 := by
    rw [mul_inv_cancel, hone, hrow, hrow2, sub_zero] at hc'
    exact hc'
  have hcc2 : SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • c (γ : Ω ≃ₐ[k] Ω)⁻¹ (n : Ω ≃ₐ[k] Ω)
      + c (γ : Ω ≃ₐ[k] Ω) ((γ : Ω ≃ₐ[k] Ω)⁻¹ * (n : Ω ≃ₐ[k] Ω))
      - c (γ : Ω ≃ₐ[k] Ω) ((γ : Ω ≃ₐ[k] Ω)⁻¹) = 0 := by
    have hcm := GaugeAlg.coc_mul_left hcc hγD (X.DD.inv_mem hγD) (X.hI n.2)
    rw [mul_inv_cancel, GaugeAlg.coc_one_left hcc hc11 (X.hI n.2)] at hcm
    rw [← hcm]
  have hEq : SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((γ : Ω ≃ₐ[k] Ω)⁻¹) (n : Ω ≃ₐ[k] Ω)
      = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • c (γ : Ω ≃ₐ[k] Ω)⁻¹ (n : Ω ≃ₐ[k] Ω) := by
    rw [sub_eq_zero] at hc'' hcc2
    exact add_right_cancel (hc''.trans hcc2.symm)
  have hfin := congrArg (fun x => (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω))⁻¹ • x) hEq
  simpa using hfin

/-- **Uniform shrinking of the coordinates.**  For prescribed open subgroups `W ≤ Ω ≃ₐ[k] Ω`
and `V ≤ ↥X.CC` there is an open subgroup `U ≤ Ω ≃ₐ[k] Ω` such that every `u ∈ U` lying in the
decomposition group `D = X.DD` has *both* its coordinates in `W`, resp. `V`.

This is the compactness (Krull) step of the local constancy of `GE`: the set of `d ∈ D` with
`ipD d ∈ W` and `projD d ∈ V` is open in `↥D` (continuity of the two coordinates,
`Work.SSGRoute.HSRow.continuous_ip`/`continuous_proj`, which is where `hIclosed` enters) and
contains `1`, hence contains the trace of an open neighbourhood of `1` in `Ω ≃ₐ[k] Ω`. -/
theorem exists_openSubgroup_coords_mem_g
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (X : Work.SSGRoute.HSRow.Ctx p k Ω K M)
    (hIclosed : IsClosed (X.I : Set (Ω ≃ₐ[k] Ω)))
    (W : Subgroup (Ω ≃ₐ[k] Ω)) (hWopen : IsOpen (W : Set (Ω ≃ₐ[k] Ω)))
    (V : Subgroup ↥X.CC) (hVopen : IsOpen (V : Set ↥X.CC)) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ u ∈ U, ∀ hu : u ∈ X.DD,
        (X.ipD ⟨u, hu⟩ : Ω ≃ₐ[k] Ω) ∈ W ∧ X.projD ⟨u, hu⟩ ∈ V := by
  classical
  have hip : Continuous (X.ipD : ↥X.DD → ↥X.I) :=
    continuous_ip k Ω X.A X.I X.σ X.hI X.hnorm X.hσ X.hsup X.hinf hIclosed
  have hpr : Continuous (X.projD : ↥X.DD → ↥X.CC) :=
    continuous_proj k Ω X.A X.I X.σ X.hI X.hnorm X.hσ X.hsup X.hinf hIclosed
  have hSopen : IsOpen {d : ↥X.DD | (X.ipD d : Ω ≃ₐ[k] Ω) ∈ W ∧ X.projD d ∈ V} :=
    (hWopen.preimage (continuous_subtype_val.comp hip)).inter (hVopen.preimage hpr)
  have h1S : (⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ : ↥X.DD) ∈
      {d : ↥X.DD | (X.ipD d : Ω ≃ₐ[k] Ω) ∈ W ∧ X.projD d ∈ V} := by
    refine ⟨?_, ?_⟩
    · show (X.ipD ⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ : Ω ≃ₐ[k] Ω) ∈ W
      rw [show X.ipD ⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ = 1 from by
        simpa using X.ipD_of_I (1 : ↥X.I)]
      exact W.one_mem
    · show X.projD ⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ ∈ V
      rw [show X.projD ⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ = 1 from by
        simpa using X.projD_of_C (1 : ↥X.CC)]
      exact V.one_mem
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hSopen
  have h1O : (1 : Ω ≃ₐ[k] Ω) ∈ O := by
    have h : (⟨(1 : Ω ≃ₐ[k] Ω), X.DD.one_mem⟩ : ↥X.DD) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      exact h1S
    exact h
  obtain ⟨H, hHO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  refine ⟨(H : Subgroup (Ω ≃ₐ[k] Ω)), H.isOpen, ?_⟩
  intro u hu huD
  have hmem : (⟨u, huD⟩ : ↥X.DD) ∈
      {d : ↥X.DD | (X.ipD d : Ω ≃ₐ[k] Ω) ∈ W ∧ X.projD d ∈ V} := by
    rw [← hOeq]
    exact hHO hu
  exact hmem

/-- **The algebraic step.**  If `u ∈ D` has both coordinates in the subgroups `W ≤ Ω ≃ₐ[k] Ω`
and `V ≤ ↥X.CC` on which (respectively) `β`, `χ` and `c` are constant — concretely, if
`β` is constant along multiplication by `W ∩ I`, `χ` along multiplication by `V`, and `c` along
multiplication by `W × W` on `D × D`, and `res k K` vanishes on `W` — then the gauge cochain
`GEd` is unchanged under right multiplication by `u`:

`ipD (g * u) = ipD g * (projD g * ipD u * (projD g)⁻¹)`, `projD (g * u) = projD g * projD u`,
and the conjugation correction lies in `W` (normality of `W`, hypothesis `hconj`). -/
theorem GEd_mul_eq_of_coords_g
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (X : Work.SSGRoute.HSRow.Ctx p k Ω K M)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (χ : ↥X.CC → M)
    (W : Subgroup (Ω ≃ₐ[k] Ω)) (V : Subgroup ↥X.CC)
    (hconj : ∀ w ∈ W, ∀ a : Ω ≃ₐ[k] Ω, a * w * a⁻¹ ∈ W)
    (hβW : ∀ n ∈ X.I, ∀ w ∈ W, w ∈ X.I → β (n * w) = β n)
    (hχV : ∀ γ : ↥X.CC, ∀ v ∈ V, χ (γ * v) = χ γ)
    (hcW : ∀ x ∈ X.DD, ∀ y ∈ X.DD, ∀ u ∈ W, ∀ v ∈ W, u ∈ X.DD → v ∈ X.DD →
      c (x * u) (y * v) = c x y)
    (hresW : ∀ w ∈ W, SSGRoute.res k K w = 1)
    (hVW : ∀ v ∈ V, (v : Ω ≃ₐ[k] Ω) ∈ W)
    (g u : ↥X.DD)
    (hip : (X.ipD u : Ω ≃ₐ[k] Ω) ∈ W) (hpr : X.projD u ∈ V) :
    X.GEd c β χ (g * u) = X.GEd c β χ g := by
  classical
  have hjI : (X.projD g : Ω ≃ₐ[k] Ω) * (X.ipD u : Ω ≃ₐ[k] Ω)
      * (X.projD g : Ω ≃ₐ[k] Ω)⁻¹ ∈ X.I :=
    X.hnorm (X.projD g) (X.CC_le_DD (X.projD g).2) (X.ipD u) (X.ipD u).2
  have hjW : (X.projD g : Ω ≃ₐ[k] Ω) * (X.ipD u : Ω ≃ₐ[k] Ω)
      * (X.projD g : Ω ≃ₐ[k] Ω)⁻¹ ∈ W := hconj (X.ipD u) hip (X.projD g)
  let w : ↥X.I := ⟨(X.projD g : Ω ≃ₐ[k] Ω) * (X.ipD u : Ω ≃ₐ[k] Ω)
      * (X.projD g : Ω ≃ₐ[k] Ω)⁻¹, hjI⟩
  have hwW : (w : Ω ≃ₐ[k] Ω) ∈ W := hjW
  have h1 : X.ipD (g * u) = X.ipD g * w := X.ipD_mul g u
  have h2 : X.projD (g * u) = X.projD g * X.projD u := X.projD_mul g u
  have hβ : β ((X.ipD (g * u) : Ω ≃ₐ[k] Ω)) = β (X.ipD g : Ω ≃ₐ[k] Ω) := by
    rw [h1, Subgroup.coe_mul]
    exact hβW (X.ipD g) (X.ipD g).2 (w : Ω ≃ₐ[k] Ω) hwW w.2
  have hres : SSGRoute.res k K ((X.ipD (g * u) : Ω ≃ₐ[k] Ω))
      = SSGRoute.res k K (X.ipD g : Ω ≃ₐ[k] Ω) := by
    rw [h1, Subgroup.coe_mul, map_mul, hresW (w : Ω ≃ₐ[k] Ω) hwW, mul_one]
  have hχ : χ (X.projD (g * u)) = χ (X.projD g) := by
    rw [h2]
    exact hχV (X.projD g) (X.projD u) hpr
  have hc : c ((X.ipD (g * u) : Ω ≃ₐ[k] Ω)) ((X.projD (g * u) : Ω ≃ₐ[k] Ω))
      = c (X.ipD g : Ω ≃ₐ[k] Ω) (X.projD g : Ω ≃ₐ[k] Ω) := by
    rw [h1, h2, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcW (X.ipD g) (X.hI (X.ipD g).2) (X.projD g) (X.CC_le_DD (X.projD g).2)
      (w : Ω ≃ₐ[k] Ω) hwW (X.projD u) (hVW (X.projD u) hpr) (X.hI w.2)
      (X.CC_le_DD (X.projD u).2)
  show β ((X.ipD (g * u) : Ω ≃ₐ[k] Ω))
        - SSGRoute.res k K ((X.ipD (g * u) : Ω ≃ₐ[k] Ω)) • χ (X.projD (g * u))
        - c ((X.ipD (g * u) : Ω ≃ₐ[k] Ω)) ((X.projD (g * u) : Ω ≃ₐ[k] Ω))
      = β ((X.ipD g : Ω ≃ₐ[k] Ω)) - SSGRoute.res k K ((X.ipD g : Ω ≃ₐ[k] Ω)) • χ (X.projD g)
        - c ((X.ipD g : Ω ≃ₐ[k] Ω)) ((X.projD g : Ω ≃ₐ[k] Ω))
  rw [hβ, hres, hχ, hc]

/-- **Closedness of the relation `(d)`.** -/
theorem Drel_isClosed (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M) (hβlc : SSGRoute.IsLocConstOn X.I β)
    (hχlc : SSGRoute.IsLocConstOn ⊤ χ)
    (hlc : SSGRoute.IsLocConst2On p k Ω K M X.DD c) :
    IsClosed {γ : ↥X.CC | X.Drel c β χ γ} := by
  -- the `n`-th condition, as a function of `γ` (equal to `LHS n γ - RHS n γ`)
  let F : ↥X.I → ↥X.CC → M := fun n γ =>
    SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • β (n : Ω ≃ₐ[k] Ω)
      - β ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹)
      + SSGRoute.res k K ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) • χ γ
      - χ γ
      + c ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) (γ : Ω ≃ₐ[k] Ω)
      - c (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)
  have hres : IsLocallyConstant (SSGRoute.res k K : (Ω ≃ₐ[k] Ω) → (K ≃ₐ[k] K)) :=
    gauge_res_lc K
  have hresC : IsLocallyConstant (fun γ : ↥X.CC => SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)) :=
    hres.comp_continuous continuous_subtype_val
  have hχ : IsLocallyConstant χ := gauge_lc_top hχlc
  have hF : ∀ n : ↥X.I, IsLocallyConstant (F n) := by
    intro n
    have hφ : Continuous (fun γ : ↥X.CC =>
        (γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) := by
      continuity
    have hφI : ∀ γ : ↥X.CC,
        (γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹ ∈ X.I :=
      fun γ => X.hnorm (γ : Ω ≃ₐ[k] Ω) (X.CC_le_DD γ.2) (n : Ω ≃ₐ[k] Ω) n.2
    have hφD : ∀ γ : ↥X.CC,
        (γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹ ∈ X.DD :=
      fun γ => X.hI (hφI γ)
    have h1 : IsLocallyConstant (fun γ : ↥X.CC =>
        SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • β (n : Ω ≃ₐ[k] Ω)) :=
      hresC.comp₂ (IsLocallyConstant.const (β (n : Ω ≃ₐ[k] Ω))) (fun a b => a • b)
    have h2 : IsLocallyConstant (fun γ : ↥X.CC =>
        β ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹)) :=
      gauge_lc_comp hβlc _ hφ hφI
    have h3 : IsLocallyConstant (fun γ : ↥X.CC =>
        SSGRoute.res k K ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) • χ γ) :=
      (hres.comp_continuous hφ).comp₂ hχ (fun a b => a • b)
    have h4 : IsLocallyConstant (fun γ : ↥X.CC => χ γ) := hχ
    have h5 : IsLocallyConstant (fun γ : ↥X.CC =>
        c ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹) (γ : Ω ≃ₐ[k] Ω)) :=
      gauge_lc2_comp hlc
        (fun γ : ↥X.CC =>
          ((γ : Ω ≃ₐ[k] Ω) * (n : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)⁻¹, (γ : Ω ≃ₐ[k] Ω)))
        (by continuity) (fun γ => ⟨hφD γ, X.CC_le_DD γ.2⟩)
    have h6 : IsLocallyConstant (fun γ : ↥X.CC => c (γ : Ω ≃ₐ[k] Ω) (n : Ω ≃ₐ[k] Ω)) :=
      gauge_lc2_comp hlc
        (fun γ : ↥X.CC => ((γ : Ω ≃ₐ[k] Ω), (n : Ω ≃ₐ[k] Ω)))
        (by continuity) (fun γ => ⟨X.CC_le_DD γ.2, X.hI n.2⟩)
    have hcomb : IsLocallyConstant (F n) := by
      have hthis := ((((h1.sub h2).add h3).sub h4).add h5).sub h6
      convert hthis using 1
      all_goals (ext γ; simp only [F, Pi.sub_apply, Pi.add_apply])
    exact hcomb
  have hEq : {γ : ↥X.CC | X.Drel c β χ γ} = ⋂ n : ↥X.I, {γ : ↥X.CC | F n γ = 0} := by
    ext γ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h n => sub_eq_zero.mpr (h n), fun h n => sub_eq_zero.mp (h n)⟩
  rw [hEq]
  exact isClosed_iInter (fun n => (hF n).isClosed_fiber 0)


/-- **The relation `(d)` holds everywhere on `C`.** -/
theorem Drel_of_mem_C (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (hσD : X.Drel c β χ X.sigmaC)
    (hclosed : IsClosed {γ : ↥X.CC | X.Drel c β χ γ}) (γ : ↥X.CC) :
    X.Drel c β χ γ := by
  let S : Subgroup ↥X.CC :=
    { carrier := {γ : ↥X.CC | X.Drel c β χ γ}
      one_mem' := X.Drel_one c β χ hcc hc11 hβ hχ1
      mul_mem' := fun h₁ h₂ => X.Drel_mul c β χ hcc hc11 hβ hχ1 h₁ h₂
      inv_mem' := fun h => X.Drel_inv c β χ hcc hc11 hβ hχ1 h }
  have hSclosed : IsClosed (S : Set ↥X.CC) := hclosed
  have hzpow : Subgroup.zpowers X.sigmaC ≤ S := Subgroup.zpowers_le.mpr hσD
  have hcl := Subgroup.topologicalClosure_minimal (Subgroup.zpowers X.sigmaC) hzpow hSclosed
  have hmap := Work.SSGRoute.map_topologicalClosure_zpowers_subtype X.CC
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers X.σ)) X.σ
    (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers X.σ))
  have hmem : (γ : Ω ≃ₐ[k] Ω)
      ∈ (Subgroup.topologicalClosure (Subgroup.zpowers X.sigmaC)).map X.CC.subtype := by
    rw [hmap]
    exact γ.2
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hyS : y ∈ S := hcl hy
  have hyγ : y = γ := Subtype.ext hyeq
  rwa [hyγ] at hyS

/-- The gauge coboundary is `c` on `D × D`. -/
theorem cob_eq_on_D (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M)
    (hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c) (hc11 : c 1 1 = 0)
    (hβ : ∀ n ∈ X.I, ∀ m ∈ X.I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (hχ1 : ∀ γ δ : ↥X.CC, χ (γ * δ)
      = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (hβlc : SSGRoute.IsLocConstOn X.I β) (hχlc : SSGRoute.IsLocConstOn ⊤ χ)
    (hlc : SSGRoute.IsLocConst2On p k Ω K M X.DD c) (hIclosed : IsClosed (X.I : Set (Ω ≃ₐ[k] Ω)))
    (m : M)
    (hm : ∀ n ∈ X.I, tprim p k Ω K M X.σ c β n - β n = SSGRoute.res k K n • m - m)
    (hχσ : χ X.sigmaC = -m) (g h : ↥X.DD) :
    GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω)
      = c (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω) := by
  have hσD : X.Drel c β χ X.sigmaC := X.Drel_sigma c β χ m hcc hc11 hβ hm hχσ
  have hclosed : IsClosed {γ : ↥X.CC | X.Drel c β χ γ} := X.Drel_isClosed c β χ hβlc hχlc hlc
  have hAll : ∀ γ : ↥X.CC, X.Drel c β χ γ := X.Drel_of_mem_C c β χ hcc hc11 hβ hχ1 hσD hclosed
  have hrow := X.cob_row c β χ hcc hc11 hβ hχ1 (hAll (X.projD g))
  have hIrow := X.cob_I_row c β χ hcc hc11 hβ hχ1 (X.ipD g)
  have hc' := GaugeAlg.cob_cocycle (SSGRoute.res k K) (X.GE c β χ)
    ((X.ipD g) : Ω ≃ₐ[k] Ω) ((X.projD g) : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω)
  have hcm := GaugeAlg.coc_mul_left hcc (X.hI (X.ipD g).2) (X.CC_le_DD (X.projD g).2) h.2
  have hrowa : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
      (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω))
      = c ((X.ipD g) : Ω ≃ₐ[k] Ω) (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω)) :=
    hIrow ⟨_, X.DD.mul_mem (X.CC_le_DD (X.projD g).2) h.2⟩
  have hrowb : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
      ((X.projD g) : Ω ≃ₐ[k] Ω)
      = c ((X.ipD g) : Ω ≃ₐ[k] Ω) ((X.projD g) : Ω ≃ₐ[k] Ω) :=
    hIrow ⟨_, X.CC_le_DD (X.projD g).2⟩
  have hsol : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ)
        (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω)
      = SSGRoute.res k K ((X.ipD g) : Ω ≃ₐ[k] Ω)
          • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.projD g) : Ω ≃ₐ[k] Ω)
            (h : Ω ≃ₐ[k] Ω)
        + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
          (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω))
        - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
          ((X.projD g) : Ω ≃ₐ[k] Ω) := by
    have key : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ)
            (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω)
          - (SSGRoute.res k K ((X.ipD g) : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.projD g) : Ω ≃ₐ[k] Ω)
                (h : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              ((X.projD g) : Ω ≃ₐ[k] Ω))
        = -(SSGRoute.res k K ((X.ipD g) : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.projD g) : Ω ≃ₐ[k] Ω)
                (h : Ω ≃ₐ[k] Ω)
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ)
              (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              ((X.projD g) : Ω ≃ₐ[k] Ω)) := by abel
    have h2 : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ)
            (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω)
          - (SSGRoute.res k K ((X.ipD g) : Ω ≃ₐ[k] Ω)
              • GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.projD g) : Ω ≃ₐ[k] Ω)
                (h : Ω ≃ₐ[k] Ω)
            + GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              (((X.projD g) : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω))
            - GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ) ((X.ipD g) : Ω ≃ₐ[k] Ω)
              ((X.projD g) : Ω ≃ₐ[k] Ω)) = 0 := by
      rw [key, hc', neg_zero]
    exact sub_eq_zero.mp h2
  have hcore : GaugeAlg.cob (SSGRoute.res k K) (X.GE c β χ)
      (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω)
      = c (((X.ipD g) : Ω ≃ₐ[k] Ω) * ((X.projD g) : Ω ≃ₐ[k] Ω)) (h : Ω ≃ₐ[k] Ω) := by
    rw [hsol, hrow h, hrowa, hrowb, ← hcm]
  rwa [X.ipD_mul_projD g] at hcore

/-- **`GE` is locally constant on `D`.** -/
theorem GE_isLocConstOn (X : Ctx p k Ω K M) (c β) (χ : ↥X.CC → M) (hβlc : SSGRoute.IsLocConstOn X.I β)
    (hχlc : SSGRoute.IsLocConstOn ⊤ χ)
    (hlc : SSGRoute.IsLocConst2On p k Ω K M X.DD c) (hIclosed : IsClosed (X.I : Set (Ω ≃ₐ[k] Ω))) :
    SSGRoute.IsLocConstOn X.DD (X.GE c β χ) := by
  classical
  obtain ⟨Uβ, hUβopen, hUβ⟩ := hβlc
  obtain ⟨Uχ, hUχopen, hUχ⟩ := hχlc
  obtain ⟨Uc, hUcopen, hUc⟩ := hlc
  -- an open *normal* subgroup `W ≤ Γ` on which `β`, `c` and `res k K` are all trivial
  have hKopen : IsOpen (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  have hS₀open : IsOpen ((Uβ ⊓ Uc ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) :=
    (hUβopen.inter hUcopen).inter hKopen
  have h1S₀ : (1 : Ω ≃ₐ[k] Ω) ∈ (Uβ ⊓ Uc ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :=
    ⟨⟨Uβ.one_mem, Uc.one_mem⟩, K.fixingSubgroup.one_mem⟩
  obtain ⟨H, hHsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS₀open h1S₀
  have hWopen : IsOpen ((H : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := H.isOpen
  have hHnorm : ((H : Subgroup (Ω ≃ₐ[k] Ω))).Normal := H.isNormal'
  have hWβ : (H : Subgroup (Ω ≃ₐ[k] Ω)) ≤ Uβ := fun w hw => (hHsub hw).1.1
  have hWc : (H : Subgroup (Ω ≃ₐ[k] Ω)) ≤ Uc := fun w hw => (hHsub hw).1.2
  have hWfix : (H : Subgroup (Ω ≃ₐ[k] Ω)) ≤ K.fixingSubgroup := fun w hw => (hHsub hw).2
  -- the open subgroup `V ≤ ↥X.CC` on which `χ` is constant and whose elements lie in `W`
  let V : Subgroup ↥X.CC := Uχ ⊓ (H : Subgroup (Ω ≃ₐ[k] Ω)).comap X.CC.subtype
  have hVopen : IsOpen (V : Set ↥X.CC) := by
    change IsOpen ((Uχ ⊓ (H : Subgroup (Ω ≃ₐ[k] Ω)).comap X.CC.subtype :
      Subgroup ↥X.CC) : Set ↥X.CC)
    rw [Subgroup.coe_inf, Subgroup.coe_comap]
    exact hUχopen.inter (hWopen.preimage continuous_subtype_val)
  obtain ⟨U, hUopen, hUmem⟩ :=
    exists_openSubgroup_coords_mem_g p k Ω K M X hIclosed
      (H : Subgroup (Ω ≃ₐ[k] Ω)) hWopen V hVopen
  refine ⟨U, hUopen, ?_⟩
  intro g hg u hu huD
  obtain ⟨hip, hpr⟩ := hUmem u hu huD
  have hβW : ∀ n ∈ X.I, ∀ w ∈ (H : Subgroup (Ω ≃ₐ[k] Ω)), w ∈ X.I → β (n * w) = β n :=
    fun n hn w hw hwI => hUβ n hn w (hWβ hw) hwI
  have hχV : ∀ γ : ↥X.CC, ∀ v ∈ V, χ (γ * v) = χ γ := by
    intro γ v hv
    exact hUχ γ (Subgroup.mem_top γ) v (Subgroup.mem_inf.mp hv).1 (Subgroup.mem_top v)
  have hcW : ∀ x ∈ X.DD, ∀ y ∈ X.DD, ∀ u ∈ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      ∀ v ∈ (H : Subgroup (Ω ≃ₐ[k] Ω)), u ∈ X.DD → v ∈ X.DD → c (x * u) (y * v) = c x y :=
    fun x hx y hy u hu v hv huD hvD => hUc x hx y hy u (hWc hu) v (hWc hv) huD hvD
  have hresW : ∀ w ∈ (H : Subgroup (Ω ≃ₐ[k] Ω)), SSGRoute.res k K w = 1 := by
    intro w hw
    refine MonoidHom.mem_ker.mp ?_
    rw [IntermediateField.restrictNormalHom_ker K]
    exact hWfix hw
  have hVW : ∀ v ∈ V, (v : Ω ≃ₐ[k] Ω) ∈ (H : Subgroup (Ω ≃ₐ[k] Ω)) :=
    fun v hv => Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hv).2
  have hkey := GEd_mul_eq_of_coords_g p k Ω K M X c β χ (H : Subgroup (Ω ≃ₐ[k] Ω)) V
    (fun w hw a => hHnorm.conj_mem w hw a) hβW hχV hcW hresW hVW
    ⟨g, hg⟩ ⟨u, huD⟩ hip hpr
  have e1 : X.GE c β χ ((⟨g * u, X.DD.mul_mem hg huD⟩ : ↥X.DD) : Ω ≃ₐ[k] Ω)
      = X.GEd c β χ (⟨g * u, X.DD.mul_mem hg huD⟩ : ↥X.DD) := X.GE_apply c β χ _
  have e2 : X.GE c β χ ((⟨g, hg⟩ : ↥X.DD) : Ω ≃ₐ[k] Ω) = X.GEd c β χ ⟨g, hg⟩ :=
    X.GE_apply c β χ _
  have hgu_eq : (⟨g * u, X.DD.mul_mem hg huD⟩ : ↥X.DD) = ⟨g, hg⟩ * ⟨u, huD⟩ := rfl
  rw [e1, e2, hgu_eq, hkey]


end Ctx

/-- **The injectivity core (normalised case).**  Let `c` be a *normalised* locally constant
`2`-cocycle on `D = decomp k A`, `β` a locally constant primitive of `c|_{I × I}`, `m ∈ M` a
witness that the `σ`-transgression of `c` computed from `β` is a coboundary on `I`
(`tprim σ c β n - β n = ρ(n) • m - m` for `n ∈ I`), and `χ : ↥C → M` a locally constant
`c`-twisted crossed homomorphism on `C = closure (zpowers σ)` with `χ σ = -m`.  Then `c` is a
locally constant `2`-coboundary on `D`. -/
theorem exists_coboundary_of_gauge
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A))
    (hc11 : c 1 1 = 0)
    (β : (Ω ≃ₐ[k] Ω) → M) (hβlc : SSGRoute.IsLocConstOn I β)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (m : M)
    (hm : ∀ n ∈ I, tprim p k Ω K M σ c β n - β n = SSGRoute.res k K n • m - m)
    (χ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → M)
    (hχlc : SSGRoute.IsLocConstOn ⊤ χ)
    (hχ1 : ∀ γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
      χ (γ * δ) = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ
        + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω))
    (hχσ : χ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ = -m) :
    c ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A) := by
  let X : Ctx p k Ω K M := ⟨A, I, σ, hI, hnorm, hσ, hsup, hinf⟩
  have hcc : SSGRoute.IsCocycle2On p k Ω K M X.DD c := hc.1
  have hlc : SSGRoute.IsLocConst2On p k Ω K M X.DD c := hc.2
  have hσD : X.Drel c β χ X.sigmaC := X.Drel_sigma c β χ m hcc hc11 hβ hm hχσ
  have hclosed : IsClosed {γ : ↥X.CC | X.Drel c β χ γ} := X.Drel_isClosed c β χ hβlc hχlc hlc
  have hγD : ∀ γ : ↥X.CC, X.Drel c β χ γ :=
    X.Drel_of_mem_C c β χ hcc hc11 hβ hχ1 hσD hclosed
  refine ⟨X.GE c β χ, X.GE_isLocConstOn c β χ hβlc hχlc hlc hIclosed, ?_⟩
  intro g hg h hh
  exact (X.cob_eq_on_D c β χ hcc hc11 hβ hχ1 hβlc hχlc hlc hIclosed m hm hχσ ⟨g, hg⟩
    ⟨h, hh⟩).symm

end

end Work.SSGRoute.HSRow
