import Mathlib
import Submission.Work.Mostow.zassDefs
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.margulisPairDefs

namespace Work.Mostow

-- File: Submission/Work/Mostow/zassenhausOfOrigin.lean.
-- Mathematical content: transport the origin case of Zassenhaus to an arbitrary base point z,
-- with the SAME η.
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- For an isometry `g` and `γ : PO n 1`, conjugating `γ` by `g` translates the displacement
`u ↦ γ • u` to the displacement of `g⁻¹ * γ * g` at `u`. -/
private lemma hdist_conj_eq {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (g γ : PO n 1) (u : E n) :
    hdist u ((g⁻¹ * γ * g) • u) = hdist (g • u) (γ • (g • u)) := by
  obtain ⟨_, _, _, hone, hmul, _, _, _, _, _, _, _⟩ := hA
  obtain ⟨_, _, _, _, _, _, hisom, -⟩ := hI
  rw [← hisom g u ((g⁻¹ * γ * g) • u)]
  congr 1
  rw [hmul (g⁻¹ * γ) g u, hmul g⁻¹ γ (g • u), ← hmul g g⁻¹ (γ • (g • u)),
    mul_inv_cancel, hone]

/-- Conjugating by an isometry `g` with `g • 0 = z` identifies "near identity at the origin"
for the conjugate with "near identity at `z`". -/
private lemma nearIdAt_conj_iff {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    {g : PO n 1} {z : E n} (hg : g • (0 : E n) = z) (η : ℝ) (γ : PO n 1) :
    NearIdAt (g⁻¹ * γ * g) (0 : E n) η ↔ NearIdAt γ z η := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
    hI.2.2.2.2.2.2.1
  have hgv : ∀ v : E n, g • (g⁻¹ • v) = v := by
    intro v
    rw [← hmul g g⁻¹ v, mul_inv_cancel, hone]
  constructor
  · intro h v hv
    have hu : hdist (0 : E n) (g⁻¹ • v) ≤ 1 := by
      have hzv : hdist (0 : E n) (g⁻¹ • v) = hdist z v := by
        rw [← hisom g (0 : E n) (g⁻¹ • v), hg, hgv v]
      rw [hzv]; exact hv
    have h1 := h (g⁻¹ • v) hu
    rw [hdist_conj_eq hA hI g γ (g⁻¹ • v), hgv v] at h1
    exact h1
  · intro h u hu
    rw [hdist_conj_eq hA hI g γ u]
    apply h
    have : hdist z (g • u) = hdist (0 : E n) u := by
      rw [← hg, hisom g (0 : E n) u]
    rw [this]; exact hu

theorem zassenhausOfOrigin (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hboost : ∀ u : E n, ∃ g : PO n 1, g • (0 : E n) = u)
    (η : ℝ) (hη : 0 < η)
    (h0 : ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
      Group.IsNilpotent (Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) (0 : E n) η})) :
    ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) → ∀ z : E n,
      Group.IsNilpotent (Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) z η}) := by
  intro Γ hdisc z
  obtain ⟨g, hg⟩ := hboost z
  -- conjugation by `g⁻¹`
  set φ : PO n 1 →* PO n 1 := (MulAut.conj g⁻¹).toMonoidHom with hφdef
  set Γ' : Subgroup (PO n 1) := Γ.map φ with hΓ'def
  have hdisc' : IsDiscrete (SetLike.coe Γ') := by
    rw [hΓ'def, hφdef]
    exact isDiscrete_map_conj hdisc g
  have hf : Function.Injective φ := by
    rw [hφdef]
    exact MulEquiv.injective (MulAut.conj g⁻¹)
  -- the isomorphism `Γ ≃* Γ'` induced by conjugation
  set e : Γ ≃* Γ' := Subgroup.equivMapOfInjective Γ φ hf with hedef
  have hcoe : ∀ γ : Γ, (e γ : PO n 1) = g⁻¹ * (γ : PO n 1) * g := by
    intro γ
    have h1 : (e γ : PO n 1) = φ (γ : PO n 1) := by
      rw [hedef]
      exact Subgroup.coe_equivMapOfInjective_apply Γ φ hf γ
    rw [h1]
    simp [hφdef]
  -- the two sets of near-identity elements correspond
  have hmem : ∀ γ : Γ, NearIdAt (e γ : PO n 1) (0 : E n) η ↔ NearIdAt (γ : PO n 1) z η := by
    intro γ
    rw [hcoe γ]
    exact nearIdAt_conj_iff hA hI hg η (γ : PO n 1)
  have hS : e '' {γ : Γ | NearIdAt (γ : PO n 1) z η}
      = {γ' : Γ' | NearIdAt (γ' : PO n 1) (0 : E n) η} := by
    ext γ'
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact (hmem γ).mpr hγ
    · intro hγ'
      refine ⟨e.symm γ', (hmem (e.symm γ')).mp ?_, ?_⟩
      · rwa [MulEquiv.apply_symm_apply]
      · simp
  have hS' : (e : Γ →* Γ') '' {γ : Γ | NearIdAt (γ : PO n 1) z η}
      = {γ' : Γ' | NearIdAt (γ' : PO n 1) (0 : E n) η} := hS
  -- h0 applies to the conjugate group
  have hnil' : Group.IsNilpotent
      (Subgroup.closure {γ' : Γ' | NearIdAt (γ' : PO n 1) (0 : E n) η}) := h0 Γ' hdisc'
  have hisoNil : (Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) z η}).map (e : Γ →* Γ')
      = Subgroup.closure {γ' : Γ' | NearIdAt (γ' : PO n 1) (0 : E n) η} := by
    rw [MonoidHom.map_closure, hS']
  rw [← hisoNil] at hnil'
  exact (Group.isNilpotent_congr
    (e.subgroupMap (Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) z η}))).mpr hnil'

end Work.Mostow
