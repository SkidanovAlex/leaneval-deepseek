import Mathlib
import Submission.Mostow.Interfaces

/-! # Area C1 (geomFinite) — shared vocabulary

Helper definitions and small lemmas for the geometric-finiteness development.
Used by `Work.Mostow.geomFinite` and by the delegated chapters (G1–G8).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Boundary fixed points of `g` (in the chart `E n`). -/
def bdFix (g : PO n 1) : Set (E n) := {ξ | ξ ∈ Sph n ∧ bd g ξ = ξ}

/-- The set of parabolic fixed points of `Γ`: points of the boundary sphere that are
fixed by a parabolic element of `Γ`. -/
def parFixed (Γ : Subgroup (PO n 1)) : Set (E n) :=
  {ξ | ξ ∈ Sph n ∧ ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ}

/-- The Busemann cocycle `c_γ(ξ) = β_{γξ}(γ·0)`. -/
def bCocy (γ : PO n 1) (ξ : E n) : ℝ := busemann (bd γ ξ) (γ • (0 : E n))

/-- A height function `ht` is `Γ`-equivariant on `P` when it solves the Busemann cochain
equation; this is exactly what makes the horoball family `{horoball ξ (ht ξ)}` `Γ`-invariant. -/
def IsEquivHeight (Γ : Subgroup (PO n 1)) (P : Set (E n)) (ht : E n → ℝ) : Prop :=
  ∀ (γ : Γ) (ξ : E n), ξ ∈ P → ht (bd (γ : PO n 1) ξ) = ht ξ + bCocy (γ : PO n 1) ξ

/-- Shortening the horoball preserves inclusion. -/
lemma horoball_mono {ξ : E n} {s t : ℝ} (h : s ≤ t) : horoball ξ s ⊆ horoball ξ t :=
  fun _ hu => lt_of_lt_of_le hu h

/-- The cocycle identity `c_{gh} = c_h + c_g ∘ (bd h)`. -/
lemma bCocy_mul (hA : POActionProp n) (hI : HypIsometryProp n)
    (g h : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) :
    bCocy (g * h) ξ = bCocy h ξ + bCocy g (bd h ξ) := by
  obtain ⟨_,_,_,_,hmul,_,_,hbdSph,_,hbdmul,_,_⟩ := hA
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbus⟩ := hI
  simp only [bCocy]
  rw [hbdmul g h ξ hξ, hmul g h 0]
  rw [hbus g (bd h ξ) (h • 0) (hbdSph h ξ hξ)]

/-- `c_1(ξ) = 0` on the sphere. -/
lemma bCocy_one (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) : bCocy (1 : PO n 1) ξ = 0 := by
  obtain ⟨_,_,_,hone,_,_,_,_,hbdone,_,_,_⟩ := hA
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbus⟩ := hI
  simp only [bCocy]
  rw [hbdone ξ hξ, hone 0]
  simp [busemann, tpart]


/-- Conjugation preserves parabolicity. -/
lemma isParabolic_conj (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (γ : PO n 1) (hγ : IsParabolic γ) :
    IsParabolic (g * γ * g⁻¹) := by
  obtain ⟨_,_,_,hone,hmul,_,_,_,_,_,_,_⟩ := hA
  obtain ⟨_,_,_,_,_,_,hisom,_,_,_,_,_,_⟩ := hI
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hmul, hmul] at hu
    have h1 : g⁻¹ • (g • (γ • (g⁻¹ • u))) = g⁻¹ • u := by rw [hu]
    rw [← hmul g⁻¹ g (γ • (g⁻¹ • u)), inv_mul_cancel, hone] at h1
    exact hγ.1 (g⁻¹ • u) h1
  · intro ε hε
    obtain ⟨u, hu⟩ := hγ.2 ε hε
    refine ⟨g • u, ?_⟩
    have hthis : (g * γ * g⁻¹) • (g • u) = g • (γ • u) := by
      rw [hmul, hmul, ← hmul g⁻¹ g u, inv_mul_cancel, hone]
    rw [hthis, hisom g u (γ • u)]
    exact hu

/-- `parFixed Γ` is `Γ`-invariant. -/
lemma parFixed_invariant (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (γ : Γ) {ξ : E n} (hξ : ξ ∈ parFixed Γ) :
    bd (γ : PO n 1) ξ ∈ parFixed Γ := by
  have hA' := hA
  have hI' := hI
  obtain ⟨_,_,_,hone,_,_,_,hbdSph,hbdone,hbdmul,_,_⟩ := hA
  obtain ⟨hξS, δ, hδpar, hδfix⟩ := hξ
  set δ' : Γ := ⟨(γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹,
      mul_mem (mul_mem γ.2 δ.2) (inv_mem γ.2)⟩ with hδ'def
  refine ⟨hbdSph (γ : PO n 1) ξ hξS, δ', ?_, ?_⟩
  · have e : (δ' : PO n 1) = (γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹ := rfl
    rw [e]
    exact isParabolic_conj hA' hI' _ _ hδpar
  · have e : (δ' : PO n 1) = (γ : PO n 1) * (δ : PO n 1) * (γ : PO n 1)⁻¹ := rfl
    rw [e]
    rw [hbdmul ((γ : PO n 1) * (δ : PO n 1)) ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ)
          (hbdSph (γ : PO n 1) ξ hξS)]
    have h2 : bd ((γ : PO n 1)⁻¹ * (γ : PO n 1)) ξ = ξ := by
      rw [inv_mul_cancel, hbdone ξ hξS]
    rw [hbdmul ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξS] at h2
    rw [h2, hbdmul (γ : PO n 1) (δ : PO n 1) ξ hξS, hδfix]

/-- Equivariant heights give `Γ`-invariant horoballs. -/
lemma horoball_equiv_of_height (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (P : Set (E n)) (ht : E n → ℝ) (hPsub : P ⊆ Sph n)
    (h : IsEquivHeight Γ P ht) :
    ∀ (γ : Γ) (ξ : E n), ξ ∈ P → ∀ u : E n,
      γ • u ∈ horoball (bd γ ξ) (ht (bd γ ξ)) ↔ u ∈ horoball ξ (ht ξ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbus⟩ := hI
  intro γ ξ hξ u
  have hξS : ξ ∈ Sph n := hPsub hξ
  change (γ : PO n 1) • u ∈ horoball (bd (γ : PO n 1) ξ) (ht (bd (γ : PO n 1) ξ)) ↔
    u ∈ horoball ξ (ht ξ)
  simp only [horoball, Set.mem_ofPred_eq]
  rw [hbus (γ : PO n 1) ξ u hξS, h γ ξ hξ, bCocy]
  constructor <;> intro hh <;> linarith


/-- `Γ` acts cocompactly on the horospheres at `ξ`: every horosphere level has a compact
`Γ_ξ`-fundamental set. This is the "cusp stabiliser is cocompact on the horosphere" clause. -/
def CuspCocompact (Γ : Subgroup (PO n 1)) (ξ : E n) : Prop :=
  ∀ t : ℝ, ∃ K : Set (E n), IsCompact K ∧
    ∀ u : E n, busemann ξ u = t →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K

/-- The existence of `Γ`-invariant disjoint cusp horoballs (based at the parabolic fixed
points `parFixed Γ`) whose complement is `Γ`-cocompact. This is the geometric core of
`GeomFiniteProp`. -/
def HasCuspHoroballs (Γ : Subgroup (PO n 1)) : Prop :=
  ∃ ht : E n → ℝ, IsEquivHeight Γ (parFixed Γ) ht ∧
    (parFixed Γ).Pairwise (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η))) ∧
    (∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
        (∀ ξ ∈ parFixed Γ, u ∉ horoball ξ (ht ξ)) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K)


/-- Assembly: the four chapters (classification of parabolics, stabiliser-preserves-horospheres,
existence of cusp horoballs with cocompact complement, cusp cocompactness) imply `GeomFiniteProp`. -/
theorem geomFinite_of_pieces (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hClass : ∀ g : PO n 1, IsParabolic g → ∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ)
    (hStab : ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
        ∀ ξ : E n, ξ ∈ parFixed Γ → ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hGeo : ∀ (Γ : Subgroup (PO n 1)), HypLattice Γ →
        (∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0) →
        HasCuspHoroballs Γ)
    (hCusp : ∀ (Γ : Subgroup (PO n 1)), HypLattice Γ → ∀ ξ : E n, ξ ∈ parFixed Γ →
        (∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) →
        CuspCocompact Γ ξ) :
    GeomFiniteProp n := by
  intro Γ hΓ
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  have hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ ξ hξ hγ => hStab Γ hdisc ξ hξ γ hγ
  obtain ⟨ht, heq, hdisj, K, hKc, hK⟩ := hGeo Γ hΓ hvan
  refine ⟨parFixed Γ, ht, ?_, ?_, ?_, hdisj, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ; exact hξ.1
  · intro γ ξ hξ; exact parFixed_invariant hA hI Γ γ hξ
  · exact horoball_equiv_of_height hA hI Γ (parFixed Γ) ht (fun ξ hξ => hξ.1) heq
  · refine ⟨K, hKc, ?_⟩
    intro u hu
    obtain ⟨γ, hγ⟩ := hK u hu
    exact ⟨γ, hγ⟩
  · intro ξ hξ; exact hCusp Γ hΓ ξ hξ hvan (ht ξ)
  · intro ξ hξ
    obtain ⟨-, γ, hpar, hfix⟩ := hξ
    exact ⟨γ, hpar, hfix⟩
  · intro γ hγpar
    obtain ⟨ξ, hξS, hfix⟩ := hClass (γ : PO n 1) hγpar
    exact ⟨ξ, ⟨hξS, γ, hγpar, hfix⟩, hfix⟩


/-- Adding a constant to an equivariant height keeps it equivariant. -/
lemma IsEquivHeight.add_const {Γ : Subgroup (PO n 1)} {P : Set (E n)} {ht : E n → ℝ}
    (h : IsEquivHeight Γ P ht) (c : ℝ) :
    IsEquivHeight Γ P (fun ξ => ht ξ + c) := by
  intro γ ξ hξ
  simp only [h γ ξ hξ]
  ring

/-- Pointwise minimum of two equivariant heights is equivariant. -/
lemma IsEquivHeight.infH {Γ : Subgroup (PO n 1)} {P : Set (E n)} {ht ht' : E n → ℝ}
    (h : IsEquivHeight Γ P ht) (h' : IsEquivHeight Γ P ht') :
    IsEquivHeight Γ P (fun ξ => Min.min (ht ξ) (ht' ξ)) := by
  intro γ ξ hξ
  simp only
  rw [h γ ξ hξ, h' γ ξ hξ, min_add_add_right]

/-- A parabolic element is not the identity. -/
lemma isParabolic_ne_one (hA : POActionProp n) {g : PO n 1} (hg : IsParabolic g) :
    g ≠ 1 := by
  intro h
  subst h
  exact hg.1 0 (hA.2.2.2.1 0)

end

end Work.Mostow
