import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.properAction
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.addSubgroupEqZmultiples
import Submission.Work.Mostow.pairStabBusemannNearFinite

/-!
# Discreteness of the Busemann cocycle on the stabiliser of a pair of boundary points

Let `Λ ≤ PO n 1` be discrete and let `ξ ≠ η` be two points of the boundary sphere.  The elements
of `Λ` fixing both `ξ` and `η` form a subgroup `Λ_{ξη}`, and the Busemann cocycle
`β γ = busemann ξ (γ • 0)` is a homomorphism `Λ_{ξη} → (ℝ,+)` (the cocycle identity holds
whenever `bd γ ξ = ξ`).

If some point `p` has `hdist p (g • p) = |β g|` for every `g` fixing the pair, then two distinct
elements of `Λ_{ξη}` with the same value of `β` displace `p` by the same amount; hence for every
`R` the elements with `|β γ| ≤ R` lie in a ball of radius `2 hdist 0 p + R` around `0` and are
therefore finite by properness of the action (`Work.Mostow.finite_nearStab`).  Consequently the
image of `β` is a discrete subgroup of `ℝ`, hence of the form `cℤ`; and the kernel of `β`
consists of elements displacing `p` by `0`, so it is finite as well.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The subgroup of `Λ` of elements fixing the boundary points `ξ` and `η`. -/
def pairStab (hA : POActionProp n) (Λ : Subgroup (PO n 1)) (ξ η : E n)
    (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) : Subgroup Λ where
  carrier := {γ | bd (γ : PO n 1) ξ = ξ ∧ bd (γ : PO n 1) η = η}
  one_mem' := by
    have hP := POBasic.ofProp hA
    exact ⟨by simpa using hP.bd_one ξ hξ, by simpa using hP.bd_one η hη⟩
  mul_mem' := by
    have hP := POBasic.ofProp hA
    rintro γ₁ γ₂ ⟨h1, h2⟩ ⟨h3, h4⟩
    constructor
    · show bd ((γ₁ : PO n 1) * (γ₂ : PO n 1)) ξ = ξ
      rw [hP.bd_mul (γ₁ : PO n 1) (γ₂ : PO n 1) ξ hξ, h3, h1]
    · show bd ((γ₁ : PO n 1) * (γ₂ : PO n 1)) η = η
      rw [hP.bd_mul (γ₁ : PO n 1) (γ₂ : PO n 1) η hη, h4, h2]
  inv_mem' := by
    have hP := POBasic.ofProp hA
    rintro γ ⟨h1, h2⟩
    constructor
    · show bd ((γ : PO n 1))⁻¹ ξ = ξ
      have h := hP.bd_mul ((γ : PO n 1))⁻¹ (γ : PO n 1) ξ hξ
      rw [inv_mul_cancel, hP.bd_one ξ hξ, h1] at h
      exact h.symm
    · show bd ((γ : PO n 1))⁻¹ η = η
      have h := hP.bd_mul ((γ : PO n 1))⁻¹ (γ : PO n 1) η hη
      rw [inv_mul_cancel, hP.bd_one η hη, h2] at h
      exact h.symm

/-- The Busemann cocycle is additive on the stabiliser of a boundary point. -/
lemma busemann_stab_mul (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (g h : PO n 1) (hg : bd g ξ = ξ) :
    busemann ξ ((g * h) • (0 : E n))
      = busemann ξ (g • (0 : E n)) + busemann ξ (h • (0 : E n)) := by
  have hP := POBasic.ofProp hA
  have hH := HypIsoData.ofProp hI
  have hb := hH.busemann_cocycle g ξ (h • (0 : E n)) hξ
  rw [hg, ← hP.mul_smul g h (0 : E n)] at hb
  linarith [hb]

/-- A boundary point fixed by `g` is fixed by `g⁻¹`. -/
lemma bd_inv_eq (hA : POActionProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1)
    (hg : bd g ξ = ξ) : bd g⁻¹ ξ = ξ := by
  have hP := POBasic.ofProp hA
  have h := hP.bd_mul g⁻¹ g ξ hξ
  rw [inv_mul_cancel, hP.bd_one ξ hξ, hg] at h
  exact h.symm

/-- The Busemann cocycle is odd on the stabiliser of a boundary point. -/
lemma busemann_stab_inv (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1) (hg : bd g ξ = ξ) :
    busemann ξ (g⁻¹ • (0 : E n)) = - busemann ξ (g • (0 : E n)) := by
  have hP := POBasic.ofProp hA
  have h1 := busemann_stab_mul hA hI ξ hξ g⁻¹ g (bd_inv_eq hA ξ hξ g hg)
  rw [inv_mul_cancel, hP.one_smul, busemann_zero] at h1
  linarith [h1]

/-- The Busemann cocycle of an element of the pair stabiliser. -/
def beta {hA : POActionProp n} {Λ : Subgroup (PO n 1)} {ξ η : E n} {hξ : ξ ∈ Sph n}
    {hη : η ∈ Sph n} (γ : pairStab hA Λ ξ η hξ hη) : ℝ :=
  busemann ξ (((γ : Λ) : PO n 1) • (0 : E n))

lemma beta_one {hA : POActionProp n} {Λ : Subgroup (PO n 1)} {ξ η : E n} {hξ : ξ ∈ Sph n}
    {hη : η ∈ Sph n} : beta (1 : pairStab hA Λ ξ η hξ hη) = 0 := by
  have hP := POBasic.ofProp hA
  simp only [beta]
  rw [show (((1 : pairStab hA Λ ξ η hξ hη) : Λ) : PO n 1) = 1 from rfl, hP.one_smul,
    busemann_zero]

lemma beta_add {hA : POActionProp n} {hI : HypIsometryProp n} {Λ : Subgroup (PO n 1)}
    {ξ η : E n} {hξ : ξ ∈ Sph n} {hη : η ∈ Sph n}
    (γ₁ γ₂ : pairStab hA Λ ξ η hξ hη) : beta (γ₁ * γ₂) = beta γ₁ + beta γ₂ := by
  have h := busemann_stab_mul hA hI ξ hξ (((γ₁ : Λ) : PO n 1)) (((γ₂ : Λ) : PO n 1)) γ₁.2.1
  have hc : (((γ₁ * γ₂ : pairStab hA Λ ξ η hξ hη) : Λ) : PO n 1)
      = (((γ₁ : Λ) : PO n 1)) * (((γ₂ : Λ) : PO n 1)) := rfl
  simp only [beta]
  rw [hc]
  linarith [h]

lemma beta_inv {hA : POActionProp n} {hI : HypIsometryProp n} {Λ : Subgroup (PO n 1)}
    {ξ η : E n} {hξ : ξ ∈ Sph n} {hη : η ∈ Sph n}
    (γ : pairStab hA Λ ξ η hξ hη) : beta γ⁻¹ = - beta γ := by
  have h := busemann_stab_inv hA hI ξ hξ (((γ : Λ) : PO n 1)) γ.2.1
  have hc : (((γ⁻¹ : pairStab hA Λ ξ η hξ hη) : Λ) : PO n 1) = (((γ : Λ) : PO n 1))⁻¹ := rfl
  simp only [beta]
  rw [hc]
  linarith [h]

/-- The set of Busemann cocycle values of the pair stabiliser, as an additive subgroup of `ℝ`. -/
def cocycleRange (hA : POActionProp n) (hI : HypIsometryProp n) (Λ : Subgroup (PO n 1))
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) : AddSubgroup ℝ where
  carrier := Set.range (fun γ : pairStab hA Λ ξ η hξ hη => beta γ)
  zero_mem' := ⟨1, beta_one⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨γ₁, hγ₁⟩ := ha
    obtain ⟨γ₂, hγ₂⟩ := hb
    have h1 : beta γ₁ = a := hγ₁
    have h2 : beta γ₂ = b := hγ₂
    refine ⟨γ₁ * γ₂, ?_⟩
    show beta (γ₁ * γ₂) = a + b
    rw [beta_add (hI := hI), h1, h2]
  neg_mem' := by
    intro a ha
    obtain ⟨γ, hγ⟩ := ha
    have h1 : beta γ = a := hγ
    refine ⟨γ⁻¹, ?_⟩
    show beta γ⁻¹ = -a
    rw [beta_inv (hI := hI), h1]

/-- The cocycle values of the pair stabiliser are a discrete subgroup of `ℝ`: for every `R` only
finitely many of them lie in `[-R,R]`. -/
lemma cocycleRange_finite (hA : POActionProp n) (hI : HypIsometryProp n) (Λ : Subgroup (PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Λ)) (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hpair : ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))|) (R : ℝ) :
    ((cocycleRange hA hI Λ ξ η hξ hη : Set ℝ) ∩ Set.Icc (-R) R).Finite := by
  by_cases hR : 0 ≤ R
  · obtain ⟨p, hp⟩ := hpair
    have hF := pairStabBusemannNearFinite n hA hI Λ hdisc ξ η hξ hη p hp R
    refine (hF.image (fun γ : Λ => busemann ξ ((γ : PO n 1) • (0 : E n)))).subset ?_
    rintro x ⟨⟨γ, rfl⟩, hxI⟩
    have hxabs : |beta γ| ≤ R := by
      have h1 := (Set.mem_Icc.mp hxI).1
      have h2 := (Set.mem_Icc.mp hxI).2
      rw [abs_le]
      exact ⟨h1, h2⟩
    refine ⟨(γ : Λ), ?_, ?_⟩
    · exact ⟨γ.2.1, γ.2.2, by simpa only [beta] using hxabs⟩
    · simp only [beta]
  · refine Set.Finite.subset (Set.finite_empty) ?_
    rintro x ⟨-, hxI⟩
    have h1 := (Set.mem_Icc.mp hxI).1
    have h2 := (Set.mem_Icc.mp hxI).2
    linarith

theorem pairStabCocycleDiscrete (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Λ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Λ)) (ξ η : E n) (hξ : ξ ∈ Sph n)
    (hη : η ∈ Sph n) (hne : ξ ≠ η)
    (hpair : ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
        hdist p (g • p) = |busemann ξ (g • (0 : E n))|) :
    ∃ c : ℝ, (∀ γ : Λ, bd (γ : PO n 1) ξ = ξ → bd (γ : PO n 1) η = η →
        ∃ m : ℤ, busemann ξ ((γ : PO n 1) • (0 : E n)) = m * c) ∧
      {γ : Λ | bd (γ : PO n 1) ξ = ξ ∧ bd (γ : PO n 1) η = η ∧
          busemann ξ ((γ : PO n 1) • (0 : E n)) = 0}.Finite := by
  obtain ⟨c, hc⟩ := addSubgroupEqZmultiples (cocycleRange hA hI Λ ξ η hξ hη)
    (cocycleRange_finite hA hI Λ hdisc ξ η hξ hη hpair)
  refine ⟨c, ?_, ?_⟩
  · intro γ hγξ hγη
    have hmem : busemann ξ ((γ : PO n 1) • (0 : E n))
        ∈ (cocycleRange hA hI Λ ξ η hξ hη : Set ℝ) :=
      ⟨⟨(γ : Λ), ⟨hγξ, hγη⟩⟩, by simp only [beta]⟩
    rw [hc] at hmem
    obtain ⟨m, hm⟩ := hmem
    exact ⟨m, hm.symm⟩
  · obtain ⟨p, hp⟩ := hpair
    have hH := HypIsoData.ofProp hI
    refine (finite_nearStab (POBasic.ofProp hA) hH hdisc (2 * hdist (0 : E n) p)).subset ?_
    intro γ hγ
    obtain ⟨h1, h2, h3⟩ := hγ
    have hz : hdist p ((γ : PO n 1) • p) = 0 := by
      rw [hp (γ : PO n 1) h1 h2, h3, abs_zero]
    have h1' := hH.triangle (0 : E n) p ((γ : PO n 1) • (0 : E n))
    have h2' := hH.triangle p ((γ : PO n 1) • p) ((γ : PO n 1) • (0 : E n))
    have h3' : hdist ((γ : PO n 1) • p) ((γ : PO n 1) • (0 : E n)) = hdist (0 : E n) p := by
      rw [hH.isom_smul (γ : PO n 1) p (0 : E n), hH.symm p (0 : E n)]
    calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) p + hdist p ((γ : PO n 1) • (0 : E n)) := h1'
      _ ≤ hdist (0 : E n) p + (hdist p ((γ : PO n 1) • p)
            + hdist ((γ : PO n 1) • p) ((γ : PO n 1) • (0 : E n))) := by linarith
      _ = hdist (0 : E n) p + (0 + hdist (0 : E n) p) := by rw [hz, h3']
      _ = 2 * hdist (0 : E n) p := by ring

end

end Work.Mostow
