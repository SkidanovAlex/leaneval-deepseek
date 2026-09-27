import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BoostTransitive

/-! # Area C1 (geomFinite) — thick–thin vocabulary

Definitions for the thick–thin decomposition of a lattice `Γ ≤ PO(n,1)` (the core of
`Work.Mostow.geomFiniteThickThin`).

We split `ℍⁿ` according to which elements of `Γ` move a point very little:

* `ThickPart Γ ε` : every nontrivial element of `Γ` moves `u` by at least `ε`;
* `ThinTube Γ ε`  : some nontrivial `γ` with **no** fixed point in `ℍⁿ` which is **not** parabolic
  moves `u` by less than `ε` (i.e. `u` lies in a tube around the axis of a short loxodromic);
* `ThinCone Γ ε`  : some nontrivial `γ` **with** a fixed point in `ℍⁿ` (a torsion element) moves `u`
  by less than `ε` (i.e. `u` lies near a cone point).

`IsCocompactUnder Γ S` says that `S` is contained in the `Γ`-translates of a compact set.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Classical

noncomputable section

variable {n : ℕ}

/-- The `ε`-thick part: the set of points moved by at least `ε` by every nontrivial element of `Γ`. -/
def ThickPart (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (E n) :=
  {u | ∀ γ : Γ, γ ≠ 1 → ε ≤ hdist u ((γ : PO n 1) • u)}

/-- `S` is contained in the `Γ`-translates of a compact set. -/
def IsCocompactUnder (Γ : Subgroup (PO n 1)) (S : Set (E n)) : Prop :=
  ∃ K : Set (E n), IsCompact K ∧ ∀ u ∈ S, ∃ γ : Γ, (γ : PO n 1) • u ∈ K

/-- Points `u` which are thin because of a nontrivial element without fixed point in `ℍⁿ` that is
not parabolic (a tube point). -/
def ThinTube (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (E n) :=
  {u | ∃ γ : Γ, (∀ p : E n, (γ : PO n 1) • p ≠ p) ∧ ¬ IsParabolic (γ : PO n 1) ∧
        hdist u ((γ : PO n 1) • u) < ε}

/-- Points `u` which are thin because of a nontrivial element with a fixed point in `ℍⁿ`
(a cone point of the quotient orbifold). -/
def ThinCone (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (E n) :=
  {u | ∃ γ : Γ, γ ≠ 1 ∧ (∃ p : E n, (γ : PO n 1) • p = p) ∧
        hdist u ((γ : PO n 1) • u) < ε}

/-- Points moved by less than `ε` by some *parabolic* element of `Γ` (the cusp region). -/
def ThinParabolic (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (E n) :=
  {u | ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ hdist u ((γ : PO n 1) • u) < ε}

/-- A point which is not `ε`-thick is moved by less than `ε` by a nontrivial element of `Γ`; such an
element is either parabolic, or has a fixed point in `ℍⁿ`, or is loxodromic. -/
theorem not_thickPart_imp (Γ : Subgroup (PO n 1)) (ε : ℝ) {u : E n} (hu : u ∉ ThickPart Γ ε) :
    u ∈ ThinParabolic Γ ε ∪ ThinTube Γ ε ∪ ThinCone Γ ε := by
  simp only [ThickPart, Set.mem_ofPred_eq, not_forall, not_le] at hu
  obtain ⟨γ, hγ1, hγ⟩ := hu
  by_cases hpar : IsParabolic (γ : PO n 1)
  · exact Or.inl (Or.inl ⟨γ, hpar, hγ⟩)
  · by_cases hfix : ∃ p : E n, (γ : PO n 1) • p = p
    · exact Or.inr ⟨γ, hγ1, hfix, hγ⟩
    · exact Or.inl (Or.inr ⟨γ, fun p hp => hfix ⟨p, hp⟩, hpar, hγ⟩)

/-- The orbit equivalence relation of `Γ` on the set of parabolic fixed points. -/
def parOrbitSetoid (hA : POActionProp n) (Γ : Subgroup (PO n 1)) :
    Setoid {ξ : E n // ξ ∈ parFixed Γ} where
  r a b := ∃ γ : Γ, bd (γ : PO n 1) a.1 = b.1
  iseqv := by
    obtain ⟨_, _, _, hone, _, _, _, hbdSph, hbdone, hbdmul, _, _⟩ := hA
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, hbdone a.1 a.2.1⟩
    · intro a b h
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ⁻¹, ?_⟩
      calc bd ((γ : PO n 1)⁻¹) b.1
          = bd ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) a.1) := by rw [hγ]
        _ = bd ((γ : PO n 1)⁻¹ * (γ : PO n 1)) a.1 := by
              rw [hbdmul (γ : PO n 1)⁻¹ (γ : PO n 1) a.1 a.2.1]
        _ = bd (1 : PO n 1) a.1 := by rw [inv_mul_cancel]
        _ = a.1 := hbdone a.1 a.2.1
    · intro a b c h1 h2
      obtain ⟨γ₁, hγ₁⟩ := h1
      obtain ⟨γ₂, hγ₂⟩ := h2
      refine ⟨γ₂ * γ₁, ?_⟩
      show bd ((γ₂ : PO n 1) * (γ₁ : PO n 1)) a.1 = c.1
      rw [hbdmul (γ₂ : PO n 1) (γ₁ : PO n 1) a.1 a.2.1, hγ₁, hγ₂]

/-- The representative point of the `Γ`-orbit class `q`. -/
def clRep (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (q : Quotient (parOrbitSetoid hA Γ)) : E n := (Quotient.out q).1

lemma clRep_mem (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (q : Quotient (parOrbitSetoid hA Γ)) : clRep hA Γ q ∈ parFixed Γ := (Quotient.out q).2

/-- The transported cocycle value at `ξ`, relative to the representative of the class `q`:
`bCocy γ (clRep q)` for any `γ` carrying `clRep q` to `ξ` (junk `0` if there is none). -/
def clVal2 (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (q : Quotient (parOrbitSetoid hA Γ)) (ξ : E n) : ℝ :=
  if h : ∃ γ : Γ, bd (γ : PO n 1) (clRep hA Γ q) = ξ then
    bCocy ((h.choose : Γ) : PO n 1) (clRep hA Γ q)
  else 0

/-- The orbit class of `ξ ∈ parFixed Γ`. -/
def clOf (hA : POActionProp n) (Γ : Subgroup (PO n 1)) (ξ : E n)
    (hξ : ξ ∈ parFixed Γ) : Quotient (parOrbitSetoid hA Γ) :=
  Quotient.mk (parOrbitSetoid hA Γ) ⟨ξ, hξ⟩

/-- An explicit `Γ`-equivariant height on `parFixed Γ`: the cocycle transported from a chosen
representative of the orbit. -/
def htFn (hA : POActionProp n) (Γ : Subgroup (PO n 1)) (ξ : E n) : ℝ :=
  if hξ : ξ ∈ parFixed Γ then clVal2 hA Γ (clOf hA Γ ξ hξ) ξ else 0

/-- If `ξ` lies in the class `q`, then some element of `Γ` carries the representative of `q`
to `ξ`. -/
lemma exists_bd_clRep (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (q : Quotient (parOrbitSetoid hA Γ)) (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hq : clOf hA Γ ξ hξ = q) :
    ∃ γ : Γ, bd (γ : PO n 1) (clRep hA Γ q) = ξ := by
  have h1 : Quotient.mk (parOrbitSetoid hA Γ) (Quotient.out q) = q := Quotient.out_eq' q
  have h : Quotient.mk (parOrbitSetoid hA Γ) (Quotient.out q)
      = Quotient.mk (parOrbitSetoid hA Γ) ⟨ξ, hξ⟩ := by
    rw [h1]
    exact hq.symm
  exact Quotient.exact h

/-- The decisive step: `hvan` makes the transported cocycle values independent of the choice of
the element of `Γ` relating two points of the same orbit. -/
lemma bCocy_transport_eq (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (r ξ ξ' : E n) (hr : r ∈ parFixed Γ) (hξ : ξ ∈ parFixed Γ) (hξ' : ξ' ∈ parFixed Γ)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ') (μ₁ : Γ) (hμ₁ : bd (μ₁ : PO n 1) r = ξ)
    (μ₂ : Γ) (hμ₂ : bd (μ₂ : PO n 1) r = ξ') :
    bCocy (μ₂ : PO n 1) r = bCocy (μ₁ : PO n 1) r + bCocy (γ : PO n 1) ξ := by
  have hAc := hA
  obtain ⟨_, _, _, hone, _, _, _, hbdSph, hbdone, hbdmul, _, _⟩ := hA
  have hrS : r ∈ Sph n := hr.1
  set δ : Γ := μ₂⁻¹ * (γ * μ₁) with hδdef
  have hδcoe : (δ : PO n 1) = (μ₂ : PO n 1)⁻¹ * ((γ : PO n 1) * (μ₁ : PO n 1)) := rfl
  have hbr : bd ((γ : PO n 1) * (μ₁ : PO n 1)) r = bd (μ₂ : PO n 1) r := by
    rw [hbdmul (γ : PO n 1) (μ₁ : PO n 1) r hrS, hμ₁, hγ, hμ₂]
  have hδfix : bd (δ : PO n 1) r = r := by
    rw [hδcoe, hbdmul (μ₂ : PO n 1)⁻¹ ((γ : PO n 1) * (μ₁ : PO n 1)) r hrS, hbr,
      ← hbdmul (μ₂ : PO n 1)⁻¹ (μ₂ : PO n 1) r hrS, inv_mul_cancel, hbdone r hrS]
  have hδzero : bCocy (δ : PO n 1) r = 0 := hvan δ r hr hδfix
  have e1 : bCocy (δ : PO n 1) r
      = bCocy ((γ : PO n 1) * (μ₁ : PO n 1)) r
        + bCocy (μ₂ : PO n 1)⁻¹ (bd (μ₂ : PO n 1) r) := by
    rw [hδcoe, bCocy_mul hAc hI (μ₂ : PO n 1)⁻¹ ((γ : PO n 1) * (μ₁ : PO n 1)) r hrS, hbr]
  have e2 : bCocy ((γ : PO n 1) * (μ₁ : PO n 1)) r
      = bCocy (μ₁ : PO n 1) r + bCocy (γ : PO n 1) ξ := by
    rw [bCocy_mul hAc hI (γ : PO n 1) (μ₁ : PO n 1) r hrS, hμ₁]
  have e3 : bCocy (μ₂ : PO n 1)⁻¹ (bd (μ₂ : PO n 1) r) = - bCocy (μ₂ : PO n 1) r := by
    have h := bCocy_mul hAc hI (μ₂ : PO n 1)⁻¹ (μ₂ : PO n 1) r hrS
    rw [inv_mul_cancel, bCocy_one hAc hI r hrS] at h
    linarith
  linarith [hδzero, e1, e2, e3]

/-- Unfolding of `clVal2` at a point known to lie in the orbit. -/
lemma clVal2_apply (hA : POActionProp n) (Γ : Subgroup (PO n 1))
    (q : Quotient (parOrbitSetoid hA Γ)) (ξ : E n)
    (h : ∃ γ : Γ, bd (γ : PO n 1) (clRep hA Γ q) = ξ) :
    clVal2 hA Γ q ξ = bCocy ((h.choose : Γ) : PO n 1) (clRep hA Γ q) := dif_pos h

/-- **The covariance of the transported cocycle value.** Two points of one orbit have heights
differing by the Busemann cocycle of any element carrying one to the other. -/
lemma clVal2_rel (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (q : Quotient (parOrbitSetoid hA Γ)) (ξ ξ' : E n) (hξ : ξ ∈ parFixed Γ)
    (hξ' : ξ' ∈ parFixed Γ) (hqξ : clOf hA Γ ξ hξ = q) (hqξ' : clOf hA Γ ξ' hξ' = q)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ') :
    clVal2 hA Γ q ξ' = clVal2 hA Γ q ξ + bCocy (γ : PO n 1) ξ := by
  set e₁ : ∃ δ : Γ, bd (δ : PO n 1) (clRep hA Γ q) = ξ :=
    exists_bd_clRep hA Γ q ξ hξ hqξ with he₁
  set e₂ : ∃ δ : Γ, bd (δ : PO n 1) (clRep hA Γ q) = ξ' :=
    exists_bd_clRep hA Γ q ξ' hξ' hqξ' with he₂
  have hμ₁ : bd ((Classical.choose e₁ : Γ) : PO n 1) (clRep hA Γ q) = ξ :=
    Classical.choose_spec e₁
  have hμ₂ : bd ((Classical.choose e₂ : Γ) : PO n 1) (clRep hA Γ q) = ξ' :=
    Classical.choose_spec e₂
  rw [clVal2_apply hA Γ q ξ' e₂, clVal2_apply hA Γ q ξ e₁]
  exact bCocy_transport_eq (hA := hA) (hI := hI) (Γ := Γ) (hvan := hvan)
    (r := clRep hA Γ q) (ξ := ξ) (ξ' := ξ') (hr := clRep_mem hA Γ q) (hξ := hξ)
    (hξ' := hξ') (γ := γ) (hγ := hγ) (μ₁ := Classical.choose e₁) (hμ₁ := hμ₁)
    (μ₂ := Classical.choose e₂) (hμ₂ := hμ₂)

/-- **Existence of a `Γ`-equivariant height on the parabolic fixed points.** If the Busemann
cocycle vanishes on the stabiliser of every parabolic fixed point, then the cocycle is a
coboundary on `parFixed Γ`. -/
theorem equivHeight_exists (hA : POActionProp n) (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0) :
    ∃ ht : E n → ℝ, IsEquivHeight Γ (parFixed Γ) ht := by
  have hAkeep : POActionProp n := hA
  obtain ⟨_, _, _, hone, _, _, _, hbdSph, hbdone, hbdmul, _, _⟩ := hA
  refine ⟨htFn hAkeep Γ, ?_⟩
  intro γ ξ hξ
  have hξS : ξ ∈ Sph n := hξ.1
  have hξ' : bd (γ : PO n 1) ξ ∈ parFixed Γ := parFixed_invariant hAkeep hI Γ γ hξ
  have hcl : clOf hAkeep Γ (bd (γ : PO n 1) ξ) hξ' = clOf hAkeep Γ ξ hξ := by
    apply Quotient.sound
    refine ⟨γ⁻¹, ?_⟩
    show bd ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = ξ
    rw [← hbdmul (γ : PO n 1)⁻¹ (γ : PO n 1) ξ hξS, inv_mul_cancel, hbdone ξ hξS]
  simp only [htFn, dif_pos hξ, dif_pos hξ']
  rw [hcl]
  exact clVal2_rel (hA := hAkeep) (hI := hI) (Γ := Γ) (hvan := hvan)
    (q := clOf hAkeep Γ ξ hξ) (ξ := ξ) (ξ' := bd (γ : PO n 1) ξ) (hξ := hξ) (hξ' := hξ')
    (hqξ := rfl) (hqξ' := hcl) (γ := γ) (hγ := rfl)


/-- Elementary inequality: the linear functional `r ↦ √(1+r²) - c r` dominates `√(1-c²)`. -/
lemma sqrt_one_sub_sq_le (c r : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Real.sqrt (1 - c ^ 2) ≤ Real.sqrt (1 + r ^ 2) - c * r := by
  have h1 : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hs2 : (Real.sqrt (1 + r ^ 2)) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : 0 ≤ Real.sqrt (1 + r ^ 2) - c * r := by
    have hr : |r| ≤ Real.sqrt (1 + r ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
    by_cases hr0 : 0 ≤ r
    · have : r ≤ Real.sqrt (1 + r ^ 2) := by rwa [abs_of_nonneg hr0] at hr
      nlinarith [mul_le_mul_of_nonneg_right hc1 hr0]
    · have hrneg : r < 0 := lt_of_not_ge hr0
      have : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hrneg.le
      linarith [Real.sqrt_nonneg (1 + r ^ 2)]
  rw [Real.sqrt_le_iff]
  refine ⟨h2, ?_⟩
  have hAM : 2 * c * r * Real.sqrt (1 + r ^ 2) ≤ (1 + c ^ 2) * r ^ 2 + c ^ 2 := by
    have hsq : (2 * c * r * Real.sqrt (1 + r ^ 2)) ^ 2 ≤ ((1 + c ^ 2) * r ^ 2 + c ^ 2) ^ 2 := by
      rw [mul_pow, mul_pow, hs2]
      nlinarith [sq_nonneg (r ^ 2 * (1 - c ^ 2) - c ^ 2)]
    by_cases hr0 : 0 ≤ r
    · have hL : 0 ≤ 2 * c * r * Real.sqrt (1 + r ^ 2) := by positivity
      have hR : 0 ≤ (1 + c ^ 2) * r ^ 2 + c ^ 2 := by positivity
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hL, abs_of_nonneg hR] at this
    · have hrneg : r < 0 := lt_of_not_ge hr0
      have hL : 2 * c * r * Real.sqrt (1 + r ^ 2) ≤ 0 := by
        have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hrneg.le
        have := mul_nonpos_of_nonpos_of_nonneg hcr (Real.sqrt_nonneg (1 + r ^ 2))
        linarith
      nlinarith [hL, sq_nonneg r, hc0, Real.sqrt_nonneg (1 + r ^ 2)]
  have hexp : (Real.sqrt (1 + r ^ 2) - c * r) ^ 2
      = 1 + r ^ 2 - 2 * c * r * Real.sqrt (1 + r ^ 2) + c ^ 2 * r ^ 2 := by
    rw [sub_sq, hs2]; ring
  rw [hexp]
  linarith [hAM, sq_nonneg c]

/-- **Disjointness criterion for horoballs.** If `exp s + exp t ≤ √(4 - ‖ξ + η‖²)` then the
horoballs at `ξ` and `η` of levels `s` and `t` are disjoint. -/
theorem horoball_disjoint {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) {s t : ℝ}
    (h : Real.exp s + Real.exp t ≤ Real.sqrt (4 - ‖ξ + η‖ ^ 2)) :
    Disjoint (horoball ξ s) (horoball η t) := by
  rw [Set.disjoint_left]
  intro u hu1 hu2
  simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
  have hξn : ‖ξ‖ = 1 := by
    rw [Sph, Metric.mem_sphere, dist_zero_right] at hξ; exact hξ
  have hηn : ‖η‖ = 1 := by
    rw [Sph, Metric.mem_sphere, dist_zero_right] at hη; exact hη
  have hargξ : 0 < tpart u - inner ℝ u ξ := by
    have hcs : inner ℝ u ξ ≤ ‖u‖ := by
      have := real_inner_le_norm u ξ
      rwa [hξn, mul_one] at this
    have hlt : ‖u‖ < tpart u := by
      rw [tpart]
      exact (Real.lt_sqrt (by positivity)).2 (by nlinarith [sq_nonneg ‖u‖])
    linarith
  have hargη : 0 < tpart u - inner ℝ u η := by
    have hcs : inner ℝ u η ≤ ‖u‖ := by
      have := real_inner_le_norm u η
      rwa [hηn, mul_one] at this
    have hlt : ‖u‖ < tpart u := by
      rw [tpart]
      exact (Real.lt_sqrt (by positivity)).2 (by nlinarith [sq_nonneg ‖u‖])
    linarith
  have h1 : tpart u - inner ℝ u ξ < Real.exp s := by
    rw [busemann] at hu1
    exact (Real.log_lt_iff_lt_exp hargξ).1 hu1
  have h2 : tpart u - inner ℝ u η < Real.exp t := by
    rw [busemann] at hu2
    exact (Real.log_lt_iff_lt_exp hargη).1 hu2
  have hcs : inner ℝ u (ξ + η) ≤ ‖u‖ * ‖ξ + η‖ := real_inner_le_norm u (ξ + η)
  have hnormle : ‖ξ + η‖ ≤ 2 := by
    calc ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := norm_add_le _ _
      _ = 2 := by rw [hξn, hηn]; norm_num
  have hc1 : ‖ξ + η‖ / 2 ≤ 1 := by linarith
  have hkey : Real.sqrt (4 - ‖ξ + η‖ ^ 2) ≤ 2 * tpart u - inner ℝ u (ξ + η) := by
    have hrad : (0:ℝ) ≤ 1 - (‖ξ + η‖ / 2) ^ 2 := by
      have h2 : (‖ξ + η‖ / 2) ^ 2 ≤ 1 := by nlinarith [hc1, norm_nonneg (ξ + η)]
      linarith
    have hsq4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hstep : Real.sqrt (4 - ‖ξ + η‖ ^ 2)
        = 2 * Real.sqrt (1 - (‖ξ + η‖ / 2) ^ 2) := by
      rw [← hsq4, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      ring
    rw [hstep, tpart]
    have := sqrt_one_sub_sq_le (‖ξ + η‖ / 2) ‖u‖ (by positivity) hc1
    nlinarith [this, hcs, Real.sqrt_nonneg (1 + ‖u‖ ^ 2)]
  rw [inner_add_right] at hkey
  linarith




/-- The hyperbolic ball `{x | hdist x v < r}` is measurable. -/
lemma measurableSet_hdist_lt (hI : HypIsometryProp n) (v : E n) (r : ℝ) :
    MeasurableSet {x : E n | hdist x v < r} := by
  have hclosed : ∀ t : ℝ, IsClosed {x : E n | hdist x v ≤ t} := by
    intro t
    have h1 : {x : E n | hdist x v ≤ t} = {x : E n | hdist v x ≤ t} := by
      refine Set.ext fun x => ?_
      show hdist x v ≤ t ↔ hdist v x ≤ t
      rw [hI.2.1 x v]
    rw [h1]
    exact (hI.2.2.2.2.2.1 v t).isClosed
  have hUnion : {x : E n | hdist x v < r}
      = ⋃ m : ℕ, {x : E n | hdist x v ≤ r - 1 / (m + 1 : ℝ)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      have hpos : 0 < r - hdist x v := sub_pos.2 hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, by linarith [le_of_lt hm]⟩
    · rintro ⟨m, hm⟩
      have h1 : 0 < (1 : ℝ) / (m + 1) := by positivity
      linarith
  rw [hUnion]
  exact MeasurableSet.iUnion fun m => (hclosed _).measurableSet

/-- **Homogeneity of hyperbolic balls** in the form needed for the volume argument: the volume of
the hyperbolic ball of radius `r` is the same at every centre. -/
theorem volH_hdist_ball_homogeneous (hA : POActionProp n) (hI : HypIsometryProp n)
    (u v : E n) (r : ℝ) :
    volH n {x : E n | hdist x u < r} = volH n {x : E n | hdist x v < r} := by
  obtain ⟨g, hg⟩ := (BoostTransitive n hA).2 u v
  have hmp : MeasurePreserving (fun y : E n => g • y) (volH n) (volH n) :=
    hI.2.2.2.2.2.2.2.2.2.2.2.1 g
  have hiso : ∀ a b : E n, hdist (g • a) (g • b) = hdist a b := fun a b => hI.2.2.2.2.2.2.1 g a b
  have hpre : (fun y : E n => g • y) ⁻¹' {y : E n | hdist y v < r}
      = {x : E n | hdist x u < r} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hg, hiso x u]
  have key : volH n {y : E n | hdist y v < r} = volH n {x : E n | hdist x u < r} := by
    calc volH n {y : E n | hdist y v < r}
        = ((volH n).map (fun y : E n => g • y)) {y : E n | hdist y v < r} := by
            rw [hmp.map_eq]
      _ = volH n ((fun y : E n => g • y) ⁻¹' {y : E n | hdist y v < r}) :=
            Measure.map_apply hmp.measurable (measurableSet_hdist_lt hI v r)
      _ = volH n {x : E n | hdist x u < r} := by rw [hpre]
  exact key.symm


end

end Work.Mostow
