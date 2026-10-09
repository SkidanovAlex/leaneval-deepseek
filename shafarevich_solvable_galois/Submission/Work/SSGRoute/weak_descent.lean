import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Central descent for anti-fixed elements: the weak (correct) hypothesis

`Work.SSGRoute.central_descent_antifixed_weak` is the descent step used to prove that *every*
anti-fixed element of `Q_σ = F(n)/F(n)^{(σ)}` is a `δ`-difference (Schmidt–Wingberg's `p = 2`
correction, needed to lift `2`-torsion along the refined filtration).

It differs from `Work.SSGRoute.central_descent_antifixed` in the hypothesis on the central
subgroup `C ◁ Q`: the strong form asks that every anti-fixed `c ∈ C` be a `δ`-difference *inside*
`C` (`∃ e ∈ C, c = (δe)⁻¹e`).  That strong form is **false** for the graded pieces of the refined
filtration: e.g. for `F = F(a,b)`, `δ : a ↔ b`, `p = 2`, the graded piece
`E_{(2,2)} = F_{(2,2)}/F_{(3,1)} ≅ γ₂/γ₂²γ₃ ≅ 𝔽₂` carries the *trivial* `δ`-action, so
`(δe)⁻¹e = e⁻¹e = 1` for every `e ∈ E_{(2,2)}`, while `[a,b] ≠ 1` is anti-fixed.  What is true (and
what the graded-piece computation `Work.SSGRoute.gradedPiece_*` provides) is the *ambient* form:
every anti-fixed `c ∈ C` is a `δ`-difference in `Q` (here `[a,b] = ν(ab)` in
`Q_{(3,1)} = F/P₃`).

The proof is the same bookkeeping as in the strong version; only the final step changes, using the
centrality of `c = ν(e)` in `Q` (rather than `e ∈ C`).

## Statement

If
* `C ◁ Q` is `δ`-stable and central in `Q`,
* every anti-fixed `c ∈ C` is a `δ`-difference in `Q` (`∃ e : Q, c = (δe)⁻¹ * e`), and
* every anti-fixed element of `Q ⧸ C` is a `δ`-difference,
then every anti-fixed element of `Q` is a `δ`-difference.
-/

namespace Work.SSGRoute

/-- **Central descent, weak hypothesis.** -/
theorem central_descent_antifixed_weak (Q : Type*) [Group Q] (δ : Q ≃* Q) (hδ : δ * δ = 1)
    (C : Subgroup Q) [C.Normal]
    (hC : C ≤ Subgroup.comap (δ : Q →* Q) C)
    (hcent : ∀ (c : C) (x : Q), (c : Q) * x = x * (c : Q))
    (hstep : ∀ c : C, δ (c : Q) = (c : Q)⁻¹ → ∃ e : Q, (c : Q) = (δ e)⁻¹ * e)
    (hquot : ∀ x : Q ⧸ C, (QuotientGroup.map C C (δ : Q →* Q) hC) x = x⁻¹ →
      ∃ r : Q ⧸ C, x = ((QuotientGroup.map C C (δ : Q →* Q) hC) r)⁻¹ * r) :
    ∀ x : Q, δ x = x⁻¹ → ∃ r : Q, x = (δ r)⁻¹ * r := by
  intro x hx
  have hδδ : ∀ y : Q, δ (δ y) = y := by
    intro y
    have h1 : (δ * δ) y = y := by rw [hδ]; rfl
    simpa using h1
  -- the class of `x` is anti-fixed in `Q ⧸ C`
  have hxq : (QuotientGroup.map C C (δ : Q →* Q) hC) (QuotientGroup.mk' C x) =
      (QuotientGroup.mk' C x)⁻¹ := by
    rw [QuotientGroup.map_mk', ← map_inv]
    rw [show (δ : Q →* Q) x = x⁻¹ from hx]
    rfl
  obtain ⟨rq, hrq⟩ := hquot _ hxq
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective C rq
  -- `x' := (δ r)⁻¹ * r` is anti-fixed
  have hx' : δ ((δ r)⁻¹ * r) = ((δ r)⁻¹ * r)⁻¹ := by
    rw [map_mul, map_inv, hδδ r, mul_inv_rev, inv_inv]
  -- `x'` has the same class as `x`
  have hcls : QuotientGroup.mk' C ((δ r)⁻¹ * r) = QuotientGroup.mk' C x := by
    rw [map_mul (QuotientGroup.mk' C), map_inv (QuotientGroup.mk' C)]
    have h1 : QuotientGroup.mk' C (δ r) =
        (QuotientGroup.map C C (δ : Q →* Q) hC) rq := by
      rw [← hr, QuotientGroup.map_mk']
      rfl
    rw [h1, hr]
    exact hrq.symm
  -- `c := x * x'⁻¹ ∈ C`
  have hmem : x * ((δ r)⁻¹ * r)⁻¹ ∈ C := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' C (x * ((δ r)⁻¹ * r)⁻¹) = 1
    rw [map_mul (QuotientGroup.mk' C), map_inv (QuotientGroup.mk' C), hcls, mul_inv_cancel]
  have hcentc : ∀ y : Q, (x * ((δ r)⁻¹ * r)⁻¹) * y = y * (x * ((δ r)⁻¹ * r)⁻¹) :=
    fun y => hcent ⟨_, hmem⟩ y
  -- `c` is anti-fixed
  have hckey : x⁻¹ * ((δ r)⁻¹ * r) = ((δ r)⁻¹ * r) * x⁻¹ := by
    have h4 : (x * ((δ r)⁻¹ * r)⁻¹) * x = x * (x * ((δ r)⁻¹ * r)⁻¹) := hcentc x
    have h5 := congrArg (fun z => x⁻¹ * z) h4
    simp only [mul_assoc, inv_mul_cancel_left] at h5
    have h6 := congrArg (fun z : Q => z⁻¹) h5
    simpa using h6
  have hcfix : δ (x * ((δ r)⁻¹ * r)⁻¹) = (x * ((δ r)⁻¹ * r)⁻¹)⁻¹ := by
    rw [map_mul, map_inv, hx, hx']
    simp only [inv_inv, mul_inv_rev]
    exact hckey
  -- the step hypothesis on `C`: a witness `e` **in `Q`**
  obtain ⟨e, he⟩ := hstep ⟨_, hmem⟩ hcfix
  have he' : x * ((δ r)⁻¹ * r)⁻¹ = (δ e)⁻¹ * e := he
  have hc_mem : (δ e)⁻¹ * e ∈ C := by
    rw [← he']
    exact hmem
  refine ⟨e * r, ?_⟩
  have hx1 : x = ((δ e)⁻¹ * e) * ((δ r)⁻¹ * r) := by
    rw [← he', mul_assoc, inv_mul_cancel, mul_one]
  -- `c = (δe)⁻¹e` is central in `Q`, so it commutes with `(δ r)⁻¹`
  have hkey : ((δ e)⁻¹ * e) * ((δ r)⁻¹ * r) = (δ r)⁻¹ * (δ e)⁻¹ * (e * r) := by
    rw [show ((δ e)⁻¹ * e) * ((δ r)⁻¹ * r) = ((δ e)⁻¹ * e) * (δ r)⁻¹ * r from by group]
    rw [hcent ⟨(δ e)⁻¹ * e, hc_mem⟩ ((δ r)⁻¹)]
    group
  rw [hx1, hkey]
  simp only [map_mul, mul_inv_rev]

end Work.SSGRoute
