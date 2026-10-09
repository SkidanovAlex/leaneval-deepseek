import Mathlib
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.gamma_commutator_jacobi_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The graded Lie ring of the lower central series

For a group `G` we write `Gam k = (⊤ : Subgroup G).lowerCentralSeries k`, so that `Gam 0 = ⊤`,
`Gam 1 = G'` and `⁅Gam p, Gam q⁆ ≤ Gam (p+q+1)`.

This file collects the element level group theory which makes the associated graded object of the
lower central series a graded Lie ring: for `a ∈ Gam p`, `b ∈ Gam q`, `c ∈ Gam r` the commutator is
bilinear, alternating, and satisfies the Jacobi identity modulo the next terms of the series, the
deviations being produced by conjugation and by the Hall–Witt identity.  The sharp moduli below
(`Gam (p+q+2)` for bilinearity and `Gam (p+q+r+3)` for Jacobi) are exactly what is needed so that
the graded pieces `Λ k = Gam k / Gam (k+1)` carry a Lie bracket with `⁅Λ p, Λ q⁆ ⊆ Λ (p+q+1)`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace graded

variable {G : Type*} [Group G]

/-- The `k`-th term of the lower central series (Mathlib indexing: `Gam 0 = ⊤`, `Gam 1 = G'`). -/
def Gam (k : ℕ) : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries k

@[simp] theorem Gam_zero : Gam (G := G) 0 = ⊤ := rfl

theorem Gam_succ (k : ℕ) : Gam (G := G) (k + 1) = ⁅Gam (G := G) k, ⊤⁆ := rfl

theorem Gam_antitone : Antitone (Gam (G := G)) := Subgroup.lowerCentralSeries_antitone ⊤

theorem Gam_succ_le (k : ℕ) : Gam (G := G) (k + 1) ≤ Gam k :=
  Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ k)

instance Gam_normal (k : ℕ) : (Gam (G := G) k).Normal := by
  induction k with
  | zero => rw [Gam_zero]; infer_instance
  | succ k ih => rw [Gam_succ]; infer_instance

/-- If `a ∈ γ_p` and `b ∈ γ_q` then `⁅a,b⁆ ∈ γ_{p+q+1}`. -/
theorem commutator_mem_Gam {p q : ℕ} {a b : G} (ha : a ∈ Gam (G := G) p)
    (hb : b ∈ Gam (G := G) q) : ⁅a, b⁆ ∈ Gam (G := G) (p + q + 1) :=
  commutator_lowerCentralSeries_le G p q (Subgroup.commutator_mem_commutator ha hb)

/-- Conjugation by an arbitrary element is trivial modulo the next term of the series. -/
theorem conj_diff_mem (k : ℕ) {u : G} (hu : u ∈ Gam (G := G) k) (v : G) :
    v * u * v⁻¹ * u⁻¹ ∈ Gam (G := G) (k + 1) := by
  have h1 : ⁅u, v⁆ ∈ Gam (G := G) (k + 1) := by
    rw [Gam_succ]
    exact Subgroup.commutator_mem_commutator hu
      (show v ∈ (⊤ : Subgroup G) from trivial)
  have h2 : ⁅v, u⁆ ∈ Gam (G := G) (k + 1) := by
    rw [← commutatorElement_inv u v]
    exact inv_mem h1
  rwa [commutatorElement_def] at h2

/-- The graded commutator is additive in the second variable, modulo `Gam (p+q+2)`. -/
theorem commutator_mul_right_mem (p q : ℕ) {a : G} (ha : a ∈ Gam (G := G) p) {b₁ b₂ : G}
    (h₁ : b₁ ∈ Gam (G := G) q) (h₂ : b₂ ∈ Gam (G := G) q) :
    ⁅a, b₁ * b₂⁆ * (⁅a, b₁⁆ * ⁅a, b₂⁆)⁻¹ ∈ Gam (G := G) (p + q + 2) := by
  have hu : ⁅a, b₂⁆ ∈ Gam (G := G) (p + q + 1) := commutator_mem_Gam ha h₂
  have hδ : b₁ * ⁅a, b₂⁆ * b₁⁻¹ * ⁅a, b₂⁆⁻¹ ∈ Gam (G := G) (p + q + 2) :=
    conj_diff_mem (p + q + 1) hu b₁
  have key : ⁅a, b₁ * b₂⁆ * (⁅a, b₁⁆ * ⁅a, b₂⁆)⁻¹
      = ⁅a, b₁⁆ * (b₁ * ⁅a, b₂⁆ * b₁⁻¹ * ⁅a, b₂⁆⁻¹) * ⁅a, b₁⁆⁻¹ := by
    rw [commutatorElement_mul_right_eq_mul_conj]; group
  rw [key]
  exact (Gam_normal (G := G) (p + q + 2)).conj_mem _ hδ ⁅a, b₁⁆

/-- The graded commutator is additive in the first variable, modulo `Gam (p+q+2)`. -/
theorem commutator_mul_left_mem (p q : ℕ) {a₁ a₂ : G} (h₁ : a₁ ∈ Gam (G := G) p)
    (h₂ : a₂ ∈ Gam (G := G) p) {b : G} (hb : b ∈ Gam (G := G) q) :
    ⁅a₁ * a₂, b⁆ * (⁅a₁, b⁆ * ⁅a₂, b⁆)⁻¹ ∈ Gam (G := G) (p + q + 2) := by
  have hv₂ : ⁅a₂, b⁆ ∈ Gam (G := G) (p + q + 1) := commutator_mem_Gam h₂ hb
  have hv₁ : ⁅a₁, b⁆ ∈ Gam (G := G) (p + q + 1) := commutator_mem_Gam h₁ hb
  have hδ : a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₂, b⁆⁻¹ ∈ Gam (G := G) (p + q + 2) :=
    conj_diff_mem (p + q + 1) hv₂ a₁
  have hε : ⁅⁅a₂, b⁆, ⁅a₁, b⁆⁆ ∈ Gam (G := G) (p + q + 2) := by
    have h := commutator_mem_Gam hv₂ hv₁
    exact Gam_antitone (by omega) h
  have key : ⁅a₁ * a₂, b⁆ * (⁅a₁, b⁆ * ⁅a₂, b⁆)⁻¹
      = (a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₂, b⁆⁻¹) * ⁅⁅a₂, b⁆, ⁅a₁, b⁆⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_def]; group
  rw [key]
  exact mul_mem hδ hε

/-- Antisymmetry of the graded commutator is exact. -/
theorem commutator_mul_antisymm (a b : G) : ⁅a, b⁆ * ⁅b, a⁆ = 1 := by
  rw [commutatorElement_def, commutatorElement_def]; group

/-- **Jacobi identity for the graded commutators.**  The Jacobi combination of `⁅a,b⁆`, `⁅b,c⁆` and
`⁅c,a⁆` lies in `Gam (p+q+r+3)`;  this is the sharp modulus needed for the Jacobi identity in
`Λ (p+q+r+2)`. -/
theorem commutator_jacobi_mem (p q r : ℕ) {a b c : G} (ha : a ∈ Gam (G := G) p)
    (hb : b ∈ Gam (G := G) q) (hc : c ∈ Gam (G := G) r) :
    ⁅⁅a, b⁆, c⁆ * ⁅⁅b, c⁆, a⁆ * ⁅⁅c, a⁆, b⁆ ∈ Gam (G := G) (p + q + r + 3) := by
  refine Gam_antitone (le_of_eq ?_) (gamma_commutator_jacobi_mem p q r a b c ha hb hc)
  rfl

/-! ## The graded pieces `Λ q = γ_q/γ_{q+1}` -/

/-- The `q`-th piece of the associated graded of the lower central series. -/
abbrev GLam (q : ℕ) : Type _ :=
  ↑(Gam (G := G) q) ⧸ (Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)

instance instGroupGLam (q : ℕ) : Group (GLam (G := G) q) := inferInstance

instance instCommGroupGLam (q : ℕ) : CommGroup (GLam (G := G) q) :=
  { (inferInstance : Group (GLam (G := G) q)) with
    mul_comm := by
      intro a b
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
        ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) a
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
        ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) b
      rw [← hx, ← hy]
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_inv]
      rw [div_eq_mul_inv]
      have h3 : (x : G) * (y : G) * ((y : G) * (x : G))⁻¹ = ⁅(x : G), (y : G)⁆ := by
        rw [commutatorElement_def]; group
      rw [h3]
      exact Gam_antitone (by omega) (commutator_mem_Gam x.property y.property) }

/-- The class in `Λ (p+q+1)` of the commutator of two representatives. -/
def commClass (p q : ℕ) (a : ↑(Gam (G := G) p)) (b : ↑(Gam (G := G) q)) :
    GLam (G := G) (p + q + 1) :=
  (⟨⁅(a : G), (b : G)⁆, commutator_mem_Gam (p := p) (q := q) a.property b.property⟩ :
    ↑(Gam (G := G) (p + q + 1)))

/-- The graded commutator as a homomorphism in the second variable, for a fixed representative
of the first variable. -/
noncomputable def bracketRightMon (p q : ℕ) (a : ↑(Gam (G := G) p)) :
    GLam (G := G) q →* GLam (G := G) (p + q + 1) :=
  QuotientGroup.lift _
    (MonoidHom.mk' (fun b : ↑(Gam (G := G) q) => commClass p q a b)
      (by
        intro b₁ b₂
        show commClass p q a (b₁ * b₂) = commClass p q a b₁ * commClass p q a b₂
        rw [commClass, commClass, commClass, ← QuotientGroup.mk_mul,
          QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_inv]
        rw [div_eq_mul_inv]
        exact commutator_mul_right_mem (p := p) (q := q) a.property b₁.property b₂.property))
    (by
      intro b hb
      show commClass p q a b = 1
      rw [commClass, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hb' : (b : G) ∈ Gam (G := G) (q + 1) := (Subgroup.mem_subgroupOf).1 hb
      have h := commutator_mem_Gam (p := p) (q := q + 1) a.property hb'
      rwa [show p + (q + 1) + 1 = p + q + 2 from by omega] at h)

@[simp] theorem bracketRightMon_mk' (p q : ℕ) (a : ↑(Gam (G := G) p))
    (b : ↑(Gam (G := G) q)) :
    bracketRightMon (G := G) p q a
        (QuotientGroup.mk' ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) b) =
      commClass p q a b := by
  rfl

/-- The graded commutator as a homomorphism in both variables. -/
noncomputable def bracketMon (p q : ℕ) :
    GLam (G := G) p →* (GLam (G := G) q →* GLam (G := G) (p + q + 1)) :=
  QuotientGroup.lift _
    (MonoidHom.mk' (fun a : ↑(Gam (G := G) p) => bracketRightMon p q a)
      (by
        intro a₁ a₂
        apply QuotientGroup.monoidHom_ext
        ext b
        simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, bracketRightMon_mk']
        show commClass p q (a₁ * a₂) b = commClass p q a₁ b * commClass p q a₂ b
        rw [commClass, commClass, commClass, ← QuotientGroup.mk_mul,
          QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_inv]
        rw [div_eq_mul_inv]
        exact commutator_mul_left_mem (p := p) (q := q) a₁.property a₂.property b.property))
    (by
      intro a ha
      apply QuotientGroup.monoidHom_ext
      ext b
      simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
      show commClass p q a b = 1
      rw [commClass, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have ha' : (a : G) ∈ Gam (G := G) (p + 1) := (Subgroup.mem_subgroupOf).1 ha
      have h := commutator_mem_Gam ha' b.property
      rwa [show (p + 1) + q + 1 = p + q + 2 from by omega] at h)

@[simp] theorem bracketMon_mk' (p q : ℕ) (a : ↑(Gam (G := G) p))
    (b : ↑(Gam (G := G) q)) :
    bracketMon (G := G) p q
        (QuotientGroup.mk' ((Gam (G := G) (p + 1)).subgroupOf (Gam (G := G) p)) a)
        (QuotientGroup.mk' ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) b) =
      commClass p q a b := by
  rfl

/-- The graded commutator as a biadditive map `Λ p →+ Λ q →+ Λ (p+q+1)`. -/
noncomputable def bracketL (p q : ℕ) :
    Additive (GLam (G := G) p) →+ (Additive (GLam (G := G) q) →+
      Additive (GLam (G := G) (p + q + 1))) where
  toFun x := MonoidHom.toAdditive (bracketMon p q (Additive.toMul x))
  map_zero' := by
    show MonoidHom.toAdditive (bracketMon p q (Additive.toMul 0)) = 0
    rw [show Additive.toMul (0 : Additive (GLam (G := G) p)) = 1 from rfl, map_one]
    exact AddMonoidHom.ext (fun z => rfl)
  map_add' := by
    intro x y
    show MonoidHom.toAdditive (bracketMon p q (Additive.toMul (x + y))) =
      MonoidHom.toAdditive (bracketMon p q (Additive.toMul x)) +
        MonoidHom.toAdditive (bracketMon p q (Additive.toMul y))
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
    exact AddMonoidHom.ext (fun z => rfl)

/-- The value of the graded bracket on classes of commutators. -/
theorem bracketL_apply_mk (p q : ℕ) (a : ↑(Gam (G := G) p)) (b : ↑(Gam (G := G) q)) :
    bracketL (G := G) p q
        (Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (p + 1)).subgroupOf
          (Gam (G := G) p)) a))
        (Additive.ofMul (QuotientGroup.mk' ((Gam (G := G) (q + 1)).subgroupOf
          (Gam (G := G) q)) b)) =
      Additive.ofMul (commClass p q a b) := by
  show bracketMon (G := G) p q
      (QuotientGroup.mk' ((Gam (G := G) (p + 1)).subgroupOf (Gam (G := G) p)) a)
      (QuotientGroup.mk' ((Gam (G := G) (q + 1)).subgroupOf (Gam (G := G) q)) b) =
    commClass p q a b
  rw [bracketMon_mk']

end graded
end Work.SSGRoute.prop5
