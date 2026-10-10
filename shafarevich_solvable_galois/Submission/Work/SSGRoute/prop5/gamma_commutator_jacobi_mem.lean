import Mathlib.GroupTheory.Nilpotent
import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Jacobi identity in the associated graded of the lower central series

Writing `γ_k = (⊤ : Subgroup G).lowerCentralSeries k` (Mathlib indexing, so `γ_0 = ⊤`,
`γ_1 = G'` and `⁅γ_p, γ_q⁆ ≤ γ_{p+q+1}`, proved in `commutator_lowerCentralSeries_le`), we show
that for `a ∈ γ_p`, `b ∈ γ_q`, `c ∈ γ_r` the Jacobi combination

`⁅⁅a,b⁆,c⁆ * ⁅⁅b,c⁆,a⁆ * ⁅⁅c,a⁆,b⁆`

lies in `γ_{p+q+r+3}` — one level deeper than the naive bound `γ_{p+q+r+2}` coming only from
`⁅γ_m,γ_n⁆ ≤ γ_{m+n+1}`.

The proof uses the Hall–Witt identity together with the fact that the conjugation appearing in it
differs from the plain commutator only by an element of `γ_{p+q+r+3}`.  The relevant *pure group
identity* is `⁅x,z⁆ * ⁅x, y*z⁆⁻¹ = ⁅⁅x,z⁆,y⁆ * ⁅x,y⁆⁻¹`.
-/

open scoped commutatorElement

namespace Work.SSGRoute.prop5

/-- If `x ∈ γ_i` and `y ∈ γ_j` then `⁅x, y⁆ ∈ γ_{i+j+1}`. -/
theorem commutatorElement_mem_lowerCentralSeries {G : Type*} [Group G] (i j : ℕ)
    {x y : G} (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries i)
    (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries j) :
    ⁅x, y⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) :=
  commutator_lowerCentralSeries_le G i j (Subgroup.commutator_mem_commutator hx hy)

/-- Weakened form:  if `x ∈ γ_i`, `y ∈ γ_j` and `t ≤ i + j + 1` then `⁅x, y⁆ ∈ γ_t`. -/
theorem commutatorElement_mem_lowerCentralSeries_of_le {G : Type*} [Group G] (i j t : ℕ)
    {x y : G} (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries i)
    (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries j) (h : t ≤ i + j + 1) :
    ⁅x, y⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries t :=
  Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) h
    (commutator_lowerCentralSeries_le G i j (Subgroup.commutator_mem_commutator hx hy))

/-- The pure group identity behind the correction in the Jacobi congruence:
`⁅x,z⁆ * ⁅x, y*z⁆⁻¹ = ⁅⁅x,z⁆, y⁆ * ⁅x,y⁆⁻¹`. -/
theorem jacobi_correction_identity {G : Type*} [Group G] (x y z : G) :
    ⁅x, z⁆ * ⁅x, y * z⁆⁻¹ = ⁅⁅x, z⁆, y⁆ * ⁅x, y⁆⁻¹ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  group

/-- **Correction step.**  If `⁅x,y⁆ ∈ N` and `⁅⁅x,z⁆,y⁆ ∈ N` for a normal subgroup `N`, then the
plain commutator `⁅x,z⁆` agrees with `⁅x, y*z⁆` modulo `N`. -/
theorem jacobi_correction_step_mem {G : Type*} [Group G] (x y z : G) (N : Subgroup G)
    (hxy : ⁅x, y⁆ ∈ N) (hxyz : ⁅⁅x, z⁆, y⁆ ∈ N) :
    ⁅x, z⁆ * ⁅x, y * z⁆⁻¹ ∈ N := by
  rw [jacobi_correction_identity]
  exact N.mul_mem hxyz (N.inv_mem hxy)

/-- **Assembly.**  If `N` is normal, `a₁, a₂, a₃ ∈ N` and `W₁ * W₂ * W₃ = 1`, then
`(a₁ * W₁) * (a₂ * W₂) * (a₃ * W₃) ∈ N`. -/
theorem jacobi_assembly_three_mem {G : Type*} [Group G] (N : Subgroup G) (hN : N.Normal)
    (a₁ a₂ a₃ W₁ W₂ W₃ : G) (ha₁ : a₁ ∈ N) (ha₂ : a₂ ∈ N) (ha₃ : a₃ ∈ N)
    (hW : W₁ * W₂ * W₃ = 1) :
    (a₁ * W₁) * (a₂ * W₂) * (a₃ * W₃) ∈ N := by
  have key : (a₁ * W₁) * (a₂ * W₂) * (a₃ * W₃)
      = a₁ * (W₁ * a₂ * W₁⁻¹) * ((W₁ * W₂) * a₃ * (W₁ * W₂)⁻¹) * (W₁ * W₂ * W₃) := by
    group
  have h1 : W₁ * a₂ * W₁⁻¹ ∈ N := hN.conj_mem a₂ ha₂ W₁
  have h2 : (W₁ * W₂) * a₃ * (W₁ * W₂)⁻¹ ∈ N := hN.conj_mem a₃ ha₃ (W₁ * W₂)
  have h12 : a₁ * (W₁ * a₂ * W₁⁻¹) ∈ N := N.mul_mem ha₁ h1
  have h123 : a₁ * (W₁ * a₂ * W₁⁻¹) * ((W₁ * W₂) * a₃ * (W₁ * W₂)⁻¹) ∈ N :=
    N.mul_mem h12 h2
  rw [key, hW, mul_one]
  exact h123

theorem gamma_commutator_jacobi_mem {G : Type*} [Group G] (p q r : ℕ) (a b c : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries p)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries q)
    (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries r) :
    (((a * b * a⁻¹ * b⁻¹) * c * (a * b * a⁻¹ * b⁻¹)⁻¹ * c⁻¹) *
      ((b * c * b⁻¹ * c⁻¹) * a * (b * c * b⁻¹ * c⁻¹)⁻¹ * a⁻¹) *
      ((c * a * c⁻¹ * a⁻¹) * b * (c * a * c⁻¹ * a⁻¹)⁻¹ * b⁻¹))
      ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) := by
  show ⁅⁅a,b⁆, c⁆ * ⁅⁅b,c⁆, a⁆ * ⁅⁅c,a⁆, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3)
  have hN : ((⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3)).Normal := inferInstance
  -- basic membership of the three inner commutators
  have hu : ⁅a,b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + 1) :=
    commutatorElement_mem_lowerCentralSeries p q ha hb
  have hv : ⁅b,c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (q + r + 1) :=
    commutatorElement_mem_lowerCentralSeries q r hb hc
  have hw : ⁅c,a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (r + p + 1) :=
    commutatorElement_mem_lowerCentralSeries r p hc ha
  -- the "naive" terms sit in γ_{p+q+r+2}
  have hBc : ⁅⁅a,b⁆, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 2) :=
    commutatorElement_mem_lowerCentralSeries_of_le (p + q + 1) r (p + q + r + 2) hu hc (by omega)
  have hVa : ⁅⁅b,c⁆, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 2) :=
    commutatorElement_mem_lowerCentralSeries_of_le (q + r + 1) p (p + q + r + 2) hv ha (by omega)
  have hWb : ⁅⁅c,a⁆, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 2) :=
    commutatorElement_mem_lowerCentralSeries_of_le (r + p + 1) q (p + q + r + 2) hw hb (by omega)
  -- pairwise commutators of the inner commutators
  have huv : ⁅⁅a,b⁆, ⁅b,c⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (p + q + 1) (q + r + 1) (p + q + r + 3)
      hu hv (by omega)
  have hvw : ⁅⁅b,c⁆, ⁅c,a⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (q + r + 1) (r + p + 1) (p + q + r + 3)
      hv hw (by omega)
  have hwu : ⁅⁅c,a⁆, ⁅a,b⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (r + p + 1) (p + q + 1) (p + q + r + 3)
      hw hu (by omega)
  have hBcv : ⁅⁅⁅a,b⁆, c⁆, ⁅b,c⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (p + q + r + 2) (q + r + 1) (p + q + r + 3)
      hBc hv (by omega)
  have hVaw : ⁅⁅⁅b,c⁆, a⁆, ⁅c,a⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (p + q + r + 2) (r + p + 1) (p + q + r + 3)
      hVa hw (by omega)
  have hWbu : ⁅⁅⁅c,a⁆, b⁆, ⁅a,b⁆⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    commutatorElement_mem_lowerCentralSeries_of_le (p + q + r + 2) (p + q + 1) (p + q + r + 3)
      hWb hu (by omega)
  -- the three correction elements lie in γ_{p+q+r+3}
  have hD1 : ⁅⁅a,b⁆, c⁆ * ⁅⁅a,b⁆, ⁅b,c⁆ * c⁆⁻¹
      ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    jacobi_correction_step_mem ⁅a,b⁆ ⁅b,c⁆ c _ huv hBcv
  have hD2 : ⁅⁅b,c⁆, a⁆ * ⁅⁅b,c⁆, ⁅c,a⁆ * a⁆⁻¹
      ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    jacobi_correction_step_mem ⁅b,c⁆ ⁅c,a⁆ a _ hvw hVaw
  have hD3 : ⁅⁅c,a⁆, b⁆ * ⁅⁅c,a⁆, ⁅a,b⁆ * b⁆⁻¹
      ∈ (⊤ : Subgroup G).lowerCentralSeries (p + q + r + 3) :=
    jacobi_correction_step_mem ⁅c,a⁆ ⁅a,b⁆ b _ hwu hWbu
  -- Hall–Witt identity, rewritten with `b*c*b⁻¹ = ⁅b,c⁆ * c` etc.
  have e1 : b * c * b⁻¹ = ⁅b,c⁆ * c := by rw [commutatorElement_def]; group
  have e2 : c * a * c⁻¹ = ⁅c,a⁆ * a := by rw [commutatorElement_def]; group
  have e3 : a * b * a⁻¹ = ⁅a,b⁆ * b := by rw [commutatorElement_def]; group
  have hHW : ⁅⁅a,b⁆, ⁅b,c⁆ * c⁆ * ⁅⁅b,c⁆, ⁅c,a⁆ * a⁆ * ⁅⁅c,a⁆, ⁅a,b⁆ * b⁆ = 1 := by
    have h := commutatorElement_commutatorElement_conj_mul a b c
    rw [e1, e2, e3] at h
    exact h
  -- `⁅x,z⁆ = (⁅x,z⁆ * ⁅x,y*z⁆⁻¹) * ⁅x, y*z⁆`
  have hterm1 : ⁅⁅a,b⁆, c⁆
      = (⁅⁅a,b⁆, c⁆ * ⁅⁅a,b⁆, ⁅b,c⁆ * c⁆⁻¹) * ⁅⁅a,b⁆, ⁅b,c⁆ * c⁆ := by group
  have hterm2 : ⁅⁅b,c⁆, a⁆
      = (⁅⁅b,c⁆, a⁆ * ⁅⁅b,c⁆, ⁅c,a⁆ * a⁆⁻¹) * ⁅⁅b,c⁆, ⁅c,a⁆ * a⁆ := by group
  have hterm3 : ⁅⁅c,a⁆, b⁆
      = (⁅⁅c,a⁆, b⁆ * ⁅⁅c,a⁆, ⁅a,b⁆ * b⁆⁻¹) * ⁅⁅c,a⁆, ⁅a,b⁆ * b⁆ := by group
  rw [hterm1, hterm2, hterm3]
  exact jacobi_assembly_three_mem _ hN _ _ _ _ _ _ hD1 hD2 hD3 hHW

end Work.SSGRoute.prop5
