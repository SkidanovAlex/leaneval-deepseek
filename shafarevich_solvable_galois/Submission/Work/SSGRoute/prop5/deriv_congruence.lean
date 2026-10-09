import Mathlib
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.gamma_commutator_jacobi_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement

/-!
# The derivation identity in the associated graded of the lower central series

For `a ∈ γ_p`, `b ∈ γ_q`, `c ∈ γ_r` the right-nested commutator `⁅a,⁅b,c⁆⁆` agrees with
`⁅⁅a,b⁆,c⁆ * ⁅b,⁅a,c⁆⁆` modulo `γ_{p+q+r+3}`.  This is the "Leibniz rule" for `ad a` on the
associated graded Lie ring `⨁ γ_k/γ_{k+1}`; it is an immediate consequence of the graded Jacobi
identity (`graded.commutator_jacobi_mem`) together with the two elementary congruences

* `⁅x⁻¹, y⁆ ≡ ⁅x, y⁆⁻¹` modulo `γ_{m+n+2}` for `x ∈ γ_m`, `y ∈ γ_n`
  (`commutator_inv_left_congruence`), and
* the abelian-ness of the graded piece, used in `deriv_congruence_assembly`.
-/

/-- **The assembly step of the derivation congruence.**  Let `N` be a normal subgroup and let
`A, B, C ∈ G` with `B * A⁻¹ * Cc`, `Cc * C⁻¹` and `⁅A, C⁻¹⁆` all in `N`.  Then
`A * (B * C)⁻¹ ∈ N`.  This is the purely group-theoretic content of the derivation identity:
the Jacobi combination supplies `B * A⁻¹ * Cc ∈ N`, the inversion congruence supplies
`Cc * C⁻¹ ∈ N`, and `⁅A, C⁻¹⁆ ∈ N` is the (deeper) error produced by reordering elements of the
graded piece, which is abelian. -/
theorem deriv_congruence_assembly {G : Type*} [Group G] (N : Subgroup G) (hN : N.Normal)
    (A B C Cc : G) (h1 : B * A⁻¹ * Cc ∈ N) (h2 : Cc * C⁻¹ ∈ N)
    (h3 : ⁅A, C⁻¹⁆ ∈ N) : A * (B * C)⁻¹ ∈ N := by
  -- `Cc⁻¹ * C ∈ N`, obtained from `Cc * C⁻¹ ∈ N` by conjugating with `Cc⁻¹`.
  have h2' : Cc⁻¹ * C ∈ N := by
    have hkey : Cc⁻¹ * C = Cc⁻¹ * (Cc * C⁻¹)⁻¹ * Cc⁻¹⁻¹ := by group
    rw [hkey]
    exact hN.conj_mem _ (inv_mem h2) Cc⁻¹
  -- `B * A⁻¹ * C ∈ N`, from `B * A⁻¹ * Cc ∈ N` and `Cc⁻¹ * C ∈ N`.
  have hBAC : B * A⁻¹ * C ∈ N := by
    have hkey : B * A⁻¹ * C = B * A⁻¹ * Cc * (Cc⁻¹ * C) := by group
    rw [hkey]
    exact N.mul_mem h1 h2'
  -- Rewrite the goal so that it is a product of the known pieces.
  have hgoal : A * (B * C)⁻¹ = ⁅A, C⁻¹⁆ * (B * A⁻¹ * C)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hgoal]
  exact N.mul_mem h3 (inv_mem hBAC)

/-- **Inversion congruence for the graded commutator.**  If `x ∈ γ_m` and `y ∈ γ_n` then
`⁅x⁻¹, y⁆ ≡ ⁅x, y⁆⁻¹` modulo `γ_{m+n+2}`;  equivalently `⁅x⁻¹, y⁆ * ⁅x, y⁆ ∈ γ_{m+n+2}`.
This is the associativity/bilinearity of the graded commutator applied to `x * x⁻¹ = 1`. -/
theorem commutator_inv_left_congruence {G : Type*} [Group G] (m n : ℕ) {x y : G}
    (hx : x ∈ graded.Gam (G := G) m) (hy : y ∈ graded.Gam (G := G) n) :
    ⁅x⁻¹, y⁆ * ⁅x, y⁆ ∈ graded.Gam (G := G) (m + n + 2) := by
  have h := graded.commutator_mul_left_mem (G := G) (p := m) (q := n) hx (inv_mem hx) hy
  simp only [mul_inv_cancel, commutatorElement_one_left, one_mul] at h
  have h2 : ⁅x, y⁆ * ⁅x⁻¹, y⁆ ∈ graded.Gam (G := G) (m + n + 2) := by
    simpa using inv_mem h
  have hkey : ⁅x⁻¹, y⁆ * ⁅x, y⁆
      = ⁅x, y⁆⁻¹ * (⁅x, y⁆ * ⁅x⁻¹, y⁆) * ⁅x, y⁆⁻¹⁻¹ := by group
  rw [hkey]
  exact (graded.Gam_normal (G := G) (m + n + 2)).conj_mem _ h2 ⁅x, y⁆⁻¹

/-- **The derivation identity in the associated graded of the lower central series.**
For `a ∈ γ_p`, `b ∈ γ_q`, `c ∈ γ_r` the right-nested commutator `⁅a,⁅b,c⁆⁆` agrees with
`⁅⁅a,b⁆,c⁆ * ⁅b,⁅a,c⁆⁆` modulo `γ_{p+q+r+3}`.  This is the sharp modulus: all three elements lie
in `γ_{p+q+r+2}`, and the identity is exactly what makes `ad x` a derivation on the associated
graded Lie ring. -/
theorem deriv_congruence (p q r : ℕ) {G : Type*} [Group G] {a b c : G}
    (ha : a ∈ Work.SSGRoute.prop5.graded.Gam (G := G) p)
    (hb : b ∈ Work.SSGRoute.prop5.graded.Gam (G := G) q)
    (hc : c ∈ Work.SSGRoute.prop5.graded.Gam (G := G) r) :
    ⁅a, ⁅b, c⁆⁆ * (⁅⁅a, b⁆, c⁆ * ⁅b, ⁅a, c⁆⁆)⁻¹ ∈
      Work.SSGRoute.prop5.graded.Gam (G := G) (p + q + r + 3) := by
  -- Membership of the two inner commutators.
  have hv : ⁅b, c⁆ ∈ graded.Gam (G := G) (q + r + 1) := graded.commutator_mem_Gam hb hc
  have hx : ⁅a, c⁆ ∈ graded.Gam (G := G) (p + r + 1) := graded.commutator_mem_Gam ha hc
  -- The graded Jacobi identity.
  have hJac := graded.commutator_jacobi_mem (G := G) p q r ha hb hc
  refine deriv_congruence_assembly (graded.Gam (G := G) (p + q + r + 3)) (graded.Gam_normal _)
    ⁅a, ⁅b, c⁆⁆ ⁅⁅a, b⁆, c⁆ ⁅b, ⁅a, c⁆⁆ ⁅⁅a, c⁆⁻¹, b⁆ ?_ ?_ ?_
  · -- `⁅⁅a,b⁆,c⁆ * ⁅a,⁅b,c⁆⁆⁻¹ * ⁅⁅a,c⁆⁻¹,b⁆ ∈ γ`, this is the Jacobi identity resubstituted.
    have e1 : ⁅⁅b, c⁆, a⁆ = ⁅a, ⁅b, c⁆⁆⁻¹ := by
      have h := commutatorElement_inv ⁅b, c⁆ a
      rw [← h, inv_inv]
    have e2a : ⁅c, a⁆ = ⁅a, c⁆⁻¹ := by
      have h := commutatorElement_inv c a
      rw [← h, inv_inv]
    have e2 : ⁅⁅c, a⁆, b⁆ = ⁅⁅a, c⁆⁻¹, b⁆ := by rw [e2a]
    rw [← e1, ← e2]
    exact hJac
  · -- `⁅⁅a,c⁆⁻¹,b⁆ * (⁅b,⁅a,c⁆⁆)⁻¹ ∈ γ`, the inversion congruence.
    have h := commutator_inv_left_congruence (G := G) (p + r + 1) q hx hb
    have e : ⁅⁅a, c⁆, b⁆ = (⁅b, ⁅a, c⁆⁆)⁻¹ := by
      have hh := commutatorElement_inv b ⁅a, c⁆
      rw [← hh]
    rw [e] at h
    exact graded.Gam_antitone (by omega) h
  · -- `⁅⁅a,⁅b,c⁆⁆, (⁅b,⁅a,c⁆⁆)⁻¹⁆ ∈ γ`, both arguments lie in `γ_{p+q+r+2}`.
    have hA : ⁅a, ⁅b, c⁆⁆ ∈ graded.Gam (G := G) (p + q + r + 2) :=
      commutatorElement_mem_lowerCentralSeries_of_le p (q + r + 1) (p + q + r + 2) ha hv (by omega)
    have hC : (⁅b, ⁅a, c⁆⁆)⁻¹ ∈ graded.Gam (G := G) (p + q + r + 2) := by
      have hC' : ⁅b, ⁅a, c⁆⁆ ∈ graded.Gam (G := G) (p + q + r + 2) :=
        commutatorElement_mem_lowerCentralSeries_of_le q (p + r + 1) (p + q + r + 2) hb hx
          (by omega)
      exact inv_mem hC'
    exact graded.Gam_antitone (by omega) (graded.commutator_mem_Gam hA hC)

end Work.SSGRoute.prop5
