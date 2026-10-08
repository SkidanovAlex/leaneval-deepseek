import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.ThmF.ChV12.torus_aux
import Submission.Work.ThmF.ChV12.norm_form_card
import Submission.Work.ThmF.ChV12.sl2_centralizer_card
import Submission.Work.ThmF.ChV12.sl2_centralizer_isCyclic
import Submission.Work.ThmF.ChV12.sl2_involution_inverts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000

namespace Work.ThmF.ChV12

/-- Conjugation by a group isomorphism carries the centralizer of a point to the centralizer of
its image. -/
theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (c : G) :
    (Subgroup.centralizer ({c} : Set G)).map φ.toMonoidHom
      = Subgroup.centralizer ({φ c} : Set H) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    change φ.toMonoidHom x * φ.toMonoidHom c = φ.toMonoidHom c * φ.toMonoidHom x
    rw [← map_mul, hx, map_mul]
  · intro hy
    refine ⟨φ.symm y, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      have := congrArg (φ.symm : H → G) hy
      simpa using this
    · show φ (φ.symm y) = y
      exact MulEquiv.apply_symm_apply φ y

open LeanEval.GroupTheory.Defs in theorem psl2_centralizer_torus (n : ℕ) (hn : 2 ≤ n) (a b : PSL2Model n) (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : orderOf (a * b) = 3) (h3 : 3 ∣ 2 ^ n + 1) : IsCyclic ↥(Subgroup.centralizer ({a * b} : Set (PSL2Model n))) ∧ Nat.card ↥(Subgroup.centralizer ({a * b} : Set (PSL2Model n))) = 2 ^ n + 1 ∧ ∀ x ∈ Subgroup.centralizer ({a * b} : Set (PSL2Model n)), a * x * a⁻¹ = x⁻¹ := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  obtain ⟨φ⟩ := Work.Models.PSL2.pslEquiv n
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card (p := 2) (n := n) (by omega)
  set a' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := φ.symm a with ha'
  set b' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := φ.symm b with hb'
  set c' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := a' * b' with hc'
  have hφa : φ a' = a := by rw [ha', MulEquiv.apply_symm_apply]
  have hφb : φ b' = b := by rw [hb', MulEquiv.apply_symm_apply]
  have hφc : φ c' = a * b := by rw [hc', map_mul, hφa, hφb]
  have hha : orderOf a' = 2 := by
    have h := φ.orderOf_eq a'; rw [hφa, ha] at h; exact h.symm
  have hhb : orderOf b' = 2 := by
    have h := φ.orderOf_eq b'; rw [hφb, hb] at h; exact h.symm
  have hhc : orderOf c' = 3 := by
    have h := φ.orderOf_eq c'; rw [hφc, hab] at h; exact h.symm
  have ha2 : a' * a' = 1 := by
    have := pow_orderOf_eq_one a'; rw [hha] at this; simpa [pow_two] using this
  have hb2 : b' * b' = 1 := by
    have := pow_orderOf_eq_one b'; rw [hhb] at this; simpa [pow_two] using this
  have hac' : a' * c' * a'⁻¹ = c'⁻¹ := by
    rw [hc', mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
    rw [← mul_assoc, ha2, one_mul]
  haveI : IsCyclic ↥(Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
    (GaloisField 2 n)))) := sl2_centralizer_isCyclic n hF h3 c' hhc
  have card' := sl2_centralizer_card n hF h3 c' hhc
  have hmap : (Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n)))).map φ.toMonoidHom
      = Subgroup.centralizer ({a * b} : Set (PSL2Model n)) := by
    rw [map_centralizer_singleton φ c', hφc]
  have hcard : Nat.card ↥(Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n))))
      = Nat.card ↥(Subgroup.centralizer ({a * b} : Set (PSL2Model n))) := by
    rw [← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
      φ.toMonoidHom φ.injective).toEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap]
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective
        (Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
          (GaloisField 2 n)))) φ.toMonoidHom φ.injective).toMonoidHom
      (Subgroup.equivMapOfInjective
        (Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
          (GaloisField 2 n)))) φ.toMonoidHom φ.injective).surjective
  · rw [← hcard]; exact card'
  · intro x hx
    have hx' : φ.symm x ∈ Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n))) := by
      have h1 : x ∈ (Subgroup.centralizer ({c'} : Set (Matrix.SpecialLinearGroup (Fin 2)
          (GaloisField 2 n)))).map φ.toMonoidHom := by
        rw [hmap]; exact hx
      rw [Subgroup.mem_map] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hsym : φ.symm x = y := by
        rw [← hyx]
        exact MulEquiv.symm_apply_apply φ y
      rw [hsym]; exact hy
    have h2 := sl2_involution_inverts n hF h3 a' c' hhc hac' (φ.symm x) hx'
    have h3eq := congrArg (φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) →
      PSL2Model n) h2
    rw [ha'] at h3eq
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h3eq

end Work.ThmF.ChV12
