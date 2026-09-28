import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polar_basic

namespace Work.HP.Q44Main.QuadCount

/-- The polar form `polQ Q v ·` is linear in its second argument. -/
lemma polQ_right_linear (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (v : Fin 5 → ℚ) :
    (∀ y z : Fin 5 → ℚ,
        Work.HP.MDEstimates.polQ Q v (y + z)
          = Work.HP.MDEstimates.polQ Q v y + Work.HP.MDEstimates.polQ Q v z) ∧
      (∀ (c : ℚ) (y : Fin 5 → ℚ),
        Work.HP.MDEstimates.polQ Q v (c • y)
          = c * Work.HP.MDEstimates.polQ Q v y) := by
  obtain ⟨hadd, hsmul, hsymm, -, -, -⟩ := Work.HP.MDEstimates.polar_basic Q hQ
  refine ⟨?_, ?_⟩
  · intro y z
    rw [hsymm v (y + z), hadd y z v, hsymm y v, hsymm z v]
  · intro c y
    rw [hsymm v (c • y), hsmul c y v, hsymm y v]

/-- `w` is the sum of its coordinates against the standard basis `Pi.single · 1`. -/
lemma self_eq_sum_single (w : Fin 5 → ℚ) :
    w = ∑ i : Fin 5, w i • Pi.single i 1 := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem polQExpand (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (v w : Fin 5 → ℚ) :
    Work.HP.MDEstimates.polQ Q v w
      = ∑ i : Fin 5, w i * Work.HP.MDEstimates.polQ Q v (Pi.single i 1) := by
  obtain ⟨hadd, hsmul, hsymm, -, -, -⟩ := Work.HP.MDEstimates.polar_basic Q hQ
  -- The second argument of the polar form is linear.
  let F : (Fin 5 → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun w => Work.HP.MDEstimates.polQ Q v w
      map_add' := fun a b => by
        rw [hsymm v (a + b), hadd a b v, hsymm a v, hsymm b v]
      map_smul' := fun c a => by
        rw [hsymm v (c • a), hsmul c a v, hsymm a v, RingHom.id_apply, smul_eq_mul] }
  calc Work.HP.MDEstimates.polQ Q v w = F w := rfl
    _ = F (∑ i : Fin 5, w i • Pi.single i 1) := by
        conv_lhs => rw [self_eq_sum_single w]
    _ = ∑ i : Fin 5, F (w i • Pi.single i 1) := by rw [map_sum]
    _ = ∑ i : Fin 5, w i * F (Pi.single i 1) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_eq_mul]
    _ = ∑ i : Fin 5, w i * Work.HP.MDEstimates.polQ Q v (Pi.single i 1) := rfl

end Work.HP.Q44Main.QuadCount
