import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs

namespace Work.HP.Sig2

/-! ## The projection part of `perpCompB`

`perpCompB b w` is by definition `w - projB b w`, where `projB b w` is the "projection"
`∑ᵢ (∑ⱼ (gramOf b)⁻¹ᵢⱼ * ⟪w, bⱼ⟫) • bᵢ`.  The dependence on `w` enters only through the scalar
products `⟪w, bⱼ⟫ = dotR w (bⱼ)`, so `projB b` is manifestly linear; extracting it as a separate
definition lets us prove its linearity once and read off the linearity of `perpCompB`. -/

/-- The projection of `w` onto `span_ℝ(Λ)` (the subtracted term in `perpCompB`). -/
private noncomputable def projB {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) : ι → ℝ :=
  ∑ i : κ, (∑ j : κ, (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
    • intCastPi (((b i : Λ) : ι → ℤ))

private lemma dotR_smul_left {ι : Type*} [Fintype ι] (a : ℝ) (u x : ι → ℝ) :
    dotR (a • u) x = a * dotR u x := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private lemma dotR_add_left {ι : Type*} [Fintype ι] (u u' x : ι → ℝ) :
    dotR (u + u') x = dotR u x + dotR u' x := by
  simp only [dotR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma projB_smul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) (a : ℝ) (u : ι → ℝ) :
    projB b (a • u) = a • projB b u := by
  unfold projB
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : (∑ j : κ, (gramOf b)⁻¹ i j * dotR (a • u) (intCastPi (((b j : Λ) : ι → ℤ))))
      = a * ∑ j : κ, (gramOf b)⁻¹ i j * dotR u (intCastPi (((b j : Λ) : ι → ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [dotR_smul_left]
    ring
  rw [hinner, mul_smul]

private lemma projB_add {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) (u u' : ι → ℝ) :
    projB b (u + u') = projB b u + projB b u' := by
  unfold projB
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : (∑ j : κ, (gramOf b)⁻¹ i j * dotR (u + u') (intCastPi (((b j : Λ) : ι → ℤ))))
      = (∑ j : κ, (gramOf b)⁻¹ i j * dotR u (intCastPi (((b j : Λ) : ι → ℤ))))
        + (∑ j : κ, (gramOf b)⁻¹ i j * dotR u' (intCastPi (((b j : Λ) : ι → ℤ)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [dotR_add_left, mul_add]
  rw [hinner, add_smul]

private lemma perpCompB_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) :
    perpCompB b w = w - projB b w := rfl

/-- `perpCompB b` is additive and homogeneous (it is `w ↦ w - proj w` with `proj` a linear map). -/
theorem perpCompB_linear {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    (∀ (a : ℝ) (u : ι → ℝ), perpCompB b (a • u) = a • perpCompB b u) ∧
    (∀ u u' : ι → ℝ, perpCompB b (u + u') = perpCompB b u + perpCompB b u') ∧
    (∀ u u' : ι → ℝ, perpCompB b (u - u') = perpCompB b u - perpCompB b u') := by
  have hsmul : ∀ (a : ℝ) (u : ι → ℝ), perpCompB b (a • u) = a • perpCompB b u := by
    intro a u
    rw [perpCompB_eq b (a • u), perpCompB_eq b u, projB_smul b a u, smul_sub]
  have hadd : ∀ u u' : ι → ℝ, perpCompB b (u + u') = perpCompB b u + perpCompB b u' := by
    intro u u'
    rw [perpCompB_eq b (u + u'), perpCompB_eq b u, perpCompB_eq b u', projB_add b u u']
    abel
  refine ⟨hsmul, hadd, ?_⟩
  intro u u'
  have hsub : u - u' = u + (-1 : ℝ) • u' := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [hsub, hadd, hsmul, neg_one_smul, sub_eq_add_neg]

end Work.HP.Sig2
