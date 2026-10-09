import Mathlib
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_bijective
import Submission.Work.CohomologicalShrinking.modsquare.squareQuotientToFun_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The first graded piece of the `p = 2` correction (degree 1)

This is the first (and lowest non-trivial) piece of the refined graded filtration
`F(n)^{(i,j)}/F(n)^{(i,j)+1}` that is needed to lift `2`-torsion.

For `τ = (1,1)` the graded piece is `F(n)^{(1,1)}/F(n)^{(2,1)} = F(n)/F(n)^2[F(n),F(n)]`,
i.e. `Work.CohomologicalShrinking.squareQuotient 2 G n`, on which `G` acts by permuting the images
of the free generators `x_{i,g}` (the regular representation).  An involution `δ ∈ G`, `δ ≠ 1`,
therefore acts on the basis in *free* orbits of size two, and the statement proved here is:

> every `δ`-fixed element of `squareQuotient 2 G n` is a `δ`-difference,
> i.e. `v = δ • w - w` for some `w`.

This is the "degree 1" instance of the family of statements
`(E_{σ})^δ ⊆ (1-δ)·Q_{σ+1}` used by the descent along the refined filtration (the degree-2
piece `F(n)^{(2,2)}/F(n)^{(3,1)}` is where the expression `A·(δA)` becomes a genuine *quadratic*
form in the letters of `A`).  The proof goes through the model
`squareQuotient 2 G n ≃ (Fin n × G → ZMod 2)`: pick a linear order (via `Fintype.equivFin`) and
set `w x = f x` on the smaller half of each two-element `δ`-orbit and `w x = 0` on the larger
half; then `(δ • w) x + w x = f x` because the orbit-partner contributes `0` (resp. `f`) and
`f` is constant on the orbit.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-- **First graded piece, degree 1.**  Every `δ`-fixed element of `F(n)/F(n)^2[F(n),F(n)]` is a
`δ`-difference. -/
theorem squareQuotient_fixed_is_delta_difference (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ v : squareQuotient 2 G n, δ • v = v →
      ∃ w : squareQuotient 2 G n, v = δ • w - w := by
  classical
  intro v hv
  set f : Fin n × G → ZMod 2 := squareQuotientToFun 2 G n v with hf
  have hpinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ
  have hf_fixed : ∀ x : Fin n × G, f (x.1, δ * x.2) = f x := by
    have h1 : δ • squareQuotientToFun 2 G n v = squareQuotientToFun 2 G n v := by
      rw [← modsquare.squareQuotientToFun_smul 2 G n δ v, hv]
    intro x
    have h2 := congrFun h1 x
    simpa [smul_prodFun_apply, hpinv] using h2
  set e : Fin n × G ≃ Fin (Fintype.card (Fin n × G)) := Fintype.equivFin _ with he
  set w : Fin n × G → ZMod 2 :=
    fun x => if e x ≤ e (x.1, δ * x.2) then f x else 0 with hw
  have hpair : ∀ x : Fin n × G, (x.1, δ * x.2) ≠ x := by
    intro x h
    have h2 : δ * x.2 = x.2 := congrArg Prod.snd h
    exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))
  have hdelta : ∀ x : Fin n × G, (x.1, δ * (δ * x.2)) = x := by
    intro x
    rw [← mul_assoc, hδ, one_mul]
  have hkey : ∀ x : Fin n × G, w (x.1, δ * x.2) + w x = f x := by
    intro x
    by_cases hc : e x ≤ e (x.1, δ * x.2)
    · have hcy : ¬ e (x.1, δ * x.2) ≤ e x := by
        intro hle
        exact hpair x (e.injective (le_antisymm hc hle).symm)
      have h3 : w x = f x := by simp only [hw]; exact if_pos hc
      have h4 : w (x.1, δ * x.2) = 0 := by
        simp only [hw, hdelta x]
        exact if_neg hcy
      rw [h3, h4, zero_add]
    · have hcy : e (x.1, δ * x.2) ≤ e x := le_of_lt (lt_of_not_ge hc)
      have h3 : w (x.1, δ * x.2) = f (x.1, δ * x.2) := by
        simp only [hw, hdelta x]
        exact if_pos hcy
      have h4 : w x = 0 := by simp only [hw]; exact if_neg hc
      rw [h3, h4, add_zero]
      exact hf_fixed x
  refine ⟨(modsquare.funToSquareQuotient 2 G n) w, ?_⟩
  have hW : squareQuotientToFun 2 G n
      (δ • (modsquare.funToSquareQuotient 2 G n) w - (modsquare.funToSquareQuotient 2 G n) w)
      = squareQuotientToFun 2 G n v := by
    rw [map_sub, modsquare.squareQuotientToFun_smul,
        modsquare.squareQuotientToFun_funToSquareQuotient]
    funext x
    rw [Pi.sub_apply, smul_prodFun_apply, hpinv, sub_eq_add_neg]
    have hneg : ∀ a : ZMod 2, -a = a := by decide
    rw [hneg]
    exact hkey x
  exact ((modsquare.squareQuotientToFun_bijective 2 G n).injective hW).symm

end Work.SSGRoute
