import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ModuleDim
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.RankAPI.rk_add_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

section Helpers

/-- `Fin.append` concatenates the ranges of the two families. -/
theorem range_finAppend {α : Type*} {k l : ℕ}
    (v : Fin k → α) (w : Fin l → α) :
    Set.range (Fin.append v w) = Set.range v ∪ Set.range w := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i' => exact Or.inl ⟨i', (Fin.append_left v w i').symm⟩
    | right j' => exact Or.inr ⟨j', (Fin.append_right v w j').symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd l i, Fin.append_left v w i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right v w j⟩

/-- The span of the range of `Fin.append v w` is the supremum of the spans of the two parts. -/
theorem span_range_finAppend {R : Type u} [Ring R] {n k l : ℕ}
    (v : Fin k → (Fin n → R)) (w : Fin l → (Fin n → R)) :
    Submodule.span R (Set.range (Fin.append v w)) =
      Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range w) := by
  rw [range_finAppend, Submodule.span_union]

/-- `Matrix.toLinearMapRight'.symm` is an anti-homomorphism from endomorphisms of `R^n`
to matrices. -/
theorem toLin_symm_mul {R : Type u} [Ring R] {n : ℕ} (f g : Module.End R (Fin n → R)) :
    Matrix.toLinearMapRight'.symm (f * g)
      = Matrix.toLinearMapRight'.symm g * Matrix.toLinearMapRight'.symm f := by
  apply Matrix.toLinearMapRight'.injective
  rw [LinearEquiv.apply_symm_apply, Matrix.toLinearMapRight'_mul,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (Module.End.mul_eq_comp f g).symm

/-- `Matrix.toLinearMapRight'.symm` is additive. -/
theorem toLin_symm_add {R : Type u} [Ring R] {n : ℕ} (f g : Module.End R (Fin n → R)) :
    Matrix.toLinearMapRight'.symm (f + g)
      = Matrix.toLinearMapRight'.symm f + Matrix.toLinearMapRight'.symm g :=
  (Matrix.toLinearMapRight'.symm).map_add f g

/-- `Matrix.toLinearMapRight'.symm` sends `1` to `1`. -/
theorem toLin_symm_one {R : Type u} [Ring R] {n : ℕ} :
    Matrix.toLinearMapRight'.symm (1 : Module.End R (Fin n → R)) = 1 := by
  apply Matrix.toLinearMapRight'.injective
  rw [LinearEquiv.apply_symm_apply, Matrix.toLinearMapRight'_one]
  rfl

/-- `Matrix.toLinearMapRight'.symm` is subtractive. -/
theorem toLin_symm_sub {R : Type u} [Ring R] {n : ℕ} (f g : Module.End R (Fin n → R)) :
    Matrix.toLinearMapRight'.symm (f - g)
      = Matrix.toLinearMapRight'.symm f - Matrix.toLinearMapRight'.symm g :=
  (Matrix.toLinearMapRight'.symm).map_sub f g

end Helpers

/-- **Subadditivity of `dimOf`.** The dimension of `span (range (Fin.append v w))` is at most
the sum of the dimensions of `span (range v)` and `span (range w)`.

This is the exactness of the dimension function attached to a Sylvester rank function over a
von Neumann regular ring.  Concretely, if `e₁`, `e₂` are idempotent projections onto `V` and
`W` with ranges `V`, `W` and `q` is an idempotent projection onto `V ⊔ W`, then
`h₁ := (1 - e₁) q` and `h₀ := (1 - e₁) e₂ z` (with `z` a weak inverse of `(1 - e₁) e₂`) are
idempotents with the *same* range `(1 - e₁) W`, so they have the same matrix rank by
`rank_idem_eq_of_range_eq`; that rank is at most `rk e₂`, because `φ⁻¹ h₀` factors through
`φ⁻¹ e₂`.  Finally `e₁ + h₁` is an idempotent with range `V ⊔ W`, hence has the rank of `q`. -/
theorem dimOf_append_le {R : Type u} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    {n k l : ℕ} (v : Fin k → (Fin n → R)) (w : Fin l → (Fin n → R)) :
    dimOf rk (Fin.append v w) ≤ dimOf rk v + dimOf rk w := by
  classical
  set V : Submodule R (Fin n → R) := Submodule.span R (Set.range v) with hV
  set W : Submodule R (Fin n → R) := Submodule.span R (Set.range w) with hW
  obtain ⟨e₁, he₁, hr₁⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v
  obtain ⟨e₂, he₂, hr₂⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux w
  obtain ⟨q, hq, hrq⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux
    (Fin.append v w)
  have hr₁' : LinearMap.range e₁ = V := hr₁
  have hr₂' : LinearMap.range e₂ = W := hr₂
  have hrq' : LinearMap.range q = V ⊔ W := by
    rw [hrq, range_finAppend, Submodule.span_union, ← hV, ← hW]
  -- `q` fixes `V`, so `q * e₁ = e₁`
  have hqe₁ : q * e₁ = e₁ := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    have hx : e₁ x ∈ LinearMap.range q := by
      rw [hrq']
      exact Submodule.mem_sup_left (by rw [← hr₁']; exact LinearMap.mem_range_self e₁ x)
    obtain ⟨c, hc⟩ := hx
    rw [← hc, ← Module.End.mul_apply q q c, hq]
  -- the idempotent `f = 1 - e₁` killing `V`
  set f : Module.End R (Fin n → R) := 1 - e₁ with hf
  have hff : f * f = f := by rw [hf]; noncomm_ring [he₁]
  -- `u = f * e₂`, and `W₀ = range u`
  set u : Module.End R (Fin n → R) := f * e₂ with hu
  set W₀ : Submodule R (Fin n → R) := LinearMap.range u with hW₀
  -- `W₀ = f '' W`
  have hW₀eq : W₀ = Submodule.map f W := by
    rw [hW₀, hu, Module.End.mul_eq_comp, LinearMap.range_comp, hr₂']
  -- `W₀ ≤ V ⊔ W`
  have hW₀_le : W₀ ≤ V ⊔ W := by
    rw [hW₀eq, Submodule.map_le_iff_le_comap]
    intro w hw
    rw [Submodule.mem_comap, hf, LinearMap.sub_apply, Module.End.one_apply]
    refine Submodule.sub_mem (V ⊔ W) (Submodule.mem_sup_right (S := V) hw) ?_
    refine Submodule.mem_sup_left (T := W) ?_
    rw [← hr₁']
    exact LinearMap.mem_range_self e₁ w
  -- weak inverse of `u`
  haveI : VonNeumannRegularRing (Module.End R (Fin n → R)) :=
    Work.ORHughesFree.StarRegular.vonNeumannRegularRing_moduleEnd n
  obtain ⟨z, hz⟩ := VonNeumannRegularRing.exists_mul_inverse u
  set h₀ : Module.End R (Fin n → R) := u * z with hh₀
  set h₁ : Module.End R (Fin n → R) := f * q with hh₁
  -- idempotency of `h₀`
  have hp₀ : h₀ * h₀ = h₀ := by
    rw [hh₀]
    have hz' : (u * z) * u = u := hz
    rw [show (u * z) * (u * z) = ((u * z) * u) * z from (mul_assoc (u * z) u z).symm, hz']
  -- range of `h₀` is `W₀`
  have hr_h₀ : LinearMap.range h₀ = W₀ := by
    have hz' : (u * z) * u = u := hz
    have hmain : LinearMap.range (u * z) = LinearMap.range u := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        exact ⟨z x, rfl⟩
      · rintro y ⟨x, rfl⟩
        refine ⟨u x, ?_⟩
        simp only [Module.End.mul_apply]
        exact congrArg (fun g : Module.End R (Fin n → R) => g x) hz'
    rw [hh₀, hW₀, hmain]
  -- range of `h₁` is `W₀`
  have hr_h₁ : LinearMap.range h₁ = W₀ := by
    rw [hh₁, hW₀eq]
    rw [Module.End.mul_eq_comp, LinearMap.range_comp, hrq', Submodule.map_sup]
    have hV0 : Submodule.map f V = ⊥ := by
      rw [← hr₁', ← LinearMap.range_comp]
      have hz' : f.comp e₁ = 0 := by
        rw [← Module.End.mul_eq_comp, hf, sub_mul, one_mul, he₁, sub_self]
      rw [hz', LinearMap.range_zero]
    rw [hV0, bot_sup_eq]
  -- idempotency of `h₁`
  have hp₁ : h₁ * h₁ = h₁ := by
    rw [hh₁]
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
    -- goal: f (q (f (q x))) = f (q x)
    have hy : f (q x) ∈ V ⊔ W := by
      have hmem : f (q x) ∈ LinearMap.range h₁ := ⟨x, by rw [hh₁, Module.End.mul_apply]⟩
      rw [hr_h₁] at hmem
      exact hW₀_le hmem
    have hqy : q (f (q x)) = f (q x) := by
      obtain ⟨c, hc⟩ := hrq' ▸ hy
      rw [← hc, ← Module.End.mul_apply q q c, hq]
    rw [hqy]
    exact congrArg (fun g : Module.End R (Fin n → R) => g (q x)) hff
  -- rank bound for `h₀`, transferred to `h₁`
  have hrank₀ : dimOfEnd rk h₀ ≤ dimOfEnd rk e₂ := by
    have hmat : Matrix.toLinearMapRight'.symm h₀
        = Matrix.toLinearMapRight'.symm z * Matrix.toLinearMapRight'.symm e₂
          * (1 - Matrix.toLinearMapRight'.symm e₁) := by
      rw [hh₀, hu, toLin_symm_mul, toLin_symm_mul, toLin_symm_sub, toLin_symm_one, mul_assoc]
    rw [dimOfEnd, hmat]
    refine le_trans (rk.rk_mul_le_left _ _) ?_
    exact rk.rk_mul_le_right _ _
  have hrank₁ : dimOfEnd rk h₁ = dimOfEnd rk h₀ :=
    rank_idem_eq_of_range_eq rk h₁ h₀ hp₁ hp₀ (by rw [hr_h₁, hr_h₀])
  -- the projection `Q = e₁ + h₁` onto `V ⊔ W`
  set Q : Module.End R (Fin n → R) := e₁ + h₁ with hQ
  -- every element of `V ⊔ W` is fixed by `Q`
  have hfixVW : ∀ x ∈ V ⊔ W, Q x = x := by
    intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have hqa : q a = a := by
      obtain ⟨c, hc⟩ := hrq' ▸ Submodule.mem_sup_left ha
      rw [← hc, ← Module.End.mul_apply q q c, hq]
    have hqb : q b = b := by
      obtain ⟨c, hc⟩ := hrq' ▸ Submodule.mem_sup_right hb
      rw [← hc, ← Module.End.mul_apply q q c, hq]
    have hea : e₁ a = a := by
      obtain ⟨c, hc⟩ := hr₁' ▸ ha
      rw [← hc, ← Module.End.mul_apply e₁ e₁ c, he₁]
    have hfa : f a = 0 := by
      obtain ⟨c, rfl⟩ := hr₁' ▸ ha
      rw [hf, LinearMap.sub_apply, Module.End.one_apply, ← Module.End.mul_apply e₁ e₁ c, he₁,
        sub_self]
    have heb : e₁ b + f b = b := by
      rw [hf, LinearMap.sub_apply, Module.End.one_apply]
      abel
    rw [← hab, hQ, LinearMap.add_apply, map_add, map_add, hh₁, Module.End.mul_apply,
      Module.End.mul_apply, hqa, hqb, hfa, hea]
    rw [zero_add, add_assoc, heb]
  have hQe₁ : Q * e₁ = e₁ := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    exact hfixVW (e₁ x) (Submodule.mem_sup_left
      (by rw [← hr₁']; exact LinearMap.mem_range_self e₁ x))
  have hQidem : Q * Q = Q := by
    rw [hQ]
    have h1z : e₁ * h₁ = 0 := by
      rw [hh₁, ← mul_assoc, hf, mul_sub, mul_one, he₁, sub_self, zero_mul]
    have h2z : h₁ * e₁ = 0 := by
      rw [hh₁, mul_assoc, hqe₁, hf, sub_mul, one_mul, he₁, sub_self]
    rw [add_mul, mul_add, mul_add, he₁, h1z, h2z, hp₁]
    abel
  have hQrange : LinearMap.range Q = V ⊔ W := by
    apply le_antisymm
    · rw [hQ]
      refine le_trans (LinearMap.range_add_le e₁ h₁) ?_
      rw [hr_h₁, hr₁']
      exact sup_le le_sup_left hW₀_le
    · exact sup_le (fun a ha => ⟨a, hfixVW a (Submodule.mem_sup_left ha)⟩)
        (fun b hb => ⟨b, hfixVW b (Submodule.mem_sup_right hb)⟩)
  -- rank of `Q` is the rank of `q`
  have hQq : dimOfEnd rk q = dimOfEnd rk Q :=
    rank_idem_eq_of_range_eq rk q Q hq hQidem (by rw [hrq', hQrange])
  -- rank subadditivity for the sum of two orthogonal idempotents
  have hQadd : dimOfEnd rk Q ≤ dimOfEnd rk e₁ + dimOfEnd rk h₁ := by
    rw [dimOfEnd, hQ, toLin_symm_add, dimOfEnd]
    exact RankAPI.rk_add_le rk _ _
  -- assemble
  have hd₁ : dimOfEnd rk e₁ = dimOf rk v := dimOf_eq rk v e₁ he₁ hr₁
  have hd₂ : dimOfEnd rk e₂ = dimOf rk w := dimOf_eq rk w e₂ he₂ hr₂
  have hdq : dimOfEnd rk q = dimOf rk (Fin.append v w) :=
    dimOf_eq rk (Fin.append v w) q hq hrq
  calc dimOf rk (Fin.append v w) = dimOfEnd rk q := hdq.symm
    _ = dimOfEnd rk Q := hQq
    _ ≤ dimOfEnd rk e₁ + dimOfEnd rk h₁ := hQadd
    _ = dimOfEnd rk e₁ + dimOfEnd rk h₀ := by rw [hrank₁]
    _ ≤ dimOfEnd rk e₁ + dimOfEnd rk e₂ := add_le_add le_rfl hrank₀
    _ = dimOf rk v + dimOf rk w := by rw [hd₁, hd₂]

end Work.ORHughesFree.NaturalExtension
