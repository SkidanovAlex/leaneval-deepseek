import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmG

/-- The character inner product of a constant function with itself is `c * conj c`. -/
theorem cfInner_const {G : Type*} [Group G] [Fintype G] (c : ℂ) :
    Work.CharCore.cfInner (fun _ : G => c) (fun _ : G => c) = c * starRingEnd ℂ c := by
  rw [Work.CharCore.cfInner_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_ne : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hcard_ne, one_mul]

/-- An irreducible character of a finite group that is constant on the group is the trivial
character: a constant irreducible character `f` with value `d = f 1` has, by the first
orthogonality relation, `cfInner f f = d * conj d = 1`; as `d` is a natural number this forces
`d = 1`, hence `f ≡ 1`. -/
theorem irr_eq_one_of_forall_eq_one {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : f ∈ Work.CharCore.Irr G) (h : ∀ x : G, f x = f 1) :
    f = (fun _ : G => (1 : ℂ)) := by
  -- the constant value `f 1` is the degree, a natural number `d`
  obtain ⟨d, hd⟩ := Work.CharCore.exists_natCast_apply_one hf
  have hfval : ∀ x, f x = (d : ℂ) := fun x => (h x).trans hd
  have hconst : f = fun _ : G => (d : ℂ) := funext hfval
  -- orthonormality of `Irr G`: the self-inner-product of `f` is `1`
  have horth : Work.CharCore.cfInner f f = 1 := Work.CharCore.cfInner_self_mem_Irr hf
  rw [hconst, cfInner_const, Complex.conj_natCast] at horth
  -- so `d * d = 1` in `ℕ`, whence `d = 1`
  have hd1 : d = 1 := by
    have h1 : (d * d : ℕ) = 1 := by
      apply Nat.cast_injective (R := ℂ); push_cast; exact horth
    exact Nat.dvd_one.mp ⟨d, by rw [h1]⟩
  funext x
  rw [hfval x, hd1]
  norm_num

end Work.ThmG
