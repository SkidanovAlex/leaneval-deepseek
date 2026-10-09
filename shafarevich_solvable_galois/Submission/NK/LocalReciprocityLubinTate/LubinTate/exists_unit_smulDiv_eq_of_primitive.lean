import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple_of_fibre
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_level
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_mem
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

/-- **Two primitive points of the same level differ by a unit.**  For the standard Lubin–Tate
group `f(T) = πT + T^q` of a uniformiser `π` of a nonarchimedean local field `F`, any two
elements `y, z` of `Λ_n ∖ Λ_{n-1}` are related by the action of a *unit* of `𝒪[F]`:

  `z = u · y`   with `u ∈ 𝒪[F]ˣ`.

This is the "rank one" statement for `Λ_n` (Milne, *CFT*, Theorem I.3.1): the whole level is the
orbit of any primitive point (`range_smulDiv_eq_LTdivisionSet`), and the multiplier of a point
which is again primitive is forced to be a unit, because an element divisible by `π` kills the
primitivity (`smulDiv_mem_iff_mem_span`). -/
theorem exists_unit_smulDiv_eq_of_primitive {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π
      (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π
      (NK.LocalReciprocityLubinTate.residueCard F))
    {y z : AlgebraicClosure F}
    (hy : y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hy' : y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1))
    (hz : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hz' : z ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1)) :
    ∃ u : (↥(ValuativeRel.valuation F).integer)ˣ,
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n
        (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy
        (u : ↥(ValuativeRel.valuation F).integer) = z := by
  classical
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  -- The level `Λ_n` is the `𝒪[F]`-orbit of the primitive point `y`.
  have hrange := NK.LocalReciprocityLubinTate.Eval.range_smulDiv_eq_LTdivisionSet
      π hπ (NK.LocalReciprocityLubinTate.residueCard F) n hq hn rfl M hpi hy hy'
  have hzrange : z ∈ Set.range (fun a : ↥(ValuativeRel.valuation F).integer =>
      NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a) := by
    rw [hrange]; exact hz
  obtain ⟨a, ha⟩ := hzrange
  beta_reduce at ha
  -- The multiplier `a` must be a unit: if `π ∣ a` then `a · y ∈ Λ_{n-1}`, contradicting `z ∉ Λ_{n-1}`.
  have hnot : a ∉ Ideal.span {π} := by
    intro hspan
    have hpow : a ∈ Ideal.span {π ^ (n - (n - 1))} := by
      have h1 : n - (n - 1) = 1 := Nat.sub_sub_self hn
      rw [h1, pow_one]
      exact hspan
    have hmem := (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem_iff_mem_span π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi hy hy hy' le_rfl (n - 1)
        (Nat.sub_le n 1) a).mpr hpow
    rw [ha] at hmem
    exact hz' hmem
  have hunit : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal, hπ.maximalIdeal_eq]
    exact hnot
  exact ⟨hunit.unit, by rw [hunit.unit_spec]; exact ha⟩

end NK.LocalReciprocityLubinTate.LubinTate
