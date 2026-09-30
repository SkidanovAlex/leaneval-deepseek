import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.RiemannRoch.RR.finite_H1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics
open Work.RiemannRoch.Curve

section

/-- `Cardinal.toNat` is nondecreasing under adding a natural number:
`a.toNat ≤ (a + n).toNat`.  (For `a` infinite both sides are `0`; for `a` finite it reads
`a.toNat ≤ a.toNat + n`.) -/
private lemma card_toNat_le_toNat_add (a : Cardinal) (n : ℕ) :
    a.toNat ≤ (a + n).toNat := by
  rcases lt_or_ge a Cardinal.aleph0 with h | h
  · have ha : (a.toNat : Cardinal) = a := Cardinal.cast_toNat_of_lt_aleph0 h
    have hthis : a + (n : Cardinal) = ((a.toNat + n : ℕ) : Cardinal) := by
      rw [Nat.cast_add, ha]
    rw [hthis, Cardinal.toNat_natCast]
    exact Nat.le_add_right _ _
  · rw [Cardinal.toNat_apply_of_aleph0_le h]; exact Nat.zero_le _

/-- A quotient of a vector space by a finite-dimensional subspace has no larger `finrank`:
this is the rank–nullity equality `finrank (W ⧸ p) + finrank p = finrank W` (when `W ⧸ p` is
infinite dimensional both `finrank`s vanish, and the inequality is trivial). -/
private lemma finrank_quotient_le_of_finiteDimensional {k : Type u} [Field k]
    {W : Type u} [AddCommGroup W] [Module k W] (p : Submodule k W) [FiniteDimensional k p] :
    Module.finrank k (W ⧸ p) ≤ Module.finrank k W := by
  have hrank : Module.rank k W = Module.rank k (W ⧸ p) + Module.rank k ↥p :=
    (rank_quotient_add_rank_of_divisionRing p).symm
  have hp : Module.rank k ↥p = (Module.finrank k ↥p : Cardinal) :=
    (Module.finrank_eq_rank k ↥p).symm
  simp only [Module.finrank]
  rw [hrank, hp]
  exact card_toNat_le_toNat_add _ _

/-- **Anti-monotonicity of `finrank` of quotients.**  For submodules `M ≤ N` of a `k`-vector
space `V` such that `N ⧸ M` is finite dimensional, the quotient by the larger submodule has no
larger `finrank`:  `finrank (V ⧸ N) ≤ finrank (V ⧸ M)`.

Indeed `V ⧸ N ≃ (V ⧸ M) ⧸ (N ⧸ M)` and `N ⧸ M ≅ N.map (mkQ M)` is finite dimensional. -/
private lemma finrank_quotient_le_of_le {k : Type u} [Field k] {V : Type u} [AddCommGroup V]
    [Module k V] (M N : Submodule k V) (hMN : M ≤ N)
    [FiniteDimensional k (↥N ⧸ M.comap N.subtype)] :
    Module.finrank k (V ⧸ N) ≤ Module.finrank k (V ⧸ M) := by
  -- `N.map (mkQ M)`, the kernel of `V ⧸ M → V ⧸ N`, is finite dimensional.
  have hfin : Module.Finite k ↥(N.map (Submodule.mkQ M)) := by
    haveI : FiniteDimensional k (↥N ⧸ M.comap N.subtype) := inferInstance
    let t : ↥N →ₗ[k] ↥(N.map (Submodule.mkQ M)) :=
      { toFun := fun x => ⟨(Submodule.mkQ M) (x : V),
          Submodule.mem_map_of_mem (f := Submodule.mkQ M) x.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp }
    have hker : LinearMap.ker t = M.comap N.subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      constructor
      · intro hx
        have h : (Submodule.mkQ M) (x : V) = 0 := Subtype.ext_iff.mp hx
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      · intro hx
        apply Subtype.ext
        show (Submodule.mkQ M) (x : V) = (0 : V ⧸ M)
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hx
    have hsurj : Function.Surjective t := by
      rintro ⟨y, hy⟩
      rw [Submodule.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
    exact Module.Finite.equiv ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective t hsurj))
  haveI := hfin
  calc Module.finrank k (V ⧸ N)
      = Module.finrank k ((V ⧸ M) ⧸ N.map (Submodule.mkQ M)) :=
        (LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotient M N hMN)).symm
    _ ≤ Module.finrank k (V ⧸ M) := finrank_quotient_le_of_finiteDimensional _

end

theorem i_anti {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) : Work.RiemannRoch.Curve.i C E ≤ Work.RiemannRoch.Curve.i C D := by
  have hAsub : Asub C D ≤ Asub C E := Submodule.comap_mono (A_mono C h)
  have hMN : Asub C D ⊔ diagK C ≤ Asub C E ⊔ diagK C := sup_le_sup hAsub le_rfl
  have hrel : Module.Finite k (relQuot (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C)) :=
    finite_sup_quotient (S := Asub C D) (T := Asub C E) (K := diagK C) (finite_relQuot_Asub C h)
  haveI : FiniteDimensional k (relQuot (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C)) := hrel
  exact finrank_quotient_le_of_le (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C) hMN

end Work.RiemannRoch.RR
