import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- `W := A ⊓ Ω₁(P)` (the involutions of a `ξ`-invariant abelian normal subgroup `A` of a
Suzuki 2-group) carries the restricted action of `ξ`; it is an elementary abelian group on which
`ξ` is transitive away from `1`.

Hints: `hW` together with `hA.map_eq` and `map_xi_omega1 h` (in
`Submission.Work.Higman.SuzukiMaximal`) shows `W` is `ξ`-invariant, so
`MulAut ↥W` can be built from `Subgroup.equivMapOfInjective` composed with
`MulEquiv.subgroupCongr`.  The exponent-2 claim is `h.mem_omega1` / `omega1_sq_eq_one`
(in `Submission.Work.Higman.Basic`).  For transitivity use `h.trans`: elements `≠ 1` of `W` have
`orderOf = 2`, and `(ξW ^ k) a = b` follows from `h.xi ^ k` applied to the underlying elements by
an induction on `k` using the first conjunct. -/
theorem clo7_W_xi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A W : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hW : W = A ⊓ Work.Higman.omega1 P) :
    ∃ ξW : MulAut ↥W,
      (∀ x : ↥W, ((ξW x) : P) = h.xi (x : P)) ∧
      (∀ x : ↥W, x * x = 1) ∧
      (∀ a b : ↥W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b) := by
  let f : P →* P := (h.xi : MulAut P).toMonoidHom
  have hf : Function.Injective f := fun a b hab => h.xi.injective hab
  -- `W = A ⊓ Ω₁(P)` is `ξ`-invariant.
  have hWmap : W.map f = W := by
    rw [hW, Subgroup.map_inf A (Work.Higman.omega1 P) f hf, hA.map_eq, map_xi_omega1 h]
  -- The restricted action of `ξ` on `W`.
  set ξW : MulAut ↥W :=
    (Subgroup.equivMapOfInjective W f hf).trans (MulEquiv.subgroupCongr hWmap) with hξW
  -- The underlying permutation of `W` is `ξ`.
  have h1 : ∀ x : ↥W, ((ξW x) : P) = h.xi (x : P) := by
    intro x
    rw [hξW, MulEquiv.coe_trans, Function.comp_apply, MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply W f hf x
  -- The power of `ξW` acts as the power of `ξ` on underlying elements.
  have hcoe : ∀ (m : ℕ) (x : ↥W), (((ξW ^ m) x : ↥W) : P) = (h.xi ^ m) (x : P) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, h1, ih x]
  refine ⟨ξW, h1, ?_, ?_⟩
  · intro x
    have hxO : (x : P) ∈ Work.Higman.omega1 P :=
      (Subgroup.mem_inf.mp (by rw [← hW]; exact x.2)).2
    have hx2 : (x : P) * (x : P) = 1 := by
      simpa [pow_two] using h.mem_omega1.mp hxO
    exact Subtype.ext (by simpa using hx2)
  · intro a b ha hb
    have haO : (a : P) ∈ Work.Higman.omega1 P :=
      (Subgroup.mem_inf.mp (by rw [← hW]; exact a.2)).2
    have hbO : (b : P) ∈ Work.Higman.omega1 P :=
      (Subgroup.mem_inf.mp (by rw [← hW]; exact b.2)).2
    have ha1 : (a : P) ≠ 1 := fun hh => ha (Subtype.ext hh)
    have hb1 : (b : P) ≠ 1 := fun hh => hb (Subtype.ext hh)
    have ha2 : orderOf (a : P) = 2 := by
      have hdvd : orderOf (a : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h.mem_omega1.mp haO)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) ha1
      · exact hh
    have hb2 : orderOf (b : P) = 2 := by
      have hdvd : orderOf (b : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h.mem_omega1.mp hbO)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hb1
      · exact hh
    obtain ⟨k, hk⟩ := h.trans (a : P) (b : P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [hcoe k a]; exact hk)⟩

end Work.Higman
