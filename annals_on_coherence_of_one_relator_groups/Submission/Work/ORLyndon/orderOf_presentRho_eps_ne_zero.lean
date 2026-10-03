import Mathlib
import Submission.Work.ORLyndon.epsNeZeroDescent_plan
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.eps_eq_toAdd_sigma
import Submission.Work.ORLyndon.addOrderOf_intCast_zmod_mul
import Submission.Work.ORLyndon.mul_ite_one_neg_one_eq_natAbs

/-!
# The order of the root of a one-relator relator from non-vanishing exponent sums

For a word `u` in the free group `F(α)` and `1 ≤ l`, the class `w = presentRho (u ^ l) u` of `u`
in the one-relator group `G = ⟨α | u ^ l⟩` has order exactly `l`, provided that **every** letter
of `u` occurs with non-zero exponent sum.

The upper bound is immediate (`w ^ l = 1`).  For the lower bound no one-relator hierarchy, no
Karrass--Magnus--Solitar torsion theorem and no root theory is needed: it suffices that **one**
letter `x₀` of `u` has non-zero exponent sum `d = eps x₀ u ≠ 0`.  The exponent sum in `x₀` is a
homomorphism `sigma x₀ : F(α) →* ℤ` (`Work.OROneRel.sigma`), and composing it with a suitable map
`Multiplicative ℤ →* Multiplicative (ZMod (l * |d|))` and applying the universal property of the
presentation `⟨α | u ^ l⟩` produces a homomorphism `φ : G →* Multiplicative (ZMod (l * |d|))`
whose value on `w` is the residue class of `d`, of order `l`.  Since the order of an image divides
the order of the element, `l ∣ orderOf w`; with `orderOf w ∣ l` this is the claim.

The two arithmetic ingredients are `Work.ORLyndon.addOrderOf_intCast_zmod_mul` (the residue class
of `D` modulo `l * D` has additive order `l`) and `Work.ORLyndon.mul_ite_one_neg_one_eq_natAbs`
(multiplying `d` by its sign returns `|d|`).
-/

namespace Work.ORLyndon

universe u

theorem orderOf_presentRho_eps_ne_zero {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (hsne : (Work.OROneRel.relatorLetters u).Nonempty) (hne : ∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0) : orderOf (Work.ORLyndon.presentRho (u ^ l) u) = l := by
  classical
  -- Choose a letter `x₀` of `u`; its exponent sum `d` is non-zero by hypothesis.
  obtain ⟨x₀, hx₀⟩ := hsne
  set d : ℤ := Work.OROneRel.eps x₀ u with hddef
  have hd : d ≠ 0 := by rw [hddef]; exact hne x₀ hx₀
  have hDne : d.natAbs ≠ 0 := (Int.natAbs_pos.mpr hd).ne'
  -- The sign `e` of `d`: the exponent sum homomorphism composed with `e`-multiplication sends `u`
  -- to `|d|`, a positive residue class of additive order `l` in `ZMod (l * |d|)`.
  set e : ℤ := if 0 ≤ d then 1 else -1 with he
  have hed : d * e = ((d.natAbs : ℕ) : ℤ) := by
    rw [he]; exact mul_ite_one_neg_one_eq_natAbs d
  have horder : addOrderOf (((d.natAbs : ℕ) : ℤ) : ZMod (l * d.natAbs)) = l :=
    addOrderOf_intCast_zmod_mul d.natAbs l hl hDne
  /- The homomorphism `Multiplicative ℤ →* Multiplicative (ZMod (l * |d|))` multiplying by `e`. -/
  let h : Multiplicative ℤ →* Multiplicative (ZMod (l * d.natAbs)) :=
    { toFun := fun m => Multiplicative.ofAdd ((m.toAdd * e : ℤ) : ZMod (l * d.natAbs))
      map_one' := by simp
      map_mul' := by intro a b; simp [add_mul] }
  let f : α → Multiplicative (ZMod (l * d.natAbs)) :=
    fun x => h ((Work.OROneRel.sigma x₀) (FreeGroup.of x))
  have hsig : (Work.OROneRel.sigma x₀) u = Multiplicative.ofAdd d := by
    rw [← ofAdd_toAdd ((Work.OROneRel.sigma x₀) u),
      ← Work.OROneRel.eps_eq_toAdd_sigma x₀ u, hddef]
  have hlift : FreeGroup.lift f u
      = Multiplicative.ofAdd (((d.natAbs : ℕ) : ℤ) : ZMod (l * d.natAbs)) := by
    have h1 := FreeGroup.lift_unique (f := f) (g := h.comp (Work.OROneRel.sigma x₀))
      (fun x => rfl) (x := u)
    rw [← h1]
    show h ((Work.OROneRel.sigma x₀) u) = _
    rw [hsig]
    show Multiplicative.ofAdd ((d * e : ℤ) : ZMod (l * d.natAbs)) = _
    rw [hed]
  /- The lifted generator map kills the relator `u ^ l`, so it descends to `G`. -/
  have hrel : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    rw [hr, map_pow, hlift, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul,
      Int.cast_natCast, ← Nat.cast_mul l d.natAbs, ZMod.natCast_self]
  let φ : Work.ORLyndon.OneRelatorGroup (u ^ l) →* Multiplicative (ZMod (l * d.natAbs)) :=
    PresentedGroup.toGroup hrel
  have h2 : (φ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))) u = FreeGroup.lift f u :=
    FreeGroup.lift_unique (f := f)
      (g := φ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))))
      (fun x => PresentedGroup.toGroup.of hrel) (x := u)
  have hφ : φ (Work.ORLyndon.presentRho (u ^ l) u)
      = Multiplicative.ofAdd (((d.natAbs : ℕ) : ℤ) : ZMod (l * d.natAbs)) := by
    have h2' := h2
    rw [MonoidHom.comp_apply] at h2'
    rw [show Work.ORLyndon.presentRho (u ^ l) u
        = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u from rfl, h2', hlift]
  /- `φ w` has order exactly `l`. -/
  have hφorder : orderOf (φ (Work.ORLyndon.presentRho (u ^ l) u)) = l := by
    rw [hφ, orderOf_ofAdd_eq_addOrderOf, horder]
  have hdvd1 : orderOf (Work.ORLyndon.presentRho (u ^ l) u) ∣ l := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [← MonoidHom.map_pow]
    exact Work.ORLyndon.presentRho_relator (u ^ l)
  have hdvd2 : l ∣ orderOf (Work.ORLyndon.presentRho (u ^ l) u) := by
    have h3 : orderOf (φ (Work.ORLyndon.presentRho (u ^ l) u))
        ∣ orderOf (Work.ORLyndon.presentRho (u ^ l) u) :=
      orderOf_map_dvd φ (Work.ORLyndon.presentRho (u ^ l) u)
    rwa [hφorder] at h3
  exact Nat.dvd_antisymm hdvd1 hdvd2

end Work.ORLyndon
