import Mathlib
import Submission.Work.ThmF.ChV3.step3
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.fpf_oddPart
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.oddPart_le_normalizer
import Submission.Work.ThmF.Prove.S3.card_dvd_card_of_free_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.S3.oddPart_dvd_fpf` — Peterfalvi II, Ch. V §3: the congruence `|K| ∣ |Q₁| - 1`

In the standing context `CtxF H Q t s r P` of Peterfalvi II, Ch. V §3, and with `Q` nilpotent:

* `H` normalises `Q₁ = O_{2'}(Q) = oddPart Q`  (Ch. V §1 Prop. 1 b, from `H ≤ N(Q)`);
* the closure `K = ⟨J(D,t)⟩ = Ksub H t` of the set `J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}` acts by
  conjugation on `Q₁`, and every `k ∈ K`, `k ≠ 1` acts **fixed-point-freely** on `Q₁`;
* hence `|K| ∣ |Q₁| - 1` (a free action on the non-identity elements), and
* `|Q₁|` is odd (Ch. V §1 Prop. 1 b, the `O_2 × O_{2'}` splitting of a finite nilpotent group).

The fixed-point-freeness for all of `K` is where `FeitThompsonProp` enters: Ch. V §1 Prop. 2
(`Work.ThmF.ChV12.Ksub_cyclic_normal`, which uses Feit–Thompson) shows that `⟨J(D,t)⟩ = J(D,t)`
as *sets*, so every element of `K` is a generator, for which Ch. V §1 Prop. 1 a
(`Work.ThmF.ChV3.fpf_Kset_oddPart`, via `Work.ThmF.ChV12.prop1a`) gives the fixed-point-freeness.

The counting step is the general fact `dvd_card_sub_one_of_free` below.
-/

namespace Work.S3

open LeanEval.GroupTheory.Defs

/-! ## Two elementary counting/action facts -/

/-- Conjugation gives an action of a subgroup `A` on a subgroup `B` whenever `A` normalises `B`:
`a • b = a b a⁻¹`. -/
noncomputable def conjMulAction {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : MulAction ↥A ↥B where
  smul a b := ⟨(a : G) * (b : G) * (a : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h a.2) (b : G)).mp b.2⟩
  one_smul b := by
    apply Subtype.ext
    show (1 : G) * (b : G) * (1 : G)⁻¹ = (b : G)
    simp
  mul_smul a₁ a₂ b := by
    apply Subtype.ext
    show ((a₁ : G) * (a₂ : G)) * (b : G) * ((a₁ : G) * (a₂ : G))⁻¹
      = (a₁ : G) * ((a₂ : G) * (b : G) * (a₂ : G)⁻¹) * (a₁ : G)⁻¹
    group

/-- A finite type with one point removed has one element fewer. -/
theorem card_subtype_ne {X : Type} [Finite X] (x0 : X) :
    Nat.card {x : X // x ≠ x0} = Nat.card X - 1 := by
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype {x : X // x = x0} := Fintype.ofFinite _
  haveI : Fintype {x : X // x ≠ x0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := X),
    Fintype.card_subtype_compl (fun x : X => x = x0), Fintype.card_subtype_eq x0]

/-- **Orbit counting.**  If a finite group `K` acts on a finite type `X`, fixes a point `x0`, and
acts freely away from `x0`, then `|K| ∣ |X| - 1`: the complement of `x0` is a disjoint union of
free orbits, each of cardinality `|K|`. -/
theorem dvd_card_sub_one_of_free {K X : Type} [Group K] [Finite K] [MulAction K X] [Finite X]
    (x0 : X) (hfix : ∀ k : K, k • x0 = x0)
    (hfree : ∀ k : K, k ≠ 1 → ∀ x : X, x ≠ x0 → k • x = x → False) :
    Nat.card K ∣ Nat.card X - 1 := by
  let Y := {x : X // x ≠ x0}
  letI : MulAction K Y :=
    { smul := fun k y => ⟨k • y.1, fun h => y.2 (by
        have h1 : k⁻¹ • (k • y.1) = k⁻¹ • x0 := by rw [h]
        rwa [inv_smul_smul, hfix k⁻¹] at h1)⟩
      one_smul := fun y => Subtype.ext (one_smul K y.1)
      mul_smul := fun a b y => Subtype.ext (mul_smul a b y.1) }
  have hfreeY : ∀ k : K, k ≠ 1 → ∀ y : Y, k • y = y → False := by
    intro k hk y hy
    refine hfree k hk (y : X) y.2 ?_
    show k • (y : X) = (y : X)
    exact congrArg Subtype.val hy
  have hdvd := Work.ThmF.Prove.S3.card_dvd_card_of_free_action (K := K) (X := Y) hfreeY
  have hY : Nat.card Y = Nat.card X - 1 := card_subtype_ne x0
  rwa [hY] at hdvd

/-! ## Fixed-point-freeness of `K = ⟨J(D,t)⟩` on `Q₁ = oddPart Q` -/

/-- In the standing context, every non-identity element of `K = Ksub H t = ⟨J(D,t)⟩` acts
fixed-point-freely on `Q₁ = oddPart Q`.

Ch. V §1 Prop. 2 (`Ksub_cyclic_normal`, using `FeitThompsonProp`) identifies the *set* `K` with
`J(D,t)`, and Ch. V §1 Prop. 1 a (`fpf_Kset_oddPart`) gives the fixed-point-freeness on the
generating set. -/
theorem Ksub_fpf_oddPart {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∀ k ∈ Work.ThmF.Ksub H t, k ≠ 1 → ∀ x ∈ Work.ThmF.oddPart Q, k * x * k⁻¹ = x → x = 1 := by
  intro k hk hk1 x hx hkx
  have hKset : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 c.sit c.split).2.1
  have hkK : k ∈ Work.ThmF.Kset H t := hKset ▸ hk
  have hcomm : x * k = k * x := by
    have h := congrArg (fun u : G => u * k) hkx
    have h' : k * x = x * k := by simpa [mul_assoc] using h
    exact h'.symm
  exact Work.ThmF.ChV3.fpf_Kset_oddPart c.sit hC4 c.split hkK hk1 hx hcomm

/-! ## The target -/

theorem oddPart_dvd_fpf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hQnil : Group.IsNilpotent ↥Q) :
    H ≤ Subgroup.normalizer ((Work.ThmF.oddPart Q : Subgroup G) : Set G) ∧
      Nat.card ↥(Work.ThmF.Ksub H t) ∣ Nat.card ↥(Work.ThmF.oddPart Q) - 1 ∧
      Odd (Nat.card ↥(Work.ThmF.oddPart Q)) := by
  classical
  -- `oddPart` is the same subgroup in the `ThmF` and `ThmG` vocabularies
  have hQ1 : Work.ThmF.oddPart Q = Work.ThmG.oddPart Q := rfl
  -- (1) `H` normalises `Q₁ = oddPart Q`
  have hnorm : H ≤ Subgroup.normalizer ((Work.ThmF.oddPart Q : Subgroup G) : Set G) := by
    have h := Work.ThmG.oddPart_le_normalizer c.split.normal
    simpa [hQ1] using h
  -- (2) `K = Ksub H t = J(D,t)` and `K ≤ D ≤ H`
  have hKD : Work.ThmF.Ksub H t ≤ Submission.Blueprint.twoPoint H t :=
    (Subgroup.closure_le _).mpr (Work.ThmF.Kset_subset H t)
  have hKH : Work.ThmF.Ksub H t ≤ H := le_trans hKD inf_le_left
  have hKN : Work.ThmF.Ksub H t ≤
      Subgroup.normalizer ((Work.ThmF.oddPart Q : Subgroup G) : Set G) := le_trans hKH hnorm
  -- (3) `K` acts freely (away from the identity) on `Q₁` by conjugation
  have hfpf := Ksub_fpf_oddPart (H := H) (Q := Q) (t := t) (s := s) (r := r) (P := P)
    hFT hC4 c
  -- (4) hence `|K| ∣ |Q₁| - 1`
  have hdvd : Nat.card ↥(Work.ThmF.Ksub H t) ∣ Nat.card ↥(Work.ThmF.oddPart Q) - 1 := by
    letI act : MulAction ↥(Work.ThmF.Ksub H t) ↥(Work.ThmF.oddPart Q) := conjMulAction hKN
    refine dvd_card_sub_one_of_free (K := ↥(Work.ThmF.Ksub H t))
      (X := ↥(Work.ThmF.oddPart Q)) (1 : ↥(Work.ThmF.oddPart Q)) ?_ ?_
    · intro k
      apply Subtype.ext
      show ((k : G) * (1 : G) * ((k : G))⁻¹) = (1 : G)
      simp
    · intro k hk1 x hx1 hkx
      have hkG : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
      have hxG : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hval : (k : G) * (x : G) * ((k : G))⁻¹ = (x : G) := by
        have h1 := congrArg (fun z : ↥(Work.ThmF.oddPart Q) => (z : G)) hkx
        show (k : G) * (x : G) * ((k : G))⁻¹ = (x : G)
        exact h1
      exact hxG (hfpf (k : G) k.2 hkG (x : G) x.2 hval)
  -- (5) `|Q₁|` is odd (the `O_2 × O_{2'}` splitting of a finite nilpotent group)
  have hodd : Odd (Nat.card ↥(Work.ThmF.oddPart Q)) := by
    have h := (Work.ThmG.nilpotent_two_odd_split Q hQnil).2.2.2.2.1
    simpa [hQ1] using h
  exact ⟨hnorm, hdvd, hodd⟩

end Work.S3
