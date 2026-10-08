import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.S3.card_dvd_card_of_free_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.S3.case1_modEq_one` — Case 1 of Peterfalvi II, Ch. V §3: `ℓ ≡ 1 (mod |K|)`

In the standing context of Ch. V §3, let `ℓ` be a prime and `U ≠ 1` an `ℓ`-group (so
`|U| = ℓ`) normalised by `K = Ksub H t = ⟨J(D,t)⟩`, sitting inside a subgroup `M ≤ G` on which
every non-identity element of `K` acts fixed-point-freely (`hMfpf`).  Then

  `ℓ ≡ 1 [MOD |K|]`.

The reason is purely combinatorial.  Conjugation gives an action of the finite group `K` on the
finite set `↥U` by group automorphisms.  The identity of `U` is a fixed point, and on the
complement `U \ {1}` the action is free: if `k ∈ K`, `k ≠ 1` and `u ∈ U ⊆ M` satisfy
`k u k⁻¹ = u`, then `hMfpf` forces `u = 1`.  The complement of a point in a finite set of size
`ℓ` has `ℓ - 1` elements, and a free action of a finite group `K` on a finite set `X` satisfies
`|K| ∣ |X|` (`card_dvd_card_of_free_action`, the orbit-stabilizer argument via Burnside's
lemma).  Hence `|K| ∣ ℓ - 1`, i.e. `ℓ ≡ 1 [MOD |K|]`.
-/

set_option linter.style.haveILetI false

namespace Work.S3

/-- The complement of a point in a finite type has one element fewer. -/
private theorem card_compl_singleton {X : Type} [Finite X] (x0 : X) :
    Nat.card {x : X // x ≠ x0} = Nat.card X - 1 := by
  have : Fintype X := Fintype.ofFinite X
  have : Fintype {x : X // x ≠ x0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := X),
    Fintype.card_subtype_compl (fun x : X => x = x0), Fintype.card_subtype_eq x0]

theorem case1_modEq_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {M U : Subgroup G} (hUle : U ≤ M) (hUne : U ≠ ⊥)
    (hUcard : Nat.card ↥U = ℓ)
    (hUinv : ∀ k ∈ Work.ThmF.Ksub H t, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hMfpf : ∀ k ∈ Work.ThmF.Ksub H t, k ≠ 1 → ∀ m ∈ M, k * m * k⁻¹ = m → m = 1) :
    ℓ ≡ 1 [MOD Nat.card ↥(Work.ThmF.Ksub H t)] := by
  classical
  haveI : Finite ↥(Work.ThmF.Ksub H t) := Subtype.finite
  haveI : Finite ↥U := Subtype.finite
  -- Conjugation makes `K = Ksub H t` act on `U`.
  letI actK : MulAction ↥(Work.ThmF.Ksub H t) ↥U :=
    { smul := fun k u =>
        ⟨(k : G) * (u : G) * (k : G)⁻¹, hUinv (k : G) k.2 (u : G) u.2⟩
      one_smul := fun u => Subtype.ext (by
        show (1 : G) * (u : G) * (1 : G)⁻¹ = (u : G)
        simp)
      mul_smul := fun a b u => Subtype.ext (by
        show ((a : G) * (b : G)) * (u : G) * ((a : G) * (b : G))⁻¹
          = (a : G) * ((b : G) * (u : G) * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  -- The identity of `U` is a fixed point.
  have hfix : ∀ k : ↥(Work.ThmF.Ksub H t), k • (1 : ↥U) = 1 := by
    intro k
    apply Subtype.ext
    show (k : G) * (1 : G) * (k : G)⁻¹ = (1 : G)
    simp
  -- On `U \ {1}` the action is free.
  let Y := {u : ↥U // u ≠ 1}
  haveI : Finite Y := Subtype.finite
  letI actY : MulAction ↥(Work.ThmF.Ksub H t) Y :=
    { smul := fun k y => ⟨k • y.1, by
        intro h
        exact y.2 (by
          have h1 : k⁻¹ • (k • y.1) = k⁻¹ • (1 : ↥U) := by rw [h]
          rwa [inv_smul_smul, hfix k⁻¹] at h1)⟩
      one_smul := fun y => Subtype.ext (one_smul _ y.1)
      mul_smul := fun a b y => Subtype.ext (mul_smul a b y.1) }
  have hfreeY : ∀ k : ↥(Work.ThmF.Ksub H t), k ≠ 1 → ∀ y : Y, k • y = y → False := by
    intro k hk y hy
    have hky : k • y.1 = y.1 := congrArg Subtype.val hy
    have hkG : (k : G) ≠ 1 := fun h => hk (Subtype.ext h)
    have hval : (k : G) * (y.1 : G) * (k : G)⁻¹ = (y.1 : G) :=
      congrArg Subtype.val hky
    exact y.2 (Subtype.ext (hMfpf (k : G) k.2 hkG (y.1 : G) (hUle y.1.2) hval))
  -- A free action: `|K| ∣ |U \ {1}| = ℓ - 1`.
  have hdvd : Nat.card ↥(Work.ThmF.Ksub H t) ∣ Nat.card Y :=
    Work.ThmF.Prove.S3.card_dvd_card_of_free_action hfreeY
  have hYcard : Nat.card Y = ℓ - 1 := by
    change Nat.card {u : ↥U // u ≠ 1} = ℓ - 1
    rw [card_compl_singleton (1 : ↥U), hUcard]
  rw [hYcard] at hdvd
  exact ((Nat.modEq_iff_dvd' hℓ.one_lt.le).mpr hdvd).symm

end Work.S3
