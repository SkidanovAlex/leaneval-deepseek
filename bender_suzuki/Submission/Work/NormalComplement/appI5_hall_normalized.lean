import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_two
import Submission.Work.Hall.MainResults
import Submission.Work.Coprime.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NormalComplement

/-- The type of Hall `π`-subgroups of a group `G`: the analogue for Hall subgroups of the type
`Sylow p G` of Sylow `p`-subgroups. -/
abbrev HallSub (π : ℕ → Prop) (G : Type*) [Group G] : Type _ :=
  {H : Subgroup G // Work.Hall.IsHall π H}

/-- A group `α` acting by automorphisms on `G` acts on the Hall `π`-subgroups of `G`
(transporting a Hall subgroup along an automorphism of `G` preserves the Hall property). -/
@[instance_reducible]
def hallSubMulAction (π : ℕ → Prop) (α G : Type*) [Group α] [Group G]
    [MulDistribMulAction α G] : MulAction α (HallSub π G) where
  smul a H :=
    ⟨a • H.1, Work.Hall.isHall_map_of_surjective (MulDistribMulAction.toMonoidEnd α G a)
      (fun y => ⟨a⁻¹ • y, by
        show (MulDistribMulAction.toMonoidEnd α G a) (a⁻¹ • y) = y
        rw [show (MulDistribMulAction.toMonoidEnd α G a) (a⁻¹ • y) = a • (a⁻¹ • y) from rfl,
          smul_inv_smul]⟩) H.2⟩
  one_smul H := Subtype.ext (one_smul α H.1)
  mul_smul a b H := Subtype.ext (mul_smul a b H.1)

/-- The automorphism `a • ·` of `X` and the inner automorphism `x * · * x⁻¹` of `X` satisfy
`a (x y x⁻¹) a⁻¹ = (a x) (a y) (a x)⁻¹`; equivalently the action of `A` by automorphisms and the
conjugation action of `X` on `X` are compatible as actions on the Hall subgroups of `X`. -/
lemma mulAut_conj_smul_compat {A X : Type*} [Group A] [Group X] [MulDistribMulAction A X]
    (a : A) (x : X) :
    MulDistribMulAction.toMulAut A X a * MulAut.conj x =
      MulAut.conj (a • x) * MulDistribMulAction.toMulAut A X a := by
  ext y
  show MulDistribMulAction.toMulAut A X a ((MulAut.conj x) y) =
    (MulAut.conj (a • x)) (MulDistribMulAction.toMulAut A X a y)
  simp only [MulAut.conj_apply, MulDistribMulAction.toMulAut_apply,
    MulDistribMulAction.toMulEquiv_apply, smul_mul', smul_inv']

/-- **App. I (5)(a), the Hall input** (Peterfalvi, *Le théorème de Bender-Suzuki I*, p. 201):
"By Hall's theorem, the number of Hall `p'`-subgroups of `X` is `≠ 0` and prime to `d`, so there is
a Hall `p'`-subgroup `R` of `X` with `R^t = R`."

Here `X` is a finite solvable subgroup of `G` normalized by `t`, with `Nat.card X` coprime to
`d = orderOf t`, and `q` is prime.  We ask for a `t`-invariant Hall `q'`-subgroup `R` of `X`,
exhibited as a subgroup of the ambient group `G` with `R ≤ X`, `NormalizedBy t R`,
`¬ q ∣ Nat.card R`, and the index `|X : R|` a power of `q`.

Intended route: put `A = Subgroup.zpowers t ≤ G` (so `Nat.card A = orderOf t = d`, and `A ≤
N_G(X)` by `htX`, giving the conjugation action `MulDistribMulAction ↥A ↥X` via
`FT.Normalizes`/`FT.instConjDistributedMulAction`), `Ω = {H : Subgroup ↥X // Work.Hall.IsHall
(fun p => p ≠ q) H}`, and apply Glauberman's fixed-point lemma
`Work.Coprime.glauberman_exists_fixed ↥A ↥X Ω` (it needs `Nonempty Ω`, which is
`Work.Hall.exists_isHall ↥X` using `hsolv`; `Nat.card A` coprime to `Nat.card X`; the compatible
actions of `↥A` and `↥X` on `Ω` given by conjugation with
`Work.Hall.IsHall.conj_iff`/`Work.Hall.IsHall.map_mulAut`; and transitivity of the conjugation
action of `↥X` on `Ω`, which is `Work.Hall.isHall_conj`).  A fixed point `H` is a Hall `q'`-subgroup
of `↥X` invariant under `t`; take `R = H.map X.subtype` and convert the Hall condition on `↥X`
(`q ∤ Nat.card H`, `H.index` a power of `q`, using primality of `q`) to the stated conditions on `R`. -/
theorem appI5_hall_normalized {G : Type*} [Group G] [Finite G] {d : ℕ} {t : G} (ht : orderOf t = d)
    {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X) {q : ℕ} (hq : q.Prime) :
    ∃ R : Subgroup G, R ≤ X ∧ Work.NormalComplement.NormalizedBy t R ∧ ¬ q ∣ Nat.card R ∧
      ∃ k : ℕ, (R.subgroupOf X).index = q ^ k := by
  classical
  -- The cyclic operator `A = ⟨t⟩` normalizes `X`, so it acts by conjugation on `↥X`.
  haveI hNA : FT.Normalizes (Subgroup.zpowers t) X :=
    ⟨by rw [Subgroup.zpowers_le]; exact mem_normalizer_of_normalizedBy htX⟩
  -- `|A| = orderOf t = d` is coprime to `|X|`.
  have hcop : (Nat.card ↥(Subgroup.zpowers t)).Coprime (Nat.card ↥X) := by
    rw [Nat.card_zpowers, ht]; exact hdX.symm
  -- The `↥X`-set of Hall `q'`-subgroups of `X`, with the (compatible) actions of `↥X` and `↥A`.
  let Ω := HallSub (fun p : ℕ => p ≠ q) ↥X
  letI : MulAction (MulAut ↥X) Ω := hallSubMulAction (fun p : ℕ => p ≠ q) (MulAut ↥X) ↥X
  letI : MulAction ↥X Ω := MulAction.compHom Ω (MulAut.conj : ↥X →* MulAut ↥X)
  letI : MulAction ↥(Subgroup.zpowers t) Ω :=
    MulAction.compHom Ω (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X)
  -- The two actions are compatible.
  have hcomp : ∀ (a : ↥(Subgroup.zpowers t)) (g : ↥X) (ω : Ω),
      a • (g • ω) = (a • g) • (a • ω) := by
    intro a g ω
    have hkey := mulAut_conj_smul_compat a g
    show (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a) • ((MulAut.conj g) • ω) =
      (MulAut.conj (a • g)) • ((MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a) • ω)
    calc (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a) • ((MulAut.conj g) • ω)
        = (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a * MulAut.conj g) • ω :=
          (mul_smul _ _ _).symm
      _ = (MulAut.conj (a • g) *
            MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a) • ω := by rw [hkey]
      _ = (MulAut.conj (a • g)) •
            ((MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a) • ω) := mul_smul _ _ _
  -- `↥X` acts transitively on `Ω` (Hall's conjugacy theorem, `C_π`).
  have htrans : ∀ ω ω' : Ω, ∃ g : ↥X, g • ω = ω' := by
    intro ω ω'
    obtain ⟨g, hg⟩ := Work.Hall.isHall_conj ω.2 ω'.2
    exact ⟨g, Subtype.ext hg.symm⟩
  haveI : Nonempty Ω := by
    obtain ⟨H, hH⟩ := Work.Hall.exists_isHall ↥X (fun p : ℕ => p ≠ q)
    exact ⟨⟨H, hH⟩⟩
  haveI : Finite Ω :=
    Finite.of_injective (fun H : Ω => (H.1 : Set ↥X))
      (fun a b h => Subtype.ext (SetLike.coe_injective h))
  -- Glauberman's fixed point lemma: a `t`-invariant Hall `q'`-subgroup of `X`.
  obtain ⟨ω, hω⟩ := Work.Coprime.glauberman_exists_fixed ↥(Subgroup.zpowers t) ↥X Ω hcop
    (Or.inr hsolv) hcomp htrans
  -- The element of `⟨t⟩` corresponding to `t`.
  let a₀ : ↥(Subgroup.zpowers t) := ⟨t, Subgroup.mem_zpowers t⟩
  -- The automorphism of `X` given by `a₀` (conjugation by `t`) fixes the fixed point.
  have hfix : (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) • ω.1 = ω.1 :=
    congrArg Subtype.val (hω a₀)
  refine ⟨ω.1.map X.subtype, Subgroup.map_subtype_le ω.1, ?_, ?_, ?_⟩
  · -- `R` is normalized by `t`
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) h ∈ ω.1 := by
      have hthis : (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) h
          ∈ (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) • ω.1 :=
        Subgroup.smul_mem_pointwise_smul (G := ↥X) h
          (MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) ω.1 hh
      rw [hfix] at hthis
      exact hthis
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    show ((MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) h : G)
      = t * (h : G) * t⁻¹
    have hcoe : ((MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a₀) h : ↥X)
        = a₀ • h := rfl
    rw [hcoe, FT.conj_smul_coe]
  · -- `q ∤ |R|`
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact fun hdvd => (ω.2).1 q hq hdvd rfl
  · -- `|X : R|` is a power of `q`
    have hidx : ((ω.1.map X.subtype).subgroupOf X).index = ω.1.index := by
      have h : (ω.1.map X.subtype).subgroupOf X = ω.1 := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective ω.1
      rw [h]
    obtain ⟨k, hk⟩ : ∃ k, ω.1.index = q ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
        (fun {d} hd hdvd => not_not.mp ((ω.2).2 d hd hdvd))⟩
    exact ⟨k, by rw [hidx, hk]⟩

end Work.NormalComplement
