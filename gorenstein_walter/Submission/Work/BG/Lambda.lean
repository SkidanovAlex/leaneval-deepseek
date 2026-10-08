import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lemma13

/-!
# Area BG: the group `Λ` of Bender–Glauberman 1981, Hypothesis 1.2

For a Hypotheses-1.2 configuration (`Work.BG.Hyp12`) with `H₀/U` **abelian** (in the paper's
application `H₀/U ≅ S₀` is cyclic), Bender–Glauberman's `Λ` is the group of all linear
characters of `H₀/U`, regarded as class functions on `H₀` by inflation.  `Λ` acts on
`Irr(H₀)` by multiplication, and `r(Λ) := ∑_{λ ∈ Λ} λ` is the regular character of `H₀/U`.

This module provides

* `Work.BG.quotGroup`, `Work.BG.quotMk` — the quotient `H₀/U` and its projection;
* `Work.BG.Lambda` — the set `Λ` of class functions on `↥H₀`;
* `Work.BG.lambdaSum` — `r(Λ) = ∑_{λ ∈ Λ} λ`;
* `Work.BG.lambdaSum_apply_eq_zero_of_not_mem_U` — **Lemma 1.7(i)**: `r(Λ)` vanishes on
  `T = H₀ ∖ U` (indeed on all of `H₀ ∖ U`), an instantiation of the Feit–Thompson
  closure's `sum_linearClassFunction_apply_eq_zero_of_not_mem_normal`;
* `Work.BG.Lambda.apply_eq_one_of_mem_U` — every `λ ∈ Λ` is trivial on `U`.

The orbit theory of §2 (the `Λ`-orbits of `Irr(H₀)`, the numbers `|Λ_ν|`, Lemma 2.1, and
the coherence theorem) is designed in `NOTES_BG.md` but not yet formalised.
-/

namespace Work.BG

open Subgroup
open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

/-- `H₀/U`: the quotient of Hypothesis 1.2 by `U` (as a quotient group of `↥H₀`). -/
abbrev quotGroup (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal] : Type :=
  ↥P.H0 ⧸ P.U.subgroupOf P.H0

/-- The projection `↥H₀ → H₀/U`. -/
abbrev quotMk (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal] :
    ↥P.H0 →* quotGroup P :=
  QuotientGroup.mk' (P.U.subgroupOf P.H0)

/-- **Bender–Glauberman's `Λ`** (Hypothesis 1.2): the set of linear characters of `H₀/U`,
inflated to class functions on `H₀`. -/
def Lambda (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal] :
    Set (ClassFunction ↥P.H0 ℂ) :=
  {δ | ∃ β : quotGroup P →* ℂˣ,
      δ = ClassFunction.compHom (quotMk P) (linearClassFunction β)}

/-- The sum of all elements of `Λ`, i.e. the regular character of `H₀/U` inflated to `H₀`;
Bender–Glauberman's `r(Λ)`.  Requires `Fintype` for the (finite) type of homomorphisms
`H₀/U →* ℂˣ`, which is provided by `Fintype ((H₀/U) →* ℂˣ)` as an explicit hypothesis. -/
noncomputable def lambdaSum (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype (quotGroup P →* ℂˣ)] : ClassFunction ↥P.H0 ℂ :=
  ∑ β : quotGroup P →* ℂˣ, ClassFunction.compHom (quotMk P) (linearClassFunction β)

/-- **Bender–Glauberman 1981, Lemma 1.7(i).**  The regular character `r(Λ)` of `H₀/U`
vanishes on `H₀ ∖ U`, hence on `T = H₀ ∖ U`. -/
theorem lambdaSum_apply_eq_zero_of_not_mem_U (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Invertible (Nat.card ↥(P.U.subgroupOf P.H0) : ℂ)]
    [Fintype (quotGroup P →* ℂˣ)]
    (habel : ∀ x y : ↥P.H0, ⁅x, y⁆ ∈ P.U.subgroupOf P.H0)
    {g : ↥P.H0} (hg : g ∉ P.U.subgroupOf P.H0) :
    lambdaSum P g = 0 :=
  sum_linearClassFunction_apply_eq_zero_of_not_mem_normal (H := P.U.subgroupOf P.H0) habel hg

/-- The `Λ`-orbit sum `∑_{λ ∈ Λ} λ·ν` of a class function `ν` of `H₀`.  `Λ` is finite
because it is the dual of the finite group `H₀/U`.

**Careful:** this is *not* `r(Λν)` in the sense of Bender–Glauberman 1981 — the map
`β ↦ Inf(β)·ν` is injective only when the stabiliser `Λ_ν = {λ : λν = ν}` is trivial
(a non-trivial stabiliser occurs as soon as `ν` vanishes on the support of a non-trivial
`λ`, e.g. for the 3-dimensional character of `A₄ = H₀` with `U = 1`).  The paper's
normalised orbit sum is `|Λ_ν|⁻¹ r(Λ)ν`; in the applications of §2 the stabilisers are
trivial (e.g. `H₀ = S × B`, `Λ = {1, λ₂}`: `(λ₂μ)(s) = -μ(s) ≠ μ(s)`), and then the two
agree.  Statements that need the orbit sum with each element counted once therefore carry
the freeness hypothesis `Function.Injective (fun β => Inf(β) * ν)` (see
`Submission/Work/BG/lemma17_ii.lean`). -/
noncomputable def lambdaOrbitSum (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype (quotGroup P →* ℂˣ)] (δ : ClassFunction ↥P.H0 ℂ) : ClassFunction ↥P.H0 ℂ :=
  ∑ β : quotGroup P →* ℂˣ,
    ClassFunction.compHom (quotMk P) (linearClassFunction β) * δ

/-- `r(Λν) = r(Λ)·ν`. -/
theorem lambdaOrbitSum_eq_mul (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype (quotGroup P →* ℂˣ)] (δ : ClassFunction ↥P.H0 ℂ) :
    lambdaOrbitSum P δ = lambdaSum P * δ := by
  ext g
  simp only [lambdaOrbitSum, lambdaSum, ClassFunction.mul_apply, ClassFunction.sum_apply]
  rw [Finset.sum_mul]

/-- **Bender–Glauberman 1981, Lemma 1.7(i), orbit form.**  Every orbit sum `r(Λν)`
vanishes on `H₀ ∖ U`, hence on `T`. -/
theorem lambdaOrbitSum_apply_eq_zero_of_not_mem_U (P : Hyp12 G)
    [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Invertible (Nat.card ↥(P.U.subgroupOf P.H0) : ℂ)]
    [Fintype (quotGroup P →* ℂˣ)]
    (habel : ∀ x y : ↥P.H0, ⁅x, y⁆ ∈ P.U.subgroupOf P.H0)
    (δ : ClassFunction ↥P.H0 ℂ) {g : ↥P.H0} (hg : g ∉ P.U.subgroupOf P.H0) :
    lambdaOrbitSum P δ g = 0 := by
  rw [lambdaOrbitSum_eq_mul, ClassFunction.mul_apply,
    lambdaSum_apply_eq_zero_of_not_mem_U P habel hg, zero_mul]

/-- The value of the regular character `r(Λ)` on `U`: every element of `Λ` is trivial on
`U`, so `r(Λ)(u) = |Λ|` for `u ∈ U`.  (When `H₀/U` is abelian, `|Λ| = |H₀/U|`, which is
the paper's "the regular character of `H₀/U` is `[H₀:U]` on `U` and `0` off `U`".) -/
theorem lambdaSum_apply_eq_card_of_mem_U (P : Hyp12 G) [hUn : (P.U.subgroupOf P.H0).Normal]
    [Fintype (quotGroup P →* ℂˣ)] {u : ↥P.H0} (hu : u ∈ P.U.subgroupOf P.H0) :
    lambdaSum P u = (Fintype.card (quotGroup P →* ℂˣ) : ℂ) := by
  classical
  have h1 : ∀ β : quotGroup P →* ℂˣ,
      ClassFunction.compHom (quotMk P) (linearClassFunction β) u = 1 := by
    intro β
    have hq : quotMk P u = 1 :=
      (QuotientGroup.eq_one_iff (N := P.U.subgroupOf P.H0) u).mpr hu
    rw [ClassFunction.compHom_apply, linearClassFunction_apply, hq, map_one]
    rfl
  have hsum : (∑ β : quotGroup P →* ℂˣ,
        ClassFunction.compHom (quotMk P) (linearClassFunction β) u) =
      ∑ _β : quotGroup P →* ℂˣ, (1 : ℂ) :=
    Finset.sum_congr rfl fun β _ => h1 β
  rw [lambdaSum, ClassFunction.sum_apply, hsum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- **The reflection character on `T`** (Bender–Glauberman's proof remark for Lemma
1.7(iii): "λ₁ is `-1` on `T`").  If `[H₀ : U] = 2` — so that the group `H₀/U` has order two
and every non-trivial linear character `β` of it has trivial kernel — then every element
`t ∈ H₀ ∖ U` of order `2` is sent to `-1` by the inflation of `β`. -/
theorem lambda_apply_eq_neg_one_of_card_two (P : Hyp12 G)
    [hUn : (P.U.subgroupOf P.H0).Normal] (h2 : Nat.card (quotGroup P) = 2)
    {β : quotGroup P →* ℂˣ} (hβ : β ≠ 1) {t : ↥P.H0} (ht : t ^ 2 = 1)
    (htU : t ∉ P.U.subgroupOf P.H0) :
    ClassFunction.compHom (quotMk P) (linearClassFunction β) t = -1 := by
  have hker : β (quotMk P t) ≠ 1 := by
    intro h
    have hmem : quotMk P t ∈ MonoidHom.ker β := h
    haveI : Fact (Nat.card (quotGroup P)).Prime := ⟨h2 ▸ Nat.prime_two⟩
    rcases (MonoidHom.ker β).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · rw [hbot] at hmem
      exact htU (by simpa using hmem)
    · exact absurd (MonoidHom.ker_eq_top_iff.mp htop) hβ
  have hsq : β (quotMk P t) ^ 2 = 1 := by
    rw [← map_pow, show quotMk P t ^ 2 = 1 from by rw [← map_pow, ht, map_one],
      map_one]
  have hC : ((β (quotMk P t) : ℂˣ) : ℂ) = -1 := by
    have h2' : (((β (quotMk P t) : ℂˣ) : ℂ)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq]; rfl
    have hfac : (((β (quotMk P t) : ℂˣ) : ℂ) - 1) * (((β (quotMk P t) : ℂˣ) : ℂ) + 1) = 0 := by
      linear_combination h2'
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) (fun hh => hker (Units.ext hh))
    · exact add_eq_zero_iff_eq_neg.mp h
  rw [ClassFunction.compHom_apply, linearClassFunction_apply]
  exact hC

namespace Lambda

variable {P : Hyp12 G} [hUn : (P.U.subgroupOf P.H0).Normal]

/-- A class function of `H₀` lies in `Λ` iff it is the inflation of a homomorphism
`H₀/U →* ℂˣ`. -/
theorem mem_iff {δ : ClassFunction ↥P.H0 ℂ} :
    δ ∈ Lambda P ↔ ∃ β : quotGroup P →* ℂˣ,
      δ = ClassFunction.compHom (quotMk P) (linearClassFunction β) := Iff.rfl

/-- Members of `Λ` are constant on conjugacy classes with value a root of unity; in
particular every `λ ∈ Λ` is trivial on `U`. -/
theorem apply_eq_one_of_mem_U {δ : ClassFunction ↥P.H0 ℂ} (hδ : δ ∈ Lambda P)
    {u : ↥P.H0} (hu : u ∈ P.U.subgroupOf P.H0) : δ u = 1 := by
  obtain ⟨β, rfl⟩ := hδ
  rw [ClassFunction.compHom_apply, linearClassFunction_apply]
      -- `β (quotMk P u) = 1` because `quotMk P u = 1`
  have h1 : quotMk P u = 1 := (QuotientGroup.eq_one_iff (N := P.U.subgroupOf P.H0) u).mpr hu
  rw [h1, map_one]
  rfl

end Lambda

end Work.BG
