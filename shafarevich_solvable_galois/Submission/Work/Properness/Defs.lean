/-
Copyright (c) 2025. All rights reserved.

# Solutions of an embedding problem with abelian kernel: the abstract setting

This chapter formalises the algebraic part of Propositions 10–11 and of steps 1–4 of Theorem 15 of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211,

namely the structure theory of the *solutions* of an embedding problem with **abelian kernel**:

* the set of solutions is a torsor under `Z¹(H, A)`;
* `H¹(H, A)` classifies the solutions up to conjugation by the kernel `A`;
* and — the only logical step of the paper's argument — a solution is *proper* (surjective) as
  soon as the images of the decomposition groups of sufficiently many completely split primes
  generate the kernel.

## The dictionary with the paper

In the paper, `k` is a global field and one is given a finite Galois extension `K/k` with group
`G`, a finite `G`-module `A` (in Proposition 11, `A = 𝔽_p[G]^n`, an induced module), and a solution
of an embedding problem is a homomorphism

`ψ : G_k →* E`,  `π ∘ ψ = ρ`,

where `E` is an extension of `G` by `A`, `π : E ↠ G = E/A` is the quotient map and
`ρ : G_k ↠ G` is (the solution constructed in the previous induction step, in the case of
Proposition 11 the restriction map `G_k ↠ G(K/k)`).

In the present development the whole situation is abstracted to

* `S.H` — the big Galois group (`G_k`),
* `S.E` — the group to be embedded (`E`), with a normal abelian subgroup `S.A = ker π` (the
  kernel `A` of the embedding problem),
* `S.Q = E/A` — the quotient, with `π : S.E →* S.Q` the quotient map,
* `S.ρ : S.H →* S.Q` — the surjection along which we lift (`G_k ↠ G`),
* `S.HK = ker ρ` — the "absolute Galois group of the field cut out by `ρ`" (`G_K`).

A **lift** (or *solution*) of the embedding problem is a homomorphism `ψ : S.H →* S.E` with
`π ∘ ψ = ρ`; for `h ∈ H_K` we have `ψ h ∈ A`. A lift is **proper** if it is surjective — this is
the paper's notion of a *proper solution* ("eigentliche Lösung"): since `π ∘ ψ = ρ` is onto, `ψ` is
onto if and only if `ψ(H_K) = A`.

## Main declarations

* `Work.Properness.Setup` — the abstract setting (`H`, `E`, `Q`, `π`, `ρ`, abelian kernel);
* `Setup.A`, `Setup.HK`, `Setup.IsLift`, `Setup.Lift`, `Setup.liftValue`, `Setup.map_HK_le_A`;
* `Setup.conjAction` — the canonical conjugation action of `H` on the kernel `A` (it factors
  through `ρ` and does not depend on any choice);
* `Setup.twist`, `Setup.twistedAction` — the twisted action of `H` on `A` attached to a
  homomorphism `ψ₀ : H →* E`; for a *lift* it agrees with `Setup.conjAction`;
* `Setup.IsProper`, `Setup.HasLift`, `Setup.HasProperLift`;
* `Setup.mulFun` — the pointwise product `h ↦ x h * ψ h` of a `1`-cochain with a homomorphism, the
  raw material of the torsor structure (`θ = x · ψ₀` of Proposition 11);
* `Setup.liftOfCocycleFun`, `Setup.cocycleOfLiftFun`, `Setup.d0Z1`;
* `Setup.IsCompatibleLocal`, `Setup.GrunwaldWangDatum`, `Setup.ScholzGrunwaldWangInput` — the
  arithmetic input (Grunwald–Wang) as a named hypothesis.

## What is *not* here

The arithmetic content of the paper — the existence of completely split primes with prescribed
local behaviour (the Grunwald–Wang theorem, together with Čebotarev's density theorem used in
Theorem 13) — is *not* available in this development and is taken as the named hypothesis
`Setup.ScholzGrunwaldWangInput` (see `Work.Properness.ScholzGrunwaldWang`).  Everything else in
this chapter is unconditional.
-/
import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.AbsoluteGalois.Cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

universe u v w

set_option warn.classDefReducibility false
set_option linter.checkUnivs false

open scoped Classical
open Work.AbsoluteGalois (conjKernelMul conjKernelMul_one conjKernelMul_mul conjKernelMul_mul_eq
  conjKernelMul_one_left conjKernelMul_of_mem_ker kernelAction)

noncomputable section

/-- **The abstract setting of an embedding problem with abelian kernel.**

* `H` — the "big" group (in the applications `H = G_k`, the absolute Galois group of a global
  field `k`);
* `E` — the group to be embedded, with a normal abelian subgroup `A = ker π`;
* `Q = E/A` — the quotient group;
* `π : E →* Q` — the quotient map (surjective by construction);
* `ρ : H →* Q` — a surjective homomorphism along which the embedding problem is solved; in the
  applications `ρ` is the restriction map `G_k ↠ G(K/k)` (Proposition 11) or, more generally, the
  solution already constructed on a lower level (Theorem 15);
* `ker_comm` — the kernel `A = ker π` is abelian. -/
structure Setup where
  H : Type u
  E : Type v
  Q : Type w
  [groupH : Group H]
  [groupE : Group E]
  [groupQ : Group Q]
  /-- the quotient map `E →* Q = E/A` -/
  π : E →* Q
  /-- the quotient map is surjective -/
  π_surj : Function.Surjective π
  /-- the restriction map `H ↠ Q` that is to be lifted -/
  ρ : H →* Q
  /-- the restriction map is surjective -/
  ρ_surj : Function.Surjective ρ
  /-- the kernel of `π` is abelian -/
  ker_comm : ∀ a b : π.ker, a * b = b * a

attribute [instance] Setup.groupH Setup.groupE Setup.groupQ

namespace Setup

variable (S : Setup.{u, v, w})

/-- The abelian kernel `A = ker π`, a normal subgroup of `E`; the exact sequence
`1 → A → E → Q → 1` is the embedding problem. -/
abbrev A : Subgroup S.E := S.π.ker

instance instCommGroupA : CommGroup S.A :=
  { (inferInstance : Group S.A) with mul_comm := S.ker_comm }

/-- `H_K = ker ρ`: the subgroup of `H` that fixes the field cut out by `ρ` (in the applications
`H_K = G_K`).  In the paper's Proposition 11, the decomposition groups of the primes that split
completely in `K` are subgroups of `H_K`; this is the hypothesis `hT` of the properness
criterion. -/
abbrev HK : Subgroup S.H := S.ρ.ker

/-! ## Lifts (solutions) -/

/-- A homomorphism `ψ : H →* E` is a **lift** (solution) of the embedding problem if
`π ∘ ψ = ρ`. -/
def IsLift (ψ : S.H →* S.E) : Prop := S.π.comp ψ = S.ρ

/-- The type of lifts (solutions) of the embedding problem.  It is a torsor under `Z¹(H, A)`
(`Work.Properness.Torsor`), not a group. -/
def Lift : Type _ := { ψ : S.H →* S.E // S.IsLift ψ }

namespace Lift

instance : Coe S.Lift (S.H →* S.E) := ⟨Subtype.val⟩
instance : CoeFun S.Lift (fun _ => S.H → S.E) := ⟨fun ψ => ψ.1⟩

@[simp] theorem coe_mk (ψ : S.H →* S.E) (h : S.IsLift ψ) :
    ((⟨ψ, h⟩ : S.Lift) : S.H →* S.E) = ψ := rfl

theorem ext {ψ φ : S.Lift} (h : ∀ x, (ψ : S.H → S.E) x = (φ : S.H → S.E) x) : ψ = φ :=
  Subtype.ext (MonoidHom.ext h)

/-- Two lifts have the same underlying homomorphism iff they are equal. -/
@[ext] theorem ext_hom {ψ φ : S.Lift} (h : (ψ : S.H →* S.E) = φ.1) : ψ = φ := Subtype.ext h

end Lift

/-- For a lift `ψ₀` and `h ∈ H_K`, the element `ψ₀ h ∈ E` lies in the kernel `A = ker π`. -/
def liftValue (ψ₀ : S.Lift) (h : S.HK) : S.A :=
  ⟨ψ₀.1 (h : S.H), by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, ψ₀.2]
    exact h.2⟩

@[simp] theorem coe_liftValue (ψ₀ : S.Lift) (h : S.HK) :
    ((S.liftValue ψ₀ h : S.A) : S.E) = ψ₀.1 h := rfl

/-- **A lift maps `H_K` into the kernel**: `ψ(H_K) ≤ A`.  (Immediate from `π ∘ ψ = ρ`.) -/
theorem map_HK_le_A (ψ₀ : S.Lift) : S.HK.map ψ₀.1 ≤ S.A := by
  rintro x ⟨y, hy, rfl⟩
  exact (S.liftValue ψ₀ ⟨y, hy⟩).2

/-! ## The conjugation action of `H` on the kernel

The set of *all* homomorphisms `H →* E` of the shape `h ↦ (something in A) · ψ h` is governed by
the action of `H` on `A` obtained by conjugating inside `E` with a chosen homomorphism `ψ₀`.  This
action automatically factors through `ρ` and is independent of the choice of `ψ₀` (because
conjugation by an element of the abelian kernel is trivial), so we can — and do — define it once,
canonically.
-/

/-- A chosen preimage of `q : Q` under `π : E ↠ Q`. -/
noncomputable def pickSection (q : S.Q) : S.E := Classical.choose (S.π_surj q)

theorem pickSection_spec (q : S.Q) : S.π (S.pickSection q) = q :=
  Classical.choose_spec (S.π_surj q)

/-- The *normalized* section of `π`: `pickSection` corrected so that `1 ↦ 1`. -/
noncomputable def normSection (q : S.Q) : S.E := S.pickSection q * (S.pickSection 1)⁻¹

theorem normSection_spec (q : S.Q) : S.π (S.normSection q) = q := by
  rw [normSection, map_mul, map_inv, pickSection_spec, pickSection_spec, inv_one, mul_one]

@[simp] theorem normSection_one : S.normSection 1 = 1 := by
  rw [normSection, mul_inv_cancel]

/-- The conjugation action of `Q = E/A` on the abelian kernel `A`: conjugation by a (normalized)
set-theoretic section of `π`.  It is well defined because conjugation by an element of the abelian
kernel is trivial. -/
noncomputable def qAction : DistribMulAction S.Q (Additive S.A) :=
  kernelAction S.π S.normSection S.normSection_spec S.normSection_one S.ker_comm

/-- **The canonical action of `H` on the kernel `A`.**  It is the conjugation action of `Q`
pulled back along `ρ`; in particular it factors through `ρ` and does not depend on any section or
lift.  This is the action with respect to which the cocycles `Z¹(H, A)` of the torsor structure
below are taken. -/
noncomputable def conjAction : DistribMulAction S.H (Additive S.A) :=
  letI := S.qAction
  DistribMulAction.compHom (Additive S.A) S.ρ

instance instDistribMulAction : DistribMulAction S.H (Additive S.A) := S.conjAction

/-- **The canonical action of `H` on `A` factors through `ρ`**: elements of `H_K = ker ρ` act
trivially.  (Immediate from `Setup.conjAction` being the conjugation action of `Q = E/A` pulled
back along `ρ`.) -/
theorem smul_eq_self_of_mem_HK (h : S.HK) (a : Additive S.A) : (h : S.H) • a = a := by
  have hh : S.ρ (h : S.H) = 1 := h.2
  letI : DistribMulAction S.Q (Additive S.A) := S.qAction
  change (S.ρ (h : S.H)) • a = a
  rw [hh, one_smul]

/-- The action of `h : H` on `a : A` induced by a *homomorphism* `ψ₀ : H →* E` (typically a
lift), written out explicitly: conjugation by `ψ₀ h` inside `E`.  Its elementary properties are
`Setup.twistedAction`; when `ψ₀` is a lift it agrees with the canonical action
(`Setup.twist_eq_smul_of_isLift`). -/
def twist (ψ₀ : S.H →* S.E) (h : S.H) (a : Additive S.A) : Additive S.A :=
  Additive.ofMul (conjKernelMul S.π (ψ₀ h) a.toMul)

/-- **The twisted action attached to `ψ₀` is an action.** -/
def twistedAction (ψ₀ : S.H →* S.E) : DistribMulAction S.H (Additive S.A) where
  smul := S.twist ψ₀
  one_smul a := by
    show S.twist ψ₀ 1 a = a
    simp only [twist, map_one, conjKernelMul_one_left, ofMul_toMul]
  mul_smul g h a := by
    show S.twist ψ₀ (g * h) a = S.twist ψ₀ g (S.twist ψ₀ h a)
    simp only [twist, map_mul, conjKernelMul_mul_eq, toMul_ofMul]
  smul_zero h := by
    show S.twist ψ₀ h 0 = 0
    simp only [twist, toMul_zero, conjKernelMul_one, ofMul_one]
  smul_add h a b := by
    show S.twist ψ₀ h (a + b) = S.twist ψ₀ h a + S.twist ψ₀ h b
    simp only [twist, toMul_add, conjKernelMul_mul, ofMul_mul]

/-! ## Properness -/

/-- A lift (solution) is **proper** if it is surjective.  Since `π ∘ ψ = ρ` and `ρ` is surjective,
this is equivalent to `ψ(H_K) = A` (`Setup.isProper_iff_map_HK_eq_A`): the paper's "proper
solution". -/
def IsProper (ψ : S.Lift) : Prop := Function.Surjective ψ.1

/-- The embedding problem has a (plain) solution: a lift of `ρ` exists.  This is the classical
"the obstruction class vanishes" condition (Ikeda/Hoechsmann). -/
def HasLift : Prop := Nonempty S.Lift

/-- The embedding problem has a **proper** solution: equivalently `EmbeddingProblem.IsSolvable`,
equivalently `Work.AbsoluteGalois.HasSurjectiveLift`.  This is strictly stronger than
`Setup.HasLift` (`Work.Properness.NoProperExample`). -/
def HasProperLift : Prop := ∃ ψ : S.Lift, S.IsProper ψ

/-! ## The `Z¹`-torsor structure: raw material

`Setup.mulFun x ψ` is the pointwise product `h ↦ x h * ψ h` in `E`.  For `x ∈ Z¹(H, A)` and a lift
`ψ` it is again a lift (`Work.Properness.Torsor.exists_mulFun_isLift`); this is Proposition 11's
`θ = x · ψ₀`.  Likewise `Setup.cocycleOfLiftFun ψ₀ ψ` is the difference of two lifts, which is a
`1`-cocycle (`Work.Properness.Torsor.cocycleOfLiftFun_mem_Z1`).
-/

/-- The pointwise product `h ↦ x h * ψ h` of a cochain `x : H → A` with a homomorphism
`ψ : H →* E`.  (Uses the canonical action `Setup.conjAction` for the cocycle condition, so this is
where `x` is a cocycle for the twisted action.) -/
def mulFun (x : S.H → Additive S.A) (ψ : S.H →* S.E) : S.H → S.E :=
  fun h => (((x h).toMul : S.A) : S.E) * ψ h

/-- `θ = x · ψ₀` of Proposition 11: the lift attached to a `1`-cocycle `x` and a homomorphism
`ψ₀`. -/
def liftOfCocycleFun (x : S.H → Additive S.A) (ψ₀ : S.Lift) : S.H → S.E :=
  S.mulFun x ψ₀.1

/-- The difference `h ↦ ψ h * (ψ₀ h)⁻¹ ∈ A` of two lifts. -/
def cocycleOfLiftFun (ψ₀ ψ : S.Lift) : S.H → Additive S.A :=
  fun h => Additive.ofMul
    ⟨ψ.1 h * (ψ₀.1 h)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, ψ.2,
        ← MonoidHom.comp_apply, ψ₀.2, mul_inv_cancel]⟩

/-- The `1`-coboundary `d⁰ a`, as an element of `Z¹(H, A)`. -/
def d0Z1 (a : Additive S.A) : GroupCohomology.Z1 S.H (Additive S.A) :=
  ⟨GroupCohomology.d0 S.H (Additive S.A) a,
    GroupCohomology.d0_mem_Z1 S.H (Additive S.A) a⟩

@[simp] theorem d0Z1_apply (a : Additive S.A) (h : S.H) :
    (S.d0Z1 a).1 h = h • a - a := rfl

/-! ## The arithmetic input: Grunwald–Wang -/

/-- **Compatibility of a family of local conditions.**  If two of the subgroups `T i` overlap, the
prescribed differences of Proposition 11 must agree on the overlap.  In the arithmetic situation
this is automatic (the local conditions are indexed by primes, and the local classes live in
different local groups unless the decomposition subgroups coincide, in which case the restriction
maps coincide as well). -/
def IsCompatibleLocal {ι : Type*} (ψ₀ : S.Lift) (T : ι → Subgroup S.H)
    (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A) : Prop :=
  ∀ (i j : ι) (t : S.H) (hi : t ∈ T i) (hj : t ∈ T j),
    φ i ⟨t, hi⟩ * (S.liftValue ψ₀ ⟨t, hT i hi⟩)⁻¹
      = φ j ⟨t, hj⟩ * (S.liftValue ψ₀ ⟨t, hT j hj⟩)⁻¹

/-- **The Grunwald–Wang data of Proposition 11.**  Given a lift `ψ₀`, subgroups `T i ≤ H_K`
(the decomposition groups of primes that split completely, transported into `H_K`) and
homomorphisms `φ i : T i →* A` (the prescribed local behaviour), this is the assertion that the
local conditions are simultaneously realized: a global `1`-cocycle `x ∈ Z¹(H, A)` whose
restrictions to `T i` are the prescribed differences `φ i - ψ₀|_{T i}`:

`x(t) = φ i t · (ψ₀ t)⁻¹`  for all `t ∈ T i`.

The *arithmetic* input of the paper is exactly that this datum always exists in the global-field
situation (surjectivity of `∏_i H¹(k_{p_i}, A) → H¹(k, A)`, the Grunwald–Wang theorem). -/
def GrunwaldWangDatum {ι : Type*} (ψ₀ : S.Lift) (T : ι → Subgroup S.H)
    (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A) : Prop :=
  ∃ x : GroupCohomology.Z1 S.H (Additive S.A),
    ∀ (i : ι) (t : T i),
      (x.1 (t : S.H)).toMul = φ i t * (S.liftValue ψ₀ ⟨(t : S.H), hT i t.2⟩)⁻¹

/-- **The named arithmetic hypothesis: Scholz–Grunwald–Wang.**  The arithmetic input of
Proposition 11, stated at the given local data: the compatible local conditions `φ i` on the
subgroups `T i ≤ H_K` are realized *globally*, i.e. there is a global `1`-cocycle
`x ∈ Z¹(H, A)` with

`x t = φ i t · (ψ₀ t)⁻¹`  for all `t ∈ T i`

(equivalently, the prescribed differences `φ i - ψ₀|_{T i}` are the restrictions of a global
class — the conclusion of the Grunwald–Wang theorem in the paper).

`S.IsCompatibleLocal ψ₀ T hT φ` is the necessary compatibility of the prescriptions on overlaps; in
the arithmetic situation it holds automatically, and it is implied by the second conjunct.

**Status.**  This is a hypothesis, not a theorem of this development: it is the *arithmetic*
input, the surjectivity of the restriction map `∏_i H¹(k_{p_i}, A) → H¹(k, A)` for the completely
split primes `p_i` and the induced module `A = 𝔽_p[G]^n` (Grunwald–Wang, together with the
existence of completely split primes with prescribed local behaviour).  No attempt to prove it is
made here.

**Warning.**  The *universal* form of this assertion — "for every abstract configuration `S` and
every compatible family the datum holds" — is **false**, and must not be used.  Two reasons:

* abstractly: any restriction map `H¹(H, A) → H¹(T, A)` for a subgroup `T ≤ H` can fail to be
  onto (e.g. `H = C₄`, `A = ℤ/2` with trivial action, `T = ⟨σ²⟩`: the prescribed value on `σ²`
  need not be hit, since every homomorphism `C₄ → ℤ/2` kills `σ²`);
* arithmetically: for `H = G_ℚ` and `A` a nontrivial `Gal(L/ℚ)`-module, `H¹(ℚ, A)` is a *finite*
  group while `H¹(T, A)` for a subgroup `T ≤ G_L` can be infinite (Kummer theory), so no
  restriction map from `H¹(ℚ, A)` can be onto.

What is true is the statement for the local data attached to the *primes* `p_i` (decomposition
groups, with the identifications `G_{k_{p_i}} ≅ T i`), and that is exactly this hypothesis at the
data that arise.  See `Submission/Work/Properness/NOTES.md` §4. -/
def ScholzGrunwaldWangInput {ι : Type*} (ψ₀ : S.Lift) (T : ι → Subgroup S.H)
    (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A) : Prop :=
  S.IsCompatibleLocal ψ₀ T hT φ ∧ S.GrunwaldWangDatum ψ₀ T hT φ

end Setup

open Setup in
/-- **The trivial counterexample to "a lift is proper".**  The abstract setting with
`H = Q = 1` (the trivial group), `E = ℤ/2` and `π`, `ρ` the trivial maps.  The embedding problem
`1 → ℤ/2 → ℤ/2 → 1 → 1` has a lift (the trivial homomorphism, hence `Setup.HasLift`), but no
surjective one: every homomorphism from the trivial group into `ℤ/2` is trivial, so no lift is
proper.  This is the abstract instance of "a split embedding problem has a plain solution for
free — the section — but properness is strictly stronger".

See `Work.Properness.trivialSetup_hasLift` and `Work.Properness.trivialSetup_no_properLift` in
`Submission/Work/Properness/Example.lean`. -/
def trivialSetup : Setup where
  H := PUnit
  E := Multiplicative (ZMod 2)
  Q := PUnit
  π := 1
  π_surj := fun q => ⟨1, Subsingleton.elim _ q⟩
  ρ := 1
  ρ_surj := fun q => ⟨1, Subsingleton.elim _ q⟩
  ker_comm := fun a b => mul_comm a b



end

end Work.Properness
