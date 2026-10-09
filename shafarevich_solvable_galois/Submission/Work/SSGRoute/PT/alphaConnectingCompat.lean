import Mathlib
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.AbsoluteKummer.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The evaluation cup `Hom_ℤ(N,C) × N → C` and its Leibniz rule (the connecting-map compatibility)

Milne, *Arithmetic Duality Theorems*, Theorem I.1.8, is proved by the five-lemma dévissage along
`0 → M → M* → M₁ → 0` (`M* = Hom(ℤ[G/U], M)`, `U` open normal acting trivially on `M`).  The two
*first* squares of his diagram (1.9.1) are the naturality of `α^r` in the coefficient module
(`PT/alphaTwo_naturality.lean`); the **third** square

    Ext^r_G(M,C) --δ--> Ext^{r+1}_G(M₁,C)
       ↓α^r(G,M)           ↓α^{r+1}(G,M₁)
    H^{2-r}(G,M)^∨ --δ^∨--> H^{1-r}(G,M₁)^∨

is *not* a naturality square: the top map is the connecting map of the short exact sequence of
**coefficient** modules `0 → Hom(M₁,C) → Hom(M*,C) → Hom(M,C) → 0` (contravariant in `M`), and the
bottom map is the transpose of the connecting map of the short exact sequence of **modules**
`0 → M → M* → M₁ → 0`.  Its commutativity is the standard **Leibniz rule** for the cup product,

    δ(c ⌣ n) = (δc) ⌣ n − c ⌣ (δn),

i.e. the compatibility of the evaluation pairing `Hom_ℤ(M,C) × M → C` with the connecting maps.
`PT/AlphaTwoKummer.lean` names this verbatim as the missing commuting square of the dévissage.

This module proves that rule, in the coefficient model of `PT/AlphaPairing.lean`
(`ConjHom N C = Hom_ℤ(N,C)` with the conjugation action `(g • f)(n) = g • f (g⁻¹ • n)`) and in the
cochain conventions of `Work.AbsoluteKummer` / `Work.GroupCohomology`
(`d¹ f (g,h) = g • f h − f (g*h) + f g`):

* `cupConn10`, `cupConn20`, `cupConn11` — the evaluation cups in bidegrees `(1,0)`, `(2,0)`, `(1,1)`
  (`(c ⌣ n)(g) = c g (g • n)`, `(c ⌣ n)(g,h) = c (g,h) ((g*h) • n)`,
  `(c ⌣ b)(g,h) = c g (g • b h)`);
* `d1_cupConn10_eq` — **the Leibniz rule** `d¹(c ⌣ n) = (d¹c) ⌣ n − c ⌣ (d⁰n)`;
* `d1_cupConn10_eq_of_shortExact` — the same identity in the short-exact-sequence form that the
  third square of (1.9.1) consumes, with `c` a `1`-cocycle lifted along `M ↪ M*`, `n ∈ M*` a lift
  of an invariant element of `M₁ = M*/M`: the connecting cocycle `d¹c` evaluated at `n` differs
  from the cup `c ⌣ d⁰n` by the *explicit* coboundary `d¹(c ⌣ n)`; hence the two sides have the
  same class in `H²(G,C)`;
* `sub_mem_d1_range` / `sub_mem_B2_cupConn` — that statement in cohomological form;
* `cupConn11_mem_Z2` — the `(1,1)`-cup of two `1`-cocycles is a `2`-cocycle (so that the cup
  descends to `H¹ × H¹ → H²`, i.e. the map `α¹`: this is what makes the bottom row of (1.9.1) at
  `r = 1` meaningful);
* `cupConn11_of_d1_eq_zero` — the cup of a `1`-cocycle with a `1`-coboundary is a `2`-coboundary
  (the second half of the descent of `α¹`).

No arithmetic enters: everything here is the cochain algebra of the evaluation pairing.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Classical

namespace Work.SSGRoute.PT

universe u v w

/-! ## The evaluation cups -/

section CupDefs

variable {G : Type u} [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- The `(1,0)`-evaluation cup of a `1`-cochain `c` with values in `Hom_ℤ(N,C)` and an element
`n : N` (a `0`-cochain): the `1`-cochain `g ↦ c g (g • n)`. -/
def cupConn10 (c : G → ConjHom N C) (n : N) : G → C := fun g => c g (g • n)

/-- The `(2,0)`-evaluation cup: the `2`-cochain `(g,h) ↦ c (g,h) ((g*h) • n)`.  (Note the action on
the argument: this is the convention for which the Leibniz rule is an identity, cf.
`d1_cupConn10_eq`.) -/
def cupConn20 (c : G × G → ConjHom N C) (n : N) : G × G → C := fun p => c p ((p.1 * p.2) • n)

/-- The `(1,1)`-evaluation cup: the `2`-cochain `(g,h) ↦ c g (g • b h)`. -/
def cupConn11 (c : G → ConjHom N C) (b : G → N) : G × G → C := fun p => c p.1 (p.1 • b p.2)

@[simp] theorem cupConn10_apply (c : G → ConjHom N C) (n : N) (g : G) :
    cupConn10 c n g = c g (g • n) := rfl

@[simp] theorem cupConn20_apply (c : G × G → ConjHom N C) (n : N) (g h : G) :
    cupConn20 c n (g, h) = c (g, h) ((g * h) • n) := rfl

@[simp] theorem cupConn11_apply (c : G → ConjHom N C) (b : G → N) (g h : G) :
    cupConn11 c b (g, h) = c g (g • b h) := rfl

/-- The `(0,1)`-evaluation cup of an element `x : Hom_ℤ(N,C)` (a `0`-cochain) with a `1`-cochain
`b` of `N`: the `1`-cochain `g ↦ x (b g)`.  (For `p = 0` the general cup formula carries no
action, the empty product being `1`.) -/
def cupConn01 (x : ConjHom N C) (b : G → N) : G → C := fun g => x (b g)

/-- The `(0,2)`-evaluation cup: the `2`-cochain `(g,h) ↦ x (b (g,h))`. -/
def cupConn02 (x : ConjHom N C) (b : G × G → N) : G × G → C := fun p => x (b p)

@[simp] theorem cupConn01_apply (x : ConjHom N C) (b : G → N) (g : G) :
    cupConn01 x b g = x (b g) := rfl

@[simp] theorem cupConn02_apply (x : ConjHom N C) (b : G × G → N) (p : G × G) :
    cupConn02 x b p = x (b p) := rfl

@[simp] theorem cupConn02_zero (x : ConjHom N C) :
    cupConn02 x (0 : G × G → N) = 0 := by
  funext p; simp [cupConn02]

@[simp] theorem cupConn20_zero (n : N) : cupConn20 (0 : G × G → ConjHom N C) n = 0 := by
  funext p; simp [cupConn20]

@[simp] theorem cupConn11_zero_left (b : G → N) :
    cupConn11 (0 : G → ConjHom N C) b = 0 := by
  funext p; simp [cupConn11]

@[simp] theorem cupConn11_zero_right (c : G → ConjHom N C) :
    cupConn11 c (0 : G → N) = 0 := by
  funext p; simp [cupConn11]

/-- The `(1,1)`-evaluation cup is additive in its first argument. -/
theorem cupConn11_add_left (c c' : G → ConjHom N C) (b : G → N) :
    cupConn11 (c + c') b = cupConn11 c b + cupConn11 c' b := by
  funext p; simp [cupConn11, ConjHom.add_apply]

/-- The `(1,1)`-evaluation cup is additive in its second argument. -/
theorem cupConn11_add_right (c : G → ConjHom N C) (b b' : G → N) :
    cupConn11 c (b + b') = cupConn11 c b + cupConn11 c b' := by
  funext p; simp [cupConn11, smul_add, map_add]

end CupDefs

/-! ## Two elementary `G`-action identities -/

section Actions

variable {G : Type u} [Group G] {N : Type v} [AddCommGroup N] [DistribMulAction G N]

/-- `(g * h) • n - g • (h • n - n) = g • n`: the difference `(g*h)·n - g·n` is `g` times the
difference `h·n - n`. -/
theorem mul_smul_sub_smul_sub (g h : G) (n : N) :
    (g * h) • n - g • (h • n - n) = g • n := by
  rw [mul_smul, smul_sub]
  abel

/-- `g⁻¹ • ((g * h) • n) = h • n`. -/
theorem inv_smul_mul_smul (g h : G) (n : N) : g⁻¹ • ((g * h) • n) = h • n := by
  rw [← mul_smul, show g⁻¹ * (g * h) = h by group]

end Actions

/-! ## The Leibniz rule for the evaluation cup -/

section Leibniz

variable {G : Type u} [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The Leibniz rule for the evaluation cup**: for an arbitrary `1`-cochain `c` with values in
`Hom_ℤ(N,C)` and an element `n : N`,

  `d¹(c ⌣ n) = (d¹c) ⌣ n − c ⌣ (d⁰n)`,

where the cups are the evaluation cups `cupConn10`, `cupConn20`, `cupConn11`.  This is the identity
that makes the third square of Milne's diagram (1.9.1) commute. -/
theorem d1_cupConn10_eq (c : G → ConjHom N C) (n : N) :
    Work.GroupCohomology.d1 G C (cupConn10 c n)
      = cupConn20 (Work.GroupCohomology.d1 G (ConjHom N C) c) n
        - cupConn11 c (Work.GroupCohomology.d0 G N n) := by
  funext p
  obtain ⟨g, h⟩ := p
  have hkey : (g * h) • n - g • (h • n - n) = g • n := mul_smul_sub_smul_sub g h n
  simp only [Work.GroupCohomology.d1_apply, Work.GroupCohomology.d0_apply,
    cupConn10_apply, cupConn20_apply, cupConn11_apply, Pi.sub_apply,
    ConjHom.sub_apply, ConjHom.add_apply, ConjHom.smul_apply, inv_smul_mul_smul]
  rw [← hkey, map_sub]
  abel

/-- **The Leibniz rule at `(0,1)`**: for an element `x : Hom_ℤ(N,C)` and a `1`-cochain `b` of `N`,

  `d¹(x ⌣ b) = (d⁰x) ⌣ b + x ⌣ (d¹b)`.

With `b` a `1`-cocycle it says that the cup `(d⁰x) ⌣ b` of a `1`-coboundary with a `1`-cocycle is
the coboundary `d¹(x ⌣ b)`: the *first* variable of the `(1,1)`-cup descends to cohomology. -/
theorem d1_cupConn01_eq (x : ConjHom N C) (b : G → N) :
    Work.GroupCohomology.d1 G C (cupConn01 x b)
      = cupConn11 (Work.GroupCohomology.d0 G (ConjHom N C) x) b
        + cupConn02 x (Work.GroupCohomology.d1 G N b) := by
  funext p
  obtain ⟨g, h⟩ := p
  have hg : g⁻¹ • (g • b h) = b h := by
    rw [← mul_smul, show g⁻¹ * g = 1 by group, one_smul]
  simp only [Work.GroupCohomology.d1_apply, Work.GroupCohomology.d0_apply, cupConn01_apply,
    cupConn02_apply, cupConn11_apply, Pi.add_apply, ConjHom.sub_apply, ConjHom.smul_apply, hg,
    map_add, map_sub]
  abel

end Leibniz

/-! ## The short-exact-sequence form (the third square of Milne (1.9.1)) -/

section SES

variable {G : Type u} [TopologicalSpace G] [Group G]
  {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

variable (S : Work.AbsoluteKummer.ShortExactSeq G M N P)

include S

/-- The evaluation of a `Hom_ℤ(N,C)`-valued `1`-cocycle's coboundary at an element of `ι(M)` is
zero, when the cochain restricts to a `1`-cocycle on `M`. -/
theorem d1_conjHom_apply_iota_eq_zero
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (g h : G) (m : M) :
    Work.GroupCohomology.d1 G (ConjHom N C) cLift (g, h) (S.iota m) = 0 := by
  rw [Work.GroupCohomology.d1_apply, ConjHom.add_apply, ConjHom.sub_apply, ConjHom.smul_apply]
  rw [← S.iota_equivariant g⁻¹ m, hlift h (g⁻¹ • m), hlift (g * h) m, hlift g m, hc g h]
  rw [ConjHom.add_apply, ConjHom.smul_apply]
  abel

/-- **The connecting-map compatibility of the evaluation pairing** (the third square of Milne's
diagram (1.9.1)), at the level of cochains.

Let `0 → M →^{ι} N →^{π} P → 0` be a short exact sequence of `G`-modules, `c` a `1`-cocycle with
values in `Hom_ℤ(M,C)`, `cLift` a lift of `c` to a `1`-cochain with values in `Hom_ℤ(N,C)` (i.e.
`cLift g ∘ ι = c g` for all `g`), and `n : N` a lift of an invariant element `π n ∈ P^G`.

Then the *connecting cocycle* `d¹cLift` evaluated at `n` differs from the cup `c ⌣ d⁰n` of `c` with the
connecting cocycle `d⁰n : g ↦ g • n - n` by the explicit coboundary `d¹(cLift ⌣ n)`:

  `d¹(cLift ⌣ n) = ⟨d¹cLift, n⟩ − cLift ⌣ (d⁰n)`.

Both terms on the right have the same class in `H²(G,C)` (they are the two composites of the third
square), so the square commutes. -/
theorem d1_cupConn10_eq_of_shortExact
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : S.pi n ∈ Work.GroupCohomology.invariants G P) :
    Work.GroupCohomology.d1 G C (cupConn10 cLift n)
      = (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
        - cupConn11 cLift (Work.GroupCohomology.d0 G N n) := by
  rw [d1_cupConn10_eq cLift n]
  funext p
  obtain ⟨g, h⟩ := p
  have hmem : (g * h) • n - n ∈ S.iota.range := by
    rw [S.range_iota_eq_ker_pi, AddMonoidHom.mem_ker, map_sub, S.pi_equivariant (g * h) n,
      hn (g * h), sub_self]
  obtain ⟨m, hm⟩ := hmem
  have hsplit : (g * h) • n = n + S.iota m := by
    rw [hm]; abel
  simp only [Pi.sub_apply]
  rw [cupConn20_apply, hsplit, map_add,
    d1_conjHom_apply_iota_eq_zero S c cLift hlift hc g h m, add_zero]

/-- **The connecting-map compatibility, in cohomological form.**  With the notation of
`d1_cupConn10_eq_of_shortExact`, the two composites of the third square of Milne's diagram (1.9.1)
differ by a `2`-coboundary:

  `(d¹cLift evaluated at n) − (cLift ⌣ d⁰n) ∈ B²_c(G,C)`.

Hence they represent the same class in `H²(G,C)` (both are `2`-cocycles as soon as one of them is:
the left one is the API's connecting cocycle `deltaCocycleC` evaluated at the invariant `π n`, cf.
`SES/deltaH2_exact`), i.e. the third square commutes. -/
theorem SES_cupConn_sub_mem_B2
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : S.pi n ∈ Work.GroupCohomology.invariants G P)
    (hlc : Work.AbsoluteKummer.IsLocallyConstant (cupConn10 cLift n)) :
    (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
      - cupConn11 cLift (Work.GroupCohomology.d0 G N n)
      ∈ Work.AbsoluteKummer.B2 G C :=
  ⟨cupConn10 cLift n, hlc, d1_cupConn10_eq_of_shortExact S c cLift hlift hc n hn⟩

end SES

/-! ## Cocycle-hood of the connecting cocycle evaluated at an invariant lift -/

section EvalZ2

variable {G : Type u} [TopologicalSpace G] [Group G]
  {M : Type v} [AddCommGroup M] [DistribMulAction G M]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {P : Type v} [AddCommGroup P] [DistribMulAction G P]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The connecting cocycle evaluated at an invariant lift is a `2`-cocycle.**  With the notation
of `d1_cupConn10_eq_of_shortExact` (a short exact sequence `ι : M ↪ N`, `π : N ↠ P = N/M`, a
`1`-cocycle `c` on `M` lifted to `cLift` on `N`, and `n` a lift of an invariant element of `P`),
the `2`-cochain

  `(g,h) ↦ (d¹cLift (g,h)) n`

is a `2`-cocycle with values in `C`.  It is the cochain representative of the *left-hand* composite
of the third square of Milne's diagram (1.9.1); together with
`d1_cupConn10_eq_of_shortExact` (which shows that its difference from the right-hand composite
`cLift ⌣ d⁰n` is the coboundary `d¹(cLift ⌣ n)`) it gives the commutativity of that square at the
level of `H²(−,C)`.

The proof: `d¹cLift` is a `2`-cocycle of the coefficient complex `Hom_ℤ(N,C)` by `d²∘d¹ = 0`, it
kills `ι(M)` (that is the hypothesis that `c` is a `1`-cocycle), and `(g*h)•n − n`, `g•n − n ∈ ι(M)`
because `π n` is invariant; evaluating the cocycle identity of `d¹cLift` at `(g*h*k)•n` therefore
gives the cocycle identity of the evaluated cochain. -/
theorem d1_eval_mem_Z2
    (ι : M →+ N) (hι : Work.GroupCohomology.IsEquivariant G ι)
    (π : N →+ P) (hπ : Work.GroupCohomology.IsEquivariant G π)
    (hker : π.ker = ι.range)
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (ι m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : π n ∈ Work.GroupCohomology.invariants G P) :
    (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
      ∈ Work.GroupCohomology.Z2 G C := by
  classical
  set V : G × G → ConjHom N C := Work.GroupCohomology.d1 G (ConjHom N C) cLift with hVdef
  have hVι : ∀ (g h : G) (m : M), V (g, h) (ι m) = 0 := by
    intro g h m
    rw [hVdef, Work.GroupCohomology.d1_apply, ConjHom.add_apply, ConjHom.sub_apply,
      ConjHom.smul_apply]
    rw [← hι g⁻¹ m, hlift h (g⁻¹ • m), hlift (g * h) m, hlift g m, hc g h]
    rw [ConjHom.add_apply, ConjHom.smul_apply]
    abel
  have hVcoc : ∀ g h k, V (g * h, k) + V (g, h) = g • V (h, k) + V (g, h * k) := by
    intro g h k
    exact Work.GroupCohomology.d1_mem_Z2 G (ConjHom N C) cLift g h k
  have hmem : ∀ u : N, π u = π n → u - n ∈ ι.range := by
    intro u hu
    rw [← hker, AddMonoidHom.mem_ker, map_sub, hu, sub_self]
  have hVeq : ∀ (p : G × G) (u : N), u - n ∈ ι.range → V p u = V p n := by
    intro p u hu
    obtain ⟨m, hm⟩ := hu
    have h1 : u = n + ι m := by rw [hm]; abel
    rw [h1, map_add, hVι p.1 p.2 m, add_zero]
  have hpinv : ∀ x : G, π (x • n) = π n := fun x => by rw [hπ, hn x]
  intro g h k
  change (V (g * h, k)) n + (V (g, h)) n
      = g • (V (h, k)) n + (V (g, h * k)) n
  have hpu : π ((g * (h * k)) • n) = π n := hpinv (g * (h * k))
  have h1 : V (g * h, k) n = V (g * h, k) ((g * (h * k)) • n) :=
    (hVeq (g * h, k) _ (hmem _ hpu)).symm
  have h2 : V (g, h) n = V (g, h) ((g * (h * k)) • n) :=
    (hVeq (g, h) _ (hmem _ hpu)).symm
  have h3 : g • V (h, k) n = (g • V (h, k)) ((g * (h * k)) • n) := by
    rw [ConjHom.smul_apply]
    congr 1
    rw [← mul_smul, show g⁻¹ * (g * (h * k)) = h * k by group]
    exact (hVeq (h, k) _ (hmem _ (hpinv (h * k)))).symm
  have h4 : V (g, h * k) n = V (g, h * k) ((g * (h * k)) • n) :=
    (hVeq (g, h * k) _ (hmem _ hpu)).symm
  rw [h1, h2, h3, h4]
  simpa only [ConjHom.add_apply] using
    congrArg (fun φ : ConjHom N C => φ ((g * (h * k)) • n)) (hVcoc g h k)

/-- The same statement for a short exact sequence (with `S.iota`, `S.pi`). -/
theorem d1_eval_mem_Z2_of_shortExact
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : S.pi n ∈ Work.GroupCohomology.invariants G P) :
    (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
      ∈ Work.GroupCohomology.Z2 G C :=
  d1_eval_mem_Z2 S.iota S.iota_equivariant S.pi S.pi_equivariant S.range_iota_eq_ker_pi.symm
    c cLift hlift hc n hn

/-- **Both composites of the third square of Milne's diagram are `2`-cocycles whose difference is a
`2`-coboundary**, i.e. the square commutes in `H²(−,C)`.  The two composites are

* `(g,h) ↦ (d¹cLift (g,h)) n` — the connecting cocycle of the coefficient sequence evaluated at the
  invariant lift `π n` (the *left hand* composite), a `2`-cocycle by `d1_eval_mem_Z2`;
* `cLift ⌣ d⁰n` — the cup of `cLift` with the connecting cocycle of the module sequence (the *right
  hand* composite);

and their difference is `d¹(cLift ⌣ n)` by `d1_cupConn10_eq_of_shortExact`.  In particular both have
the same class in `H²(G,C)`, which is the commutativity of the third square. -/
theorem SES_cupConn11_d0_mem_Z2
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : S.pi n ∈ Work.GroupCohomology.invariants G P) :
    cupConn11 cLift (Work.GroupCohomology.d0 G N n) ∈ Work.GroupCohomology.Z2 G C := by
  have hU := d1_eval_mem_Z2_of_shortExact S c cLift hlift hc n hn
  have hd : (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
      - cupConn11 cLift (Work.GroupCohomology.d0 G N n) ∈ Work.GroupCohomology.B2 G C :=
    ⟨cupConn10 cLift n, d1_cupConn10_eq_of_shortExact S c cLift hlift hc n hn⟩
  have hsub : (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
      - ((fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n)
          - cupConn11 cLift (Work.GroupCohomology.d0 G N n))
      = cupConn11 cLift (Work.GroupCohomology.d0 G N n) := by abel
  rw [← hsub]
  exact sub_mem hU (Work.GroupCohomology.B2_le_Z2 G C hd)

/-- **Commutativity of the third square of Milne's diagram (1.9.1)** at the level of the class in
`H²(G,C)`: the two composites of `d1_eval_mem_Z2` and of `SES_cupConn11_d0_mem_Z2` — the connecting
cocycle evaluated at `n`, and the cup of `cLift` with the connecting cocycle `d⁰n` — represent the
same class.  This is the square that the five-lemma dévissage of Milne's Theorem I.1.8 reads off,
and the `r = 1` companion of `PT/alphaTwo_naturality.lean`. -/
theorem SES_cupConn_H2π_eq
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (c : G → ConjHom M C) (cLift : G → ConjHom N C)
    (hlift : ∀ (g : G) (m : M), cLift g (S.iota m) = c g m)
    (hc : ∀ g h : G, c (g * h) = g • c h + c g)
    (n : N) (hn : S.pi n ∈ Work.GroupCohomology.invariants G P)
    (hU : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n))
    (hy : Work.AbsoluteKummer.IsLocallyConstant
      (cupConn11 cLift (Work.GroupCohomology.d0 G N n)))
    (hcob : Work.AbsoluteKummer.IsLocallyConstant (cupConn10 cLift n)) :
    Work.AbsoluteKummer.H2π G C
        ⟨fun p : G × G => Work.GroupCohomology.d1 G (ConjHom N C) cLift p n,
          ⟨d1_eval_mem_Z2_of_shortExact S c cLift hlift hc n hn, hU⟩⟩
      = Work.AbsoluteKummer.H2π G C
        ⟨cupConn11 cLift (Work.GroupCohomology.d0 G N n),
          ⟨SES_cupConn11_d0_mem_Z2 S c cLift hlift hc n hn, hy⟩⟩ := by
  rw [Work.AbsoluteKummer.H2π_eq_iff]
  exact SES_cupConn_sub_mem_B2 S c cLift hlift hc n hn hcob

end EvalZ2

/-! ## The cohomological form -/

section Cohomological

variable {G : Type u} [TopologicalSpace G] [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The connecting cocycle evaluated at `n` and the cup with the connecting cocycle differ by a
coboundary** (`(1,0)`-Leibniz rule, general form). -/
theorem sub_mem_d1_range (c : G → ConjHom N C) (n : N) :
    cupConn20 (Work.GroupCohomology.d1 G (ConjHom N C) c) n
      - cupConn11 c (Work.GroupCohomology.d0 G N n)
      ∈ (Work.GroupCohomology.d1 G C).range :=
  ⟨cupConn10 c n, d1_cupConn10_eq c n⟩

/-- The same, with the cobounding cochain required to be a *continuous* `1`-cochain. -/
theorem sub_mem_B2_cupConn (c : G → ConjHom N C) (n : N)
    (hlc : Work.AbsoluteKummer.IsLocallyConstant (cupConn10 c n)) :
    cupConn20 (Work.GroupCohomology.d1 G (ConjHom N C) c) n
      - cupConn11 c (Work.GroupCohomology.d0 G N n)
      ∈ Work.AbsoluteKummer.B2 G C :=
  ⟨cupConn10 c n, hlc, d1_cupConn10_eq c n⟩

end Cohomological

/-! ## The `(1,1)`-cup: cocycles and coboundaries -/

section Cup11

variable {G : Type u} [Group G]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The `(1,1)`-evaluation cup of two `1`-cocycles is a `2`-cocycle**: the cup descends to
`H¹(G, Hom_ℤ(N,C)) × H¹(G,N) → H²(G,C)`, i.e. it is the map `α¹` of Milne's diagram. -/
theorem cupConn11_mem_Z2 {c : G → ConjHom N C} {b : G → N}
    (hc : c ∈ Work.GroupCohomology.Z1 G (ConjHom N C)) (hb : b ∈ Work.GroupCohomology.Z1 G N) :
    cupConn11 c b ∈ Work.GroupCohomology.Z2 G C := by
  intro g h k
  simp only [cupConn11_apply]
  rw [hc g h, ConjHom.add_apply, ConjHom.smul_apply, inv_smul_mul_smul]
  rw [hb h k, smul_add, mul_smul, map_add]
  abel

/-- **The `(1,1)`-evaluation cup of a `1`-cocycle with a `1`-coboundary is a `2`-coboundary**: the
cup descends to `H¹(G, Hom_ℤ(N,C)) × H¹(G,N) → H²(G,C)` in the second variable as well. -/
theorem cupConn11_of_d1_eq_zero (c : G → ConjHom N C) (n : N)
    (hc : Work.GroupCohomology.d1 G (ConjHom N C) c = 0) :
    cupConn11 c (Work.GroupCohomology.d0 G N n)
      = - Work.GroupCohomology.d1 G C (cupConn10 c n) := by
  have h := d1_cupConn10_eq c n
  rw [hc, cupConn20_zero] at h
  rw [h]
  abel

/-- **The `(1,1)`-cup of a `1`-coboundary with a `1`-cocycle is a `2`-coboundary**: the first
variable of `cupConn11` descends to cohomology as well, so that the `(1,1)`-cup is a well defined
pairing `H¹(G, Hom_ℤ(N,C)) × H¹(G,N) → H²(G,C)` (the map `α¹` of Milne's diagram). -/
theorem cupConn11_d0_eq (x : ConjHom N C) (b : G → N)
    (hb : Work.GroupCohomology.d1 G N b = 0) :
    cupConn11 (Work.GroupCohomology.d0 G (ConjHom N C) x) b
      = Work.GroupCohomology.d1 G C (cupConn01 x b) := by
  rw [d1_cupConn01_eq x b, hb, cupConn02_zero, add_zero]

end Cup11

/-! ## Naturality of the `(1,1)`-cup in the coefficient module -/

section Precomp

variable {G : Type u} [Group G]
  {N₁ : Type v} [AddCommGroup N₁] [DistribMulAction G N₁]
  {N₂ : Type v} [AddCommGroup N₂] [DistribMulAction G N₂]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **Naturality of the `(1,1)`-evaluation cup in the coefficient module**: for an equivariant
`φ : N₁ →+ N₂`, cupping the pushed-forward cochain `g ↦ c g ∘ φ` with `b` is the same as cupping
`c` with `φ ∘ b`.  This is the square that identifies `α¹` computed on `N₁` with `α¹` computed on
`N₂` (the `r = 1` companion of `PT/alphaTwo_naturality.lean`). -/
theorem cupConn11_precomp (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (c : G → ConjHom N₂ C) (b : G → N₁) :
    cupConn11 (fun g => ConjHom.precomp φ (c g)) b = cupConn11 c (fun g => φ (b g)) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [cupConn11_apply, ConjHom.precomp_apply, hφ g (b h)]

end Precomp

end Work.SSGRoute.PT
