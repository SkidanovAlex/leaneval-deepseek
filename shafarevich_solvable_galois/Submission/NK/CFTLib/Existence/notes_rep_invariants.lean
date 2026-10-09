/-
# Brief for `NK.CFTLib.Existence.rep_invariants_le_range_norm_of_auxiliary`

(Comment-only module: import it to read the plan; it contains no declarations.)

## The statement

```lean
theorem rep_invariants_le_range_norm_of_auxiliary (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype Nsub]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants ≤
      LinearMap.range ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm)
```

## What it says, and why it is TRUE

Put `G := Gal(Ω/K)`, `A := C_Ω` (the idèle class group of `Ω`, as a `ℤ[G]`-module via
`IdeleClassGroup.rep`, additive notation), and

* `M' := fixedField Msub` (so `Msub = Gal(Ω/M')`), `L' := fixedField Nsub` (so `Nsub = Gal(Ω/L')`).

`hdisj` says `M' ⊓ L' = ⊥` and `hsup` says `M' ⊔ L' = ⊤`, hence `Ω = M'L'`, the restriction
`Gal(Ω/L') → Gal(M'/K)` is an isomorphism, and `G ≅ Gal(M'/K) × Gal(L'/K)`; `hcyc` says
`Gal(M'/K) = G/Msub ≅ Nsub` is cyclic and `hM`, `hN` force `|Msub| = |Nsub| = n := [L:K]`, hence
`G ≅ ℤ/n × Gal(L'/K)` — in particular `G` is abelian of order `n²` and of exponent `n`.

The conclusion is `A^G ⊆ range(N_N)` where `N_N = ∑_{g ∈ Nsub} ρ(g) : A → A` is the norm of the
restriction of `A` to `Nsub`.  Since `A^N = C_{L'}` (invariants = idèle class group of the fixed
field, available as `NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup`) and
`range(N_N) = N_{Ω/L'}C_Ω =: N`, the conclusion is the classical statement

  `C_K ⊆ N_{Ω/L'}C_Ω`  (inside `C_{L'}`),

i.e. the image of the idèle class group of the base field lies in the norm subgroup of the
cyclotomic-compositum direction.  It is the *arithmetic input* `(**)′` of
`Submission/Work/CFTLib/RouteB/plan.lean` (see the "Record" section of that file, which discusses a
previous prover's verdict), and the H⁰ mirror of the target
`NK.CFTLib.Existence.res_inf_le_ker_res_of_auxiliary`.

Why it is true: it is the Verlagerung (transfer) computation.  For `x ∈ C_K ⊆ C_{L'}` the map
`C_K → C_{L'} → Gal(Ω/L')^{ab} = Nsub` induced by the two reciprocity isomorphisms equals
`V ∘ art_{Ω/K}` where `V : G^{ab} → Nsub^{ab}` is the transfer; and for `G = Msub × Nsub` with
`|Nsub| = n` the transfer is `V(m,k) = k^{|Msub|} = k^n = 1`, since `Nsub` is cyclic of order `n`.
(Equivalently: the Artin symbol of `𝔞𝒪_{L'}` in `Ω/L'` is the `[L':K] = n`-th power of the Artin
symbol of `𝔞` in `Ω/K`, and `G` has exponent `n`.)

The statement is NOT derivable from the abstract class-formation axioms: the trivial formation
`A = ℤ`, `G = (ℤ/2)²`, `Msub = Nsub =` the two factors satisfies `hM, hN, hcyc, hdisj, hsup`, but
`A^G = ℤ ⊄ 2ℤ = range(N_N)`.

## Available, sorry-free, and directly useful

* `NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup`:
  for `L/K` finite Galois with `ψ : C[K] →* C[L]` an "inclusion" (i.e. induced from a monoid
  homomorphism `𝕀 K →* 𝕀 L` whose components are the local embeddings, `hφ`), `q ∈ ψ.range ↔ q` is
  `Gal(L/K)`-fixed.  This gives `A^G = range(C_K → C_Ω)` (and the `Nsub`-analogue
  `A^N = range(C_{L'} → C_Ω)`).
* `NK.GlobalCFT.Cohomology.ofMul_mem_range_norm_iff`:
  for `L/K` finite Galois and `ψ : C[K] →* C[L]` injective with the norm identity
  `ψ (N_{L/K} q) = ∏_{σ : L ≃ₐ[K] L} σ • q`, one has
  `Additive.ofMul (ψ q) ∈ LinearMap.range ((rep K L).ρ.norm) ↔ q ∈ N_{L/K}C_L`.
  Instantiated at the extension `Ω/L'` this converts membership in `N_{Ω/L'}C_Ω` (= the norm
  subgroup, in `C_{L'}`) into membership in `range(N_N)` (in `C_Ω`), so it is the bridge needed to
  turn any statement about `C_K ⊆ N_{Ω/L'}C_Ω` into the conclusion of this lemma.
  The norm identity is available: see `NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom`
  (`ψ₀ (normClassHom K M q) = ∏ σ : M ≃ₐ[K] M, σ • q`).
* `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`: **unconditionally**
  `(N_{L/K}C_L).index = [L : K]` for cyclic `L/K`.  Applied to `Ω/L'` (cyclic of degree `n`):
  `[C_{L'} : N_{Ω/L'}C_Ω] = n`.
* `NK.GlobalCFTdeep.secondInequality_unconditional` / `index_le_finrank_of_isGalois`
  (`index_le_finrank_of_isGalois`): `[C_K : N_{L/K}C_L] ≤ [L:K]` for all finite Galois `L/K`,
  unconditionally.
* `NK.Existence.ker_normClassHom_le_normClassSubgroup_of_isCyclic`: **unconditionally**, for a
  tower `K ⊆ M ⊆ L` with `L/K` cyclic: `ker (N_{M/K} : C_M → C_K) ⊆ N_{L/M}C_L`.  Its proof is pure
  index arithmetic (`index_normClassSubgroup_le_mul_index`, the cyclic index formula at the top, the
  second inequality at the two lower levels, then the abstract group lemma
  `Commons.FieldTheory.Galois.ker_le_range_of_index_map_eq_mul`).  This is a *template*: any index
  identity of the form
  `[C_K : N_{L/K}C_L] = [C_M : N_{L/M}C_L] · [C_K : N_{M/K}C_M]` yields `ker ⊆ range`.
* `NK.CFTLib.Arl.artinSym` (`Submission/Work/CFTLib/Arl/Defs.lean`): the Artin symbol
  `A ↦ ∏_𝔭 frobAtPrime 𝔭 ^ (count 𝔭 A)` of a fractional ideal; `artinSym_mul`, `artinSym_prime`,
  `artinSym_one`.
* `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one`: **sorry-free and axiom-clean**, and it is the
  only thing needed to prove the "crux" `artinSym_spanSingleton_eq_one_of_mem_congruence`
  (two lines: unwrap `IsCongruenceSubgroup` into its `hcong`/`hpos` components; see
  `Submission/Work/CFTLib/Arl/NOTES_artinSym_congruence.md`).  WARNING: the file
  `Submission/Work/CFTLib/Arl/artinSym_spanSingleton_eq_one_of_mem_congruence.lean` currently has a
  `sorry`, and therefore `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` is *tainted* (`#print axioms`
  shows `sorryAx`).  Do NOT import/use `exists_monoidHom_ideleArtin`.  Copy its proof into your own
  file, replacing the crux by your own two-line proof.
* `NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one`: **sorry-free, axiom-clean** — the
  transfer step at a single prime: for `K ⊆ L₀ ⊆ E` with `E/K` Galois, `M` intermediate Galois
  abelian, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`, `𝔭` unramified in `M` and `σ ^ [L₀:K] = 1` for
  `σ ∈ Gal(M/K)`:
  `∏_{𝔮 | 𝔭} Frob_𝔮(E/L₀)^{e(𝔮|𝔭)} = 1`.
* `NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_relNorm_eq_one`: **sorry-free, axiom-clean** — the
  ideal-theoretic Artin symbol kills norms of ideals (`frobSymbol` is defined to be `1` at ramified
  primes, so ramified primes are simply ignored).
* `NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`: **sorry-free, axiom-clean** — the
  modulus-`m` congruence subgroup `U ≤ 𝕀 K` with the adjustment `∀ x, ∃ b : Kˣ, x · (b) ∈ U`.
* `h : ArtinReciprocityIdeal` gives, for the abelian extension `Ω/L'`: a modulus `m` with
  `0 < m`, all `𝔭 ∤ (m)` unramified in `Ω/L'`, and the Artin law `hprinc` at modulus `m`.  Enlarging
  `m` by the product of the ramified primes is free (the assumption `a ≡ 1 mod m'` is stronger), so
  one may assume every ramified prime divides `(m)`.

## A route that gets most of the way (and where it stops)

Build the idèlic Artin map `art : 𝕀 L' →* Gal(Ω/L')` from `h` exactly as in
`Submission/Work/CFTLib/Arl/exists_monoidHom_ideleArtin.lean` (but with your own crux).  It is
surjective, kills the principal idèles `L'^×`, and satisfies
`art (ideleOfPrime 𝔮) = frobAtPrime 𝔮` for `𝔮 ∤ (m)`; the crux shows `art = artinSym ∘ idealOf`,
i.e. `art` is well defined.

Then (`art` kills `L'^×`, and `idealOf` of a unit idèle is `1`):

1. For a prime `𝔭` of `K` with `𝔭 ∤ (m)`:
   `art (i (ideleOfPrime 𝔭)) = artinSym (𝔭𝒪_{L'}) = ∏_{𝔮 | 𝔭} frobAtPrime(𝔮)^{e(𝔮|𝔭)} = 1`
   by the transfer lemma above (`L₀ := L'`, `M := M'`, `E := Ω`, `σ := frobAtPrime(𝔭)` with
   `σ^n = 1` because `Gal(M'/K) ≅ ℤ/n`).
2. `art ∘ i` kills `K^×`, the unit idèles (finite part), and the archimedean components.
3. `𝕀 K` is generated by its principal idèles, its unit idèles, the prime idèles at the primes
   `𝔭 ∤ (m)`, and the archimedean components (each `K_𝔭^× = 𝒪_𝔭^× · π_𝔭^ℤ`, and `art ∘ i` depends
   only on the finite part).
   Hence `art ∘ i = 1`, i.e. `C_K ⊆ ker(art)`.

To conclude `C_K ⊆ N_{Ω/L'}C_Ω` one wants `ker(art) = N_{Ω/L'}C_Ω`.  One inclusion is the local
input: `N ⊆ ker(art)` ("the Artin map kills the norms"), which is *elementary away from the ramified
primes* (`artinSymbol_relNorm_eq_one`; note that the ramified primes of `Ω/L'` are exactly the
primes ramified in `M'/K`, i.e. those dividing `(m)`, because
`I_𝔭(Ω/K) ∩ Nsub ≠ 1` forces the image of `I_𝔭` in `Gal(M'/K) = G/Msub` to be non-trivial), but at
the ramified primes it needs the local reciprocity theorem (the norm group of a local extension
contains a congruence subgroup of the local units — Milne *CFT* Theorem 8.1 / Hasse reciprocity).
Both `ker(art)` and `N_{Ω/L'}C_Ω` have index `n` in `C_{L'}` (`index_eq_finrank_of_isCyclic`, and
surjectivity of `art`), so *one* inclusion suffices.

## Honest assessment

Two independent pieces are needed and both are substantial:

1. the cohomological reduction from the H² form of the target to this H⁰ form (being done by the
   requester, by `capture_two_map_eq_zero_of_cyclic` + the five-term sequence);
2. the arithmetic above, whose genuinely missing ingredient is the local input at the ramified
   primes.  See `Submission/Work/CFTLib/RouteB/plan.lean` ("Record: the verdict on
   `res_inf_le_ker_res_of_auxiliary`") and `Submission/Work/CFTLib/Arl/STATUS.md`.

If step 2 stalls at the ramified primes, please say so precisely (and record which sub-steps *are*
proved, in files of your own), rather than declaring the statement false: the statement is
mathematically true (the transfer computation above) and its H² sibling was already the subject of
one "declared FALSE / mis-stated" verdict on exactly the grounds of missing infrastructure.
-/
