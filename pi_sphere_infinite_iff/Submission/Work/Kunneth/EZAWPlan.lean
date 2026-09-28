import Mathlib
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.EZAWHomotopy

/-!
# The Eilenberg–Zilber homotopy `ezMap ≫ awMap ≃ 𝟙`: plan and interfaces

This file contains no declarations; it is the written plan for the remaining work.

## The target

`Work.Kunneth.ez_aw_homotopy (X Y : SSet) : Nonempty (Homotopy (ezMap X Y ≫ awMap X Y) (𝟙 (tChain X Y)))`
in `Submission/Work/Kunneth/ez_aw_homotopy.lean`.

## The strategy (acyclic models over the pairs `(Δ[p], Δ[q])`)

Vocabulary (all in `EZAWDefs.lean` / `EZAWHomotopy.lean`):
* `SdS n = Δ[n]`, `sMod n = C_*(Δ[n])`, `tMod p q = sMod p ⊗ sMod q` (the Koszul tensor product
  `tpC` of `Tensor.lean`), `U p q = σ_p ⊗ τ_q` (universal element, degree `p+q`),
  `Ezaw X Y = ezMap X Y ≫ awMap X Y`, `Em p q = Ezaw(U p q) - U p q` (degree `p+q`).
* `ind f g = tpMap (chainComplexMap f zz) (chainComplexMap g zz)`, the map induced on the
  tensor complexes by a pair of simplicial maps; `phiMod p q i : tMod p q ⟶ tMod (p+1) q` and
  `psiMod p q j : tMod p q ⟶ tMod p (q+1)` are the cofaces.
* `phiSum p q = AlternatingCofaceMapComplex.objD (phiCos q) p` and
  `psiSum p q = AlternatingCofaceMapComplex.objD (psiCos p) q` are the alternating sums of the
  cofaces; `phiSum_eq`/`psiSum_eq` expand them as sums of `phiMod`/`psiMod`,
  `phiSum_comp`/`psiSum_comp` are the square-zero identities and `psiSum_phiSum` says that the two
  coface sums commute.
* `dcast p q h` transports elements of `tMod p q` along an equality `h` of degrees;
  `d_dcast`, `phiMod_dcast`, `psiMod_dcast` are the commutation lemmas.
* `phiT W p q i` (degree `(p+1)+q`) and `psiT W p q j` (degree `p+(q+1)`) are the φ- and ψ-terms
  built from a family `W : (p q : ℕ) → (tMod p q).X (p+q+1)`.
* `dfc W p q` is **the defect**: `Em p q` minus the φ-sum of `W (p-1) q` minus `(-1)^p` times the
  ψ-sum of `W p (q-1)`, i.e. the element that the model chain `W p q` must fill.  Its four cases
  (`match p, q`) are exactly the four possible vanishing patterns of the sums.

## Remaining pieces

1. `ezaw_model_acyclic` (delegated): every cycle in positive degree of `tMod p q` is a boundary.
2. `Em_zero`: `Em 0 0 = 0` (delegated; a concrete computation over `Δ[0] ⊗ Δ[0]`).
3. The recursion: `∃ W, ∀ p q, (tMod p q).d (p+q+1) (p+q) (W p q) = dfc W p q`.  The values are
   obtained by filling `dfc W p q`, which requires (and is proved together with) the fact that
   `dfc W p q` is a cycle in positive degree.  The cycle condition is proved by the standard
   computation: apply `d` to the defect, use that `Ezaw` is a chain map together with the
   naturality `ezaw_ind_nat` for the `Em` part (giving
   `d (Em p q) = φ-sum of Em (p-1) q + (-1)^p ψ-sum of Em p (q-1)`), that the φ- and ψ-terms
   commute with `d` (chain maps + `dcast`), and that the second-order terms cancel by
   `phiSum_comp`/`psiSum_comp` (the φφ- and ψψ-terms) and by `psiSum_phiSum` (the mixed terms).
4. The assembly `ezaw_homotopy_of_W` (delegated): given `W` with the recursion equations, produce
   the natural chain homotopy `ezMap ≫ awMap ≃ 𝟙` on `tChain X Y` for all `X Y`.

## Hints for the degree bookkeeping in items 3 (in particular `dfc_cycle`)

* All the degree mismatches are between propositionally equal `Nat` expressions such as
  `p + (q+1)`, `(p+1) + q`, `p + q + 1`; they are handled by `dcast p q h` (transport of elements
  along an equality of degrees).  `dcast_congr` says that the transport does not depend on the
  chosen proof, `d_dcast` says that the differential commutes with it, and
  `phiMod_dcast`/`psiMod_dcast` say that the coface maps do.
* The `Em`-boundary identity (used in the cycle condition)
  `d (Em p q) = Σ_i (-1)^i φ_i(Em (p-1,q)) + (-1)^p Σ_j (-1)^j ψ_j(Em (p,q-1))`
  is *not yet in the workspace*: it has to be proved from `Ezaw` being a chain map plus the
  naturality `ezaw_ind_nat`, together with `d_genCh`-type expansions for the universal
  simplices `univS` and `d_dcast`.  Its degenerate cases (`p = 0` or `q = 0`) need no cast at
  all, since `0 + q` and `p + 0` reduce; only the case `(p+1, q+1)` needs `dcast`.
* Generating the recursion (item 3) can be done by strong induction on the total degree `p + q`:
  at level `n+1`, for each pair `(p,q)` with `p + q = n + 1` the element `dfc W p q` is filled
  with `ezaw_model_acyclic` (applied with `m := p+q`), which needs `dfc_cycle`; the recursion
  equations are needed only at total degree `n`, which is exactly the induction hypothesis.
-/

/-!

## Status (2026-09-24) and the exact remainder

**Done** (all sorry-free, axiom-clean): `tChain_hom_ext`, `ezaw_ind_nat` (naturality of `Ezaw`
w.r.t. `ind`), `Em_zero`, `ezaw_model_acyclic` (acyclicity of the models, via the `ModelContr`
framework of `ModelContr.lean`/`stdModelContr.lean`/`modelH_comm.lean`), and the **assembly**
`ezaw_homotopy_of_W`.

**Remaining**: only the recursion, i.e. the single lemma

```lean
theorem ezaw_W_exists :
    ∃ W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)),
      ∀ p q, (tMod p q).d (p + q + 1) (p + q) (W p q) = dfc W p q
```

Once this exists, `ez_aw_homotopy` is `by obtain ⟨W, hW⟩ := ezaw_W_exists; exact ezaw_homotopy_of_W W hW X Y`.

It splits into (a) the cycle condition `dfc_cycle` (statement in `_st_F.lean`) and (b) the
bookkeeping of the recursion.

### The key trick that removes every degree cast

**Do everything with the total degree as a variable and destruct the pair coordinates into
literal successors.**  In the `(p,q)`-indexed formulation the degrees such as `p+(q+1)`,
`(p+1)+q`, `p+q+1` are only propositionally equal, so `dcast` is needed everywhere.  If instead
one works with the "level" family

```lean
F : (n : ℕ) → (pq : tpIdx n) → ↥((tMod pq.1.1 pq.1.2).X (n + 1))
```

then all degrees are the variable `n` (or `n+1`, `n+2`), and if for a given pair one first
rewrites the coordinates as literal successors,

```lean
obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩   -- when 1 ≤ p
obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩   -- when 1 ≤ q
```

then `tMod p q` *reduces* to `tMod (p'+1) (q'+1)` and the coface maps `phiMod p' q' i`,
`psiMod p' (q') j` have literally the right source and target models.  Everything is then
cast-free: `tpC_d`, `tpD_lof_tmul`, `d_genCh`, `tpMap_tpLof`/`tpMap_tmul` all apply by `rw`.
(The same trick is used in `ezaw_model_acyclic`: `obtain ⟨k, rfl⟩ : ∃ k, m = k + 1`.)

In this formulation the recursion is a plain `Nat.rec`: **`dfc` at total degree `n+1` involves
the `W`-values only at total degree `n`** — that is what makes the induction work.  The level-`n`
data must therefore be indexed by `tpIdx n` (or by a pair together with an equation proof), and
the induction step needs the level-`n` datum of `⟨(p-1,q), _⟩` and `⟨(p,q-1), _⟩`; with the
successor rewriting these are `⟨(p',q'+1), _⟩` and `⟨(p'+1,q'), _⟩`, i.e. no subtraction at all.
(The level data should be shown to be independent of the proof component of the `tpIdx` element,
by induction on the level, so that these can be identified.)

### The `Em`-boundary identity (the only ingredient not yet in the workspace)

```lean
d (Em p q) = Σ_i (-1)^i · φ_i (Em (p-1,q)) + (-1)^p · Σ_j (-1)^j · ψ_j (Em (p,q-1))
```

Proof (no explicit expansion of `Ezaw` needed!):
`d (Em p q) = d (Ezaw (U p q) - U p q) = Ezaw (d (U p q)) - d (U p q) = (Ezaw - 1) (d (U p q))`,
using that `Ezaw` is a chain map; expand `d (U p q)` with `tpC_d`/`tpD_lof_tmul`/`d_genCh`
(the `φ`-terms are the faces of `genCh (univS p)`, the `ψ`-terms those of `genCh (univS q)`),
then use the **naturality** `ezaw_ind_nat` (applied to the coface pair `(δ_i, 𝟙)` resp.
`(𝟙, δ_j)`) to move `Ezaw - 1` inside.  The identification
`(stdSimplex.map (δ_i)) (univS q) = (SdS (q+1)).δ i (univS (q+1))`
(face of the universal simplex = coface of the universal simplex) is a `stdSimplex.objEquiv`
computation, and `chainComplexMap_id`/the generator lemmas of `AWAux.lean` handle the rest.

### Cycle condition

With the level/successor formulation this is the routine `D² = 0` computation:
expand `dfc`, apply `d` (`map_sub`, `map_sum`, `map_zsmul`), use the `Em`-boundary identity
above, the recursion equations one level below, the chain-map property of the cofaces
(`HomologicalComplex.Hom.comm`) and then cancel: `φφ` and `ψψ` second-order terms by
`phiSum_comp`/`psiSum_comp`, mixed terms by `psiSum_phiSum` (with the signs
`(-1)^{p-1} + (-1)^p = 0`), and the `Em` terms against the boundary identity.
-/
