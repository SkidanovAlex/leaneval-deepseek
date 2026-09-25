/-
Copyright: the martinet_totally_real_towers team.

# The twisted product attached to a factor system, and the monodromy defect

Let `G` be a topological group, `M` a discrete `G`-module and `z : G × G → M` a `2`-cocycle
(`Work.ConCohomology.IsCocycle2`).  The **twisted product** `M × G` with the multiplication

`twistMul z (m, g) (m', g') = (m + g • m' + z (g, g'), g * g')`

is the group of the extension of `G` by `M` classified by the cocycle `z` (the standard dictionary
`H²(G,M) ≅ extensions of G by M`, realised here directly on cocycles).

## The route to the target statement

For an extension `1 → N → G → Q → 1` (`E : GroupExt G Q N`) whose `N`-action on `M` is trivial
(which follows from `hcompG` and `hcompN` of the target statement), the preimage of `N` inside the
twisted product is the extension of `N` by `M` with the **trivial** action; hence, when
`H²(N,M) = 0` (`hN2`), it splits: there is `u : N → M` with

`u (n * n') = u n + u n' - z (E.i n, E.i n')`,

and `σ n := (- u n, E.i n)` (`nSect E u`) is a homomorphic section over `N` (`nSect_hom`).

Fix `x₀ : G` lifting a topological generator `q₀` of `Q`.  The **monodromy defect**

`defectElt n := σ (σn)⁻¹ * (0, x₀) * σ n * (0, x₀)⁻¹   (∈ M × 1)`,   `σn := E.conj x₀ n`,

lies in the subgroup `{(m, 1)}` (`defectElt_snd`), and its `M`-coordinate `defect E z u x₀ n` is
additive in `n` (`defect_hom`) — this is the concrete form of the **`E₂^{1,1}`-component** of the
Hochschild--Serre filtration evaluated at the generator `q₀` of `Q`.

* `hact` (the `G`-action on `H¹(N,M)` is trivial) is exactly what makes the class of `defect`
  independent of the splitting `u` (changing `u ↦ u + ψ` changes `defect` by
  `n ↦ q₀ • ψ n - ψ (σ n)`, which `conjZ1Map x₀ ψ = ψ` kills);
* `hN2` provides some `u`, and `hQ2` is what will kill the kernel of the resulting map.

## Status of the layer (built and green in this module)

`twistMul` and its full group laws, `z_one_left/right`, `z_inv_left`, cancellation, `twistInv_mul`,
`twistInv_twistMul`, `twistInv_comm`, `conj_mul`, `mPart`/`mPart_twistMul`, `nSect`, `nSect_hom`,
`phi`, `phi_mul`, `defectElt`, `defect`, `defectElt_snd`, `defectElt_eq`, `central_M`,
`central_commute`, `defectElt_commute`, `defectElt_twistMul`, and **`defect_hom`** (the monodromy
defect is additive in `n`, for a normalised cocycle `z (1,1) = 0`).

## The crux: status and the next link (pullback ⟹ inflated)

Done in this module: `conj_x0_nSect` (vanishing defect gives `(0,x₀) σ n (0,x₀)⁻¹ = σ (E.conj x₀ n)`)
and `conj_nSect_mem` (`p σ n p⁻¹ = σ (n₀ n n₀⁻¹) · (m,1)` for `p = (m₀, i n₀) ∈ π⁻¹(N)`), so that
`σ(N)·M = π⁻¹(N)` is normalised by `⟨π⁻¹(N), (0,x₀)⟩`.

**Next link** (`exists_inflated_of_vanish_defect`), in the *abstractly cyclic* case
(`hcyc' : ∀ g : G, ∃ k : ℤ, ∃ n : N, g = x₀ ^ k * E.i n`):

1. `conj_x0_pow_nSect`: iterate `conj_x0_nSect` over powers of `(0,x₀)`:
   `x̃₀^k σ n x̃₀^{-k} = σ (σ^k n)` (induction, using `twistInv_twistMul`).
2. In the case `x₀ ^ m = E.i ζ` (so that `⟨x₀⟩ ∩ N ≠ 1`), the *power defect*
   `ω := x̃₀^m · σ(ζ)⁻¹ ∈ M` measures the failure of the section to descend; the section
   `ŝ (x₀^k n) := x̃₀^k σ(n)` on the `G`-side of the normal form is a homomorphism exactly when
   `ω = 1`, and then `b := (M`-coordinate of `ŝ)` satisfies
   `z - d¹b = (the factor system of `Ĝ/σ(N)`, pulled back along `q × q`)`, i.e. `[z] ∈ im (inf₂)`.
   Concretely `Ĝ/σ(N)` is an extension of `Q` by `M` (`M ∩ σ(N) = 1`, `M·σ(N) = π⁻¹(N)`) and the
   map `Ĝ → (Ĝ/σ(N)) ×_Q G` is bijective (`surjective` on fibres because
   `P·σ(N) ⊇ M·σ(N)`), which is the pullback condition; translating it through the explicit
   twisted-product coordinates gives the cochain `b`.
3. **Density transfer** (for the target statement, where `Q` is only *topologically* cyclic): the
   equation `z - d¹b = c ∘ (q × q)` is between locally constant cochains, so (with `hcyc` and
   `N·⟨x₀⟩` dense in `G`) it suffices to verify it on the dense subgroup; constructing `b` on all
   of `G` from its values on `N·⟨x₀⟩` is the local-constancy step still to be solved.
4. With `[z] ∈ im (inf₂)` and `Subsingleton (H²(Q,M))` (so that `im (inf₂) = 0`), the map
   `Φ : H²(G,M) → H¹(N,M)` is injective, and the target statement follows (normalise `z` first via
   `defect_coboundary`, then `exists_u_of_subsingleton_H2` + `defect_hom` give the class in `H¹`).

## The crux (not yet formalised)

`ker (z ↦ [defect]) = im (inflation : H²(Q,M) → H²(G,M))`.  Constructive route, verified by hand
for `G = N * ⟨x₀⟩` (abstractly cyclic quotient): vanishing defect ⟹ `σ (N) ⊴ Ĝ` (normalised by
`P = π⁻¹ N` and by `(0,x₀)`) ⟹ `Ĝ` is the pullback along `G ↠ Q` of an extension of `Q` ⟹
`[z] ∈ im (inf)`; then `hQ2` gives the target injection.  The general (only topologically cyclic)
case needs a density/local-constancy argument on top.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.FiveTerm
import Submission.Work.ConCohomology.ker_H2Res_eq_range_tg

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ShaBoundProcyclic

open Work.ConCohomology Function

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-! ### The twisted product -/

/-- The twisted multiplication on `M × G` attached to a `2`-cochain `z`. -/
def twistMul (z : G × G → M) (p q : M × G) : M × G :=
  (p.1 + p.2 • q.1 + z (p.2, q.2), p.2 * q.2)

@[simp] lemma twistMul_fst (z : G × G → M) (p q : M × G) :
    (twistMul z p q).1 = p.1 + p.2 • q.1 + z (p.2, q.2) := rfl

@[simp] lemma twistMul_snd (z : G × G → M) (p q : M × G) :
    (twistMul z p q).2 = p.2 * q.2 := rfl

/-- The unit of the twisted product. -/
def twistOne (z : G × G → M) : M × G := (-z (1, 1), 1)

@[simp] lemma twistOne_fst (z : G × G → M) : (twistOne z).1 = -z (1, 1) := rfl

@[simp] lemma twistOne_snd (z : G × G → M) : (twistOne z).2 = 1 := rfl

/-- The inverse in the twisted product. -/
noncomputable def twistInv (z : G × G → M) (p : M × G) : M × G :=
  (p.2⁻¹ • (-z (1, 1) - p.1 - z (p.2, p.2⁻¹)), p.2⁻¹)

@[simp] lemma twistInv_fst (z : G × G → M) (p : M × G) :
    (twistInv z p).1 = p.2⁻¹ • (-z (1, 1) - p.1 - z (p.2, p.2⁻¹)) := rfl

@[simp] lemma twistInv_snd (z : G × G → M) (p : M × G) : (twistInv z p).2 = p.2⁻¹ := rfl

/-! ### The cocycle identities for the extreme variables -/

lemma z_one_left (z : G × G → M) (hz : IsCocycle2 z) (g : G) : z (1, g) = z (1, 1) := by
  have h := hz 1 1 g
  simp only [one_smul, one_mul, mul_one] at h
  simpa using sub_eq_zero.mp h

lemma z_one_right (z : G × G → M) (hz : IsCocycle2 z) (g : G) : z (g, 1) = g • z (1, 1) := by
  have h := hz g 1 1
  simp only [mul_one] at h
  have h' : g • z (1, 1) - z (g, 1) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using h
  exact (sub_eq_zero.mp h').symm

lemma z_inv_left (z : G × G → M) (hz : IsCocycle2 z) (g : G) :
    z (g⁻¹, g) = g⁻¹ • z (g, g⁻¹) - z (1, 1) + g⁻¹ • z (1, 1) := by
  have h := hz g⁻¹ g g⁻¹
  simp only [inv_mul_cancel, mul_inv_cancel] at h
  rw [z_one_left z hz, z_one_right z hz g⁻¹] at h
  have h' : -(z (g⁻¹, g) - (g⁻¹ • z (g, g⁻¹) - z (1, 1) + g⁻¹ • z (1, 1))) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  exact sub_eq_zero.mp (neg_eq_zero.mp h')

/-! ### The group laws -/

lemma twistMul_assoc (z : G × G → M) (hz : IsCocycle2 z) (p q r : M × G) :
    twistMul z (twistMul z p q) r = twistMul z p (twistMul z q r) := by
  obtain ⟨m, g⟩ := p
  obtain ⟨m', g'⟩ := q
  obtain ⟨m'', g''⟩ := r
  simp only [twistMul, Prod.mk.injEq]
  constructor
  · have h3 : z (g * g', g'') = g • z (g', g'') + z (g, g' * g'') - z (g, g') := by
      have h := hz g g' g''
      have hneg : -(z (g * g', g'') - (g • z (g', g'') + z (g, g' * g'') - z (g, g'))) = 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
      exact sub_eq_zero.mp (neg_eq_zero.mp hneg)
    rw [h3]
    simp only [smul_add, mul_smul]
    abel
  · rw [mul_assoc]

lemma twistOne_mul (z : G × G → M) (hz : IsCocycle2 z) (p : M × G) :
    twistMul z (twistOne z) p = p := by
  obtain ⟨m, g⟩ := p
  simp only [twistMul, twistOne, Prod.mk.injEq]
  rw [z_one_left z hz g]
  exact ⟨by simp, by simp⟩

lemma twistMul_one (z : G × G → M) (hz : IsCocycle2 z) (p : M × G) :
    twistMul z p (twistOne z) = p := by
  obtain ⟨m, g⟩ := p
  simp only [twistMul, twistOne, Prod.mk.injEq]
  rw [z_one_right z hz g, smul_neg]
  exact ⟨by abel, by simp⟩

lemma twistMul_inv (z : G × G → M) (hz : IsCocycle2 z) (p : M × G) :
    twistMul z p (twistInv z p) = twistOne z := by
  obtain ⟨m, g⟩ := p
  simp only [twistMul, twistInv, twistOne, Prod.mk.injEq]
  refine ⟨?_, by simp⟩
  rw [← mul_smul, mul_inv_cancel, one_smul]
  abel

lemma twistInv_mul (z : G × G → M) (hz : IsCocycle2 z) (p : M × G) :
    twistMul z (twistInv z p) p = twistOne z := by
  obtain ⟨m, g⟩ := p
  simp only [twistMul, twistInv, twistOne, Prod.mk.injEq]
  refine ⟨?_, by simp⟩
  rw [z_inv_left z hz g]
  simp only [smul_sub, smul_neg]
  abel

/-! ### Cancellation and inverses of products -/

lemma twistMul_left_cancel (z : G × G → M) (hz : IsCocycle2 z) {p q r : M × G}
    (h : twistMul z p q = twistMul z p r) : q = r := by
  have h2 := congrArg (fun x => twistMul z (twistInv z p) x) h
  simpa only [← twistMul_assoc z hz, twistInv_mul z hz, twistOne_mul z hz] using h2

lemma twistMul_right_cancel (z : G × G → M) (hz : IsCocycle2 z) {p q r : M × G}
    (h : twistMul z q p = twistMul z r p) : q = r := by
  have h2 := congrArg (fun x => twistMul z x (twistInv z p)) h
  simpa only [twistMul_assoc z hz, twistMul_inv z hz, twistMul_one z hz] using h2

/-- An element is the inverse of another when the product is the unit. -/
lemma twistInv_eq_of_mul_eq_one (z : G × G → M) (hz : IsCocycle2 z) {p q : M × G}
    (h : twistMul z p q = twistOne z) : p = twistInv z q := by
  calc p = twistMul z p (twistOne z) := (twistMul_one z hz p).symm
    _ = twistMul z p (twistMul z q (twistInv z q)) := by rw [twistMul_inv z hz q]
    _ = twistMul z (twistMul z p q) (twistInv z q) := (twistMul_assoc z hz p q _).symm
    _ = twistMul z (twistOne z) (twistInv z q) := by rw [h]
    _ = twistInv z q := twistOne_mul z hz _

/-- An element whose right product with `p` is the unit is the inverse of `p`. -/
lemma eq_twistInv_of_twistMul_eq_one (z : G × G → M) (hz : IsCocycle2 z) {p q : M × G}
    (h : twistMul z p q = twistOne z) : q = twistInv z p := by
  calc q = twistMul z (twistOne z) q := (twistOne_mul z hz q).symm
    _ = twistMul z (twistMul z (twistInv z p) p) q := by rw [twistInv_mul z hz p]
    _ = twistMul z (twistInv z p) (twistMul z p q) := twistMul_assoc z hz (twistInv z p) p q
    _ = twistMul z (twistInv z p) (twistOne z) := by rw [h]
    _ = twistInv z p := twistMul_one z hz _

/-- The inverse of a product in the twisted product. -/
lemma twistInv_twistMul (z : G × G → M) (hz : IsCocycle2 z) (p q : M × G) :
    twistInv z (twistMul z p q) = twistMul z (twistInv z q) (twistInv z p) := by
  refine (eq_twistInv_of_twistMul_eq_one z hz ?_).symm
  calc twistMul z (twistMul z p q) (twistMul z (twistInv z q) (twistInv z p))
      = twistMul z p (twistMul z q (twistMul z (twistInv z q) (twistInv z p))) :=
        twistMul_assoc z hz p q _
    _ = twistMul z p (twistMul z (twistMul z q (twistInv z q)) (twistInv z p)) := by
        rw [← twistMul_assoc z hz q (twistInv z q) (twistInv z p)]
    _ = twistMul z p (twistMul z (twistOne z) (twistInv z p)) := by rw [twistMul_inv z hz q]
    _ = twistMul z p (twistInv z p) := by rw [twistOne_mul z hz]
    _ = twistOne z := twistMul_inv z hz p

/-! ### The `M`-part of elements over `1` -/

/-- For an element with `G`-coordinate `1`, its shifted `M`-coordinate: `(m,1) * (m',1) =
(m + m' + z (1,1), 1)`, so `mPart` (and not the first coordinate) is additive. -/
def mPart (z : G × G → M) (p : M × G) : M := p.1 + z (1, 1)

lemma mPart_twistMul (z : G × G → M) {p q : M × G} (hp : p.2 = 1) (hq : q.2 = 1) :
    mPart z (twistMul z p q) = mPart z p + mPart z q := by
  obtain ⟨m, g⟩ := p
  obtain ⟨m', g'⟩ := q
  simp only at hp hq
  subst hp
  subst hq
  simp only [twistMul, mPart, one_mul, one_smul]
  abel

/-- Conjugation by a fixed element is multiplicative on `N`. -/
lemma conj_mul {G Q N : Type*} [Group G] [Group Q] [Group N] (E : GroupExt G Q N) (g : G)
    (n n' : N) : E.conj g (n * n') = E.conj g n * E.conj g n' := by
  apply E.injective_i
  simp only [E.i_conj, map_mul]
  group

/-! ### The splitting section and the monodromy defect -/

section HomDefect

variable {Q N : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
variable [DistribMulAction Q M] [DistribMulAction N M]
variable [IsDiscreteGModule Q M] [IsDiscreteGModule N M]

/-- The homomorphic section over `N` attached to a `1`-cochain `u` on `N`: `n ↦ (-u n, i n)`. -/
noncomputable def nSect (E : GroupExt G Q N) (u : N → M) (n : N) : M × G :=
  (-u n, E.i n)

/-- The element of the twisted product whose `M`-coordinate is the monodromy defect. -/
noncomputable def defectElt (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G)
    (n : N) : M × G :=
  twistMul z (twistMul z (twistMul z (twistInv z (nSect E u (E.conj x₀ n))) (0, x₀))
    (nSect E u n)) (twistInv z (0, x₀))

/-- The **monodromy defect**: the `M`-coordinate of
`σ (σn)⁻¹ * (0, x₀) * σ n * (0, x₀)⁻¹`, where `σ = nSect E u` and `σn = E.conj x₀ n`. -/
noncomputable def defect (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (n : N) : M :=
  (defectElt E z u x₀ n).1

/-- **`nSect` is a homomorphism** as soon as `u` solves the restricted factor system. -/
lemma nSect_hom (E : GroupExt G Q N) (z : G × G → M) (u : N → M)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n n' : N) :
    twistMul z (nSect E u n) (nSect E u n') = nSect E u (n * n') := by
  apply Prod.ext
  · simp only [twistMul, nSect, map_mul]
    rw [hu n n', htriv n (-u n')]
    abel
  · simp only [twistMul, nSect, map_mul]

/-- The monodromy defect lies over `1`. -/
lemma defectElt_snd (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (n : N) :
    (defectElt E z u x₀ n).2 = 1 := by
  simp only [defectElt, twistMul_snd, twistInv_snd, nSect]
  rw [E.i_conj]
  group

/-- **`M` is central in the preimage of `N`**: conjugation by `(m₀, i n)` fixes `(m, 1)` when the
`N`-action on `M` is trivial. -/
lemma central_M (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n : N) (m₀ m : M) :
    twistMul z (twistMul z (m₀, E.i n) (m, 1)) (twistInv z (m₀, E.i n)) = (m, 1) := by
  apply Prod.ext
  · simp only [twistMul, twistInv, mul_one, one_mul]
    rw [htriv n m, ← mul_smul, mul_inv_cancel, one_smul, z_one_right z hz (E.i n),
      htriv n (z (1, 1))]
    abel
  · simp only [twistMul, twistInv, mul_one]
    rw [mul_inv_cancel]

/-- Elements of `{(m,1)}` commute with elements of the preimage of `N`. -/
lemma central_commute (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n : N) (m₀ m : M) :
    twistMul z (m₀, E.i n) (m, 1) = twistMul z (m, 1) (m₀, E.i n) := by
  have h := central_M E z hz htriv n m₀ m
  have h2 := congrArg (fun x => twistMul z x (m₀, E.i n)) h
  simpa only [twistMul_assoc z hz, twistInv_mul z hz, twistMul_one z hz] using h2

/-- Conjugation by `p` is multiplicative in the twisted product. -/
lemma conj_twistMul (z : G × G → M) (hz : IsCocycle2 z) (p q r : M × G) :
    twistMul z (twistMul z p (twistMul z q r)) (twistInv z p) =
      twistMul z (twistMul z (twistMul z p q) (twistInv z p))
        (twistMul z (twistMul z p r) (twistInv z p)) := by
  apply twistMul_right_cancel z hz (p := p)
  rw [twistMul_assoc z hz (twistMul z p (twistMul z q r)) (twistInv z p) p,
    twistInv_mul z hz p, twistMul_one z hz]
  rw [twistMul_assoc z hz (twistMul z (twistMul z p q) (twistInv z p))
    (twistMul z (twistMul z p r) (twistInv z p)) p]
  rw [twistMul_assoc z hz (twistMul z p r) (twistInv z p) p, twistInv_mul z hz p,
    twistMul_one z hz]
  rw [twistMul_assoc z hz (twistMul z p q) (twistInv z p) (twistMul z p r)]
  rw [← twistMul_assoc z hz (twistInv z p) p r, twistInv_mul z hz p, twistOne_mul z hz]
  rw [← twistMul_assoc z hz p q r]

/-- The conjugated section `(0, x₀) * σ n * (0, x₀)⁻¹`. -/
noncomputable def phi (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (n : N) : M × G :=
  twistMul z (twistMul z (0, x₀) (nSect E u n)) (twistInv z (0, x₀))

/-- `defectElt` is `σ (σn)⁻¹` times the conjugated section. -/
lemma defectElt_eq (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M)
    (x₀ : G) (n : N) :
    defectElt E z u x₀ n =
      twistMul z (twistInv z (nSect E u (E.conj x₀ n))) (phi E z u x₀ n) := by
  simp only [defectElt, phi, twistMul_assoc z hz]

/-- The conjugated section is multiplicative. -/
lemma phi_mul (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n n' : N) :
    phi E z u x₀ (n * n') = twistMul z (phi E z u x₀ n) (phi E z u x₀ n') := by
  have h2 : nSect E u (n * n') = twistMul z (nSect E u n) (nSect E u n') :=
    (nSect_hom E z u hu htriv n n').symm
  simp only [phi, h2]
  exact conj_twistMul z hz (0, x₀) (nSect E u n) (nSect E u n')

/-- Inverses also commute: if `a b = b a` then `a⁻¹ b = b a⁻¹`. -/
lemma twistInv_comm (z : G × G → M) (hz : IsCocycle2 z) {a b : M × G}
    (h : twistMul z a b = twistMul z b a) :
    twistMul z (twistInv z a) b = twistMul z b (twistInv z a) := by
  have h2 := congrArg (fun x => twistMul z (twistMul z (twistInv z a) x) (twistInv z a)) h
  have key : twistMul z (twistInv z a) b = twistMul z b (twistInv z a) := by
    have h3 := h2
    rw [← twistMul_assoc z hz (twistInv z a) a b, twistInv_mul z hz a, twistOne_mul z hz] at h3
    rw [← twistMul_assoc z hz (twistInv z a) b a,
      twistMul_assoc z hz (twistMul z (twistInv z a) b) a (twistInv z a),
      twistMul_inv z hz a, twistMul_one z hz] at h3
    exact h3.symm
  exact key

/-- The monodromy defect commutes with the conjugated section. -/
lemma defectElt_commute (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M)
    (x₀ : G) (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n n' : N) :
    twistMul z (twistInv z (nSect E u (E.conj x₀ n'))) (defectElt E z u x₀ n) =
      twistMul z (defectElt E z u x₀ n) (twistInv z (nSect E u (E.conj x₀ n'))) := by
  have hd : defectElt E z u x₀ n = (defect E z u x₀ n, 1) := by
    apply Prod.ext
    · rfl
    · exact defectElt_snd E z u x₀ n
  have h := central_commute E z hz htriv (E.conj x₀ n') (-(u (E.conj x₀ n')))
    (defect E z u x₀ n)
  rw [← hd] at h
  exact twistInv_comm z hz h

/-- **The monodromy defect is multiplicative**: the defect elements multiply. -/
lemma defectElt_twistMul (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M)
    (x₀ : G) (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n n' : N) :
    defectElt E z u x₀ (n * n') =
      twistMul z (defectElt E z u x₀ n) (defectElt E z u x₀ n') := by
  have hσ : nSect E u (E.conj x₀ (n * n')) =
      twistMul z (nSect E u (E.conj x₀ n)) (nSect E u (E.conj x₀ n')) := by
    rw [conj_mul E x₀ n n']
    exact (nSect_hom E z u hu htriv _ _).symm
  have hcom := defectElt_commute E z hz u x₀ htriv n n'
  calc defectElt E z u x₀ (n * n')
      = twistMul z (twistInv z (nSect E u (E.conj x₀ (n * n')))) (phi E z u x₀ (n * n')) :=
        defectElt_eq E z hz u x₀ (n * n')
    _ = twistMul z (twistInv z (twistMul z (nSect E u (E.conj x₀ n))
          (nSect E u (E.conj x₀ n')))) (twistMul z (phi E z u x₀ n) (phi E z u x₀ n')) := by
        rw [hσ, phi_mul E z hz u x₀ hu htriv n n']
    _ = twistMul z (twistMul z (twistInv z (nSect E u (E.conj x₀ n')))
          (twistInv z (nSect E u (E.conj x₀ n)))) (twistMul z (phi E z u x₀ n) (phi E z u x₀ n')) := by
        rw [twistInv_twistMul z hz]
    _ = twistMul z (twistMul z (twistInv z (nSect E u (E.conj x₀ n')))
          (twistMul z (twistInv z (nSect E u (E.conj x₀ n))) (phi E z u x₀ n))) (phi E z u x₀ n') := by
        simp only [twistMul_assoc z hz]
    _ = twistMul z (twistMul z (twistInv z (nSect E u (E.conj x₀ n')))
          (defectElt E z u x₀ n)) (phi E z u x₀ n') := by
        rw [← defectElt_eq E z hz u x₀ n]
    _ = twistMul z (twistMul z (defectElt E z u x₀ n)
          (twistInv z (nSect E u (E.conj x₀ n')))) (phi E z u x₀ n') := by rw [hcom]
    _ = twistMul z (defectElt E z u x₀ n)
          (twistMul z (twistInv z (nSect E u (E.conj x₀ n'))) (phi E z u x₀ n')) := by
        rw [twistMul_assoc z hz]
    _ = twistMul z (defectElt E z u x₀ n) (defectElt E z u x₀ n') := by
        rw [← defectElt_eq E z hz u x₀ n']

/-- **The monodromy defect is additive** (for a normalised cocycle, so that the `M`-coordinate itself
is additive on elements over `1`). -/
lemma defect_hom (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (hz11 : z (1, 1) = 0)
    (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n n' : N) :
    defect E z u x₀ (n * n') = defect E z u x₀ n + defect E z u x₀ n' := by
  have h := defectElt_twistMul E z hz u x₀ hu htriv n n'
  have h2 : (twistMul z (defectElt E z u x₀ n) (defectElt E z u x₀ n')).1
      = defect E z u x₀ n + defect E z u x₀ n' := by
    simp only [twistMul_fst, defectElt_snd, one_smul, hz11, add_zero]
    rfl
  show (defectElt E z u x₀ (n * n')).1 = defect E z u x₀ n + defect E z u x₀ n'
  rw [h, h2]


/-- **`hN2` provides the splitting `u`**: when `H²(N,M)` is a subsingleton, the restriction of the
factor system `z` to `N × N` is a coboundary, i.e. there is a locally constant `u : N → M` with
`u (n * n') = u n + u n' - z (E.i n, E.i n')`. -/
lemma exists_u_of_subsingleton_H2 (E : GroupExt G Q N) (z : Z2 G M)
    (hN2 : Subsingleton (H2 N M)) (hi : Continuous E.i)
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m)
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) :
    ∃ u : N → M, ∀ n n' : N, u (n * n') = u n + u n' - z.1 (E.i n, E.i n') := by
  classical
  have hres : H2Res E.i hi hcompN (H2.mk z) = 0 := Subsingleton.elim _ _
  rw [H2Res_mk, H2.mk_eq_zero_iff, mem_B2', mem_B2] at hres
  obtain ⟨u, hu⟩ := hres
  refine ⟨(u : N → M), fun n n' => ?_⟩
  have h := congrFun (congrArg (fun c : Cochain2 N M => (c : N × N → M)) hu) (n, n')
  simp only [Z2Res_coe, d1Hom_apply, cochain2Res_apply] at h
  rw [hcompN n ((u : N → M) n'), htriv n ((u : N → M) n')] at h
  have hAC : (u : N → M) n' + (u : N → M) n
      = z.1 (E.i n, E.i n') + (u : N → M) (n * n') := by
    have h0 := congrArg (fun x => x + (u : N → M) (n * n')) h
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, neg_add_cancel_comm,
      neg_add_cancel, add_neg_cancel, add_neg_cancel_comm, add_zero, zero_add] using h0
  rw [eq_sub_iff_add_eq]
  rw [add_comm ((u : N → M) (n * n')) (z.1 (E.i n, E.i n'))]
  rw [add_comm ((u : N → M) n) ((u : N → M) n')]
  exact hAC.symm
    -- **DONE (gate 1)**: `exists_u_of_subsingleton_H2` (proved in this module).
    -- **NEXT (gate 2a)**: `defect_add_psi`: changing the splitting `u ↦ u + ψ` (with `ψ` a hom
    -- `N → M`) changes the defect by `n ↦ q₀ • ψ n - ψ (σ n)`; combined with `hact`
    -- (`conjCochain x₀ ψ = ψ`, i.e. `q₀ • ψ n = ψ (σ n)`, which needs `B1' N M = 0` together with
    -- `H1.mk_eq_mk_iff`) this is zero, so `Φ` is independent of `u`.
    -- **IN PROGRESS (gate 2b)**: `defect_coboundary`.  The supporting lemmas are DONE and proved
    -- in this module: `phiCob`, `phiCob_mul` (the map `(m,g) ↦ (m + w g, g)` is a homomorphism
    -- from the `z'`-product to the `z`-product when `z' = z + d¹w`), `w_one_eq_zero` (forced by
    -- `hz11`, `hz'11`), `phiCob_one`, `phiCob_inv`, `phiCob_nSect` (`φ ∘ nSect_{u+w∘i} = nSect_u`),
    -- `phiCob_zero` (`φ (0,x₀) = (w x₀,1) * (0,x₀)`), `over_one_conj` (conjugation by an element
    -- over `1` fixes elements over `1` for normalised `z`).  REMAINING: pull `φ` inside `defectElt`
    -- with three `← phiCob_mul` and the above, move `(w x₀,1)` past the two sections with
    -- `twistInv_twistMul` + `central_commute`, cancel it with `over_one_conj`, and take
    -- `M`-coordinates (`phiCob_fst`, `defectElt_snd`, `w_one_eq_zero`).
    -- The original plan: if `z' = z + d¹w` (both normalised) then with
    -- `u' := u + w ∘ E.i` one has `defect E z' u' x₀ n = defect E z u x₀ n`, so `Φ` descends to
    -- `H²(G,M) → H¹(N,M)`.  PROOF SKETCH (worked out by hand, reviewed and confirmed by two
    -- mathematicians): let `φ (m,g) := (m + w g, g)`.  Then
    --   (i) `φ (twistMul z' p q) = twistMul z (φ p) (φ q)` by `hw` (`d1Fun w (g,h) = g•w h -
    --       w (g h) + w g`) — `φ` is a group isomorphism;
    --   (ii) `w 1 = 0` from `hz11`, `hz'11` and `hw` at `(1,1)` (`d1Fun w (1,1) = w 1`), so `φ`
    --       sends units to units and fixes elements over `1`;
    --   (iii) `φ (nSect E u' n) = nSect E u n` (the `w`-shifts cancel);
    --   (iv) `φ (0,x₀) = (w x₀, x₀) = c * twistMul z c... ` with `c := (w x₀, 1)`; since
    --       `q (E.i (σ n)) = 1`, the conjugation action of `nSect E u (E.conj x₀ n) ∈ π⁻¹(N)` on
    --       the `M`-coordinate is trivial (`central_commute` / `htriv`), and elements over `1`
    --       commute with each other for normalised `z`; hence
    --       `φ (defectElt E z' u' x₀ n) = defectElt E z u x₀ n`, and taking `M`-coordinates (with
    --       `w 1 = 0`) gives the claim.
/-! ### The isomorphism attached to a coboundary change of the factor system -/

/-- The map `(m, g) ↦ (m + w g, g)` carrying the `z'`-twisted product to the `z`-twisted one when
`z' = z + d¹ w`. -/
def phiCob (w : G → M) (p : M × G) : M × G := (p.1 + w p.2, p.2)

@[simp] lemma phiCob_fst (w : G → M) (p : M × G) : (phiCob w p).1 = p.1 + w p.2 := rfl

@[simp] lemma phiCob_snd (w : G → M) (p : M × G) : (phiCob w p).2 = p.2 := rfl

/-- `phiCob w` is a homomorphism from the `z'`-twisted product to the `z`-twisted product. -/
lemma phiCob_mul (z z' : G × G → M) (w : G → M)
    (hw : ∀ g h : G, z' (g, h) = z (g, h) + d1Fun w (g, h)) (p q : M × G) :
    twistMul z (phiCob w p) (phiCob w q) = phiCob w (twistMul z' p q) := by
  obtain ⟨m, g⟩ := p
  obtain ⟨m', g'⟩ := q
  simp only [twistMul, phiCob]
  rw [hw, d1Fun_apply]
  simp only [smul_add]
  abel

/-- `w 1 = 0` is forced by `z (1,1) = z' (1,1) = 0` and `z' = z + d¹ w`. -/
lemma w_one_eq_zero (z z' : G × G → M) (w : G → M) (hz11 : z (1, 1) = 0) (hz'11 : z' (1, 1) = 0)
    (hw : ∀ g h : G, z' (g, h) = z (g, h) + d1Fun w (g, h)) : w 1 = 0 := by
  have h := hw 1 1
  simp only [d1Fun_apply, one_smul, mul_one] at h
  rw [hz11, hz'11, zero_add] at h
  simpa using h.symm

/-- `phiCob w` sends units to units. -/
lemma phiCob_one (z z' : G × G → M) (w : G → M) (hz11 : z (1, 1) = 0) (hz'11 : z' (1, 1) = 0)
    (hw1 : w 1 = 0) : phiCob w (twistOne z') = twistOne z := by
  simp only [phiCob, twistOne, hw1, hz11, hz'11, add_zero]

/-- `phiCob w` commutes with inverses. -/
lemma phiCob_inv (z z' : G × G → M) (hz : IsCocycle2 z) (hz' : IsCocycle2 z') (w : G → M)
    (hw : ∀ g h : G, z' (g, h) = z (g, h) + d1Fun w (g, h)) (hz11 : z (1, 1) = 0)
    (hz'11 : z' (1, 1) = 0) (p : M × G) :
    phiCob w (twistInv z' p) = twistInv z (phiCob w p) := by
  have hw1 := w_one_eq_zero z z' w hz11 hz'11 hw
  refine eq_twistInv_of_twistMul_eq_one z hz (p := phiCob w p) ?_
  rw [phiCob_mul z z' w hw p (twistInv z' p), twistMul_inv z' hz',
    phiCob_one z z' w hz11 hz'11 hw1]

/-- `phiCob w` fixes the splitting sections (with the shifted `u`). -/
lemma phiCob_nSect (E : GroupExt G Q N) (u : N → M) (w : G → M) (n : N) :
    phiCob w (nSect E (fun n => u n + w (E.i n)) n) = nSect E u n := by
  simp only [phiCob, nSect]
  refine Prod.ext ?_ rfl
  show -(u n + w (E.i n)) + w (E.i n) = -u n
  abel

/-- The image of the lift `(0, x₀)` under `phiCob w`. -/
lemma phiCob_zero (z : G × G → M) (hz : IsCocycle2 z) (hz11 : z (1, 1) = 0) (w : G → M)
    (x₀ : G) : phiCob w (0, x₀) = twistMul z (w x₀, 1) (0, x₀) := by
  simp only [phiCob, twistMul, one_smul, mul_one]
  rw [z_one_left z hz x₀, hz11]
  simp

/-- Conjugation by an element over `1` fixes every element over `1` (for a normalised factor
system). -/
lemma over_one_conj (z : G × G → M) (hz11 : z (1, 1) = 0) (c : M) (p : M × G) (hp : p.2 = 1) :
    twistMul z (twistMul z (c, 1) p) (twistInv z (c, 1)) = p := by
  obtain ⟨m, g⟩ := p
  simp only at hp
  subst hp
  simp only [twistMul, twistInv, hz11, one_smul, one_mul, mul_one, inv_one, add_zero, zero_add,
    zero_sub, sub_zero, Prod.mk.injEq]
  exact ⟨by abel, trivial⟩

/-- The element-level form of the coboundary invariance of the monodromy defect. -/
lemma defect_coboundary_elt (E : GroupExt G Q N) (z z' : G × G → M) (hz : IsCocycle2 z)
    (hz' : IsCocycle2 z') (hz11 : z (1, 1) = 0) (hz'11 : z' (1, 1) = 0) (w : G → M)
    (hw : ∀ g h : G, z' (g, h) = z (g, h) + d1Fun w (g, h)) (u : N → M) (x₀ : G)
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n : N) :
    phiCob w (defectElt E z' (fun n => u n + w (E.i n)) x₀ n)
      = twistMul z (twistMul z (w x₀, 1) (defectElt E z u x₀ n)) (twistInv z (w x₀, 1)) := by
  set A : M × G := nSect E u (E.conj x₀ n) with hAdef
  set B : M × G := nSect E u n with hBdef
  set c : M × G := (w x₀, (1 : G)) with hcdef
  set xt : M × G := ((0 : M), x₀) with hxdef
  have hcommA : twistMul z A c = twistMul z c A := by
    rw [hAdef, hcdef]
    exact central_commute E z hz htriv (E.conj x₀ n) (-(u (E.conj x₀ n))) (w x₀)
  have hcommB : twistMul z B c = twistMul z c B := by
    rw [hBdef, hcdef]
    exact central_commute E z hz htriv n (-(u n)) (w x₀)
  have hcommA' : twistMul z (twistInv z A) c = twistMul z c (twistInv z A) :=
    twistInv_comm z hz hcommA
  have hφ : phiCob w (defectElt E z' (fun n => u n + w (E.i n)) x₀ n)
      = twistMul z (twistMul z (twistMul z (twistInv z A) (twistMul z c xt)) B)
          (twistInv z (twistMul z c xt)) := by
    rw [hAdef, hBdef, hcdef, hxdef]
    simp only [defectElt]
    rw [← phiCob_mul z z' w hw, ← phiCob_mul z z' w hw, ← phiCob_mul z z' w hw,
      phiCob_inv z z' hz hz' w hw hz11 hz'11, phiCob_inv z z' hz hz' w hw hz11 hz'11,
      phiCob_nSect E u w, phiCob_nSect E u w, phiCob_zero z hz hz11 w x₀]
  rw [hφ, twistInv_twistMul z hz c xt, ← twistMul_assoc z hz (twistInv z A) c xt, hcommA',
    twistMul_assoc z hz c (twistInv z A) xt]
  simp only [defectElt]
  rw [← hAdef, ← hBdef, ← hxdef]
  simp only [twistMul_assoc z hz]

/-- **Gate 2b**: the monodromy defect is unchanged by a coboundary change of the factor system
(with the correspondingly shifted splitting). -/
theorem defect_coboundary (E : GroupExt G Q N) (z z' : G × G → M)
    (hz : IsCocycle2 z) (hz' : IsCocycle2 z')
    (hz11 : z (1, 1) = 0) (hz'11 : z' (1, 1) = 0) (w : G → M)
    (hw : ∀ g h : G, z' (g, h) = z (g, h) + d1Fun w (g, h))
    (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m) (n : N) :
    defect E z' (fun n => u n + w (E.i n)) x₀ n = defect E z u x₀ n := by
  have hw1 := w_one_eq_zero z z' w hz11 hz'11 hw
  have key := defect_coboundary_elt E z z' hz hz' hz11 hz'11 w hw u x₀ htriv n
  have hconj := over_one_conj z hz11 (w x₀) (defectElt E z u x₀ n) (defectElt_snd E z u x₀ n)
  rw [hconj] at key
  show (defectElt E z' (fun n => u n + w (E.i n)) x₀ n).1 = (defectElt E z u x₀ n).1
  have h := congrArg Prod.fst key
  simpa only [phiCob_fst, defectElt_snd, hw1, add_zero] using h

/-! ### Gate 3, first link: vanishing defect and the normality of the splitting sections -/

/-- **Vanishing defect ⟹ equivariance**: conjugation by `(0, x₀)` sends the splitting section to
the splitting section of the conjugated element. -/
lemma conj_x0_nSect (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) (n : N) :
    twistMul z (twistMul z (0, x₀) (nSect E u n)) (twistInv z (0, x₀))
      = nSect E u (E.conj x₀ n) := by
  set A : M × G := nSect E u (E.conj x₀ n) with hAdef
  set B : M × G := nSect E u n with hBdef
  set xt : M × G := (0, x₀) with hxdef
  have hdefA : (defectElt E z u x₀ n).1 = 0 := hdef n
  have h2 : (defectElt E z u x₀ n).2 = 1 := defectElt_snd E z u x₀ n
  simp only [defectElt] at hdefA h2
  have hE : twistMul z (twistMul z (twistMul z (twistInv z A) xt) B) (twistInv z xt)
      = twistOne z := by
    apply Prod.ext
    · rw [hdefA]
      simp [twistOne, hz11]
    · rw [h2]
      simp [twistOne]
  rw [hAdef] at hE
  -- hE : ((A⁻¹ * xt) * B) * xt⁻¹ = twistOne z
  have h3 : twistMul z A (twistMul z (twistMul z (twistMul z (twistInv z A) xt) B) (twistInv z xt))
      = twistMul z A (twistOne z) := by rw [hE]
  simpa only [← twistMul_assoc z hz, twistMul_inv z hz, twistOne_mul z hz, twistMul_one z hz]
    using h3

/-- Bookkeeping: the `G`-coordinate of the conjugate of a splitting section by `(m₀, i n₀)`. -/
lemma snd_conj_nSect (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (m₀ : M) (n₀ n : N) :
    (twistMul z (twistMul z (m₀, E.i n₀) (nSect E u n)) (twistInv z (m₀, E.i n₀))).2
      = E.i (n₀ * n * n₀⁻¹) := by
  simp only [twistMul_snd, twistInv_snd, nSect]
  rw [map_mul, map_mul, map_inv]

/-- Every element of the twisted product lying over `1` is of the form `(m, 1)`. -/
lemma eq_mElt_of_snd_eq_one {p : M × G} (hp : p.2 = 1) : p = (p.1, 1) := by
  obtain ⟨m, g⟩ := p
  simp only at hp
  subst hp
  rfl

/-- **Vanishing defect ⟹ normality in the preimage of `N`**: conjugation by `p = (m₀, i n₀) ∈ P`
sends `σ n` to `σ (n₀ * n * n₀⁻¹)` times an element of `M` (i.e. `σ (N)` is normalised by `P` up to
the central subgroup `M`). -/
lemma conj_nSect_mem (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M)
    (m₀ : M) (n₀ n : N) :
    ∃ m : M, twistMul z (twistMul z (m₀, E.i n₀) (nSect E u n)) (twistInv z (m₀, E.i n₀))
      = twistMul z (nSect E u (n₀ * n * n₀⁻¹)) (m, 1) := by
  set σc : M × G := nSect E u (n₀ * n * n₀⁻¹) with hσ
  set p : M × G := twistMul z (twistMul z (m₀, E.i n₀) (nSect E u n)) (twistInv z (m₀, E.i n₀))
    with hp
  have hq : (twistMul z (twistInv z σc) p).2 = 1 := by
    rw [twistMul_snd, twistInv_snd, hp, hσ, snd_conj_nSect]
    simp only [nSect, inv_mul_cancel]
  refine ⟨(twistMul z (twistInv z σc) p).1, ?_⟩
  have hpq := eq_mElt_of_snd_eq_one hq
  calc p = twistMul z (twistOne z) p := (twistOne_mul z hz p).symm
    _ = twistMul z (twistMul z σc (twistInv z σc)) p := by rw [twistMul_inv z hz σc]
    _ = twistMul z σc (twistMul z (twistInv z σc) p) := twistMul_assoc z hz σc _ p
    _ = twistMul z σc ((twistMul z (twistInv z σc) p).1, 1) := by rw [hpq]

/-! ### Iterating the equivariance -/

/-- The inverse of the unit is the unit. -/
lemma twistInv_twistOne (z : G × G → M) (hz : IsCocycle2 z) :
    twistInv z (twistOne z) = twistOne z := by
  symm
  refine eq_twistInv_of_twistMul_eq_one z hz (p := twistOne z) (q := twistOne z) ?_
  rw [twistOne_mul z hz]

/-- Conjugation by a product is the composite of the conjugations. -/
lemma conj_twistMul_twistMul (z : G × G → M) (hz : IsCocycle2 z) (p q R : M × G) :
    twistMul z (twistMul z (twistMul z p q) R) (twistInv z (twistMul z p q))
      = twistMul z (twistMul z p (twistMul z (twistMul z q R) (twistInv z q))) (twistInv z p) := by
  rw [twistInv_twistMul z hz]
  simp only [twistMul_assoc z hz]

/-- Iterating: `f^[k] ∘ f = f^[k+1]`. -/
lemma iterate_succ_comp (f : N → N) (k : ℕ) : f^[k] ∘ f = f^[k+1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ (f := f) (n := k), Function.iterate_succ (f := f) (n := k + 1), ih]

/-- **Iterated equivariance**: when the monodromy defect vanishes, conjugation by the `k`-th power
of `(0, x₀)` acts on the splitting section by the `k`-fold conjugation on `N`. -/
lemma conj_x0_pow_nSect (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) :
    ∀ k : ℕ, ∀ n : N,
      twistMul z (twistMul z (((fun q => twistMul z q (0, x₀))^[k]) (twistOne z)) (nSect E u n))
        (twistInv z (((fun q => twistMul z q (0, x₀))^[k]) (twistOne z)))
      = nSect E u ((E.conj x₀)^[k] n) := by
  intro k
  induction k with
  | zero =>
      intro n
      simp only [Function.iterate_zero, id_eq]
      rw [twistOne_mul z hz, twistInv_twistOne z hz, twistMul_one z hz]
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply']
      rw [conj_twistMul_twistMul z hz]
      rw [conj_x0_nSect E z hz hz11 u x₀ hdef]
      rw [ih]
      have hcomp := congrFun (iterate_succ_comp (E.conj x₀) k) n
      simpa only [Function.comp_apply] using congrArg (fun x => nSect E u x) hcomp

/-! ### The lift powers and the power defect -/

/-- The `k`-th power of the lift `(0, x₀)` in the twisted product. -/
def x0pow (z : G × G → M) (x₀ : G) : ℕ → M × G
  | 0 => twistOne z
  | (k + 1) => twistMul z (x0pow z x₀ k) (0, x₀)

@[simp] lemma x0pow_zero (z : G × G → M) (x₀ : G) : x0pow z x₀ 0 = twistOne z := rfl

@[simp] lemma x0pow_succ (z : G × G → M) (x₀ : G) (k : ℕ) :
    x0pow z x₀ (k + 1) = twistMul z (x0pow z x₀ k) (0, x₀) := rfl

/-- The `G`-coordinate of `x0pow`. -/
lemma x0pow_snd (z : G × G → M) (x₀ : G) (k : ℕ) : (x0pow z x₀ k).2 = x₀ ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [x0pow_succ, ih, pow_succ]

/-- **Iterated equivariance** (in terms of `x0pow`). -/
lemma conj_x0pow_nSect (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) (k : ℕ) :
    ∀ n : N, twistMul z (twistMul z (x0pow z x₀ k) (nSect E u n)) (twistInv z (x0pow z x₀ k))
      = nSect E u ((E.conj x₀)^[k] n) := by
  induction k with
  | zero =>
      intro n
      simp only [x0pow_zero, Function.iterate_zero, id_eq]
      rw [twistOne_mul z hz, twistInv_twistOne z hz, twistMul_one z hz]
  | succ k ih =>
      intro n
      rw [x0pow_succ, conj_twistMul_twistMul z hz]
      rw [conj_x0_nSect E z hz hz11 u x₀ hdef]
      rw [ih]
      have hcomp := congrFun (iterate_succ_comp (E.conj x₀) k) n
      simpa only [Function.comp_apply] using congrArg (fun x => nSect E u x) hcomp

/-- The **power defect**: the failure of `x₀ ^ m` (when it lies in `N`) to be matched by the `m`-th
power of the lift `(0, x₀)` (i.e. the defect of the normal-form section at the relator `x₀ ^ m`). -/
noncomputable def powerDefect (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (m : ℕ) (ζ : N) :
    M × G :=
  twistMul z (x0pow z x₀ m) (twistInv z (nSect E u ζ))

@[simp] lemma powerDefect_def (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (m : ℕ)
    (ζ : N) :
    powerDefect E z u x₀ m ζ = twistMul z (x0pow z x₀ m) (twistInv z (nSect E u ζ)) := rfl

/-- The power defect lies over `1` whenever `x₀ ^ m = E.i ζ`. -/
lemma powerDefect_snd (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G) (m : ℕ) (ζ : N)
    (hpow : x₀ ^ m = E.i ζ) : (powerDefect E z u x₀ m ζ).2 = 1 := by
  rw [powerDefect_def, twistMul_snd, twistInv_snd, x0pow_snd, nSect, hpow, mul_inv_cancel]

/-- The power defect vanishes exactly when the `m`-th power of the lift is the splitting section at
`ζ` — i.e. exactly when the normal-form section is well defined at the relator `x₀ ^ m`. -/
lemma powerDefect_eq_one_iff (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z) (u : N → M)
    (x₀ : G) (m : ℕ) (ζ : N) :
    powerDefect E z u x₀ m ζ = twistOne z ↔ x0pow z x₀ m = nSect E u ζ := by
  rw [powerDefect_def]
  constructor
  · intro h
    have h' : twistMul z (twistMul z (x0pow z x₀ m) (twistInv z (nSect E u ζ))) (nSect E u ζ)
        = twistMul z (twistOne z) (nSect E u ζ) := by rw [h]
    simpa only [twistMul_assoc z hz, twistInv_mul z hz, twistMul_one z hz, twistOne_mul z hz]
      using h'
  · intro h
    rw [h, twistMul_inv z hz]

/-- Inserting and deleting `1 = P⁻¹ P` inside a product. -/
lemma twistMul_conj_cancel (z : G × G → M) (hz : IsCocycle2 z) (P X Q : M × G) :
    twistMul z (twistMul z (twistMul z P X) (twistInv z P)) (twistMul z P Q)
      = twistMul z (twistMul z P X) Q := by
  rw [← twistMul_assoc z hz _ P Q, twistMul_assoc z hz (twistMul z P X) (twistInv z P) P,
    twistInv_mul z hz, twistMul_one z hz]

/-- The power law for `x0pow`. -/
lemma x0pow_add (z : G × G → M) (hz : IsCocycle2 z) (x₀ : G) (k j : ℕ) :
    x0pow z x₀ (k + j) = twistMul z (x0pow z x₀ k) (x0pow z x₀ j) := by
  induction j with
  | zero => simp [twistMul_one z hz]
  | succ j ih =>
      rw [Nat.add_succ, x0pow_succ, ih, x0pow_succ, twistMul_assoc z hz]

/-- On the normal form `n · x₀ ^ k` the section `(n, k) ↦ σ n · x0pow z x₀ k` is multiplicative,
with the conjugation action of `x₀ ^ k` on the `N`-coordinate. -/
lemma normalForm_mul (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) (k j : ℕ) (n n' : N) :
    twistMul z (twistMul z (nSect E u n) (x0pow z x₀ k))
        (twistMul z (nSect E u n') (x0pow z x₀ j))
      = twistMul z (nSect E u (n * (E.conj x₀)^[k] n')) (x0pow z x₀ (k + j)) := by
  have hmid : twistMul z (twistMul z (x0pow z x₀ k) (nSect E u n')) (x0pow z x₀ j)
      = twistMul z (twistMul z (nSect E u ((E.conj x₀)^[k] n')) (x0pow z x₀ k))
          (x0pow z x₀ j) := by
    calc twistMul z (twistMul z (x0pow z x₀ k) (nSect E u n')) (x0pow z x₀ j)
        = twistMul z (twistMul z (twistMul z (x0pow z x₀ k) (nSect E u n'))
            (twistInv z (x0pow z x₀ k)))
            (twistMul z (x0pow z x₀ k) (x0pow z x₀ j)) :=
          (twistMul_conj_cancel z hz (x0pow z x₀ k) (nSect E u n') (x0pow z x₀ j)).symm
      _ = twistMul z (nSect E u ((E.conj x₀)^[k] n'))
            (twistMul z (x0pow z x₀ k) (x0pow z x₀ j)) := by
          rw [conj_x0pow_nSect E z hz hz11 u x₀ hdef k n']
      _ = twistMul z (twistMul z (nSect E u ((E.conj x₀)^[k] n')) (x0pow z x₀ k))
            (x0pow z x₀ j) := (twistMul_assoc z hz _ _ _).symm
  rw [twistMul_assoc z hz]
  rw [← twistMul_assoc z hz (x0pow z x₀ k) (nSect E u n') (x0pow z x₀ j)]
  rw [hmid]
  rw [twistMul_assoc z hz (nSect E u ((E.conj x₀)^[k] n')) (x0pow z x₀ k) (x0pow z x₀ j)]
  rw [← x0pow_add z hz x₀ k j]
  rw [← twistMul_assoc z hz (nSect E u n) (nSect E u ((E.conj x₀)^[k] n')) (x0pow z x₀ (k + j))]
  rw [nSect_hom E z u hu htriv]

/-- The lift power commutes with the sections, up to the conjugation on `N`. -/
lemma x0pow_nSect_comm (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) (k : ℕ) (n : N) :
    twistMul z (x0pow z x₀ k) (nSect E u n)
      = twistMul z (nSect E u ((E.conj x₀)^[k] n)) (x0pow z x₀ k) := by
  have h := conj_x0pow_nSect E z hz hz11 u x₀ hdef k n
  have h2 := congrArg (fun x => twistMul z x (x0pow z x₀ k)) h
  simpa only [twistMul_assoc z hz, twistInv_mul z hz, twistMul_one z hz] using h2

/-- **The reduction step for the normal form**: if `x₀ ^ m = E.i ζ` and the power defect at `(m, ζ)`
vanishes, then the two decompositions `n · x₀ ^ (k + m)` and `(n · conj^k ζ) · x₀ ^ k` of the same
element of `G` receive the same value under the section `n ↦ σ n · x0pow`. -/
lemma nSect_x0pow_step (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) {m : ℕ} {ζ : N}
    (hm : powerDefect E z u x₀ m ζ = twistOne z) (k : ℕ) (n : N) :
    twistMul z (nSect E u n) (x0pow z x₀ (k + m))
      = twistMul z (nSect E u (n * (E.conj x₀)^[k] ζ)) (x0pow z x₀ k) := by
  rw [x0pow_add z hz x₀ k m, (powerDefect_eq_one_iff E z hz u x₀ m ζ).mp hm,
    x0pow_nSect_comm E z hz hz11 u x₀ hdef k ζ,
    ← twistMul_assoc z hz (nSect E u n) (nSect E u ((E.conj x₀)^[k] ζ)) (x0pow z x₀ k),
    nSect_hom E z u hu htriv]

/-! ### The section on decompositions, and the iteration of the reduction step -/

/-- The value of the normal-form section on a *decomposition* `n · x₀ ^ k`. -/
noncomputable def sectVal (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G)
    (p : N × ℕ) : M × G :=
  twistMul z (nSect E u p.1) (x0pow z x₀ p.2)

/-- The `N`-adjustment produced by `t` successive relator reductions, in the order in which the
reductions produce it: `conj^{k+(t-1)m} ζ · … · conj^{k+m} ζ · conj^k ζ`. -/
noncomputable def relProd (E : GroupExt G Q N) (x₀ : G) (ζ : N) (m : ℕ) (k : ℕ) : ℕ → N
  | 0 => 1
  | (t + 1) => (E.conj x₀)^[k + t * m] ζ * relProd E x₀ ζ m k t

@[simp] lemma relProd_zero (E : GroupExt G Q N) (x₀ : G) (ζ : N) (m k : ℕ) :
    relProd E x₀ ζ m k 0 = 1 := rfl

@[simp] lemma relProd_succ (E : GroupExt G Q N) (x₀ : G) (ζ : N) (m k t : ℕ) :
    relProd E x₀ ζ m k (t + 1) = (E.conj x₀)^[k + t * m] ζ * relProd E x₀ ζ m k t := rfl

/-- **Iterating the reduction step**: `t` successive relator reductions change the decomposition
`n · x₀ ^ (k + t·m)` into `(n · ∏ conj) · x₀ ^ k` without changing the section value. -/
lemma nSect_x0pow_step_iter (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) {m : ℕ} {ζ : N}
    (hm : powerDefect E z u x₀ m ζ = twistOne z) (t k : ℕ) :
    ∀ n : N, sectVal E z u x₀ (n, k + t * m)
      = sectVal E z u x₀ (n * relProd E x₀ ζ m k t, k) := by
  induction t with
  | zero => intro n; simp [relProd, sectVal]
  | succ t ih =>
      intro n
      rw [show k + (t + 1) * m = (k + t * m) + m from by ring]
      rw [relProd_succ]
      simp only [sectVal]
      rw [nSect_x0pow_step E z hz hz11 u x₀ hu htriv hdef hm (k + t * m) n]
      have hih := ih (n * (E.conj x₀)^[k + t * m] ζ)
      simp only [sectVal] at hih
      rw [hih]
      simp only [mul_assoc]

/-- **Decomposition independence of the section value**, reduced to the structure of the relations of
the abstractly-cyclic extension: if every equality of two decompositions `n · x₀ ^ k = n' · x₀ ^ k'`
is produced by the relator `x₀ ^ m = E.i ζ` (i.e. `k' = k + t·m` with the `N`-parts reconciled by
`relProd`), then the section value only depends on the element of `G`. -/
theorem sectVal_eq_of_eq (E : GroupExt G Q N) (z : G × G → M) (hz : IsCocycle2 z)
    (hz11 : z (1, 1) = 0) (u : N → M) (x₀ : G)
    (hu : ∀ n n' : N, u (n * n') = u n + u n' - z (E.i n, E.i n'))
    (htriv : ∀ (n : N) (m : M), E.i n • m = m)
    (hdef : ∀ n : N, defect E z u x₀ n = 0) {m : ℕ} {ζ : N}
    (hm : powerDefect E z u x₀ m ζ = twistOne z)
    (hrel : ∀ (n n' : N) (k k' : ℕ), E.i n * x₀ ^ k = E.i n' * x₀ ^ k' →
      (∃ t : ℕ, k = k' + t * m ∧ n' = n * relProd E x₀ ζ m k' t) ∨
      (∃ t : ℕ, k' = k + t * m ∧ n = n' * relProd E x₀ ζ m k t))
    (n n' : N) (k k' : ℕ) (heq : E.i n * x₀ ^ k = E.i n' * x₀ ^ k') :
    sectVal E z u x₀ (n, k) = sectVal E z u x₀ (n', k') := by
  rcases hrel n n' k k' heq with ⟨t, hk, hn⟩ | ⟨t, hk, hn⟩
  · subst hk
    subst hn
    rw [nSect_x0pow_step_iter E z hz hz11 u x₀ hu htriv hdef hm t k' n]
  · subst hk
    subst hn
    rw [← nSect_x0pow_step_iter E z hz hz11 u x₀ hu htriv hdef hm t k n']

/-- The section `G → Ĝ` obtained from a choice of decomposition `g = E.i n · x₀ ^ k`. -/
noncomputable def normalFormSect (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G)
    (hcyc : ∀ g : G, ∃ p : N × ℕ, g = E.i p.1 * x₀ ^ p.2) (g : G) : M × G :=
  sectVal E z u x₀ (Classical.choose (hcyc g))

/-- The chosen section is a section of `G → Ĝ` (i.e. has the right `G`-coordinate). -/
lemma normalFormSect_snd (E : GroupExt G Q N) (z : G × G → M) (u : N → M) (x₀ : G)
    (hcyc : ∀ g : G, ∃ p : N × ℕ, g = E.i p.1 * x₀ ^ p.2) (g : G) :
    (normalFormSect E z u x₀ hcyc g).2 = g := by
  have hspec : normalFormSect E z u x₀ hcyc g
      = sectVal E z u x₀ (Classical.choose (hcyc g)) := rfl
  rw [hspec]
  simp only [sectVal, twistMul_snd, nSect, x0pow_snd]
  exact (Classical.choose_spec (hcyc g)).symm

end HomDefect

end Work.ShaBoundProcyclic
