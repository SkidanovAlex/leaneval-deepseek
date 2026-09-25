import Submission.NK.BrauerHasse.Hasse
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.BrauerHasse.ofLevel_zero

/-!
# The local Brauer input `H²(G_κ, ℤ/p) ≅ ℤ/p`: interface and reductions

This module is the `NK.LocalCFT` side of the local Brauer input that the sibling area
`Submission/Work/BrauerHasse/` consumes (their "input (A)": `NK.BrauerHasse.LocalFieldBrauerCyclic`
and `NK.BrauerHasse.LocalH2Input`).

## The mathematics

For a `p`-adic field `κ` with separable closure `κ'`, local class field theory gives

  `H²(G_κ, ℤ/p) ≅ ℤ/p`,   equivalently   `Br(κ)[p] ≅ ℤ/p`,

where `Br(κ) ≅ ℚ/ℤ` is the Brauer group of `κ`.  The two proofs in the literature go through Tate
local duality (`H²(κ, μ_p) ≅ ℤ/p`, the invariant map `Br(κ) ≅ ℚ/ℤ`) together with the Kummer
sequence `1 → μ_p → κ̄ˣ → κ̄ˣ → 1` and the perfect cup-product pairing
`H¹(G_κ, ℤ/p) × H¹(G_κ, μ_p) → H²(G_κ, μ_p) ≅ ℤ/p`; the trivial-coefficient statement holds for
*every* prime `p`, with no relation to the residue characteristic of `κ`.

Neither the Brauer group nor Tate duality is available in this workspace, so this module does not
*prove* the input.  What it does is

* restate it in its two halves (`NK.LocalCFT.LocalH2Cardinality`, `NK.LocalCFT.LocalH2Nonvanishing`)
  and identify them with the sibling's `NK.BrauerHasse.LocalFieldBrauerCyclic`
  (`NK.LocalCFT.localFieldBrauerCyclic_iff`), so that a caller can supply either form;
* reduce the **non-vanishing half** — the only half the Neukirch–Uchida argument consumes, see
  `NK.BrauerHasse.exists_loc_ne_zero` — to a statement about a *single finite level* of the
  defining colimit (`NK.LocalCFT.localH2Nonvanishing_iff_finiteLevel`), i.e. to a statement about
  `H²(Gal(L/κ), ℤ/p)` for one finite Galois extension `L/κ`;
* record the *necessary* condition that the level class be non-zero
  (`NK.LocalCFT.exists_level_ne_zero_of_localH2Nonvanishing`), and isolate the missing
  *sufficient* direction — injectivity of the inflation maps — as the named input
  `NK.LocalCFT.InflationInjective`
  (`NK.LocalCFT.localH2Nonvanishing_of_level`);
* isolate the transport of non-vanishing from `G_κ` to a closed subgroup `H ≤ G_K` isomorphic to
  `G_κ` (which is what `NK.BrauerHasse.LocalH2Input` asks for) as the structure
  `NK.LocalCFT.ColimitTransport`, and prove that with it the sibling's `LocalH2Input` follows from
  the local non-vanishing (`NK.LocalCFT.localH2Input_of_transport`).

Every theorem in this file is proved; the definitions are the named classical inputs.
-/

open CategoryTheory

universe u

namespace NK.LocalCFT

/-- **The non-vanishing half of the local Brauer computation**: `H²(G_κ, ℤ/p)` has a non-zero
element, where `G_κ = Gal(κ'/κ)`.  Classically this is `Br(κ)[p] ≅ ℤ/p`. -/
def LocalH2Nonvanishing (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∃ x : NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p ⊤, x ≠ 0

/-- **The cardinality half of the local Brauer computation**: `H²(G_κ, ℤ/p)` is in bijection with
`ℤ/p` (in particular it has exactly `p` elements). -/
def LocalH2Cardinality (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  Nonempty (NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p ⊤ ≃ NK.BrauerHasse.Coeff.{u} p)

/-- The sibling's `NK.BrauerHasse.LocalFieldBrauerCyclic` is exactly the conjunction of the two
halves above. -/
theorem localFieldBrauerCyclic_iff {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] :
    NK.BrauerHasse.LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p ↔
      LocalH2Cardinality p κ κ' ∧ LocalH2Nonvanishing p κ κ' :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The non-vanishing of `H²(G_κ, ℤ/p)` is a statement about a single finite level of the colimit:
every class is the inflation of a class of `H²(Gal(L/κ), ℤ/p)` for some finite Galois extension
`L/κ` (a `FiniteGaloisIntermediateField κ κ'`). -/
theorem localH2Nonvanishing_iff_finiteLevel {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] :
    LocalH2Nonvanishing p κ κ' ↔
      ∃ (L : FiniteGaloisIntermediateField κ κ')
        (a : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ L),
        NK.BrauerHasse.H2Profinite.ofLevel L a ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective x
    exact ⟨L, a, hx⟩
  · rintro ⟨L, a, ha⟩
    exact ⟨NK.BrauerHasse.H2Profinite.ofLevel L a, ha⟩

/-- **A necessary condition**: a non-zero class of the colimit `H²(G_κ, ℤ/p)` has a non-zero
representative at some finite level.  (The easy direction; it uses
`NK.BrauerHasse.ofLevel_zero`.) -/
theorem exists_level_ne_zero_of_localH2Nonvanishing {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ']
    [Algebra κ κ'] [IsSepClosure κ κ'] (h : LocalH2Nonvanishing p κ κ') :
    ∃ (L : FiniteGaloisIntermediateField κ κ')
      (a : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ L), a ≠ 0 := by
  obtain ⟨L, a, ha⟩ := localH2Nonvanishing_iff_finiteLevel.mp h
  exact ⟨L, a, fun h0 => ha (by rw [h0, NK.BrauerHasse.ofLevel_zero])⟩

/-- **The missing sufficient direction, isolated as an input**: the inflation maps of the defining
colimit of `H²(G_κ, ℤ/p)` are injective, i.e. a non-zero class of a finite level
`H²(Gal(L/κ), ℤ/p)` stays non-zero after inflating to every larger finite Galois level.

Classically this is the injectivity of inflation `H²(G/N, (ℤ/p)^N) → H²(G, ℤ/p)` for the kernel `N`,
which holds as soon as `H¹(N, ℤ/p) = 0`; it is the first half of the inflation–restriction exact
sequence, and it is *not* available in Mathlib. -/
def InflationInjective (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (L : FiniteGaloisIntermediateField κ κ')
    (a : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ L),
    a ≠ 0 → NK.BrauerHasse.H2Profinite.ofLevel L a ≠ 0

/-- With injectivity of inflation, non-vanishing at a *finite level* implies non-vanishing of
`H²(G_κ, ℤ/p)`.  Combined with `NK.LocalCFT.localH2Nonvanishing_iff_finiteLevel` this shows that
the local Brauer non-vanishing is *equivalent* to the existence of a finite Galois extension `L/κ`
with `H²(Gal(L/κ), ℤ/p) ≠ 0` — the form in which the classical Kummer/Tate-duality computation
produces it. -/
theorem localH2Nonvanishing_of_level {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (hinj : InflationInjective p κ κ')
    (h : ∃ (L : FiniteGaloisIntermediateField κ κ')
      (a : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ L), a ≠ 0) :
    LocalH2Nonvanishing p κ κ' := by
  classical
  obtain ⟨L, a, ha⟩ := h
  exact ⟨NK.BrauerHasse.H2Profinite.ofLevel L a, hinj L a ha⟩

/-- **The local Brauer input in its sharpest finite form**: a *surviving* class.

There is a finite Galois extension `L/κ` and a non-zero class `a ∈ H²(Gal(L/κ), ℤ/p)` whose image
under every inflation to a larger finite Galois level `L' ⊇ L` is again non-zero.

By `NK.LocalCFT.localH2Nonvanishing_iff_surviving` this is *equivalent* to
`NK.LocalCFT.LocalH2Nonvanishing p κ κ'` (i.e. to `H²(G_κ, ℤ/p) ≠ 0`), but it is a statement
about *finite* group cohomology only, and it is the form in which the classical proof produces the
input.

Warning (this is the crux of the classical theorem, not a formality): the naive candidate — the
fundamental class of a degree-`p` *cyclic* level `L/κ` (whose existence follows from the unramified
degree-`p` extension, or from the existence theorem of local class field theory) — does *not*
survive: its inflation to the degree-`p²` level dies, because the cyclic extension
`1 → ℤ/p → ℤ/p² → ℤ/p → 1` classified by that class splits after pullback along
`C_{p²} ↠ C_p` (for `p = 2` this is the explicit computation that the "carry" cocycle on `C_2`
becomes a coboundary on `C_4`).  The classical proof (Tate local duality, equivalently the
Demushkin presentation of the maximal pro-`p` quotient of `G_κ`) produces instead the class of the
*relation* of `G_κ^{(p)}`, which survives.  See `README.md` §4. -/
def SurvivingH2Class (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∃ (L : FiniteGaloisIntermediateField κ κ')
    (a : NK.BrauerHasse.LevelH2 (K := κ) (K' := κ') p ⊤ L),
    a ≠ 0 ∧ ∀ (L' : FiniteGaloisIntermediateField κ κ') (h : L ≤ L'),
      (NK.BrauerHasse.levelMap p (U := ⊤) h) a ≠ 0

/-- **The transport input** of the local Brauer computation from the local field itself to a closed
subgroup `H ≤ G_K` of the absolute Galois group of a number field `K` which is isomorphic to
`G_κ = Gal(κ'/κ)`.

Classically the isomorphism `H ≃* Gal(κ'/κ)` of profinite groups matches the open subgroups of `H`
with the open subgroups of `G_κ` (via the Galois correspondence on both sides), so it induces a
bijection of the defining colimits `H²(H, ℤ/p) ≅ H²(G_κ, ℤ/p)`.  Formalising this requires the
Galois correspondence for `K'/K` in the vocabulary of the colimit
`NK.BrauerHasse.H2Profinite`, which is what is isolated here. -/
structure ColimitTransport (p : ℕ) (K K' κ κ' : Type u) [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] where
  /-- the comparison map from the local cohomology to the cohomology of `H` -/
  map : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Nonempty (H ≃* Gal(κ'/κ)) →
    NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p ⊤ → NK.BrauerHasse.H2Profinite p H
  /-- it maps the zero class to the zero class -/
  map_zero : ∀ (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : Nonempty (H ≃* Gal(κ'/κ))),
    map H hH e 0 =
      (NK.BrauerHasse.H2Profinite.ofLevel (K := K) (K' := K') (p := p) (U := H) ⊥
        (0 : NK.BrauerHasse.LevelH2 (K := K) (K' := K') p H ⊥))
  /-- it detects non-zero classes -/
  map_ne_zero : ∀ (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (e : Nonempty (H ≃* Gal(κ'/κ))) (x : NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p ⊤),
    x ≠ 0 → map H hH e x ≠ 0

/-- **`NK.BrauerHasse.LocalH2Input` from the local non-vanishing and the transport input.**  This
is the exact form in which the sibling area consumes the local Brauer computation. -/
theorem localH2Input_of_transport {p : ℕ} {K K' κ κ' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (htransport : ColimitTransport p K K' κ κ')
    (h : LocalH2Nonvanishing p κ κ') :
    NK.BrauerHasse.LocalH2Input p K K' κ κ' := by
  intro H hH hκ
  obtain ⟨x, hx⟩ := h
  exact ⟨htransport.map H hH hκ x, htransport.map_ne_zero H hH hκ x hx⟩

end NK.LocalCFT
