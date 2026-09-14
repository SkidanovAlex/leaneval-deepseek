import Mathlib
import Submission.Vdw.LocalField.QpPadic
import Submission.Commons.Topology.Algebra.Module.eq_top_of_finiteDimensional_of_dense
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers

open scoped NumberField WithZero Valued
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

/-!
# Local-field chapter (G2(b)): `K_P` is finite-dimensional over `ℚ_[p]`

With the rebased algebra `Algebra (Padic p) (kpAdic p P)` (QpPadic) this
module proves the finiteness instance:

* `padic_smul_rat` — the scalar compatibility `(q : Padic p) • x = q • x`
  (the tower `ℚ → ℚ_[p] → K_P` makes the two module actions agree);
* `algebraMap_K_smul_rat` — the completed embedding `K → K_P` is `ℚ`-linear
  (scalar level; ring-hom + the scalar tower `ℚ → K → K_P`);
* `continuous_algebraMap_padic` / `continuousSMul_kpAdic` — the rebased
  algebraMap is continuous, so the scalar action is continuous (needed for
  the finite-dimensional-submodule closure lemma);
* **`moduleFinite_kpAdic`** — the instance
  `Module.Finite (Padic p) (kpAdic p P)`: the images of a finite `ℚ`-basis
  of `K` generate `K_P` over `ℚ_[p]` (their span is finite-dimensional, hence
  closed by `Submodule.closed_of_finiteDimensional`; it contains the dense
  image of `K` — `kpAdic_denseRange_algebraMap` — so it is all of `K_P` by
  the commons dense-submodule lemma
  `eq_top_of_finiteDimensional_of_dense`).

This is the type-level foundation for `finrank (Padic p) (kpAdic p P) = e·f`
(completion preserves ramification/inertia) and the degree corollary
`[ℚ_p(ζ):ℚ_p] = f` (G3).

(G2(b) integer level): the ℚ_p-integer ring
`QpInt p := (qprime p).adicCompletionIntegers ℚ` (ℤ_[p]), the ring hom
`qpIntToKpInt : QpInt p →+* kpInt p P` (the rebased algebraMap restricted to
the integer rings, via `algebraMap_mem_kpInt`) and the algebra structure
`kpIntAlgebraQpInt` of `kpInt p P` over `QpInt p`; the density of 𝓞K in
`kpInt p P` (fleet `ringOfIntegers_dense_in_adicIntegers`); integer scalar
compatibilities `algebraMap_QpInt_int`/`QpInt_smul_int`;
`ringOfIntegers_mem_kpInt`, the ring hom `ringOfIntegersToKpInt : 𝓞 K →+*
kpInt p P`, and **`ringOfIntegers_image_mem_QpInt_span`** — (a2) the image
of 𝓞K lies in the QpInt-span of the images of an integral ℤ-basis
(`Module.finBasis ℤ (𝓞 K)`, decomposed via `Module.Basis.sum_repr`,
`map_sum`, `map_zsmul`, `QpInt_smul_int`).  Still to build for the
integer-level finiteness `Module.Finite (QpInt p) (kpInt p P)`: (a3)
closedness of that span in `kpInt` (module topology: `ContinuousSMul
(QpInt p) (kpInt p P)` + compactness — instances do not currently
synthesize), then (a4) span = ⊤ from density, then the fraction-field rank
identity.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Scalar compatibility: the `ℚ_[p]`-scalar action and the `ℚ`-action on
`K_P` agree (the scalar tower `ℚ → ℚ_[p] → K_P`). -/
lemma padic_smul_rat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) (x : kpAdic p P) :
    (q : Padic p) • x = q • x := by
  simp [Algebra.smul_def]

/-- The completed embedding `K → K_P` is `ℚ`-linear (scalar level). -/
lemma algebraMap_K_smul_rat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) (x : K) :
    (algebraMap K (kpAdic p P)) (q • x) = q • (algebraMap K (kpAdic p P)) x := by
  calc
    (algebraMap K (kpAdic p P)) (q • x)
        = (algebraMap K (kpAdic p P)) ((algebraMap ℚ K q) * x) := by rw [Algebra.smul_def]
    _ = (algebraMap K (kpAdic p P)) (algebraMap ℚ K q) * (algebraMap K (kpAdic p P)) x := by
          rw [map_mul]
    _ = algebraMap ℚ (kpAdic p P) q * (algebraMap K (kpAdic p P)) x := by
          rw [show (algebraMap K (kpAdic p P)) (algebraMap ℚ K q) = algebraMap ℚ (kpAdic p P) q by
            exact (IsScalarTower.algebraMap_apply ℚ K (kpAdic p P) q).symm]
    _ = q • (algebraMap K (kpAdic p P)) x := by rw [Algebra.smul_def]

/-- The rebased algebraMap `ℚ_[p] → K_P` is continuous. -/
lemma continuous_algebraMap_padic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (algebraMap (Padic p) (kpAdic p P)) := by
  rw [algebraMap_eq_qpPadic p P]
  refine (continuous_qpToKp p P).comp ?_
  exact (qpPadicEquiv p).symm.continuous_toFun

/-- The `ℚ_[p]`-action on `K_P` is continuous. -/
instance continuousSMul_kpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ContinuousSMul (Padic p) (kpAdic p P) := by
  constructor
  show Continuous (fun q : (Padic p) × kpAdic p P => q.1 • q.2)
  have h : (fun q : (Padic p) × kpAdic p P => q.1 • q.2) =
      (fun z : kpAdic p P × kpAdic p P => z.1 * z.2) ∘
        (Prod.map (algebraMap (Padic p) (kpAdic p P)) (id : kpAdic p P → kpAdic p P)) := by
    funext q
    exact Algebra.smul_def q.1 q.2
  rw [h]
  exact continuous_mul.comp (Continuous.prodMap (continuous_algebraMap_padic p P) continuous_id)
/-- The images of a finite `ℚ`-basis of the number field `K` span `K_P` over
`ℚ_[p]` — the finite-dimensionality witness of `moduleFinite_kpAdic`,
exported as a standalone statement (usable for rank computations). -/
theorem basisImages_span_eq_top (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Submodule.span (Padic p)
      (Set.range (fun i : Fin (Module.finrank ℚ K) =>
        algebraMap K (kpAdic p P) (Module.finBasis ℚ K i))) = ⊤ := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K := Module.finBasis ℚ K
  let f : Fin (Module.finrank ℚ K) → kpAdic p P := fun i => algebraMap K (kpAdic p P) (b i)
  let fins : Finset (kpAdic p P) := Finset.univ.image f
  let S : Submodule (Padic p) (kpAdic p P) := Submodule.span (Padic p) (fins : Set (kpAdic p P))
  have hset : Submodule.span (Padic p)
      (Set.range (fun i : Fin (Module.finrank ℚ K) => algebraMap K (kpAdic p P) (b i))) = S := by
    simp [S, fins, f]
  rw [hset]
  have hSfg : S.FG := ⟨fins, rfl⟩
  haveI hSfd : FiniteDimensional (Padic p) S := (Submodule.fg_iff_finiteDimensional S).mp hSfg
  have hKsubS : Set.range (algebraMap K (kpAdic p P)) ⊆ (S : Set (kpAdic p P)) := by
    rintro y ⟨k, rfl⟩
    have hk : k = ∑ i : Fin (Module.finrank ℚ K), (b.repr k) i • b i :=
      (Module.Basis.sum_repr b k).symm
    rw [hk]
    rw [map_sum]
    refine S.sum_mem ?_
    intro i hi
    have h1 : (algebraMap K (kpAdic p P)) (((b.repr k) i) • b i)
        = (((b.repr k) i : ℚ) : Padic p) • (algebraMap K (kpAdic p P)) (b i) := by
      rw [algebraMap_K_smul_rat]
      exact (padic_smul_rat p P ((b.repr k) i) (algebraMap K (kpAdic p P) (b i))).symm
    rw [h1]
    have hmem : (algebraMap K (kpAdic p P)) (b i) ∈ (S : Set (kpAdic p P)) := by
      exact Submodule.subset_span (by simp [fins, f])
    exact Submodule.smul_mem S (((b.repr k) i : ℚ) : Padic p) hmem
  apply Commons.Topology.Algebra.Module.eq_top_of_finiteDimensional_of_dense
    (kpAdic_denseRange_algebraMap p P) S
  exact hKsubS

/-- **`K_P` is a finite-dimensional `ℚ_[p]`-vector space**: the images of a
finite `ℚ`-basis of the number field `K` generate `K_P` over `ℚ_[p]`. -/
noncomputable instance moduleFinite_kpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Finite (Padic p) (kpAdic p P) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K := Module.finBasis ℚ K
  let fins : Finset (kpAdic p P) := Finset.univ.image
    (fun i : Fin (Module.finrank ℚ K) => algebraMap K (kpAdic p P) (b i))
  exact Module.Finite.of_fg_top ⟨fins, by
    rw [← basisImages_span_eq_top (p := p) (P := P)]
    congr 1
    ext x
    simp [fins, b]⟩


/-- The ring of integers of the `ℚ_p`-completion: `(qprime p).adicCompletionIntegers ℚ`
(ℤ_[p], up to `padicIntEquiv`). -/
abbrev QpInt (p : ℕ) [Fact (Nat.Prime p)] : Type := (qprime p).adicCompletionIntegers ℚ

/-- The rebased algebraMap sends the ℚ_p-integers into the K_P-integers
(`algebraMap_mem_kpInt`), giving the ring hom `QpInt →+* kpInt`. -/
noncomputable def qpIntToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    QpInt p →+* kpInt p P := by
  classical
  let g : QpInt p → kpInt p P := fun x =>
    ⟨algebraMap (QpAdic p) (kpAdic p P) (x : QpAdic p),
      algebraMap_mem_kpInt (p := p) (P := P) x⟩
  refine { toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · exact Subtype.ext (by simp [g, map_one])
  · intro x y
    exact Subtype.ext (by simp [g, map_mul])
  · exact Subtype.ext (by simp [g])
  · intro x y
    exact Subtype.ext (by simp [g, map_add])

/-- `kpInt p P` is a `QpInt p`-algebra (the restriction of the `ℚ_p`-algebra
structure of `kpAdic` to the integer rings). -/
noncomputable instance kpIntAlgebraQpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Algebra (QpInt p) (kpInt p P) :=
  RingHom.toAlgebra (qpIntToKpInt p P)


/-- Integer scalars act through the `QpInt`-algebra map: the `QpInt`-image of
an integer `n` is the integer `n` of `kpInt`.  (First step of the
closure/free-module chain: it lets integer combinations of an integral basis
be read as `QpInt`-linear combinations of the basis images.) -/
lemma algebraMap_QpInt_int (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℤ) :
    algebraMap (QpInt p) (kpInt p P) (n : QpInt p) = (n : kpInt p P) := by
  apply Subtype.ext
  have h1 : ((algebraMap (QpInt p) (kpInt p P) (n : QpInt p) : kpInt p P) : kpAdic p P)
      = algebraMap (QpAdic p) (kpAdic p P) ((n : QpInt p) : QpAdic p) := rfl
  rw [h1]
  calc
    algebraMap (QpAdic p) (kpAdic p P) ((n : QpInt p) : QpAdic p)
        = algebraMap (QpAdic p) (kpAdic p P) (algebraMap ℚ (QpAdic p) (n : ℚ)) := by simp
    _ = algebraMap ℚ (kpAdic p P) (n : ℚ) := by exact qpToKp_algebraMap_rat p P (n : ℚ)
    _ = (n : kpAdic p P) := by simp

/-- Integer scalar compatibility in the `QpInt`-algebra structure of `kpInt`:
the `QpInt`-scalar action of an integer agrees with the `ℤ`-module action. -/
lemma QpInt_smul_int (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℤ) (x : kpInt p P) :
    (n : QpInt p) • x = n • x := by
  rw [Algebra.smul_def, zsmul_eq_mul]
  congr 1
  exact algebraMap_QpInt_int p P n


lemma ringOfIntegers_mem_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : 𝓞 K) :
    (algebraMap K (kpAdic p P) (x : K) : kpAdic p P) ∈ (kprime p P).adicCompletionIntegers K := by
  have h : algebraMap K (kpAdic p P) (x : K) = ((x : K) : kpAdic p P) := by
    simpa using (congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
      (R := 𝓞 K) (K := K) (S := K) (v := kprime p P)) (x : K))
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 K) (K := K)
    (v := kprime p P) (x : 𝓞 K)

-- 1. ring hom
lemma mem_kpInt_algebraMap_apply (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (a b : 𝓞 K) :
    (algebraMap K (kpAdic p P) (a + b : K) : kpAdic p P) ∈ (kprime p P).adicCompletionIntegers K := by
  simpa using ringOfIntegers_mem_kpInt p P (a + b)

noncomputable def ringOfIntegersToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : 𝓞 K →+* kpInt p P := by
  classical
  let g : 𝓞 K → kpInt p P := fun x => ⟨algebraMap K (kpAdic p P) (x : K), ringOfIntegers_mem_kpInt p P x⟩
  refine { toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · exact Subtype.ext (by simp [g, map_one])
  · intro x y
    exact Subtype.ext (by simp [g, map_mul])
  · exact Subtype.ext (by simp [g])
  · intro x y
    exact Subtype.ext (by simp [g, map_add])

-- 2. containment

theorem ringOfIntegers_image_mem_QpInt_span (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : 𝓞 K) :
    (ringOfIntegersToKpInt p P x : kpInt p P) ∈
      Submodule.span (QpInt p)
        (Set.range (fun i : Fin (Module.finrank ℤ (𝓞 K)) =>
          ringOfIntegersToKpInt p P (Module.finBasis ℤ (𝓞 K) i : 𝓞 K))) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let φ : 𝓞 K →+* kpInt p P := ringOfIntegersToKpInt p P
  let T : Submodule (QpInt p) (kpInt p P) :=
    Submodule.span (QpInt p)
      (Set.range (fun j : Fin (Module.finrank ℤ (𝓞 K)) => φ (Module.finBasis ℤ (𝓞 K) j)))
  have hx : x = ∑ i : Fin (Module.finrank ℤ (𝓞 K)), (b.repr x) i • b i :=
    (Module.Basis.sum_repr b x).symm
  change φ x ∈ T
  rw [hx]
  rw [map_sum]
  refine T.sum_mem ?_
  intro i hi
  have hφ : φ ((b.repr x) i • b i) = ((b.repr x) i : ℤ) • φ (b i) := by
    exact map_zsmul φ ((b.repr x) i) (b i)
  rw [hφ]
  have hg : φ (b i) ∈ (T : Set (kpInt p P)) := by
    exact Submodule.subset_span (by dsimp [T, b]; exact ⟨i, rfl⟩)
  rw [← QpInt_smul_int p P ((b.repr x) i) (φ (b i))]
  exact Submodule.smul_mem T (((b.repr x) i : ℤ) : QpInt p) hg


/-! ### next G2(b): the dimension of the completion

**TARGET** (`finrank_kpAdic_eq_ramIdx_mul_inertiaDeg`):

    Module.finrank (Padic p) (kpAdic p P) = P.ramificationIdx ℤ * P.inertiaDeg ℤ

i.e. `[K_P : ℚ_p] = e_P · f_P` (the completion of the number field `K` at the
prime `P | (p)` has degree the product of the ramification index and the
inertia degree).  With `moduleFinite_kpAdic` the finrank is well-formed.

Decomposition plan (pieces, in dependency order):

1. (done) `Module.Finite (Padic p) (kpAdic p P)`
   (`moduleFinite_kpAdic`) with the spanning witness
   `basisImages_span_eq_top` (images of a `ℚ`-basis of `K`,
   `d := Module.finrank ℚ K` elements, span `K_P` over `ℚ_[p]`).
2. (Mathlib, available) the tower law `Module.finrank_mul_finrank F K A`:
   `finrank F K * finrank K A = finrank F A` for free modules over fields —
   with an intermediate complete subfield it decomposes the target.
3. (to build — the bulk of G2(b)) `[K_P : ℚ_p] = e_P·f_P` is most directly
   obtained from the fundamental identity over the *completed* integer
   rings: apply `Ideal.sum_ramification_inertia_eq_finrank`
   (RingTheory/RamificationInertia/Basic) to the tower
   `ℤ_[p]-integers → kpInt p P` (single prime over the maximal ideal, since
   `kpInt` is a DVR), giving `e·f = finrank (ℤ_[p]-ints) (kpInt p P)`;
   then identify that rank with `[K_P : ℚ_p]` (rank of the finite free
   module over the DVR = fraction-field degree — the
   `finrank_fiber`/fraction-field rank machinery of RamificationInertia);
   and prove the compatibility `ramificationIdx ℤ_[p] = P.ramificationIdx ℤ`
   resp. `inertiaDeg ℤ_[p] = P.inertiaDeg ℤ` (completion preserves e and f).
4. (G3, after 3) `[ℚ_p(ζ):ℚ_p] = f` via the residue-bijection
   (`teich_power_units_bijective`) and the unramified/cyclotomic degree
   argument.

Next concrete stones of G2(b), step (a): (a1 DONE) integer scalar lemma
`algebraMap_QpInt_int`/`QpInt_smul_int`; (a2 DONE) containment
`ringOfIntegers_image_mem_QpInt_span` (the image of `𝓞K` lies in the
QpInt-span of the integral-basis images; the ambient-span membership is
proved via a let-bound `T` submodule + `T.sum_mem`, `map_zsmul` per term,
and `QpInt_smul_int` to change ℤ-scalars into QpInt-scalars); (a3)
closedness of that span in `kpInt` (needs module topology: `ContinuousSMul
(QpInt p) (kpInt p P)` and compactness/finite-free-over-complete-DVR
arguments — CompactSpace for QpInt/kpInt do NOT currently synthesize);
(a4) with 𝓞K dense in kpInt (fleet L102) conclude span = ⊤, giving
Module.Finite; then the fraction-field rank identity.  (b)
primesOver-singleton of the completed tower; (c) completion-e/f
compatibilities.  Each is a bounded stone.
-/

end
end Submission.Vdw.LocalField
