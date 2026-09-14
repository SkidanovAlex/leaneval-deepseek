import Mathlib
import Submission.Vdw.LocalField.RankIdentity
import Submission.Vdw.LocalField.QpIntFinite
import Submission.Vdw.LocalField.Unramified
import Submission.Vdw.LocalField.ResidueInstances
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Submission.Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map

open scoped NumberField WithZero Valued
open IsDedekindDomain
open Submission.Vdw.LocalField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Local-field chapter (G2(b) translation stone, part 1): the base identification
`QpInt p ≃ ℤ_[p]` and the inertia-degree compatibility

With the algebraic core of G2(b) closed (`RankIdentity`: `e·f = [K_P:ℚ_p]`
for the *completed* tower), this module begins the translation of the
completed ramification/inertia data into the *global* data of the base prime
`P | (p)`:

* `adicCompletionIntegers_padicIntEquiv_congr` — the index-renamed integer
  identification `v.adicCompletionIntegers ℚ ≃+* ℤ_[p]` for a height-one
  prime `v` of `ℤ` with `primesEquiv v = p` (Mathlib's
  `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, with the
  `ℤ`-algebra instance conflict resolved by `Ring.toIntAlgebra`);
* `qpPadicIntEquiv` — `QpInt p ≃+* PadicInt p`: the ℚ_p-integers of our
  completion formalism ARE the standard `p`-adic integers `ℤ_[p]`;
* `padicIntResidue_card` / `qpIntResidue_card` — the residue fields are
  `𝔽_p`: `Nat.card (QpInt p ⧸ mR) = p` (via `PadicInt.residueField ≃ ZMod p`
  and the local-ring residue functor `ResidueField.mapEquiv`);
* `int_span_card` — `Nat.card (ℤ ⧸ (p)) = p`;
* `maximalIdeal_eq_unique` — in a local ring the unique maximal ideal is
  `IsLocalRing.maximalIdeal`;
* **`inertiaDeg_compat`** — THE inertia-degree compatibility:
  `mS.inertiaDeg (QpInt p) = P.inertiaDeg ℤ` where `mS :=
  maximalIdeal (kpInt p P)` is the maximal ideal of the completed integer
  ring and `P.inertiaDeg ℤ` is the *global* inertia degree of the prime
  `P | (p)` of `𝓞 K`.  Proof: `mS.LiesOver mR := maximalIdeal (QpInt p)`
  (the maximal ideal of the top pulls back to the maximal ideal of the base
  since `kpInt` is integral over the local ring `QpInt` and its maximal
  ideal is maximal), the analogous global tower `ℤ → 𝓞 K` gives `pZ.IsMaximal`;
  `Ideal.cardQuot_pow_inertiaDeg` at both towers yields
  `|QpInt ⧸ mR| ^ f_c = |kpInt ⧸ mS|` and `|ℤ ⧸ pZ| ^ f_P = |𝓞K ⧸ P|`;
  the three residue cardinalities `p, p^{f_P}, p` (this module +
  `ResidueInstances.kpIntResidue_card`) give `p^{f_c} = p^{f_P}`, hence
  `f_c = f_P` by injectivity of the base-`p` power.
* **`finrank_kpAdic_eq_ramIdx_mul_global_inertiaDeg`** — the rank identity
  with the *global* inertia degree:
  `[K_P : ℚ_p] = mS.ramificationIdx (QpInt p) * P.inertiaDeg ℤ`
  (`RankIdentity.finrank_kpAdic_eq_ramIdx_mul_inertiaDeg` + f-compat).

**The ramification-index compatibility is DONE in this module too**
(e-part, completed in the same session with the fleet lemma
`adicCompletionIntegers_maximalIdeal_eq_map`, which supplies the top
uniformizer `mS = P·kpInt`): `mS.ramificationIdx (QpInt p) =
P.ramificationIdx ℤ` (`ramificationIdx_compat`) — via
`ramificationIdx_tower` at the two towers `ℤ → QpInt → kpInt` and
`ℤ → 𝓞 K → kpInt`, both base indices being `1`
(`mR_ramIdx_over_int`: `(p)·QpInt = mR`; `mS_ramIdx_over_ringOfIntegers`:
`P·kpInt = mS`, multiplicity of a prime ideal in itself is `1`) — and the
full rank identity `finrank_kpAdic_eq_global`:
`[K_P : ℚ_p] = P.ramificationIdx ℤ * P.inertiaDeg ℤ`.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

open Rat.HeightOneSpectrum

/-- Index-renamed integer identification: for a height-one prime `v` of `ℤ`
whose `primesEquiv`-value is `p`, the ring of integers of the `v`-adic
completion of `ℚ` is `ℤ_[p]` (Mathlib's
`Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, renamed from
`ℤ_[primesEquiv v]` to `ℤ_[p]`; the two candidate `ℤ`-algebra instances are
aligned by `Ring.toIntAlgebra`). -/
noncomputable def adicCompletionIntegers_padicIntEquiv_congr (p : ℕ) [Fact (Nat.Prime p)]
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) :
    (v.adicCompletionIntegers ℚ) ≃+* PadicInt p := by
  subst p
  haveI : Fact (Nat.Prime ↑(Rat.HeightOneSpectrum.primesEquiv v)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  letI : Algebra ℤ (PadicInt ↑(Rat.HeightOneSpectrum.primesEquiv v)) := Ring.toIntAlgebra _
  exact (adicCompletionIntegers.padicIntEquiv v).toRingEquiv

/-- **`QpInt p ≃+* ℤ_[p]`**: the ℚ_p-integers of our completion formalism
(the integers of `(qprime p).adicCompletion ℚ`) are the standard `p`-adic
integers (index renamed via `primesEquiv_qprime`). -/
noncomputable def qpPadicIntEquiv (p : ℕ) [Fact (Nat.Prime p)] :
    QpInt p ≃+* PadicInt p :=
  adicCompletionIntegers_padicIntEquiv_congr p (qprime p) (primesEquiv_qprime p)

/-- The residue field of `ℤ_[p]` is `𝔽_p`:
`Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p` (`PadicInt.residueField ≃ ZMod p`). -/
lemma padicIntResidue_card (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (PadicInt p ⧸ IsLocalRing.maximalIdeal (PadicInt p)) = p := by
  calc
    Nat.card (PadicInt p ⧸ IsLocalRing.maximalIdeal (PadicInt p))
        = Nat.card (IsLocalRing.ResidueField (PadicInt p)) := by rfl
    _ = Nat.card (ZMod p) := by
          exact Nat.card_congr (PadicInt.residueField (p := p)).toEquiv
    _ = p := Nat.card_zmod p

/-- The residue field of the ℚ_p-completion's integer ring is `𝔽_p`:
`Nat.card (QpInt p ⧸ maximalIdeal (QpInt p)) = p` (transport of
`padicIntResidue_card` along `qpPadicIntEquiv`, via the residue-field
functor of local rings). -/
lemma qpIntResidue_card (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) = p := by
  calc
    Nat.card (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p))
        = Nat.card (IsLocalRing.ResidueField (QpInt p)) := by rfl
    _ = Nat.card (IsLocalRing.ResidueField (PadicInt p)) := by
          exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (qpPadicIntEquiv p)).toEquiv
    _ = p := by
          change Nat.card (PadicInt p ⧸ IsLocalRing.maximalIdeal (PadicInt p)) = p
          exact padicIntResidue_card p

/-- `ℤ ⧸ (p)` has `p` elements: `ℤ` modulo the ideal `(p)` is `ZMod p`
(`Int.quotientSpanEquivZMod`). -/
lemma int_span_card (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) = p := by
  calc
    Nat.card (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ))
        = Nat.card (ZMod (Int.natAbs (p : ℤ))) := by
          exact Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv
    _ = Nat.card (ZMod p) := by simp [Int.natAbs]
    _ = p := Nat.card_zmod p

variable {K : Type u} [Field K] [NumberField K]

/-- In a local ring the maximal ideal is the unique maximal ideal:
any maximal ideal equals `IsLocalRing.maximalIdeal`. -/
lemma maximalIdeal_eq_unique (R : Type*) [CommSemiring R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsMaximal) : I = IsLocalRing.maximalIdeal R := by
  obtain ⟨m, hm, huniq⟩ := IsLocalRing.maximal_ideal_unique R
  have hmR : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have h1 : m = IsLocalRing.maximalIdeal R := (huniq (IsLocalRing.maximalIdeal R) hmR).symm
  exact (huniq I hI).trans h1

/-- **Inertia-degree compatibility**: the inertia degree of the maximal
ideal of the completed integer ring `kpInt p P` over `QpInt p` equals the
global inertia degree of the prime `P` of `𝓞 K` over `ℤ`.

Proof sketch: both `QpInt → kpInt` (the maximal ideal of the top pulls back
to the maximal ideal of the bottom, since `kpInt` is integral over the local
ring `QpInt`) and `ℤ → 𝓞 K` are towers to which
`Ideal.cardQuot_pow_inertiaDeg` applies; with the residue cardinalities
`|QpInt ⧸ mR| = p` (`qpIntResidue_card`), `|kpInt ⧸ mS| = p^{f_P}`
(`ResidueInstances.kpIntResidue_card`), `|ℤ ⧸ pZ| = p`, both sides of the
two identities become `p^{f_c}` and `p^{f_P}`, and injectivity of the
base-`p` natural power gives `f_c = f_P`. -/
theorem inertiaDeg_compat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).inertiaDeg (QpInt p) = P.inertiaDeg ℤ := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  haveI hInt : Algebra.IsIntegral (QpInt p) (kpInt p P) := inferInstance
  have hmax_comap : Ideal.IsMaximal (mS.comap (algebraMap (QpInt p) (kpInt p P))) :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := QpInt p) (S := kpInt p P) mS
  have hmSeq : mS.comap (algebraMap (QpInt p) (kpInt p P)) = mR := by
    dsimp [mR]
    exact maximalIdeal_eq_unique (QpInt p) (mS.comap (algebraMap (QpInt p) (kpInt p P))) hmax_comap
  haveI hmSLies : mS.LiesOver mR := by
    constructor
    dsimp [mR, mS]
    change IsLocalRing.maximalIdeal (QpInt p) = Ideal.comap (algebraMap (QpInt p) (kpInt p P))
      (IsLocalRing.maximalIdeal (kpInt p P))
    exact hmSeq.symm
  haveI hIntZ : Algebra.IsIntegral ℤ (𝓞 K) := inferInstance
  have hmax_comapZ : Ideal.IsMaximal (P.comap (algebraMap ℤ (𝓞 K))) :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ) (S := 𝓞 K) P
  have hPcomap : P.comap (algebraMap ℤ (𝓞 K)) = pZ := by
    simpa [pZ, Ideal.under_def] using (Ideal.over_def P pZ).symm
  haveI hpZmax : pZ.IsMaximal := by
    rw [← hPcomap]
    exact hmax_comapZ
  have h1 := Ideal.cardQuot_pow_inertiaDeg (R := QpInt p) (S := kpInt p P) mR mS
  have h2 := Ideal.cardQuot_pow_inertiaDeg (R := ℤ) (S := 𝓞 K) pZ P
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h1
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h2
  have hQp : Nat.card (QpInt p ⧸ mR) = p := by
    simpa [mR] using (qpIntResidue_card (p := p))
  have hKp : Nat.card (kpInt p P ⧸ mS) = p ^ P.inertiaDeg ℤ := by
    simpa [mS] using (kpIntResidue_card (K := K) (p := p) (P := P))
  have hZ : Nat.card (ℤ ⧸ pZ) = p := by
    simpa [pZ] using (int_span_card (p := p))
  have h1' : p ^ mS.inertiaDeg (QpInt p) = p ^ P.inertiaDeg ℤ := by
    calc
      p ^ mS.inertiaDeg (QpInt p)
          = Nat.card (QpInt p ⧸ mR) ^ mS.inertiaDeg (QpInt p) := by rw [hQp]
      _ = Nat.card (kpInt p P ⧸ mS) := h1
      _ = p ^ P.inertiaDeg ℤ := hKp
  exact (Nat.pow_right_injective (a := p) (Nat.Prime.two_le (Fact.out : Nat.Prime p))) h1'

/-- **The rank identity with the global inertia degree**:
`[K_P : ℚ_p] = e_c · P.inertiaDeg ℤ`, where `e_c :=
mS.ramificationIdx (QpInt p)` is the completed ramification index and
`P.inertiaDeg ℤ` the global inertia degree (composite of
`RankIdentity.finrank_kpAdic_eq_ramIdx_mul_inertiaDeg` and
`inertiaDeg_compat`). -/
theorem finrank_kpAdic_eq_ramIdx_mul_global_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (QpAdic p) (kpAdic p P) =
      (IsLocalRing.maximalIdeal (kpInt p P)).ramificationIdx (QpInt p) *
        P.inertiaDeg ℤ := by
  rw [finrank_kpAdic_eq_ramIdx_mul_inertiaDeg p P]
  rw [inertiaDeg_compat p P]


/-! ### e-part groundwork: the base uniformizer of `QpInt p`

The ramification-index compatibility (next stone) needs the *base* maximal
ideal to be principal, generated by `p`: `mR = (p) · QpInt p` (transport of
`PadicInt.maximalIdeal_eq_span_p`).  This section supplies the generic
transport lemmas:

* `maximalIdeal_map_eq_of_ringEquiv` — the image of the maximal ideal under
  a ring equivalence between local rings is the maximal ideal;
* `congr_intCast` / `congr_natCast` — the index-renamed identification
  `adicCompletionIntegers_padicIntEquiv_congr` preserves integer / natural
  constants (it is a `ℤ`-algebra map);
* **`qpIntMaximalIdeal_eq_span_p`** — `mR = Ideal.span {(p : QpInt p)}`:
  `p` is a uniformizer of `QpInt p`.  Together with the residue cardinality
  `|QpInt ⧸ mR| = p` this pins the base local data `(ℤ_[p], (p), 𝔽_p)`;
  the top uniformizer fact (`P · kpInt = mS`, the maximal ideal of the
  completion generated by the image of `P`) is the remaining input of the
  e-compat proof (Roadmap Session-71).
-/

/-- The image of the maximal ideal under a ring equivalence between local
rings is the maximal ideal (of the codomain). -/
lemma maximalIdeal_map_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (IsLocalRing.maximalIdeal R).map (e : R →+* S) = IsLocalRing.maximalIdeal S := by
  classical
  haveI hloc : IsLocalHom (e : R →+* S) :=
    IsLocalHom.of_surjective (f := (e : R →+* S)) e.surjective
  have hle : (IsLocalRing.maximalIdeal R).map (e : R →+* S) ≤ IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_le (e : R →+* S)
  have hle' : IsLocalRing.maximalIdeal S ≤ (IsLocalRing.maximalIdeal R).map (e : R →+* S) := by
    haveI hloc' : IsLocalHom ((e.symm : S →+* R)) :=
      IsLocalHom.of_surjective (f := (e.symm : S →+* R)) e.symm.surjective
    have hle2 : (IsLocalRing.maximalIdeal S).map (e.symm : S →+* R) ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.map_maximalIdeal_le (e.symm : S →+* R)
    have hmm := Ideal.map_mono (f := (e : R →+* S)) hle2
    have hme : (IsLocalRing.maximalIdeal S) =
        Ideal.map (↑e) (Ideal.map (↑e.symm) (IsLocalRing.maximalIdeal S)) := by
      simpa using (Ideal.map_of_equiv (I := IsLocalRing.maximalIdeal S) (e.symm)).symm
    rw [hme]
    exact hmm
  exact le_antisymm hle hle'

/-- The index-renamed identification preserves integer constants: the
underlying `ℤ`-algebra map of `adicCompletionIntegers.padicIntEquiv` sends
`(z : ℤ)` to `(z : ℤ)` (after aligning the `ℤ`-algebra instances by
`Ring.toIntAlgebra`). -/
lemma congr_intCast (p : ℕ) [Fact (Nat.Prime p)]
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) (z : ℤ) :
    adicCompletionIntegers_padicIntEquiv_congr p v hv ((z : ℤ) : v.adicCompletionIntegers ℚ) =
      ((z : ℤ) : PadicInt p) := by
  subst p
  haveI : Fact (Nat.Prime ↑(Rat.HeightOneSpectrum.primesEquiv v)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  letI : Algebra ℤ (PadicInt ↑(Rat.HeightOneSpectrum.primesEquiv v)) := Ring.toIntAlgebra _
  change (adicCompletionIntegers.padicIntEquiv v) ((z : ℤ) : v.adicCompletionIntegers ℚ) =
      ((z : ℤ) : PadicInt ↑(Rat.HeightOneSpectrum.primesEquiv v))
  exact (adicCompletionIntegers.padicIntEquiv v).commutes' z

/-- The index-renamed identification preserves natural constants. -/
lemma congr_natCast (p : ℕ) [Fact (Nat.Prime p)]
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) (n : ℕ) :
    adicCompletionIntegers_padicIntEquiv_congr p v hv ((n : ℕ) : v.adicCompletionIntegers ℚ) =
      ((n : ℕ) : PadicInt p) := by
  simpa using congr_intCast p v hv (n : ℤ)

/-- **Base uniformizer**: the maximal ideal of `QpInt p` is generated by `p`
(transport of `PadicInt.maximalIdeal_eq_span_p` along `qpPadicIntEquiv`). -/
lemma qpIntMaximalIdeal_eq_span_p (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalRing.maximalIdeal (QpInt p) = Ideal.span ({(p : QpInt p)} : Set (QpInt p)) := by
  classical
  let e : QpInt p ≃+* PadicInt p := qpPadicIntEquiv p
  have hmap : (IsLocalRing.maximalIdeal (PadicInt p)).map (e.symm : PadicInt p →+* QpInt p) =
      IsLocalRing.maximalIdeal (QpInt p) := by
    exact (maximalIdeal_map_eq_of_ringEquiv (e.symm))
  have hp : e.symm ((p : PadicInt p)) = (p : QpInt p) := by
    have hs := congr_natCast p (qprime p) (primesEquiv_qprime p) p
    have h2 := congrArg (fun x : PadicInt p => e.symm x) hs
    simpa [e] using h2.symm
  have hspan : (IsLocalRing.maximalIdeal (PadicInt p)).map (e.symm : PadicInt p →+* QpInt p) =
      Ideal.span ({(p : QpInt p)} : Set (QpInt p)) := by
    rw [PadicInt.maximalIdeal_eq_span_p (p := p)]
    rw [Ideal.map_span]
    rw [Set.image_singleton]
    exact congrArg Ideal.span (congrArg Set.singleton hp)
  exact hmap.symm.trans hspan


/-- The maximal ideal of the completed integer ring lies over the maximal
ideal of the base integer ring: `kpInt` is integral over the local ring
`QpInt`, so the pullback of the top maximal ideal is the (unique) maximal
ideal of the base. -/
lemma mS_liesOver_mR (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).LiesOver (IsLocalRing.maximalIdeal (QpInt p)) := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  haveI hInt : Algebra.IsIntegral (QpInt p) (kpInt p P) := inferInstance
  have hmax_comap : Ideal.IsMaximal (mS.comap (algebraMap (QpInt p) (kpInt p P))) :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := QpInt p) (S := kpInt p P) mS
  have hmSeq : mS.comap (algebraMap (QpInt p) (kpInt p P)) = mR := by
    dsimp [mR]
    exact maximalIdeal_eq_unique (QpInt p) (mS.comap (algebraMap (QpInt p) (kpInt p P))) hmax_comap
  constructor
  change IsLocalRing.maximalIdeal (QpInt p) = Ideal.comap (algebraMap (QpInt p) (kpInt p P))
    (IsLocalRing.maximalIdeal (kpInt p P))
  exact hmSeq.symm


/-! ### e-part: the ramification-index compatibility to the GLOBAL value

With the fleet lemma `adicCompletionIntegers_maximalIdeal_eq_map` (the
maximal ideal of the completion's integer ring is generated by the image of
the prime: `mS = P·kpInt`) and the base uniformizer
`qpIntMaximalIdeal_eq_span_p` (`mR = (p)·QpInt`), the completed-tower
ramification index equals the global one:

* `mS_liesOver_P` — the maximal ideal `mS` of `kpInt p P` lies over `P` in
  the tower `𝓞 K → kpInt` (from `P ⊆ mS.comap` via `mS = P·kpInt`, properness
  of the comap, and maximality of `P`);
* `mS_ramIdx_over_ringOfIntegers` — `mS.ramificationIdx (𝓞 K) = 1` (the
  completion at `P` is unramified over `𝓞 K`): via
  `ramificationIdx_eq_multiplicity` the index is the multiplicity of `mS` in
  `P·kpInt = mS`, which is `1`;
* `mR_ramIdx_over_int` — `mR.ramificationIdx ℤ = 1` (the completion of `ℤ`
  at `(p)` is unramified): likewise `(p)·QpInt = mR` and multiplicity of `mR`
  in `mR` is `1`;
* **`ramificationIdx_compat`** — THE theorem:
  `mS.ramificationIdx (QpInt p) = P.ramificationIdx ℤ`.  Proof:
  `ramificationIdx_tower` in the two towers `ℤ → QpInt → kpInt` and
  `ℤ → 𝓞 K → kpInt` gives `mS.ramificationIdx ℤ = 1 · e_c = e_P · 1`.
* **`finrank_kpAdic_eq_global`** — `[K_P : ℚ_p] = P.ramificationIdx ℤ *
  P.inertiaDeg ℤ` (composite of `RankIdentity.finrank_kpAdic_eq_ramIdx_mul_inertiaDeg`,
  `inertiaDeg_compat` and `ramificationIdx_compat`).
-/


/-- `1` is not in the maximal ideal of a local ring. -/
lemma one_not_mem_maximal (R : Type*) [CommSemiring R] [IsLocalRing R] :
    (1 : R) ∉ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal]
  exact fun h => h isUnit_one

/-- The maximal ideal of the completed integer ring lies over `P` in the
tower `𝓞 K → kpInt p P`: `mS = P·kpInt` (`adicCompletionIntegers_maximalIdeal_eq_map`)
shows `P ⊆ mS.comap`; the comap is proper and `P` is maximal, so the comap is
`P` itself. -/
lemma mS_liesOver_P (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).LiesOver P := by
  classical
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  have hC1 : mS = P.map (algebraMap (𝓞 K) (kpInt p P)) := by
    have h := Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map
      (K := K) (V := kprime p P)
    simpa [kpInt, mS, kprime_asIdeal] using h
  have hPsub : P ≤ mS.comap (algebraMap (𝓞 K) (kpInt p P)) := by
    intro x hx
    change algebraMap (𝓞 K) (kpInt p P) x ∈ mS
    rw [hC1]
    exact Ideal.subset_span (Set.mem_image_of_mem (algebraMap (𝓞 K) (kpInt p P)) hx)
  have hne : mS.comap (algebraMap (𝓞 K) (kpInt p P)) ≠ ⊤ := by
    intro htop
    have honeZ : (1 : 𝓞 K) ∈ mS.comap (algebraMap (𝓞 K) (kpInt p P)) := by
      rw [htop]
      trivial
    exact one_not_mem_maximal (kpInt p P) ((Ideal.mem_comap.mp honeZ))
  have hpcoat : IsCoatom P := Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)
  have hEq : mS.comap (algebraMap (𝓞 K) (kpInt p P)) = P := by
    exact (hpcoat.le_iff_eq hne).mp hPsub
  constructor
  change P = Ideal.comap (algebraMap (𝓞 K) (kpInt p P)) mS
  exact hEq.symm

/-- **The completed tower is unramified over `𝓞 K`**: the ramification index
of `mS` over `𝓞 K` is `1`.  Via `ramificationIdx_eq_multiplicity` the index
is the multiplicity of `mS` in `P·kpInt = mS`, which is `1`
(`multiplicity_self`). -/
lemma mS_ramIdx_over_ringOfIntegers (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).ramificationIdx (𝓞 K) = 1 := by
  classical
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  haveI hSL : mS.LiesOver P := mS_liesOver_P p P
  have hC1 : mS = P.map (algebraMap (𝓞 K) (kpInt p P)) := by
    have h := Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map
      (K := K) (V := kprime p P)
    simpa [kpInt, mS, kprime_asIdeal] using h
  have hne0 : P.map (algebraMap (𝓞 K) (kpInt p P)) ≠ ⊥ := by
    rw [← hC1]
    exact IsDiscreteValuationRing.not_a_field (kpInt p P)
  have hEq := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    (R := 𝓞 K) (S := kpInt p P) (p := P) (q := mS) hne0
  rw [← hC1] at hEq
  simpa using hEq

/-- **The ℚ_p-completion of `ℤ` is unramified over `ℤ`**: the ramification
index of the maximal ideal of `QpInt p` over `ℤ` is `1` (multiplicity of `mR`
in `(p)·QpInt = mR` is `1`). -/
lemma mR_ramIdx_over_int (p : ℕ) [Fact (Nat.Prime p)] :
    (IsLocalRing.maximalIdeal (QpInt p)).ramificationIdx ℤ = 1 := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hmap : pZ.map (algebraMap ℤ (QpInt p)) = mR := by
    calc
      (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (QpInt p))
          = Ideal.span {((p : ℕ) : QpInt p)} := by
            rw [Ideal.map_span, Set.image_singleton]
            congr 1
            simp
      _ = IsLocalRing.maximalIdeal (QpInt p) := (qpIntMaximalIdeal_eq_span_p p).symm
  have hsub : pZ ≤ mR.comap (algebraMap ℤ (QpInt p)) := by
    intro x hx
    change algebraMap ℤ (QpInt p) x ∈ mR
    rw [← hmap]
    change algebraMap ℤ (QpInt p) x ∈
      Ideal.span (⇑(algebraMap ℤ (QpInt p)) '' (↑(Ideal.span ({(p : ℤ)} : Set ℤ)) : Set ℤ))
    exact Ideal.subset_span ⟨x, hx, rfl⟩
  have hne : mR.comap (algebraMap ℤ (QpInt p)) ≠ ⊤ := by
    intro htop
    have honeZ : (1 : ℤ) ∈ mR.comap (algebraMap ℤ (QpInt p)) := by
      rw [htop]
      trivial
    exact one_not_mem_maximal (QpInt p) ((Ideal.mem_comap.mp honeZ))
  have hpcoat : IsCoatom pZ := Ideal.isMaximal_def.mp (inferInstance : pZ.IsMaximal)
  have hEq : mR.comap (algebraMap ℤ (QpInt p)) = pZ := by
    exact (hpcoat.le_iff_eq hne).mp hsub
  haveI hRL : mR.LiesOver pZ := by
    constructor
    change pZ = Ideal.comap (algebraMap ℤ (QpInt p)) mR
    exact hEq.symm
  have hne0 : pZ.map (algebraMap ℤ (QpInt p)) ≠ ⊥ := by
    rw [hmap]
    exact IsDiscreteValuationRing.not_a_field (QpInt p)
  have hEq2 := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    (R := ℤ) (S := QpInt p) (p := pZ) (q := mR) hne0
  rw [hmap] at hEq2
  simpa using hEq2

/-- **Ramification-index compatibility**: the ramification index of the
maximal ideal `mS` of the completed integer ring over `QpInt p` equals the
GLOBAL ramification index of the prime `P` of `𝓞 K` over `ℤ`.

Proof: `ramificationIdx_tower` (multiplicativity in towers) applied to
`ℤ → QpInt → kpInt` and `ℤ → 𝓞 K → kpInt` expresses the single index
`mS.ramificationIdx ℤ` both as `mR.ramificationIdx ℤ · e_c = 1 · e_c` and as
`P.ramificationIdx ℤ · mS.ramificationIdx (𝓞 K) = e_P · 1`; the two base
indices are `1` by `mR_ramIdx_over_int` and
`mS_ramIdx_over_ringOfIntegers`. -/
theorem ramificationIdx_compat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).ramificationIdx (QpInt p) =
      P.ramificationIdx ℤ := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  haveI hSL_mR : mS.LiesOver mR := by
    simpa [mS, mR] using (mS_liesOver_mR p P)
  haveI hSL_P : mS.LiesOver P := by
    simpa [mS] using (mS_liesOver_P p P)
  have hT1 := Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 K) (T := kpInt p P)
    (q := P) (r := mS)
  have hT2 := Ideal.ramificationIdx_tower (R := ℤ) (S := QpInt p) (T := kpInt p P)
    (q := mR) (r := mS)
  have h1over : mS.ramificationIdx (𝓞 K) = 1 := by
    simpa [mS] using (mS_ramIdx_over_ringOfIntegers p P)
  have h1base : mR.ramificationIdx ℤ = 1 := by
    simpa [mR] using (mR_ramIdx_over_int p)
  have hA : mS.ramificationIdx ℤ = P.ramificationIdx ℤ := by
    rw [h1over, mul_one] at hT1
    exact hT1
  have hB : mS.ramificationIdx (QpInt p) = mS.ramificationIdx ℤ := by
    rw [h1base, one_mul] at hT2
    exact hT2.symm
  exact hB.trans hA

/-- **The full rank identity with GLOBAL ramification and inertia data**:
`[K_P : ℚ_p] = P.ramificationIdx ℤ * P.inertiaDeg ℤ` (composite of
`RankIdentity.finrank_kpAdic_eq_ramIdx_mul_inertiaDeg`, `ramificationIdx_compat`
and `inertiaDeg_compat`). -/
theorem finrank_kpAdic_eq_global (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (QpAdic p) (kpAdic p P) = P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  rw [finrank_kpAdic_eq_ramIdx_mul_inertiaDeg p P]
  rw [ramificationIdx_compat p P]
  rw [inertiaDeg_compat p P]

end
end Submission.Vdw.LocalField
