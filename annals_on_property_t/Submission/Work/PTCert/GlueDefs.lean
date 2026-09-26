import Submission.Work.PTCert.Chain
import Submission.Work.PTCert.KernelCert

/-!
# PTCert — glue interfaces between the kernel checks and the certificate chain

Definitions and `Prop`s only (see `NOTES_LEAD_glue.md` at the workspace root for the whole chain).

* Generic (any group / index type): `conjAct` (conjugation action on an injective family),
  `OrbitDecomp` (Gram form of an invariant matrix = row-orbit sum, up to `conjAvg`),
  `FourierVanish`, `FourierTransport`, `KleinLevel` (the two-level sign-character Fourier
  reduction on top of `TwistedFourierCriterion`), `LdlChainSound` (the kernel LDL row steps
  give a PSD certificate).
* Rank 5: codes of signed permutations (`codeElt`, `CodeFacts`), letter tables (`TabOf`),
  the conjugation action on `B₂`-codes (`ActCSound`), faithfulness of the model key
  (`RedWCanonical`, `ModelKeyFaithful`), bit/character bridges (`BitsBridge`), `WhtSound`.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-! ## Generic: conjugation action on an injective family -/

/-- Conjugation action of `σ` on the indices of a family `f : ι → G` (by choice; meaningful when
the family is closed under conjugation by `σ` and injective). -/
def conjAct {G : Type} [Group G] {ι : Type} (f : ι → G) (σ : G) (x : ι) : ι := by
  classical
  exact if h : ∃ y, f y = σ * f x * σ⁻¹ then Classical.choose h else x

/-- **(GL1)** Facts about `conjAct` for an injective family closed under conjugation by a finite
subgroup. -/
def ConjActFacts : Prop :=
  ∀ (G : Type) [Group G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} (f : ι → G), Function.Injective f →
      (∀ σ ∈ Sg, ∀ x, ∃ y, f y = σ * f x * σ⁻¹) →
      ConjAction Sg f (conjAct f) ∧
      (∀ σ ∈ Sg, ∀ τ ∈ Sg, ∀ x, conjAct f (σ * τ) x = conjAct f σ (conjAct f τ x)) ∧
      (∀ x, conjAct f 1 x = x) ∧
      (∀ σ ∈ Sg, Function.Bijective (conjAct f σ)) ∧
      (∀ σ ∈ Sg, ∀ x y, f y = σ * f x * σ⁻¹ → conjAct f σ x = y)

/-- **(GL2) Orbit decomposition of a Gram form.**  For an `Sg`-invariant matrix `P` and a choice of
one representative `x0 r` per class `r` of a labelling `rowOf` such that every `x` is an
`Sg`-translate of `x0 (rowOf x)`, the Gram form of `P` has the same `conjAvg` as the
row-orbit sum `Σ_r #{x : rowOf x = r} • Σ_y P (x0 r) y • of((f (x0 r))⁻¹ f y)`. -/
def OrbitDecomp : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → G) (act : G → ι → ι), ConjAction Sg f act →
      (∀ σ ∈ Sg, Function.Bijective (act σ)) →
      ∀ (P : Matrix ι ι ℝ), (∀ σ ∈ Sg, ∀ x y, P (act σ x) (act σ y) = P x y) →
      ∀ {R : Type} [Fintype R] [DecidableEq R] (x0 : R → ι) (rowOf : ι → R),
        (∀ x, ∃ σ ∈ Sg, act σ (x0 (rowOf x)) = x) →
        conjAvg Sg (gramForm f P) =
          conjAvg Sg (∑ r, ((Finset.univ.filter (fun x => rowOf x = r)).card : ℝ) •
            ∑ y, P (x0 r) y • MonoidAlgebra.of ℝ G ((f (x0 r))⁻¹ * f y))

/-! ## Generic: sign-character Fourier blocks -/

/-- The (untwisted) Fourier block function of `M` for the sign character `S`:
`W_S(x, y) = Σ_a χ_S(a) · M x (act a y)`. -/
def fourierW {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (M : Matrix ι ι ℝ)
    (S : Finset (Fin m)) (x y : ι) : ℝ :=
  ∑ a, chiS S a * M x (act a y)

/-- **(GL3) Vanishing rows.**  If `a` fixes `x` and `χ_S(a) = -1` then the Fourier block function
vanishes in the row and in the column of `x`. -/
def FourierVanish : Prop :=
  ∀ (m : ℕ) {ι : Type} (act : (Fin m → ZMod 2) → ι → ι),
    (∀ a b x, act (a + b) x = act a (act b x)) → (∀ x, act 0 x = x) →
    ∀ (M : Matrix ι ι ℝ), (∀ a x y, M (act a x) (act a y) = M x y) →
    ∀ (S : Finset (Fin m)) (x : ι) (a : Fin m → ZMod 2), act a x = x → chiS S a = -1 →
      ∀ y, fourierW act M S x y = 0 ∧ fourierW act M S y x = 0

/-- **(GL4) Transport of Fourier blocks.**  A bijection `τ` of the index set normalising the
`(ℤ/2)^m`-action through the coordinate permutation `p` and preserving `M` carries the block of
`S` to the block of `p(S)` by a signed permutation of the representatives; in particular PSD
transports. -/
def FourierTransport : Prop :=
  ∀ (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (act : (Fin m → ZMod 2) → ι → ι),
    (∀ a b x, act (a + b) x = act a (act b x)) → (∀ x, act 0 x = x) →
    ∀ (M : Matrix ι ι ℝ), (∀ a x y, M (act a x) (act a y) = M x y) →
    ∀ (rep : ι → ι) (nu : ι → (Fin m → ZMod 2)),
      (∀ x, act (nu x) (rep x) = x) → (∀ x, rep (rep x) = rep x) → (∀ a x, rep (act a x) = rep x) →
    ∀ (τ : ι ≃ ι) (p : Equiv.Perm (Fin m)),
      (∀ a x, τ (act a x) = act (fun i => a (p.symm i)) (τ x)) → (∀ x y, M (τ x) (τ y) = M x y) →
    ∀ S : Finset (Fin m),
      (Matrix.of fun (x y : {x // rep x = x}) => fourierW act M S x.1 y.1).PosSemidef →
      (Matrix.of fun (x y : {x // rep x = x}) =>
        fourierW act M (S.map p.toEmbedding) x.1 y.1).PosSemidef

/-- **(GL5) Klein level.**  Second Fourier level for an elementary abelian group `(ℤ/2)^m2`
acting by `kap`, normalising the first-level action (`kap b ∘ act a = act (θ b a) ∘ kap b`) and
fixing the character `S`.  On the representatives `ks` of the Klein orbits of the
`χ_S`-admissible N-representatives (those whose N-stabiliser lies in `ker χ_S`), the `ψ`-blocks are
symmetric, and if they are all PSD then the whole block `W_S` (on all N-representatives) is PSD. -/
def KleinLevel : Prop :=
  ∀ (m m2 : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (act : (Fin m → ZMod 2) → ι → ι) (kap : (Fin m2 → ZMod 2) → ι → ι)
    (θ : (Fin m2 → ZMod 2) → (Fin m → ZMod 2) → (Fin m → ZMod 2)),
    (∀ a b x, act (a + b) x = act a (act b x)) → (∀ x, act 0 x = x) →
    (∀ a b x, kap (a + b) x = kap a (kap b x)) → (∀ x, kap 0 x = x) →
    (∀ b a x, kap b (act a x) = act (θ b a) (kap b x)) → (∀ b a, θ b (θ b a) = a) →
    ∀ (S : Finset (Fin m)), (∀ b a, chiS S (θ b a) = chiS S a) →
    ∀ (M : Matrix ι ι ℝ), M.transpose = M → (∀ a x y, M (act a x) (act a y) = M x y) →
      (∀ b x y, M (kap b x) (kap b y) = M x y) →
    ∀ (rep : ι → ι) (nu : ι → (Fin m → ZMod 2)),
      (∀ x, act (nu x) (rep x) = x) → (∀ x, rep (rep x) = rep x) → (∀ a x, rep (act a x) = rep x) →
    ∀ (ks : List ι),
      -- the listed Klein representatives are admissible N-representatives
      (∀ y ∈ ks, rep y = y ∧ ∀ a, act a y = y → chiS S a = 1) →
      -- they lie in distinct Klein orbits
      (∀ (i j : Fin ks.length) (b : Fin m2 → ZMod 2), rep (kap b (ks.get i)) = ks.get j → i = j) →
      -- every admissible N-representative is in the Klein orbit of a listed one
      (∀ x, rep x = x → (∀ a, act a x = x → chiS S a = 1) →
        ∃ (i : Fin ks.length) (b : Fin m2 → ZMod 2), rep (kap b (ks.get i)) = x) →
      (∀ ψ : Finset (Fin m2), ∀ i j : Fin ks.length,
        (∑ b, chiS ψ b * chiS S (nu (kap b (ks.get j))) *
            fourierW act M S (ks.get i) (rep (kap b (ks.get j)))) =
        (∑ b, chiS ψ b * chiS S (nu (kap b (ks.get i))) *
            fourierW act M S (ks.get j) (rep (kap b (ks.get i))))) ∧
      ((∀ ψ : Finset (Fin m2),
        (Matrix.of fun (i j : Fin ks.length) =>
          ∑ b, chiS ψ b * chiS S (nu (kap b (ks.get j))) *
            fourierW act M S (ks.get i) (rep (kap b (ks.get j)))).PosSemidef) →
      (Matrix.of fun (x y : {x // rep x = x}) => fourierW act M S x.1 y.1).PosSemidef)

/-- **(GL10) Soundness of the kernel LDL row steps.**  If every row `i < n` of an integer
symmetric matrix `B` passes `ldlRowStep` (upper-triangle entries `B i (i+d)`, positive weights `w`,
lower-triangular factor rows `C i` of length `≤ i + 1`, column accumulators `acc i` starting at
zero), then `B` is positive semidefinite. -/
def LdlChainSound : Prop :=
  ∀ (n : ℕ) (B : ℕ → ℕ → ℤ) (w : ℕ → ℤ) (C : ℕ → List ℤ) (acc : ℕ → List ℤ),
    (∀ i j, B i j = B j i) → (∀ i < n, 0 < w i) → (∀ i < n, (C i).length ≤ i + 1) →
    acc 0 = List.replicate n 0 →
    (∀ i < n, ldlRowStep ((List.range (n - i)).map (fun d => B i (i + d))) (w i)
        ((List.range (n - i)).map (fun d => w (i + d))) (C i)
        ((List.range (n - i)).map (fun d => C (i + d))) (acc i) = some (acc (i + 1))) →
    (Matrix.of fun (i j : Fin n) => (B i j : ℝ)).PosSemidef

/-! ## Rank 5: codes of signed permutations and letter tables -/

/-- `Aut(F₅)`. -/
abbrev G5 : Type := MulAut (FreeGroup (Fin 5))

/-- Base-8 code of a permutation (digit `i` = `p i`). -/
def pcOf (p : Equiv.Perm (Fin 5)) : ℕ := ∑ i : Fin 5, (p i).val * 8 ^ i.val

/-- Binary code of a sign function. -/
def scOf (s : Fin 5 → Bool) : ℕ := ∑ i : Fin 5, (if s i then 1 else 0) * 2 ^ i.val

/-- Sign function of a binary code. -/
def scBits (sc : ℕ) : Fin 5 → Bool := fun i => decide (sbit sc i.val = 1)

/-- The permutation with code `pc` (identity if there is none). -/
def permOfPC (pc : ℕ) : Equiv.Perm (Fin 5) := by
  classical
  exact if h : ∃ p : Equiv.Perm (Fin 5), pcOf p = pc then Classical.choose h else 1

/-- The signed permutation of the code `c = 32 · pc + sc`. -/
def codeElt (c : ℕ) : G5 := sigAut (permOfPC (c / 32)) (scBits (c % 32))

/-- `σ` acts on the letters by the packed table `tab` (field `k` = image of letter `k`). -/
def TabOf (σ : G5) (tab : ℕ) : Prop := ∀ k < 81, σ * b1 5 k * σ⁻¹ = b1 5 (lk tab k)

/-- **(GL6) Codes.**  Valid codes give elements of `SigmaSet 5` acting on letters by `actL` (with
values `< 81`); every element of `SigmaSet 5` has a valid code; explicit codes of `sigAut p s`. -/
def CodeFacts : Prop :=
  (∀ c : ℕ, validPC 5 (c / 32) = true →
      codeElt c ∈ SigmaSet 5 ∧
      ∀ k < 81, actL 5 (c / 32) (c % 32) k < 81 ∧
        codeElt c * b1 5 k * (codeElt c)⁻¹ = b1 5 (actL 5 (c / 32) (c % 32) k)) ∧
  (∀ σ ∈ SigmaSet 5, ∃ c : ℕ, validPC 5 (c / 32) = true ∧ codeElt c = σ) ∧
  (∀ (p : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool),
      validPC 5 (pcOf p) = true ∧ scOf s < 32 ∧ codeElt (32 * pcOf p + scOf s) = sigAut p s) ∧
  (∀ sc < 32, scOf (scBits sc) = sc) ∧
  (∀ pc, validPC 5 pc = true → ∀ i : Fin 5, (permOfPC pc i).val = pdig pc i.val)

/-- Commutation table soundness. -/
def CmSound (cm : NT) : Prop :=
  ∀ a < 81, ∀ b < 81, commB cm a b = true → b1 5 a * b1 5 b = b1 5 b * b1 5 a

/-- **(GL8) The kernel action on codes.**  With a sound commutation table, `normC` computes a code
of `b1 a * b1 b`, and a letter table of `σ` acts on codes by conjugation. -/
def ActCSound : Prop :=
  ∀ (cm : NT), CmSound cm →
    (∀ a < 81, ∀ b < 81, eltC (normC cm a b) = b1 5 a * b1 5 b ∧
        normC cm a b / 128 < 81 ∧ normC cm a b % 128 < 81) ∧
    ∀ (σ : G5) (tab : ℕ), TabOf σ tab → (∀ k < 81, lk tab k < 81) →
      ∀ c : ℕ, c / 128 < 81 → c % 128 < 81 →
        eltC (actC cm tab c) = σ * eltC c * σ⁻¹ ∧ actC cm tab c / 128 < 81 ∧ actC cm tab c % 128 < 81

/-- **(GL7) Free reduction is canonical.** -/
def RedWCanonical : Prop :=
  ∀ (r : ℕ) (u v : List ℕ), (∀ c ∈ u, c < 2 * r) → (∀ c ∈ v, c < 2 * r) →
    evalW (r := r) u = evalW (r := r) v → redW u = redW v

/-- **(GL7b) The model key is a function of the automorphism.** -/
def ModelKeyFaithful : Prop :=
  ∀ a b a' b' : ℕ, a < 81 → b < 81 → a' < 81 → b' < 81 →
    b1 5 a * b1 5 b = b1 5 a' * b1 5 b' → modelKey (128 * a + b) = modelKey (128 * a' + b')

/-- Sign vector of a binary code. -/
def zOfSc {m : ℕ} (sc : ℕ) : Fin m → ZMod 2 := fun i => ((sbit sc i.val : ℕ) : ZMod 2)

/-- The subset of `Fin m` of a bit mask. -/
def maskSet {m : ℕ} (S : ℕ) : Finset (Fin m) := Finset.univ.filter (fun i => sbit S i.val = 1)

/-- Sign function of a `ZMod 2` vector. -/
def zBool (a : Fin 5 → ZMod 2) : Fin 5 → Bool := fun i => decide (a i = 1)

/-- **(GL12) Bits bridge** between `ZMod 2` vectors / `chiS` and binary codes / `chiS5`, and the
blockRow sign of `ψ`. -/
def BitsBridge : Prop :=
  (∀ (m : ℕ) (F : (Fin m → ZMod 2) → ℝ), ∑ a, F a = ∑ sc ∈ Finset.range (2 ^ m), F (zOfSc sc)) ∧
  (∀ (m : ℕ) (a : Fin m → ZMod 2), ∃ sc < 2 ^ m, zOfSc sc = a) ∧
  (∀ S sc : ℕ, S < 32 → sc < 32 → chiS (maskSet (m := 5) S) (zOfSc sc) = (chiS5 S sc : ℝ)) ∧
  (∀ psi b : ℕ, psi < 4 → b < 4 → chiS (maskSet (m := 2) psi) (zOfSc b) =
      (if ((b &&& psi) % 2 + ((b &&& psi) / 2) % 2) = 1 then -1 else 1)) ∧
  (∀ sc < 32, zBool (zOfSc sc) = scBits sc) ∧
  (∀ a b : Fin 5 → ZMod 2, scOf (zBool (a + b)) = scOf (zBool a) ^^^ scOf (zBool b))

/-- **(GL9) Walsh–Hadamard transform.** -/
def WhtSound : Prop :=
  ∀ vs : List ℤ, vs.length = 32 →
    wht 5 vs = (List.range 32).map (fun S => ∑ sc ∈ Finset.range 32, chiS5 S sc * vs.getD sc 0)

end Submission.PTCert

end
