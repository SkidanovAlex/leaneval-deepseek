import Submission.Work.PTCert.Glue2

/-!
# PTCert — glue layer 3: the mathematical steps on the concrete objects (Props only)

Each Prop below is one dispatched lemma; the final assembly (`Final*.lean`) composes them.
All Props take the value table `pv : ℕ → ℤ` (key `2048 r + g` ↦ numerator of `P(x₀_r, g)`) as a
parameter, so they serve both certificates.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert.G

open Submission.PTCert Submission.PTCert.D

theorem zero_mem_eS : 0 ∈ eS := by
  unfold eS; rw [List.mem_toFinset]; unfold eAll; exact List.Mem.head _

/-- A base point of `EI` (the code `0` = the identity). -/
def pt0 : EI := ⟨0, zero_mem_eS⟩

/-- **(A) Action set-up.** -/
def ActSetup : Prop :=
  Function.Injective fE ∧
  (∀ σ ∈ Sg, ∀ x : EI, ∃ y : EI, fE y = σ * fE x * σ⁻¹) ∧
  ConjAction Sg fE actE ∧
  (∀ σ ∈ Sg, ∀ τ ∈ Sg, ∀ x, actE (σ * τ) x = actE σ (actE τ x)) ∧ (∀ x, actE 1 x = x) ∧
  (∀ σ ∈ Sg, Function.Bijective (actE σ)) ∧
  (∀ (σ : G5) (tab : ℕ), TabOf σ tab → (∀ k < 81, lk tab k < 81) → ∀ x : EI, (actE σ x).1 = actC cmT tab x.1) ∧
  (∀ c : ℕ, validPC 5 (c / 32) = true → ∀ x : EI, (actE (codeElt c) x).1 = actCode c x.1) ∧
  (∀ a b x, actN (a + b) x = actN a (actN b x)) ∧ (∀ x, actN 0 x = x) ∧
  (∀ a, signAut (zBool a) ∈ Sg) ∧
  (∀ sc < 32, ∀ x : EI, (actN (zOfSc sc) x).1 = actC cmT (ntab sc) x.1)

/-- **(B) N-structure** (hypotheses of `TwistedFourierCriterion` for the sign flips). -/
def NStructure : Prop :=
  (∀ x : EI, actN (nuE x) (repE x) = x) ∧ (∀ x, repE (repE x) = repE x) ∧
  (∀ a x, repE (actN a x) = repE x) ∧
  (∀ t < 611, rp t ∈ eS) ∧
  (∀ x : EI, (em x.1 - 1) / 32 < 611 ∧ (repE x).1 = rp ((em x.1 - 1) / 32)) ∧
  (∀ t < 611, ∀ x : EI, repE (repEI t x) = repEI t x ∧ (repEI t x).1 = rp t)

/-- **(C) Row facts** of `Pmat`: the row formula, invariance, and every element is a translate of
its row code. -/
def RowFacts : Prop :=
  ∀ pv : ℕ → ℤ,
    (∀ r < 18, ∀ x y : EI, x.1 = x0c r → Pmat pv x y = pv (keyOf r (labE r y.1))) ∧
    (∀ σ ∈ Sg, ∀ x y, Pmat pv (actE σ x) (actE σ y) = Pmat pv x y) ∧
    (∀ x : EI, labE 0 x.1 < 18 ∧ ∃ σ ∈ Sg, ∃ x' : EI, x'.1 = x0c (labE 0 x.1) ∧ actE σ x' = x)

/-- The transpose-consistency condition on a value table (the meaning of `symOK`). -/
def SymHyp (pv : ℕ → ℤ) : Prop :=
  ∀ r < 18, ∀ g < ngE r,
    pv (keyOf r g) =
      pv (keyOf (rinfo ((em (grepE r g) - 1) / 32) / 128)
        (labE (rinfo ((em (grepE r g) - 1) / 32) / 128)
          (actC cmT (piIT.get (rinfo ((em (grepE r g) - 1) / 32) % 128))
            (actC cmT (ntab ((em (grepE r g) - 1) % 32)) (x0c r)))))

/-- **(D) Symmetry.** -/
def SymFacts : Prop := ∀ pv : ℕ → ℤ, SymHyp pv → (Pmat pv).transpose = Pmat pv

/-- The N-level Fourier block of `Pmat pv` for the character `S`. -/
def WN (pv : ℕ → ℤ) (S : Finset (Fin 5)) : Matrix {x : EI // repE x = x} {x : EI // repE x = x} ℝ :=
  Matrix.of fun x y => fourierW actN (Pmat pv) S x.1 y.1

/-- **(E) N-level.** `Pmat ⪰ 0` from the blocks of the six base characters. -/
def NLevel : Prop :=
  ∀ pv : ℕ → ℤ, (Pmat pv).transpose = Pmat pv →
    (∀ k ≤ 5, (WN pv (SkF k)).PosSemidef) → (Pmat pv).PosSemidef

/-- Klein representative number `i` of the base character `k`, as an element of `EI`. -/
def kE (k i : ℕ) : EI := repEI ((ksL.getD k []).getD i 0) pt0
def nK (k : ℕ) : ℕ := (ksL.getD k []).length

/-- The `ψ`-block (`ψ < 4` a bit mask on the two Klein generators) of the base character `k`. -/
def psiBlock (pv : ℕ → ℤ) (k ψ : ℕ) : Matrix (Fin (nK k)) (Fin (nK k)) ℝ :=
  Matrix.of fun i j => ∑ b : Fin 2 → ZMod 2, chiS (maskSet (m := 2) ψ) b *
    chiS (SkF k) (nuE (kapE k b (kE k j))) * fourierW actN (Pmat pv) (SkF k) (kE k i) (repE (kapE k b (kE k j)))

/-- **(F) Klein level** for each base character. -/
def KleinFacts : Prop :=
  ∀ pv : ℕ → ℤ, (Pmat pv).transpose = Pmat pv → ∀ k ≤ 5,
    (∀ ψ < 4, ∀ i j, psiBlock pv k ψ i j = psiBlock pv k ψ j i) ∧
    ((∀ ψ < 4, (psiBlock pv k ψ).PosSemidef) → (WN pv (SkF k)).PosSemidef)

/-- Row tables of a certificate: `rowVal rowTs r S t = Σ_sc χ(S, sc) · pv(r, label of ν_sc · rep_t)`. -/
def RowTabHyp (pv : ℕ → ℤ) (rowTs : List NT) : Prop :=
  ∀ r < 18, ∀ t < 611, ∀ S < 32,
    rowVal rowTs r S t = ∑ sc ∈ Finset.range 32, chiS5 S sc * pv (keyOf r (labE r (actC cmT (ntab sc) (rp t))))

/-- The kernel's block entry `(i, j)`, `i ≤ j`, of the `ψ`-block of base character `k`. -/
def kEntry (rowTs : List NT) (k ψ i j : ℕ) : ℤ :=
  ((blockRows4 cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k []) (ysL.getD k []) i).getD ψ []).getD (j - i) 0

/-- **(G) Entry formula**: the kernel block entries are the `ψ`-block entries. -/
def EntryFormula : Prop :=
  ∀ (pv : ℕ → ℤ) (rowTs : List NT), RowTabHyp pv rowTs → ∀ k ≤ 4, ∀ ψ < 4, ∀ i j : Fin (nK k),
    i.1 ≤ j.1 → psiBlock pv k ψ i j = (kEntry rowTs k ψ i.1 j.1 : ℝ)

/-- **(H) LDL**: chained `ldlSeg` checks give PSD of the symmetrised kernel blocks. -/
def LdlFacts : Prop :=
  ∀ (rowTs : List NT) (k : ℕ), k ≤ 4 →
    ∀ (Cs : List (List (List ℤ))) (Ws : List (List ℤ)) (segs : List (List ℕ)) (accs : ℕ → List (List ℤ)),
      segs.flatten = List.range (nK k) →
      accs 0 = List.replicate 4 (List.replicate (nK k) 0) →
      (∀ j < segs.length, ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
          (ysL.getD k []) Cs Ws (segs.getD j []) (accs j) = some (accs (j + 1))) →
      (∀ ψ < 4, (Ws.getD ψ []).length = nK k ∧ (Cs.getD ψ []).length = nK k ∧
        ∀ i < nK k, 0 < (Ws.getD ψ []).getD i 1 ∧ ((Cs.getD ψ []).getD i []).length ≤ i + 1) →
      (ysL.getD k []).length = nK k →
      ∀ ψ < 4, (Matrix.of fun (i j : Fin (nK k)) =>
        ((if i.1 ≤ j.1 then kEntry rowTs k ψ i.1 j.1 else kEntry rowTs k ψ j.1 i.1 : ℤ) : ℝ)).PosSemidef

/-- **(I) Row tables** from the kernel `rowCheck`s. -/
def RowTabSound : Prop :=
  ∀ (valT : NT) (rowTs : List NT),
    (∀ r < 18, ∀ t < 611, rowCheck valT (olTs.getD r (NT.leaf 0)) (rowTs.getD r (NT.leaf 0)) r [t] = true) →
    RowTabHyp (fun k => sv (p8 valT k)) rowTs

/-- **(J) Orbit decomposition down to the group keys.** -/
def OrbitKeys : Prop :=
  ∀ pv : ℕ → ℤ,
    conjAvg Sg (gramForm fE (Pmat pv)) =
      conjAvg Sg (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
        ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) • MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))

/-- The target of a certificate as a sum over the letter pairs `p = 81 a + b`. -/
def targetSum (q : ℕ → ℤ) (Dq : ℤ) : MonoidAlgebra ℝ G5 :=
  ∑ p ∈ Finset.range 6561, ((q p : ℝ) / (Dq : ℝ)) • MonoidAlgebra.of ℝ G5 (lprod 5 [invL (p / 81), p % 81, 0, 0])

/-- The symmetrised residual element. -/
def residualSum (res : ℕ → ℤ) (den : ℝ) : MonoidAlgebra ℝ G5 :=
  ∑ c ∈ Finset.range ncls, ((res c : ℝ) / den / 2) •
    (MonoidAlgebra.of ℝ G5 (lprod 5 (canonW c)) + MonoidAlgebra.of ℝ G5 (lprod 5 (canonW c))⁻¹)

/-- **(K) Label identity**: exact class sums (the meaning of `classSumOK`) and the residual
symmetry give a vanishing `conjAvg`. -/
def LabelIdentity : Prop :=
  ∀ (pv q res : ℕ → ℤ) (Dq SCv : ℤ), 0 < Dq → 0 < SCv →
    (∀ c < ncls, Dq * (((klist.getD c []).map (fun k => (multE k : ℤ) * pv k)).sum) -
        SCv * (((tlist.getD c []).map q).sum) + res c = 0) →
    (∀ c < ncls, res (icls c) = res c ∧ icls (icls c) = c) →
    conjAvg Sg ((1 / (SCv : ℝ)) • (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
          ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) • MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))
        - targetSum q Dq + residualSum res ((SCv : ℝ) * (Dq : ℝ))) = 0

/-- LDL data of one base character for a certificate (the hypotheses of `LdlFacts`). -/
def LdlData (rowTs : List NT) (k : ℕ) : Prop :=
  ∃ (Cs : List (List (List ℤ))) (Ws : List (List ℤ)) (segs : List (List ℕ)) (accs : ℕ → List (List ℤ)),
    segs.flatten = List.range (nK k) ∧
    accs 0 = List.replicate 4 (List.replicate (nK k) 0) ∧
    (∀ j < segs.length, ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
        (ysL.getD k []) Cs Ws (segs.getD j []) (accs j) = some (accs (j + 1))) ∧
    (∀ ψ < 4, (Ws.getD ψ []).length = nK k ∧ (Cs.getD ψ []).length = nK k ∧
      ∀ i < nK k, 0 < (Ws.getD ψ []).getD i 1 ∧ ((Cs.getD ψ []).getD i []).length ≤ i + 1)

/-- **(L) PSD assembly**: symmetry + row tables + LDL data for the five base characters ⇒ `Pmat ⪰ 0`. -/
def PsdAssembly : Prop :=
  ∀ (pv : ℕ → ℤ) (rowTs : List NT), SymHyp pv → RowTabHyp pv rowTs →
    (∀ k ≤ 4, LdlData rowTs k) → (Pmat pv).PosSemidef

/-- **(M) Final step** of a certificate: PSD Gram matrix + exact class sums + absorbed residual ⇒ SOS. -/
def FinalStep : Prop :=
  ∀ (pv q res : ℕ → ℤ) (Dq SCv : ℤ) (T : MonoidAlgebra ℝ G5) (c : ℝ), 0 < Dq → 0 < SCv →
    (Pmat pv).PosSemidef →
    (∀ cl < ncls, Dq * (((klist.getD cl []).map (fun k => (multE k : ℤ) * pv k)).sum) -
        SCv * (((tlist.getD cl []).map q).sum) + res cl = 0) →
    (∀ cl < ncls, res (icls cl) = res cl ∧ icls (icls cl) = cl) →
    ∑ cl ∈ Finset.range ncls, res cl = 0 →
    16 * (∑ cl ∈ Finset.range ncls, |(res cl : ℝ)|) ≤ c * (SCv : ℝ) * (Dq : ℝ) →
    (∀ σ ∈ Sg, MonoidAlgebra.of ℝ G5 σ * T * MonoidAlgebra.of ℝ G5 σ⁻¹ = T) →
    T = targetSum q Dq + c • Edge.deltaSub 5 5 →
    IsSOS T

end Submission.PTCert.G

end
