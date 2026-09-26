import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.fourierTransport
import Submission.Work.PTCert.sigmaGroupFacts

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects of the rank-5 certificate: EI, fE,
actE, actN, repE, nuE, Pmat, …, and the semantic Props ESem/TabSem/NSem/RowSem/GroupSem/OrbLabSem/
ClassSem/KleinSem = plain meanings of the kernel checks) and `Glue3.lean` (the Props of the
mathematical steps). READ BOTH FIRST, and `NOTES_LEAD_glue.md` (workspace root) for the whole chain.
Hypotheses of the form `CodeFacts`, `ConjActFacts`, `ActCSound`, `BitsBridge`, `OrbitDecomp`,
`KleinLevel`, `FourierTransport`, `LdlChainSound`, `WhtSound` are GlueDefs Props proved in parallel by
other agents; `ESem`… are data facts proved by kernel checks. Use them as given; do not re-prove them.
Already-proved theorems you may use directly: `Work.PTCert.avgMatInvariant`, `rowFormula`,
`twistedFourierCriterion`, `psdOfBlock`, `psdSignedPerm`, `labelPrinciple`, `avgPrinciple`, `gramSOS`,
`avgGram`, `ldlScaledPrinciple`, `letterAction`, `modelSound`, `sigmaGroupFacts` (+ namespace
SigmaFacts: signAut_mul, signAut_inv, sigAut_mul, sigAut_inv, mem_SigmaSet_iff, ...), `permCheckKSound`.
NEVER unfold the big data definitions (`eAll`, `eM`, …) or try `decide` on them: all data facts come
through the Sem hypotheses. Do not change Glue*.lean. If the statement is false, `declare_false`
with the concrete reason (and say which hypothesis is missing).

`nLevel` is the `NLevel` step of the PSD chain: the `N = (ℤ/2)^5` sign flips act on the index type
`EI` of `B₂`-codes, and `Pmat pv` is invariant under this action (`RowFacts`, since every sign flip
is in `Sg`).  By `twistedFourierCriterion` (`sgn = 1`, `rep = repE`, `nu = nuE`) it is enough that
every Fourier block `W_S` (`S ⊆ Fin 5`) is PSD.  `NLevel` only provides the six *base* characters
`SkF k = {0, …, k-1}`; `FourierTransport` carries PSD of the block of `S` to the block of `S.map p`,
and every subset of `Fin 5` is `(SkF S.card).map p` for some permutation `p`
(`Equiv.Perm.exists_map_finset_eq`).  The transport `τ` is `actE (permAut q)` with `q := p`, which
normalises the `N`-action through `p` by the group identity
`permAut q * signAut s * (permAut q)⁻¹ = signAut (s ∘ q.symm)`; its `Pmat`-invariance comes from
`RowFacts` because `permAut q ∈ Sg` (`CodeFacts`).
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G

open scoped BigOperators

open Work.PTCert.SigmaFacts

/-! ## Small helper lemmas -/

/-- The base character `SkF k` has exactly `k` elements (for `k ≤ 5`). -/
lemma card_SkF (k : ℕ) (hk : k ≤ 5) : (SkF k).card = k := by
  interval_cases k <;> decide

/-- Every subset `S ⊆ Fin 5` is the image of the base character of the same cardinality under some
permutation. -/
lemma exists_perm_skF (S : Finset (Fin 5)) :
    ∃ p : Equiv.Perm (Fin 5), (SkF S.card).map p.toEmbedding = S := by
  have hk : S.card ≤ 5 := by simpa using Finset.card_le_univ S
  refine Equiv.Perm.exists_map_finset_eq (SkF S.card) S ?_
  rw [card_SkF S.card hk]

/-- `32 * a / 32 = a`. -/
lemma div32mul (a : ℕ) : (32 * a) / 32 = a := Nat.mul_div_cancel_left a (by norm_num)

/-- **Conjugation of a sign flip by a coordinate permutation**:
`permAut q * signAut s * (permAut q)⁻¹ = signAut (s ∘ q.symm)`. -/
lemma permAut_conj_signAut (p : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) :
    Submission.RouteB.permAut p * signAut s * (Submission.RouteB.permAut p)⁻¹
      = signAut (fun i => s (p.symm i)) := by
  rw [Submission.RouteB.mulAut_eq_iff]
  intro k
  rw [SigmaFacts.signAut_apply (fun i => s (p.symm i)) k]
  change Submission.RouteB.permAut p
      (signAut s ((Submission.RouteB.permAut p)⁻¹ (FreeGroup.of k)))
    = if s ((Equiv.symm p) k) = true then (FreeGroup.of k)⁻¹ else FreeGroup.of k
  rw [Submission.RouteB.permAut_inv, Submission.RouteB.permAut_apply,
      SigmaFacts.signAut_apply s (p.symm k)]
  by_cases h : s ((Equiv.symm p) k) = true
  · rw [if_pos h, if_pos h, map_inv, Submission.RouteB.permAut_apply, Equiv.apply_symm_apply]
  · rw [if_neg h, if_neg h, Submission.RouteB.permAut_apply, Equiv.apply_symm_apply]

/-- `permAut σ ∈ Sg` for every `σ : Equiv.Perm (Fin 5)`: the code `32 * pcOf σ` realises it
(`CodeFacts`). -/
lemma permAut_mem_Sg (hCF : CodeFacts) (p : Equiv.Perm (Fin 5)) :
    Submission.RouteB.permAut p ∈ Sg := by
  have h1 : validPC 5 (pcOf p) = true := (hCF.2.2.1 p (fun _ : Fin 5 => false)).1
  have h2 : codeElt (32 * pcOf p + scOf (fun _ : Fin 5 => false))
      = sigAut p (fun _ : Fin 5 => false) := (hCF.2.2.1 p (fun _ : Fin 5 => false)).2.2
  have hsc : scOf (fun _ : Fin 5 => false) = 0 := by simp [scOf]
  have hsig : sigAut p (fun _ : Fin 5 => false) = Submission.RouteB.permAut p := by
    rw [sigAut, SigmaFacts.signAut_one, one_mul]
  have h3 : codeElt (32 * pcOf p) = Submission.RouteB.permAut p := by
    have harg : 32 * pcOf p + scOf (fun _ : Fin 5 => false) = 32 * pcOf p := by
      rw [hsc, add_zero]
    calc codeElt (32 * pcOf p) = codeElt (32 * pcOf p + scOf (fun _ : Fin 5 => false)) := by
          rw [harg]
      _ = sigAut p (fun _ : Fin 5 => false) := h2
      _ = Submission.RouteB.permAut p := hsig
  have hvalid : validPC 5 ((32 * pcOf p) / 32) = true :=
    (congrArg (fun x => validPC 5 x) (div32mul (pcOf p))).trans h1
  have hmem : codeElt (32 * pcOf p) ∈ SigmaSet 5 := (hCF.1 (32 * pcOf p) hvalid).1
  rw [h3] at hmem
  exact hmem

/-- **N-level PSD reduction**: symmetry of `Pmat pv` and PSD of the six base-character blocks
`W_{S_k}` imply `Pmat pv ⪰ 0`. -/
theorem nLevel (hA : ActSetup) (hNst : NStructure) (hRF : RowFacts) (hFT : FourierTransport)
    (hBB : BitsBridge) (hCF : CodeFacts) : NLevel := by
  intro pv hsym hblocks
  obtain ⟨hfE_inj, hclosure, hConjAct, hActMul, hActOne, hActBij, hTab, hActCode,
    hNmul, hNone, hsgnSg, hNtab⟩ := hA
  have hactnu : ∀ x : EI, actN (nuE x) (repE x) = x := hNst.1
  have hreprep : ∀ x, repE (repE x) = repE x := hNst.2.1
  have hrepact : ∀ a x, repE (actN a x) = repE x := hNst.2.2.1
  -- `Pmat pv` is invariant under the sign-flip action (every sign flip is in `Sg`)
  have hMinv : ∀ a x y, Pmat pv (actN a x) (actN a y) = Pmat pv x y :=
    fun a x y => (hRF pv).2.1 (signAut (zBool a)) (hsgnSg a) x y
  -- every Fourier block is PSD, by transport from the base characters
  have hWSall : ∀ S : Finset (Fin 5), (WN pv S).PosSemidef := by
    intro S
    obtain ⟨p, hp⟩ := exists_perm_skF S
    have hmem : Submission.RouteB.permAut p ∈ Sg := permAut_mem_Sg hCF p
    let τ : EI ≃ EI := Equiv.ofBijective (actE (Submission.RouteB.permAut p))
      (hActBij (Submission.RouteB.permAut p) hmem)
    -- the conjugation identity, in the form needed to push `actN` past `τ`
    have hconj : ∀ a : Fin 5 → ZMod 2, Submission.RouteB.permAut p * signAut (zBool a)
        = signAut (zBool (fun i => a (p.symm i))) * Submission.RouteB.permAut p := by
      intro a
      have h := permAut_conj_signAut p (zBool a)
      have h2 := congrArg (fun z => z * Submission.RouteB.permAut p) h
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h2
      exact h2
    have hτ : ∀ a x, τ (actN a x) = actN (fun i => a (p.symm i)) (τ x) := by
      intro a x
      show actE (Submission.RouteB.permAut p) (actE (signAut (zBool a)) x)
          = actE (signAut (zBool (fun i => a (p.symm i))))
              (actE (Submission.RouteB.permAut p) x)
      rw [← hActMul (Submission.RouteB.permAut p) hmem (signAut (zBool a)) (hsgnSg a) x,
        hconj a,
        hActMul (signAut (zBool (fun i => a (p.symm i)))) (hsgnSg _)
          (Submission.RouteB.permAut p) hmem x]
    have hMτ : ∀ x y, Pmat pv (τ x) (τ y) = Pmat pv x y := by
      intro x y
      show Pmat pv (actE (Submission.RouteB.permAut p) x)
          (actE (Submission.RouteB.permAut p) y) = Pmat pv x y
      exact (hRF pv).2.1 (Submission.RouteB.permAut p) hmem x y
    have hk : S.card ≤ 5 := by simpa using Finset.card_le_univ S
    have hb : (WN pv (SkF S.card)).PosSemidef := hblocks S.card hk
    have hstep := hFT 5 (act := actN) hNmul hNone (Pmat pv) hMinv repE nuE hactnu hreprep
      hrepact τ p hτ hMτ (SkF S.card) hb
    rwa [hp] at hstep
  -- assembles through the twisted Fourier criterion
  have hMinv' : ∀ a x y, (1:ℝ) * 1 * Pmat pv (actN a x) (actN a y) = Pmat pv x y := by
    intro a x y; rw [one_mul, one_mul]; exact hMinv a x y
  refine twistedFourierCriterion 5 (act := actN) (sgn := fun _ _ => (1:ℝ)) hNmul hNone ?_ ?_
    (Pmat pv) hsym hMinv' repE nuE hactnu hreprep hrepact ?_
  · intro a b x; simp
  · intro a x; simp
  · intro S
    convert hWSall S using 1
    ext x y
    simp [WN, fourierW]

end Work.PTCert
