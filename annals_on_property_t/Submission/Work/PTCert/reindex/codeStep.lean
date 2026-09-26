import Mathlib
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.sigmaGroupFacts

namespace Work.PTCert.reindex

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.RouteB
open scoped BigOperators

set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-- Conjugation of a sign flip by a coordinate permutation: `π⁻¹ ν_s π = ν_{s ∘ q}` for
`π = permAut q` (which sends `a_k ↦ a_{q k}`).  (Local copy of
`Work.PTCert.efz_conj_permAut_signAut`, kept here to avoid depending on `entryFormula`.) -/
private theorem conj_permAut_signAut (q : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) :
    (permAut q)⁻¹ * signAut s * permAut q = signAut (fun i => s (q i)) := by
  have hq : permAut q = sigAut q (fun _ => false) := by
    rw [sigAut, Work.PTCert.SigmaFacts.signAut_one, one_mul]
  have hs : signAut s = sigAut 1 s := by
    rw [sigAut, Submission.RouteB.permAut_one, mul_one]
  have hsq : signAut (fun i => s (q i)) = sigAut 1 (fun i => s (q i)) := by
    rw [sigAut, Submission.RouteB.permAut_one, mul_one]
  rw [hq, hs, hsq, Work.PTCert.SigmaFacts.sigAut_inv]
  rw [show (fun x => (fun _ : Fin 5 => false) (q x)) = (fun _ : Fin 5 => false) from rfl]
  rw [Work.PTCert.SigmaFacts.sigAut_mul]
  rw [show q.symm * 1 = q.symm from mul_one q.symm]
  rw [show (fun k => (fun _ : Fin 5 => false) k ^^ s ((q.symm).symm k))
        = (fun k => s (q k)) from by funext k; simp [Equiv.symm_symm]]
  rw [Work.PTCert.SigmaFacts.sigAut_mul]
  rw [show q.symm * q = 1 from by ext i; simp]
  rw [show (fun k => s (q k) ^^ (fun _ : Fin 5 => false) ((q.symm).symm k))
        = (fun k => s (q k)) from by funext k; simp]

/-- The code identity behind `reindexEntryRow`.  With `π = codeElt (efPc k i)` (a permutation
`π = permAut (permOfPC (efPc k i / 32))` because `efPc k i % 32 = 0`), `π⁻¹ · rep_{Ta}` has code
`Z = actC cmT (efTabInv k i) (rp Ta)`, and `Z = ν_{Z % 32} · rep_{Z / 32}` (`NSem`).  For a code
`Phi sc` whose sign vector is `zOfSc sc ∘ q + zOfSc (Z % 32)` (`q = permOfPC (efPc k i / 32)`),
`π⁻¹ ν_{sc} rep_{Ta} = ν_{Phi sc} rep_{Z / 32}` because `π⁻¹ ν_sc π = ν_{zOfSc sc ∘ q}`. -/
theorem codeStep (hA : Submission.PTCert.G.ActSetup) (hNst : Submission.PTCert.G.NStructure)
    (hCF : Submission.PTCert.CodeFacts) (hN : Submission.PTCert.G.NSem)
    (hT : Submission.PTCert.G.TabSem) (hR : Submission.PTCert.G.RowSem)
    (hBB : Submission.PTCert.BitsBridge) (k i Ta : ℕ) (Phi : ℕ → ℕ)
    (hi : i < (Work.PTCert.efKs k).length) (ht : Work.PTCert.efT k i < 611) (hTa : Ta < 611)
    (hPhil : ∀ sc < 32, Phi sc < 32)
    (hPhiv : ∀ sc < 32, Submission.PTCert.zOfSc (m := 5) (Phi sc) =
        (fun j => Submission.PTCert.zOfSc (m := 5) sc
          ((Submission.PTCert.permOfPC (Work.PTCert.efPc k i / 32)) j)) +
          Submission.PTCert.zOfSc (m := 5)
            ((Submission.PTCert.G.em (Submission.PTCert.actC Submission.PTCert.D.cmT
              (Work.PTCert.efTabInv k i) (Submission.PTCert.G.rp Ta)) - 1) % 32))
    (sc : ℕ) (hsc : sc < 32) :
    Submission.PTCert.actC Submission.PTCert.D.cmT (Work.PTCert.efTabInv k i)
        (Submission.PTCert.actC Submission.PTCert.D.cmT (Submission.PTCert.G.ntab sc)
          (Submission.PTCert.G.rp Ta)) =
      Submission.PTCert.actC Submission.PTCert.D.cmT
        (Submission.PTCert.G.ntab (Phi sc))
        (Submission.PTCert.G.rp
          ((Submission.PTCert.G.em (Submission.PTCert.actC Submission.PTCert.D.cmT
            (Work.PTCert.efTabInv k i) (Submission.PTCert.G.rp Ta)) - 1) / 32)) := by
  obtain ⟨hfE_inj, hclosure, hConjAct, hActMul, hActOne, hActBij, hTabA, hActCode, hNmul,
    hNone, hsgnSg, hNtab⟩ := hA
  obtain ⟨hnu, hreprep, hrepact, hrpS, hrepE, hrepEI⟩ := hNst
  -- the row/index data of the representative `kE k i` and its letter-table data
  obtain ⟨hr, hidx, hrow⟩ := hR.2.2.1 (Work.PTCert.efT k i) ht
  obtain ⟨hvalid, hmod, hTabP, hTabPi, hlk⟩ := hT.2 (Work.PTCert.efIdx k i) hidx
  have hlkPi : ∀ j < 81, lk (Work.PTCert.efTabInv k i) j < 81 := fun j hj => (hlk j hj).2
  have hSginv : ∀ {s : G5}, s ∈ Sg → s⁻¹ ∈ Sg :=
    fun {s} hs => (Work.PTCert.sigmaGroupFacts 5).1.2.2 s hs
  have hy : (repEI Ta pt0).1 = rp Ta := (hrepEI Ta hTa pt0).2
  -- `π = codeElt (efPc k i)` is the permutation `permAut q` (`efPc k i % 32 = 0`)
  have hπ : codeElt (Work.PTCert.efPc k i) = permAut (permOfPC (Work.PTCert.efPc k i / 32)) := by
    rw [codeElt, show Work.PTCert.efPc k i % 32 = 0 from hmod]
    rw [show scBits 0 = (fun _ : Fin 5 => false) from by funext j; simp [scBits, sbit]]
    rw [sigAut, Work.PTCert.SigmaFacts.signAut_one, one_mul]
  -- the code of `π⁻¹ · rep_Ta`
  let Z' : EI := actE (codeElt (Work.PTCert.efPc k i))⁻¹ (repEI Ta pt0)
  have hZcode : Z'.1 = actC cmT (Work.PTCert.efTabInv k i) (rp Ta) := by
    show (actE (codeElt (Work.PTCert.efPc k i))⁻¹ (repEI Ta pt0)).1 = _
    rw [hTabA (codeElt (Work.PTCert.efPc k i))⁻¹ (Work.PTCert.efTabInv k i) hTabPi hlkPi
      (repEI Ta pt0), hy]
  have hZmem : actC cmT (Work.PTCert.efTabInv k i) (rp Ta) ∈ eAll := by
    have h1 : Z'.1 ∈ eS := Z'.2
    rw [hZcode] at h1
    exact List.mem_toFinset.mp h1
  obtain ⟨hge1, hlt611, hZrep⟩ := hN.1 (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) hZmem
  -- `Z' = ν_{μ'} · rep_t` with `μ' = (em Z - 1) % 32` and `t = (em Z - 1) / 32`
  have hZ'eq : Z' = actN (zOfSc (m := 5) ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta))
        - 1) % 32))
      (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0) := by
    apply Subtype.ext
    rw [hNtab ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) % 32)
      (Nat.mod_lt _ (by norm_num))
      (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0)]
    rw [(hrepEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) hlt611 pt0).2]
    rw [hZcode]
    exact hZrep.symm
  -- `π` and `ν = ν_sc` lie in `Sg`, and `ν` is `signAut (zBool ·)`
  have hπSg : codeElt (Work.PTCert.efPc k i) ∈ Sg := (hCF.1 (Work.PTCert.efPc k i) hvalid).1
  have hνSg : signAut (scBits sc) ∈ Sg := by
    rw [← hBB.2.2.2.2.1 sc hsc]; exact hsgnSg (zOfSc (m := 5) sc)
  have hzB : (fun j : Fin 5 => scBits sc ((permOfPC (Work.PTCert.efPc k i / 32)) j))
      = zBool (fun j : Fin 5 => zOfSc (m := 5) sc
          ((permOfPC (Work.PTCert.efPc k i / 32)) j)) := by
    funext j
    simp only [zBool, scBits]
    rw [decide_eq_decide]
    have h2 : sbit sc ((permOfPC (Work.PTCert.efPc k i / 32)) j).val = 0 ∨
        sbit sc ((permOfPC (Work.PTCert.efPc k i / 32)) j).val = 1 := by unfold sbit; omega
    rcases h2 with h | h <;> rw [zOfSc, h] <;> simp
  have hscqSg : signAut (fun j : Fin 5 => scBits sc
      ((permOfPC (Work.PTCert.efPc k i / 32)) j)) ∈ Sg := by
    rw [hzB]; exact hsgnSg _
  -- `π⁻¹ * ν = signAut (scBits sc ∘ q) * π⁻¹`
  have hsplit : (codeElt (Work.PTCert.efPc k i))⁻¹ * signAut (scBits sc)
      = signAut (fun j : Fin 5 => scBits sc ((permOfPC (Work.PTCert.efPc k i / 32)) j))
        * (codeElt (Work.PTCert.efPc k i))⁻¹ := by
    rw [hπ, ← conj_permAut_signAut (permOfPC (Work.PTCert.efPc k i / 32)) (scBits sc)]
    group
  -- the element identity
  have hmain : actE (codeElt (Work.PTCert.efPc k i))⁻¹ (actN (zOfSc (m := 5) sc) (repEI Ta pt0))
      = actN (zOfSc (m := 5) (Phi sc))
          (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0) := by
    calc actE (codeElt (Work.PTCert.efPc k i))⁻¹ (actN (zOfSc (m := 5) sc) (repEI Ta pt0))
        = actE (codeElt (Work.PTCert.efPc k i))⁻¹
            (actE (signAut (scBits sc)) (repEI Ta pt0)) := by
            rw [show actN (zOfSc (m := 5) sc) (repEI Ta pt0)
                = actE (signAut (scBits sc)) (repEI Ta pt0) from by
              unfold actN; rw [hBB.2.2.2.2.1 sc hsc]]
      _ = actE ((codeElt (Work.PTCert.efPc k i))⁻¹ * signAut (scBits sc)) (repEI Ta pt0) :=
            (hActMul _ (hSginv hπSg) _ hνSg (repEI Ta pt0)).symm
      _ = actE (signAut (fun j : Fin 5 => scBits sc ((permOfPC (Work.PTCert.efPc k i / 32)) j))
              * (codeElt (Work.PTCert.efPc k i))⁻¹) (repEI Ta pt0) := by rw [hsplit]
      _ = actE (signAut (fun j : Fin 5 => scBits sc
              ((permOfPC (Work.PTCert.efPc k i / 32)) j)))
            (actE (codeElt (Work.PTCert.efPc k i))⁻¹ (repEI Ta pt0)) :=
            hActMul _ hscqSg _ (hSginv hπSg) (repEI Ta pt0)
      _ = actN (fun j : Fin 5 => zOfSc (m := 5) sc
              ((permOfPC (Work.PTCert.efPc k i / 32)) j)) Z' := by
            show actE (signAut (fun j : Fin 5 => scBits sc
                ((permOfPC (Work.PTCert.efPc k i / 32)) j)))
                (actE (codeElt (Work.PTCert.efPc k i))⁻¹ (repEI Ta pt0))
              = actE (signAut (zBool (fun j : Fin 5 => zOfSc (m := 5) sc
                ((permOfPC (Work.PTCert.efPc k i / 32)) j)))) Z'
            rw [hzB]
      _ = actN ((fun j : Fin 5 => zOfSc (m := 5) sc
              ((permOfPC (Work.PTCert.efPc k i / 32)) j))
            + zOfSc (m := 5) ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) % 32))
            (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0) := by
            rw [hZ'eq, ← hNmul]
      _ = actN (zOfSc (m := 5) (Phi sc))
            (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0) := by
            rw [← hPhiv sc hsc]
  -- the two codes of that element
  have hLHS : (actE (codeElt (Work.PTCert.efPc k i))⁻¹
        (actN (zOfSc (m := 5) sc) (repEI Ta pt0))).1
      = actC cmT (Work.PTCert.efTabInv k i) (actC cmT (ntab sc) (rp Ta)) := by
    rw [hTabA (codeElt (Work.PTCert.efPc k i))⁻¹ (Work.PTCert.efTabInv k i) hTabPi hlkPi]
    rw [hNtab sc hsc, hy]
  have hRHS : (actN (zOfSc (m := 5) (Phi sc))
        (repEI ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32) pt0)).1
      = actC cmT (ntab (Phi sc))
        (rp ((em (actC cmT (Work.PTCert.efTabInv k i) (rp Ta)) - 1) / 32)) := by
    rw [hNtab (Phi sc) (hPhil sc hsc)]
    rw [(hrepEI _ hlt611 pt0).2]
  rw [← hLHS, hmain, hRHS]

end Work.PTCert.reindex
