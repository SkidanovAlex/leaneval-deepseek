import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.sym_prep
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.bmats_dvd
import Submission.Work.SGsep.symAux.defs
import Submission.Work.SGsep.symAux.base
import Submission.Work.SGsep.symAux.symChk_dvd
import Submission.Work.SGsep.symAux.sgTau_cocycle
import Submission.Work.SGsep.symAux.symDef_gen

/-!
# Soundness of the *yes* half of the `sym` certificate (`symChk_yes`)

The `sym` certificate of representative `k` certifies the order of `[τ_k] ∈ H¹(P, ℝ³/ℤ³)`.
The check `Data.SymCert.chk k a` says that for every *generator* `g` of the arithmetic class

  `a.sig - g · a.sig ≡ (a.o · n) · z_g  (mod n²)`,   `z_g = n · τ_k(g)`,

i.e. that `a.o · τ_k` is a coboundary for the potential `σ = a.sig / n²` *on the generators*.
Since the defect `A ↦ a.o·τ_k(A) − (σ − Aσ)` is additive over products
(`Work.SGsep.defect_mul`, because `τ_k` is a cocycle and `A` is integral), and the element
table is a BFS enumeration `elems (i+1) = gens[p₁] · elems[p₂]`, the vanishing of the defect
on generators propagates to every element of the class.  That is the induction below.

The three algebraic pieces are delegated:
* `symAux.symChk_dvd`  — unpacking `Data.SymCert.chk` into the divisibility above;
* `symAux.symDef_gen`   — the generator case: `symDef k a (GK k g) ∈ ℤ³`;
* `symAux.sgTau_cocycle` — the cocycle identity for `sgTau` on the table.
-/

namespace Work.SGsep

open Work.SG

/-- The defect of `a.o · τ_k` vanishes on the whole element table. -/
theorem symDef_all (k : Fin 230) (a : Data.SymCert) (hk : TauOnTable k)
    (ha : Data.SymCert.chk k.val a = true) :
    ∀ i, i < nK k → symDef k a (eK k i) ∈ zLat := by
  obtain ⟨-, hdvd⟩ := symAux.symChk_dvd k a ha
  intro i₀
  refine Nat.strong_induction_on i₀ ?_
  intro i ih hi
  rcases i with _ | j
  · rw [eK_zero k]
    exact symDef_one k a hk
  · have hparj : j < (Dk k).par.length := by
      have h := dk_par_length k
      omega
    have hg1 : par1 k j < kK k := (dk_facts k).par_bound1 j hparj
    have hg2 : par2 k j ≤ j := (dk_facts k).par_le j hparj
    have hg2n : par2 k j < nK k := by omega
    have hgn : geni k (par1 k j) < nK k := (dk_facts k).genidx_bound (par1 k j) hg1
    have hmn : mulg k (par1 k j) (par2 k j) < nK k :=
      (dk_facts k).mulgen_bound (par1 k j) hg1 (par2 k j) hg2n
    have hvalg : sgTau k (GK k (par1 k j)) =
        fun c => ((zK k (geni k (par1 k j))).toFun c : ℝ) / (nK k : ℝ) := by
      rw [← eK_geni k (par1 k j) hg1]
      exact sgTau_eK k hk (geni k (par1 k j)) hgn
    have hgen : symDef k a (GK k (par1 k j)) ∈ zLat :=
      symAux.symDef_gen k a (par1 k j) (nK_pos k) hvalg (fun c => hdvd (par1 k j) hg1 c)
    have hpre : symDef k a (eK k (par2 k j)) ∈ zLat := ih (par2 k j) (by omega) hg2n
    have hcoc : ∃ m : IVec, sgTau k (GK k (par1 k j) * eK k (par2 k j))
        = sgTau k (GK k (par1 k j))
          + (toRMat (GK k (par1 k j))).mulVec (sgTau k (eK k (par2 k j))) + toRVec m :=
      symAux.sgTau_cocycle k (par1 k j) (par2 k j) hvalg
        (sgTau_eK k hk (par2 k j) hg2n)
        (by
          rw [← eK_mulgen k (par1 k j) (par2 k j) hg1 hg2n]
          exact sgTau_eK k hk (mulg k (par1 k j) (par2 k j)) hmn)
        (repZ_cocycle k (par1 k j) (par2 k j) hg1 hg2n)
    obtain ⟨m, hm⟩ := hcoc
    have hgoal : symDef k a (GK k (par1 k j) * eK k (par2 k j)) ∈ zLat :=
      defect_mul hm hgen hpre
    have hpar' : eK k (j + 1) = GK k (par1 k j) * eK k (par2 k j) := eK_par k j hparj
    simpa only [Nat.succ_eq_add_one, hpar'] using hgoal

/-- **Soundness of the `yes` half of the `sym` certificate**: if the certificate of
representative `k` passes its check, then `a.o · τ_k` is a coboundary on the arithmetic class
of `k`, with potential `a.sig / n²`. -/
theorem symChk_yes (k : Fin 230) (a : Data.SymCert) (hk : TauOnTable k)
    (ha : Data.SymCert.chk k.val a = true) :
    IsCob (arithRep (sgArith k)) (fun A => (a.o : ℝ) • sgTau k A) := by
  rw [isCob_iff_defect]
  refine ⟨symSig k a, fun A hA => ?_⟩
  obtain ⟨i, hi, rfl⟩ := (mem_arithRep_iff k A).mp hA
  exact symDef_all k a hk ha i hi

end Work.SGsep
