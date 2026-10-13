import Submission.Work.DSM4p.LvlMisc
import Submission.Work.DSM4p.LvlQRET
import Submission.Work.DSM4p.lvl_dvd
import Submission.Work.DSM4p.lvl_torsionFree
import Submission.Work.DSM4p.lvl_frobSurj
import Submission.Work.DSM4p.lvl_frobInj
import Submission.Work.DSM4p.isQRETp_adicCompletion
import Submission.Work.DSM4p.perfectoidData_adicCompletion
import Submission.Work.DSM4p.Basic

/-!
# DSM4p — the Route U assembly: the non-degenerate case of `area_M4p`

For a perfectoid `B` (`Q : PerfectoidData p B`), a compatible root system `gr` with `gr 0 ≠ 0`
and `p` not a unit, this module builds the tower of the node

  `lvlComp Q hgr n := AdicCompletion (Ideal.span {(p : lvl Q hgr n)}) (lvl Q hgr n)`

— the `p`-adic completion of the untilted level `lvl Q hgr n := untiltOf (lvlP …)` — and verifies
all three clauses of `Work.DSM4p.AreaM4p`:

* `QD n : PerfectoidData p (lvlComp Q hgr n)` with `(QD n).ϖ k = algebraMap B _ (Q.ϖ k)`, from
  `Work.DSM4p.perfectoidData_adicCompletion` applied to `lvl Q hgr n` with the inputs
  `lvl_torsionFree`, `lvl_frobSurj`, `lvl_frobInj`;
* `g = gr 0` divides `p ^ n`, transported from `lvl_dvd` along the completion
  (`AdicCompletion.of` is a ring hom, and `AdicCompletion.algebraMap_apply` identifies the
  structure maps);
* `IsQRETp p B Q.ϖ gr (lvlComp Q hgr) tr`, from `Work.DSM4p.isQRETp_adicCompletion` applied to
  `Work.DSM4p.lvl_isQRETp`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open DSMap DSMap.Mix DSMap.Mix2

namespace Work.DSM4p

universe a

/-- **The non-degenerate case of `area_M4p`** (Route U): `p` is not a unit and `gr 0 ≠ 0`, so the
untilted levels are nontrivial and the characteristic-`p` chart machinery applies. -/
theorem areaM4p_notIsUnit {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : PerfectoidData p B) (gr : ℕ → B) (hgr : IsRootSystem p gr) (hgr0 : gr 0 ≠ 0)
    (hunit : ¬ IsUnit (p : B)) : AreaM4p p B Q gr := by
  haveI hfac : Fact (¬ IsUnit (p : B)) := ⟨hunit⟩
  haveI hcomp : IsAdicComplete (Ideal.span {(p : B)}) B := Q.complete
  have hQD : ∀ n, ∃ QD : PerfectoidData p (lvlComp Q hgr n),
      ∀ k, QD.ϖ k = algebraMap B (lvlComp Q hgr n) (Q.ϖ k) :=
    fun n => perfectoidData_adicCompletion (p := p) (Q := Q)
      (lvl_torsionFree Q hgr n) (lvl_frobSurj Q hgr hgr0 n) (lvl_frobInj Q hgr hgr0 n)
  let QD : ∀ n, PerfectoidData p (lvlComp Q hgr n) := fun n => (hQD n).choose
  have hv : ∀ n k, (QD n).ϖ k = algebraMap B (lvlComp Q hgr n) (Q.ϖ k) :=
    fun n => (hQD n).choose_spec
  obtain ⟨tr, htr⟩ := isQRETp_adicCompletion (p := p) Q.ϖ gr (lvl_torsionFree Q hgr)
    (lvlTrAlg Q hgr) (lvl_isQRETp Q hgr hgr0)
  have hdvd : ∀ n, ∃ y : lvlComp Q hgr n,
      algebraMap B (lvlComp Q hgr n) (gr 0) * y = (p : lvlComp Q hgr n) ^ n := by
    intro n
    obtain ⟨y₀, hy₀⟩ := lvl_dvd (p := p) Q hgr n
    refine ⟨algebraMap (lvl Q hgr n) (lvlComp Q hgr n) y₀, ?_⟩
    have h1 : algebraMap B (lvlComp Q hgr n) (gr 0)
        = algebraMap (lvl Q hgr n) (lvlComp Q hgr n) (algebraMap B (lvl Q hgr n) (gr 0)) := by
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : (p : lvlComp Q hgr n)
        = algebraMap (lvl Q hgr n) (lvlComp Q hgr n) (p : lvl Q hgr n) :=
      (map_natCast (algebraMap (lvl Q hgr n) (lvlComp Q hgr n)) p).symm
    rw [h1, h2, ← map_mul, hy₀, map_pow]
  exact ⟨fun n => lvlComp Q hgr n, inferInstance, inferInstance, QD, tr, hv, hdvd, htr⟩

end Work.DSM4p
