import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvl_exists_teich
import Submission.Work.DSM4p.chartLevel_perfect
import Submission.Work.DSM4p.lvlP_charP

namespace Work.DSM4p

universe a

/-- **Frobenius is surjective modulo `p` on the untilted levels.**

Step (6) of the Route U plan (`Submission/Work/DSM4p/Plan.lean`).  Given `y : lvl Q hgr N`, the
Teichmüller dictionary `lvl_exists_teich` produces `r : lvlP Q hgr N` with
`y ≡ mk (teichmuller p r) mod p`; the characteristic-`p` chart level is perfect
(`chartLevel_perfect`), so `r = r' ^ p` for some `r'`; and since `teichmuller p` is a monoid
homomorphism (`WittVector.teichmuller : R →* 𝕎 R`) and `untiltOf.mk` is a ring homomorphism,

  `(mk (teichmuller p r')) ^ p = mk (teichmuller p (r' ^ p)) = mk (teichmuller p r)`, so that
  `z := mk (teichmuller p r')` satisfies `y - z ^ p ≡ y - mk (teichmuller p r) ≡ 0 mod p`. -/
theorem lvl_frobSurj {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (N : ℕ) :
    ∀ y : Work.DSM4p.lvl Q hgr N,
      ∃ z : Work.DSM4p.lvl Q hgr N,
        y - z ^ p ∈ Ideal.span {((p : Work.DSM4p.lvl Q hgr N))} := by
  intro y
  -- Teichmüller representatives modulo `p`.
  obtain ⟨r, hr⟩ := lvl_exists_teich Q hgr hgr0 N y
  -- The characteristic-`p` chart level is perfect, so `r` has a `p`-th root `r'`.
  have hperf : PerfectRing (lvlP Q hgr N) p :=
    chartLevel_perfect (tiltTower_isRootSystem gr hgr) (tiltTower_isRootSystem Q.ϖ Q.root) N
  obtain ⟨r', hr'⟩ := hperf.bijective_frobenius.2 r
  have hr'' : r' ^ p = r := hr'
  refine ⟨DSM5c.untiltOf.mk (p := p) (W := B)
    (algebraMap (PreTilt B p) (lvlP Q hgr N)) (WittVector.teichmuller p r'), ?_⟩
  -- `(mk (teich r')) ^ p = mk (teich r)`.
  have hz : (DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (lvlP Q hgr N)) (WittVector.teichmuller p r')) ^ p =
      DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (lvlP Q hgr N)) (WittVector.teichmuller p r) := by
    rw [← map_pow (f := DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (lvlP Q hgr N))),
      ← map_pow (f := WittVector.teichmuller p), hr'']
  rw [hz]
  exact hr

end Work.DSM4p
